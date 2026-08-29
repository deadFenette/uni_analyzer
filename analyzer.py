
#!/usr/bin/env python3

"""
Universal-ish Python Project Architecture Analyzer
---------------------------------------------------

Single-file static analyzer.

Usage:

    python analyzer.py C:\\Projects\\MyProject

HTML:

    python analyzer.py C:\\Projects\\MyProject --html report.html

JSON:

    python analyzer.py C:\\Projects\\MyProject --json report.json

Both:

    python analyzer.py C:\\Projects\\MyProject --html report.html --json report.json

No third-party dependencies.
"""

import ast
import argparse
import json
import math
import os
import sys
from collections import defaultdict, Counter, deque
from dataclasses import dataclass, field
from html import escape


# ============================================================
# DATA MODELS
# ============================================================

@dataclass
class FunctionInfo:
    name: str
    file: str
    line: int
    end_line: int
    complexity: int = 1
    calls: set = field(default_factory=set)

    @property
    def loc(self):
        return max(1, self.end_line - self.line + 1)


@dataclass
class ClassInfo:
    name: str
    file: str
    line: int
    end_line: int

    methods: list = field(default_factory=list)
    dependencies: set = field(default_factory=set)
    dependents: set = field(default_factory=set)

    @property
    def loc(self):
        return max(1, self.end_line - self.line + 1)

    @property
    def method_count(self):
        return len(self.methods)

    @property
    def complexity(self):
        if not self.methods:
            return 1
        return sum(m.complexity for m in self.methods)

    @property
    def average_complexity(self):
        if not self.methods:
            return 0
        return self.complexity / len(self.methods)


@dataclass
class FileInfo:
    path: str
    loc: int = 0
    classes: list = field(default_factory=list)
    functions: list = field(default_factory=list)
    imports: set = field(default_factory=set)


# ============================================================
# AST ANALYSIS
# ============================================================

class ComplexityVisitor(ast.NodeVisitor):

    def __init__(self):
        self.complexity = 1

    def visit_If(self, node):
        self.complexity += 1
        self.generic_visit(node)

    def visit_For(self, node):
        self.complexity += 1
        self.generic_visit(node)

    def visit_AsyncFor(self, node):
        self.complexity += 1
        self.generic_visit(node)

    def visit_While(self, node):
        self.complexity += 1
        self.generic_visit(node)

    def visit_IfExp(self, node):
        self.complexity += 1
        self.generic_visit(node)

    def visit_Try(self, node):
        self.complexity += len(node.handlers)
        self.generic_visit(node)

    def visit_BoolOp(self, node):
        self.complexity += max(0, len(node.values) - 1)
        self.generic_visit(node)

    def visit_Match(self, node):
        self.complexity += len(node.cases)
        self.generic_visit(node)


class CallVisitor(ast.NodeVisitor):

    def __init__(self):
        self.calls = set()

    def visit_Call(self, node):
        name = self.extract_name(node.func)

        if name:
            self.calls.add(name)

        self.generic_visit(node)

    @staticmethod
    def extract_name(node):

        if isinstance(node, ast.Name):
            return node.id

        if isinstance(node, ast.Attribute):

            parts = []
            current = node

            while isinstance(current, ast.Attribute):
                parts.append(current.attr)
                current = current.value

            if isinstance(current, ast.Name):
                parts.append(current.id)

            return ".".join(reversed(parts))

        return None


# ============================================================
# MAIN ANALYZER
# ============================================================

class ProjectAnalyzer:

    IGNORED_DIRS = {
        ".git",
        ".hg",
        ".svn",
        "__pycache__",
        ".venv",
        "venv",
        "env",
        "node_modules",
        "dist",
        "build",
        ".idea",
        ".vscode",
        ".mypy_cache",
        ".pytest_cache",
    }

    def __init__(self, root):

        self.root = os.path.abspath(root)

        self.files = {}
        self.classes = {}
        self.functions = {}

        self.symbol_to_class = {}
        self.symbol_to_function = {}

        self.graph = defaultdict(set)

        self.errors = []

        self.cycles = []

    # ========================================================
    # SCANNING
    # ========================================================

    def scan(self):

        for dirpath, dirnames, filenames in os.walk(self.root):

            dirnames[:] = [
                d for d in dirnames
                if d not in self.IGNORED_DIRS
            ]

            for filename in filenames:

                if not filename.endswith(".py"):
                    continue

                path = os.path.join(dirpath, filename)

                self.analyze_file(path)

    # ========================================================
    # FILE
    # ========================================================

    def analyze_file(self, path):

        rel = os.path.relpath(path, self.root)

        try:

            with open(
                path,
                "r",
                encoding="utf-8"
            ) as f:

                source = f.read()

            tree = ast.parse(
                source,
                filename=path
            )

        except Exception as e:

            self.errors.append(
                (rel, str(e))
            )

            return

        info = FileInfo(
            path=rel,
            loc=source.count("\n") + 1
        )

        self.files[rel] = info

        info.imports.update(
            self.extract_imports(tree)
        )

        # First pass: classes
        for node in ast.walk(tree):

            if isinstance(node, ast.ClassDef):

                key = f"{rel}:{node.name}"

                cls = ClassInfo(
                    name=node.name,
                    file=rel,
                    line=node.lineno,
                    end_line=getattr(
                        node,
                        "end_lineno",
                        node.lineno
                    )
                )

                self.classes[key] = cls

                info.classes.append(key)

                self.symbol_to_class[
                    node.name
                ] = key

                for child in node.body:

                    if not isinstance(
                        child,
                        (
                            ast.FunctionDef,
                            ast.AsyncFunctionDef
                        )
                    ):
                        continue

                    self.add_function(
                        child,
                        rel,
                        cls
                    )

        # Second pass: standalone functions
        for node in ast.walk(tree):

            if not isinstance(
                node,
                (
                    ast.FunctionDef,
                    ast.AsyncFunctionDef
                )
            ):
                continue

            if self.is_method(tree, node):
                continue

            self.add_function(
                node,
                rel,
                None
            )

        self.resolve_dependencies(
            rel,
            tree
        )

    # ========================================================
    # FUNCTIONS
    # ========================================================

    def add_function(
        self,
        node,
        file,
        owner
    ):

        complexity = ComplexityVisitor()
        complexity.visit(node)

        calls = CallVisitor()
        calls.visit(node)

        function = FunctionInfo(
            name=node.name,
            file=file,
            line=node.lineno,
            end_line=getattr(
                node,
                "end_lineno",
                node.lineno
            ),
            complexity=complexity.complexity,
            calls=calls.calls
        )

        if owner is not None:

            owner.methods.append(
                function
            )

            key = (
                f"{file}:"
                f"{owner.name}."
                f"{node.name}"
            )

        else:

            key = (
                f"{file}:"
                f"{node.name}"
            )

        self.functions[key] = function

        self.symbol_to_function[
            node.name
        ] = key

    # ========================================================
    # HELPERS
    # ========================================================

    def is_method(self, tree, target):

        for node in ast.walk(tree):

            if not isinstance(
                node,
                ast.ClassDef
            ):
                continue

            for child in node.body:

                if child is target:
                    return True

        return False

    def extract_imports(self, tree):

        result = set()

        for node in ast.walk(tree):

            if isinstance(
                node,
                ast.Import
            ):

                for alias in node.names:
                    result.add(alias.name)

            elif isinstance(
                node,
                ast.ImportFrom
            ):

                if node.module:
                    result.add(node.module)

        return result

    # ========================================================
    # DEPENDENCIES
    # ========================================================

    def resolve_dependencies(
        self,
        file,
        tree
    ):

        current = self.files[file].classes

        for class_key in current:

            cls = self.classes[class_key]

            node = self.find_class_node(
                tree,
                cls.name
            )

            if node is None:
                continue

            names = set()

            for child in ast.walk(node):

                if isinstance(
                    child,
                    ast.Name
                ):

                    names.add(child.id)

                elif isinstance(
                    child,
                    ast.Attribute
                ):

                    if isinstance(
                        child.value,
                        ast.Name
                    ):

                        names.add(
                            child.value.id
                        )

            for name in names:

                target = self.symbol_to_class.get(
                    name
                )

                if target is None:
                    continue

                if target == class_key:
                    continue

                cls.dependencies.add(
                    target
                )

                self.graph[
                    class_key
                ].add(target)

    def find_class_node(
        self,
        tree,
        name
    ):

        for node in ast.walk(tree):

            if isinstance(
                node,
                ast.ClassDef
            ):

                if node.name == name:
                    return node

        return None

    # ========================================================
    # GRAPH
    # ========================================================

    def build_dependents(self):

        for source, targets in self.graph.items():

            for target in targets:

                if target in self.classes:

                    self.classes[
                        target
                    ].dependents.add(
                        source
                    )

    def find_cycles(self):

        visited = set()
        stack = []
        cycles = []

        def dfs(node):

            if node in stack:

                index = stack.index(node)

                cycle = (
                    stack[index:]
                    + [node]
                )

                normalized = (
                    self.normalize_cycle(
                        cycle
                    )
                )

                if normalized not in cycles:
                    cycles.append(
                        normalized
                    )

                return

            if node in visited:
                return

            visited.add(node)
            stack.append(node)

            for child in self.graph.get(
                node,
                []
            ):

                dfs(child)

            stack.pop()

        for node in self.classes:

            dfs(node)

        self.cycles = cycles

        return cycles

    @staticmethod
    def normalize_cycle(
        cycle
    ):

        cycle = cycle[:-1]

        if not cycle:
            return tuple()

        rotations = [
            tuple(
                cycle[i:]
                + cycle[:i]
            )
            for i in range(
                len(cycle)
            )
        ]

        return min(rotations)

    # ========================================================
    # GRAPH METRICS
    # ========================================================

    def graph_centrality(self, key):

        """
        Approximate degree centrality.
        """

        total = max(
            1,
            len(self.classes) - 1
        )

        fan_in = len(
            self.classes[key].dependents
        )

        fan_out = len(
            self.classes[key].dependencies
        )

        return round(
            ((fan_in + fan_out) / total)
            * 100,
            2
        )

    def dependency_depth(self, key):

        """
        Longest dependency chain starting
        from a class.
        """

        visited = set()

        def walk(node):

            if node in visited:
                return 0

            visited.add(node)

            children = self.graph.get(
                node,
                set()
            )

            if not children:
                return 1

            return 1 + max(
                walk(child)
                for child in children
            )

        return walk(key)

    # ========================================================
    # SCORES
    # ========================================================

    def god_object_score(self, cls):

        loc = cls.loc
        methods = cls.method_count
        fan_out = len(cls.dependencies)
        fan_in = len(cls.dependents)
        complexity = cls.complexity

        score = 0

        score += min(
            25,
            loc / 50
        )

        score += min(
            20,
            methods / 2
        )

        score += min(
            20,
            fan_out * 1.5
        )

        score += min(
            15,
            fan_in * 0.75
        )

        score += min(
            20,
            complexity / 2
        )

        return min(
            100,
            round(score, 1)
        )

    def responsibility_score(
        self,
        cls
    ):

        """
        Heuristic:
        large class + many methods +
        many dependencies +
        high complexity.
        """

        size = min(
            100,
            cls.loc / 10
        )

        methods = min(
            100,
            cls.method_count * 4
        )

        deps = min(
            100,
            (
                len(cls.dependencies)
                + len(cls.dependents)
            ) * 3
        )

        complexity = min(
            100,
            cls.average_complexity * 5
        )

        return round(
            (
                size * 0.25
                + methods * 0.25
                + deps * 0.25
                + complexity * 0.25
            ),
            1
        )

    def priority_score(
        self,
        cls
    ):

        god = self.god_object_score(
            cls
        )

        responsibility = (
            self.responsibility_score(
                cls
            )
        )

        centrality = (
            self.graph_centrality(
                self.class_key(cls)
            )
        )

        cycle_bonus = 0

        for cycle in self.cycles:

            if self.class_key(cls) in cycle:

                cycle_bonus = 20
                break

        score = (
            god * 0.40
            + responsibility * 0.25
            + centrality * 0.20
            + cycle_bonus
        )

        return min(
            100,
            round(score, 1)
        )

    def class_key(self, cls):

        return f"{cls.file}:{cls.name}"

    # ========================================================
    # FULL REPORT
    # ========================================================

    def analyze(self):

        self.scan()
        self.build_dependents()
        self.find_cycles()

        classes = []

        for key, cls in self.classes.items():

            classes.append({
                "key": key,
                "name": cls.name,
                "file": cls.file,
                "line": cls.line,
                "loc": cls.loc,
                "methods": cls.method_count,
                "complexity": cls.complexity,
                "avg_complexity": round(
                    cls.average_complexity,
                    2
                ),
                "fan_in": len(
                    cls.dependents
                ),
                "fan_out": len(
                    cls.dependencies
                ),
                "centrality": self.graph_centrality(
                    key
                ),
                "dependency_depth":
                    self.dependency_depth(key),
                "god_object":
                    self.god_object_score(cls),
                "responsibility":
                    self.responsibility_score(cls),
                "priority":
                    self.priority_score(cls),
                "dependencies":
                    list(cls.dependencies),
                "dependents":
                    list(cls.dependents),
            })

        classes.sort(
            key=lambda x: x["priority"],
            reverse=True
        )

        # ----------------------------------------------------
        # Basic statistics
        # ----------------------------------------------------

        total_loc = sum(
            x.loc
            for x in self.files.values()
        )

        total_methods = len(
            self.functions
        )

        total_complexity = sum(
            x["complexity"]
            for x in classes
        )

        avg_class_loc = (
            total_loc / len(classes)
            if classes
            else 0
        )

        avg_complexity = (
            total_complexity / len(classes)
            if classes
            else 0
        )

        avg_fan_in = (
            sum(x["fan_in"] for x in classes)
            / len(classes)
            if classes
            else 0
        )

        avg_fan_out = (
            sum(x["fan_out"] for x in classes)
            / len(classes)
            if classes
            else 0
        )

        # ----------------------------------------------------
        # Histograms
        # ----------------------------------------------------

        size_buckets = Counter()

        for item in classes:

            loc = item["loc"]

            if loc < 100:
                bucket = "<100"
            elif loc < 250:
                bucket = "100-249"
            elif loc < 500:
                bucket = "250-499"
            elif loc < 1000:
                bucket = "500-999"
            else:
                bucket = "1000+"

            size_buckets[bucket] += 1

        complexity_buckets = Counter()

        for item in classes:

            c = item["avg_complexity"]

            if c <= 5:
                bucket = "1-5"
            elif c <= 10:
                bucket = "6-10"
            elif c <= 15:
                bucket = "11-15"
            elif c <= 20:
                bucket = "16-20"
            else:
                bucket = "20+"

            complexity_buckets[bucket] += 1

        # ----------------------------------------------------
        # Health
        # ----------------------------------------------------

        if classes:

            avg_priority = (
                sum(
                    x["priority"]
                    for x in classes
                )
                / len(classes)
            )

            critical = sum(
                1
                for x in classes
                if x["priority"] >= 80
            )

            high = sum(
                1
                for x in classes
                if 65 <= x["priority"] < 80
            )

            health = max(
                0,
                min(
                    100,
                    round(
                        100
                        - avg_priority
                        - len(self.cycles) * 2
                    )
                )
            )

        else:

            health = 100
            critical = 0
            high = 0

        # ----------------------------------------------------
        # Files
        # ----------------------------------------------------

        file_stats = []

        for path, info in self.files.items():

            file_stats.append({
                "file": path,
                "loc": info.loc,
                "classes": len(
                    info.classes
                ),
                "functions": len(
                    info.functions
                ),
                "imports": len(
                    info.imports
                ),
            })

        file_stats.sort(
            key=lambda x: x["loc"],
            reverse=True
        )

        # ----------------------------------------------------
        # Graph
        # ----------------------------------------------------

        graph_nodes = []

        for item in classes:

            graph_nodes.append({
                "id": item["key"],
                "name": item["name"],
                "file": item["file"],
                "score": item["priority"],
            })

        graph_edges = []

        for source, targets in self.graph.items():

            for target in targets:

                graph_edges.append({
                    "source": source,
                    "target": target,
                })

        return {
            "project": self.root,

            "summary": {
                "files": len(self.files),
                "classes": len(self.classes),
                "functions": total_methods,
                "loc": total_loc,
                "dependencies": sum(
                    len(v)
                    for v in self.graph.values()
                ),
                "avg_class_loc":
                    round(avg_class_loc, 2),
                "avg_complexity":
                    round(avg_complexity, 2),
                "avg_fan_in":
                    round(avg_fan_in, 2),
                "avg_fan_out":
                    round(avg_fan_out, 2),
                "cycles":
                    len(self.cycles),
                "health":
                    health,
                "critical":
                    critical,
                "high":
                    high,
            },

            "classes": classes,

            "files": file_stats,

            "cycles": [
                list(cycle)
                for cycle in self.cycles
            ],

            "histograms": {
                "class_size":
                    dict(size_buckets),
                "complexity":
                    dict(complexity_buckets),
            },

            "graph": {
                "nodes": graph_nodes,
                "edges": graph_edges,
            },

            "errors": self.errors,
        }


# ============================================================
# CONSOLE UI
# ============================================================

def bar(value, width=24):

    value = max(
        0,
        min(100, value)
    )

    filled = round(
        value / 100 * width
    )

    return (
        "█" * filled
        + "░" * (width - filled)
    )


def severity(score):

    if score >= 80:
        return "CRITICAL"

    if score >= 65:
        return "HIGH"

    if score >= 45:
        return "MEDIUM"

    return "LOW"


def print_report(report):

    s = report["summary"]

    print()
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║              PROJECT ARCHITECTURE ANALYZER                  ║")
    print("╚══════════════════════════════════════════════════════════════╝")

    print()
    print(f"Project:          {report['project']}")

    print()
    print("GENERAL")
    print("─" * 65)

    print(f"Files:             {s['files']}")
    print(f"Classes:           {s['classes']}")
    print(f"Functions:         {s['functions']}")
    print(f"Lines of code:     {s['loc']}")
    print(f"Dependencies:      {s['dependencies']}")

    print()
    print("ARCHITECTURE HEALTH")
    print("─" * 65)

    print(
        f"{bar(s['health'])} "
        f"{s['health']}/100"
    )

    print(
        f"Critical: {s['critical']}    "
        f"High: {s['high']}    "
        f"Cycles: {s['cycles']}"
    )

    print()
    print("AVERAGES")
    print("─" * 65)

    print(
        f"Class size:         {s['avg_class_loc']:.1f} LOC"
    )

    print(
        f"Complexity:         {s['avg_complexity']:.2f}"
    )

    print(
        f"Fan-in:             {s['avg_fan_in']:.2f}"
    )

    print(
        f"Fan-out:            {s['avg_fan_out']:.2f}"
    )

    # --------------------------------------------------------
    # Top classes
    # --------------------------------------------------------

    print()
    print("TOP REFACTOR TARGETS")
    print("─" * 65)

    for index, item in enumerate(
        report["classes"][:15],
        start=1
    ):

        print()
        print(
            f"{index:2}. "
            f"[{severity(item['priority']):8}] "
            f"{item['name']}"
        )

        print(
            f"    Score        : "
            f"{item['priority']}/100"
        )

        print(
            f"    Location     : "
            f"{item['file']}:{item['line']}"
        )

        print(
            f"    LOC          : "
            f"{item['loc']}"
        )

        print(
            f"    Methods      : "
            f"{item['methods']}"
        )

        print(
            f"    Complexity   : "
            f"{item['complexity']} "
            f"(avg {item['avg_complexity']})"
        )

        print(
            f"    Fan-in/out   : "
            f"{item['fan_in']} / "
            f"{item['fan_out']}"
        )

        print(
            f"    Centrality   : "
            f"{item['centrality']}%"
        )

        print(
            f"    Depth        : "
            f"{item['dependency_depth']}"
        )

        print(
            f"    God Object   : "
            f"{item['god_object']}/100"
        )

        print(
            f"    Responsibility: "
            f"{item['responsibility']}/100"
        )

    # --------------------------------------------------------
    # Largest
    # --------------------------------------------------------

    print()
    print("LARGEST CLASSES")
    print("─" * 65)

    largest = sorted(
        report["classes"],
        key=lambda x: x["loc"],
        reverse=True
    )

    for item in largest[:10]:

        print(
            f"{item['loc']:5} LOC  "
            f"{item['name']:<30} "
            f"{item['file']}"
        )

    # --------------------------------------------------------
    # Most connected
    # --------------------------------------------------------

    print()
    print("MOST CONNECTED")
    print("─" * 65)

    connected = sorted(
        report["classes"],
        key=lambda x:
        x["fan_in"] + x["fan_out"],
        reverse=True
    )

    for item in connected[:10]:

        total = (
            item["fan_in"]
            + item["fan_out"]
        )

        print(
            f"{total:4} connections  "
            f"{item['name']:<30}"
        )

    # --------------------------------------------------------
    # Complex
    # --------------------------------------------------------

    print()
    print("MOST COMPLEX")
    print("─" * 65)

    complex_items = sorted(
        report["classes"],
        key=lambda x:
        x["avg_complexity"],
        reverse=True
    )

    for item in complex_items[:10]:

        print(
            f"{item['avg_complexity']:6.2f} avg  "
            f"{item['name']:<30}"
        )

    # --------------------------------------------------------
    # Cycles
    # --------------------------------------------------------

    print()
    print("DEPENDENCY CYCLES")
    print("─" * 65)

    if not report["cycles"]:

        print("No cycles detected.")

    else:

        for index, cycle in enumerate(
            report["cycles"][:20],
            start=1
        ):

            names = []

            for key in cycle:

                if ":" in key:

                    name = key.split(":")[-1]

                else:

                    name = key

                names.append(name)

            if names:

                print(
                    f"{index}. "
                    + " → ".join(names)
                    + " → "
                    + names[0]
                )

    if report["errors"]:

        print()
        print("PARSING ERRORS")
        print("─" * 65)

        for path, error in report["errors"]:

            print(
                f"{path}: {error}"
            )

    print()
    print("Done.")


# ============================================================
# JSON
# ============================================================

def save_json(
    report,
    path
):

    with open(
        path,
        "w",
        encoding="utf-8"
    ) as f:

        json.dump(
            report,
            f,
            indent=2,
            ensure_ascii=False
        )


# ============================================================
# HTML
# ============================================================

def html_report(report):

    data = json.dumps(
        report,
        ensure_ascii=False
    )

    template = r"""<!DOCTYPE html>
<html lang="ru">

<head>

<meta charset="UTF-8">

<meta name="viewport"
      content="width=device-width, initial-scale=1.0">

<title>Architecture Report</title>

<style>

* {
    box-sizing: border-box;
}

body {
    margin: 0;
    background: #0f1117;
    color: #e6e6e6;
    font-family:
        -apple-system,
        BlinkMacSystemFont,
        "Segoe UI",
        sans-serif;
}

header {
    padding: 30px 40px;
    background: #151821;
    border-bottom: 1px solid #292d38;
}

h1 {
    margin: 0;
    font-size: 28px;
}

h2 {
    margin-top: 0;
}

.container {
    padding: 30px 40px;
    max-width: 1600px;
    margin: auto;
}

.grid {
    display: grid;
    grid-template-columns:
        repeat(auto-fit, minmax(220px, 1fr));
    gap: 16px;
    margin-bottom: 25px;
}

.card {
    background: #171a23;
    border: 1px solid #292d38;
    border-radius: 12px;
    padding: 20px;
}

.metric {
    font-size: 32px;
    font-weight: 700;
    margin-top: 8px;
}

.label {
    color: #8d94a5;
    font-size: 13px;
}

.small {
    color: #8d94a5;
    font-size: 13px;
}

table {
    width: 100%;
    border-collapse: collapse;
}

th,
td {
    padding: 10px;
    text-align: left;
    border-bottom: 1px solid #292d38;
}

th {
    color: #8d94a5;
    font-size: 12px;
}

tr:hover {
    background: #1d212c;
}

.badge {
    padding: 4px 8px;
    border-radius: 6px;
    font-size: 11px;
    font-weight: 700;
}

.critical {
    background: #5c2020;
}

.high {
    background: #5c4220;
}

.medium {
    background: #4b4820;
}

.low {
    background: #204c30;
}

.chart {
    height: 260px;
    display: flex;
    align-items: end;
    gap: 14px;
    padding: 20px 10px 35px;
}

.bar {
    flex: 1;
    min-width: 30px;
    background: #4f7cff;
    border-radius: 5px 5px 0 0;
    position: relative;
}

.bar span {
    position: absolute;
    bottom: -25px;
    width: 100%;
    text-align: center;
    font-size: 11px;
    color: #8d94a5;
}

.bar b {
    position: absolute;
    top: -20px;
    width: 100%;
    text-align: center;
    font-size: 11px;
}

.section {
    margin-bottom: 30px;
}

</style>

</head>

<body>

<header>

<h1>Project Architecture Report</h1>

<div class="small" id="project"></div>

</header>

<div class="container">

<div id="app"></div>

</div>

<script>

const DATA = __REPORT_DATA__;

function esc(value) {
    return String(value)
        .replaceAll("&", "&amp;")
        .replaceAll("<", "&lt;")
        .replaceAll(">", "&gt;")
        .replaceAll('"', "&quot;");
}

function severity(score) {

    if (score >= 80)
        return ["CRITICAL", "critical"];

    if (score >= 65)
        return ["HIGH", "high"];

    if (score >= 45)
        return ["MEDIUM", "medium"];

    return ["LOW", "low"];
}

function card(label, value) {

    return `
        <div class="card">
            <div class="label">
                ${esc(label)}
            </div>

            <div class="metric">
                ${esc(value)}
            </div>
        </div>
    `;
}

function histogram(data) {

    const values = Object.entries(data);

    if (!values.length)
        return "<div class='small'>No data</div>";

    const max = Math.max(
        ...values.map(x => x[1]),
        1
    );

    return `
        <div class="chart">

            ${values.map(
                ([label, value]) => `

                    <div
                        class="bar"
                        style="height:${Math.max(
                            4,
                            value / max * 190
                        )}px"
                    >

                        <b>${value}</b>

                        <span>
                            ${esc(label)}
                        </span>

                    </div>

                `
            ).join("")}

        </div>
    `;
}

function render() {

    const s = DATA.summary;

    document.getElementById(
        "project"
    ).textContent = DATA.project;

    let html = "";

    // ========================================================
    // SUMMARY
    // ========================================================

    html += `
        <div class="grid">

            ${card(
                "Architecture Health",
                s.health + "/100"
            )}

            ${card(
                "Files",
                s.files
            )}

            ${card(
                "Classes",
                s.classes
            )}

            ${card(
                "Functions",
                s.functions
            )}

            ${card(
                "Lines of Code",
                s.loc
            )}

            ${card(
                "Dependencies",
                s.dependencies
            )}

            ${card(
                "Cycles",
                s.cycles
            )}

            ${card(
                "Avg Complexity",
                s.avg_complexity
            )}

        </div>
    `;

    // ========================================================
    // REFACTOR PRIORITY
    // ========================================================

    html += `
        <div class="section card">

            <h2>
                Refactor Priority
            </h2>

            <table>

                <thead>

                    <tr>
                        <th>#</th>
                        <th>Class</th>
                        <th>Score</th>
                        <th>LOC</th>
                        <th>Methods</th>
                        <th>Complexity</th>
                        <th>Fan-in</th>
                        <th>Fan-out</th>
                        <th>Centrality</th>
                        <th>God Object</th>
                    </tr>

                </thead>

                <tbody>

                    ${
                        DATA.classes
                            .slice(0, 50)
                            .map((x, i) => {

                                const sev =
                                    severity(
                                        x.priority
                                    );

                                return `
                                    <tr>

                                        <td>
                                            ${i + 1}
                                        </td>

                                        <td>

                                            <b>
                                                ${esc(x.name)}
                                            </b>

                                            <br>

                                            <span
                                                class="small"
                                            >
                                                ${esc(x.file)}
                                            </span>

                                        </td>

                                        <td>

                                            <span
                                                class="badge ${sev[1]}"
                                            >
                                                ${x.priority}
                                            </span>

                                        </td>

                                        <td>
                                            ${x.loc}
                                        </td>

                                        <td>
                                            ${x.methods}
                                        </td>

                                        <td>
                                            ${x.avg_complexity}
                                        </td>

                                        <td>
                                            ${x.fan_in}
                                        </td>

                                        <td>
                                            ${x.fan_out}
                                        </td>

                                        <td>
                                            ${x.centrality}%
                                        </td>

                                        <td>
                                            ${x.god_object}
                                        </td>

                                    </tr>
                                `;

                            })
                            .join("")
                    }

                </tbody>

            </table>

        </div>
    `;

    // ========================================================
    // HISTOGRAMS
    // ========================================================

    html += `

        <div class="grid">

            <div class="card">

                <h2>
                    Class Size Distribution
                </h2>

                ${histogram(
                    DATA.histograms.class_size
                )}

            </div>

            <div class="card">

                <h2>
                    Complexity Distribution
                </h2>

                ${histogram(
                    DATA.histograms.complexity
                )}

            </div>

        </div>

    `;

    // ========================================================
    // CYCLES
    // ========================================================

    html += `

        <div class="section card">

            <h2>
                Dependency Cycles
            </h2>

            ${
                DATA.cycles.length
                ?
                `
                    <table>

                        <tbody>

                            ${
                                DATA.cycles
                                    .map(
                                        (cycle, i) => `

                                            <tr>

                                                <td>
                                                    ${i + 1}
                                                </td>

                                                <td>
                                                    ${
                                                        cycle
                                                            .map(
                                                                x =>
                                                                    esc(
                                                                        x
                                                                            .split(":")
                                                                            .pop()
                                                                    )
                                                            )
                                                            .join(
                                                                " → "
                                                            )
                                                    }
                                                </td>

                                            </tr>

                                        `
                                    )
                                    .join("")
                            }

                        </tbody>

                    </table>
                `
                :
                `
                    <div class="small">
                        No dependency cycles detected.
                    </div>
                `
            }

        </div>

    `;

    // ========================================================
    // LARGEST FILES
    // ========================================================

    html += `

        <div class="section card">

            <h2>
                Largest Files
            </h2>

            <table>

                <thead>

                    <tr>
                        <th>File</th>
                        <th>LOC</th>
                        <th>Classes</th>
                        <th>Functions</th>
                        <th>Imports</th>
                    </tr>

                </thead>

                <tbody>

                    ${
                        DATA.files
                            .slice(0, 50)
                            .map(
                                x => `

                                    <tr>

                                        <td>
                                            ${esc(x.file)}
                                        </td>

                                        <td>
                                            ${x.loc}
                                        </td>

                                        <td>
                                            ${x.classes}
                                        </td>

                                        <td>
                                            ${x.functions}
                                        </td>

                                        <td>
                                            ${x.imports}
                                        </td>

                                    </tr>

                                `
                            )
                            .join("")
                    }

                </tbody>

            </table>

        </div>

    `;

    document.getElementById(
        "app"
    ).innerHTML = html;
}

render();

</script>

</body>

</html>
"""

    return template.replace(
        "__REPORT_DATA__",
        data
    )


# ============================================================
# MAIN
# ============================================================

def main():

    parser = argparse.ArgumentParser(
        description=(
            "Analyze Python project "
            "architecture and complexity."
        )
    )

    parser.add_argument(
        "project",
        help="Project directory"
    )

    parser.add_argument(
        "--json",
        metavar="FILE",
        help="Save JSON report"
    )

    parser.add_argument(
        "--html",
        metavar="FILE",
        help="Save HTML report"
    )

    args = parser.parse_args()

    if not os.path.isdir(
        args.project
    ):

        print(
            f"Error: directory does not exist:\n"
            f"{args.project}",
            file=sys.stderr
        )

        sys.exit(1)

    analyzer = ProjectAnalyzer(
        args.project
    )

    report = analyzer.analyze()

    print_report(
        report
    )

    if args.json:

        save_json(
            report,
            args.json
        )

        print(
            f"\nJSON report: {args.json}"
        )

    if args.html:

        with open(
            args.html,
            "w",
            encoding="utf-8"
        ) as f:

            f.write(
                html_report(report)
            )

        print(
            f"HTML report: {args.html}"
        )


if __name__ == "__main__":
    main()
