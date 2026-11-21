#!/usr/bin/env python3
"""Measure same-directory single-importer folds at a Git revision. No source edits."""
import argparse
from collections import Counter
from graphlib import TopologicalSorter
import hashlib
from pathlib import Path
import re
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("revision", nargs="?", default="HEAD")
parser.add_argument("--plan", type=Path, help="write the child and its immediate importer as TSV")
args = parser.parse_args()
root = subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip()
rev = subprocess.check_output(["git", "-C", root, "rev-parse", "--verify",
                               f"{args.revision}^{{commit}}"], text=True).strip()

# The pinned source uses ordinary single-line imports. Refuse a different grammar.
import_line = re.compile(rb"^import[ \t]+([^\s]+)[ \t]*$", re.M)
header_command = re.compile(rb"^[ \t]*(?:(?:public|private|meta|all)[ \t]+)*import\b", re.M)
sensitive = re.compile(rb"(?m)^\s*(?:(?:private|local|scoped|partial|unsafe)\s+)*"
                       rb"(?:elab(?:_rules)?|macro(?:_rules)?|syntax|initialize|builtin_initialize|run_cmd)\b"
                       rb"|(?m:^\s*#\w+)|\b_private\.")
entries = subprocess.check_output(["git", "-C", root, "ls-tree", "-rz", rev]).split(b"\0")
imports, size, locked = {}, {}, set()
all_files = all_lines = 0
with subprocess.Popen(["git", "-C", root, "cat-file", "--batch"], stdin=subprocess.PIPE,
                      stdout=subprocess.PIPE) as blobs:
    for entry in entries:
        if not entry.endswith(b".lean"):
            continue
        meta, path = entry.split(b"\t", 1)
        oid = meta.split()[2]
        blobs.stdin.write(oid + b"\n")
        blobs.stdin.flush()
        answer, kind, length = blobs.stdout.readline().split()
        if answer != oid or kind != b"blob":
            raise ValueError(f"Cannot read {path!r}")
        data = blobs.stdout.read(int(length))
        if blobs.stdout.read(1) != b"\n":
            raise ValueError(f"Incomplete object {oid!r}")
        lines = data.count(b"\n")
        all_files += 1
        all_lines += lines
        if not path.startswith(b"src/"):
            continue
        mod = path[4:-5].decode().replace("/", ".")
        found = import_line.findall(data)
        if len(found) != len(header_command.findall(data)):
            raise ValueError(f"Unsupported import syntax in {mod}")
        imports[mod] = [name.decode() for name in found]
        size[mod] = lines
        if mod in {"Main", "Statements", "Challenge"} or mod.startswith("BuildAid.") or sensitive.search(data):
            locked.add(mod)
    blobs.stdin.close()
    if blobs.wait():
        raise RuntimeError("git cat-file failed")

libraries = {m.split(".")[0] for m in imports}
graph, consumers = {}, Counter()
for mod, dependencies in imports.items():
    missing = [d for d in dependencies if d.split(".")[0] in libraries and d not in imports]
    if missing:
        raise ValueError(f"{mod} imports missing project modules {missing}")
    graph[mod] = {d for d in dependencies if d in imports}
    consumers.update(graph[mod])

def closure(graph, root):
    visited, todo = set(), [root]
    while todo:
        node = todo.pop()
        if node not in visited:
            visited.add(node)
            todo.extend(graph[node])
    return visited

before = closure(graph, "Main")
order = list(TopologicalSorter(graph).static_order())
folds, count, weight = {}, {}, {}
for mod in order:
    count[mod], weight[mod] = 1, size[mod]
    if mod not in before or mod in locked:
        continue
    for child in sorted(graph[mod], key=lambda d: (weight[d], d)):
        if child in locked or consumers[child] != 1 or child.rpartition(".")[0] != mod.rpartition(".")[0]:
            continue
        if count[mod] + count[child] > 16 or weight[mod] + weight[child] > 1600:
            continue
        folds[child] = mod
        count[mod] += count[child]
        weight[mod] += weight[child]

# Check the proposed graph without editing a Lean file.
owner = {}
for mod in reversed(order):
    owner[mod] = owner[folds[mod]] if mod in folds else mod
reduced = {m: set() for m in order if m not in folds}
for mod, dependencies in graph.items():
    reduced[owner[mod]].update(owner[d] for d in dependencies if owner[d] != owner[mod])
list(TopologicalSorter(reduced).static_order())
if closure(reduced, "Main") != {owner[m] for m in before}:
    raise ValueError("Main lost a group")
plan = "".join(f"{child}\t{folds[child]}\n" for child in sorted(folds)).encode()
if args.plan:
    args.plan.write_bytes(plan)
print(f"Commit {rev}\nTracked Lean files {all_files:,}; lines {all_lines:,}")
print(f"Main closure {len(before):,} files; {sum(size[m] for m in before):,} lines")
print(f"One direct importer {sum(consumers[m] == 1 for m in before):,}")
print(f"Folds {len(folds):,}; remaining tracked files {all_files-len(folds):,}; "
      f"reduction {len(folds)/all_files:.4%}")
print(f"Multi-file groups {sum(count[m] > 1 for m in reduced):,}; plan SHA-256 {hashlib.sha256(plan).hexdigest()}")
for area, n in Counter(".".join(m.split(".")[:2]) for m in folds).most_common(6):
    print(f"{area}: {n:,}")
