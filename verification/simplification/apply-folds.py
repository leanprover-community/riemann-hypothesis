#!/usr/bin/env python3
"""Move same-directory single-use modules into their importer in original DFS order."""
import argparse
from collections import Counter, defaultdict
import csv
from graphlib import TopologicalSorter
import gzip
import hashlib
from pathlib import Path
import re

from fold_names import DeclarationOwners

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("root", type=Path, help="fork checkout")
parser.add_argument("plan", type=Path, help="module-folds.py TSV from before declaration pruning")
parser.add_argument("decls", type=Path, help="v0.2 decls.csv.gz")
parser.add_argument("manifest", type=Path, help="write actual source-to-destination map")
parser.add_argument("--apply", action="store_true")
args = parser.parse_args()
src = args.root / "src"
proposed = dict(line.split("\t") for line in args.plan.read_text().splitlines())
participants = set(proposed) | set(proposed.values())
with args.decls.open("rb") as f:
    if hashlib.file_digest(f, "sha256").hexdigest() != "af5daf53fdb72862666665eaf02a6f22b3307d5e0d175e3864d37a1ebcc9b4db":
        raise ValueError("Incorrect declaration map")
header = re.compile(r"\A(?:(?:import [^\n]*|[ \t]*)\n)*")
import_line = re.compile(r"^import[ \t]+([^\s]+)[ \t]*$", re.M)
scope = re.compile(r"^\s*(?:(?:noncomputable|public|private|meta)\s+)*(namespace|section|end)(?:\s+([^\s]+))?\s*(?:--.*)?$")
declaration = re.compile(r"^\s*(?:@\[[^\n]*?\]\s*)*(?:(?:private|protected|noncomputable|nonrec|unsafe|partial|public|meta|local|scoped)\s+)*(?:theorem|lemma|def|abbrev|class|structure|inductive|instance|opaque)\s+([^\s:(\[{⦃]+)")
special = re.compile(r"(?m)^\s*(?:cpt_copy_thms|#\w+|run_cmd|initialize|builtin_initialize|export)\b")
def source(m):
    return src / (m.replace(".", "/") + ".lean")

def inspect(body):
    stack, names = [], set()
    for line in body.splitlines():
        m = scope.fullmatch(line)
        if m:
            cmd, name = m.groups()
            parts = name.split(".") if name else [""]
            if cmd == "end":
                if [x for _,x in stack[-len(parts):]] != parts:
                    raise ValueError("scope")
                del stack[-len(parts):]
            else:
                stack.extend((cmd, part) for part in parts)
            continue
        if re.match(r"^\s*(?:(?:public|noncomputable|meta)\s+)*(section|namespace|end)\b", line):
            raise ValueError("scope")
        d = declaration.match(line)
        if d:
            name = d[1]
            if name.startswith("_root_."):
                names.add(name.removeprefix("_root_."))
            else:
                names.add(".".join([v for k,v in stack if k == "namespace"] + [name]))
    return names, "".join("end" + ((" "+part) if part else "") + "\n" for _,part in reversed(stack))

by_name = sorted(".".join(p.relative_to(src).with_suffix("").parts) for p in src.rglob("*.lean"))
present = set(by_name)
catalog = DeclarationOwners()
names = defaultdict(set)
with gzip.open(args.decls, "rt") as f:
    for row in csv.DictReader(f):
        m = row["module"]
        if m in present:
            name = row["decl"]
            prefix = "_private." + m + "."
            private = name.startswith(prefix)
            if private:
                name = name[len(prefix):].split(".",1)[-1]
            catalog.add(name, m, private)
            if m in participants:
                names[m].add(name)
deps, closure_ends, blocked = {}, {}, {}
roots = {p.name for p in src.iterdir() if p.is_dir()} | {"Main","Statements","Challenge"}
for m in by_name:
    text = source(m).read_text()
    h = header.match(text).end()
    deps[m] = import_line.findall(text[:h])
    if import_line.search(text[h:]):
        raise ValueError(f"Unexpected import after source commands in {m}")
    # The export can attribute an identically named theorem to just one of its
    # modules. Also register names from the source, including relocated aliases.
    stack = []
    for line in text[h:].splitlines():
        sc = scope.fullmatch(line)
        if sc:
            cmd, label = sc.groups()
            parts = label.split(".") if label else [""]
            if cmd == "end":
                del stack[-len(parts):]
            else:
                stack.extend((cmd, v) for v in parts)
        else:
            d = declaration.match(line)
            if d:
                name = d[1]
                if name.startswith("_root_."):
                    name = name[7:]
                else:
                    name = ".".join([v for k,v in stack if k == "namespace"] + [name])
                catalog.add(name, m, "private" in line[:d.start(1)].split())
    if m not in participants:
        continue
    if special.search(text[h:]):
        blocked[m] = "module-specific command"
        continue
    try:
        found, closure_ends[m] = inspect(text[h:])
        names[m].update(found)
    except ValueError:
        blocked[m] = "unsupported section boundary"
graph = {m:{d for d in ds if d in deps} for m,ds in deps.items()}
users = Counter(d for ds in graph.values() for d in ds)
order = list(TopologicalSorter(graph).static_order())
folds, skipped = {}, Counter()
for m in order:
    for child in deps[m]:
        if proposed.get(child) != m or child in folds:
            continue
        if users[child] != 1 or child.rpartition(".")[0] != m.rpartition(".")[0]:
            raise ValueError(f"Invalid fold {child} into {m}")
        if m in blocked or child in blocked:
            skipped[blocked.get(m, blocked.get(child))] += 1
        elif names[m] & names[child]:
            skipped["declaration name collision"] += 1
        else:
            names[m].update(names[child])
            folds[child] = m

def group_owners():
    result = {}
    for m in reversed(order):
        result[m] = result[folds[m]] if m in folds else m
    return result

owners = group_owners()
while True:
    conflicts = catalog.conflicting_groups(graph, owners)
    if not conflicts:
        break
    unsafe = [m for m in folds if owners[m] in conflicts]
    if not unsafe:
        raise ValueError("Unable to isolate conflicting imported declarations")
    for m in unsafe:
        del folds[m]
    skipped["newly visible same-name declaration"] += len(unsafe)
    owners = group_owners()
groups = defaultdict(set)
for m,owner in owners.items():
    groups[owner].add(m)
new_deps = dict(deps)
def render(owner, members):
    imported, seen, bodies = [], set(), []
    visited = set()
    def visit(m):
        if m in visited:
            return
        visited.add(m)
        for dep in deps[m]:
            if dep in members:
                visit(dep)
            elif dep not in seen:
                seen.add(dep)
                imported.append(dep)
        data = source(m).read_text()
        body = data[header.match(data).end():]
        if body.strip():
            bodies.append("section\n" + body.rstrip("\n") + "\n" + closure_ends[m] + "end\n")
    visit(owner)
    if visited != members:
        raise ValueError(f"Incomplete group {owner}")
    return imported, "\n".join("import "+d for d in imported) + "\n\n" + "\n".join(bodies)
for owner,members in groups.items():
    if len(members) > 1:
        imports, output = render(owner,members)
        new_deps[owner] = imports
        if args.apply:
            source(owner).write_text(output)
if args.apply:
    for child in folds:
        source(child).unlink()
reduced = {}
for m,ds in new_deps.items():
    if m in folds:
        continue
    if any(d in folds or (d.split(".")[0] in roots and d not in deps) for d in ds):
        raise ValueError(f"Dangling import in {m}")
    reduced[m] = {d for d in ds if d in deps}
list(TopologicalSorter(reduced).static_order())
def reachable(g):
    seen, todo = set(), ["Main"]
    while todo:
        m = todo.pop()
        if m not in seen:
            seen.add(m)
            todo.extend(g[m])
    return seen
if reachable(reduced) != {owners[m] for m in reachable(graph)}:
    raise ValueError("Main reachability mismatch")
with args.manifest.open("w") as f:
    for child in sorted(folds):
        f.write(f"{child}\t{owners[child]}\n")
print(f"Folded {len(folds):,} modules into {sum(len(g)>1 for g in groups.values()):,} files. "
      f"Main reaches {len(reachable(reduced)):,} modules.")
print(f"Skipped {len(proposed)-len(folds):,} proposed folds: {dict(skipped)}")
