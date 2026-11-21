#!/usr/bin/env python3
"""Remove plain theorem commands absent from the kernel cone and retained source."""
import argparse
from collections import Counter, defaultdict, deque
import csv
import gzip
import hashlib
from pathlib import Path
import re
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("fork", type=Path)
parser.add_argument("original", type=Path, help="source at 40e56bab026552e089d7afcfeff08d2defb9c005")
parser.add_argument("data", type=Path, help="v0.2 decls.csv.gz and decl_edges.csv.gz")
parser.add_argument("--apply", action="store_true")
parser.add_argument("--manifest", type=Path, required=True)
args = parser.parse_args()
for filename, expected in {
    "decls.csv.gz": "af5daf53fdb72862666665eaf02a6f22b3307d5e0d175e3864d37a1ebcc9b4db",
    "decl_edges.csv.gz": "0e450a0120add04c917c574150a2898db6c07c87e1da9623d2eafe506ddc2025",
}.items():
    with (args.data / filename).open("rb") as stream:
        if hashlib.file_digest(stream, "sha256").hexdigest() != expected:
            raise ValueError(f"Unexpected dependency data: {filename}")

files = sorted(p.relative_to(args.fork).as_posix() for p in (args.fork / "src").rglob("*.lean"))
header = re.compile(rb"\A(?:(?:import [^\n]*|[ \t]*)\n)*")
signature = re.compile(rb"^[ \t]*(?:(private|protected)[ \t]+)?(?:lemma|theorem)[ \t]+([^\s:(\[{]+)")
identifier = re.compile(rb"[A-Za-z_][A-Za-z0-9_']*")
byfile = defaultdict(list)
with gzip.open(args.data / "decls.csv.gz", "rt") as f:
    for row in csv.DictReader(f):
        if (row["source"] == "routeB-env" and row["in_cone"] == "false"
                and row["n_shared_aux_in_cone"] == "0" and row["decls_in_command"] == "1"
                and row["generated"] == "false" and row["command_kind"] in {"theorem", "lemma"}
                and row["start_line"] == row["range_start_line"]):
            byfile[row["file"]].append((int(row["start_line"])-1, int(row["end_line"]), row["decl"]))

# A candidate's complete source command must still be at its original path, in
# a matching file body. Keep attributes, command prefixes and unusual names.
commands, names, public, private = {}, {}, defaultdict(list), defaultdict(lambda: defaultdict(list))
for file in files:
    if file not in byfile:
        continue
    old = (args.original / file).read_bytes()
    prefix = header.match(old).end()
    body = old[prefix:]
    new = (args.fork / file).read_bytes()
    pos = new.find(body) if body else -1
    if pos < 0 or (pos and new[pos-1] != 10) or new.find(body, pos+1) >= 0:
        continue
    offset = new[:pos].count(b"\n") - old[:prefix].count(b"\n")
    lines = new.splitlines(keepends=True)
    selected = []
    for start, end, name in sorted(byfile[file]):
        start, end = start+offset, end+offset
        if not 0 <= start < end <= len(lines):
            raise ValueError(f"Invalid command range in {file}")
        match = signature.match(lines[start])
        if not match or (selected and selected[-1][1] > start):
            continue
        last = match[2].split(b".")[-1]
        if not identifier.fullmatch(last) or name.split(".")[-1] != last.decode():
            continue
        # A scope on the preceding line can apply to this command alone.
        prev = start - 1
        while prev >= 0 and not lines[prev].strip():
            prev -= 1
        previous = lines[prev].strip() if prev >= 0 else b""
        if previous.endswith(b" in") or (previous.startswith(b"@[") and previous.endswith(b"]")):
            continue
        i = len(names)
        if name in names:
            raise ValueError(f"Duplicate dataset name {name}")
        names[name] = i
        selected.append((start, end, i))
        if match[1] == b"private":
            private[file][last].append(i)
        else:
            public[last].append(i)
    if selected:
        commands[file] = selected
del byfile
print(f"Screened {len(names):,} plain theorem commands", flush=True)
# Give a name its own graph node. A reference to an ambiguous short name keeps
# every possible public target plus the private targets in its file.
edges = defaultdict(set)
next_node = len(names)
def name_nodes(index):
    global next_node
    result = {}
    for key, targets in index.items():
        result[key] = next_node
        edges[next_node].update(targets)
        next_node += 1
    return result
pub = name_nodes(public)
priv = {f: name_nodes(d) for f, d in private.items()}
keep = set()
# Include Lean files outside src (the challenge checks and cache utilities).
tracked = subprocess.check_output(["git", "-C", str(args.fork), "ls-files", "-z", "*.lean"])
outside = [p.decode() for p in tracked.split(b"\0") if p and not p.startswith(b"src/")]
for file in files + outside:
    lines = (args.fork / file).read_bytes().splitlines(keepends=True)
    local = priv.get(file, {})
    def scan(text, out):
        tokens = set(identifier.findall(text))
        out.update(pub[t] for t in tokens if t in pub)
        if local:
            out.update(local[t] for t in tokens if t in local)
        if b"_private." in text:
            # A spelled-out private reference is visible across modules.
            for full in re.findall(rb"_private\.[\w.\x80-\xff']+", text):
                parts = full.decode().split(".")
                while parts:
                    decl = ".".join(parts)
                    if decl in names:
                        out.add(names[decl])
                        break
                    parts.pop()
    cursor = 0
    for start, end, i in commands.get(file, ()):
        scan(b"".join(lines[cursor:start]), keep)
        scan(b"".join(lines[start:end]), edges[i])
        cursor = end
    scan(b"".join(lines[cursor:]), keep)
print("Checked explicit references in fork source", flush=True)
with gzip.open(args.data / "decl_edges.csv.gz", "rt", newline="") as f:
    rows = csv.reader(f)
    assert next(rows) == ["src", "src_kind", "dst", "dst_kind", "via"]
    for src, sk, dst, dk, via in rows:
        if dk != "decl" or dst not in names:
            continue
        target = names[dst]
        if sk == "decl" and src in names:
            edges[names[src]].add(target)
        else:
            keep.add(target)
todo = deque(keep)
while todo:
    for dest in edges.get(todo.popleft(), ()):
        if dest not in keep:
            keep.add(dest)
            todo.append(dest)
reverse = {i:n for n,i in names.items()}
counts = Counter()
with args.manifest.open("w") as manifest:
    for file, spans in sorted(commands.items()):
        drops = [(a,b,i) for a,b,i in spans if i not in keep]
        if not drops:
            continue
        lines = (args.fork / file).read_bytes().splitlines(keepends=True)
        out, cursor = [], 0
        for a,b,i in drops:
            out.extend(lines[cursor:a])
            manifest.write(f"{file}\t{a+1}\t{b}\t{reverse[i]}\n")
            counts["lines"] += sum(line.count(b"\n") for line in lines[a:b])
            counts["declarations"] += 1
            cursor = b
        out.extend(lines[cursor:])
        counts["files"] += 1
        if args.apply:
            (args.fork / file).write_bytes(b"".join(out))
print(dict(counts), flush=True)
