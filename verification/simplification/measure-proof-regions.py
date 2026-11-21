#!/usr/bin/env python3
"""Intersect a clean fork checkout with upstream v0.2 declaration ranges."""
import argparse
from collections import Counter
import csv
import gzip
import hashlib
from pathlib import Path
import re

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("fork", type=Path, help="clean fork checkout")
parser.add_argument("original", type=Path, help="original proof checkout at 40e56bab")
parser.add_argument("data", type=Path, help="directory holding the two v0.2 release assets")
args = parser.parse_args()
for filename, digest in {
    "decls.csv.gz": "af5daf53fdb72862666665eaf02a6f22b3307d5e0d175e3864d37a1ebcc9b4db",
    "dominators.tsv.gz": "3ce626a50f605c168aaa0607030c5b3a0b61c45741476fe081664279b9329172",
}.items():
    with (args.data / filename).open("rb") as data:
        if hashlib.file_digest(data, "sha256").hexdigest() != digest:
            raise ValueError(f"Unexpected v0.2 digest for {filename}")

# Count at the original path only. Earlier moves and partial rewrites are excluded.
header = re.compile(rb"\A(?:(?:import [^\n]*|[ \t]*)\n)*")
matched = set()
for path in (args.fork / "src").rglob("*.lean"):
    relative = path.relative_to(args.fork)
    original = args.original / relative
    if not original.is_file():
        continue
    source = original.read_bytes()
    body = source[header.match(source).end():]
    if body and body in path.read_bytes():
        matched.add(relative.as_posix())

roots = {
    "UpperTheory.FinalTheorems.everyCharacter_of_row",
    "UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin",
    "UpperTheory.Lit.every_character_of_theta_integrals_local_matching",
    "UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound",
    "GlobalTheory.Fc.S0.StageU.hypotheses_nonempty_of_unramified_exponents_alt",
    "UpperTheory.One.vwin_of_row",
    "SelfIntersectionVolumeEstimates.topCovolSlim2_use_alt_alt",
    "UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter",
}
windows, owned = {}, Counter()
with gzip.open(args.data / "dominators.tsv.gz", "rt") as data:
    for row in csv.DictReader(data, delimiter="\t"):
        # The dataset visits parents before descendants. tin/tout are half-open.
        tin = int(row["tin"])
        if row["decl"] in roots:
            windows[row["decl"]] = tin, int(row["tout"])
        if row["file"] in matched:
            for name, (start, end) in windows.items():
                if start <= tin < end:
                    owned[name] += int(row["lines"])
if windows.keys() != roots:
    raise ValueError("Missing a selected root in the dominator data")

unused, counts = Counter(), Counter()
with gzip.open(args.data / "decls.csv.gz", "rt") as data:
    for row in csv.DictReader(data):
        if (row["in_cone"] == "false" and row["file"] in matched
                and row["source"] == "routeB-env" and int(row["n_shared_aux_in_cone"]) == 0):
            area = "/".join(row["file"].split("/")[:3])
            unused[area] += int(row["lines"])
            counts[area] += 1
print(f"Matching module bodies: {len(matched):,}")
for name, lines in owned.most_common():
    print(f"{name}: {lines:,} declaration lines")
print(f"Outside the original kernel cone: {counts.total():,} declarations, {unused.total():,} declaration lines")
for area, lines in unused.most_common(6):
    print(f"{area}: {lines:,} declaration lines")
