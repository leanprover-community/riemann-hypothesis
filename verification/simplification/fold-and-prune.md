# Module consolidation and unused theorem removal

The baseline is the fork after the quotient and interlacing pilot, at `576bebfc0787cf20ded025e5c0fe240c4fa8ddd1`. Counts cover every tracked Lean file, including the Comparator challenge and build utilities. Lines are newline counts.

| Measure | Before | After | Reduction |
| --- | ---: | ---: | ---: |
| Tracked Lean files | 138,826 | 78,632 | 60,194 (43.36%) |
| Lean files reachable from Main | 138,817 | 78,623 | 60,194 |
| Tracked Lean lines | 16,434,546 | 16,072,826 | 361,720 (2.20%) |

## Removed theorem commands

The pass removed 34,025 theorems and lemmas from 7,745 files, totaling 374,270 lines. The largest reductions were in Development/AbelianVarietyTheory (98,477 lines), Formalism/LocalToGlobal (52,271) and Formalism/SharpRestriction (52,100).

Each removed command met these conditions:

- The complete original module body occurs at the same fork path, and the declaration maps to an ordinary, single theorem or lemma command at that location.
- The original five-theorem kernel dependency graph excludes the declaration and its shared auxiliary lemmas.
- A second traversal, starting at all retained declarations and source outside the candidate commands, finds no dependency on that theorem. This traversal includes compiled type and value references, unqualified and qualified source references, and private name visibility. Ambiguous public short names keep all candidate matches.
- Commands with attributes, instances, notation and unsupported declaration forms stay in place. The on-disk deletion ranges have zero intersections with ranges that supply a used declaration or shared auxiliary in the original export.

The earlier estimate of 222,198 candidates included definitions, instances and commands whose names appear elsewhere in source. It was a screening count. The declaration manifest lists each actual deletion with its file and its start and end lines on the pre-pruning fork. [Upstream dependency data, v0.2](https://github.com/james-shore/rh-proof-dependencies/releases/tag/v0.2)

## Consolidated modules

The pass moved 60,194 helper modules into 15,856 files. Each retired module had a single direct importer in its directory. A group contains at most 16 original modules and 1,600 original lines. Original import order determines the order of its proof bodies. Each body has its own section so that local options, notation, opens and variables retain their scope. External consumers of retired module paths can use the destination in the fold manifest.

Of the 60,480 proposed folds, 135 would have put repeated declaration names in one file. Four involved a module-specific command. A further 147 were left separate to isolate 20 groups in which pooling imports would expose previously invisible declarations of the same name.

Consolidation added 12,550 net lines for scopes, separators and import changes. The net project line reduction comes from pruning. The resulting import graph is acyclic. Every surviving proof group is reachable from Main. The five public theorem statements and bodies, the standalone challenge and the axiom-check file match the baseline byte for byte.

## Verification

A source readback checks every surviving module. It matches each untouched file byte for byte and checks each grouped file's ordered imports, original proof bodies and inserted scope boundaries. The upstream kernel dataset describes the original proof. A clean build of the reduced `Main`, its five endpoint axiom reports and Comparator remain pending.

[Independent source reconstruction and targeted Lean builds](https://github.com/mmmbeer/riemann-hypothesis/actions/runs/44913736053)

## Reproduce

Use clean checkouts of the baseline fork and the original source at `40e56bab026552e089d7afcfeff08d2defb9c005`. Save `decls.csv.gz` and `decl_edges.csv.gz` from dataset v0.2 in a separate directory. The scripts check the published file digests. Run with Python 3.11 or newer. The following commands use the scripts in this revision to modify the separate baseline checkout.

```bash
scripts_dir="$(pwd)/verification/simplification"
cd /path/to/clean-baseline-fork
python3 "$scripts_dir/module-folds.py" HEAD --plan /tmp/proposed.tsv
python3 "$scripts_dir/prune-unused.py" . /path/to/original /path/to/v0.2 --manifest /tmp/pruned.tsv --apply
python3 "$scripts_dir/apply-folds.py" . /tmp/proposed.tsv /path/to/v0.2/decls.csv.gz /tmp/folded.tsv --apply
git add -u src
tree=$(git write-tree)
git rev-parse "$tree:src"
```

| Reproducible output | Digest |
| --- | --- |
| Source tree after pruning, Git tree | `6ca322793b923d8d404e8292f66a6b3db6dcd5d3` |
| Final source, Git tree | `b333064d48e43652ded81269bac949a14800f536` |
| Removed commands, TSV SHA-256 | `9e4c654ad68d14da28450fabfce425640a99e5eb742d52cabc642cad9cbe00b1` |
| Retired module and final importer, TSV SHA-256 | `b6afc57430470cfcb6a1c6a39c8d472350f6f2b8c630fb96ec703a64794c3be6` |
