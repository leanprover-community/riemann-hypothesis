# Where to reduce the Lean proof

For the implemented file and declaration reductions, see [module consolidation and pruning results](fold-and-prune.md). The measurements below describe the planning baseline.

The largest reproducible file-count reduction on the current fork is **60,482 files (43.57%)**. The largest mathematical target covers **8,215,997 lines**. The first figure comes from a concrete list of module moves. The second measures code behind a theorem for which a shorter proof is still needed.

The baseline is commit `7bf5b5d67b5369f0fdf403a11f5bae67515c6772`, shared by the fork's main and simplification branches when measured. It has 138,828 tracked Lean files and 16,436,985 newline-terminated source lines. Of these, 138,819 files and 16,436,151 lines are in the import closure of `Main`. The repository totals include the Comparator challenge, theorem checks and cache utilities. Lake dependencies are excluded. All percentages below use the repository totals unless otherwise indicated. [Baseline source](https://github.com/mmmbeer/riemann-hypothesis/tree/7bf5b5d67b5369f0fdf403a11f5bae67515c6772)

| Priority | Change | Measured scope | What the evidence establishes |
| --- | --- | ---: | --- |
| 1 | Fold helper modules into their only importer in the same directory | 60,482 fewer files, leaving 78,346 | The proposed import graph is acyclic. Every surviving proof group remains reachable from Main. The JetHarmonics pilot tests this change in Lean. |
| 2 | Find a shorter proof of `UpperTheory.FinalTheorems.everyCharacter_of_row` | 8,215,997 matching declaration lines (49.98%) | In the original compiled proof, every path from the five endpoints to these declarations passes through this theorem. A replacement must prove the same result from the same row hypothesis. |
| 3 | Prune commands outside the original five-theorem kernel dependency graph | 222,198 declarations spanning 2,134,480 lines (12.99%) in matching source bodies | The screen excludes declarations with a shared auxiliary used by the proof. Some candidates still supply notation, elaboration, tactics or instances needed to compile. |
| 4 | Replace repeated statements and fully expanded signatures | Upstream bounds identical-statement savings at 606,437 lines in the original used declarations. The fork pilot saves 2,432 lines in one file. | Equivalent public types can be checked individually against their original source. Visibility and import cycles limit reuse across modules. |

The rows use different units and overlap. In particular, folding a file keeps its declarations. The line counts for mathematical replacements measure existing code, before the cost of a new proof.

## File consolidation

The original submission contained 175,187 proof modules. Earlier work on this fork had already consolidated aliases, removed unreachable modules and shortened imports. The 60,482 proposed folds are measured after those changes. [Upstream verification notes](https://github.com/leanprover-community/riemann-hypothesis/blob/9266b88245feaf2906ebba592613dd8098b0e8f6/verification/NOTES.md) · [Previous release measurements](release-verification.json)

Of the modules reached by Main, 79,113 have one direct importer. The plan considers only dependencies in the same directory as that importer. It packs smaller dependencies first and limits a changed file to 16 original modules and 1,600 original lines. It keeps the entry points, BuildAid and modules detected as containing syntax extensions, initializers, command elaborators, inspection commands or explicit private-name references in their own files. The result has 15,850 multi-file groups. AbelianVarietyTheory accounts for 34,143 folds, AutomorphicArithmetic for 7,736 and AutomorphicSpectrum for 4,287.

After applying the two pilot folds, the branch has **138,826 tracked Lean files**. Rerunning the same planner on the pilot source tree identifies **60,480 further folds (43.57%)**, again leaving 78,346 files. The post-pilot plan digest is `0a9c9daaf6d751a1704c968658ec54e038d5bb9f3c2c369121780b384cb6997d`.

A grouped source file must retain the scopes of its original declarations. Private-name collisions, local notation, instance ordering and tactic resolution can all require edits. An importer outside this repository that uses a retired module path would also need to change its import. The count assumes those paths can be retired. It makes no prediction about wall-clock build time.

The pilot moves `SideSucc` and `ProdLeOfInterlacingPairing` into `InterlacedShiftedDistanceBracketBound`. The two helpers and their caller already use the same Finset scope. Their theorem names, statements and proof commands are preserved. The three files contain 250 lines before the move and one file contains 243 after it. The direct consumer is `TwoBracketsLePowMulProdEntries`.

## Mathematical replacements

Shore's v0.2 dataset records which declarations dominate others in the original kernel export. A declaration dominates another when every dependency path from the five public theorems passes through it. I counted a source range on this fork only if the original file's entire body after its import header appears byte-for-byte at the same path. This matched 137,576 file bodies. Moved or partially rewritten bodies receive no credit. The fork's own compiled dependency graph could differ from the original. [Dataset and method](https://github.com/james-shore/rh-proof-dependencies/blob/464c8989e1473b42efc872f897e242afc8114ac3/README.md)

| Theorem to replace | Matching lines behind it on the fork | What its caller needs |
| --- | ---: | --- |
| `everyCharacter_of_row` | 8,215,997 | Derive `EveryCharacter` from `Row0b`. The current proof constructs the literature inputs and obtains the window bound from the row. |
| `every_character_of_literature_of_vWin` | 7,087,610 | Supply `EveryCharacter` from `OpenLiteratureStatements` and the character window bound. The current proof assembles the theta-matching and covolume inputs. |
| `every_character_of_theta_integrals_local_matching` | 4,197,620 | Discharge the theta-matching step on the same path. |
| `nonempty_hyps_definite_side_of_closed_bound` | 3,534,227 | Construct the definite-side hypotheses used by theta matching. |

These regions are nested. A 43% net line reduction requires removing 7,067,904 lines. The first region leaves a budget of 1,148,093 lines for code retained or added if all the other counted lines can be removed. The second leaves only 19,706 lines. A shorter proof of the row implication has the stronger margin. The two-line source of that implication is already an application of another theorem. Changing its spelling saves essentially nothing. [Row implication](https://github.com/mmmbeer/riemann-hypothesis/blob/7bf5b5d67b5369f0fdf403a11f5bae67515c6772/src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean) · [Upstream proof map and corrections](https://github.com/leanprover-community/riemann-hypothesis/issues/5)

## Smaller changes with direct checks

- Start declaration pruning in `Development/AbelianVarietyTheory` (845,801 candidate lines), followed by `Formalism/LocalToGlobal` (183,651) and `GroundTheory/HeightsAndTheta` (155,230). Rebuild affected importers. The earlier text-based trim missed dependencies through dot notation, typeclass synthesis and open declarations. [Upstream issue 3, correction](https://github.com/leanprover-community/riemann-hypothesis/issues/3#issuecomment-7053198266)
- In `FreeModuleQuotient.lean`, the public theorem restated its private helper's signature with thousands of explicit typeclass arguments. Giving the public theorem its ordinary quotient-module statement and the helper's proof takes the file from 2,516 lines to 84. The same directory contains an approximately 8,000-line signature for `Gr34.mem_UC` in `FixPiIff.lean`. The `Uc13.aux4` signature in `MulMemIntA.lean` occupies 2,647 lines before a reflexivity proof. These are concrete next candidates.
- Preserve all five endpoints. Each alone uses at least 804,889 of the original 804,912 used project declarations. The conductor-one alternative in upstream PR 12 assumes two open geometric hypotheses and covers ordinary RH. It cannot replace the unconditional Dirichlet results. [Kernel dependency counts](https://github.com/james-shore/rh-proof-dependencies/blob/464c8989e1473b42efc872f897e242afc8114ac3/README.md) · [Conductor-one reduction](https://github.com/leanprover-community/riemann-hypothesis/pull/12)
- The fork has already narrowed Main's import and removed the `plugAll` and `everyE₂` side route. Upstream PRs 4, 9 and 10 cover import minimization, repeated imports and generated tactic fallbacks. PR 4 documents elaboration dependencies that disappear from compiled proof terms. [PR 4](https://github.com/leanprover-community/riemann-hypothesis/pull/4) · [PR 8](https://github.com/leanprover-community/riemann-hypothesis/pull/8) · [PR 9](https://github.com/leanprover-community/riemann-hypothesis/pull/9) · [PR 10](https://github.com/leanprover-community/riemann-hypothesis/pull/10)

## Reproduce the counts

With Python 3.11 or newer, run the following command from this fork. The optional TSV has one row per proposed source module and its immediate importer. On the baseline its SHA-256 is `b601d306b089f24c0c13ee3553ce5e3f2e1b449a4c70cfd1b5a6da9f194329fe`.

```sh
python3 verification/simplification/module-folds.py 7bf5b5d67b5369f0fdf403a11f5bae67515c6772 --plan /tmp/module-folds.tsv
```

For the declaration counts, use clean source checkouts of the baseline and original `40e56bab026552e089d7afcfeff08d2defb9c005`. Place `decls.csv.gz` and `dominators.tsv.gz` from release v0.2 in one directory. The script verifies the asset digests. [Release assets](https://github.com/james-shore/rh-proof-dependencies/releases/tag/v0.2)

```sh
python3 verification/simplification/measure-proof-regions.py /path/to/baseline /path/to/original /path/to/v0.2
```

## Check the pilot

The target build uses Lean 4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Building the second target also compiles the combined interlacing module. The existing consumer reports two unused `beta_reduce` tactics. Lean accepted both changed modules and the direct bracket consumer. It closed the comparison with the original quotient theorem type by `rfl`. The original expanded type triggers unused-binder warnings in the comparison file. The quotient theorem, the five interlacing theorems and the downstream bracket theorem each reported exactly `propext`, `Classical.choice` and `Quot.sound`. The complete Main build and five-endpoint axiom audit remain pending.

```sh
export LEAN_ABORT_ON_PANIC=1 LAKE_ARTIFACT_CACHE=false
lake build Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FreeModuleQuotient \
  Development.AbelianVarietyTheory.Proofs.JetHarmonics.TwoBracketsLePowMulProdEntries
```

To compare the compact public theorem with its full original type, extract that type directly from Git. Lean must close the equality by reflexivity.

```sh
python3 - <<'PY' > /tmp/CheckQuotient.lean
import subprocess
module = "Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FreeModuleQuotient"
path = "src/" + module.replace(".", "/") + ".lean"
baseline = "7bf5b5d67b5369f0fdf403a11f5bae67515c6772"
old = subprocess.check_output(["git", "show", f"{baseline}:{path}"], text=True)
name = "UpperTheory.Reformulated.B.FreeModuleQuotient.freeN_quot"
old_type = old.split(f"theorem {name} :\n", 1)[1].rsplit(" := by\n", 1)[0]
print(f"import {module}")
print("set_option autoImplicit false\nset_option maxHeartbeats 4000000\nset_option maxRecDepth 16384")
print(f"example : (type_of% @{name}) = (\n{old_type}) := rfl")
print(f"#print axioms {name}")
PY
lake env lean /tmp/CheckQuotient.lean
```
