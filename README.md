# riemann-hypothesis

[![checks](https://github.com/leanprover-community/riemann-hypothesis/actions/workflows/checks.yml/badge.svg)](https://github.com/leanprover-community/riemann-hypothesis/actions/workflows/checks.yml)

A community-led effort to clean up and maintain a Lean formalization of the 2026 proofs of the Riemann Hypothesis and of GRH for Dirichlet L-functions.

> [!CAUTION]
> This repo moved suddenly to a highly condensed version recently, on November 25, 2026. Prior progress is preserved on the `alpoge` branch.

The purpose of this repo is to create an artifact that is:

- **accessible**: we want to improve build performance and modularity to enable researchers to feasibly engage with the proof even without access to massive amounts of compute.
- **readable**: we want to improve code quality, aspirationally to Mathlib levels. This includes lemma organization, formatting and idiomatic style, eliminating linter warnings, slop-free documentation, and more.
- **integrated with the community**: we would like to add bibliographic references to prior work where appropriate, and rely on existing formalization projects when possible.

Please note: we are **not** looking for:

- claims about your own machine's builds / comparator run
- adding files which are not necessary for the Riemann Hypothesis proof

This work is taking place on the `main` branch, which is based on a copy of the readable
edition (`grh/`) of https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207.

The `alpoge` branch retains the progress the community made towards cleaning up the original version of the proof released by Levent Alpöge in the first few days before the aforementioned readable edition was released.

The `original` branch preserves the first publicly-released version of the proof retrieved on 2026-11-20 from <https://alpo.ge/remark.pdf>.

If you want to open the original proof without compiling it, see the repo
[riemann-hypothesis-original](https://github.com/homeowmorphism/riemann-hypothesis-original).
It keeps the published Lean source unchanged and provides a prebuilt cache for it.

## Theorem Statements

`src/Main.lean` proves the following theorems:

| Theorem | Statement |
|---|---|
| `riemannHypothesis` | Mathlib's `RiemannHypothesis` |
| `riemannZeta_eq_zero_re` | the same statement as `riemannHypothesis`, spelled out without Mathlib |
| `LFunction_ne_zero_of_half_lt_re` | L(χ, s) ≠ 0 for Re s > 1/2, for every modulus and every Dirichlet character, except the trivial character at s = 1 |
| `LFunction_eq_zero_re` | every zero of L(χ, s) with 0 < Re s < 1 has Re s = 1/2 |
| `LFunction_eq_zero_re_of_isPrimitive` | the special case of `LFunction_eq_zero_re` for primitive characters |

[`Challenge.lean`](Challenge.lean) states the same five with `sorry` in place of the
proofs, in a file that imports only Mathlib. Comparator checks that `Main.lean` proves exactly those statements, that it uses no axioms other than `propext`, `Quot.sound` and
`Classical.choice`, and that Lean's kernel and nanoda both accept the proof.

## Cache

```
lake exe cache get
lake build
```

This needs Python 3.11 or newer and curl 7.71 or newer. (No credentials are necessary.) It fetches Mathlib's cache, then this project's, and unpacks it. `lake exe mathlib/cache get` fetches Mathlib alone.

See [`CACHE.md`](CACHE.md) for details.

## Checking the proof yourself

Take a fresh clone on a Linux machine with
[bubblewrap](https://github.com/containers/bubblewrap) installed and run:

```bash
MATHLIB_CACHE_GET_URL=https://cache.mathlib.org/mathlib4 lake exe mathlib/cache get
lake comparator
```

The first command fetches Mathlib's compiled files and nothing of ours. Don't use
`lake exe cache get` here, because that also downloads our prebuilt copy of the submission. The
second reads `comparator.json`, builds `Challenge` and `Main` in a sandbox with no network, and
makes the checks described under [Theorem Statements](#theorem-statements).

Compiling the submission runs its code, so you may want to do it in a VM or your own sandbox. To do that, fetch Mathlib's cache as above, then run the check in three steps:

```bash
export LEAN_ABORT_ON_PANIC=1        # as Comparator does
export LAKE_ARTIFACT_CACHE=false    # compile everything; read nothing from a Lake cache

# in a clone where the submission has not been compiled
lake build Challenge
lake env leanexport Challenge -- $(cat export-targets.txt) > challenge.export

# wherever you build the submission
lake build Main
lake env leanexport Main -- $(cat export-targets.txt) > solution.export

# from an empty directory, with the same Lean release and comparator.json from the first clone
lake comparator --config comparator.json \
  --challenge-from-export challenge.export --solution-from-export solution.export
```

## CI

To lend a Linux machine with plenty of memory and disk, see
[CI-RUNNERS.md](verification/CI-RUNNERS.md). To assemble a batch of pull requests by hand, or
to resolve a pull request's conflict with the batch being built (`batch-conflict`), see
[BATCHES.md](verification/BATCHES.md). The CI scripts are in [`scripts/`](scripts/).

## Layout

*For now, this section is copied from https://github.com/lsernau/grh-lean. It is subject to change.*

About 300,000 lines of code; 433,000 non-blank lines with comments; 477,000 lines in all.
- `src/Lib` (495 files): background results, classed as known in the literature, that Mathlib lacks, with the steps of their proofs. It imports nothing from `src/New`.
- `src/New` (306 files): the set-up and the steps of the argument, in folders that follow its order. The main inequality is in `src/New/Reduction/MainInequality.lean`, the theorem in half-plane form in `src/New/Reduction/OneSidedBound.lean`.
- `src/Lib/Speed.lean` holds the main settings that apply to the whole development (instance priorities, `simp` lemmas taken out of the default set, one added `simp` lemma). With the file emptied, everything still compiled on Lean 4.33.1. `GUIDE.md` explains them.
- `GUIDE.md`: start here. It gives the reading order, a glossary, sizes and conventions. `CONTENTS.md`: every file with its title. `INDEX.md`: the results, with sources or related work and files.
- `REFERENCES.md` lists the citations and says which were compared with their sources.

## License

The proof belongs to its author Levent Alpöge with Claude and was originally published without a license. The repo https://github.com/lsernau/grh-lean uses Apache 2.0, and so does this repo; see [`LICENSE`](LICENSE.md), [`NOTICE`](NOTICE.md) and [`ATTRIBUTION.md`](ATTRIBUTION.md).

*Soon, we will re-integrate Formal Conjectures.*

The declarations in `comparator/` that will be copied from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) are copyright The Formal
Conjectures Authors, under the [Apache License 2.0](https://www.apache.org/licenses/LICENSE-2.0).
The files that hold them carry the notice.
