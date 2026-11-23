# riemann-hypothesis

[![checks](https://github.com/leanprover-community/riemann-hypothesis/actions/workflows/checks.yml/badge.svg)](https://github.com/leanprover-community/riemann-hypothesis/actions/workflows/checks.yml)

A community-led effort to clean up and maintain a Lean formalization of the 2026 proof of the Riemann Hypothesis and of GRH for Dirichlet L-functions.

The purpose of this repo is to create an artifact that is:

- **accessible**: we want to improve build performance and modularity to enable researchers to feasibly engage with the proof even without access to massive amounts of compute.
- **readable**: we want to improve code quality while preserving the "logic" of the proof, aspirationally to Mathlib levels. This includes lemma organization, formatting and idiomatic style, eliminating linter warnings, slop-free documentation, and more.
- **integrated with the community**: we would like to add bibliographic references to prior work where appropriate, and rely on existing formalization projects when possible.

Please note: we are **not** looking for:

- complete overhauls that follow a substantially different proof path
- claims about your own machine's builds / comparator run
- adding files which are not necessary for the Riemann Hypothesis proof

This work is taking place on the `main` branch. The `original` branch preserves the first publicly-released version of the proof retrieved on 2026-11-20 from <https://alpo.ge/remark.pdf>.

If you want to open the original proof without compiling it, use
[riemann-hypothesis-original](https://github.com/homeowmorphism/riemann-hypothesis-original).
It keeps the published Lean source unchanged and provides a prebuilt cache for it.

## Theorem Statements

`src/Main.lean` proves the following theorems:

| Theorem | Statement |
|---|---|
| `riemannHypothesis` | Mathlib's `RiemannHypothesis` |
| `riemannZeta_eq_zero_re` | An equivalent restatement of the Riemann Hypothesis not reliant on Mathlib directly: every zero of the Riemann Zeta function with 0 < Re s < 1 has Re s = 1/2 |
| `LFunction_ne_zero_of_half_lt_re` | L(χ, s) ≠ 0 for Re s > 1/2, for every modulus and every Dirichlet character, except the trivial character at s = 1 |
| `LFunction_eq_zero_re` | every zero of L(χ, s) with 0 < Re s < 1 has Re s = 1/2 |
| `LFunction_eq_zero_re_of_isPrimitive` | every zero of L(χ, s) for a Primitive Dirichlet character χ with 0 < Re s < 1 has Re s = 1/2 |

[`src/Challenge.lean`](src/Challenge.lean) states the same five with `sorry` in place of the proofs, in a file that imports only Mathlib. Comparator checks that `Main.lean` proves exactly those statements, that it uses no axioms other than `propext`, `Quot.sound` and `Classical.choice`, and that Lean's kernel and nanoda both accept the proof.

## Cache

A full build takes hours, so you should use the cache:

```bash
lake exe cache get
lake build --no-build
```

A full build makes Lean check every proof on your machine. The cache downloads files that were compiled elsewhere, so you can read and edit the project within minutes, but Lean does not re-check them.

## Checking the proof yourself

Take a fresh clone on a Linux machine with
[bubblewrap](https://github.com/containers/bubblewrap) installed and run:

```bash
MATHLIB_CACHE_GET_URL=https://cache.mathlib.org/mathlib4 lake exe mathlib/cache get
lake comparator
```

The first command fetches Mathlib's compiled files and nothing of ours. Don't use `lake exe cache get` here, because that also downloads our prebuilt copy of the submission. The second reads `comparator.json`, builds `Challenge` and `Main` in a sandbox with no network, and makes the checks described under [Theorem Statements](#theorem-statements).

Compiling the submission runs its code, so you may want to do it in a VM or your own sandbox. To do that, fetch Mathlib's cache as above, then run the check in three steps:

```bash
export LEAN_ABORT_ON_PANIC=1        # as Comparator does
export LAKE_ARTIFACT_CACHE=false    # in case cache-env.sh was sourced

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

The published source uses Lean 4.33.1, which has neither `lake comparator` nor `leanexport`.
[An older version of this README](https://github.com/leanprover-community/riemann-hypothesis/blob/7cce738ba719a32964ca3822d0994f4c6952c7ae/README.md#checking-it)
has the two-toolchain steps for checking it.

## Known limitation: quotient replay in exported-proof verification

[Lean issue #15643](https://github.com/leanprover/lean4/issues/15643) reports a discrepancy between normal Lean proof checking and the verification of exported declarations using `leanchecker --from-export`.

In particular, the issue reports that Lean accepts the following theorem by reflexivity, while the exported proof is rejected with an unknown-constant error for `Quot.lift`:

```lean
theorem a_append : Quot.lift (· + 1) h (Quot.mk Eq 4) = 5 := rfl
```

The reported error is:

```text
(kernel) unknown constant 'Quot.lift'
```

### Relevance to this repository

This repository uses Comparator to verify exported proof artifacts. Its configuration includes `leanchecker-paranoid --from-export` as an external checker, alongside nanoda.

The quotient case reported in issue #15643 is therefore relevant to the verification infrastructure used by this project. The repository is pinned to Lean `v4.37.0-rc1`, whose [`Lean/Replay.lean`](https://github.com/leanprover/lean4/blob/v4.37.0-rc1/src/Lean/Replay.lean) implementation contains special replay handling for string-literal dependencies but does not contain equivalent explicit handling for quotient-generated constants.

The reported behavior appears consistent with a replay-ordering problem. Quotient declarations generate constants such as `Quot.mk`, `Quot.lift` and `Quot.ind`. If an exported declaration refers to one of these generated constants before the quotient package has been installed in the reconstructed kernel environment, the checker may fail to resolve that reference.

### Potential verification impact

This behavior can produce a **false negative in exported-proof verification**: a declaration accepted by Lean during normal compilation may be rejected by the export checker because the replay environment has not reconstructed the required constants at the point where they are needed.

This is a limitation in the verification tooling, not evidence that the mathematical proof is invalid. It does not demonstrate a kernel soundness failure, nor does it indicate that an invalid theorem has been accepted.

The string-literal component of issue #15643 was addressed separately in [Lean PR #15853](https://github.com/leanprover/lean4/pull/15853). The quotient-related reproducer is also documented in the original issue.

**Scope and current evidence.** We have not demonstrated that the current exported Riemann Hypothesis or Generalized Riemann Hypothesis declarations trigger this exact quotient replay failure. This note records a potential limitation relevant to the verification toolchain; it does not claim that the current proof has failed verification. The quotient reproducer should be tested against the exact checker versions and export configuration used by this repository before any conclusion is drawn about its current proof artifacts.

### Attribution

The original Lean issue and its initial reproducer were reported by Leo0506 in [Lean issue #15643](https://github.com/leanprover/lean4/issues/15643).

The connection between this replay limitation and the Comparator-based verification workflow of this repository was identified by **Lunz Research Group**.

The technical analysis, candidate-fix investigation and documentation were prepared with assistance from **ChatGPT (OpenAI)**. This AI assistance is disclosed for transparency.

## The formal-conjectures statement

[`comparator/`](comparator/) holds a second Comparator setup. Its challenge states the Riemann Hypothesis and the Generalized Riemann Hypothesis the way
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/d8d031d4998c78575159ccab9a7a9e95ce043883/FormalConjectures/Millennium/RiemannHypothesis.lean)
does, in statements that neither the author nor we wrote, and the files next to it prove them from `src/Main.lean`. [NOTES.md](verification/NOTES.md#formal-conjectures) says how to check it and what has been checked so far.

## CI

To lend a Linux machine with plenty of memory and disk, see
[CI-RUNNERS.md](verification/CI-RUNNERS.md). The CI scripts are in [`scripts/`](scripts/) and
[`tools/ci_native/`](tools/ci_native/README.md).

## License

The submission belongs to its author and was published without a license. It is mirrored here so that it can be checked. Commit `40e56bab` is the unmodified copy.

The declarations in `comparator/` that are copied from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) are copyright The Formal Conjectures Authors, under the [Apache License 2.0](https://www.apache.org/licenses/LICENSE-2.0).
The files that hold them carry the notice.
