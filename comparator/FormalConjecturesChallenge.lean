/-
Copyright 2025 The Formal Conjectures Authors.
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

The declarations in this file are copied from two files of formal-conjectures, named below.
Three things are changed: the instance is given a name, `trivialZeros` is marked
`noncomputable`, and formal-conjectures' own `category` and `AMS` attributes are left out.
-/
module

public import Mathlib

/-!
# The formal-conjectures challenge

This file is not part of the submission, and it imports nothing but Mathlib. It is the
challenge of the second Comparator setup, `comparator/formal-conjectures.json`: the Riemann
Hypothesis and the Generalized Riemann Hypothesis as
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) states them, in
`FormalConjectures/Millennium/RiemannHypothesis.lean` at commit
`d8d031d4998c78575159ccab9a7a9e95ce043883`.

The declarations are copied from there, and from the one other file of formal-conjectures that
the statement of GRH depends on. This file is a copy, and does not import formal-conjectures,
because Comparator needs the challenge and the solution built against the same Mathlib, and
formal-conjectures follows its own. CI checks the copy against the text at that commit.

They are the work of the formal-conjectures authors, under the license above. Salvatore Mercuri
wrote `GRH.trivialZeros`, the theorem `GRH.generalized_riemann_hypothesis` and the instance in
November 2025, in formal-conjectures pull requests
[1176](https://github.com/google-deepmind/formal-conjectures/pull/1176) and
[1184](https://github.com/google-deepmind/formal-conjectures/pull/1184); mirefek corrected the
docstring of `trivialZeros` in
[1677](https://github.com/google-deepmind/formal-conjectures/pull/1677); and franzhusch added
`riemannHypothesis` in
[2378](https://github.com/google-deepmind/formal-conjectures/pull/2378).
`verification/NOTES.md` has the rest of the history.

The file is frozen: a pull request that changes it fails CI.

Like the files it copies from, this file uses Lean's module system. That matters for the proof
`by rfl` in the instance: in a `module`, Lean states the constant it becomes as
`ψ (-1) = -1 ↔ ψ.Odd`, as in formal-conjectures, and elsewhere as `ψ (-1) = -1 ↔ ψ (-1) = -1`.
-/

@[expose] public section

namespace DirichletCharacter

/-- From `FormalConjecturesForMathlib/NumberTheory/DirichletCharacter/Basic.lean`. The instance
has no name there. This is the name Lean generates for it in that file, written out because
Comparator matches constants by name. -/
instance instDecidablePredOddOfDecidableEq_formalConjecturesForMathlib
    {S : Type*} [DecidableEq S] [CommRing S] {m : ℕ} :
    DecidablePred (Odd (S := S) (m := m)) :=
  fun ψ ↦ decidable_of_iff (ψ (-1) = -1) <| by rfl

end DirichletCharacter

namespace RiemannHypothesis

/-- The **Riemann Hypothesis**: all non-trivial zeros of the Riemann zeta function have real
part $\frac{1}{2}$. That is, if $\zeta(s) = 0$, $s \neq 1$, and $s$ is not a trivial zero
$-2(n+1)$ for some $n \in \mathbb{N}$, then $\operatorname{Re}(s) = \frac{1}{2}$.

This is the official Millennium Prize Problem as posed by the
[Clay Mathematics Institute](https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf).

This uses the `RiemannHypothesis` type from Mathlib, which is defined as
`∀ (s : ℂ), riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re = 1 / 2`. -/
theorem riemannHypothesis : RiemannHypothesis := by
  sorry

end RiemannHypothesis

namespace GRH

/-- Let $\chi$ be a Dirichlet character, `trivialZeros` is the set of trivial zeros of the
Dirichlet $L$-function of $\chi$ which is always a set of non-positive integers.
- $\chi = 1$ then the Dirichlet $L$-function is the Riemann zeta function, having trivial
  zeroes at all negative even integers (exclude $0$).
- $\chi$ is odd, then the trivial zeroes are the negative odd integers.
- $\chi \neq 1$ is even, then the trivial zeroes are the non-positive even integers. -/
noncomputable def trivialZeros {q : ℕ} (χ : DirichletCharacter ℂ q) : Set ℤ :=
  if q = 1 then {-2 * (n + 1) | (n : ℕ) } else
    if χ.Odd then { -2 * n - 1 | (n : ℕ) } else
      { - 2 * n | (n : ℕ) }

/-- The **Generalized Riemann Hypothesis** asserts that all the non-trivial zeros of the
Dirichlet $L$-function $L(\chi, s)$ of a primitive Dirichlet character $\chi$ have real part
$\frac{1}{2}$. -/
theorem generalized_riemann_hypothesis (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (s : ℂ) (hs : χ.LFunction s = 0)
    (hs_nontrivial : s ∉ Int.cast '' trivialZeros χ) :
    s.re = 1 / 2 := by
  sorry

end GRH
