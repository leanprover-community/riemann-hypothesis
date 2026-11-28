import Statements
import FormalConjecturesStatement
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# From the submission's Dirichlet statement to formal-conjectures' GRH

This file is not part of the submission. It was written by the people checking it, and it does
not import the submission's proofs: only `Statements.lean`, Mathlib, and the declarations
copied from formal-conjectures in `FormalConjecturesStatement.lean`.

[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) states the
Generalized Riemann Hypothesis as `GRH.generalized_riemann_hypothesis`, for every non-trivial
zero of a primitive Dirichlet L-function in the whole plane. The submission's
`PrimitiveDirichletLZerosOnLine` speaks only of the critical strip. This file proves that the
two are equivalent, so that `FormalConjecturesSolution.lean` can prove the formal-conjectures
theorem from the submission's.

* `mem_trivialZeros_of_re_nonpos` is the key step: for primitive `χ`, a zero with `Re s ≤ 0` is
  one of formal-conjectures' trivial zeros. It uses the functional equation for the primitive
  character `χ⁻¹` and the non-vanishing of `L(χ⁻¹, ·)` on `Re ≥ 1`. The root number is never
  needed.
* `generalized_riemann_hypothesis_of_primitive` is the direction the solution uses. After its
  first hypothesis, its signature is the statement of formal-conjectures' theorem, as written
  there, and `FormalConjecturesSolution.lean` takes its own statement from this signature. The
  statement is written in this file so that Lean elaborates it with nothing of the submission
  imported but `Statements.lean`: instances declared by the submission cannot change what it
  means.
* `primitiveDirichletLZerosOnLine_iff` is the equivalence.

The GRH statement is Salvatore Mercuri's, from formal-conjectures, which is under the Apache 2.0
license: see `FormalConjecturesStatement.lean`. The proof is adapted from
[issue #34](https://github.com/leanprover-community/riemann-hypothesis/issues/34), by
`gh-dv-openclaw`.
-/

set_option autoImplicit false

open Complex DirichletCharacter

namespace FormalConjecturesBridge

/-- formal-conjectures' GRH as a proposition, for stating the equivalence. -/
def GeneralizedRiemannHypothesis : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ s : ℂ, χ.LFunction s = 0 → s ∉ Int.cast '' GRH.trivialZeros χ → s.re = 1 / 2

section

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

omit [NeZero q] in
lemma isPrimitive_inv (hχ : χ.IsPrimitive) : χ⁻¹.IsPrimitive := by
  rw [isPrimitive_def, conductor_inv]
  exact hχ

lemma ne_one_of_isPrimitive (hχ : χ.IsPrimitive) (hq : q ≠ 1) : χ ≠ 1 := by
  rintro rfl
  rw [isPrimitive_def, conductor_one] at hχ
  exact hq hχ.symm

/-- At a zero, `s ≠ 0 ∨ q ≠ 1`: for `q = 1` the L-function is `ζ`, and `ζ(0) = -1/2`. -/
lemma ne_zero_or_ne_one_of_LFunction_eq_zero {s : ℂ} (hs : LFunction χ s = 0) :
    s ≠ 0 ∨ q ≠ 1 := by
  by_contra h
  push Not at h
  obtain ⟨rfl, rfl⟩ := h
  rw [LFunction_modOne_eq, riemannZeta_zero] at hs
  norm_num at hs

/-- For primitive `χ`, the completed L-function does not vanish on `Re s ≤ 0`, away from
`s = 0` when `q = 1`. Apply the functional equation to `χ⁻¹`, which is primitive too, and use
that `L(χ⁻¹, 1 - s) ≠ 0` because `Re (1 - s) ≥ 1`. -/
lemma completedLFunction_ne_zero (hχ : χ.IsPrimitive) {s : ℂ} (hre : s.re ≤ 0)
    (h0 : s ≠ 0 ∨ q ≠ 1) : completedLFunction χ s ≠ 0 := by
  intro hΛ
  have hFE := (isPrimitive_inv hχ).completedLFunction_one_sub s
  rw [inv_inv, hΛ, mul_zero] at hFE
  have hre' : 1 ≤ (1 - s).re := by
    rw [sub_re, one_re]
    linarith
  have h1s : (1 : ℂ) - s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [sub_re, one_re, zero_re] at this
    linarith
  have hL := LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s) (Or.inl h1s)
  rw [hFE, zero_div] at hL
  refine LFunction_ne_zero_of_one_le_re χ⁻¹ ?_ hre' hL
  rcases h0 with h0 | hq
  · right
    intro h
    apply h0
    linear_combination -h
  · left
    rw [Ne, inv_eq_one]
    exact ne_one_of_isPrimitive hχ hq

/-- **Trivial zeros.** For primitive `χ`, every zero of `L(χ, s)` with `Re s ≤ 0` is one of the
trivial zeros listed by formal-conjectures' `GRH.trivialZeros`. -/
lemma mem_trivialZeros_of_re_nonpos (hχ : χ.IsPrimitive) {s : ℂ}
    (hs : LFunction χ s = 0) (hre : s.re ≤ 0) :
    s ∈ (Int.cast '' GRH.trivialZeros χ : Set ℂ) := by
  have h0 := ne_zero_or_ne_one_of_LFunction_eq_zero hs
  have hΛ := completedLFunction_ne_zero hχ hre h0
  have hΓ : gammaFactor χ s = 0 := by
    have h := LFunction_eq_completed_div_gammaFactor χ s h0
    rw [hs, eq_comm, div_eq_zero_iff] at h
    exact h.resolve_left hΛ
  unfold GRH.trivialZeros
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def, Gammaℝ_eq_zero_iff] at hΓ
    obtain ⟨n, rfl⟩ := hΓ
    split_ifs with hq hodd
    · -- `q = 1`: here `n ≠ 0`, because `s = 0` is not a zero of `ζ`
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
        refine Nat.exists_eq_succ_of_ne_zero ?_
        rintro rfl
        simp [hq] at h0
      exact ⟨-2 * ((m : ℤ) + 1), ⟨m, rfl⟩, by push_cast; ring⟩
    · exact absurd hodd he.not_odd
    · exact ⟨-2 * (n : ℤ), ⟨n, rfl⟩, by push_cast; ring⟩
  · rw [ho.gammaFactor_def, Gammaℝ_eq_zero_iff] at hΓ
    obtain ⟨n, hn⟩ := hΓ
    split_ifs with hq
    · -- the character mod 1 is even, so this case cannot occur
      exfalso
      subst hq
      exact absurd (show χ.Even from map_one _) ho.not_even
    · exact ⟨-2 * (n : ℤ) - 1, ⟨n, rfl⟩, by push_cast; linear_combination -hn⟩

/-- For primitive `χ`, `L(χ, s) ≠ 0` on `Re s ≥ 1`, including `s = 1` when `q = 1`: Mathlib's
value for `ζ(1)` is not zero. -/
lemma LFunction_ne_zero_of_one_le_re_of_isPrimitive (hχ : χ.IsPrimitive) {s : ℂ}
    (hre : 1 ≤ s.re) : LFunction χ s ≠ 0 := by
  by_cases hq : q = 1
  · subst hq
    intro hs
    rcases eq_or_ne s 1 with rfl | hs1
    · rw [LFunction_modOne_eq] at hs
      exact riemannZeta_one_ne_zero hs
    · exact LFunction_ne_zero_of_one_le_re χ (Or.inr hs1) hre hs
  · exact LFunction_ne_zero_of_one_le_re χ (Or.inl (ne_one_of_isPrimitive hχ hq)) hre

end

/-- **The submission's primitive statement implies formal-conjectures' GRH**: zeros with
`Re s ≥ 1` do not exist, zeros with `Re s ≤ 0` are trivial, and the rest lie in the strip.

Everything after `h` is the statement of `GRH.generalized_riemann_hypothesis` as
`FormalConjectures/Millennium/RiemannHypothesis.lean` writes it. -/
theorem generalized_riemann_hypothesis_of_primitive (h : PrimitiveDirichletLZerosOnLine)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (s : ℂ) (hs : χ.LFunction s = 0)
    (hs_nontrivial : s ∉ Int.cast '' GRH.trivialZeros χ) :
    s.re = 1 / 2 := by
  rcases lt_or_ge 0 s.re with hpos | hnonpos
  · rcases lt_or_ge s.re 1 with hlt | hge
    · exact h q χ hχ s hpos hlt hs
    · exact absurd hs (LFunction_ne_zero_of_one_le_re_of_isPrimitive hχ hge)
  · exact absurd (mem_trivialZeros_of_re_nonpos hχ hs hnonpos) hs_nontrivial

/-- **Conversely**, formal-conjectures' GRH implies the submission's primitive statement:
trivial zeros are non-positive integers, so none lies in the critical strip. -/
theorem primitive_of_generalizedRiemannHypothesis (h : GeneralizedRiemannHypothesis) :
    PrimitiveDirichletLZerosOnLine := by
  unfold PrimitiveDirichletLZerosOnLine
  intro N _ χ hχ s hpos _ hs
  refine h N χ hχ s hs ?_
  rintro ⟨z, hz, rfl⟩
  have hz0 : z ≤ 0 := by
    unfold GRH.trivialZeros at hz
    split_ifs at hz <;> obtain ⟨n, rfl⟩ := hz <;> omega
  rw [Complex.intCast_re] at hpos
  have : (z : ℝ) ≤ 0 := by exact_mod_cast hz0
  linarith

/-- The submission's `PrimitiveDirichletLZerosOnLine` is equivalent to formal-conjectures'
GRH. -/
theorem primitiveDirichletLZerosOnLine_iff :
    PrimitiveDirichletLZerosOnLine ↔ GeneralizedRiemannHypothesis :=
  ⟨fun h q _ χ hχ s hs hnt ↦ generalized_riemann_hypothesis_of_primitive h q χ hχ s hs hnt,
    primitive_of_generalizedRiemannHypothesis⟩

end FormalConjecturesBridge
