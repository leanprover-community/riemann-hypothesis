module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Lib.General.LinearAlgebra.IntegralLattices
import TauCeti.RepresentationTheory.SingularMinor

/-!
# Functions of positive type and singular minors

A function `Θ` on a finite group `G` is of positive type if `Θ (a⁻¹ * b) = ⟪u a, u b⟫` for some
vectors `u a` of a complex inner product space. This file delegates the Gram sum identity and the
singular minor mass bound to `TauCeti.GroupTheory.PositiveDefinite.GramSum` and
`TauCeti.RepresentationTheory.SingularMinor`.

## Main definitions and results

* `New.inner_sum_sum_eq_card_mul`: `⟪∑ a, u a, ∑ a, v a⟫ = |G| · ∑ s, f s` when
  `⟪u a, v b⟫ = f (a⁻¹ * b)`.
* `New.card_mul_sum_det_eq_zero_le`: bounds the `Θ`-mass of `{s | det (A₁ᵀ π(s) A₀) = 0}` by
  `(2 Θ(G) + q ^ (|m| + |n| / 2) Y) / q`.

## Relation to the literature

See `New.Spanning.Unfolding.Moments` for related work.
-/

@[expose] public section

open scoped BigOperators
open InnerProductSpace Finset Matrix

namespace New

variable {G H k n m : Type*} [Group G] [Fintype G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [Field k] [Fintype n] [DecidableEq n] [Fintype m] {u : G → H}

/-- If the inner product of two families of vectors indexed by a finite group `G` has the form
`⟪u a, v b⟫ = f (a⁻¹ * b)`, then `⟪∑ a, u a, ∑ a, v a⟫ = |G| · ∑ s, f s`. -/
lemma inner_sum_sum_eq_card_mul {v : G → H} (f : G → ℂ)
    (h : ∀ a b : G, ⟪u a, v b⟫_ℂ = f (a⁻¹ * b)) :
    ⟪∑ a : G, u a, ∑ a : G, v a⟫_ℂ = Fintype.card G * ∑ s : G, f s :=
  TauCeti.inner_sum_sum_eq_card_mul_sum f h

/-- Let `π` be a representation of a finite group `G` by `n × n` matrices over a field with `q`
elements, and let `π' s` be the inverse transpose of `π s`. Let `A₀` and `A₁` be two `n × m`
matrices, and let `Θ ≥ 0` be of positive type: `Θ (a⁻¹ * b) = ⟪u a, u b⟫`. Suppose that, for every
`v ≠ 0`, each of two sums of `Θ` is at most `Y ≥ 0`: the sum over the `s` with `π s` fixing `A₀ v`,
and the sum over the `s` with `π' s` fixing `A₁ v`. Then `q · Θ {s | det (A₁ᵀ π(s) A₀) = 0} ≤ 2
Θ(G) + q ^ (|m| + |n| / 2) Y`. -/
lemma card_mul_sum_det_eq_zero_le [DecidableEq m] [Fintype k] [DecidableEq k] (π : G →* GL n k)
    (A₀ A₁ : Matrix n m k) {Θ : G → ℝ} (hΘ : ∀ s : G, 0 ≤ Θ s)
    (hu : ∀ a b : G, ⟪u a, u b⟫_ℂ = Θ (a⁻¹ * b)) (Y : ℝ) (hY : 0 ≤ Y)
    (h_fix₀ : ∀ v : m → k, v ≠ 0 → ∑ s : G with A₀ *ᵥ v = π s • A₀ *ᵥ v, Θ s ≤ Y)
    (h_fix₁ : ∀ v : m → k, v ≠ 0 →
      ∑ s : G with A₁ *ᵥ v = invTransposeGL (π s) • A₁ *ᵥ v, Θ s ≤ Y) :
    Fintype.card k * ∑ s : G with (A₁ᵀ * (π s).val * A₀).det = 0, Θ s ≤
      2 * ∑ s : G, Θ s +
        Fintype.card k ^ Fintype.card m * √(Fintype.card k ^ Fintype.card n) * Y := by
  have h_row (g : GL n k) (x : n → k) :
      x ᵥ* (g : Matrix n n k) = x ↔ x = invTransposeGL g • x := by
    have hinv : (invTransposeGL g • x) = x ᵥ* (g⁻¹ : Matrix n n k) := by
      simp [invTransposeGL, transposeGL, Units.smul_def, mulVec_transpose]
    rw [hinv]
    exact ⟨fun h ↦ by simpa [vecMul_vecMul] using congrArg (· ᵥ* (g⁻¹ : Matrix n n k)) h,
      fun h ↦ by simpa [vecMul_vecMul] using congrArg (· ᵥ* (g : Matrix n n k)) h⟩
  simpa only [Nat.cast_pow] using TauCeti.PositiveType.card_mul_sum_det_eq_zero_le π A₀ A₁ hΘ hu hY
    (fun v hv ↦ by simpa only [Units.smul_def, Matrix.smul_eq_mulVec, eq_comm] using h_fix₀ v hv)
    (fun v hv ↦ by simpa only [h_row] using h_fix₁ v hv)

end New
