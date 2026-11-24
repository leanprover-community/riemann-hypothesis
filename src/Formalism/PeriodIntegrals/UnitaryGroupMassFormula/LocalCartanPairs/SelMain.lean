module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalCartanPairs.SelCore
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open Matrix

namespace PI.SqPair.LCP

variable {R : Type} [CommRing R] [IsDomain R]

theorem sel_main (σ : R ≃+* R) (ϖ : R) (hϖ0 : ϖ ≠ 0) (hϖ : ¬ IsUnit ϖ) (hσϖ : σ ϖ = ϖ)
    (hval : ∀ x : R, x ≠ 0 → ∃ n : ℕ, ∃ u : R, IsUnit u ∧ x = ϖ ^ n * u)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A A' h : Matrix ι ι R) (hA : IsUnit A.det) (hA' : IsUnit A'.det) (k : ℕ)
    (hrel : (h.map σ)ᵀ * A * h = ϖ ^ (2 * k) • A') :
    ∃ (m : ℕ) (h₁ : Matrix ι ι R), h = ϖ ^ m • h₁ ∧ m ≤ k ∧
      (h₁.map σ)ᵀ * A * h₁ = ϖ ^ (2 * (k - m)) • A' ∧
      ((m = k ∧ IsUnit h₁.det) ∨
       (m < k ∧ ∃ (g₁ : Matrix ι ι R) (j : ι) (y : ι → R),
          g₁ * h₁ = ϖ ^ (2 * (k - m)) • 1 ∧ h₁ * g₁ = ϖ ^ (2 * (k - m)) • 1 ∧
          (∃ i, IsUnit ((h₁ *ᵥ Pi.single j 1) i)) ∧
          (fun l => σ ((h₁ *ᵥ Pi.single j 1) l)) ⬝ᵥ (A *ᵥ y) = 1 ∧
          (fun l => σ ((h₁ *ᵥ Pi.single j 1) l)) ⬝ᵥ (A *ᵥ (h₁ *ᵥ Pi.single j 1)) =
            ϖ ^ (2 * (k - m)) * A' j j ∧
          ϖ ^ (2 * (k - m)) • y = h₁ *ᵥ (g₁ *ᵥ y))) := by
  have hc : ∀ n : ℕ, ϖ ^ n ≠ 0 := fun n => pow_ne_zero n hϖ0
  have hh : h ≠ 0 := by
    rintro rfl
    have h0 : ϖ ^ (2 * k) • A' = 0 := by rw [← hrel]; simp
    rcases smul_eq_zero.1 h0 with h2 | h2
    · exact hc _ h2
    · rw [h2, Matrix.det_zero] at hA'
      exact not_isUnit_zero hA'
  obtain ⟨m, h₁, i, j, rfl, hu⟩ := sel_factor ϖ hϖ0 hval h hh
  obtain ⟨hmk, hrel₁⟩ := sel_le σ ϖ hϖ0 hϖ hσϖ A A' h₁ hA' m k hrel
  refine ⟨m, h₁, rfl, hmk, hrel₁, ?_⟩
  rcases Nat.lt_or_ge m k with hlt | hge
  · right
    refine ⟨hlt, ?_⟩
    obtain ⟨hg1, hg2⟩ := sel_inv σ A A' h₁ hA' (hc _) hrel₁
    have hxi : IsUnit ((h₁ *ᵥ Pi.single j 1) i) := by simpa [Matrix.mulVec_single] using hu
    obtain ⟨y, hy⟩ := sel_dual σ A hA (h₁ *ᵥ Pi.single j 1) i hxi
    refine ⟨A'⁻¹ * (h₁.map σ)ᵀ * A, j, y, hg1, hg2, ⟨i, hxi⟩, hy, ?_, ?_⟩
    · rw [sel_form σ A h₁ (Pi.single j 1) (Pi.single j 1), hrel₁]
      have hs : (fun l : ι => σ ((Pi.single j (1 : R) : ι → R) l)) = (Pi.single j 1 : ι → R) := by
        funext l
        by_cases hl : l = j
        · subst hl
          simp
        · simp [Pi.single_apply, hl]
      rw [hs]
      simp [Matrix.mulVec_single, dotProduct, Pi.single_apply]
    · rw [Matrix.mulVec_mulVec, hg2, Matrix.smul_mulVec, Matrix.one_mulVec]
  · left
    have hm : m = k := le_antisymm hmk hge
    subst hm
    refine ⟨rfl, ?_⟩
    rw [Nat.sub_self, mul_zero, pow_zero, one_smul] at hrel₁
    exact sel_unit_of_rel σ A A' h₁ hA' hrel₁

end PI.SqPair.LCP
