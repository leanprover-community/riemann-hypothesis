module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open MvPowerSeries

set_option autoImplicit false

namespace GlobalTheory.Katz

theorem coeff_at2_x2_x3_eq_zero_of_first_ne_zero {R : Type} [CommRing R] {d : ℕ} (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    (a b e : Fin d →₀ ℕ) (ha : a ≠ 0) :
    coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x2 x3) = 0 := by
  classical
  have hX : ∀ s, Sum.elim (x2 (R := R) (d := d)) x3 s
      = X (Sum.elim (fun i => Sum.inr (Sum.inl i)) (fun i => Sum.inr (Sum.inr i)) s) := by
    intro s; cases s <;> rfl
  have hs : HasSubst (Sum.elim (x2 (R := R) (d := d)) x3) :=
    hasSubst_of_constantCoeff_zero fun s => by rw [hX]; exact constantCoeff_X _
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h; push_neg at h; exact ha (Finsupp.ext h)
  unfold at2
  rw [coeff_subst hs]
  apply finsum_eq_zero_of_forall_eq_zero
  intro α
  have key : ∃ β : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, β (Sum.inl i) = 0 ∧
      (α.prod fun s k => (Sum.elim (x2 (R := R) (d := d)) x3 s) ^ k) = monomial β 1 := by
    unfold Finsupp.prod
    refine Finset.prod_induction _ (fun f => ∃ β : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ,
      β (Sum.inl i) = 0 ∧ f = monomial β 1) ?_ ?_ ?_
    · rintro f g ⟨β, hβ, rfl⟩ ⟨γ, hγ, rfl⟩
      exact ⟨β + γ, by simp [hβ, hγ], by rw [monomial_mul_monomial, one_mul]⟩
    · exact ⟨0, rfl, (monomial_zero_one).symm⟩
    · intro s _
      refine ⟨Finsupp.single (Sum.elim (fun i => Sum.inr (Sum.inl i)) (fun i => Sum.inr (Sum.inr i)) s) (α s), ?_, ?_⟩
      · cases s <;> simp
      · dsimp only
        rw [hX, X_pow_eq]
  obtain ⟨β, hβ, hp⟩ := key
  rw [hp, coeff_monomial_ne, smul_zero]
  intro h
  apply hi
  have := congrArg (fun w => w (Sum.inl i)) h
  simpa [hβ] using this

end GlobalTheory.Katz
