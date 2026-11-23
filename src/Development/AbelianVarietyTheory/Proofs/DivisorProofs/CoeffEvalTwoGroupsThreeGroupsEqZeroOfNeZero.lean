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
public import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

@[expose] public section

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory

theorem coeff_at2_x1_x2_eq_zero_of_third_ne_zero {R : Type} [CommRing R] {d : ℕ}
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a b e : Fin d →₀ ℕ) (he : e ≠ 0) :
    coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x1 x2) = 0 := by
  classical
  let g : Fin d ⊕ Fin d → Fin d ⊕ (Fin d ⊕ Fin d) := Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)
  have hg : (Sum.elim x1 x2 : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = X ∘ g := by
    funext s; rcases s with s | s <;> rfl
  have h1 : at2 c x1 x2 = rename g c := by
    rw [rename_eq_subst, ← hg]; rfl
  rw [h1]
  apply coeff_rename_eq_zero
  rintro ⟨v, hv⟩
  obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
    by_contra h; push_neg at h; exact he (Finsupp.ext h)
  apply hi
  have h2 := congrArg (fun w : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ => w (Sum.inr (Sum.inr i))) hv
  rw [Finsupp.mapDomain_notin_range] at h2
  · simpa using h2.symm
  · rintro ⟨s, hs⟩; rcases s with s | s <;> simp [g] at hs

end GlobalTheory
