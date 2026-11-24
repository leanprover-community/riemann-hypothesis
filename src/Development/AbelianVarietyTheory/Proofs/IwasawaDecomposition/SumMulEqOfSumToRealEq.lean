module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.PolFan

section OfCover

variable {X : Type} [AddCommGroup X]

theorem sum_mul_eq_of_sum_toReal_eq {L ι κ : Type} [AddCommGroup L] [Fintype ι] [Fintype κ]
    {j : L →ₗ[ℤ] LinearMap.BilinForm ℤ X} (hj : Function.Injective j) (ℓ : L →ₗ[ℤ] ℤ) {u : ι → L} {w : κ → L}
    {a : ι → ℝ} {b : κ → ℝ} (h : ∑ i, a i • toReal (j (u i)) = ∑ k, b k • toReal (j (w k))) :
    ∑ i, a i * (ℓ (u i) : ℝ) = ∑ k, b k * (ℓ (w k) : ℝ) := by
  have := sum_mul_eq_zero_of_sum_toReal hj ℓ (β := Sum.elim u w) (c := Sum.elim a (-b)) (by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, h, add_neg_cancel])
  rw [Fintype.sum_sum_type] at this
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this
  linarith

theorem toReal_injective : Function.Injective (toReal : LinearMap.BilinForm ℤ X → X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :=
  fun β β' h => LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ h a b
    simp only [toReal_apply] at this
    exact_mod_cast this

end OfCover

end GlobalTheory.PolFan
