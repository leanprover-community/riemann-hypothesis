module

public import Formalism.GaussValuationBounds.GaussUnit
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

noncomputable section

namespace Formalism.NOK

open scoped ENNReal

open IsDiscreteValuationRing in
theorem minLeGaussValAdd : GaussAdd := by
  intro O _ _ _ x f g
  refine le_iInf fun n => ?_
  have h1 : min (gaussV x f) (gaussV x g) ≤
      min ((((addVal O (PowerSeries.coeff n f) : ℕ∞)) : ℝ≥0∞) + ENNReal.ofReal (x * n))
        ((((addVal O (PowerSeries.coeff n g) : ℕ∞)) : ℝ≥0∞) + ENNReal.ofReal (x * n)) :=
    min_le_min (iInf_le _ n) (iInf_le _ n)
  refine h1.trans ?_
  rw [min_add_add_right, map_add (f := _)]
  gcongr ?_ + _
  have h2 := addVal_add (R := O) (a := PowerSeries.coeff n f) (b := PowerSeries.coeff n g)
  rcases le_total (addVal O (PowerSeries.coeff n f)) (addVal O (PowerSeries.coeff n g)) with h | h
  · rw [min_eq_left (ENat.toENNReal_le.mpr h)]
    exact ENat.toENNReal_le.mpr (by rwa [min_eq_left h] at h2)
  · rw [min_eq_right (ENat.toENNReal_le.mpr h)]
    exact ENat.toENNReal_le.mpr (by rwa [min_eq_right h] at h2)

theorem gaussValC : GaussC := by
  intro O _ _ _ x _ c
  refine le_antisymm ((iInf_le _ 0).trans (by simp)) (le_iInf fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [PowerSeries.coeff_C, if_neg hn.ne', addVal_zero]
    simp

theorem gaussValUnit : GaussUnit := by
  intro O _ _ _ x _ u hu
  obtain ⟨w, hw⟩ := hu.map (PowerSeries.constantCoeff (R := O))
  refine le_antisymm ((iInf_le _ 0).trans ?_) (by simp)
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, ← hw, addVal_eq_zero_of_unit]
  simp


end Formalism.NOK
