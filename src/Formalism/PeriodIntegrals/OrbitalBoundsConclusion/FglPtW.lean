module

public import Formalism.PeriodIntegrals.FglPtW
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupPoints.AddGenThm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupPoints.MulGenThm
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem formal_group_add_generation : PI.FglPtW.AddGen := PI.FglPtW.Wk.addGen_thm

theorem formal_group_mul_generation : PI.FglPtW.MulGen := PI.FglPtW.Wk.mulGen_thm

private theorem cc_subst_lemma {K : Type*} [CommRing K] {σ : Type*} {a : MvPowerSeries σ K}
    (ha : MvPowerSeries.constantCoeff a = 0) (f : PowerSeries K) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = PowerSeries.constantCoeff f := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [map_pow, ha, zero_pow hd]

private theorem subst_subst_eq_of_subst_eq_X {K : Type*} [CommRing K] {l ex : PowerSeries K}
    (hex : PowerSeries.constantCoeff ex = 0) (hl : PowerSeries.subst ex l = PowerSeries.X)
    {σ : Type*} {u : MvPowerSeries σ K} (hu : MvPowerSeries.constantCoeff u = 0) :
    PowerSeries.subst (PowerSeries.subst u ex) l = u := by
  have hexS : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex
  have huS : PowerSeries.HasSubst u := PowerSeries.HasSubst.of_constantCoeff_zero hu
  rw [← PowerSeries.subst_comp_subst_apply hexS huS, hl, PowerSeries.subst_X huS]
