module

public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.EdgeNoTrunc
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace Formalism.InvariantFactorPaths.G7.Top

open Formalism.InvariantFactorPaths.G7

theorem thetaLogIsSubst : ThetaLogIsSubst := by
  intro K _ ν r0 r1 _ om oms ϖ μ Tht hμ

  have hz0 : ∀ x : Bool × EV ν r0 r1, MvPowerSeries.constantCoeff (zLin om oms x) = 0 := by
    intro x
    unfold zLin

    rw [map_sum]
    apply Finset.sum_eq_zero
    intro s _
    split_ifs <;> simp
  have hz : ∀ x : Bool × EV ν r0 r1, PowerSeries.HasSubst (zLin om oms x) := fun x =>
    PowerSeries.HasSubst.of_constantCoeff_zero (hz0 x)

  have hs : ∀ x : Bool × EV ν r0 r1, MvPowerSeries.constantCoeff (sSub om oms μ x) = 0 := by
    intro x
    unfold sSub
    rw [PowerSeries.constantCoeff_subst (hz x)]
    apply finsum_eq_zero_of_forall_eq_zero
    intro d
    rcases d with _ | d
    · simp [hμ]
    · simp [map_pow, hz0 x]
  have ha : MvPowerSeries.HasSubst (fun x : Bool × EV ν r0 r1 => MvPowerSeries.C ϖ * sSub om oms μ x) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun x => by simp [hs x])
  have hb : MvPowerSeries.HasSubst (fun y : ZV ν r0 r1 =>
      MvPowerSeries.C ϖ⁻¹ * (MvPowerSeries.X y : MvPowerSeries (ZV ν r0 r1) K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun y => by simp)
  exact MvPowerSeries.subst_comp_subst_apply ha hb Tht

end Formalism.InvariantFactorPaths.G7.Top
