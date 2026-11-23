module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.CurveHyp
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.IsTransSys
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Series
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

namespace Two

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem fExp_zero : Formalism.L2.Th1.B.fExp (0 : PowerSeries K) = 1 := by
  have h := Formalism.L2.Th1.B.fExp_add (K := K) (ι := Unit) (f := 0) (g := 0) (map_zero _) (map_zero _)
  rw [add_zero] at h
  have hc : MvPowerSeries.constantCoeff (Formalism.L2.Th1.B.fExp (0 : MvPowerSeries Unit K)) = 1 :=
    Formalism.L2.Th1.B.constantCoeff_fExp (map_zero _)
  have hne : Formalism.L2.Th1.B.fExp (0 : MvPowerSeries Unit K) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hc; exact zero_ne_one hc
  exact (mul_left_cancel₀ hne (h.symm.trans (mul_one _).symm))

theorem oneUnit_fExp_neg {f : PowerSeries K} (h : Formalism.InvariantFactorPaths.G7.Simeq (ι := Unit) f 0) :
    OneUnit (Formalism.L2.Th1.B.fExp (-f)) := by
  obtain ⟨h0, hI⟩ := h
  rw [sub_zero] at h0 hI
  have h0n : MvPowerSeries.constantCoeff (-f : MvPowerSeries Unit K) = 0 := by
    rw [map_neg, h0, neg_zero]
  have hf : OneUnit (Formalism.L2.Th1.B.fExp f) :=
    ⟨Formalism.L2.Th1.B.constantCoeff_fExp h0, (Ser.intS_iff_integral _).2 hI⟩
  refine Ser.oneUnit_of_mul_eq_one hf ?_
  rw [← Formalism.L2.Th1.B.fExp_add h0 h0n, add_neg_cancel]
  exact fExp_zero

end Two

end Formalism.L2.Th1.E
