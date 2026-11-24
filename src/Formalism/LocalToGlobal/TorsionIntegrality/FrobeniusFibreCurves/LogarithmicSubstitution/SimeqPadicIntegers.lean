module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementB
public import Formalism.GL3MeanSquares.LegendreCoefficient
public import Formalism.GL3MeanSquares.HookFormulaTorsion.ExpSeries
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.Th1.B.Sim

open Finset
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.HermitianLattices.ExpSeriesBivariate (InLam)
open Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition (inLam_zero inLam_add inLam_neg inLam_nsmul integral_of_mul_eq_one)

variable {K ι : Type} [NormedField K] [CharZero K]

theorem simeq_iff (f g : MvPowerSeries ι K) : Simeq f g ↔ InLam (f - g) := Iff.rfl

theorem inLam_zsmul [IsUltrametricDist K] {f : MvPowerSeries ι K} (hf : InLam f) (n : ℤ) :
    InLam (n • f) := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [natCast_zsmul]; exact inLam_nsmul hf m
  · rw [neg_zsmul, natCast_zsmul]; exact inLam_neg (inLam_nsmul hf m)

theorem inLam_fLog {g : MvPowerSeries ι K} (hg0 : MvPowerSeries.constantCoeff g = 1)
    (hg : Integral g) : InLam (fLog g) := by
  refine ⟨constantCoeff_fLog hg0, ?_⟩
  have e : fExp (fLog g) = g := fExp_fLog hg0
  have h : Integral (fExp (fLog g)) := by rw [e]; exact hg
  exact h

end Formalism.L2.Th1.B.Sim

namespace Formalism.L2.Th1.B.Sim

open Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition (inLam_add inLam_neg)

theorem simeq_integral_series : SimeqInt := by
  intro K ι _ _ _ f g f' g' h h'
  rw [simeq_iff] at h h'
  refine ⟨?_, ?_, fun n => ?_⟩
  · rw [simeq_iff]
    have e : f - f' - (g - g') = (f - g) + -(f' - g') := by ring
    rw [e]; exact inLam_add h (inLam_neg h')
  · rw [simeq_iff]
    have e : -f - -g = -(f - g) := by ring
    rw [e]; exact inLam_neg h
  · rw [simeq_iff]
    have e : (n : MvPowerSeries ι K) * f - n * g = n • (f - g) := by
      rw [zsmul_eq_mul]; ring
    rw [e]; exact inLam_zsmul h n

theorem simeq_formal_log : SimeqLog := by
  intro K ι _ _ _ g hg0 hg
  have h := inLam_fLog hg0 hg
  refine ⟨?_, ?_⟩
  · rw [simeq_iff, sub_zero]; exact h
  · rw [simeq_iff, sub_zero]; exact inLam_neg h

end Formalism.L2.Th1.B.Sim
