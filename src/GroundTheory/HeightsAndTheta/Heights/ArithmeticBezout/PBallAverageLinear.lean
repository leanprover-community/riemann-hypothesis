module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SphereMeanVol
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Measure Matrix

noncomputable section

namespace BallAverageLinear

def matEquiv {n : ℕ} (h : HermNorm n) : (Fin n → ℂ) ≃L[ℝ] (Fin n → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.ofLinearMap (f := (Matrix.mulVecLin h.mat).restrictScalars ℝ)
      (g := (Matrix.mulVecLin h.mat⁻¹).restrictScalars ℝ)
      (LinearMap.ext fun v => by
        simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h.isUnit_det])
      (LinearMap.ext fun v => by
        simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.isUnit_det]))

theorem matEquiv_apply {n : ℕ} (h : HermNorm n) (v : Fin n → ℂ) : matEquiv h v = h.mat *ᵥ v := rfl

theorem ballH_eq_preimage {n : ℕ} (h : HermNorm n) :
    ballH h = matEquiv h ⁻¹' ballH (HermNorm.std n) := by
  ext v
  simp [ballH, HermNorm.norm, HermNorm.std, matEquiv_apply]

end BallAverageLinear

open BallAverageLinear in
theorem BallAverageLinear.proof : BallAverageLinear.Statement := by
  intro n h φ
  set L := matEquiv h
  have hb := ballH_eq_preimage h
  have hpre : ∀ s : Set (Fin n → ℂ), IntegrableOn (fun v => φ (h.mat *ᵥ v)) (L ⁻¹' s) ↔
      IntegrableOn φ s := by
    intro s
    have he : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
    have hmap : (map L volume).IsAddHaarMeasure := L.isAddHaarMeasure_map volume
    have h2 : map L (volume : Measure (Fin n → ℂ)) =
        addHaarScalarFactor (map L volume) volume • volume := isAddLeftInvariant_eq_smul _ _
    have hpos := addHaarScalarFactor_pos_of_isAddHaarMeasure (map L (volume : Measure (Fin n → ℂ))) volume
    rw [show (fun v => φ (h.mat *ᵥ v)) = φ ∘ L from rfl, ← he.integrableOn_map_iff, h2,
      show (addHaarScalarFactor (map L volume) volume • (volume : Measure (Fin n → ℂ))) =
        ((addHaarScalarFactor (map L volume) volume : ENNReal) • volume) from rfl,
      IntegrableOn, IntegrableOn, Measure.restrict_smul,
      integrable_smul_measure (by simpa using hpos.ne') ENNReal.coe_ne_top]
  refine ⟨by rw [hb]; exact hpre _, ?_⟩
  rw [hb]
  exact SphereMean.setAverage_comp_linearEquiv volume volume L _ φ

end

end GroundTheory.Heights₂.Heights
