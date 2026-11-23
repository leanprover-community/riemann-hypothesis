module

public import Development.AbelianVarietyTheory.Definitions.Divisors.VdmSplit
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CARUnit
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CsqDdPt
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.LayerLeGeneratedTensorFock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapConditionsOfLargeGaps

@[expose] public section

noncomputable section

open Finset ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

theorem casimirValue_highestWeightCoordinates : CasCoord := by
  intro n ε lam M _ _ E hE z hz hD s
  have hE' := eT_isGlRep (n := n) hE
  have h2 := LinearMap.congr_fun (two_D_sq hE' cpT_cmT_isCAR (eT_commutesCAR E) ε) z
  have hK := casimirK_khwVec_compact ε (diagE_compact hE' cpT_cmT_isCAR (eT_commutesCAR E) ε) hz
  have hs : ∑ a, ((rhoHol ε a : ℝ) : ℂ) • diagE ε (eT E) cpT cmT a a z =
      ((dot (rhoHol ε) (gaW ε lam) : ℝ) : ℂ) • z := by
    simp only [dot, Complex.ofReal_sum, Complex.ofReal_mul, sum_smul, hz.1, smul_smul]
  have h0 : ((2 : ℂ) • ((dOp ε (eT E) cpT + dOp' ε (eT E) cmT) * (dOp ε (eT E) cpT + dOp' ε (eT E) cmT))) z = 0 := by
    rw [LinearMap.smul_apply, mul_apply_eq_comp]
    have : (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) z = 0 := hD
    rw [this, map_zero, smul_zero]
  rw [h0] at h2
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, hK, hs] at h2
  have hid := khw_real_identity ε (lam - rhoC ε)
  have hg : lam - rhoC ε + rhoHol ε = gaW ε lam := rfl
  have hl : lam - rhoC ε + rhoC ε = lam := sub_add_cancel _ _
  rw [hg, hl] at hid
  have hc : casimir (eT (n := n) E) z = ((casVal lam : ℝ) : ℂ) • z := by
    have e : casimir (eT (n := n) E) z =
        ((nsq (gaW ε lam + rhoC ε) - nsq (rhoC ε) : ℝ) : ℂ) • z -
          (2 : ℂ) • (((dot (rhoHol ε) (gaW ε lam) : ℝ) : ℂ) • z) := by
      linear_combination (norm := module) h2
    rw [e, casVal, ← hid]
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat, sub_smul, smul_smul]
  have hcoord := congrArg (tco s) hc
  rw [TRGap.casimir_eT, tco_map_left] at hcoord
  simpa only [tco, map_smul] using hcoord

end GlobalTheory.PsCo.PcEF
