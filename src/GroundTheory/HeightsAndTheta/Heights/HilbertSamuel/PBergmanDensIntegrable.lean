module

import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBergmanDensChartSum
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergmanDensIntegrable
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.A
open scoped ENNReal ContDiff ComplexConjugate Matrix

noncomputable section

namespace BergmanDensIntegrable

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem weight_contDiffOn {L : HolLineBundle A} (W : Weight L) (j : Fin A.n) :
    ContDiffOn ℝ ∞ (W.φ j ∘ (A.chart j).symm) (A.chart j).target :=
  (W.smooth j j).mono fun _ hy => ⟨hy, (A.chart j).map_target hy⟩

theorem trans_source_eq (j k : Fin A.n) :
    ((A.chart j).symm.trans (A.chart k)).source =
      (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]

theorem trans_target_eq (j k : Fin A.n) :
    ((A.chart j).symm.trans (A.chart k)).target =
      (A.chart k).target ∩ (A.chart k).symm ⁻¹' (A.chart j).source := by
  rw [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target]

theorem trans_analytic (j k : Fin A.n) :
    AnalyticOnNhd ℂ ((A.chart j).symm.trans (A.chart k))
      ((A.chart j).symm.trans (A.chart k)).source := by
  rw [trans_source_eq, OpenPartialHomeomorph.coe_trans]
  exact A.holo j k

theorem hessC_weight_trans {L : HolLineBundle A} (W : Weight L) (j k : Fin A.n) {y : Fin D → ℂ}
    (hy : y ∈ ((A.chart j).symm.trans (A.chart k)).source) :
    hessC (W.φ j ∘ (A.chart j).symm) y =
      (jacC ((A.chart j).symm.trans (A.chart k)) y)ᵀ *
        hessC (W.φ k ∘ (A.chart k).symm) (((A.chart j).symm.trans (A.chart k)) y) *
        (jacC ((A.chart j).symm.trans (A.chart k)) y).map (starRingEnd ℂ) := by
  apply GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanDensChartSum.hessC_weight_trans <;> assumption

theorem chernTopDens_trans {L : HolLineBundle A} (W : Weight L) (j k : Fin A.n) {y : Fin D → ℂ}
    (hy : y ∈ ((A.chart j).symm.trans (A.chart k)).source) :
    chernTopDens W j y = Complex.normSq (jacC ((A.chart j).symm.trans (A.chart k)) y).det *
      chernTopDens W k (((A.chart j).symm.trans (A.chart k)) y) := by
  unfold chernTopDens
  rw [hessC_weight_trans W j k hy]
  set J := jacC ((A.chart j).symm.trans (A.chart k)) y
  set H := hessC (W.φ k ∘ (A.chart k).symm) (((A.chart j).symm.trans (A.chart k)) y)
  set c : ℂ := ((1 / Real.pi : ℝ) : ℂ)
  have h1 : c • (Jᵀ * H * J.map (starRingEnd ℂ)) = Jᵀ * (c • H) * J.map (starRingEnd ℂ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have h2 : (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h2,
    show J.det * (c • H).det * starRingEnd ℂ J.det = ((Complex.normSq J.det : ℝ) : ℂ) * (c • H).det by
      rw [← Complex.mul_conj]; ring,
    Complex.re_ofReal_mul]
  ring

variable [MeasurableSpace X] [BorelSpace X]

theorem lintegral_dens_trans (dV : SmoothVolume A) (j k : Fin A.n)
    (f : (Fin D → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y in ((A.chart j).symm.trans (A.chart k)).source, f y * ENNReal.ofReal (dV.dens j y) =
      ∫⁻ y in ((A.chart j).symm.trans (A.chart k)).source,
        ENNReal.ofReal (Complex.normSq (jacC ((A.chart j).symm.trans (A.chart k)) y).det) *
          (f y * ENNReal.ofReal (dV.dens k (((A.chart j).symm.trans (A.chart k)) y))) := by
  apply GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanDensChartSum.lintegral_dens_trans <;> assumption


omit [MeasurableSpace X] [BorelSpace X] in
theorem jacC_trans_continuousOn (j k : Fin A.n) :
    ContinuousOn (jacC ((A.chart j).symm.trans (A.chart k)))
      ((A.chart j).symm.trans (A.chart k)).source := by
  have h := (trans_analytic (A := A) j k).fderiv.continuousOn
  refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => ?_
  exact (continuous_apply a).comp_continuousOn
    ((ContinuousLinearMap.apply ℂ _ (Pi.single b 1)).continuous.comp_continuousOn h)

theorem dens_trans (dV : SmoothVolume A) (j k : Fin A.n) {y : Fin D → ℂ}
    (hy : y ∈ ((A.chart j).symm.trans (A.chart k)).source) :
    dV.dens j y = Complex.normSq (jacC ((A.chart j).symm.trans (A.chart k)) y).det *
      dV.dens k (((A.chart j).symm.trans (A.chart k)) y) := by
  apply GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanDensChartSum.dens_trans <;> assumption

variable {L : HolLineBundle A}

def densIn (W : Weight L) (dV : SmoothVolume A) (j : Fin A.n) (x : X) : ℝ :=
  chernTopDens W j (A.chart j x) / ((D.factorial : ℝ) * dV.dens j (A.chart j x))

theorem densIn_eq (W : Weight L) (dV : SmoothVolume A) (j k : Fin A.n) {x : X}
    (hx : x ∈ (A.chart j).source ∩ (A.chart k).source) :
    densIn W dV j x = densIn W dV k x := by
  have hy : A.chart j x ∈ ((A.chart j).symm.trans (A.chart k)).source := by
    rw [trans_source_eq]
    exact ⟨(A.chart j).map_source hx.1,
      Set.mem_preimage.2 (by rw [(A.chart j).left_inv hx.1]; exact hx.2)⟩
  have hT : ((A.chart j).symm.trans (A.chart k)) (A.chart j x) = A.chart k x := by
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, (A.chart j).left_inv hx.1]
  have hc := chernTopDens_trans W j k hy
  have hd := dens_trans dV j k hy
  rw [hT] at hc hd
  set n := Complex.normSq (jacC ((A.chart j).symm.trans (A.chart k)) (A.chart j x)).det
  have hpos : 0 < dV.dens j (A.chart j x) := dV.pos j _ ((A.chart j).map_source hx.1)
  have hn : n ≠ 0 := by
    intro h0; rw [hd, h0, zero_mul] at hpos; exact lt_irrefl 0 hpos
  unfold densIn
  rw [hc, hd, show (D.factorial : ℝ) * (n * dV.dens k (A.chart k x)) =
    n * ((D.factorial : ℝ) * dV.dens k (A.chart k x)) by ring, mul_div_mul_left _ _ hn]


omit [BorelSpace X] in
theorem densIn_continuousAt (W : Weight L) (dV : SmoothVolume A) (j : Fin A.n) {x : X}
    (hx : x ∈ (A.chart j).source) : ContinuousAt (densIn W dV j) x := by
  have hy : A.chart j x ∈ (A.chart j).target := (A.chart j).map_source hx
  have hnhds : (A.chart j).target ∈ 𝓝 (A.chart j x) := (A.chart j).open_target.mem_nhds hy
  have hH : ContinuousAt (hessC (W.φ j ∘ (A.chart j).symm)) (A.chart j x) :=
    (hessC_continuousOn _ _ (A.chart j).open_target
      ((weight_contDiffOn W j).of_le (by first | simp |
        exact WithTop.coe_le_coe.2 le_top))).continuousAt hnhds
  have hdet : Continuous fun M : Matrix (Fin D) (Fin D) ℂ =>
      (D.factorial : ℝ) * ((((1 / Real.pi : ℝ) : ℂ) • M).det).re := by fun_prop
  have hC : ContinuousAt (chernTopDens W j) (A.chart j x) := hdet.continuousAt.comp hH
  have hdens : ContinuousAt (dV.dens j) (A.chart j x) :=
    (dV.smooth j).continuousOn.continuousAt hnhds
  have hc := (A.chart j).continuousAt hx
  refine (hC.comp hc).div (continuousAt_const.mul (hdens.comp hc)) ?_
  exact mul_ne_zero (by exact_mod_cast (Nat.factorial_pos D).ne') (dV.pos j _ hy).ne'

theorem bergmanDens_continuous (W : Weight L) (dV : SmoothVolume A) :
    Continuous (bergmanDens W dV) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hx : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  have hev : densIn W dV (chartIdx A x) =ᶠ[𝓝 x] bergmanDens W dV := by
    filter_upwards [(A.chart (chartIdx A x)).open_source.mem_nhds hx] with x' hx'
    exact densIn_eq W dV _ _ ⟨hx', Classical.choose_spec (A.cover x')⟩
  exact (densIn_continuousAt W dV _ hx).congr hev

end BergmanDensIntegrable

theorem BergmanDensIntegrable.proof : BergmanDensIntegrable.Statement := by
  intro D X _ _ _ _ _ A L W dV
  have := dV.isProb
  exact integrableOn_univ.1
    ((BergmanDensIntegrable.bergmanDens_continuous W dV).continuousOn.integrableOn_compact
      isCompact_univ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
