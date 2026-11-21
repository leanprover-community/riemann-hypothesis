import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMeasureOfPublished
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LevelSubgroupIndexBounded
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HaarMeasureFundamentalDomainNeZeroOfCocompact
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.VolumeFundamentalDomainNeTopOfFiniteCovolume
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExactRatioOfFundamentalDomain
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExactRatioOfFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogMeasureRatioLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.PlugPairs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogMeasureRatioLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMeasureOfPrintsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CovolumeLowerBoundOfCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureBoundStatementStatement

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.ExactRatioProof
open scoped InnerProductSpace ComplexConjugate
theorem exact_covolume_ratio : ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕), GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ExactRatio C i P μ 𝓕 := by
  intro hP D Tu C t0 hC i P μ 𝓕 hF T _ hT ha θ hθ σ M hV F hFm f hf hc
  have hμ : μ.IsHaarMeasure := hF.1.1
  have hS : ∃ c, IsMultIP M μ 𝓕 F F c :=
    GlobalTheory.MultFinite.schurMult GlobalTheory.T.cusp_forms_rapid_decay μ 𝓕 hθ hμ hF.2 F hFm F hFm
  refine ⟨hS, ?_⟩
  obtain ⟨v, hv1, hnorm⟩ : ∃ v : M.Vec, (∀ τ, ‖(v τ : M.H τ)‖ = 1) ∧
      ∀ g, ‖F v g‖ = ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f g‖ := by
    rcases hc with ⟨-, v, hv, e⟩ | ⟨-, v, hv, e⟩
    · exact ⟨v, fun τ => (hv τ).1, fun g => by rw [e]⟩
    · exact ⟨v, hv, fun g => by rw [e, RCLike.norm_conj]⟩
  have hFM := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hFm
  have haut := hFM.aut v
  have h1 := (ipM_spec M μ 𝓕 F F hS v v).2
  have hprod : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ = 1 :=
    Finset.prod_eq_one fun τ _ => by rw [inner_self_eq_norm_sq_to_K, hv1 τ]; simp
  rw [hprod, mul_one] at h1
  have hs : GoodEmb T.Q.c (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ) := goodEmb_goodOf _ _
  set c := lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i) with hcdef
  have hc0 : 0 < c := lieFacZ_pos _ _
  set ψ : AutQ (Wc D i) → ℂ := fun q => ((‖F v q.out‖ / c : ℝ) : ℂ) with hψdef
  have hK2 := K2 D T hT i _ hs hV f
  have hK3 := K3 D T hT i _ hs f hf
  have hE : eLpNorm ψ 2 (muQ1 (Wc D i)) = petE (T.V ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ))
      (T.dict ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)) (muQ1 (T.V ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)))
      (modelWt (T.U ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f := by
    have e1 : eLpNorm ψ 2 (muQ1 (Wc D i)) =
        eLpNorm (c⁻¹ • fun q : AutQ (Wc D i) => ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f q.out‖) 2 (muQ1 (Wc D i)) := by
      refine eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun q => ?_)
      simp only [hψdef, Pi.smul_apply, smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_norm,
        abs_of_pos hc0, abs_mul, abs_inv, hnorm]
      ring
    rw [e1, eLpNorm_const_smul, hK2, ← mul_assoc, Real.enorm_eq_ofReal (inv_nonneg.2 hc0.le),
      ← ENNReal.ofReal_mul (inv_nonneg.2 hc0.le), inv_mul_cancel₀ hc0.ne', ENNReal.ofReal_one, one_mul]
  have hψm : AEStronglyMeasurable ψ (muQ1 (Wc D i)) := by
    haveI : BorelSpace (GA D (Wc D i)) := ⟨rfl⟩
    have hm : Measurable fun q : AutQ (Wc D i) => F v q.out := by
      rw [measurable_from_quotient]
      have e : ((fun q : AutQ (Wc D i) => F v q.out) ∘ Quotient.mk'') = F v := funext fun g => by
        have h2 : g * (Quotient.mk (QuotientGroup.rightRel (GQ (Wc D i))) g).out⁻¹ ∈ GQ (Wc D i) :=
          QuotientGroup.rightRel_apply.1 (Quotient.mk_out g)
        have h3 := haut.left _ h2 (Quotient.mk (QuotientGroup.rightRel (GQ (Wc D i))) g).out
        rw [inv_mul_cancel_right] at h3
        exact h3.symm
      rw [e]
      exact haut.cont.measurable
    refine Measurable.aestronglyMeasurable ?_
    exact Complex.measurable_ofReal.comp ((hm.norm).div_const c)
  have hψ : MemLp ψ 2 (muQ1 (Wc D i)) := ⟨hψm, by rw [hE]; exact lt_top_iff_ne_top.2 hK3⟩
  have hI := GlobalTheory.ReadingNorm.integral_star_mul (Wc D i) (D.sp.W_sig _) hμ hF.2 (F v) haut.left ψ hψ c
    (fun q => by
      simp only [hψdef, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_norm, abs_of_pos hc0]
      field_simp)
  have hL : ‖hψ.toLp ψ‖ = (petE (T.V ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ))
      (T.dict ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)) (muQ1 (T.V ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)))
      (modelWt (T.U ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f).toReal := by
    rw [Lp.norm_toLp, hE]
  rw [Formalism.IndefR.Links.ipAt, ← h1, hI, L1 D i σ, hL]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.probSq
  push_cast
  ring
end GlobalTheory.ExactRatioProof
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_ratio_eq_index : ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕), GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ExactRatio C i P μ 𝓕 := by
  first | exact @_root_.GlobalTheory.ExactRatioProof.exact_covolume_ratio | exact _root_.GlobalTheory.ExactRatioProof.exact_covolume_ratio | (intros; apply _root_.GlobalTheory.ExactRatioProof.exact_covolume_ratio <;> assumption)
end
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
namespace GlobalTheory.OneMeasureRatio
theorem log_covolume_ratio_le : ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L), Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio D i μ 𝓕) ≤ 122 * (D.R.f * (D.R.r : ℝ) ^ 2 * L) := by
  intro hP D Tu C t0 hC i P μ 𝓕 hF L hL
  have h0 := _root_.GlobalTheory.T.fundamentalDomain_volume_ne_zero hP D Tu C t0 hC i P μ 𝓕 hF
  have ht := _root_.GlobalTheory.T.quotient_measure_lt_top_of_finite_covolume hP D Tu C t0 hC i P μ 𝓕 hF
  have hv := _root_.MainStatements.Tam.Plug.tamagawa_pairs_compatible hP D Tu C t0 hC i P μ 𝓕 hF L hL
  have hd : ∀ τ, Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) ≤ 3 / 2 * (D.R.r : ℝ) ^ 2 * L :=
    GlobalTheory.T.log_lowestKTypeWeylDimension_le_of_sizeBounds D i L hL
  have hd1 : ∀ τ, 1 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ := GlobalTheory.DimAtOne.one_le_dimAt D i
  have hvpos : 0 < (μ 𝓕).toReal := ENNReal.toReal_pos h0 ht
  have hdpos : ∀ τ, 0 < GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ := fun τ => zero_lt_one.trans_le (hd1 τ)
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio
  rw [Real.log_mul hvpos.ne' (Finset.prod_pos fun τ _ => hdpos τ).ne',
    Real.log_prod (fun τ _ => (hdpos τ).ne')]
  have hsum : ∑ τ, Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) ≤ ∑ _τ : D.what₂.Tau, 3 / 2 * (D.R.r : ℝ) ^ 2 * L :=
    Finset.sum_le_sum fun τ _ => hd τ
  rw [Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul] at hsum
  have hlog := log_r_add_three_le D L hL
  have hL0 : 0 ≤ L := le_trans (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) D.R.r; linarith)) hlog
  have hfr : 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 := by positivity
  have h3 := mul_le_mul_of_nonneg_left hlog hfr
  have h4 : 0 ≤ (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * L := mul_nonneg hfr hL0
  nlinarith
end GlobalTheory.OneMeasureRatio
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_measure_ratio_bounded : ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L), Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio D i μ 𝓕) ≤ 122 * (D.R.f * (D.R.r : ℝ) ^ 2 * L) := by
  first | exact @_root_.GlobalTheory.OneMeasureRatio.log_covolume_ratio_le | exact _root_.GlobalTheory.OneMeasureRatio.log_covolume_ratio_le | (intros; apply _root_.GlobalTheory.OneMeasureRatio.log_covolume_ratio_le <;> assumption)
end
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
namespace GlobalTheory.OneMeasureAll
theorem covolume_measure_eq_one : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.OneMeasure D := by
  intro hP D Tu C t0 hC i P
  refine ⟨_root_.GlobalTheory.T.level_subgroup_index_bounded hP D Tu C t0 hC i P, fun τ => GlobalTheory.T.one_le_dimAt' D i τ, fun μ 𝓕 hF =>
    ⟨_root_.GlobalTheory.T.fundamentalDomain_volume_ne_zero hP D Tu C t0 hC i P μ 𝓕 hF, _root_.GlobalTheory.T.quotient_measure_lt_top_of_finite_covolume hP D Tu C t0 hC i P μ 𝓕 hF,
      _root_.GlobalTheory.T.covolume_ratio_eq_index hP D Tu C t0 hC i P μ 𝓕 hF, fun L hL =>
        ⟨fun τ => GlobalTheory.T.log_lowestKTypeWeylDimension_le_of_sizeBounds D i L hL τ, _root_.MainStatements.Tam.Plug.tamagawa_pairs_compatible hP D Tu C t0 hC i P μ 𝓕 hF L hL,
          _root_.GlobalTheory.T.log_measure_ratio_bounded hP D Tu C t0 hC i P μ 𝓕 hF L hL⟩⟩⟩
end GlobalTheory.OneMeasureAll
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalized_covolume_eq_one : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.OneMeasure D := by
  first | exact @_root_.GlobalTheory.OneMeasureAll.covolume_measure_eq_one | exact _root_.GlobalTheory.OneMeasureAll.covolume_measure_eq_one | (intros; apply _root_.GlobalTheory.OneMeasureAll.covolume_measure_eq_one <;> assumption)
end
end

section
section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
namespace GlobalTheory.CovTop.MeasRd
theorem covering_measure_reduction : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Meas := by
  intro h
  have h2 := _root_.GlobalTheory.T.normalized_covolume_eq_one h
  refine Closed.imp (Closed.and (GlobalTheory.T.log_ratio_upper_bound h2) (_root_.GlobalTheory.T.covolume_lower_bound_of_cover h)) ?_
  intro _ Fm _ _ hh
  obtain ⟨⟨K1, hK1, a, ha⟩, ⟨K2, hK2, b, hb⟩⟩ := hh
  refine ⟨(K1 + K2) / 2, by positivity, max a b, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨hr, hu⟩ := ha x hx ((le_max_left _ _).trans hle) ι p hp i
  have hl := hb x hx ((le_max_right _ _).trans hle) ι p hp i
  exact measAt_of p i (GlobalTheory.T.exact_at_of_one_measure p hp.1 (h2 _) i) hr hK1 hK2 hu hl
end GlobalTheory.CovTop.MeasRd
end
end

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_measure_reduction_bound : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Meas := by
  first | exact @_root_.GlobalTheory.CovTop.MeasRd.covering_measure_reduction | exact _root_.GlobalTheory.CovTop.MeasRd.covering_measure_reduction | (intros; apply _root_.GlobalTheory.CovTop.MeasRd.covering_measure_reduction <;> assumption)
end
end
