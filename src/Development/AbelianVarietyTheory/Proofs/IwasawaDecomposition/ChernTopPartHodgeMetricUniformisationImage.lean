import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentBaseDimEqCmTypeCardMulPq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComponentUniformisationContinuousOnAnalyticAtCha
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricLieFramesSmoothHermitianOffBoundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationImageBoundedDomainEqOpenPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopChartIndependent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopDensityModelMetricOrigin
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingCompEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopChernDensityInvariantHolomorphicFrameChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityCompHolomorphicNormSqDet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAndFderivMoebI
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMoebZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRestrictScalarsMatrixLeftRightMulAdeleTens
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationComponentEqOfSameModulusPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameDomainCoordinatesHolomorphic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicInvertibleFrameCoordinates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicChartOfExpChartGenericFibre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasChernIntegralOfEqMul

section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagSpaceComponent_base_dim_eq_cmType_card_mul_pq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim := by
  first | exact @GlobalTheory.BaseDim.card_eq_dim | exact GlobalTheory.BaseDim.card_eq_dim | (intros; apply GlobalTheory.BaseDim.card_eq_dim <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.componentUniformisation_continuousOn_analyticAt_charts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ContinuousOn ψ (DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p)) ∧ ∀ w ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), ∀ ch : AlgChart X.str (σ.comp e.toRingHom) X.dim, ψ w ∈ ch.e.source → AnalyticAt ℂ (fun w' => ch.e (ψ w')) w := by
  first | exact @GlobalTheory.UnifHolo.unif_continuousOn_analyticAt | exact GlobalTheory.UnifHolo.unif_continuousOn_analyticAt | (intros; apply GlobalTheory.UnifHolo.unif_continuousOn_analyticAt <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeMetric_lie_frames_smooth_hermitian_off_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (C : FlagCpt T.Z e), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : C.Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e C X j f f₀ Eb A₀ → IsMetricOn Eb (openPart j) (lieGram e U hj f₀ A₀) := by
  first | exact @GlobalTheory.LieBase.isMetricOn_lieGram | exact GlobalTheory.LieBase.isMetricOn_lieGram | (intros; apply GlobalTheory.LieBase.isMetricOn_lieGram <;> assumption)
end

section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal

namespace GlobalTheory.PoincareLower

open Topology Filter

section General

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem diff_fderiv_apply {F : E → ℝ} {x : E} (hF : ContDiffAt ℝ 2 F x) (a : E) :
    DifferentiableAt ℝ (fun v => fderiv ℝ F v a) x :=
  ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply (differentiableAt_const a)

theorem eventually_diff {F : E → ℝ} {x : E} (hF : ContDiffAt ℝ 2 F x) :
    ∀ᶠ v in 𝓝 x, DifferentiableAt ℝ F v :=
  (hF.eventually (by simp)).mono fun _ hv => hv.differentiableAt (by norm_num)

theorem fderiv_anti {F : E → ℝ} {x : E} (hF : ContDiffAt ℝ 2 F x) (a b c : E) :
    fderiv ℝ (fun v => (fderiv ℝ (fun u => (F u : ℂ)) v a + Complex.I * fderiv ℝ (fun u => (F u : ℂ)) v b) / 2) x c =
      ((fderiv ℝ (fun v => fderiv ℝ F v a) x c : ℝ) + Complex.I * (fderiv ℝ (fun v => fderiv ℝ F v b) x c : ℝ)) / 2 := by
  have e : (fun v => (fderiv ℝ (fun u => (F u : ℂ)) v a + Complex.I * fderiv ℝ (fun u => (F u : ℂ)) v b) / 2) =ᶠ[𝓝 x]
      fun v => (((fderiv ℝ F v a : ℝ) : ℂ) + Complex.I * ((fderiv ℝ F v b : ℝ) : ℂ)) * (2 : ℂ)⁻¹ := by
    filter_upwards [eventually_diff hF] with v hv
    have h : HasFDerivAt (fun u => (F u : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ F v)) v :=
      Complex.ofRealCLM.hasFDerivAt.comp v hv.hasFDerivAt
    rw [h.fderiv]
    simp [div_eq_mul_inv]
  have h1 : HasFDerivAt (fun v => ((fderiv ℝ F v a : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (fun v => fderiv ℝ F v a) x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (diff_fderiv_apply hF a).hasFDerivAt
  have h2 : HasFDerivAt (fun v => ((fderiv ℝ F v b : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (fun v => fderiv ℝ F v b) x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (diff_fderiv_apply hF b).hasFDerivAt
  rw [e.fderiv_eq, ((h1.fun_add (h2.const_mul Complex.I)).mul_const (2 : ℂ)⁻¹).fderiv]
  simp
  ring

end General

variable {ι : Type} [Fintype ι] {p q : ℕ}

theorem isOpen_domFlat : IsOpen (DomFlat ι p q) := by
  refine isOpen_iff_mem_nhds.2 fun x0 hx0 => ?_
  refine Filter.eventually_all.2 fun τ => ExhB.posDef_eventually
    (fun v : ι × Fin p × Fin q → ℂ => 1 - (unflat v τ)ᴴ * unflat v τ) (fun i j => ?_)
    (fun v => isHermitian_one.sub (isHermitian_conjTranspose_mul_self _)) x0 (hx0 τ)
  simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, unflat, Matrix.of_apply]
  fun_prop

theorem ddc_eq {f : Pt ι p q → ℝ} {z : Pt ι p q} (hf : ContDiffAt ℝ 2 (fun v => f (unflat v)) (flat z))
    (ξ : Pt ι p q) : ddc f z ξ =
      (fderiv ℝ (fun v => fderiv ℝ (fun u => f (unflat u)) v (flat ξ)) (flat z) (flat ξ) +
        fderiv ℝ (fun v => fderiv ℝ (fun u => f (unflat u)) v (flat (Complex.I • ξ))) (flat z)
          (flat (Complex.I • ξ))) / (4 * Real.pi) := by
  have e : ∀ ζ, dR (fun w => dAnti (fun u => (f u : ℂ)) w ξ) z ζ = _ :=
    fun ζ => fderiv_anti hf (flat ξ) (flat (Complex.I • ξ)) (flat ζ)
  rw [ddc, dHol, e, e]
  simp
  ring

variable {Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)} (B : BdData ι p q Γ)

end GlobalTheory.PoincareLower
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

open Filter Topology GlobalTheory.GoodMetric
open scoped ComplexOrder

set_option maxHeartbeats 800000 in

theorem GlobalTheory.UnifDens.chernTop_unif_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ ch : AlgChart X.str (σ.comp e.toRingHom) X.dim, ψ (GlobalTheory.UnifDens.flatL h v) ∈ ch.e.source → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), chernTop (pointPoly H Dw) (fun u => lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h u))) v = Complex.normSq (LinearMap.det (fderiv ℂ (fun u => ch.e (ψ (GlobalTheory.UnifDens.flatL h u))) v : ReciprocityTheory.L2DbarEstimates.V X.dim →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V X.dim)) * chernTop (pointPoly H Dw) (fun u => lieGram e U hj f₀ A₀ A (ch.e.symm u)) (ch.e (ψ (GlobalTheory.UnifDens.flatL h v))) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ h v hv ch hch A hA
  have hholo := GlobalTheory.T.componentUniformisation_continuousOn_analyticAt_charts E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hM := GlobalTheory.T.hodgeMetric_lie_frames_smooth_hermitian_off_boundary E H Dw l Xo c O β Y T F e σ U hσ hU (Φ.C k) X j f f₀ Eb A₀ hj hL
  have hyO : ψ (GlobalTheory.UnifDens.flatL h v) ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j) := by
    rw [← GlobalTheory.T.uniformisation_image_boundedDomain_eq_openPart E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ]
    exact ⟨_, hv, rfl⟩
  set y := ψ (GlobalTheory.UnifDens.flatL h v) with hydef
  let K : ReciprocityTheory.L2DbarEstimates.V X.dim → Mat Dw.mult ℂ := fun u => lieGram e U hj f₀ A₀ A (ch.e.symm u)
  let φ : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.L2DbarEstimates.V X.dim := fun u => ch.e (ψ (GlobalTheory.UnifDens.flatL h u))
  have hφ : AnalyticAt ℂ φ v :=
    (hholo.2 _ hv ch hch).comp (show AnalyticAt ℂ (GlobalTheory.UnifDens.flatL h) v from (GlobalTheory.UnifDens.flatL h).toContinuousLinearMap.analyticAt v)
  have hy'' : ch.e.symm (ch.e y) = y := ch.e.left_inv hch
  have hK2 : ∀ τ, MContDiffAt 2 (fun u => K u τ) (φ v) := by
    intro τ a b
    have hsm := hM.smooth y hyO A hA τ a b
    have hre := GlobalTheory.ChernWeilLine.cInfAt_eventually hsm.1
    have him := GlobalTheory.ChernWeilLine.cInfAt_eventually hsm.2
    have hn : ∀ {g : CxPts X.str (σ.comp e.toRingHom) → ℝ}, (∀ᶠ z in 𝓝 y, CInfAt g z) →
        ContDiffAt ℝ 2 (g ∘ ch.e.symm) (ch.e y) := by
      intro g hg
      have hs : ch.e.target ∩ ch.e.symm ⁻¹' {z | CInfAt g z} ∈ 𝓝 (ch.e y) := by
        refine Filter.inter_mem (ch.e.open_target.mem_nhds (ch.e.map_source hch)) ?_
        exact (ch.e.continuousAt_symm (ch.e.map_source hch)).preimage_mem_nhds (hy''.symm ▸ hg)
      exact ((contDiffOn_chart (fun z hz => hz) ch).contDiffAt hs).of_le (by norm_cast)
    have h1 := (Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hn hre)).add
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hn him)).mul (contDiffAt_const (c := Complex.I)))
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    simp only [Function.comp_apply, Complex.ofRealCLM_apply, K]
    exact (Complex.re_add_im _).symm
  have hKu : ∀ τ, IsUnit (K (φ v) τ).det := by
    intro τ
    have hp := hM.posDef y hyO A hA τ
    show IsUnit (lieGram e U hj f₀ A₀ A (ch.e.symm (ch.e y)) τ).det
    rw [hy'']
    exact (Matrix.isUnit_iff_isUnit_det _).1 hp.isUnit
  have key := GlobalTheory.ChernPull.chernTop_comp (pointPoly H Dw) K φ v hφ hK2 hKu
  have hcont : ContinuousAt (fun u => ψ (GlobalTheory.UnifDens.flatL h u)) v :=
    (hholo.1.continuousAt (GlobalTheory.PoincareLower.isOpen_domFlat.mem_nhds hv)).comp
      (GlobalTheory.UnifDens.flatL h).continuous.continuousAt
  have hg : (fun u => lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h u))) =ᶠ[𝓝 v] fun w => K (φ w) := by
    filter_upwards [hcont.preimage_mem_nhds (ch.e.open_source.mem_nhds hch)] with w hw
    simp only [K, φ, ch.e.left_inv hw]
  rw [GlobalTheory.ChernWeilLine.chernTop_congr _ hg, key]
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_class_density_uniformisation_chart_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ ch : AlgChart X.str (σ.comp e.toRingHom) X.dim, ψ (GlobalTheory.UnifDens.flatL h v) ∈ ch.e.source → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), chernTop (pointPoly H Dw) (fun u => lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h u))) v = Complex.normSq (LinearMap.det (fderiv ℂ (fun u => ch.e (ψ (GlobalTheory.UnifDens.flatL h u))) v : ReciprocityTheory.L2DbarEstimates.V X.dim →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V X.dim)) * chernTop (pointPoly H Dw) (fun u => lieGram e U hj f₀ A₀ A (ch.e.symm u)) (ch.e (ψ (GlobalTheory.UnifDens.flatL h v))) := by
  atlas_forward_decl GlobalTheory.UnifDens.chernTop_unif_chart
end

section
section
open Formalism.DegreeFormula

open Matrix Formalism.MJ Formalism.UG GlobalTheory.HodgeDomain GlobalTheory.HermFrame GlobalTheory.TrueCx
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.DomDensInv

variable {ι : Type} [Fintype ι] {p q n : ℕ}

theorem unflat_zero : unflat (0 : ι × Fin p × Fin q → ℂ) = 0 := by
  funext i; ext a b; rfl

theorem exists_upqI {z : ι → Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ DomI ι p q) :
    ∃ g ∈ UpqI ι p q, moebI g 0 = z := by
  have : ∀ τ, ∃ g : GL (Fin p ⊕ Fin q) ℂ, g ∈ Upq p q ∧ moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) 0 = z τ := by
    intro τ
    obtain ⟨g, hg, hgz⟩ := GlobalTheory.TrueCx.FrameOnto.exists_moeb_zero (hz τ)
    have hd : g.det ≠ 0 := by
      intro h0
      have h1 := congrArg det hg
      have h2 := congrArg det (Jpq_sq (p := p) (q := q))
      rw [det_mul, h0, mul_zero] at h1
      rw [det_mul, ← h1] at h2
      simp at h2
    exact ⟨GeneralLinearGroup.mkOfDetNeZero _ hd, upq_iff.2 hg, hgz⟩
  choose g hg hgz using this
  exact ⟨g, fun τ _ => hg τ, funext fun τ => hgz τ⟩

theorem normSq_det_jW {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) :
    Complex.normSq (jW g 0).det = ((hQ (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) 0)).det).re := by
  have h := hP_moeb hg (zero_mem_hcDom p q)
  have e0 : hP (0 : Matrix (Fin p) (Fin q) ℂ) = 1 := by simp [hP]
  rw [e0, Matrix.mul_one] at h
  have h2 := congrArg Matrix.det h
  rw [det_mul, det_conjTranspose, hP, det_one_sub_mul_comm] at h2
  rw [hQ, ← h2, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

theorem normSq_det_kapQ_inv {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) :
    Complex.normSq ((kapQ g 0)⁻¹).det = ((hQ (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) 0)).det).re := by
  have h := hQ_moeb hg (zero_mem_hcDom p q)
  have e0 : hQ (0 : Matrix (Fin p) (Fin q) ℂ) = 1 := by simp [hQ]
  rw [e0] at h
  have h2 := congrArg Matrix.det h
  rw [det_mul, det_mul, det_conjTranspose, det_one] at h2
  set d := (kapQ g 0).det
  set H := (hQ (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) 0)).det
  have h3 : H * ((Complex.normSq d : ℝ) : ℂ) = 1 := by
    rw [← Complex.mul_conj, ← h2, Complex.star_def]; ring
  have h4 : H = ((Complex.normSq d : ℝ) : ℂ)⁻¹ := eq_inv_of_mul_eq_one_left h3
  rw [det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀, h4, ← Complex.ofReal_inv, Complex.ofReal_re]

end GlobalTheory.DomDensInv

namespace GlobalTheory.DomDensInv

variable {ι : Type} [Fintype ι] {p q n : ℕ}

theorem det_flat_mul (A : ι → Matrix (Fin p) (Fin p) ℂ) (B : ι → Matrix (Fin q) (Fin q) ℂ)
    (L : (ι × Fin p × Fin q → ℂ) →ₗ[ℂ] (ι × Fin p × Fin q → ℂ))
    (hL : ∀ x, L x = flat (fun τ => A τ * unflat x τ * B τ)) :
    LinearMap.det L = ∏ τ, (A τ).det ^ q * (B τ).det ^ p := by
  let E : (ι × Fin p × Fin q → ℂ) ≃ₗ[ℂ] (ι → Matrix (Fin p) (Fin q) ℂ) :=
    { toFun := unflat, invFun := flat, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have key : (E : (ι × Fin p × Fin q → ℂ) →ₗ[ℂ] (ι → Matrix (Fin p) (Fin q) ℂ)) ∘ₗ L ∘ₗ
      (E.symm : (ι → Matrix (Fin p) (Fin q) ℂ) →ₗ[ℂ] (ι × Fin p × Fin q → ℂ)) =
      LinearMap.pi fun τ => (GlobalTheory.ModuLR.lrLin (A τ) (B τ)).comp (LinearMap.proj τ) := by
    refine LinearMap.ext fun x => funext fun τ => ?_
    change unflat (L (flat x)) τ = A τ * x τ * B τ
    rw [hL]; rfl
  rw [← LinearMap.det_conj L E, key, LinearMap.det_pi]
  simp only [GlobalTheory.ModuLR.det_lrLin, Fintype.card_fin]

theorem model_smooth (h : Fintype.card (ι × Fin p × Fin q) = n) {u : ReciprocityTheory.L2DbarEstimates.V n}
    (hu : GlobalTheory.UnifDens.flatL h u ∈ DomFlat ι p q) (τ : ι) :
    MContDiffAt 2 (fun w : ReciprocityTheory.L2DbarEstimates.V n => ((hP (unflat (GlobalTheory.UnifDens.flatL h w) τ))⁻¹)ᵀ) u ∧
      IsUnit (((hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹)ᵀ).det := by
  have hp := hP_posDef (hu τ)
  have hunit : IsUnit (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ)).det := hp.det_pos.ne'.isUnit
  refine ⟨MContDiffAt.transpose (MContDiffAt.inv ?_ hunit), ?_⟩
  · have hY : MContDiffAt 2 (fun w : ReciprocityTheory.L2DbarEstimates.V n => unflat (GlobalTheory.UnifDens.flatL h w) τ) u := by
      intro a b
      have e : (fun w : ReciprocityTheory.L2DbarEstimates.V n => unflat (GlobalTheory.UnifDens.flatL h w) τ a b) =
          fun w => (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι × Fin p × Fin q => ℂ) (τ, a, b)).comp
            (GlobalTheory.UnifDens.flatL h : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (ι × Fin p × Fin q → ℂ))).restrictScalars ℝ) w := rfl
      rw [e]; exact (ContinuousLinearMap.contDiff _).contDiffAt
    exact (mContDiffAt_const 1).sub (hY.mul hY.conjTranspose)
  · rw [det_transpose]; exact isUnit_nonsing_inv_det _ hunit

theorem gram_transpose_of_congr {J Hg Hy : Matrix (Fin p) (Fin p) ℂ} (hJ : IsUnit J.det) (h : Jᴴ * Hg * J = Hy) :
    Hgᵀ = (J⁻¹)ᵀ * Hyᵀ * ((J⁻¹)ᵀ)ᴴ := by
  have hJ' : IsUnit Jᴴ.det := by rw [det_conjTranspose]; exact hJ.star
  have h1 : Hg = (J⁻¹)ᴴ * Hy * J⁻¹ := by
    rw [← h, conjTranspose_nonsing_inv]
    simp only [← Matrix.mul_assoc, nonsing_inv_mul _ hJ', Matrix.one_mul]
    rw [Matrix.mul_assoc, mul_nonsing_inv _ hJ, Matrix.mul_one]
  rw [h1, transpose_mul, transpose_mul]
  have e : ((J⁻¹)ᴴ)ᵀ = ((J⁻¹)ᵀ)ᴴ := by ext i j; rfl
  rw [e, Matrix.mul_assoc]

theorem chernTop_model_moeb : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n) (v : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.UnifDens.flatL h v ∈ Formalism.DegreeFormula.DomFlat ι p q → GlobalTheory.GoodMetric.chernTop (m := fun _ : ι => p) (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q) (fun u τ => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) v = GlobalTheory.GoodMetric.chernTop (m := fun _ : ι => p) (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q) (fun u τ => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) 0 * ∏ i, ((Formalism.DegreeFormula.hQ (Formalism.DegreeFormula.unflat (GlobalTheory.UnifDens.flatL h v) i)).det.re) ^ (-((p + q : ℕ) : ℤ)) := by
  intro ι _ p q n h v hv
  classical
  set e := GlobalTheory.UnifDens.flatL h with he
  set K : ReciprocityTheory.L2DbarEstimates.V n → ι → Matrix (Fin p) (Fin p) ℂ := fun u τ => ((hP (unflat (e u) τ))⁻¹)ᵀ with hK
  set R : MvPolynomial (ι × ℕ) ℝ := ∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q with hR
  set z := unflat (e v) with hz
  have hzD : z ∈ DomI ι p q := hv
  obtain ⟨g, hg, hgz⟩ := exists_upqI hzD
  set Φ : (ι × Fin p × Fin q → ℂ) → (ι × Fin p × Fin q → ℂ) := fun w => flat (moebI g (unflat w)) with hΦ
  set φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n := fun u => e.symm (Φ (e u)) with hφ
  have h0D : (0 : ι × Fin p × Fin q → ℂ) ∈ DomFlat ι p q := by
    intro τ; rw [unflat_zero]; exact zero_mem_hcDom p q
  have he0 : e 0 = 0 := map_zero e
  have hφ0 : φ 0 = v := by
    show e.symm (flat (moebI g (unflat (e 0)))) = v
    rw [he0, unflat_zero, hgz]
    exact e.symm_apply_apply v
  obtain ⟨ho, H⟩ := GlobalTheory.HodgeDomain.ActionDeriv.isOpen_and_fderiv_moebI ι p q
  obtain ⟨hd, hD⟩ := H g hg
  have hΦan : AnalyticAt ℂ Φ 0 := GlobalTheory.SCV.analyticOnNhd_of_differentiableOn ho hd 0 h0D
  have hΦan' : AnalyticAt ℂ Φ (e 0) := by rw [he0]; exact hΦan
  have hφan : AnalyticAt ℂ φ 0 :=
    (e.symm : (ι × Fin p × Fin q → ℂ) →L[ℂ] ReciprocityTheory.L2DbarEstimates.V n).analyticAt _ |>.comp
      (hΦan'.comp ((e : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (ι × Fin p × Fin q → ℂ)).analyticAt 0))
  have hKv := fun τ => model_smooth h (u := v) hv τ
  have h0S : e 0 ∈ DomFlat ι p q := by rw [he0]; exact h0D
  have hK0 := fun τ => model_smooth h (u := 0) h0S τ

  have hA := GlobalTheory.ChernPull.chernTop_comp R K φ 0 hφan (by rw [hφ0]; exact fun τ => (hKv τ).1)
    (by rw [hφ0]; exact fun τ => (hKv τ).2)
  rw [hφ0] at hA

  set S : Set (ReciprocityTheory.L2DbarEstimates.V n) := e ⁻¹' DomFlat ι p q with hS
  have hSo : IsOpen S := ho.preimage e.continuous
  have h0S' : (0 : ReciprocityTheory.L2DbarEstimates.V n) ∈ S := h0S
  set g' : ReciprocityTheory.L2DbarEstimates.V n → ι → Matrix (Fin p) (Fin p) ℂ :=
    fun w τ => ((jW (g τ) (unflat (e w) τ))⁻¹)ᵀ with hg'
  have hΦcd : ContDiffOn ℂ 1 Φ (DomFlat ι p q) :=
    (GlobalTheory.SCV.analyticOnNhd_of_differentiableOn ho hd).contDiffOn ho.uniqueDiffOn
  have hΨ : ContDiffOn ℂ 1 (fun w => Φ (e w)) S :=
    hΦcd.comp (e : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (ι × Fin p × Fin q → ℂ)).contDiff.contDiffOn fun w hw => hw
  have hg'an : ∀ τ i j, AnalyticAt ℂ (fun w => g' w τ i j) 0 := by
    intro τ i j
    have hent : ∀ a b, ContDiffOn ℂ 1 (fun w => jW (g τ) (unflat (e w) τ) a b) S := by
      intro a b
      have ee : (fun w => jW (g τ) (unflat (e w) τ) a b) = fun w =>
          (g τ).1.toBlocks₁₁ a b - ∑ k, Φ (e w) (τ, a, k) * (g τ).1.toBlocks₂₁ k b := by
        funext w; simp only [jW, Matrix.sub_apply, Matrix.mul_apply]; rfl
      rw [ee]
      exact contDiffOn_const.sub (ContDiffOn.sum fun k _ => ((contDiffOn_pi.1 hΨ) (τ, a, k)).mul contDiffOn_const)
    have hinv := GlobalTheory.HodgeDomain.ActionDeriv.diffOn_inv (s := S) (M := fun w => jW (g τ) (unflat (e w) τ)) hent
      (fun w hw => (jW_isUnit (hg τ (Set.mem_univ _)) (hw τ)).ne_zero) j i
    exact GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hSo (hinv.differentiableOn one_ne_zero) 0 h0S'
  have hg'u : ∀ τ, IsUnit (g' 0 τ).det := by
    intro τ
    rw [hg', det_transpose]
    exact isUnit_nonsing_inv_det _ (jW_isUnit (hg τ (Set.mem_univ _)) (h0S τ))
  have hev : ∀ᶠ w in nhds (0 : ReciprocityTheory.L2DbarEstimates.V n), ∀ τ, K (φ w) τ =
      (((fun _ : ι => (1 : ℝ)) τ : ℝ) : ℂ) • (g' w τ * K w τ * (g' w τ)ᴴ) := by
    filter_upwards [hSo.mem_nhds h0S'] with w hw τ
    have hy : unflat (e w) τ ∈ hcDom p q := hw τ
    have hgt := hg τ (Set.mem_univ _)
    have key := gram_transpose_of_congr (jW_isUnit hgt hy) (hP_inv_moeb hgt hy)
    have e1 : K (φ w) τ = ((hP (moeb ((g τ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (unflat (e w) τ)))⁻¹)ᵀ := by
      show ((hP (unflat (e (e.symm (Φ (e w)))) τ))⁻¹)ᵀ = _
      rw [e.apply_symm_apply]; rfl
    rw [e1, key, Complex.ofReal_one, one_smul]
  have hB := GlobalTheory.PointChern.chernTop_changeFrame R (fun w => K (φ w)) K g' (fun _ => (1 : ℝ)) 0
    (fun _ => one_pos) hg'an hg'u (fun τ => (hK0 τ).1) (fun τ => (hK0 τ).2) hev

  have hΦd : HasFDerivAt Φ (fderiv ℂ Φ 0) (e 0) := by rw [he0]; exact hΦan.differentiableAt.hasFDerivAt
  have hφd : HasFDerivAt φ ((e.symm : (ι × Fin p × Fin q → ℂ) →L[ℂ] ReciprocityTheory.L2DbarEstimates.V n).comp
      ((fderiv ℂ Φ 0).comp (e : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (ι × Fin p × Fin q → ℂ)))) 0 :=
    e.symm.hasFDerivAt.comp 0 (hΦd.comp 0 e.hasFDerivAt)
  have hdetF : LinearMap.det (fderiv ℂ Φ 0 : (ι × Fin p × Fin q → ℂ) →ₗ[ℂ] (ι × Fin p × Fin q → ℂ)) =
      ∏ τ, (jW (g τ) 0).det ^ q * ((kapQ (g τ) 0)⁻¹).det ^ p := by
    refine det_flat_mul _ _ _ fun x => ?_
    have := hD 0 (fun τ => zero_mem_hcDom p q) (unflat x)
    exact this
  have hdet : LinearMap.det (fderiv ℂ φ 0 : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V n) =
      ∏ τ, (jW (g τ) 0).det ^ q * ((kapQ (g τ) 0)⁻¹).det ^ p := by
    rw [hφd.fderiv, ← hdetF, ← LinearMap.det_conj (fderiv ℂ Φ 0 : (ι × Fin p × Fin q → ℂ) →ₗ[ℂ] (ι × Fin p × Fin q → ℂ))
      e.symm.toLinearEquiv]
    rfl
  have hx : ∀ τ, Complex.normSq (jW (g τ) 0).det = ((hQ (z τ)).det).re ∧
      Complex.normSq ((kapQ (g τ) 0)⁻¹).det = ((hQ (z τ)).det).re := by
    intro τ
    have hgt := hg τ (Set.mem_univ _)
    have hzτ : moeb ((g τ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) 0 = z τ := congrFun hgz τ
    rw [← hzτ]
    exact ⟨normSq_det_jW hgt, normSq_det_kapQ_inv hgt⟩
  have hN : Complex.normSq (LinearMap.det (fderiv ℂ φ 0 : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V n)) =
      ∏ τ, ((hQ (z τ)).det).re ^ (p + q) := by
    rw [hdet, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_mul, map_pow, map_pow, (hx τ).1, (hx τ).2, pow_add, mul_comm]
  have hpos : ∀ τ, 0 < ((hQ (z τ)).det).re := fun τ =>
    (Complex.pos_iff.1 (show (hQ (z τ)).PosDef from hzD τ).det_pos).1
  have hNpos : 0 < ∏ τ, ((hQ (z τ)).det).re ^ (p + q) := Finset.prod_pos fun τ _ => pow_pos (hpos τ) _
  rw [hB, hN] at hA
  have e2 : ∏ τ, ((hQ (z τ)).det).re ^ (-((p + q : ℕ) : ℤ)) = (∏ τ, ((hQ (z τ)).det).re ^ (p + q))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [_root_.zpow_neg, zpow_natCast]
  show GlobalTheory.GoodMetric.chernTop R K v = GlobalTheory.GoodMetric.chernTop R K 0 * ∏ τ, ((hQ (z τ)).det).re ^ (-((p + q : ℕ) : ℤ))
  rw [e2, hA]
  field_simp

end GlobalTheory.DomDensInv
end
end

open Formalism.DegreeFormula

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernPolyTopDensity_bounded_domain_invariant : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n) (v : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.UnifDens.flatL h v ∈ Formalism.DegreeFormula.DomFlat ι p q → GlobalTheory.GoodMetric.chernTop (m := fun _ : ι => p) (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q) (fun u τ => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) v = GlobalTheory.GoodMetric.chernTop (m := fun _ : ι => p) (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q) (fun u τ => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) 0 * ∏ i, ((Formalism.DegreeFormula.hQ (Formalism.DegreeFormula.unflat (GlobalTheory.UnifDens.flatL h v) i)).det.re) ^ (-((p + q : ℕ) : ℤ)) := by
  atlas_forward_decl GlobalTheory.DomDensInv.chernTop_model_moeb
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix
open Filter Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameLift

open Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ShFam.SecFrame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ} (hj : j ≤ r)
  {Tau : Type} (κ : Tau ≃ X.Ψ)

theorem analyticAt_frameAt [Fintype Tau] (τ : X.Ψ) (a b : Fin r) (v₀ : Tau × Fin j × Fin (r - j) → ℂ) :
    AnalyticAt ℂ (fun v : Tau × Fin j × Fin (r - j) → ℂ => mat (frameAt X hj κ (unflat v)) τ a b) v₀ := by
  have hM : ∀ c, AnalyticAt ℂ (fun v : Tau × Fin j × Fin (r - j) → ℂ =>
      ((reindex (idx hj) (idx hj)).symm (fromBlocks 1 (unflat v (κ.symm τ)) 0 1)) c b) v₀ := by
    intro c
    simp only [reindex_symm, reindex_apply, Equiv.symm_symm, submatrix_apply]
    rcases (idx hj) c with c' | c' <;> rcases (idx hj) b with b' | b' <;>
      simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, unflat, of_apply] <;>
      first | exact analyticAt_const | exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Tau × Fin j × Fin (r - j) => ℂ) _).analyticAt _
  simp only [mat_frameAt, mul_apply]
  exact Finset.analyticAt_fun_sum _ fun c _ => analyticAt_const.fun_mul (hM c)

end GlobalTheory.FrameLift

open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ShFam.SecFrame in

theorem GlobalTheory.FrameLift.exists_analytic_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (p q n : ℕ) (Xd : ReciprocityTheory.ChartRestriction.G.FD.Data E (p + q)), Xd.p0 = p + q - p → ∀ (h : Fintype.card (Xd.Ψ × Fin p × Fin (p + q - p)) = n) (v : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.UnifDens.flatL h v ∈ DomFlat Xd.Ψ p (p + q - p) → ∃ s : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.ChartRestriction.G.FD.Frame Xd.Ψ (p + q), AnalyticAt ℂ s v ∧ (∀ (τ : Xd.Ψ) (a b : Fin p), AnalyticAt ℂ (fun w => coW Xd (Nat.le_add_right p q) (s w) τ a b) v) ∧ ∀ᶠ w in nhds v, ∃ hs : s w ∈ Xd.dom, flat (domPt Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) (s w)) = GlobalTheory.UnifDens.flatL h w := by
  intro E _ _ _ p q n Xd hp h v hv
  refine ⟨fun w => frameAt Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) (unflat (GlobalTheory.UnifDens.flatL h w)), ?_, ?_, ?_⟩
  · rw [analyticAt_pi_iff]; intro τ
    rw [analyticAt_pi_iff]; intro a
    rw [analyticAt_pi_iff]; intro b
    have hL : AnalyticAt ℂ (GlobalTheory.UnifDens.flatL h) v := (GlobalTheory.UnifDens.flatL h).toContinuousLinearMap.analyticAt v
    exact (GlobalTheory.FrameLift.analyticAt_frameAt Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) τ a b
      (GlobalTheory.UnifDens.flatL h v)).comp hL
  · intro τ a b
    have e : (fun w => coW Xd (Nat.le_add_right p q)
        (frameAt Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) (unflat (GlobalTheory.UnifDens.flatL h w))) τ a b) =
        fun _ => (1 : Matrix (Fin p) (Fin p) ℂ) a b := by
      funext w; rw [(co_frameAt Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) _ τ).1]
    rw [e]; exact analyticAt_const
  · have ho : IsOpen (DomFlat Xd.Ψ p (p + q - p)) := GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat
    filter_upwards [(GlobalTheory.UnifDens.flatL h).continuous.continuousAt.preimage_mem_nhds (ho.mem_nhds hv)] with w hw
    refine ⟨frameAt_mem Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) hp hw, ?_⟩
    rw [domPt_frameAt]
    rfl
end
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analytic_flagDomain_section_flatCoordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (p q n : ℕ) (Xd : ReciprocityTheory.ChartRestriction.G.FD.Data E (p + q)), Xd.p0 = p + q - p → ∀ (h : Fintype.card (Xd.Ψ × Fin p × Fin (p + q - p)) = n) (v : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.UnifDens.flatL h v ∈ DomFlat Xd.Ψ p (p + q - p) → ∃ s : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.ChartRestriction.G.FD.Frame Xd.Ψ (p + q), AnalyticAt ℂ s v ∧ (∀ (τ : Xd.Ψ) (a b : Fin p), AnalyticAt ℂ (fun w => coW Xd (Nat.le_add_right p q) (s w) τ a b) v) ∧ ∀ᶠ w in nhds v, ∃ hs : s w ∈ Xd.dom, flat (domPt Xd (Nat.le_add_right p q) (Equiv.refl Xd.Ψ) (s w)) = GlobalTheory.UnifDens.flatL h w := by
  atlas_forward_decl GlobalTheory.FrameLift.exists_analytic_section
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix
open Filter Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifFrame

section SlopeTestRemainingChoices

variable {F : Type} [Field F] {X : Var F} {σ' : F →+* ℂ}

theorem eventually_mem_frames {ι : Type} [Finite ι] {m : ι → ℕ} {S : Fr (ratOf X) m 0} {y : CxPts X.str σ'}
    {A : Mat m X.Fn} (hA : A ∈ S.S (under y)) : ∀ᶠ z in 𝓝 y, A ∈ S.S (under z) := by
  obtain ⟨U, B, hU, hB, hS⟩ := S.loc (under y)
  have hP := (hS _ hU A).1 hA
  have hreg : ∀ g : X.Fn, RegAt (under y) g → ∀ᶠ z in 𝓝 y, RegAt (under z) g := by
    intro g hg
    obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
    filter_upwards [(isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)] with z hz
    exact regAt_fnOf (mem_ptsIn.1 hz) _ a
  have hU' : ∀ᶠ z in 𝓝 y, under z ∈ U := by
    filter_upwards [(isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU)] with z hz
    exact mem_ptsIn.1 hz
  have h1 : ∀ᶠ z in 𝓝 y, ∀ τ, (∀ i j, RegAt (under z) ((A * B⁻¹) τ i j)) ∧ RegAt (under z) ((A * B⁻¹) τ).det⁻¹ :=
    Filter.eventually_all.2 fun τ => (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      hreg _ (mem_O_ratOf.1 ((hP τ).1 i j))).and (hreg _ (mem_O_ratOf.1 (hP τ).2.2.1))
  filter_upwards [hU', h1] with z hz hz1
  exact (hS _ hz A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 ((hz1 τ).1 i j), (hP τ).2.1, mem_O_ratOf.2 (hz1 τ).2,
    fun i j hi => absurd hi (by simp)⟩

end SlopeTestRemainingChoices

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {σ : c.F →+* ℂ} {e : F ≃+* c.F} {X : Var F} {j : X.X ⟶ gen Z}
  {f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)} {S : Fr (ratOf X) Dw.mult 0} {A₀ : Mat Dw.mult X.Fn}

theorem exists_frame_of_tied (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (hT : Tied e X j f₀ S A₀)
    (y : CxPts X.str (σ.comp e.toRingHom)) {A : Mat Dw.mult X.Fn} (hA : A ∈ S.S (under y)) :
    ∃ g : EigFrame Z σ ((cxOf e σ hj y).1 ≫ genι Z), FrameAt e f₀ A₀ A y g := by
  obtain ⟨φ, fz, hc⟩ := hT.2 (under y) A hA
  have hy : y.1 = spMap (Var.evStalk y) ≫ stalkPt X (under y) :=
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk y.1).symm
  have hφ : σ = (Var.evStalk y).comp φ := RingHom.ext fun a => by
    have h3 : φ a = algebraMap F _ (e.symm a) := IsFractionRing.injective _ X.X.functionField
      ((RingHom.congr_fun hc.2.1 a).symm.trans ((X.stalkIncl (under y)).commutes _).symm)
    show σ a = Var.evStalk y (φ a)
    rw [h3]
    refine Eq.trans ?_ ((Var.evStalk_germ (U := ⊤) trivial _).trans (ev_algX mem_ptsIn_top _)).symm
    simp
  have hx : (cxOf e σ hj y).1 ≫ genι Z = spMap (Var.evStalk y) ≫ stalkPt X (under y) ≫ j ≫ genι Z := by
    show (y.1 ≫ j) ≫ genι Z = _
    rw [hy]
    exact Category.assoc _ _ _
  obtain ⟨g, hg⟩ := fz.exists_isMap (Var.evStalk y) hφ hx
  exact ⟨g, φ, fz, Var.evStalk y, hy, hc, hg⟩

end Frame

theorem eventually_frameAt_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (X : Var F) (j : X.X ⟶ gen T.Z) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), ∀ᶠ w in nhds v, ∃ g : EigFrame T.Z σ ((cxOf e σ hj (ψ (GlobalTheory.UnifDens.flatL h w))).1 ≫ genι T.Z), FrameAt e f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h w)) g := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU k X j f₀ Eb A₀ hj hji hT ψ hψ h v hv A hA
  classical
  have hp0 : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by rw [(hU.2.1 k).1]; omega
  let L : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) ≃L[ℂ]
      (Fin (Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p))) → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin _).symm).toContinuousLinearEquiv
  have ho : IsOpen (DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p)) := GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat
  set B : Set (Fin (Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p))) → ℂ) :=
    L.symm ⁻¹' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) with hBdef
  have hB : IsOpen B := ho.preimage L.symm.continuous
  let x : (Fin (Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p))) → ℂ) → (U.X k).dom := fun b =>
    stdFrame (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl _) hp0 (unflat (L.symm b))
  have hd : ∀ τ a c, DifferentiableOn ℂ (fun b => ReciprocityTheory.ChartRestriction.G.FD.mat (x b).1 τ a c) B := fun τ a c =>
    ((GlobalTheory.TrueCx.TorHolo.differentiable_stdMat (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl _) τ a c).comp
      L.symm.differentiable).differentiableOn.congr fun b hb => by
        show ReciprocityTheory.ChartRestriction.G.FD.mat (stdFrame _ _ _ _ _).1 τ a c = _
        rw [stdFrame_val _ _ _ _ hb]
        rfl
  have hY := GlobalTheory.GramFamily.isHolTo_cxPt T.Z hU k hB x hd
  have key : ∀ v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p),
      cxOf e σ hj (ψ v) = cxPt T.Z (U.un k (x (L v))) := by
    intro v hv
    have h1 := hψ (x (L v))
    have h2 : flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) (x (L v)).1) = v := by
      show flat (domPt _ _ _ (stdFrame _ _ _ hp0 (unflat (L.symm (L v)))).1) = v
      rw [L.symm_apply_apply, domPt_stdFrame _ _ _ hp0 hv]
      rfl
    rw [h2] at h1
    exact h1
  have hcont : ContinuousOn (fun b => cxPt T.Z (U.un k (x b))) B := by
    rw [continuousOn_iff_continuous_restrict]
    refine GlobalTheory.CxPts.continuous_iff.2 fun W => ⟨?_, fun g => ?_⟩
    · have := (hY W 0).1.preimage (continuous_subtype_val (p := (· ∈ B)))
      convert this using 1
      ext v
      simp only [Set.mem_preimage, Set.restrict_apply, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨v.2, h⟩, fun h => h.2⟩
    · intro v hv
      have hm : (v : Fin _ → ℂ) ∈ {b ∈ B | ⊤ ≤ (cxPt T.Z (U.un k (x b))).1 ⁻¹ᵁ W} := ⟨v.2, hv⟩
      have hca := (((hY W g).2).differentiableAt (((hY W g).1).mem_nhds hm)).continuousAt
      exact (hca.comp continuous_subtype_val.continuousAt).continuousWithinAt
  have hκ := isOpenEmbedding_cxOf e σ hj
  have hLB : ∀ v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), L v ∈ B := fun v hv => by
    show L.symm (L v) ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p)
    rwa [L.symm_apply_apply]
  have hψc : ContinuousOn ψ (DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p)) := by
    rw [hκ.isInducing.continuousOn_iff]
    exact (hcont.comp L.continuous.continuousOn hLB).congr fun v hv => key v hv
  have hc : ContinuousAt (fun u => ψ (GlobalTheory.UnifDens.flatL h u)) v :=
    (hψc.continuousAt (ho.mem_nhds hv)).comp (GlobalTheory.UnifDens.flatL h).continuous.continuousAt
  filter_upwards [hc.eventually (eventually_mem_frames hA)] with w hw
  exact exists_frame_of_tied hj hT _ hw

end GlobalTheory.UnifFrame
end
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_lieEigenspaceFrameAt_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (X : Var F) (j : X.X ⟶ gen T.Z) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), ∀ᶠ w in nhds v, ∃ g : EigFrame T.Z σ ((cxOf e σ hj (ψ (GlobalTheory.UnifDens.flatL h w))).1 ≫ genι T.Z), FrameAt e f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h w)) g := by
  atlas_forward_decl GlobalTheory.UnifFrame.eventually_frameAt_unif
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix
open Filter Topology
open GlobalTheory.PointChern

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifFrameChange

theorem isHolTo_cxPt_V {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) {σ : c.F →+* ℂ}
    {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) {n : ℕ}
    {B : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hB : IsOpen B) (x : ReciprocityTheory.L2DbarEstimates.V n → (U.X k).dom)
    (hd : ∀ τ a a', DifferentiableOn ℂ (fun b => ReciprocityTheory.ChartRestriction.G.FD.mat (x b).1 τ a a') B) :
    IsHolTo B fun b => (cxPt Z (U.un k (x b))).1 := by
  let L := EuclideanSpace.equiv (Fin n) ℂ
  have hB₁ : IsOpen (L.symm ⁻¹' B) := hB.preimage L.symm.continuous
  have h1 := GlobalTheory.GramFamily.isHolTo_cxPt Z hU k hB₁ (fun u => x (L.symm u)) fun τ a a' =>
    (hd τ a a').comp L.symm.differentiableOn fun u hu => hu
  intro W f
  obtain ⟨ho, hdf⟩ := h1 W f
  have hset : {b ∈ B | ⊤ ≤ (cxPt Z (U.un k (x b))).1 ⁻¹ᵁ W} =
      L ⁻¹' {u ∈ L.symm ⁻¹' B | ⊤ ≤ (cxPt Z (U.un k (x (L.symm u)))).1 ⁻¹ᵁ W} := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply]
  rw [hset]
  refine ⟨ho.preimage L.continuous, ?_⟩
  have := hdf.comp L.differentiableOn (Set.mapsTo_preimage _ _)
  refine this.congr fun b _ => ?_
  simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]

end GlobalTheory.UnifFrameChange

open GlobalTheory.UnifFrameChange in

theorem GlobalTheory.UnifFrameChange.exists_holomorphic_frame_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (X : Var F) (j : X.X ⟶ gen T.Z) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), ∀ s : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ (Dw.p + Dw.q), AnalyticAt ℂ s v → (∀ᶠ w in nhds v, ∃ hs : s w ∈ (U.X k).dom, flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) (s w)) = GlobalTheory.UnifDens.flatL h w) → ∃ K : ReciprocityTheory.L2DbarEstimates.V X.dim → Mat Dw.mult ℂ, (∀ τ a b, AnalyticAt ℂ (fun w => K w τ a b) v) ∧ (∀ τ, IsUnit (K v τ).det) ∧ ∀ᶠ w in nhds v, ∀ (hs : s w ∈ (U.X k).dom) (g : EigFrame T.Z σ ((cxOf e σ hj (ψ (GlobalTheory.UnifDens.flatL h w))).1 ≫ genι T.Z)), FrameAt e f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h w)) g → ∀ (M : EigMet T.Z σ) (τ : E →+* ℂ), M.gram (cxOf e σ hj (ψ (GlobalTheory.UnifDens.flatL h w))) g τ = (K w τ)ᴴ * M.gram (cxPt T.Z (U.un k ⟨s w, hs⟩)) (cxFrame T.Z (U.un k ⟨s w, hs⟩)) τ * K w τ := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _ hU k X j f₀ Eb A₀ hj hoi hT ψ hψ h v _ A hA s han hlift
  classical

  set pt : ReciprocityTheory.L2DbarEstimates.V X.dim → CxPts X.str (σ.comp e.toRingHom) := fun w => ψ (GlobalTheory.UnifDens.flatL h w) with hptdef

  obtain ⟨B₀, hB₀all, hB₀, hv₀⟩ := eventually_nhds_iff.1 (hlift.and han.eventually_analyticAt)
  choose hsB₀ hflB₀ using fun b (hb : b ∈ B₀) => (hB₀all b hb).1
  have hpt₀ : ∀ b (hb : b ∈ B₀), cxPt T.Z (U.un k ⟨s b, hsB₀ b hb⟩) = cxOf e σ hj (pt b) := by
    intro b hb
    have := hψ ⟨s b, hsB₀ b hb⟩
    rw [hflB₀ b hb] at this
    exact this.symm
  let x : ReciprocityTheory.L2DbarEstimates.V X.dim → (U.X k).dom := fun b =>
    if hb : b ∈ B₀ then ⟨s b, hsB₀ b hb⟩ else ⟨s v, hsB₀ v hv₀⟩
  have hxB : ∀ b (hb : b ∈ B₀), x b = ⟨s b, hsB₀ b hb⟩ := fun b hb => by simp only [x, dif_pos hb]
  have hsd : DifferentiableOn ℂ s B₀ := fun b hb => (hB₀all b hb).2.differentiableAt.differentiableWithinAt
  have hd : ∀ τ a a', DifferentiableOn ℂ (fun b => ReciprocityTheory.ChartRestriction.G.FD.mat (x b).1 τ a a') B₀ := by
    intro τ a a'
    refine (differentiableOn_pi.1 (differentiableOn_pi.1 (differentiableOn_pi.1 hsd τ) a) a').congr fun b hb => ?_
    rw [hxB b hb]
    rfl
  have hY := isHolTo_cxPt_V T.Z hU k hB₀ x hd
  have hxpt : ∀ b (hb : b ∈ B₀), (cxPt T.Z (U.un k (x b))) = cxOf e σ hj (pt b) := fun b hb => by
    rw [hxB b hb]; exact hpt₀ b hb

  have hgenev : ∀ W' : (gen T.Z).Opens, cxOf e σ hj (pt v) ∈ ptsIn (genStr T.Z) σ W' →
      ∀ᶠ w in 𝓝 v, w ∈ B₀ ∧ ⊤ ≤ (cxPt T.Z (U.un k (x w))).1 ⁻¹ᵁ W' := by
    intro W' hW'
    refine ((hY W' 0).1).mem_nhds ⟨hv₀, ?_⟩
    show ⊤ ≤ (cxPt T.Z (U.un k (x v))).1 ⁻¹ᵁ W'
    rw [hxpt v hv₀]
    exact hW'
  have hpre : ∀ (W : X.X.Opens) (z : CxPts X.str (σ.comp e.toRingHom)),
      z ∈ ptsIn X.str (σ.comp e.toRingHom) W ↔ cxOf e σ hj z ∈ ptsIn (genStr T.Z) σ (j ''ᵁ W) := by
    intro W z
    have := mem_ptsIn_preimage (m := cxOf e σ hj) (f := j) (fun _ => rfl) (U := j ''ᵁ W) (z := z)
    rwa [j.preimage_image_eq W] at this
  have hXev : ∀ W : X.X.Opens, pt v ∈ ptsIn X.str (σ.comp e.toRingHom) W →
      ∀ᶠ w in 𝓝 v, pt w ∈ ptsIn X.str (σ.comp e.toRingHom) W := by
    intro W hW
    filter_upwards [hgenev _ ((hpre W _).1 hW)] with w hw
    refine (hpre W _).2 ?_
    rw [← hxpt w hw.1]
    exact hw.2
  have hregev : ∀ {g : X.Fn}, RegAt (under (pt v)) g → ∀ᶠ w in 𝓝 v, RegAt (under (pt w)) g := by
    intro g hg
    obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
    filter_upwards [hXev W (mem_ptsIn.2 hW)] with w hw
    exact regAt_fnOf (mem_ptsIn.1 hw) _ a
  have hmemev : ∀ᶠ w in 𝓝 v, A ∈ Eb.S (under (pt w)) := by
    obtain ⟨U', B', hU', hB', hS⟩ := Eb.loc (under (pt v))
    have hP := (hS _ hU' A).1 hA
    have hU'' : ∀ᶠ w in 𝓝 v, under (pt w) ∈ U' := by
      filter_upwards [hXev U' (mem_ptsIn.2 hU')] with w hw
      exact mem_ptsIn.1 hw
    have h1 : ∀ᶠ w in 𝓝 v, ∀ τ, (∀ i j, RegAt (under (pt w)) ((A * B'⁻¹) τ i j)) ∧
        RegAt (under (pt w)) ((A * B'⁻¹) τ).det⁻¹ :=
      Filter.eventually_all.2 fun τ => (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
        hregev (mem_O_ratOf.1 ((hP τ).1 i j))).and (hregev (mem_O_ratOf.1 (hP τ).2.2.1))
    filter_upwards [hU'', h1] with w hw hw1
    exact (hS _ hw A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 ((hw1 τ).1 i j), (hP τ).2.1, mem_O_ratOf.2 (hw1 τ).2,
      fun i j hi => absurd hi (by simp)⟩
  have hratan : ∀ {g : X.Fn}, RegAt (under (pt v)) g → AnalyticAt ℂ (fun w => ratVal g (pt w)) v := by
    intro g hg
    haveI : IsOpenImmersion j := hoi
    obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
    set g' := (j.appIso W).inv.hom a
    have hvS : v ∈ {b ∈ B₀ | ⊤ ≤ (cxPt T.Z (U.un k (x b))).1 ⁻¹ᵁ (j ''ᵁ W)} := by
      refine ⟨hv₀, ?_⟩
      rw [hxpt v hv₀]
      exact GlobalTheory.LieBase.le_preimage_cxOf e σ hj W (mem_ptsIn.2 hW)
    have han' := GlobalTheory.SCV.analyticAt_of_differentiableOn ((hY (j ''ᵁ W) g').2) (((hY (j ''ᵁ W) g').1).mem_nhds hvS)
    refine han'.congr ?_
    filter_upwards [hXev W (mem_ptsIn.2 hW), hB₀.mem_nhds hv₀] with w hw hwB
    show valAt' _ _ _ = ratVal _ (pt w)
    rw [ratVal_fnOf hw, GlobalTheory.LieBase.ev_eq_valAt'_cxOf e σ hj W a hw, hxpt w hwB]

  obtain ⟨V₀, hV₀, φ, Φ, hzV, hφ, -⟩ := EigSpread.exists_stable_eigFrame E H Dw l Xo c O β T.Z
    ((cxOf e σ hj (pt v)).1 (IsLocalRing.closedPoint ℂ))
  let V : (gen T.Z).affineOpens := ⟨V₀, hV₀⟩
  have hφ' : LogKS.chart V ≫ genStr T.Z = spMap φ := hφ
  have hyV : cxOf e σ hj (pt v) ∈ ptsIn (genStr T.Z) σ V.1 := mem_ptsIn.2 hzV
  obtain ⟨M, hM⟩ := GlobalTheory.T.frame_coordinates_eq_rational_matrix_values_chart E H Dw l Xo c O β T.Z σ F e X j f₀ Eb A₀ hj hoi hT V φ Φ hφ' A
  have hVn : ∀ᶠ w in 𝓝 v, cxOf e σ hj (pt w) ∈ ptsIn (genStr T.Z) σ V.1 := by
    filter_upwards [hgenev _ hyV] with w hw
    rw [← hxpt w hw.1]
    exact hw.2
  obtain ⟨B, hBall, hB, hb₀⟩ := eventually_nhds_iff.1
    ((show ∀ᶠ w in 𝓝 v, w ∈ B₀ from hB₀.mem_nhds hv₀).and (hVn.and hmemev))
  have hsB : ∀ b ∈ B, s b ∈ (U.X k).dom := fun b hb => hsB₀ b (hBall b hb).1
  have hpt : ∀ b (hb : b ∈ B), cxPt T.Z (U.un k ⟨s b, hsB b hb⟩) = cxOf e σ hj (pt b) :=
    fun b hb => hpt₀ b (hBall b hb).1
  obtain ⟨N, hN, hNco⟩ := GlobalTheory.FrameLift.exists_coords (Z := T.Z) hU k hB hb₀ hsB
    (hsd.mono fun b hb => (hBall b hb).1) V Φ (fun b hb => by rw [hpt b hb]; exact (hBall b hb).2.1)
  have key : ∀ b (hb : b ∈ B) (G g : EigFrame T.Z σ ((cxOf e σ hj (pt b)).1 ≫ genι T.Z)),
      (∀ τ i, G.v τ i = (cxFrame T.Z (U.un k ⟨s b, hsB b hb⟩)).v τ i) → FrameAt e f₀ A₀ A (pt b) g →
        ∀ τ, G.co g τ = N b τ * (M τ).map fun r => ratVal r (pt b) := by
    intro b hb G g hG hg τ
    obtain ⟨-, hzV, hzS⟩ := hBall b hb
    have hov : σ = (evHom hzV).comp φ := by
      generalize cxOf e σ hj (pt b) = z at hzV
      exact GlobalTheory.ShFam.EigLoc.spMap_inj (z.2.symm.trans (by
        rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hφ', ← Category.assoc, GlobalTheory.LieMet.spMap_evHom hzV]))
    have hx : (cxOf e σ hj (pt b)).1 ≫ genι T.Z = spMap (evHom hzV) ≫ LogKS.chart V ≫ genι T.Z := by
      rw [← Category.assoc, GlobalTheory.LieMet.spMap_evHom hzV]
    obtain ⟨f, hf⟩ := Φ.exists_isMap (evHom hzV) hov hx
    rw [← hNco b hb _ (hpt b hb) hzV G f hG hf τ, ← (hM _ hzS hzV).2.2 g hg f hf τ, EigFrame.co_mul]
  have hex : ∀ b ∈ B, ∃ g : EigFrame T.Z σ ((cxOf e σ hj (pt b)).1 ≫ genι T.Z),
      FrameAt e f₀ A₀ A (pt b) g := fun b hb => (hM _ (hBall b hb).2.2 (hBall b hb).2.1).2.1
  refine ⟨fun b τ => N b τ * (M τ).map fun r => ratVal r (pt b), fun τ a a' => ?_, fun τ => ?_, ?_⟩
  · simp only [Matrix.mul_apply, Matrix.map_apply]
    exact Finset.analyticAt_fun_sum _ fun i _ =>
      (GlobalTheory.SCV.analyticAt_of_differentiableOn (hN τ a i) (hB.mem_nhds hb₀)).mul
        (hratan ((hM (pt v) hA hyV).1 τ i a'))
  · obtain ⟨g, hg⟩ := hex _ hb₀
    obtain ⟨G, hG, -⟩ := GlobalTheory.FrameLift.exists_transport (hpt _ hb₀) (cxFrame T.Z _)
    show IsUnit (N v τ * (M τ).map fun r => ratVal r (pt v)).det
    rw [← key _ hb₀ G g hG hg τ]
    exact G.isUnit_det_co g τ
  · filter_upwards [hB.mem_nhds hb₀] with b hb
    intro hsb g hg Me τ
    obtain ⟨G, hG, hGm⟩ := GlobalTheory.FrameLift.exists_transport (hpt b hb) (cxFrame T.Z _)
    rw [← key b hb G g hG hg τ, ← hGm Me τ]
    exact Me.change _ G g τ

end
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_frameChange_along_analyticLift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (X : Var F) (j : X.X ⟶ gen T.Z) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), ∀ s : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ (Dw.p + Dw.q), AnalyticAt ℂ s v → (∀ᶠ w in nhds v, ∃ hs : s w ∈ (U.X k).dom, flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) (s w)) = GlobalTheory.UnifDens.flatL h w) → ∃ K : ReciprocityTheory.L2DbarEstimates.V X.dim → Mat Dw.mult ℂ, (∀ τ a b, AnalyticAt ℂ (fun w => K w τ a b) v) ∧ (∀ τ, IsUnit (K v τ).det) ∧ ∀ᶠ w in nhds v, ∀ (hs : s w ∈ (U.X k).dom) (g : EigFrame T.Z σ ((cxOf e σ hj (ψ (GlobalTheory.UnifDens.flatL h w))).1 ≫ genι T.Z)), FrameAt e f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h w)) g → ∀ (M : EigMet T.Z σ) (τ : E →+* ℂ), M.gram (cxOf e σ hj (ψ (GlobalTheory.UnifDens.flatL h w))) g τ = (K w τ)ᴴ * M.gram (cxPt T.Z (U.un k ⟨s w, hs⟩)) (cxFrame T.Z (U.un k ⟨s w, hs⟩)) τ * K w τ := by
  atlas_forward_decl GlobalTheory.UnifFrameChange.exists_holomorphic_frame_change
end

section
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix

namespace GlobalTheory.HodgeUnifFrame

theorem transpose_hermitian_gram_submatrix_bijection {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (e : n → m)
    (he : Function.Bijective e) (K G : Matrix m m ℂ) (W P : Matrix n n ℂ) (c : ℂ)
    (hG : G.submatrix e e = c • (Wᴴ * P * W)) :
    ((Kᴴ * G * K)ᵀ).submatrix e e = c • ((W * K.submatrix e e)ᵀ * Pᵀ * ((W * K.submatrix e e)ᵀ)ᴴ) := by
  have h1 : (Kᴴ * G * K).submatrix e e = (K.submatrix e e)ᴴ * G.submatrix e e * K.submatrix e e := by
    rw [Matrix.submatrix_mul _ _ _ e _ he, Matrix.submatrix_mul _ _ _ e _ he, Matrix.conjTranspose_submatrix]
  have h2 : ((Kᴴ * G * K)ᵀ).submatrix e e = ((Kᴴ * G * K).submatrix e e)ᵀ := by ext; rfl
  rw [h2, h1, hG]
  have h3 : ((W * K.submatrix e e)ᵀ)ᴴ = ((W * K.submatrix e e)ᴴ)ᵀ := by ext; rfl
  rw [h3]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

theorem lieGram_unif_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), ∀ (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U), ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), ∀ τ : GlobalTheory.AllWt.Psi H, ∃ c : ℝ, 0 < c ∧ ∃ g : ReciprocityTheory.L2DbarEstimates.V X.dim → Matrix (Fin Dw.p) (Fin Dw.p) ℂ, (∀ i j, AnalyticAt ℂ (fun w => g w i j) v) ∧ IsUnit (g v).det ∧ ∀ᶠ w in nhds v, (lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h w)) τ.1).submatrix (Fin.cast (GlobalTheory.HodgeGenUnf.mult_psi τ).symm) (Fin.cast (GlobalTheory.HodgeGenUnf.mult_psi τ).symm) = (c : ℂ) • (g w * ((hP (unflat (GlobalTheory.UnifDens.flatL h w) (GlobalTheory.HodgeGenUnf.letter hσ hU k τ)))⁻¹)ᵀ * (g w)ᴴ) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ h v hv A hA τ
  obtain ⟨hoi, -, hT⟩ := hL
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by rw [(hU.2.1 k).1]; omega
  obtain ⟨s, hsa, hWa, hsev⟩ := GlobalTheory.T.exists_analytic_flagDomain_section_flatCoordinates E Dw.p Dw.q X.dim (U.X k) hp h v hv
  obtain ⟨K, hKa, hKu, hKev⟩ := GlobalTheory.T.exists_holomorphic_frameChange_along_analyticLift E H Dw l Xo c O β Y T F e σ U hσ hU k X j f₀ Eb A₀ hj hoi hT ψ hψ h v hv A hA s hsa hsev
  have hex := GlobalTheory.T.eventually_lieEigenspaceFrameAt_uniformisation E H Dw l Xo c O β Y T F e σ U hσ hU k X j f₀ Eb A₀ hj hoi hT ψ hψ h v hv A hA
  set τ' := GlobalTheory.HodgeGenUnf.letter hσ hU k τ with hτ'
  set ec : Fin Dw.p → Fin (Dw.mult τ.1) := Fin.cast (GlobalTheory.HodgeGenUnf.mult_psi τ).symm with hec
  have he : Function.Bijective ec := (finCongr (GlobalTheory.HodgeGenUnf.mult_psi τ).symm).bijective
  refine ⟨2 * Real.pi, Real.two_pi_pos,
    fun w => (coW (U.X k) (Nat.le_add_right Dw.p Dw.q) (s w) τ' * (K w τ.1).submatrix ec ec)ᵀ, ?_, ?_, ?_⟩
  · intro a b
    simp only [Matrix.transpose_apply, Matrix.mul_apply, Matrix.submatrix_apply]
    exact Finset.analyticAt_fun_sum _ fun i _ => (hWa τ' b i).mul (hKa τ.1 (ec i) (ec a))
  · obtain ⟨hs0, -⟩ := hsev.self_of_nhds
    rw [Matrix.det_transpose, Matrix.det_mul]
    refine (isUnit_coW (U.X k) _ hp hs0 τ').mul ?_
    have : (K v τ.1).submatrix ec ec = (K v τ.1).submatrix (finCongr (GlobalTheory.HodgeGenUnf.mult_psi τ).symm)
      (finCongr (GlobalTheory.HodgeGenUnf.mult_psi τ).symm) := rfl
    rw [this, Matrix.det_submatrix_equiv_self]
    exact hKu τ.1
  · filter_upwards [hsev, hKev, hex] with w ⟨hs, hflat⟩ hKw ⟨g0, hg0⟩
    have hexw : ∃ g, FrameAt e f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h w)) g := ⟨g0, hg0⟩
    rw [lieGram, dif_pos hexw]
    show (((hodgeMet T.Z U).gram _ hexw.choose τ.1)ᵀ).submatrix ec ec = _
    rw [hKw hs _ hexw.choose_spec (hodgeMet T.Z U) τ.1]
    have hG := GlobalTheory.HodgeGenUnf.hodgeMet_gram_frame T.Z hσ hU k ⟨s w, hs⟩ τ τ' rfl (Nat.le_add_right Dw.p Dw.q)
    have hz : domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) (s w) τ' = unflat (GlobalTheory.UnifDens.flatL h w) τ' := by
      rw [← hflat]; rfl
    have hG' : ((hodgeMet T.Z U).gram (cxPt T.Z (U.un k ⟨s w, hs⟩)) (cxFrame T.Z (U.un k ⟨s w, hs⟩)) τ.1).submatrix ec ec =
        ((2 * Real.pi : ℝ) : ℂ) • ((coW (U.X k) (Nat.le_add_right Dw.p Dw.q) (s w) τ')ᴴ *
          (hP (unflat (GlobalTheory.UnifDens.flatL h w) τ'))⁻¹ * coW (U.X k) (Nat.le_add_right Dw.p Dw.q) (s w) τ') := by
      rw [← hz]; exact hG
    rw [transpose_hermitian_gram_submatrix_bijection ec he _ _ _ _ _ hG']

end GlobalTheory.HodgeUnifFrame
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_metric_uniformisation_gram_local_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), ∀ (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U), ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), ∀ τ : GlobalTheory.AllWt.Psi H, ∃ c : ℝ, 0 < c ∧ ∃ g : ReciprocityTheory.L2DbarEstimates.V X.dim → Matrix (Fin Dw.p) (Fin Dw.p) ℂ, (∀ i j, AnalyticAt ℂ (fun w => g w i j) v) ∧ IsUnit (g v).det ∧ ∀ᶠ w in nhds v, (lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h w)) τ.1).submatrix (Fin.cast (GlobalTheory.HodgeGenUnf.mult_psi τ).symm) (Fin.cast (GlobalTheory.HodgeGenUnf.mult_psi τ).symm) = (c : ℂ) • (g w * ((hP (unflat (GlobalTheory.UnifDens.flatL h w) (GlobalTheory.HodgeGenUnf.letter hσ hU k τ)))⁻¹)ᵀ * (g w)ᴴ) := by
  atlas_forward_decl GlobalTheory.HodgeUnifFrame.lieGram_unif_local
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix

namespace GlobalTheory.ModelMetricReg

open scoped ComplexOrder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiff_det {m : Type*} [Fintype m] [DecidableEq m] {k : WithTop ℕ∞}
    {F : E → Matrix m m ℂ} (hF : ∀ a b, ContDiff ℝ k (fun x => F x a b)) :
    ContDiff ℝ k (fun x => (F x).det) := by
  simp only [Matrix.det_apply']
  refine ContDiff.sum (fun σ _ => ?_)
  exact contDiff_const.mul (contDiff_prod (fun i _ => hF _ _))

theorem contDiff_adjugate_apply {m : Type*} [Fintype m] [DecidableEq m] {k : WithTop ℕ∞}
    {F : E → Matrix m m ℂ} (hF : ∀ a b, ContDiff ℝ k (fun x => F x a b)) (i j : m) :
    ContDiff ℝ k (fun x => (F x).adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  refine contDiff_det (fun a b => ?_)
  by_cases hab : a = j
  · subst hab; simp only [Matrix.updateRow_self]; exact contDiff_const
  · simp only [Matrix.updateRow_ne hab]; exact hF a b

theorem det_one_sub_mul_conjTranspose_ne_zero {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ)
    (hz : (1 - zᴴ * z).PosDef) : (1 - z * zᴴ).det ≠ 0 := by
  rw [Matrix.det_one_sub_mul_comm]
  exact hz.det_pos.ne'

end GlobalTheory.ModelMetricReg

namespace GlobalTheory.ModelMetricReg

open scoped ComplexOrder

theorem contDiff_hP_entry (ι : Type) [Fintype ι] (p q n : ℕ)
    (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι) (a b : Fin p) :
    ContDiff ℝ 2 (fun w : ReciprocityTheory.L2DbarEstimates.V n => hP (unflat (GlobalTheory.UnifDens.flatL h w) τ) a b) := by
  have hz : ∀ c : ι × Fin p × Fin q,
      ContDiff ℝ 2 (fun w : ReciprocityTheory.L2DbarEstimates.V n => GlobalTheory.UnifDens.flatL h w c) := by
    intro c
    have hL : ContDiff ℝ 2 (fun w : ReciprocityTheory.L2DbarEstimates.V n => GlobalTheory.UnifDens.flatL h w) :=
      ((GlobalTheory.UnifDens.flatL h).contDiff).restrict_scalars ℝ
    exact (contDiff_apply ℝ ℂ c).comp hL
  simp only [hP, Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, unflat,
    Matrix.of_apply]
  refine contDiff_const.sub (ContDiff.sum (fun k _ => ?_))
  have hs : ContDiff ℝ 2 (fun w : ReciprocityTheory.L2DbarEstimates.V n => star (GlobalTheory.UnifDens.flatL h w (τ, b, k))) := by
    have := (Complex.conjCLE.contDiff (n := 2)).comp (hz (τ, b, k))
    convert this using 2
    simp [Function.comp, Complex.conjCLE_apply, Complex.star_def]
  exact (hz (τ, a, k)).mul hs

theorem invT_contDiffAt_and_isUnit : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n) (v : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.UnifDens.flatL h v ∈ DomFlat ι p q → ∀ τ : ι, MContDiffAt 2 (fun w => ((hP (unflat (GlobalTheory.UnifDens.flatL h w) τ))⁻¹)ᵀ) v ∧ IsUnit (((hP (unflat (GlobalTheory.UnifDens.flatL h v) τ))⁻¹)ᵀ).det := by
  intro ι _ p q n h v hv τ
  have hpos : (1 - (unflat (GlobalTheory.UnifDens.flatL h v) τ)ᴴ * unflat (GlobalTheory.UnifDens.flatL h v) τ).PosDef :=
    hv τ
  have hne : (hP (unflat (GlobalTheory.UnifDens.flatL h v) τ)).det ≠ 0 :=
    det_one_sub_mul_conjTranspose_ne_zero _ hpos
  refine ⟨fun a b => ?_, ?_⟩
  · have hE := contDiff_hP_entry ι p q n h τ
    have hdet := contDiff_det (F := fun w : ReciprocityTheory.L2DbarEstimates.V n => hP (unflat (GlobalTheory.UnifDens.flatL h w) τ)) hE
    have hadj := contDiff_adjugate_apply (F := fun w : ReciprocityTheory.L2DbarEstimates.V n => hP (unflat (GlobalTheory.UnifDens.flatL h w) τ)) hE b a
    simp only [Matrix.transpose_apply, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul,
      Ring.inverse_eq_inv']
    exact (hdet.contDiffAt.inv hne).mul hadj.contDiffAt
  · rw [Matrix.det_transpose, Matrix.det_nonsing_inv]
    rw [Ring.inverse_eq_inv']
    exact (inv_ne_zero hne).isUnit

end GlobalTheory.ModelMetricReg
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundedDomainModelMetric_contDiffAt_and_isUnit : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n) (v : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.UnifDens.flatL h v ∈ DomFlat ι p q → ∀ τ : ι, MContDiffAt 2 (fun w => ((hP (unflat (GlobalTheory.UnifDens.flatL h w) τ))⁻¹)ᵀ) v ∧ IsUnit (((hP (unflat (GlobalTheory.UnifDens.flatL h v) τ))⁻¹)ᵀ).det := by
  atlas_forward_decl GlobalTheory.ModelMetricReg.invT_contDiffAt_and_isUnit
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase

open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

open scoped Matrix

namespace GlobalTheory.UnifDensTransport

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem aeval_term {κ S : Type} [CommRing S] [Algebra ℝ S] (φ : κ → S) (x : κ) (a s : ℕ) :
    aeval φ ((C ((-1 : ℝ) ^ a) * X x) ^ s) = (algebraMap ℝ S ((-1 : ℝ) ^ a) * φ x) ^ s := by
  rw [map_pow (aeval φ), map_mul (aeval φ), aeval_C, aeval_X]

theorem chernPoly_cast {n a b : ℕ} (hab : a = b) (G : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ) :
    chernPoly (fun u => (G u).submatrix (Fin.cast hab.symm) (Fin.cast hab.symm)) v k = chernPoly G v k := by
  subst hab; rfl

theorem chernTop_pointPoly_eq (H : Host E) (Dw : Datum H) {n : ℕ} (G : ReciprocityTheory.L2DbarEstimates.V n → Mat Dw.mult ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) :
    chernTop (pointPoly H Dw) G v =
      GlobalTheory.GoodMetric.chernTop (m := fun _ : GlobalTheory.AllWt.Psi H => Dw.p)
        (∏ τ : GlobalTheory.AllWt.Psi H, (MvPolynomial.C ((-1 : ℝ) ^ Dw.p) * MvPolynomial.X (τ, Dw.p)) ^ (Dw.p + Dw.q - Dw.p))
        (fun u τ => (G u τ.1).submatrix (Fin.cast (GlobalTheory.HodgeGenUnf.mult_psi τ).symm)
          (Fin.cast (GlobalTheory.HodgeGenUnf.mult_psi τ).symm)) v := by
  unfold chernTop
  congr 3
  rw [pointPoly, map_prod, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [aeval_term, aeval_term]
  erw [chernPoly_cast (GlobalTheory.HodgeGenUnf.mult_psi τ) (fun u => G u τ.1) v Dw.p]
  exact congrArg (fun m => (algebraMap ℝ (MvPolynomial (Fin n × Fin n) ℂ) ((-1 : ℝ) ^ m) *
    chernPoly (fun u => G u τ.1) v m) ^ (Dw.p + Dw.q - m)) (GlobalTheory.HodgeGenUnf.mult_psi τ)

theorem chernTop_reindex {ι ι' : Type} [Fintype ι] [Fintype ι'] (a : ι → ι') (ha : Function.Bijective a)
    (p s : ℕ) {n : ℕ} (K : ReciprocityTheory.L2DbarEstimates.V n → Mat (fun _ : ι' => p) ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) :
    GlobalTheory.GoodMetric.chernTop (m := fun _ : ι => p)
                 (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ s) (fun u τ => K u (a τ)) v =
      GlobalTheory.GoodMetric.chernTop (m := fun _ : ι' => p)
        (∏ τ : ι', (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ s) K v := by
  unfold chernTop
  congr 3
  rw [map_prod, map_prod]
  simp only [aeval_term]
  exact Fintype.prod_bijective _ ha _ _ fun τ => rfl

end GlobalTheory.UnifDensTransport

namespace GlobalTheory.UnifDensTransport

theorem letter_bijective {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)}
    (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) :
    Function.Bijective (GlobalTheory.HodgeGenUnf.letter hσ hU k) := by
  obtain ⟨hb, hg, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  refine ⟨fun a b hab => Subtype.ext (hb.1 (congrArg Subtype.val hab)), fun τ' => ?_⟩
  obtain ⟨τ, hτ⟩ := hb.2 τ'.1
  have hm : τ H.rt = H.rt0 := (hg τ).1 (by rw [hτ]; exact ((hU.2.1 k).2 τ'.1).1 τ'.2)
  exact ⟨⟨τ, hm⟩, Subtype.ext hτ⟩

theorem chernTop_pointPoly_transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), chernTop (pointPoly H Dw) (fun u => lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h u))) v = GlobalTheory.GoodMetric.chernTop (m := fun _ : (U.X k).Ψ => Dw.p) (∏ τ : (U.X k).Ψ, (MvPolynomial.C ((-1 : ℝ) ^ Dw.p) * MvPolynomial.X (τ, Dw.p)) ^ (Dw.p + Dw.q - Dw.p)) (fun u τ => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) v := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ h v hv A hA
  rw [chernTop_pointPoly_eq, ← chernTop_reindex _ (letter_bijective hσ hU k)]
  choose cc hcc g hg hgu hG using GlobalTheory.T.hodge_metric_uniformisation_gram_local_holomorphic E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ h v hv A hA
  exact GlobalTheory.PointChern.chernTop_changeFrame _ _ _ (fun w τ => g τ w) cc v hcc hg hgu
    (fun τ => (GlobalTheory.T.boundedDomainModelMetric_contDiffAt_and_isUnit _ _ _ _ h v hv _).1) (fun τ => (GlobalTheory.T.boundedDomainModelMetric_contDiffAt_and_isUnit _ _ _ _ h v hv _).2) (Filter.eventually_all.2 hG)

end GlobalTheory.UnifDensTransport
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointClass_density_hodge_uniformisation_eq_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), chernTop (pointPoly H Dw) (fun u => lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h u))) v = GlobalTheory.GoodMetric.chernTop (m := fun _ : (U.X k).Ψ => Dw.p) (∏ τ : (U.X k).Ψ, (MvPolynomial.C ((-1 : ℝ) ^ Dw.p) * MvPolynomial.X (τ, Dw.p)) ^ (Dw.p + Dw.q - Dw.p)) (fun u τ => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) v := by
  atlas_forward_decl GlobalTheory.UnifDensTransport.chernTop_pointPoly_transport
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

namespace GlobalTheory.UnifDens

theorem chernTop_domain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), chernTop (pointPoly H Dw) (fun u => lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h u))) v = grassConst Dw.p (Dw.p + Dw.q - Dw.p) ^ Fintype.card (U.X k).Ψ * ∏ i, ((hQ (unflat (GlobalTheory.UnifDens.flatL h v) i)).det.re) ^ (-((Dw.p + (Dw.p + Dw.q - Dw.p) : ℕ) : ℤ)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ h v hv A hA
  rw [GlobalTheory.T.pointClass_density_hodge_uniformisation_eq_model E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ h v hv A hA,
    GlobalTheory.T.chernPolyTopDensity_bounded_domain_invariant _ _ _ _ h v hv, GlobalTheory.T.chernTop_density_model_metric_origin]

end GlobalTheory.UnifDens
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointClassDensity_hodgeMetric_boundedDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), chernTop (pointPoly H Dw) (fun u => lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h u))) v = grassConst Dw.p (Dw.p + Dw.q - Dw.p) ^ Fintype.card (U.X k).Ψ * ∏ i, ((hQ (unflat (GlobalTheory.UnifDens.flatL h v) i)).det.re) ^ (-((Dw.p + (Dw.p + Dw.q - Dw.p) : ℕ) : ℤ)) := by
  atlas_forward_decl GlobalTheory.UnifDens.chernTop_domain
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifDens

open Filter Topology GlobalTheory.UnifDens in

theorem chernTopPart_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ A ⊆ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), MeasurableSet A → Set.InjOn ψ A → chernTopPart Eb (lieGram e U hj f₀ A₀) (pointPoly H Dw) 1 (ψ '' A) = ENNReal.ofReal (grassConst Dw.p (Dw.p + Dw.q - Dw.p) ^ Fintype.card (U.X k).Ψ) * muD (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) A := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ A hAD hAm hinj
  have hdim := GlobalTheory.T.flagSpaceComponent_base_dim_eq_cmType_card_mul_pq E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL
  obtain ⟨hcont, hana⟩ := GlobalTheory.T.componentUniformisation_continuousOn_analyticAt_charts E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have h3a := GlobalTheory.T.point_class_density_uniformisation_chart_change E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ hdim
  have h3b := GlobalTheory.T.pointClassDensity_hodgeMetric_boundedDomain E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ hdim
  set D := DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) with hDdef
  have hDo : IsOpen D := GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat
  set L := flatL hdim with hLdef
  set C : ℝ := grassConst Dw.p (Dw.p + Dw.q - Dw.p) ^ Fintype.card (U.X k).Ψ with hCdef
  have hC : 0 ≤ C := by
    rw [hCdef, grassConst]
    refine pow_nonneg (div_nonneg (Finset.prod_nonneg fun i _ => by positivity) (by positivity)) _
  set dens : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → ℝ := fun w =>
    ∏ i, ((hQ (unflat w i)).det.re) ^ (-((Dw.p + (Dw.p + Dw.q - Dw.p) : ℕ) : ℤ)) with hdens
  set μD := muD (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) with hμD
  set ρ : AlgChart X.str (σ.comp e.toRingHom) X.dim → CxPts X.str (σ.comp e.toRingHom) → ENNReal := fun ch y =>
    ENNReal.ofReal ((((1 : ℤˣ) : ℤ) : ℝ) * chernTop (pointPoly H Dw)
      (fun v => lieGram e U hj f₀ A₀ (Eb.nonempty (under y)).choose (ch.e.symm v)) (ch.e y)) with hρ
  have hμ : chernTopPart Eb (lieGram e U hj f₀ A₀) (pointPoly H Dw) 1 =
      glueMeas (fun ch : AlgChart X.str (σ.comp e.toRingHom) X.dim => ch.e) ρ := rfl
  have hpre : ∀ S : Set (CxPts X.str (σ.comp e.toRingHom)), MeasurableSet S → MeasurableSet (D ∩ ψ ⁻¹' S) := by
    intro S hS
    have hm : Measurable (D.restrict ψ) := (continuousOn_iff_continuous_restrict.1 hcont).measurable
    have := hDo.measurableSet.subtype_image (hm hS)
    convert this using 1
    ext w
    constructor
    · rintro ⟨hw, hwS⟩
      exact ⟨⟨w, hw⟩, hwS, rfl⟩
    · rintro ⟨⟨w, hw⟩, hwS, rfl⟩
      exact ⟨hw, hwS⟩
  have key : ∀ (ch : AlgChart X.str (σ.comp e.toRingHom) X.dim)
      (B : Set ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ)), MeasurableSet B → B ⊆ D → Set.InjOn ψ B →
      chartMeas ch.e (ρ ch) (ψ '' B) = ENNReal.ofReal C * μD (B ∩ ψ ⁻¹' ch.e.source) := by
    intro ch B hB hBD hBi
    set B' := B ∩ ψ ⁻¹' ch.e.source with hB'
    have hB'm : MeasurableSet B' := by
      have e0 : B' = B ∩ (D ∩ ψ ⁻¹' ch.e.source) := by
        ext w
        simp only [hB', Set.mem_inter_iff, Set.mem_preimage]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, hBD h1, h2⟩
        · rintro ⟨h1, -, h2⟩
          exact ⟨h1, h2⟩
      rw [e0]
      exact hB.inter (hcont.isOpen_inter_preimage hDo ch.e.open_source).measurableSet
    have hψB : MeasurableSet (ψ '' B) := hB.image_of_continuousOn_injOn (hcont.mono hBD) hBi
    rw [chartMeas_apply ch.e (ρ ch) hψB]
    have e1 : ch.e.source ∩ ψ '' B = ψ '' B' := by
      rw [hB', Set.image_inter_preimage, Set.inter_comm]
    set φ : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.L2DbarEstimates.V X.dim := fun u => ch.e (ψ (L u)) with hφ
    set S := L ⁻¹' B' with hS
    have e2 : ch.e '' (ψ '' B') = φ '' S := by
      rw [hS, hφ, ← Set.image_image (fun w => ch.e (ψ w)) L, Set.image_preimage_eq _ L.surjective,
        Set.image_image]
    have hSm : MeasurableSet S := L.continuous.measurable hB'm
    have hdiff : ∀ u ∈ S, DifferentiableAt ℂ φ u := by
      intro u hu
      have hu' : L u ∈ B' := hu
      exact (hana (L u) (hBD hu'.1) ch hu'.2).differentiableAt.comp u L.differentiableAt
    have hder : ∀ u ∈ S, HasFDerivWithinAt φ ((fderiv ℂ φ u).restrictScalars ℝ) S u :=
      fun u hu => ((hdiff u hu).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    have hinjφ : Set.InjOn φ S := by
      intro u1 h1 u2 h2 h12
      have h1' : L u1 ∈ B' := h1
      have h2' : L u2 ∈ B' := h2
      have h3 : ψ (L u1) = ψ (L u2) := ch.e.injOn h1'.2 h2'.2 h12
      exact L.injective (hBi h1'.1 h2'.1 h3)
    rw [e1, e2, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSm hder hinjφ]
    have hint : ∀ u ∈ S, ENNReal.ofReal |((fderiv ℂ φ u).restrictScalars ℝ).det| * ρ ch (ch.e.symm (φ u)) =
        ENNReal.ofReal (C * dens (L u)) := by
      intro u hu
      have hu' : L u ∈ B' := hu
      have hsym : ch.e.symm (φ u) = ψ (L u) := ch.e.left_inv hu'.2
      rw [hsym]
      have hdet : ((fderiv ℂ φ u).restrictScalars ℝ).det =
          Complex.normSq (LinearMap.det (fderiv ℂ φ u : ReciprocityTheory.L2DbarEstimates.V X.dim →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V X.dim)) := by
        have := LinearMap.det_restrictScalars (R := ℝ)
          (f := (fderiv ℂ φ u : ReciprocityTheory.L2DbarEstimates.V X.dim →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V X.dim))
        rw [Algebra.norm_complex_apply] at this
        exact this
      have hA := (Eb.nonempty (under (ψ (L u)))).choose_spec
      have ha := h3a u (hBD hu'.1) ch hu'.2 _ hA
      have hb := h3b u (hBD hu'.1) _ hA
      rw [hdet, abs_of_nonneg (Complex.normSq_nonneg _), hρ, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _)]
      congr 1
      simp only [Units.val_one, Int.cast_one, one_mul]
      rw [← ha, hb]
    rw [setLIntegral_congr_fun hSm hint]
    have hmp := (flatL_mp hdim).setLIntegral_comp_preimage_emb L.toHomeomorph.measurableEmbedding
      (fun w => ENNReal.ofReal (C * dens w)) B'
    rw [hS]
    refine hmp.trans ?_
    simp_rw [ENNReal.ofReal_mul hC]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hμD, muD, withDensity_apply _ hB'm,
      Measure.restrict_restrict hB'm, Set.inter_eq_left.2 (Set.inter_subset_left.trans hBD)]

  set ν : Measure (CxPts X.str (σ.comp e.toRingHom)) := ENNReal.ofReal C • Measure.map ψ (μD.restrict A) with hν
  have hae : AEMeasurable ψ (μD.restrict A) := (hcont.mono hAD).aemeasurable hAm
  have hνT : ∀ S, MeasurableSet S → ν S = ENNReal.ofReal C * μD (A ∩ ψ ⁻¹' S) := by
    intro S hS
    rw [hν, Measure.smul_apply, Measure.map_apply_of_aemeasurable hae hS, Measure.restrict_apply' hAm,
      Set.inter_comm, smul_eq_mul]
  have hAS : ∀ S : Set (CxPts X.str (σ.comp e.toRingHom)), MeasurableSet S → MeasurableSet (A ∩ ψ ⁻¹' S) := by
    intro S hS
    have e0 : A ∩ ψ ⁻¹' S = A ∩ (D ∩ ψ ⁻¹' S) := by
      ext w
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      exact ⟨fun h => ⟨h.1, hAD h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [e0]
    exact hAm.inter (hpre S hS)
  have hψA : MeasurableSet (ψ '' A) := hAm.image_of_continuousOn_injOn (hcont.mono hAD) hinj
  have hle : (glueMeas (fun ch : AlgChart X.str (σ.comp e.toRingHom) X.dim => ch.e) ρ).restrict (ψ '' A) ≤ ν := by
    rw [glueMeas, GlobalTheory.ChernScale.restrict_iSup_eq _ hψA]
    refine iSup_le fun ch => Measure.le_iff.2 fun S hS => ?_
    rw [Measure.restrict_apply hS, hνT S hS, Set.inter_comm, ← Set.image_inter_preimage,
      key ch _ (hAS S hS) (Set.inter_subset_left.trans hAD) (hinj.mono Set.inter_subset_left)]
    exact mul_le_mul' le_rfl (measure_mono Set.inter_subset_left)
  have heq : (glueMeas (fun ch : AlgChart X.str (σ.comp e.toRingHom) X.dim => ch.e) ρ).restrict (ψ '' A) = ν := by
    refine ext_of_cover (fun ch : AlgChart X.str (σ.comp e.toRingHom) X.dim => ch.e.source)
      (fun ch => ch.e.open_source) (fun y => AlgChart.exists_mem_source y) fun ch S hS hSc =>
        le_antisymm (Measure.le_iff'.1 hle S) ?_
    rw [Measure.restrict_apply hS, hνT S hS]
    have e3 : A ∩ ψ ⁻¹' S = (A ∩ ψ ⁻¹' S) ∩ ψ ⁻¹' ch.e.source :=
      (Set.inter_eq_left.2 fun w (hw : w ∈ A ∩ ψ ⁻¹' S) => hSc hw.2).symm
    calc ENNReal.ofReal C * μD (A ∩ ψ ⁻¹' S)
        = chartMeas ch.e (ρ ch) (ψ '' (A ∩ ψ ⁻¹' S)) := by
          rw [key ch _ (hAS S hS) (Set.inter_subset_left.trans hAD) (hinj.mono Set.inter_subset_left), ← e3]
      _ = chartMeas ch.e (ρ ch) (S ∩ ψ '' A) := by rw [Set.image_inter_preimage, Set.inter_comm]
      _ ≤ glueMeas (fun ch : AlgChart X.str (σ.comp e.toRingHom) X.dim => ch.e) ρ (S ∩ ψ '' A) :=
          Measure.le_iff'.1 (le_iSup (fun ch : AlgChart X.str (σ.comp e.toRingHom) X.dim => chartMeas ch.e (ρ ch)) ch) _
  rw [hμ, ← Measure.restrict_apply_self, heq, hνT _ hψA, Set.inter_eq_left.2 (Set.subset_preimage_image ψ A)]

end GlobalTheory.UnifDens
end
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernTopPart_hodgeMetric_uniformisation_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ A ⊆ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), MeasurableSet A → Set.InjOn ψ A → chernTopPart Eb (lieGram e U hj f₀ A₀) (pointPoly H Dw) 1 (ψ '' A) = ENNReal.ofReal (grassConst Dw.p (Dw.p + Dw.q - Dw.p) ^ Fintype.card (U.X k).Ψ) * muD (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) A := by
  atlas_forward_decl GlobalTheory.UnifDens.chernTopPart_image
end
