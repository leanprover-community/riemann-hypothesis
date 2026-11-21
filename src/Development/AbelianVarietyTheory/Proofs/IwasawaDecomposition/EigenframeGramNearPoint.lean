import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFamilyChartDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedComplexPointOfEigenFrameOffBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFamilyChartHolomorphic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformizedFamilyChartIndex

section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_family_chart_domain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n) (d : ℕ) (B : Set (ReciprocityTheory.L2DbarEstimates.V d)) (P : ReciprocityTheory.L2DbarEstimates.V d → ((Fu.Di i).La →+ (Fin g → ℂ))), IsOpen B → (∀ b ∈ B, IsPeriod (Fu.Di i) ty (P b)) → (∀ v, DifferentiableOn ℂ (fun b => P b v) B) → ∃ Hm : ReciprocityTheory.L2DbarEstimates.V d → Matrix (Fin g) (Fin g) ℂ, (∀ b ∈ B, IsRiem Fu i (P b) (Hm b)) ∧ ∀ p q, ContDiffOn ℝ ∞ (fun b => Hm b p q) B := by
  first | exact @GlobalTheory.RiemSmooth.exists_riem_contDiffOn | exact GlobalTheory.RiemSmooth.exists_riem_contDiffOn | (intros; apply GlobalTheory.RiemSmooth.exists_riem_contDiffOn <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_family_chart_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (d g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (ch : AlgChart (genStr Z) σ d) (i : Fin Fu.n) (B : Set (ReciprocityTheory.L2DbarEstimates.V d)) (P : ReciprocityTheory.L2DbarEstimates.V d → ((Fu.Di i).La →+ (Fin g → ℂ))), IsOpen B → B ⊆ ch.e.target → (∀ b ∈ B, IsPeriod (Fu.Di i) ty (P b)) → (∀ v, DifferentiableOn ℂ (fun b => P b v) B) → (∀ b ∈ B, ∀ y : FrPt Xo c (CAt σ), ch.e.symm b = cxPt Z y → Fu.u i (P b) = y.x) → Mono (genι Z) → ∀ (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (F : EigFrame Z φ (LogKS.chart V ≫ genι Z)), LogKS.chart V ≫ genStr Z = spMap φ → ∃ z : ReciprocityTheory.L2DbarEstimates.V d → ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ), (∀ τ k, DifferentiableOn ℂ (fun b => z b τ k) {b ∈ B | ch.e.symm b ∈ ptsIn (genStr Z) σ V.1 ∧ ¬ LiesIn (ch.e.symm b) (genBd Z)}) ∧ ∀ b ∈ B, ∀ (hy : ch.e.symm b ∈ ptsIn (genStr Z) σ V.1) (f : EigFrame Z σ ((ch.e.symm b).1 ≫ genι Z)), F.IsMap (evHom hy) f → ∀ q : FrPt Xo c (CAt σ), cxPt Z q = ch.e.symm b → (∀ τ k, ∃ w : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left, w ≫ Z.m0.toSABMap.φ = q.u τ k ∧ w ≫ Z.m.φ = f.v τ k) → ∀ τ k, IsDerivAt0 (fun w => (Fu.ex i (P b) w).left) (z b τ k) (q.u τ k) := by
  first | exact @GlobalTheory.ShFam.ExpCoord.exists_expCoord | exact GlobalTheory.ShFam.ExpCoord.exists_expCoord | (intros; apply GlobalTheory.ShFam.ExpCoord.exists_expCoord <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff

set_option autoImplicit false

namespace GlobalTheory.ShFam

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem oF_pt_ext {Z : Model Xo c (algebraMap (𝓞 c.F) c.F)} {R : Type} [CommRing R] {w w' : Sp R ⟶ Z.oF.t.G.left}
    (h0 : w ≫ Z.m0.toSABMap.φ = w' ≫ Z.m0.toSABMap.φ) (h : w ≫ Z.m.φ ≫ Z.t.G.hom = w' ≫ Z.m.φ ≫ Z.t.G.hom) : w = w' := by
  refine Z.m0.toSABMap.cart.1.hom_ext h0 ?_
  apply pullback.hom_ext
  · simp only [Category.assoc, ← Z.m0.toSABMap.cart.1.w]
    rw [reassoc_of% h0]
  · rw [← Z.jQ_over]
    obtain ⟨g, hg⟩ := Spec.map_surjective (w ≫ Z.oF.t.G.hom ≫ Z.jQ ≫ pullback.snd Z.s (spMap (algebraMap (𝓞 c.F) c.F)))
    obtain ⟨g', hg'⟩ := Spec.map_surjective (w' ≫ Z.oF.t.G.hom ≫ Z.jQ ≫ pullback.snd Z.s (spMap (algebraMap (𝓞 c.F) c.F)))
    have e1 : ∀ v : Sp R ⟶ Z.oF.t.G.left, (v ≫ Z.oF.t.G.hom ≫ Z.jQ ≫ pullback.snd _ _) ≫
        spMap (algebraMap (𝓞 c.F) c.F) = (v ≫ Z.m.φ ≫ Z.t.G.hom) ≫ Z.s := fun v => by
      simp only [Category.assoc, ← pullback.condition]
      rw [← reassoc_of% Z.m.cart.1.w]
    have hh : Spec.map g ≫ spMap (algebraMap (𝓞 c.F) c.F) = Spec.map g' ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
      rw [hg, hg', e1, e1, h]
    rw [← Spec.map_comp, ← Spec.map_comp] at hh
    have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective hh)
    have h3 : g.hom = g'.hom := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) (by simpa using h2)
    simp only [Category.assoc]
    rw [← hg, ← hg', CommRingCat.hom_ext h3]

end
end GlobalTheory.ShFam

namespace GlobalTheory.ShFam.ToroidalCompactificationData

theorem hodge_gram_of_sameVec : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb κ.c σ → ∀ (W : UnfWit (s.U σ)) (i : Fin W.F.n) (P : (W.F.Di i).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab κ.c σ (W.e j).1) P → ∀ (Hm : Matrix (Fin W.g) (Fin W.g) ℂ), IsRiem W.F i P Hm → ∀ (q : FrPt (S.Xo κ.l) κ.c (CAt σ)) (z : ∀ τ : D.host.E →+* ℂ, Fin (S.Dw.mult τ) → (Fin W.g → ℂ)), AnLie W.F i P q z → ∀ (y : CxPts (genStr s.T.Z) σ), cxPt s.T.Z q = y → ∀ f : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z), (∀ τ k, ∃ w : Sp (DualNumber ℂ) ⟶ s.T.Z.oF.t.G.left, w ≫ s.T.Z.m0.toSABMap.φ = q.u τ k ∧ w ≫ s.T.Z.m.φ = f.v τ k) → ∀ τ a b, (x.hodge σ).gram y f τ a b = (Real.pi : ℂ) * hermForm Hm (z τ b) (z τ a) := by
  intro D A N j S κ s x σ hσ W i P hP Hm hH q z hq y hy f hf τ a b
  subst hy
  have hv : ∀ τ k, f.v τ k = (cxFrame s.T.Z q).v τ k := by
    intro τ k
    obtain ⟨w, hw0, hw⟩ := hf τ k
    obtain ⟨w', -, hw0', hw'⟩ := EigFrame.ofFrPt_v (S := CAt σ) s.T.Z q (Category.assoc _ _ _).symm τ k
    have hb : w ≫ s.T.Z.m.φ ≫ s.T.Z.t.G.hom = w' ≫ s.T.Z.m.φ ≫ s.T.Z.t.G.hom := by
      rw [reassoc_of% hw, reassoc_of% hw', (f.tan τ k).1]
      exact ((cxFrame s.T.Z q).tan τ k).1.symm
    have e : w = w' := oF_pt_ext (hw0.trans hw0'.symm) hb
    rw [← hw, e]
    exact hw'
  have hco : (cxFrame s.T.Z q).co f τ = 1 := by
    refine EigFrame.co_eq fun k => ?_
    rw [hv τ k]
    convert isCombAtG_single _ _ ((cxFrame s.T.Z q).tan τ) k using 1
    funext a
    simp [Matrix.one_apply, Pi.single_apply]
  rw [(x.hodge σ).change _ (cxFrame s.T.Z q) f τ, hco, x.hodge_gram_riemann hσ W hP hH hq τ]
  simp

end GlobalTheory.ShFam.ToroidalCompactificationData
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_form_frame_point : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb κ.c σ → ∀ (W : UnfWit (s.U σ)) (i : Fin W.F.n) (P : (W.F.Di i).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab κ.c σ (W.e j).1) P → ∀ (Hm : Matrix (Fin W.g) (Fin W.g) ℂ), IsRiem W.F i P Hm → ∀ (q : FrPt (S.Xo κ.l) κ.c (CAt σ)) (z : ∀ τ : D.host.E →+* ℂ, Fin (S.Dw.mult τ) → (Fin W.g → ℂ)), AnLie W.F i P q z → ∀ (y : CxPts (genStr s.T.Z) σ), cxPt s.T.Z q = y → ∀ f : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z), (∀ τ k, ∃ w : Sp (DualNumber ℂ) ⟶ s.T.Z.oF.t.G.left, w ≫ s.T.Z.m0.toSABMap.φ = q.u τ k ∧ w ≫ s.T.Z.m.φ = f.v τ k) → ∀ τ a b, (x.hodge σ).gram y f τ a b = (Real.pi : ℂ) * hermForm Hm (z τ b) (z τ a) := by
  first | exact @GlobalTheory.ShFam.ToroidalCompactificationData.hodge_gram_of_sameVec | exact GlobalTheory.ShFam.ToroidalCompactificationData.hodge_gram_of_sameVec | (intros; apply GlobalTheory.ShFam.ToroidalCompactificationData.hodge_gram_of_sameVec <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff

set_option autoImplicit false

theorem GlobalTheory.ShFam.ToroidalCompactificationData.hodge_gram_smooth_near : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb κ.c σ → ∀ (V : (gen s.T.Z).affineOpens) (φ : κ.c.F →+* Γ(gen s.T.Z, V.1)) (F : EigFrame s.T.Z φ (LogKS.chart V ≫ genι s.T.Z)) (τ : D.host.E →+* ℂ) (a b : Fin (S.Dw.mult τ)), LogKS.chart V ≫ genStr s.T.Z = spMap φ → ∀ y₀ : CxPts (genStr s.T.Z) σ, ¬ LiesIn y₀ (genBd s.T.Z) → y₀ ∈ ptsIn (genStr s.T.Z) σ V.1 → ∃ (T : Set (CxPts (genStr s.T.Z) σ)) (g : CxPts (genStr s.T.Z) σ → ℂ), IsOpen T ∧ y₀ ∈ T ∧ (manifold s.T.Z σ).SmoothOn T (fun y => (g y).re) ∧ (manifold s.T.Z σ).SmoothOn T (fun y => (g y).im) ∧ ∀ y ∈ T, ∀ (hy : y ∈ ptsIn (genStr s.T.Z) σ V.1) (f : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)), F.IsMap (evHom hy) f → (x.hodge σ).gram y f τ a b = g y := by
  intro D A N j S κ s x σ hσ V φ F τ a b hstr y₀ hbd hV
  obtain ⟨ch, hch⟩ := AlgChart.exists_mem_source (p := genStr s.T.Z) (σ := σ) (D := S.Dw.dim) y₀
  obtain ⟨W⟩ := nonempty_unfWit_of_isUnf _ _ _ _ _ _ σ _ _ (s.unf σ hσ).1
  obtain ⟨f₀, -⟩ := (FinalTheorems.exists_isHodgeFrame_iff (s := s) (y := y₀)).2 hbd
  obtain ⟨q₀, hq₀, -⟩ := GlobalTheory.T.exists_framedComplexPoint_of_eigenFrame_off_boundary _ _ _ _ _ _ _ _ s.T.Z σ y₀ hbd f₀
  obtain ⟨i, B, P, hB, hb₀, hBt, hPer, hPhol, hPu⟩ :=
    GlobalTheory.ShFam.chart_lift_periods _ _ _ _ _ _ _ _ s.T.Z σ S.Dw.dim W.g _ W.F ch q₀ (hq₀ ▸ hch)
  rw [hq₀] at hb₀
  obtain ⟨Hm, hHm, hHs⟩ := GlobalTheory.T.period_family_chart_domain _ _ _ _ _ _ σ W.g _ W.F i S.Dw.dim B P hB hPer hPhol
  have hmono : Mono (genι s.T.Z) := by
    have : Epi (CommRingCat.ofHom (algebraMap (𝓞 κ.c.F) κ.c.F)) := IsLocalization.epi (nonZeroDivisors (𝓞 κ.c.F)) κ.c.F
    have : Mono (spMap (algebraMap (𝓞 κ.c.F) κ.c.F)) := Scheme.Spec.map_mono (CommRingCat.ofHom _).op
    infer_instance
  obtain ⟨z, hz, hzl⟩ := GlobalTheory.T.period_family_chart_holomorphic _ _ _ _ _ _ _ _ s.T.Z σ S.Dw.dim W.g _ W.F ch i B P hB hBt hPer hPhol hPu hmono V φ F hstr
  set B' : Set (ReciprocityTheory.L2DbarEstimates.V S.Dw.dim) := {c ∈ B | ch.e.symm c ∈ ptsIn (genStr s.T.Z) σ V.1 ∧
    ¬ LiesIn (ch.e.symm c) (genBd s.T.Z)} with hB'
  have hB'o : IsOpen B' := by
    have h1 := ch.e.continuousOn_symm.isOpen_inter_preimage ch.e.open_target
      ((isOpen_ptsIn (p := genStr s.T.Z) (σ := σ) V.1).inter (isOpen_not_liesIn (p := genStr s.T.Z) (σ := σ) (genBd s.T.Z)))
    have e : B' = B ∩ (ch.e.target ∩ ch.e.symm ⁻¹' (ptsIn (genStr s.T.Z) σ V.1 ∩ {y | ¬ LiesIn y (genBd s.T.Z)})) := by
      ext c
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, hBt h1, h2, h3⟩
      · rintro ⟨h1, -, h2, h3⟩
        exact ⟨h1, h2, h3⟩
    rw [e]
    exact hB.inter h1
  have hz' : ∀ τ k p, ContDiffOn ℝ ∞ (fun c => z c τ k p) B' := fun τ k p =>
    GlobalTheory.ChartGlue.contDiffOn_real hB'o ((differentiableOn_pi.1 (hz τ k)) p)
  let G : ReciprocityTheory.L2DbarEstimates.V S.Dw.dim → ℂ := fun c => (Real.pi : ℂ) * hermForm (Hm c) (z c τ b) (z c τ a)
  have hG : ContDiffOn ℝ ∞ G B' := by
    have hc : ∀ p, ContDiffOn ℝ ∞ (fun c => star (z c τ a p)) B' := fun p =>
      Complex.conjCLE.contDiff.comp_contDiffOn (hz' τ a p)
    have e : G = fun c => (Real.pi : ℂ) * ∑ p, z c τ b p * ∑ q, Hm c p q * star (z c τ a q) := by
      funext c
      simp only [G, hermForm, dotProduct, Matrix.mulVec, Pi.star_apply]
    rw [e]
    exact contDiffOn_const.mul (ContDiffOn.sum fun p _ => (hz' τ b p).mul
      (ContDiffOn.sum fun q _ => ((hHs p q).mono fun c hc => hc.1).mul (hc q)))
  refine ⟨ch.e.source ∩ ch.e ⁻¹' B', fun y => G (ch.e y), ch.e.isOpen_inter_preimage hB'o,
    ⟨hch, hb₀, by rw [ch.e.left_inv hch]; exact hV, by rw [ch.e.left_inv hch]; exact hbd⟩, ?_, ?_, ?_⟩
  · intro c'
    have ht : ContDiffOn ℝ ∞ (ch.e ∘ c'.e.symm) (c'.e.target ∩ c'.e.symm ⁻¹' ch.e.source) :=
      (contDiffOn_piLp 2).2 fun a => GlobalTheory.ChartGlue.contDiffOn_real (GlobalTheory.ChartGlue.isOpen_over c'.e ch.e.open_source)
        (differentiableOn_euclidean.1 (AlgChart.holo_trans c' ch) a)
    exact (Complex.reCLM.contDiff.comp_contDiffOn hG).comp (ht.mono fun v hv => ⟨hv.1, hv.2.1⟩) fun v hv => hv.2.2
  · intro c'
    have ht : ContDiffOn ℝ ∞ (ch.e ∘ c'.e.symm) (c'.e.target ∩ c'.e.symm ⁻¹' ch.e.source) :=
      (contDiffOn_piLp 2).2 fun a => GlobalTheory.ChartGlue.contDiffOn_real (GlobalTheory.ChartGlue.isOpen_over c'.e ch.e.open_source)
        (differentiableOn_euclidean.1 (AlgChart.holo_trans c' ch) a)
    exact (Complex.imCLM.contDiff.comp_contDiffOn hG).comp (ht.mono fun v hv => ⟨hv.1, hv.2.1⟩) fun v hv => hv.2.2
  · rintro y ⟨hys, hyB⟩ hy f hf
    show _ = G (ch.e y)
    obtain ⟨c0, hc0, rfl⟩ : ∃ c0 ∈ B', ch.e.symm c0 = y := ⟨ch.e y, hyB, ch.e.left_inv hys⟩
    rw [ch.e.right_inv (hBt hc0.1)]
    obtain ⟨q, hq, hw⟩ := GlobalTheory.T.exists_framedComplexPoint_of_eigenFrame_off_boundary _ _ _ _ _ _ _ _ s.T.Z σ _ hc0.2.2 f
    have hd := hzl c0 hc0.1 hy f hf q hq hw
    have hu := hPu c0 hc0.1 q hq.symm
    exact GlobalTheory.T.riemann_form_frame_point D A N j S κ s x σ hσ W i (P c0) (hPer c0 hc0.1) (Hm c0) (hHm c0 hc0.1) q (z c0) ⟨hu.symm, hd⟩ _ hq f hw τ a b
end
