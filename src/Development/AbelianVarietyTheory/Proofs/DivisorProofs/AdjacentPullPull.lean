import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartDensityChangeFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsOffOpenFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFibreEmbeddingsCard
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinateNearGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAffineNeighbourhoodExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsArithVarEffCartier
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP

section
open MeasureTheory Topology
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glueMeas_univ_eq_mul_of_fibre_encard_eq : ∀ (n : ℕ), n ≠ 0 → ∀ (A B ι κ : Type) [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B] [SecondCountableTopology A] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B] [BorelSpace B] (e : ι → OpenPartialHomeomorph A (ReciprocityTheory.L2DbarEstimates.V n)) (ρ : ι → A → ℝ≥0∞) (e' : κ → OpenPartialHomeomorph B (ReciprocityTheory.L2DbarEstimates.V n)) (ρ' : κ → B → ℝ≥0∞), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e i j)) → (∀ i j y, y ∈ (e i).source → y ∈ (e j).source → ρ i y = ENNReal.ofReal (‖GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2) * ρ j y) → (∀ i j, DifferentiableOn ℂ (e' j ∘ (e' i).symm) (ReciprocityTheory.L2DbarEstimates.Y.ovl e' i j)) → (∀ i j y, y ∈ (e' i).source → y ∈ (e' j).source → ρ' i y = ENNReal.ofReal (‖GlobalTheory.ChartGlue.transDet (e' i) (e' j) y‖ ^ 2) * ρ' j y) → ∀ (m : B → A), Continuous m → ∀ T : Set A, T.Finite → (m ⁻¹' T).Finite → ∀ d : ℕ, d ≠ 0 → (∀ x ∉ T, (m ⁻¹' {x}).encard = d) → (∀ z, m z ∉ T → ∃ i j, z ∈ (e' j).source ∧ m z ∈ (e i).source ∧ ∀ w ∈ (e' j).source, m w ∈ (e i).source → e' j w = e i (m w) ∧ ρ' j w = ρ i (m w)) → GlobalTheory.ChartGlue.glueMeas e' ρ' Set.univ = d * GlobalTheory.ChartGlue.glueMeas e ρ Set.univ := by
  first | exact @GlobalTheory.GlueCover.glueMeas_univ_of_cover | exact GlobalTheory.GlueCover.glueMeas_univ_of_cover | (intros; apply GlobalTheory.GlueCover.glueMeas_univ_of_cover <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_metric_pullback_isometric : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (fl : Vert.Flag E r) (π : Y ⟶ X) (hπ : π ≫ p = q) (i : Fin r), (VMetric.grLB (fl.pull π) i (H.pull π hπ)).Isometric ((VMetric.grLB fl i H).pull π hπ) := by
  first | exact @GlobalTheory.VMetric.isometric_grLB_pull | exact GlobalTheory.VMetric.isometric_grLB_pull | (intros; apply GlobalTheory.VMetric.isometric_grLB_pull <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_points_off_open_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X], IsArithVar p 1 → ∀ U : X.Opens, genericPoint X ∈ U → ∀ σ : k →+* ℂ, (ptsIn p σ U)ᶜ.Finite := by
  first | exact @GlobalTheory.SurfacePoints.finite_compl_ptsIn | exact GlobalTheory.SurfacePoints.finite_compl_ptsIn | (intros; apply GlobalTheory.SurfacePoints.finite_compl_ptsIn <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_fibre_embeddings_card : ∀ (A B : Type) [CommRing A] [IsDomain A] [CommRing B] (f : A →+* B), f.Finite → f.Etale → ∀ φ : A →+* ℂ, {ψ : B →+* ℂ | ψ.comp f = φ}.encard = (letI := f.toAlgebra; Module.finrank A B : ℕ) := by
  first | exact @GlobalTheory.EtaleFibre.encard_points_eq_finrank | exact GlobalTheory.EtaleFibre.encard_points_eq_finrank | (intros; apply GlobalTheory.EtaleFibre.encard_points_eq_finrank <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_coordinate_near_generic_point : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X], IsArithVar p 1 → ∃ (U : X.Opens) (x : Fin 1 → Γ(X, U)), IsAffineOpen U ∧ genericPoint X ∈ U ∧ (MvPolynomial.eval₂Hom (algX p U) x).Etale := by
  first | exact @GlobalTheory.GenericEtale.exists_etale_coord_surface | exact GlobalTheory.GenericEtale.exists_etale_coord_surface | (intros; apply GlobalTheory.GenericEtale.exists_etale_coord_surface <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_affine_neighbourhood_exists : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar p 1 → IsArithVar q 1 → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ U₀ : X.Opens, genericPoint X ∈ U₀ → ∃ U : X.Opens, U ≤ U₀ ∧ IsAffineOpen U ∧ genericPoint X ∈ U ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧ (π.app U).hom.Finite ∧ (π.app U).hom.Etale ∧ (letI := (π.app U).hom.toAlgebra; Module.finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U)) = π.residueDegree (genericPoint Y) := by
  first | exact @GlobalTheory.GenFiniteEtale.exists_finite_etale | exact GlobalTheory.GenFiniteEtale.exists_finite_etale | (intros; apply GlobalTheory.GenFiniteEtale.exists_finite_etale <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ChartGlue
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.VBExt (AdaptedChart)
open ReciprocityTheory.L2DbarEstimates (V)
open Limits (cokernel)

namespace GlobalTheory.FlagPull

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open MeasureTheory VMetric
open scoped ENNReal

theorem exists_open_finite_etale : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (Y : Scheme.{0})
    [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar p 1 → IsArithVar q 1 → ∀ (π : Y ⟶ X), π ≫ p = q →
    π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 →
    ∃ (U : X.Opens) (x : Fin 1 → Γ(X, U)), IsAffineOpen U ∧ genericPoint X ∈ U ∧
      (MvPolynomial.eval₂Hom (algX p U) x).Etale ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧ (π.app U).hom.Finite ∧
      (π.app U).hom.Etale ∧
      (letI := (π.app U).hom.toAlgebra; Module.finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U)) =
        π.residueDegree (genericPoint Y) := by
  intro k _ X p _ Y _ q hp hq π hπ hg hd
  obtain ⟨U₁, x, hU₁, hg₁, hx⟩ := GlobalTheory.T.etale_coordinate_near_generic_point k X p hp
  obtain ⟨U, hle, hU, hgU, hV, h₁, h₂, h₃⟩ := GlobalTheory.T.finite_affine_neighbourhood_exists k X p Y q hp hq π hπ hg hd U₁ hg₁
  have hres := Scheme.Hom.etale_appLE (𝟙 X) hU₁ hU hle
  refine ⟨U, fun a => (Scheme.Hom.appLE (𝟙 X) U₁ U hle).hom (x a), hU, hgU, ?_, hV, h₁, h₂, h₃⟩
  have hw : 𝟙 X ≫ p = p ≫ spMap (RingHom.id k) := by
    rw [show spMap (RingHom.id k) = 𝟙 _ from Spec.map_id _, Category.comp_id, Category.id_comp]
  have e : (MvPolynomial.eval₂Hom (algX p U) fun a => (Scheme.Hom.appLE (𝟙 X) U₁ U hle).hom (x a)) =
      (Scheme.Hom.appLE (𝟙 X) U₁ U hle).hom.comp (MvPolynomial.eval₂Hom (algX p U₁) x) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun a => ?_
    · have := RingHom.congr_fun (TopForm.appLE_comp_algX (p := p) (p' := p) (φ := 𝟙 X)
        (σ := RingHom.id k) hw (V := U₁) (W := U) hle) a
      simpa using this.symm
    · simp
  rw [e]
  exact RingHom.Etale.stableUnderComposition _ _ hx hres

theorem exists_finite_exceptional : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (Y : Scheme.{0})
    [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar p 1 → IsArithVar q 1 → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q),
    π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ σ : k →+* ℂ,
    ∃ T : Set (CxPts p σ), T.Finite ∧ (PtsOver.map π hπ (spMap σ) ⁻¹' T).Finite ∧
      (∀ x ∉ T, (PtsOver.map π hπ (spMap σ) ⁻¹' {x}).encard = π.residueDegree (genericPoint Y)) ∧
      ∀ z, PtsOver.map π hπ (spMap σ) z ∉ T → ∃ (c : AlgChart p σ 1) (c' : AlgChart q σ 1),
        z ∈ c'.e.source ∧ PtsOver.map π hπ (spMap σ) z ∈ c.e.source ∧
        ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source →
          c'.e w = c.e (PtsOver.map π hπ (spMap σ) w) := by
  intro k _ X p _ Y _ q hp hq π hπ hg hd σ
  obtain ⟨U, x, hU, hgU, hx, hV, hfin, het, hr⟩ := exists_open_finite_etale k X p Y q hp hq π hπ hg hd
  have : Nonempty U := ⟨⟨_, hgU⟩⟩
  have hgV : genericPoint Y ∈ π ⁻¹ᵁ U := show π (genericPoint Y) ∈ U from hg ▸ hgU
  set m := PtsOver.map π hπ (spMap σ) with hm
  have hmem (z : CxPts q σ) : z ∈ ptsIn q σ (π ⁻¹ᵁ U) ↔ m z ∈ ptsIn p σ U := Iff.rfl
  have hCx (a : k) : algX q (π ⁻¹ᵁ U) a = (π.app U).hom (algX p U a) := by
    have hw : π ≫ p = q ≫ spMap (RingHom.id k) := by
      rw [hπ, show spMap (RingHom.id k) = 𝟙 _ from Spec.map_id _, Category.comp_id]
    have := RingHom.congr_fun (TopForm.appLE_comp_algX (p := p) (p' := q) (φ := π)
      (σ := RingHom.id k) hw (V := U) (W := π ⁻¹ᵁ U) le_rfl) a
    simpa [Scheme.Hom.app_eq_appLE] using this.symm
  have hcx : (MvPolynomial.eval₂Hom (algX q (π ⁻¹ᵁ U)) fun a => π.app U (x a)) =
      (π.app U).hom.comp (MvPolynomial.eval₂Hom (algX p U) x) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun a => ?_
    · simp [hCx]
    · simp
  have hx' : (MvPolynomial.eval₂Hom (algX q (π ⁻¹ᵁ U)) fun a => π.app U (x a)).Etale := by
    rw [hcx]
    exact RingHom.Etale.stableUnderComposition _ _ hx het
  refine ⟨(ptsIn p σ U)ᶜ, GlobalTheory.T.complex_points_off_open_finite k X p hp U hgU σ, GlobalTheory.T.complex_points_off_open_finite k Y q hq _ hgV σ, fun y hy => ?_, fun z hz => ?_⟩
  · have hy' : y ∈ ptsIn p σ U := not_not.1 hy
    have hc := GlobalTheory.T.etale_fibre_embeddings_card Γ(X, U) Γ(Y, π ⁻¹ᵁ U) (π.app U).hom hfin het (evHom hy')
    rw [hr] at hc
    rw [← hc]
    have hz (z : m ⁻¹' {y}) : z.1 ∈ ptsIn q σ (π ⁻¹ᵁ U) := (hmem z.1).2 (by rw [z.2]; exact hy')
    have hev (z : m ⁻¹' {y}) (a) : ev q σ _ ((π.app U).hom a) z.1 = ev p σ U a y := by
      exact (ev_app π hπ U a z.1).trans (congrArg _ z.2)
    refine Set.encard_congr (Equiv.ofBijective (fun z => ⟨evHom (hz z), RingHom.ext fun a => ?_⟩) ⟨?_, ?_⟩)
    · simp only [RingHom.comp_apply, ← ev_eq]
      exact hev z a
    · intro z z' h
      refine Subtype.ext (Subtype.ext (ext_of_valR hV (hz z) (hz z') fun a => ?_))
      have := RingHom.congr_fun (congrArg Subtype.val h) a
      exact (ev_eq (hz z) a).trans (this.trans (ev_eq (hz z') a).symm)
    · rintro ⟨ψ, hψ⟩
      have hC (a : k) : ψ (algX q (π ⁻¹ᵁ U) a) = σ a := by
        have e₁ : algX q (π ⁻¹ᵁ U) a = (π.app U).hom (algX p U a) := hCx a
        rw [e₁]
        exact (RingHom.congr_fun hψ _).trans ((ev_eq hy' _).symm.trans (ev_algX hy' a))
      have hzz := ofHom_mem hV ψ hC
      have hy₂ : m (ofHom hV ψ hC) = y := by
        refine Subtype.ext (ext_of_valR hU hzz hy' fun a => ?_)
        exact ((ev_app π hπ U a _).symm.trans (ev_ofHom hV ψ hC _)).trans
          ((RingHom.congr_fun hψ a).trans (ev_eq hy' a).symm)
      refine ⟨⟨ofHom hV ψ hC, hy₂⟩, Subtype.ext (RingHom.ext fun a => ?_)⟩
      exact (ev_eq hzz a).symm.trans (ev_ofHom hV ψ hC a)
  · have hz' : z ∈ ptsIn q σ (π ⁻¹ᵁ U) := not_not.1 hz
    obtain ⟨c, hc, hcU, hcx⟩ := AlgChart.exists_of_etale hU x hx (σ := σ) (hmem z |>.1 hz')
    obtain ⟨c', hc', hcU', hcx'⟩ := AlgChart.exists_of_etale hV _ hx' hz'
    refine ⟨c, c', hc', hc, fun w hw hw' => ?_⟩
    have key₁ : ∀ (U' : X.Opens) (h : U' = U) (x' : Fin 1 → Γ(X, U')), x' = h ▸ x → ∀ a y,
        ev p σ U' (x' a) y = ev p σ U (x a) y := by
      rintro U' rfl x' rfl a y
      rfl
    have key₂ : ∀ (U' : Y.Opens) (h : U' = π ⁻¹ᵁ U) (x' : Fin 1 → Γ(Y, U')),
        x' = h ▸ (fun a => π.app U (x a)) → ∀ a y,
        ev q σ U' (x' a) y = ev q σ (π ⁻¹ᵁ U) (π.app U (x a)) y := by
      rintro U' rfl x' rfl a y
      rfl
    ext a
    rw [c'.apply_eq w hw a, c.apply_eq _ hw' a, key₂ _ hcU' _ hcx', key₁ _ hcU _ hcx]
    exact ev_app π hπ U _ w

theorem bcMeas_pullStep {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} [IsIntegral X]
    {q : Y ⟶ Sp k} [IsIntegral Y] (hp : IsArithVar p 1) (hq : IsArithVar q 1) (π : Y ⟶ X) (hπ : π ≫ p = q)
    (hg : π (genericPoint Y) = genericPoint X) (hd : π.residueDegree (genericPoint Y) ≠ 0)
    {E : X.Modules} {r : ℕ} {h : VMetric p E r} (H : h.IsCInf) (fl : Vert.Flag E r) (i : Fin r) (σ : k →+* ℂ) :
    (((h.pull π hπ).stepMet (fl.pull π) i).met σ).bcMeas (stepSeq_shortExact (fl.pull π) i)
        ((fl.pull π).isVB i.castSucc) ((fl.pull π).isVB_gr i) univ =
      π.residueDegree (genericPoint Y) * ((h.stepMet fl i).met σ).bcMeas (stepSeq_shortExact fl i)
        (fl.isVB i.castSucc) (fl.isVB_gr i) univ := by
  obtain ⟨T, hT, hT', hf, hc⟩ := exists_finite_exceptional k X p Y q hp hq π hπ hg hd σ
  have H₁ : (h.stepMet fl i).IsCInf := H.restrict _ _
  have H₂ : ((h.pull π hπ).stepMet (fl.pull π) i).IsCInf := (H.pull π hπ).restrict _ _
  have := CxPts.t2Space_cxPts_of_isProjOver σ hp.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver σ hq.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hp.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hq.isProjOver
  refine GlobalTheory.T.glueMeas_univ_eq_mul_of_fibre_encard_eq 1 one_ne_zero (CxPts p σ) (CxPts q σ) (AlgChart p σ 1) (AlgChart q σ 1) _ _ _ _
    (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ?_)
    (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ?_)
    _ (PtsOver.continuous_map π hπ _) T hT hT' _ hd hf fun z hz => ?_
  · rw [Met.bcDens_trans _ _ _ c c' (H₁ σ) hy hy', ENNReal.ofReal_mul (sq_nonneg _)]
  · rw [Met.bcDens_trans _ _ _ c c' (H₂ σ) hy hy', ENNReal.ofReal_mul (sq_nonneg _)]
  · obtain ⟨c, c', h₁, h₂, h₃⟩ := hc z hz
    exact ⟨c, c', h₁, h₂, fun w hw hw' => ⟨h₃ w hw hw', congrArg _ (bcDens_pullStep H hπ c c' hw hw' h₃)⟩⟩

theorem exists_isSelfInter (hA : Published.ArCalc) {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} (hp : IsArithVar p 1) (L : HermLB p) : ∃ x, L.IsSelfInter x := by
  obtain ⟨Φ, hΦ⟩ := ((hA.arExists k X p 1 hp).2 PUnit fun _ => L).1
  exact ⟨_, ((hA.arIso k X p 1 hp).2 PUnit _ Φ hΦ).1 PUnit.unit⟩

theorem isFlagCh2_pull : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar p 1 → IsArithVar q 1 → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (fl : Vert.Flag E r), ∃ fl' : Vert.Flag ((Scheme.Modules.pullback π).obj E) r, ∀ a : ℝ, VMetric.IsFlagCh2 H fl a ↔ VMetric.IsFlagCh2 (H.pull π hπ) fl' (π.residueDegree (genericPoint Y) * a) := by
  intro hA k _ X p _ Y _ q hp hq π hπ hg hd E r h H fl
  refine ⟨fl.pull π, fun a => ?_⟩
  set d := π.residueDegree (genericPoint Y) with hd'
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd
  have hdE₀ : (d : ENNReal) ≠ 0 := Nat.cast_ne_zero.2 hd
  have hdE₁ : (d : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top d
  have hm := fun i σ => bcMeas_pullStep hp hq π hπ hg hd H fl i σ
  have hfin : h.FlagBcFinite fl ↔ (h.pull π hπ).FlagBcFinite (fl.pull π) := by
    have key (x : ENNReal) : x ≠ ⊤ ↔ (d : ENNReal) * x ≠ ⊤ := by
      simp [ENNReal.mul_eq_top, hdE₀, hdE₁]
    refine forall_congr' fun i => forall_congr' fun σ => ?_
    rw [hm i σ]
    exact key _
  have := hp.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  have hbc : (h.pull π hπ).flagBc (fl.pull π) = d * h.flagBc fl := by
    rw [flagBc, flagBc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bcInt, bcInt, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hm i σ, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hx : ∀ (i : Fin r) (x : ℝ), (grLB fl i H).IsSelfInter x →
      (grLB (fl.pull π) i (H.pull π hπ)).IsSelfInter (d * x) := fun i x hx =>
    (GlobalTheory.T.graded_metric_pullback_isometric k X Y p q E r h H fl π hπ i).symm.isSelfInter hq ((hA.arProj k X Y p q 1 hp hq π hπ hg hd).1 _ x hx)
  refine ⟨?_, ?_⟩
  · rintro ⟨h₁, x, h₂, rfl⟩
    refine ⟨hfin.1 h₁, fun i => d * x i, fun i => hx i _ (h₂ i), ?_⟩
    rw [hbc, mul_sub, Finset.mul_sum]
    simp only [mul_div_assoc]
  · rintro ⟨h₁, x', h₂, e⟩
    choose x hx₀ using fun i => exists_isSelfInter hA hp (grLB fl i H)
    refine ⟨hfin.2 h₁, x, hx₀, mul_left_cancel₀ hd0 (e.trans ?_)⟩
    have e' (i) : x' i = d * x i := (h₂ i).unique hq (hx i _ (hx₀ i))
    rw [hbc, mul_sub, Finset.mul_sum]
    simp only [e', mul_div_assoc]

end GlobalTheory.FlagPull
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.FlagPull

open VMetric

theorem isFlagCh2_flag_pull : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar p 1 → IsArithVar q 1 → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (fl : Vert.Flag E r) (a : ℝ), VMetric.IsFlagCh2 H fl a ↔ VMetric.IsFlagCh2 (H.pull π hπ) (fl.pull π) (π.residueDegree (genericPoint Y) * a) := by
  intro hA k _ X p _ Y _ q hp hq π hπ hg hd E r h H fl a
  set d := π.residueDegree (genericPoint Y) with hd'
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd
  have hdE₀ : (d : ENNReal) ≠ 0 := Nat.cast_ne_zero.2 hd
  have hdE₁ : (d : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top d
  have hm := fun i σ => bcMeas_pullStep hp hq π hπ hg hd H fl i σ
  have hfin : h.FlagBcFinite fl ↔ (h.pull π hπ).FlagBcFinite (fl.pull π) := by
    have key (x : ENNReal) : x ≠ ⊤ ↔ (d : ENNReal) * x ≠ ⊤ := by
      simp [ENNReal.mul_eq_top, hdE₀, hdE₁]
    refine forall_congr' fun i => forall_congr' fun σ => ?_
    rw [hm i σ]
    exact key _
  have := hp.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  have hbc : (h.pull π hπ).flagBc (fl.pull π) = d * h.flagBc fl := by
    rw [flagBc, flagBc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bcInt, bcInt, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hm i σ, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hx : ∀ (i : Fin r) (x : ℝ), (grLB fl i H).IsSelfInter x →
      (grLB (fl.pull π) i (H.pull π hπ)).IsSelfInter (d * x) := fun i x hx =>
    (GlobalTheory.T.graded_metric_pullback_isometric k X Y p q E r h H fl π hπ i).symm.isSelfInter hq ((hA.arProj k X Y p q 1 hp hq π hπ hg hd).1 _ x hx)
  refine ⟨?_, ?_⟩
  · rintro ⟨h₁, x, h₂, rfl⟩
    refine ⟨hfin.1 h₁, fun i => d * x i, fun i => hx i _ (h₂ i), ?_⟩
    rw [hbc, mul_sub, Finset.mul_sum]
    simp only [mul_div_assoc]
  · rintro ⟨h₁, x', h₂, e⟩
    choose x hx₀ using fun i => exists_isSelfInter hA hp (grLB fl i H)
    refine ⟨hfin.2 h₁, x, hx₀, mul_left_cancel₀ hd0 (e.trans ?_)⟩
    have e' (i) : x' i = d * x i := (h₂ i).unique hq (hx i _ (hx₀ i))
    rw [hbc, mul_sub, Finset.mul_sum]
    simp only [e', mul_div_assoc]

end GlobalTheory.FlagPull
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_smul app_resM)

namespace GlobalTheory.VB

theorem isFrame_of_epi_mono_principal {Y : Scheme.{0}} [IsIntegral Y] {E M L : Y.Modules}
    [E.IsQuasicoherent] [M.IsQuasicoherent] (π : E ⟶ M) (m : M ⟶ L) [Epi π] [Mono m]
    {V : Y.Opens} {l : Fin 1 → Γ(L, V)} {g : Γ(Y, V)} {t : Γ(E, V)} (hl : IsFrame l) (hg : g ≠ 0)
    (ht : (π ≫ m).app V t = g • l 0)
    (hs : ∀ (W : Y.Opens) (h : W ≤ V) (s : Γ(E, W)), ∃ a : Γ(Y, W),
      (π ≫ m).app W s = a • resM L h (g • l 0)) :
    IsFrame (fun _ : Fin 1 => π.app V t) := by
  have hc (W : Y.Opens) (s : Γ(E, W)) : (π ≫ m).app W s = m.app W (π.app W s) := rfl
  refine isFrame_of_forall_exists fun V' h x hx => ?_
  obtain ⟨W, hW, hxW, hle⟩ := QCoh.exists_affine_mem_le x hx
  refine ⟨W, hle, hxW, ?_⟩
  have hWV : W ≤ V := hle.trans h
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hm (a : Fin 1 → Γ(Y, W)) :
      m.app W (Fintype.linearCombination Γ(Y, W) (fun _ : Fin 1 => resM M hWV (π.app V t)) a) =
        a 0 • resM L hWV (g • l 0) := by
    rw [Fintype.linearCombination_apply, Fin.sum_univ_one, Scheme.Modules.Hom.app_smul, app_resM,
      ← hc, ht]
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    have h1 := hm a
    rw [ha, map_zero, resM_smul, smul_smul] at h1
    have h2 := (hl W hWV).1 (a₁ := fun _ => a 0 * resG Y hWV g) (a₂ := 0) (by
      rw [map_zero, Fintype.linearCombination_apply, Fin.sum_univ_one]
      exact h1.symm)
    have h3 : a 0 * resG Y hWV g = 0 := congrFun h2 0
    have h4 : resG Y hWV g ≠ 0 := fun h0 =>
      hg (map_injective_of_isIntegral Y (homOfLE hWV) (h0.trans (map_zero _).symm))
    funext i
    rw [Subsingleton.elim i 0]
    exact (mul_eq_zero.1 h3).resolve_right h4
  · intro s
    obtain ⟨u, rfl⟩ := QCoh.surjective_app_of_epi π hW s
    obtain ⟨a, ha⟩ := hs W hWV u
    refine ⟨fun _ => a, QCoh.injective_app_of_mono m W ?_⟩
    rw [hm, ← hc, ha]

theorem isSubbundle_kernel_of_locally_principal :
    ∀ (Y : Scheme.{0}) [IsIntegral Y] (E L : Y.Modules) (ψ : E ⟶ L) (n : ℕ), IsVB E (n + 1) →
      IsVB L 1 → (∀ y : Y, ∃ (V : Y.Opens) (l : Fin 1 → Γ(L, V)) (g : Γ(Y, V)) (t : Γ(E, V)),
        y ∈ V ∧ IsFrame l ∧ g ≠ 0 ∧ (ψ).app V t = g • l 0 ∧
        ∀ (W : Y.Opens) (h : W ≤ V) (s : Γ(E, W)), ∃ a : Γ(Y, W),
          (ψ).app W s = a • GlobalTheory.Twist.resM (L) h (g • l 0)) →
      IsSubbundle (Limits.kernel.ι ψ) ∧ IsVB (Limits.kernel ψ) n := by
  intro Y _ E L ψ n hE hL H
  have := hE.isQuasicoherent
  have := hL.isQuasicoherent
  have hM : IsVB (cokernel (kernel.ι ψ)) 1 := by
    intro y
    obtain ⟨V, l, g, t, hy, hl, hg, ht, hs⟩ := H y
    have e : cokernel.π (kernel.ι ψ) ≫ Abelian.factorThruCoimage ψ = ψ := Abelian.coimage.fac ψ
    exact ⟨V, _, hy, isFrame_of_epi_mono_principal (cokernel.π (kernel.ι ψ))
      (Abelian.factorThruCoimage ψ) hl hg (by rw [e]; exact ht) (by rw [e]; exact hs)⟩
  refine ⟨⟨inferInstance, 1, hM⟩, ?_⟩
  have hS : (ShortComplex.mk _ _ (cokernel.condition (kernel.ι ψ))).ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  exact isVB_X₁_of_shortExact Y _ n 1 hS hE hM

end GlobalTheory.VB
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

open GlobalTheory.Twist (resM resM_resM resM_smul app_resM)

namespace GlobalTheory.VB

theorem mem_annihilator_cokernel_iff {X : Scheme.{0}} {E L : X.Modules} (φ : E ⟶ L)
    [SheafOfModules.IsQuasicoherent E] [SheafOfModules.IsQuasicoherent L]
    [QCoh.IsFiniteQC (Limits.cokernel φ)] {U : X.Opens} (hU : IsAffineOpen U)
    {l : Fin 1 → Γ(L, U)} (hl : IsFrame l) (a : Γ(X, U)) :
    a ∈ Module.annihilator Γ(X, U) Γ(Limits.cokernel φ, U) ↔ ∃ u, φ.app U u = a • l 0 := by
  have hex : Function.Exact (φ.app U) ((Limits.cokernel.π φ).app U) :=
    QCoh.exact_app_of_exact (S := ShortComplex.mk φ (Limits.cokernel.π φ)
      (Limits.cokernel.condition φ)) (ShortComplex.exact_cokernel φ) hU
  have hsur := QCoh.surjective_app_of_epi (Limits.cokernel.π φ) hU
  have hsm (b : Γ(X, U)) (s : Γ(L, U)) :
      (Limits.cokernel.π φ).app U (b • s) = b • (Limits.cokernel.π φ).app U s :=
    (QCoh.appLinear (Limits.cokernel.π φ) U).map_smul b s
  rw [Module.mem_annihilator]
  constructor
  · intro H
    refine (hex _).1 ?_
    rw [hsm]
    exact H _
  · rintro ⟨u, hu⟩ m
    obtain ⟨s, rfl⟩ := hsur m
    have h0 : a • (Limits.cokernel.π φ).app U (l 0) = 0 := by
      rw [← hsm]
      exact (hex _).2 ⟨u, hu⟩
    have hs := (hl.basis le_rfl).sum_repr s
    rw [Fin.sum_univ_one, IsFrame.basis_apply, Twist.resM_self] at hs
    rw [← hs, hsm, smul_comm, h0, smul_zero]

theorem exists_image_principal_of_effCartier : ∀ (X Y : Scheme.{0}) [IsIntegral Y] (ρ : Y ⟶ X) (E L : X.Modules) (φ : E ⟶ L) (r : ℕ) [GlobalTheory.QCoh.IsFiniteQC (Limits.cokernel φ)], IsVB E r → IsVB L 1 → ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier ((GlobalTheory.QCoh.annihilatorSheaf (Limits.cokernel φ)).comap ρ) → ∀ y : Y, ∃ (V : Y.Opens) (l : Fin 1 → Γ((Scheme.Modules.pullback ρ).obj L, V)) (g : Γ(Y, V)) (t : Γ((Scheme.Modules.pullback ρ).obj E, V)), y ∈ V ∧ IsFrame l ∧ g ≠ 0 ∧ ((Scheme.Modules.pullback ρ).map φ).app V t = g • l 0 ∧ ∀ (W : Y.Opens) (h : W ≤ V) (s : Γ((Scheme.Modules.pullback ρ).obj E, W)), ∃ a : Γ(Y, W), ((Scheme.Modules.pullback ρ).map φ).app W s = a • GlobalTheory.Twist.resM ((Scheme.Modules.pullback ρ).obj L) h (g • l 0) := by
  intro X Y _ ρ E L φ r _ hE hL hC y
  haveI := hE.isQuasicoherent
  haveI := hL.isQuasicoherent
  obtain ⟨U₀, l₀, hyU₀, hl₀⟩ := hL (ρ y)
  obtain ⟨U, e, hU, hyU, hle, he⟩ := hE.exists_affine hyU₀
  have hl := hl₀.res hle
  set l : Fin 1 → Γ(L, U) := fun i => resM L hle (l₀ i) with hldef
  obtain ⟨U', f, hyU', hf, hI⟩ := hC y
  obtain ⟨h, hhle, hyh⟩ := U'.2.exists_basicOpen_le (V := ρ ⁻¹ᵁ U) ⟨y, hyU⟩ hyU'
  let A : Y.affineOpens := Y.affineBasicOpen h
  have hAU : (A : Y.Opens) ≤ ρ ⁻¹ᵁ U := hhle
  have hAU' : A ≤ U' := Y.basicOpen_le h
  have hyA : y ∈ (A : Y.Opens) := hyh
  let g : Γ(Y, A) := Y.presheaf.map (homOfLE hAU').op f
  have hI1 : ((QCoh.annihilatorSheaf (Limits.cokernel φ)).comap ρ).ideal A = Ideal.span {g} := by
    rw [← Scheme.IdealSheafData.map_ideal _ hAU', hI, Ideal.map_span, Set.image_singleton]
  have hI2 := Principalise.comapIdealAffine (QCoh.annihilatorSheaf (Limits.cokernel φ)) ρ
    ⟨U, hU⟩ A hAU
  rw [hI1, QCoh.annihilatorSheaf_ideal] at hI2
  have hg : g ≠ 0 := by
    haveI : Nonempty (A : Y.Opens) := ⟨⟨y, hyA⟩⟩
    haveI : Nonempty (U' : Y.Opens) := ⟨⟨y, hyU'⟩⟩
    intro h0
    refine nonZeroDivisors.ne_zero hf ?_
    apply map_injective_of_isIntegral Y (homOfLE (show (A : Y.Opens) ≤ U' from hAU'))
    rw [map_zero]
    exact h0
  have hres (F : X.Modules) (s : Γ(F, U)) :
      resM _ hAU (QCoh.pullbackSections ρ F le_rfl s) = QCoh.pullbackSections ρ F hAU s :=
    QCoh.res_pullbackSections ρ F le_rfl hAU s
  have hl' : IsFrame fun i => QCoh.pullbackSections ρ L hAU (l i) := by
    simpa only [hres] using (hl.pullback ρ).res hAU
  have he' : IsFrame fun i => QCoh.pullbackSections ρ E hAU (e i) := by
    simpa only [hres] using (he.pullback ρ).res hAU
  set l' := QCoh.pullbackSections ρ L hAU (l 0) with hl'def
  let ψ := (Scheme.Modules.pullback ρ).map φ
  have key (u : Γ(E, U)) (a : Γ(X, U)) (hu : φ.app U u = a • l 0) :
      ψ.app A (QCoh.pullbackSections ρ E hAU u) = ρ.appLE U A hAU a • l' := by
    rw [QCoh.pullback_map_app_pullbackSections, hu, QCoh.pullbackSections_smul]
  let J : Ideal Γ(Y, A) := (LinearMap.range (QCoh.appLinear ψ A)).comap
    (LinearMap.toSpanSingleton Γ(Y, A) _ l')
  have hgJ : g ∈ J := by
    have : Ideal.span {g} ≤ J := by
      rw [hI2, Ideal.map_le_iff_le_comap]
      intro a ha
      obtain ⟨u, hu⟩ := (mem_annihilator_cokernel_iff φ hU hl a).1 ha
      exact ⟨_, key u a hu⟩
    exact this (Ideal.subset_span rfl)
  obtain ⟨t, ht⟩ := hgJ
  have hei (i : Fin r) : ∃ c : Γ(Y, A),
      ψ.app A (QCoh.pullbackSections ρ E hAU (e i)) = c • (g • l') := by
    have hs := (hl.basis le_rfl).sum_repr (φ.app U (e i))
    rw [Fin.sum_univ_one, IsFrame.basis_apply, Twist.resM_self] at hs
    have hm : ρ.appLE U A hAU ((hl.basis le_rfl).repr (φ.app U (e i)) 0) ∈ Ideal.span {g} := by
      rw [hI2]
      exact Ideal.mem_map_of_mem _ ((mem_annihilator_cokernel_iff φ hU hl _).2 ⟨_, hs.symm⟩)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hm
    exact ⟨c, by rw [key _ _ hs.symm, ← hc, mul_smul]⟩
  choose c hc using hei
  refine ⟨A, _, g, t, hyA, hl', hg, ht, fun W hW s => ?_⟩
  refine ⟨∑ i, (he'.basis hW).repr s i * resG Y hW (c i), ?_⟩
  have hs := (he'.basis hW).sum_repr s
  calc ψ.app W s = QCoh.appLinear ψ W (∑ i, (he'.basis hW).repr s i • he'.basis hW i) := by
        rw [hs]; rfl
    _ = _ := by
      rw [map_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, IsFrame.basis_apply, QCoh.appLinear_apply, app_resM, hc, resM_smul, mul_smul]

end GlobalTheory.VB
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.VB

theorem genericPoint_notMem_support_cokernel_of_ne_zero :
    ∀ (X : Scheme.{0}) [IsIntegral X] (E L : X.Modules) (φ : E ⟶ L), IsVB L 1 → φ ≠ 0 → genericPoint X ∉ GlobalTheory.QCoh.support (Limits.cokernel φ) := by
  intro X _ E L φ hL h0
  have hex : ∃ (V : X.Opens) (s : Γ(E, V)), φ.app V s ≠ 0 := by
    by_contra hc
    push Not at hc
    apply h0
    ext V s
    exact (hc V s).trans rfl
  obtain ⟨V, s, hs⟩ := hex
  have hV : genericPoint X ∈ V := by
    by_contra hη
    refine hs (QCoh.section_eq_zero_of_germ _ fun x hx => ?_)
    exact absurd (VB.genericPoint_mem hx) hη
  have hg : L.presheaf.germ V _ hV (φ.app V s) ≠ 0 := fun h => hs (hL.isTorsionFree V hV _ h)
  have hr : Module.finrank X.functionField (genStalk L) = 1 := hL.genRank_eq
  have hsurj : Function.Surjective (QCoh.stalkLinear φ (genericPoint X)) := by
    intro w
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hg).1 hr w
    refine ⟨c • E.presheaf.germ V _ hV s, ?_⟩
    rw [map_smul, QCoh.stalkLinear_germ]
    exact hc
  have hexact := (QCoh.exact_iff_stalkLinear _).1 (ShortComplex.exact_cokernel φ) (genericPoint X)
  refine QCoh.notMem_support_iff.2 ⟨fun a b => ?_⟩
  have key : ∀ y, y = (0 : ((Limits.cokernel φ).presheaf.stalk (genericPoint X) :)) := by
    intro y
    obtain ⟨t, rfl⟩ := QCoh.stalkLinear_surjective (Limits.cokernel.π φ) (genericPoint X) y
    obtain ⟨u, rfl⟩ := hsurj t
    exact (hexact _).2 ⟨u, rfl⟩
  rw [key a, key b]

end GlobalTheory.VB
end

section
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Vert

namespace GlobalTheory.FlagChain

section Sub

variable {C C' : Type*} [Category C] [Category C'] {A B A' E E' : C}

def Le (f : A ⟶ E) (g : B ⟶ E) : Prop := ∃ u : A ⟶ B, u ≫ g = f

def Same (f : A ⟶ E) (g : B ⟶ E) : Prop := ∃ e : A ≅ B, e.hom ≫ g = f

variable {f : A ⟶ E} {g : B ⟶ E} {f' : A' ⟶ E}

theorem Le.trans (h : Le f g) (h' : Le g f') : Le f f' := by
  obtain ⟨u, rfl⟩ := h
  obtain ⟨v, rfl⟩ := h'
  exact ⟨u ≫ v, Category.assoc ..⟩

theorem Le.map (h : Le f g) (F : C ⥤ C') : Le (F.map f) (F.map g) := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨F.map u, (F.map_comp ..).symm⟩

theorem Same.refl (f : A ⟶ E) : Same f f := ⟨Iso.refl _, Category.id_comp _⟩

theorem Same.symm (h : Same f g) : Same g f := by
  obtain ⟨e, rfl⟩ := h
  exact ⟨e.symm, e.inv_hom_id_assoc _⟩

theorem Same.trans (h : Same f g) (h' : Same g f') : Same f f' := by
  obtain ⟨u, rfl⟩ := h
  obtain ⟨v, rfl⟩ := h'
  exact ⟨u ≪≫ v, Category.assoc ..⟩

theorem Same.le (h : Same f g) : Le f g := h.elim fun e he => ⟨e.hom, he⟩

theorem Same.map (h : Same f g) (F : C ⥤ C') : Same (F.map f) (F.map g) := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨F.mapIso u, (F.map_comp ..).symm⟩

theorem Same.comp (h : Same f g) (t : E ⟶ E') : Same (f ≫ t) (g ≫ t) := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨u, (Category.assoc ..).symm⟩

theorem same_natIso {F G : C ⥤ C'} (e : F ≅ G) (f : A ⟶ E) :
    Same (F.map f ≫ (e.app E).hom) (G.map f) :=
  ⟨e.app A, (e.hom.naturality f).symm⟩

end Sub

section Bundles

variable {X Y Z : Scheme.{0}} {A B E E' H : X.Modules} {r : ℕ}

theorem isSubbundle_comp {u : A ⟶ B} {g : B ⟶ E} (hu : IsSubbundle u) (hg : IsSubbundle g) :
    IsSubbundle (u ≫ g) := by
  have := hu.mono
  have := hg.mono
  obtain ⟨s, hs⟩ := hu.isVB_cokernel
  obtain ⟨t, ht⟩ := hg.isVB_cokernel
  exact ⟨inferInstance, _, (VBExt.isVB_and_cls_det_of_shortExact X _ _ _
    (Vert.shortExact_cokernel_comp u g) hs ht).1⟩

theorem isVB_cokernel [Nonempty X] {g : B ⟶ E} {b : ℕ} (hg : IsSubbundle g) (hB : IsVB B b)
    (hE : IsVB E r) : ∃ s, r = b + s ∧ IsVB (cokernel g) s := by
  obtain ⟨_, s, hs⟩ := hg
  exact ⟨s, hE.rank_unique (VBExt.isVB_and_cls_det_of_shortExact X (.mk g (cokernel.π _)
    (cokernel.condition _)) b s { exact := ShortComplex.exact_cokernel _ } hB hs).1, hs⟩

theorem isVB_cokernel_one [Nonempty X] {u : A ⟶ B} {g : B ⟶ E} {a : ℕ} (hu : IsSubbundle (u ≫ g))
    (hg : IsSubbundle g) (hA : IsVB A a) (hB : IsVB B (a + 1)) (hE : IsVB E r) :
    IsVB (cokernel u) 1 := by
  have := hg.mono
  obtain ⟨s, e, hs⟩ := isVB_cokernel hu hA hE
  obtain ⟨t, e', ht⟩ := isVB_cokernel hg hB hE
  obtain rfl : s = 1 + t := by omega
  exact VB.isVB_X₁_of_shortExact X _ 1 _ (Vert.shortExact_cokernel_comp u g) hs ht

abbrev Joined (fl fl' : Flag E r) : Prop := Relation.ReflTransGen Flag.Adjacent fl fl'

theorem Joined.pull {fl fl' : Flag E r} (h : Joined fl fl') (ρ : Y ⟶ X) :
    Joined (fl.pull ρ) (fl'.pull ρ) :=
  h.lift (fun a : Flag E r => a.pull ρ) fun _ _ ⟨j, hj⟩ =>
    ⟨j, fun i hi => Same.map (hj i hi) (Scheme.Modules.pullback ρ)⟩

theorem Joined.ofIso {fl fl' : Flag E r} (h : Joined fl fl') (e : E ≅ E') :
    Joined (fl.ofIso e) (fl'.ofIso e) :=
  h.lift (fun a : Flag E r => a.ofIso e) fun _ _ ⟨j, hj⟩ =>
    ⟨j, fun i hi => Same.comp (hj i hi) e.hom⟩

theorem adjacent_pull_pull (fl : Flag E r) (ρ : Y ⟶ X) (τ : Z ⟶ Y) :
    (((fl.pull ρ).pull τ).ofIso ((Scheme.Modules.pullbackComp τ ρ).app E)).Adjacent
      (fl.pull (τ ≫ ρ)) :=
  ⟨0, fun i _ => same_natIso (Scheme.Modules.pullbackComp τ ρ) (fl.ι i)⟩

theorem Joined.pull_comp {fl fl' : Flag E r} {ρ : Y ⟶ X} {τ : Z ⟶ Y}
    (h : Joined ((fl.pull ρ).pull τ) ((fl'.pull ρ).pull τ)) :
    Joined (fl.pull (τ ≫ ρ)) (fl'.pull (τ ≫ ρ)) :=
  ((h.ofIso _).tail (adjacent_pull_pull fl' ρ τ)).head (adjacent_pull_pull fl ρ τ).symm

theorem exists_update (fl : Flag E r) (j : Fin (r + 1)) {κ : H ⟶ E} (hs : IsSubbundle κ)
    (hv : IsVB H j) (hl : j ≠ Fin.last r)
    (h₁ : ∀ i : Fin r, i.succ = j → Le (fl.ι i.castSucc) κ)
    (h₂ : ∀ i : Fin r, i.castSucc = j → Le κ (fl.ι i.succ)) :
    ∃ fl' : Flag E r, Same (fl'.ι j) κ ∧ ∀ i, i ≠ j → Same (fl'.ι i) (fl.ι i) := by
  let G : Fin (r + 1) → Σ A : X.Modules, (A ⟶ E) :=
    Function.update (fun i => ⟨fl.F i, fl.ι i⟩) j ⟨H, κ⟩
  have e₁ : G j = ⟨H, κ⟩ := Function.update_self ..
  have e₂ (i) (hi : i ≠ j) : G i = ⟨fl.F i, fl.ι i⟩ := Function.update_of_ne hi ..
  have hsub (i) : IsSubbundle (G i).2 := by
    by_cases hi : i = j
    · rw [hi, e₁]; exact hs
    · rw [e₂ i hi]; exact fl.isSubbundle i
  have hvb (i) : IsVB (G i).1 i := by
    by_cases hi : i = j
    · rw [hi, e₁]; exact hv
    · rw [e₂ i hi]; exact fl.isVB i
  have hstep (i : Fin r) : Le (G i.castSucc).2 (G i.succ).2 := by
    by_cases hi : i.castSucc = j
    · rw [e₂ i.succ (hi ▸ i.castSucc_lt_succ.ne'), hi, e₁]; exact h₂ i hi
    by_cases hi' : i.succ = j
    · rw [e₂ _ hi, hi', e₁]; exact h₁ i hi'
    · rw [e₂ _ hi, e₂ _ hi']; exact ⟨fl.step i, fl.step_ι i⟩
  choose step step_ι using hstep
  have hiso : IsIso (G (Fin.last r)).2 := by
    rw [e₂ _ hl.symm]; exact fl.isIso_last
  refine ⟨⟨fun i => (G i).1, fun i => (G i).2, hsub, hvb, step, step_ι, hiso⟩, ?_, fun i hi => ?_⟩
  · change Same (G j).2 κ
    rw [e₁]; exact .refl _
  · change Same (G i).2 _
    rw [e₂ i hi]; exact .refl _

end Bundles

section Covers

variable {k : Type} [CommRing k] {D : ℕ} {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  [IsIntegral Z] {p : X ⟶ Sp k} {A E L H : X.Modules} {r : ℕ}

def IsCov (p : X ⟶ Sp k) (D : ℕ) (ρ : Y ⟶ X) : Prop :=
  IsArithVar (ρ ≫ p) D ∧ ρ (genericPoint Y) = genericPoint X ∧ ρ.residueDegree (genericPoint Y) ≠ 0

theorem IsCov.id (h : IsArithVar p D) : IsCov p D (𝟙 X) :=
  ⟨(Category.id_comp p).symm ▸ h, rfl, (Scheme.Hom.residueDegree_id _).trans_ne one_ne_zero⟩

theorem IsCov.comp {ρ : Y ⟶ X} {τ : Z ⟶ Y} (h : IsCov p D ρ) (h' : IsCov (ρ ≫ p) D τ) :
    IsCov p D (τ ≫ ρ) := by
  refine ⟨(Category.assoc τ ρ p).symm ▸ h'.1, ?_, ?_⟩
  · rw [Scheme.Hom.comp_apply, h'.2.1, h.2.1]
  · rw [CurveDegreesCompare.residueDegree_comp, h'.2.1]
    exact mul_ne_zero h.2.2 h'.2.2

theorem exists_cov_kernel (hX : IsArithVar p D) (φ : E ⟶ L) {n : ℕ} (hE : IsVB E (n + 1))
    (hL : IsVB L 1) (hφ : φ ≠ 0) : ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (_ : IsIntegral Y), IsCov p D ρ ∧
      IsSubbundle (kernel.ι ((Scheme.Modules.pullback ρ).map φ)) ∧
      IsVB (kernel ((Scheme.Modules.pullback ρ).map φ)) n := by
  have := hE.isFiniteQC
  have := hL.isFiniteQC
  obtain ⟨Y, ρ, _, h₁, h₂, h₃, h₄⟩ := BlowArith.exists_isArithVar_effCartier k X p D hX (QCoh.annihilatorSheaf (cokernel φ))
    fun h => VB.genericPoint_notMem_support_cokernel_of_ne_zero X E L φ hL hφ ((QCoh.coe_support_annihilatorSheaf _).le h)
  exact ⟨Y, ρ, inferInstance, ⟨h₁, h₂, h₃⟩, VB.isSubbundle_kernel_of_locally_principal Y _ _ _ n (hE.pullback ρ) (hL.pullback ρ)
    (VB.exists_image_principal_of_effCartier X Y ρ E L φ _ hE hL h₄)⟩

theorem exists_common (hX : IsArithVar p D) (fl : Flag E r) {n : ℕ} (hn : n + 1 < r) {κ : H ⟶ E}
    (hs : IsSubbundle κ) (hv : IsVB H (n + 1)) (hle : Le κ (fl.ι ⟨n + 2, by omega⟩)) :
    ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (_ : IsIntegral Y), IsCov p D ρ ∧
      ∃ (K : Y.Modules) (μ : K ⟶ (Scheme.Modules.pullback ρ).obj E), IsSubbundle μ ∧ IsVB K n ∧
        Le μ ((fl.pull ρ).ι ⟨n + 1, by omega⟩) ∧ Le μ ((Scheme.Modules.pullback ρ).map κ) := by
  obtain ⟨u, rfl⟩ := hle
  have := hs.mono
  have : Mono u := mono_of_mono u (fl.ι _)
  have hL := isVB_cokernel_one hs (fl.isSubbundle _) hv (fl.isVB _) fl.isVB_self
  let s : fl.F ⟨n + 1, by omega⟩ ⟶ fl.F ⟨n + 2, by omega⟩ := fl.step ⟨n + 1, hn⟩
  have hs' : s ≫ fl.ι _ = fl.ι _ := fl.step_ι ⟨n + 1, hn⟩
  by_cases hφ : s ≫ cokernel.π u = 0
  · have h₀ : Le (fl.ι ⟨n, by omega⟩) (fl.ι ⟨n + 1, by omega⟩) :=
      ⟨fl.step ⟨n, by omega⟩, fl.step_ι ⟨n, by omega⟩⟩
    have h₁ : Le (fl.ι ⟨n + 1, by omega⟩) (u ≫ fl.ι _) :=
      ⟨Abelian.monoLift u s hφ, by rw [Abelian.monoLift_comp_assoc, hs']⟩
    exact ⟨X, 𝟙 X, inferInstance, .id hX, _, (fl.pull _).ι ⟨n, by omega⟩, (fl.pull _).isSubbundle _,
      (fl.pull _).isVB _, h₀.map _, (h₀.trans h₁).map _⟩
  obtain ⟨Y, ρ, _, hρ, h₁, h₂⟩ := exists_cov_kernel hX _ (fl.isVB ⟨n + 1, by omega⟩) hL hφ
  refine ⟨Y, ρ, inferInstance, hρ, _, kernel.ι _ ≫ (fl.pull ρ).ι ⟨n + 1, by omega⟩,
    isSubbundle_comp h₁ ((fl.pull ρ).isSubbundle _), h₂, ⟨_, rfl⟩, ?_⟩
  have : Mono ((Scheme.Modules.pullback ρ).map u) :=
    (SubPull.isSubbundle_pullback X Y ρ _ _ u _ hv ⟨inferInstance, 1, hL⟩).mono
  have h₃ : (kernel.ι ((Scheme.Modules.pullback ρ).map (s ≫ cokernel.π u)) ≫
      (Scheme.Modules.pullback ρ).map s) ≫ cokernel.π ((Scheme.Modules.pullback ρ).map u) = 0 := by
    rw [← cancel_mono (cokernelComparison u (Scheme.Modules.pullback ρ)), Category.assoc,
      π_comp_cokernelComparison, Category.assoc, ← Functor.map_comp, kernel.condition, zero_comp]
  refine ⟨Abelian.monoLift _ _ h₃, ?_⟩
  refine (congrArg (_ ≫ ·) (Functor.map_comp _ u _)).trans
    ((Abelian.monoLift_comp_assoc _ _ h₃ _).trans ((Category.assoc ..).trans ?_))
  rw [← Functor.map_comp, hs']
  rfl

def Moves (p : X ⟶ Sp k) (D : ℕ) (fl : Flag E r) (n : Fin (r + 1)) (κ : H ⟶ E) : Prop :=
  ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (_ : IsIntegral Y), IsCov p D ρ ∧
    ∃ g : Flag ((Scheme.Modules.pullback ρ).obj E) r, Joined (fl.pull ρ) g ∧
      Same (g.ι n) ((Scheme.Modules.pullback ρ).map κ) ∧
      ∀ i, n < i → Same (g.ι i) ((fl.pull ρ).ι i)

theorem Moves.of_pull {fl : Flag E r} {n : Fin (r + 1)} {κ : H ⟶ E} {ρ : Y ⟶ X} (hρ : IsCov p D ρ)
    (h : Moves (ρ ≫ p) D (fl.pull ρ) n ((Scheme.Modules.pullback ρ).map κ)) : Moves p D fl n κ := by
  obtain ⟨Z, τ, _, hτ, g, h₁, h₂, h₃⟩ := h
  exact ⟨Z, τ ≫ ρ, inferInstance, hρ.comp hτ, g.ofIso ((Scheme.Modules.pullbackComp τ ρ).app E),
    (h₁.ofIso _).head (adjacent_pull_pull fl ρ τ).symm,
    (h₂.comp _).trans (same_natIso (Scheme.Modules.pullbackComp τ ρ) κ), fun i hi =>
      ((h₃ i hi).comp _).trans (same_natIso (Scheme.Modules.pullbackComp τ ρ) (fl.ι i))⟩

theorem moves (n : ℕ) : ∀ {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {E H : X.Modules},
    IsArithVar p D → ∀ (fl : Flag E r) (hn : n < r) (κ : H ⟶ E), IsSubbundle κ → IsVB H n →
      Le κ (fl.ι ⟨n + 1, by omega⟩) → Moves p D fl ⟨n, by omega⟩ κ := by
  induction n with
  | zero =>
    intro X _ p E H hX fl hn κ _ hv _
    have h₀ := isVB_zero_iff.1 ((fl.pull (𝟙 X)).isVB ⟨0, by omega⟩)
    exact ⟨X, 𝟙 X, inferInstance, .id hX, _, .refl,
      ⟨h₀.iso (isVB_zero_iff.1 (hv.pullback _)), h₀.eq_of_src _ _⟩, fun _ _ => .refl _⟩
  | succ n ih =>
    intro X _ p E H hX fl hn κ hs hv hle
    obtain ⟨Y, ρ, _, hρ, K, μ, h₁, h₂, h₃, h₄⟩ := exists_common hX fl hn hs hv hle
    refine .of_pull hρ ?_
    obtain ⟨Z, τ, _, hτ, g, k₁, k₂, k₃⟩ := ih hρ.1 (fl.pull ρ) (by omega) μ h₁ h₂ h₃
    obtain ⟨g', l₁, l₂⟩ := exists_update g ⟨n + 1, by omega⟩
      (SubPull.isSubbundle_pullback _ _ τ _ _ _ _ (hv.pullback ρ)
        (SubPull.isSubbundle_pullback _ _ ρ _ _ κ _ hv hs)) ((hv.pullback ρ).pullback τ)
      (fun e => hn.ne (congrArg Fin.val e))
      (fun i hi => by
        obtain rfl : i = ⟨n, Nat.lt_of_succ_lt hn⟩ := Fin.ext (Nat.succ_injective (congrArg Fin.val hi))
        exact k₂.le.trans (h₄.map _))
      (fun i hi => by
        obtain rfl : i = ⟨n + 1, hn⟩ := Fin.ext (congrArg Fin.val hi :)
        exact ((hle.map _).map _).trans
          (k₃ ⟨n + 2, by omega⟩ (Fin.mk_lt_mk.2 (by omega))).symm.le)
    exact ⟨Z, τ, inferInstance, hτ, g', k₁.tail ⟨_, fun i hi => (l₂ i hi).symm⟩, l₁, fun i hi =>
      (l₂ i hi.ne').trans (k₃ i (lt_trans (Fin.mk_lt_mk.2 n.lt_succ_self) hi))⟩

theorem joined_of_same (n : ℕ) : ∀ {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {E : X.Modules},
    IsArithVar p D → n ≤ r → ∀ fl fl' : Flag E r,
      (∀ i : Fin (r + 1), n ≤ i → Same (fl.ι i) (fl'.ι i)) →
      ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (_ : IsIntegral Y), IsCov p D ρ ∧
        Joined (fl.pull ρ) (fl'.pull ρ) := by
  induction n with
  | zero =>
    intro X _ p E hX _ fl fl' h
    exact ⟨X, 𝟙 X, inferInstance, .id hX,
      Joined.pull (.single ⟨0, fun i _ => h i (Nat.zero_le _)⟩) _⟩
  | succ n ih =>
    intro X _ p E hX hn fl fl' h
    obtain ⟨Y, ρ, _, hρ, g, h₁, h₂, h₃⟩ := moves n hX fl hn (fl'.ι ⟨n, by omega⟩)
      (fl'.isSubbundle _) (fl'.isVB _)
      (Le.trans ⟨fl'.step ⟨n, hn⟩, fl'.step_ι ⟨n, hn⟩⟩ (h ⟨n + 1, by omega⟩ le_rfl).symm.le)
    obtain ⟨Z, τ, _, hτ, k₁⟩ := ih hρ.1 (by omega) g (fl'.pull ρ) fun i hi => by
      rcases hi.eq_or_lt with e | e
      · obtain rfl : i = ⟨n, Nat.lt_succ_of_lt hn⟩ := Fin.ext e.symm
        exact h₂
      · exact (h₃ i e).trans ((h i e).map _)
    exact ⟨Z, τ ≫ ρ, inferInstance, hρ.comp hτ, Joined.pull_comp ((h₁.pull τ).trans k₁)⟩

theorem exists_cov_joined (hX : IsArithVar p D) (fl fl' : Flag E r) :
    ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (_ : IsIntegral Y), IsCov p D ρ ∧
      Joined (fl.pull ρ) (fl'.pull ρ) :=
  joined_of_same r hX le_rfl fl fl' fun i hi => by
    obtain rfl : i = Fin.last r := Fin.last_le_iff.1 hi
    exact ⟨asIso (fl.ι _) ≪≫ (asIso (fl'.ι _)).symm, by simp⟩

end Covers

theorem exists_seq {α : Type*} {R : α → α → Prop} {a b : α} (h : Relation.ReflTransGen R a b) :
    ∃ (m : ℕ) (g : Fin (m + 1) → α), g 0 = a ∧ g (Fin.last m) = b ∧
      ∀ j : Fin m, R (g j.castSucc) (g j.succ) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, fun _ => b, rfl, rfl, finZeroElim⟩
  | @head a c hac _ ih =>
    obtain ⟨m, g, rfl, h₂, h₃⟩ := ih
    exact ⟨m + 1, Fin.cons a g, rfl, h₂, Fin.cases hac h₃⟩

theorem exists_chain : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X], (∀ (Y : Scheme.{0}) (q : Y ⟶ Sp k) [IsIntegral Y], IsArithVar q 1 → Nonempty (RegCover q)) → IsArithVar p 1 → ∀ (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (fl fl' : Vert.Flag E r), ∃ (C : RegCover p) (m : ℕ) (g : Fin (m + 1) → Vert.Flag ((Scheme.Modules.pullback C.ρ).obj E) r), (∀ a : ℝ, VMetric.IsFlagCh2 H fl a ↔ VMetric.IsFlagCh2 (H.pull C.ρ rfl) (g 0) (C.deg * a)) ∧ (∀ a : ℝ, VMetric.IsFlagCh2 H fl' a ↔ VMetric.IsFlagCh2 (H.pull C.ρ rfl) (g (Fin.last m)) (C.deg * a)) ∧ ∀ j : Fin m, (g j.castSucc).Adjacent (g j.succ) := by
  intro hA k _ X p _ hR hX E r h H fl fl'
  obtain ⟨Y, ρ, _, hρ, hj⟩ := exists_cov_joined hX fl fl'
  obtain ⟨C'⟩ := hR Y (ρ ≫ p) hρ.1
  have hC : IsCov p 1 (C'.ρ ≫ ρ) := hρ.comp ⟨C'.reg.toIsArithVar, C'.generic, C'.finite⟩
  obtain ⟨m, g, h₀, h₁, h₂⟩ := exists_seq (hj.pull C'.ρ).pull_comp
  refine ⟨⟨C'.Y, C'.ρ ≫ ρ, (Category.assoc C'.ρ ρ p).symm ▸ C'.reg, hC.2.1, hC.2.2⟩, m, g,
    fun a => ?_, fun a => ?_, h₂⟩
  · rw [h₀]
    exact FlagPull.isFlagCh2_flag_pull hA k X p _ _ hX hC.1 _ rfl hC.2.1 hC.2.2 E r h H fl a
  · rw [h₁]
    exact FlagPull.isFlagCh2_flag_pull hA k X p _ _ hX hC.1 _ rfl hC.2.1 hC.2.2 E r h H fl' a

end GlobalTheory.FlagChain
end
