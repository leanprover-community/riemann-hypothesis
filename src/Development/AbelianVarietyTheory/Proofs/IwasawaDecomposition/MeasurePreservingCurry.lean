import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingGlueLowerUnitriangularBlocks
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralLeadingMinorFlagDensityPosDef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorSignsOverBoundedFlagDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFintypeProd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PoissonSummationInfinitePlaceGaussianLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DomainPointStabilizerTrivial

section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_leadingMinorFlagDensity_posDef : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ), A.PosDef → ∫⁻ y : Low m → ℂ, ENNReal.ofReal (dens A y) = ENNReal.ofReal (A.det.re ^ (1 - (m : ℤ)) / flagConst m) := by
  first | exact @GlobalTheory.FlagFibre.FlagInt.lintegral_dens | exact GlobalTheory.FlagFibre.FlagInt.lintegral_dens | (intros; apply GlobalTheory.FlagFibre.FlagInt.lintegral_dens <;> assumption)
end

section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibreInt

theorem dens_neg {m : ℕ} (B : Matrix (Fin m) (Fin m) ℂ) (y : Low m → ℂ) : dens (-B) y = dens B y := by
  unfold dens
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Matrix.mul_neg, Matrix.neg_mul, lminor, lminor, submatrix_neg, Pi.neg_apply, Pi.neg_apply, det_neg]
  simp

theorem shear_neg_J {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) :
    shear (-Jpq p q) Z = fromBlocks (-1) (-Z) (-Zᴴ) (hQ Z) := by
  simp [shear, Jpq, hQ, fromBlocks_neg, fromBlocks_conjTranspose, fromBlocks_multiply, sub_eq_neg_add]

theorem flagConst_pos (m : ℕ) : 0 < flagConst m :=
  Finset.prod_pos fun i _ => by have := Real.pi_pos; positivity

theorem lintegral_dens_glue : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ), reindex e e A = -Jpq p q → ∀ v : Fin p × Fin q → ℂ, toMat v ∈ hcDom p q → ∫⁻ b : (Low q → ℂ) × (Low p → ℂ), ENNReal.ofReal (dens A (glue e (v, b))) = ENNReal.ofReal ((hQ (toMat v)).det.re ^ (-((p + q : ℕ) : ℤ)) / (flagConst p * flagConst q)) := by
  intro r p q e he A hA v hv
  set Z := toMat v with hZ
  have hH : (hQ Z).PosDef := hv
  have hd := hH.det_pos
  have hu : IsUnit (hQ Z).det := hd.ne'.isUnit
  set B : Matrix (Fin p) (Fin p) ℂ := 1 + Z * (hQ Z)⁻¹ * Zᴴ with hB
  have hBp : B.PosDef := PosDef.one.add_posSemidef (hH.inv.posSemidef.mul_mul_conjTranspose_same Z)
  have hs : schur (shear (-Jpq p q) Z) = -B := by
    rw [shear_neg_J, schur, hB]
    simp
    abel
  have h22 : (shear (-Jpq p q) Z).toBlocks₂₂ = hQ Z := by rw [shear_neg_J, toBlocks_fromBlocks₂₂]
  have hdet : B.det = ((hQ Z).det)⁻¹ := by
    have e1 : (1 : Matrix (Fin q) (Fin q) ℂ) + (hQ Z)⁻¹ * Zᴴ * Z = (hQ Z)⁻¹ := by
      rw [Matrix.mul_assoc, ← nonsing_inv_mul _ hu, ← Matrix.mul_add, hQ, sub_add_cancel, Matrix.mul_one]
    rw [hB, Matrix.mul_assoc, det_one_add_mul_comm, e1, det_nonsing_inv, Ring.inverse_eq_inv']
  obtain ⟨d, hd0, hdd⟩ : ∃ d : ℝ, 0 < d ∧ (hQ Z).det = d := by
    obtain ⟨h1, h2⟩ := Complex.pos_iff.1 hd
    exact ⟨_, h1, Complex.ext (by simp) (by simp [← h2])⟩
  have hpt : ∀ b : (Low q → ℂ) × (Low p → ℂ), ENNReal.ofReal (dens A (glue e (v, b))) =
      (ENNReal.ofReal (d ^ (-(2 * p : ℤ))) * ENNReal.ofReal (dens (hQ Z) b.1)) * ENNReal.ofReal (dens B b.2) := by
    intro b
    rw [GlobalTheory.T.leadingMinorFlagDensity_glueLowerUnitriangular r p q e he A (v, b) (by rw [hA]; exact h22 ▸ hu), hA]
    simp only [← hZ]
    rw [h22, hs, dens_neg, hdd, Complex.norm_real, Real.norm_of_nonneg hd0.le,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (mul_nonneg (by positivity) (dens_nonneg _ _)),
      mul_comm (dens (hQ Z) b.1)]
  simp only [hpt]
  rw [Measure.volume_eq_prod, lintegral_prod_mul
    (f := fun y => ENNReal.ofReal (d ^ (-(2 * p : ℤ))) * ENNReal.ofReal (dens (hQ Z) y))
    (g := fun y => ENNReal.ofReal (dens B y))
    ((measurable_dens _).ennreal_ofReal.const_mul _).aemeasurable (measurable_dens _).ennreal_ofReal.aemeasurable,
    lintegral_const_mul _ (measurable_dens _).ennreal_ofReal, GlobalTheory.T.lintegral_leadingMinorFlagDensity_posDef _ _ hH, GlobalTheory.T.lintegral_leadingMinorFlagDensity_posDef _ _ hBp, hdet, hdd,
    ← Complex.ofReal_inv, Complex.ofReal_re, Complex.ofReal_re]
  have hp := flagConst_pos p
  have hq := flagConst_pos q
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [_root_.inv_zpow', ← mul_div_assoc _ _ (flagConst q), div_mul_div_comm, ← zpow_add₀ hd0.ne', ← zpow_add₀ hd0.ne', mul_comm (flagConst q)]
  congr 2
  push_cast
  ring

end GlobalTheory.FlagFibreInt
end

section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_flagDensity_fibre_boundedDomain : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ), reindex e e A = -Jpq p q → ∀ v : Fin p × Fin q → ℂ, toMat v ∈ hcDom p q → ∫⁻ b : (Low q → ℂ) × (Low p → ℂ), ENNReal.ofReal (dens A (glue e (v, b))) = ENNReal.ofReal ((hQ (toMat v)).det.re ^ (-((p + q : ℕ) : ℤ)) / (flagConst p * flagConst q)) := by
  first | exact @GlobalTheory.FlagFibreInt.lintegral_dens_glue | exact GlobalTheory.FlagFibreInt.lintegral_dens_glue | (intros; apply GlobalTheory.FlagFibreInt.lintegral_dens_glue <;> assumption)
end

section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leading_minor_signs_over_bounded_flag_domain : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ), reindex e e A = -Jpq p q → ∀ y : Low r → ℂ, toMat (base e y) ∈ hcDom p q → ∀ i : Fin (r + 1), 0 < psgn q i * (lminor ((uni y)ᴴ * A * uni y) i).re := by
  first | exact @GlobalTheory.FlagFibre.signs_over_dom | exact GlobalTheory.FlagFibre.signs_over_dom | (intros; apply GlobalTheory.FlagFibre.signs_over_dom <;> assumption)
end

section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.ProdFibre

theorem lintegral_pi_fibre : ∀ (T A B C : Type) [Fintype T] [MeasureSpace A] [MeasureSpace B] [MeasureSpace C] [SigmaFinite (volume : Measure A)] [SigmaFinite (volume : Measure B)] [SigmaFinite (volume : Measure C)] (g : A × B → C) (π : C → A) (D : C → ℝ≥0∞) (φ : (T → A) → ℝ≥0∞), MeasurePreserving g volume volume → Measurable π → (∀ w, π (g w) = w.1) → Measurable D → Measurable φ → ∫⁻ c : T → C, φ (fun t => π (c t)) * ∏ t, D (c t) = ∫⁻ a : T → A, φ a * ∏ t, ∫⁻ b, D (g (a t, b)) := by
  intro T A B C _ _ _ _ _ _ _ g π D φ hg hπ hgπ hD hφ
  have h1 : MeasurePreserving (fun (a : T → A × B) (t : T) => g (a t)) volume volume :=
    volume_preserving_pi (f := fun _ : T => g) (fun _ => hg)
  have h2 := (volume_measurePreserving_arrowProdEquivProdArrow A B T).symm
  have h3 := h1.comp h2
  have hF : Measurable (fun c : T → C => φ (fun t => π (c t)) * ∏ t, D (c t)) := by
    refine Measurable.mul (hφ.comp ?_) ?_
    · exact measurable_pi_lambda _ (fun t => hπ.comp (measurable_pi_apply t))
    · exact Finset.measurable_prod _ (fun t _ => hD.comp (measurable_pi_apply t))
  rw [← h3.lintegral_comp hF, Measure.volume_eq_prod]
  refine (lintegral_prod _ (hF.comp h3.measurable).aemeasurable).trans ?_
  refine lintegral_congr (fun a => ?_)
  have hm : ∀ t, Measurable (fun b : B => D (g (a t, b))) := fun t =>
    hD.comp (hg.measurable.comp measurable_prodMk_left)
  have hin := GlobalTheory.SnMass.Push.lintegral_fintype_prod (X := fun _ : T => B)
    (μ := fun _ => (volume : Measure B)) (fun t b => D (g (a t, b))) hm
  rw [← hin, ← volume_pi, ← lintegral_const_mul]
  · refine lintegral_congr (fun b => ?_)
    change φ (fun t => π (g (a t, b t))) * ∏ t, D (g (a t, b t)) = _
    simp only [hgπ]
  · exact Finset.measurable_prod _ (fun t _ => (hm t).comp (measurable_pi_apply t))

end GlobalTheory.ProdFibre
end

section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_pi_fibre_measurePreserving : ∀ (T A B C : Type) [Fintype T] [MeasureSpace A] [MeasureSpace B] [MeasureSpace C] [SigmaFinite (volume : Measure A)] [SigmaFinite (volume : Measure B)] [SigmaFinite (volume : Measure C)] (g : A × B → C) (π : C → A) (D : C → ℝ≥0∞) (φ : (T → A) → ℝ≥0∞), MeasurePreserving g volume volume → Measurable π → (∀ w, π (g w) = w.1) → Measurable D → Measurable φ → ∫⁻ c : T → C, φ (fun t => π (c t)) * ∏ t, D (c t) = ∫⁻ a : T → A, φ a * ∏ t, ∫⁻ b, D (g (a t, b)) := by
  first | exact @GlobalTheory.ProdFibre.lintegral_pi_fibre | exact GlobalTheory.ProdFibre.lintegral_pi_fibre | (intros; apply GlobalTheory.ProdFibre.lintegral_pi_fibre <;> assumption)
end

section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre

theorem measurePreserving_coords_sorted (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ) :
    MeasurePreserving (coords X κ) volume volume := by
  let e : Fin (nd X) ≃ Tau × Low r :=
    ((Equiv.prodCongr κ (Equiv.refl (Low r))).trans (Fintype.equivFin (Ent X))).symm
  have h1 := GlobalTheory.volume_preserving_ofLp_complex (Fin (nd X))
  have h2 := volume_preserving_arrowCongr' e (MeasurableEquiv.refl ℂ) (MeasurePreserving.id _)
  have h3 := GlobalTheory.FlagBase.PoissonV.measurePreserving_curry Tau (Low r)
  exact h3.comp (h2.comp h1)

end GlobalTheory.FlagFibre
end

section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurePreserving_flagFibreChartCoordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), MeasurePreserving (coords X κ) volume volume := by
  first | exact @GlobalTheory.FlagFibre.measurePreserving_coords_sorted | exact GlobalTheory.FlagFibre.measurePreserving_coords_sorted | (intros; apply GlobalTheory.FlagFibre.measurePreserving_coords_sorted <;> assumption)
end

section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.domain_point_stabilizer_trivial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, domPt X hj κ (lact γ x) = domPt X hj κ x → γ = 1 := by
  first | exact @GlobalTheory.FreeOnDomain.eq_one_of_domPt_lact_eq | exact GlobalTheory.FreeOnDomain.eq_one_of_domPt_lact_eq | (intros; apply GlobalTheory.FreeOnDomain.eq_one_of_domPt_lact_eq <;> assumption)
end

section
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre.FundPre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ae_lact_notMem (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    {Bad : Set (Frame X.Ψ r)} (hB : MeasurableSet Bad)
    (hinv : ∀ x, ∀ b ∈ Bor X.Ψ r, (rmul x b ∈ Bad ↔ x ∈ Bad))
    (h0 : ∀ᵐ z ∂muF X x0, cpt X x0 z ∉ Bad) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    ∀ᵐ z ∂muF X x0, lact γ (cpt X x0 z) ∉ Bad := by
  have hφ : Measurable (Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞)) :=
    measurable_one.indicator hB
  have hM := measInv_holds (E := E) r X x0 (lact γ x0) ho (KU.isOrth_lact X hγ ho)
    (Bad.indicator 1) hφ (fun x _ b hb => by
      classical
      simp only [Set.indicator_apply, hinv x b hb, Pi.one_apply])
  have h1 : ∫⁻ z, Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X x0 z) ∂muF X x0 = 0 := by
    rw [lintegral_congr_ae (g := fun _ => 0), lintegral_zero]
    filter_upwards [h0] with z hz
    exact Set.indicator_of_notMem hz _
  rw [h1, KU.muF_lact X hγ] at hM
  have hm : Measurable fun z => Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X (lact γ x0) z) :=
    hφ.comp (KU.cont_cpt X _).measurable
  have h2 := (lintegral_eq_zero_iff hm).1 hM.symm
  filter_upwards [h2] with z hz hbad
  rw [← KU.cpt_lact] at hbad
  simp only [Set.indicator_of_mem hbad, Pi.one_apply, Pi.zero_apply] at hz
  exact one_ne_zero hz

theorem isFundSet_preimage (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ)
    (X : Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ)
    (hp : X.p0 = r - j)
    (hfree : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, domPt X hj κ (lact γ x) = domPt X hj κ x → γ = 1)
    (hnull : ∀ N, MeasurableSet N → N ⊆ DomFlat Tau j (r - j) → muD Tau j (r - j) N = 0 →
      muF X (x0F X) (proj X hj κ ⁻¹' N) = 0)
    (F : Set (Tau × Fin j × Fin (r - j) → ℂ)) (hF : IsFD (gammaU X hj κ) F) :
    ∃ F', MeasurableSet F' ∧ F' ⊆ F ∧ muD Tau j (r - j) (F \ F') = 0 ∧
      IsFundSet X (x0F X) (proj X hj κ ⁻¹' F' ∩ OmF X (x0F X)) := by
  obtain ⟨hFm, hFD, hcov, hbad⟩ := hF
  obtain ⟨N0, hN0, hN0m, hN0z⟩ := exists_measurable_superset_of_null hbad
  have ho := isOrth_x0F X
  have hOm : MeasurableSet (OmF X (x0F X)) :=
    ((FourierCoefficientDomain.isOpen_dom X).preimage (KU.cont_cpt X (x0F X))).measurableSet
  have hNm : MeasurableSet (F ∩ N0) := hFm.inter hN0m
  have hNz : muD Tau j (r - j) (F ∩ N0) = 0 := measure_mono_null Set.inter_subset_right hN0z
  refine ⟨F \ N0, hFm.diff hN0m, Set.sdiff_subset, ?_, ?_, Set.inter_subset_right, ?_, ?_⟩
  · rw [Set.sdiff_sdiff_right_self]; exact hNz
  · exact (measurable_proj X hj κ (hFm.diff hN0m)).inter hOm
  · rintro z ⟨⟨hz, hzN⟩, hzO⟩ z' ⟨⟨hz', -⟩, -⟩ γ hγ b hb h
    have hd : domPt X hj κ (cpt X (x0F X) z') = domPt X hj κ (lact γ (cpt X (x0F X) z)) := by
      rw [h, KU.lact_rmul', domPt_rmul X hj κ hb]
    have hfix : domPt X hj κ (lact γ (cpt X (x0F X) z)) = domPt X hj κ (cpt X (x0F X) z) := by
      by_contra hne
      apply hzN
      apply hN0
      refine ⟨hz, toUpq X hj κ γ, ⟨γ, hγ, rfl⟩, ?_, ?_⟩
      · change flat (moebI _ (domPt X hj κ (cpt X (x0F X) z))) ∈ F
        rw [← domPt_lact X hj κ hp γ hzO, ← hd]
        exact hz'
      · change moebI _ (domPt X hj κ (cpt X (x0F X) z)) ≠ domPt X hj κ (cpt X (x0F X) z)
        rw [← domPt_lact X hj κ hp γ hzO]
        exact hne
    have h1 := hfree γ hγ _ hzO hfix
    rw [h1, KU.lact_one] at h
    have hS : cpt X (x0F X) z' ∈ KU.Sset X (x0F X) {z} := by
      rw [h, KU.rmul_mem_S X hb, KU.cpt_mem_S X ho]
      rfl
    exact ((KU.cpt_mem_S X ho z').1 hS).symm
  · have := KU.countable_Γ X
    have hA : ∀ᵐ z ∂muF X (x0F X), ∀ γ : X.Γ, lact (γ : GL (Fin r) E) (cpt X (x0F X) z) ∉
        (fun x => flat (domPt X hj κ x)) ⁻¹' (F ∩ N0) := by
      refine ae_all_iff.2 fun γ => ae_lact_notMem X ho (measurable_domPt X hj κ hNm) ?_ ?_ γ.2
      · intro x b hb
        simp only [Set.mem_preimage, domPt_rmul X hj κ hb]
      · exact measure_eq_zero_iff_ae_notMem.1
          (hnull _ hNm (Set.inter_subset_left.trans hFD) hNz)
    have hB : ∀ᵐ z ∂muF X (x0F X), ∀ γ : X.Γ, lact (γ : GL (Fin r) E) (cpt X (x0F X) z) ∉
        (KU.Sset X (x0F X) (OmF X (x0F X)))ᶜ := by
      refine ae_all_iff.2 fun γ => ae_lact_notMem X ho (KU.meas_S X ho hOm).compl ?_ ?_ γ.2
      · intro x b hb
        simp only [Set.mem_compl_iff, KU.rmul_mem_S X hb]
      · filter_upwards [ExtFPf.ae_OmF (X := X) (x0 := x0F X)] with z hz hn
        exact hn ((KU.cpt_mem_S X ho z).2 hz)
    filter_upwards [hA, hB, ExtFPf.ae_OmF (X := X) (x0 := x0F X)] with z hzA hzB hzO
    obtain ⟨_, ⟨γ, hγ, rfl⟩, hγF⟩ := hcov _ (domPt_mem X hj κ hp hzO)
    rw [← domPt_lact X hj κ hp γ hzO] at hγF
    have h1 := hzA ⟨γ, hγ⟩
    obtain ⟨⟨z', b⟩, ⟨hz', hb⟩, he⟩ := not_not.1 (hzB ⟨γ, hγ⟩)
    have he' : rmul (cpt X (x0F X) z') b = lact γ (cpt X (x0F X) z) := he
    have hpr : proj X hj κ z' = flat (domPt X hj κ (lact γ (cpt X (x0F X) z))) := by
      rw [← he', domPt_rmul X hj κ hb]; rfl
    refine ⟨z', ⟨?_, hz'⟩, γ⁻¹, X.Γ.inv_mem hγ, b, hb, ?_⟩
    · rw [Set.mem_preimage, hpr]
      exact ⟨hγF, fun hn => h1 ⟨hγF, hn⟩⟩
    · rw [he', KU.lact_lact, inv_mul_cancel, KU.lact_one]

end GlobalTheory.FlagFibre.FundPre
end

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFundamentalSet_chart_preimage_fundamentalDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, domPt X hj κ (lact γ x) = domPt X hj κ x → γ = 1) → (∀ N, MeasurableSet N → N ⊆ DomFlat Tau j (r - j) → muD Tau j (r - j) N = 0 → muF X (x0F X) (proj X hj κ ⁻¹' N) = 0) → ∀ F, IsFD (gammaU X hj κ) F → ∃ F', MeasurableSet F' ∧ F' ⊆ F ∧ muD Tau j (r - j) (F \ F') = 0 ∧ IsFundSet X (x0F X) (proj X hj κ ⁻¹' F' ∩ OmF X (x0F X)) := by
  atlas_forward_decl GlobalTheory.FlagFibre.FundPre.isFundSet_preimage
end

section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

noncomputable section

namespace GlobalTheory.FlagFibre

theorem measurePreserving_curry (ι κ : Type) [Fintype ι] [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℂ) volume volume := by
  have h : (volume : Measure (ι × κ → ℂ)) =
      (volume : Measure (ι → κ → ℂ)).map (MeasurableEquiv.curry ι κ ℂ).symm := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hs)]
    have e : (MeasurableEquiv.curry ι κ ℂ).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
      ext f; simp [MeasurableEquiv.coe_curry_symm, Function.uncurry]
    rw [e, volume_pi, Measure.pi_pi]
    simp_rw [volume_pi, Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  refine ⟨(MeasurableEquiv.curry ι κ ℂ).measurable, ?_⟩
  rw [h, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
  simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r j : ℕ} (X : Data E r) (hj : j ≤ r) {Tau : Type}
  [Fintype Tau] (κ : Tau ≃ X.Ψ)

theorem mem_OmF_of_proj (hp : X.p0 = r - j) {z : V (nd X)} (hz : proj X hj κ z ∈ DomFlat Tau j (r - j)) :
    z ∈ OmF X (x0F X) := by
  intro τ
  obtain ⟨t, rfl⟩ := κ.surjective τ
  refine ⟨?_, fun i => ?_⟩
  · have e : mat (cpt X (x0F X) z) (κ t) = mat (x0F X) (κ t) * uni (coords X κ z t) := rfl
    rw [e, det_mul, det_uni, mul_one]
    exact det_x0F X _
  · rw [dmin_cpt X κ z t i, hp]
    refine GlobalTheory.T.leading_minor_signs_over_bounded_flag_domain r j (r - j) (idx hj) (isBlockOrderedSumEquiv_trueIndex hj) _ (reindex_sgn hj) _ ?_ i
    have h := hz t
    have e : unflat (proj X hj κ z) t = toMat (base (idx hj) (coords X κ z t)) := by
      ext a b; exact proj_eq X hj κ z t (a, b)
    rwa [e] at h

theorem inter_OmF (hp : X.p0 = r - j) {S : Set (Tau × Fin j × Fin (r - j) → ℂ)} (hD : S ⊆ DomFlat Tau j (r - j)) :
    proj X hj κ ⁻¹' S ∩ OmF X (x0F X) = proj X hj κ ⁻¹' S :=
  Set.inter_eq_left.2 fun _ hz => mem_OmF_of_proj X hj κ hp (hD hz)

theorem densF_eq (z : V (nd X)) :
    densF X (x0F X) z = ∏ t, dens (sgnMat r X.p0) (coords X κ z t) := by
  rw [densF, ← κ.prod_comp]
  exact Finset.prod_congr rfl fun t _ => Finset.prod_congr rfl fun i _ => by rw [dmin_cpt X κ z t]

theorem muF_preimage (hp : X.p0 = r - j) {S : Set (Tau × Fin j × Fin (r - j) → ℂ)} (hS : MeasurableSet S)
    (hD : S ⊆ DomFlat Tau j (r - j)) :
    muF X (x0F X) (proj X hj κ ⁻¹' S) =
      ENNReal.ofReal ((flagConst j * flagConst (r - j))⁻¹ ^ Fintype.card Tau) * muD Tau j (r - j) S := by
  have hS' := measurable_proj X hj κ hS
  set c := MeasurableEquiv.curry Tau (Fin j × Fin (r - j)) ℂ with hc
  set φ : (Tau → Fin j × Fin (r - j) → ℂ) → ℝ≥0∞ := (c.symm ⁻¹' S).indicator 1 with hφ
  have hφm : Measurable φ := measurable_one.indicator (c.symm.measurable hS)
  have hDm : Measurable fun y => ENNReal.ofReal (dens (sgnMat r (r - j)) y) := (measurable_dens _).ennreal_ofReal
  have key := GlobalTheory.T.lintegral_pi_fibre_measurePreserving Tau _ _ _ (glue (idx hj)) (base (idx hj)) _ φ (GlobalTheory.T.measurePreserving_glueLowerUnitriangularBlocks _ _ _ _ (isBlockOrderedSumEquiv_trueIndex hj))
    (measurable_base _) (base_glue (isBlockOrderedSumEquiv_trueIndex hj)) hDm hφm
  have hm : Measurable fun y : Tau → Low r → ℂ => φ (fun t => base (idx hj) (y t)) *
      ∏ t, ENNReal.ofReal (dens (sgnMat r (r - j)) (y t)) :=
    (hφm.comp (measurable_pi_lambda _ fun t => (measurable_base _).comp (measurable_pi_apply t))).mul
      (Finset.measurable_prod _ fun t _ => hDm.comp (measurable_pi_apply t))
  rw [← (GlobalTheory.T.measurePreserving_flagFibreChartCoordinates E r X Tau κ).lintegral_comp hm,
    ← (measurePreserving_curry Tau (Fin j × Fin (r - j))).lintegral_comp_emb c.measurableEmbedding] at key
  rw [muF, muD, withDensity_apply _ hS', withDensity_apply _ hS, Measure.restrict_restrict hS',
    Measure.restrict_restrict hS, Set.inter_eq_left.2 hD,
    inter_OmF X hj κ hp hD, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_indicator hS', ← lintegral_indicator hS]
  refine Eq.trans (lintegral_congr fun z => ?_) (key.trans (lintegral_congr fun v => ?_))
  · have e : c.symm (fun t => base (idx hj) (coords X κ z t)) = proj X hj κ z :=
      funext fun s => (proj_eq X hj κ z s.1 s.2).symm
    by_cases h : proj X hj κ z ∈ S
    · rw [Set.indicator_of_mem (show z ∈ proj X hj κ ⁻¹' S from h), hφ,
        Set.indicator_of_mem (by rwa [Set.mem_preimage, e]), Pi.one_apply, one_mul, densF_eq X κ, hp,
        ENNReal.ofReal_prod_of_nonneg fun _ _ => dens_nonneg _ _]
    · rw [Set.indicator_of_notMem (show z ∉ proj X hj κ ⁻¹' S from h), hφ,
        Set.indicator_of_notMem (by rwa [Set.mem_preimage, e]), zero_mul]
  · by_cases h : v ∈ S
    · rw [Set.indicator_of_mem h, hφ, Set.indicator_of_mem (show c v ∈ c.symm ⁻¹' S from h), Pi.one_apply, one_mul]
      have hc0 : 0 < flagConst j * flagConst (r - j) := mul_pos (flagConst_pos _) (flagConst_pos _)
      have hv : ∀ t, toMat (c v t) ∈ hcDom j (r - j) := hD h
      have hpos : ∀ t, 0 ≤ (hQ (toMat (c v t))).det.re ^ (-((j + (r - j) : ℕ) : ℤ)) := fun t =>
        zpow_nonneg (Complex.pos_iff.1 (PosDef.det_pos (hv t))).1.le _
      rw [Finset.prod_congr rfl fun t _ => GlobalTheory.T.lintegral_flagDensity_fibre_boundedDomain r j (r - j) (idx hj) (isBlockOrderedSumEquiv_trueIndex hj) (sgnMat r (r - j))
        (reindex_sgn hj) (c v t) (hv t), ← ENNReal.ofReal_prod_of_nonneg fun t _ => div_nonneg (hpos t) hc0.le,
        ← ENNReal.ofReal_mul (by positivity), Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
        div_eq_inv_mul, inv_pow]
      rfl
    · rw [Set.indicator_of_notMem h, hφ, Set.indicator_of_notMem (show c v ∉ c.symm ⁻¹' S from h), zero_mul]

theorem covol_eq_muD : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : Data E r) (hj : j ≤ r)
    (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ F, IsFD (gammaU X hj κ) F →
    muD Tau j (r - j) F < ⊤ ∧
      covol X = grassConst j (r - j) ^ Fintype.card Tau * (muD Tau j (r - j) F).toReal := by
  intro E _ _ _ r j X hj Tau _ κ hp F hF
  obtain ⟨F', hm, hsub, h0, hfs⟩ := GlobalTheory.T.isFundamentalSet_chart_preimage_fundamentalDomain E r j X hj Tau κ hp (GlobalTheory.T.domain_point_stabilizer_trivial E r j X hj Tau κ hp)
    (fun N hN hD h => by rw [muF_preimage X hj κ hp hN hD, h, mul_zero]) F hF
  have hD := hsub.trans hF.2.1
  rw [inter_OmF X hj κ hp hD] at hfs
  obtain ⟨h1, h2⟩ := covol_eq X (isOrth_x0F X) hfs
  have e : muD Tau j (r - j) F' = muD Tau j (r - j) F := (measure_eq_measure_of_null_diff hsub h0)
  have hc0 : 0 < flagConst j * flagConst (r - j) := mul_pos (flagConst_pos _) (flagConst_pos _)
  rw [muF_preimage X hj κ hp hm hD, e] at h1 h2
  refine ⟨?_, ?_⟩
  · refine lt_top_iff_ne_top.2 fun h => h1.ne ?_
    rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']
  · have e1 : flagConst r = grassConst j (r - j) * (flagConst j * flagConst (r - j)) := by
      rw [← mul_assoc, ← flagConst_add, Nat.add_sub_cancel' hj]
    have e2 : X.Ψ.card = Fintype.card Tau := by rw [Fintype.card_congr κ, Fintype.card_coe]
    rw [h2, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), e1, e2, mul_pow, inv_pow]
    field_simp

end GlobalTheory.FlagFibre
end
end
