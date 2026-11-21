import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnitaryGroupTuplesTopologicalFacts
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarOfInvariantRadonOnCosets
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FibreFamilyUnique
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.OrthogonalInvarianceOfStableRankOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramFibreMeasureFreeTupleNeZeroFinite
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardFrameGramDetNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVSec
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfSS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuadBaseChangeIsFieldOrSplit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions

section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localUnitaryGroup_tuples_topological_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), IsTopologicalRing (Fv F v ⊗[F] E) ∧ LocallyCompactSpace (Fv F v ⊗[F] E) ∧ T2Space (Fv F v ⊗[F] E) ∧ SecondCountableTopology (Fv F v ⊗[F] E) ∧ IsTopologicalGroup (HA (Fv F v) σ J) ∧ LocallyCompactSpace (HA (Fv F v) σ J) ∧ T2Space (HA (Fv F v) σ J) ∧ SecondCountableTopology (HA (Fv F v) σ J) ∧ ∀ a : ℕ, IsOpen {X : Fin a → Fin n → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ∧ Continuous (fun p : HA (Fv F v) σ J × (Fin a → Fin n → Fv F v ⊗[F] E) => p.1 • p.2) := by
  first | exact @GlobalTheory.LocalUnitaryTop.top_facts | exact GlobalTheory.LocalUnitaryTop.top_facts | (intros; apply GlobalTheory.LocalUnitaryTop.top_facts <;> assumption)
end

section
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.WeilOrbit

theorem measurableEmbedding_of_sigmaCompact {Y X : Type} [TopologicalSpace Y] [T2Space Y]
    [SigmaCompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] {φ : Y → X} (hc : Continuous φ)
    (hi : Function.Injective φ) : MeasurableEmbedding φ := by
  refine ⟨hi, hc.measurable, fun s hs => ?_⟩
  have h : φ '' s = ⋃ n, (fun y : compactCovering Y n => φ y) '' (Subtype.val ⁻¹' s) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨n, hn⟩ := exists_mem_compactCovering y
      exact ⟨n, ⟨y, hn⟩, hy, rfl⟩
    · rintro ⟨n, y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [h]
  refine MeasurableSet.iUnion fun n => ?_
  haveI : CompactSpace (compactCovering Y n) :=
    isCompact_iff_compactSpace.mp (isCompact_compactCovering Y n)
  have hce : Topology.IsClosedEmbedding (fun y : compactCovering Y n => φ y) :=
    (hc.comp continuous_subtype_val).isClosedEmbedding (hi.comp Subtype.val_injective)
  exact hce.measurableEmbedding.measurableSet_image.mpr (measurable_subtype_coe hs)

theorem exists_compact_cover {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] (H : Subgroup G) {C : Set (G ⧸ H)} (hC : IsCompact C) :
    ∃ K : Set G, IsCompact K ∧ C ⊆ (QuotientGroup.mk : G → G ⧸ H) '' K := by
  refine hC.induction_on (p := fun C => ∃ K : Set G, IsCompact K ∧
    C ⊆ (QuotientGroup.mk : G → G ⧸ H) '' K) ⟨∅, isCompact_empty, by simp⟩ ?_ ?_ ?_
  · rintro s t hst ⟨K, hK, h⟩
    exact ⟨K, hK, hst.trans h⟩
  · rintro s t ⟨K, hK, h⟩ ⟨L, hL, h'⟩
    exact ⟨K ∪ L, hK.union hL, by rw [Set.image_union]; exact Set.union_subset_union h h'⟩
  · intro q _
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨K, hK, hg⟩ := exists_compact_mem_nhds g
      exact ⟨_, mem_nhdsWithin_of_mem_nhds (QuotientGroup.isOpenMap_coe.image_mem_nhds hg),
        K, hK, subset_rfl⟩

def orbitMap (G : Type) {X : Type} [Group G] [MulAction G X] (x0 : X) :
    G ⧸ MulAction.stabilizer G x0 → X :=
  MulAction.ofQuotientStabilizer G x0

theorem orbitMap_mk {G X : Type} [Group G] [MulAction G X] (x0 : X) (g : G) :
    orbitMap G x0 (g : G ⧸ MulAction.stabilizer G x0) = g • x0 := rfl

theorem orbitMap_injective {G X : Type} [Group G] [MulAction G X] (x0 : X) :
    Function.Injective (orbitMap G x0) :=
  MulAction.injective_ofQuotientStabilizer G x0

theorem weil_formula : ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [MulAction G X] [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (x0 : X), Continuous (fun p : G × X => p.1 • p.2) → ∀ (μ : Measure G), μ.IsHaarMeasure → ∀ (ν : Measure X), ν {y | ¬ ∃ g : G, g • x0 = y} = 0 → (∀ (g : G) (s : Set X), MeasurableSet s → ν ((fun y => g • y) ⁻¹' s) = ν s) → (∀ K : Set G, IsCompact K → ν ((fun g => g • x0) '' K) < ⊤) → ν ≠ 0 → ∃ μ' : Measure (MulAction.stabilizer G x0), μ'.IsHaarMeasure ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : X → G, (∀ y, (∃ g : G, g • x0 = y) → s y • x0 = y) → ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h', f (s y * (h' : G)) ∂μ' ∂ν := by
  intro G X _ _ _ _ _ _ _ _ _ _ _ _ _ _ x0 hcont μ hμ ν hν0 hinv hfin hne
  set H := MulAction.stabilizer G x0 with hHdef
  have hc0 : Continuous (fun g : G => g • x0) :=
    hcont.comp (continuous_id.prodMk continuous_const)
  have hH : IsClosed (H : Set G) := isClosed_eq hc0 continuous_const
  haveI := hH
  letI : MeasurableSpace (G ⧸ H) := borel _
  haveI : BorelSpace (G ⧸ H) := ⟨rfl⟩
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SigmaCompactSpace (G ⧸ H) := inferInstance
  let φ : G ⧸ H → X := orbitMap G x0
  have hφc : Continuous φ := (QuotientGroup.isQuotientMap_mk H).continuous_iff.mpr hc0
  have hφ : MeasurableEmbedding φ :=
    measurableEmbedding_of_sigmaCompact hφc (orbitMap_injective x0)
  have hrange : Set.range φ = {y | ∃ g : G, g • x0 = y} := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H g => exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨(g : G ⧸ H), rfl⟩
  have hae : ∀ᵐ y ∂ν, y ∈ Set.range φ := by
    rw [hrange]
    exact hν0
  have hmap : (ν.comap φ).map φ = ν := by
    rw [hφ.map_comap, Measure.restrict_eq_self_of_ae_mem hae]
  have hrad : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.IsInvariantRadon H (ν.comap φ) := by
    refine ⟨fun h0 => hne ?_, ⟨fun C hC => ?_⟩, ⟨fun g s hs => ?_⟩⟩
    · rw [← hmap, h0, Measure.map_zero]
    · obtain ⟨K, hK, hCK⟩ := exists_compact_cover H hC
      rw [hφ.comap_apply]
      refine (measure_mono ?_).trans_lt (hfin K hK)
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨g, hg, rfl⟩ := hCK hq
      exact ⟨g, hg, rfl⟩
    · rw [hφ.comap_apply, hφ.comap_apply, ← hinv g (φ '' s) (hφ.measurableSet_image.mpr hs)]
      congr 1
      have heq : ∀ (a : G) (q : G ⧸ H), φ (a • q) = a • φ q := by
        intro a q
        induction q using QuotientGroup.induction_on with
        | H b => exact mul_smul a b x0
      ext y
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨g • q, hq, heq g q⟩
      · rintro ⟨q, hq, h⟩
        refine ⟨g⁻¹ • q, by simpa using hq, ?_⟩
        rw [heq, h, inv_smul_smul]
  let ν0 : Measure H := Measure.haar
  obtain ⟨dg, ⟨hdg, hq⟩, -⟩ :=
    GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon G H hH ν0 _ hrad
  let c := Measure.haarScalarFactor μ dg
  have hc : μ = c • dg := Measure.isMulLeftInvariant_eq_smul μ dg
  have hcpos : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure μ dg).ne'
  refine ⟨c • ν0, Measure.IsHaarMeasure.nnreal_smul ν0 hcpos, fun f hf s hs => ?_⟩
  have h1 : ∫⁻ y, ∫⁻ h' : H, f (s y * (h' : G)) ∂ν0 ∂ν = ∫⁻ g, f g ∂dg := by
    rw [(hq f hf).2]
    conv_lhs => rw [← hmap]
    rw [hφ.lintegral_map]
    refine lintegral_congr fun q => ?_
    rw [← GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral_mk H ν0 f]
    congr 1
    apply orbitMap_injective x0
    rw [orbitMap_mk]
    exact hs _ (by
      have : φ q ∈ Set.range φ := ⟨q, rfl⟩
      rwa [hrange] at this)
  rw [hc]
  simp only [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, h1]

end GlobalTheory.WeilOrbit
end

section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_integration_formula_orbit : ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [MulAction G X] [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (x0 : X), Continuous (fun p : G × X => p.1 • p.2) → ∀ (μ : Measure G), μ.IsHaarMeasure → ∀ (ν : Measure X), ν {y | ¬ ∃ g : G, g • x0 = y} = 0 → (∀ (g : G) (s : Set X), MeasurableSet s → ν ((fun y => g • y) ⁻¹' s) = ν s) → (∀ K : Set G, IsCompact K → ν ((fun g => g • x0) '' K) < ⊤) → ν ≠ 0 → ∃ μ' : Measure (MulAction.stabilizer G x0), μ'.IsHaarMeasure ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : X → G, (∀ y, (∃ g : G, g • x0 = y) → s y • x0 = y) → ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h', f (s y * (h' : G)) ∂μ' ∂ν := by
  first | exact @GlobalTheory.WeilOrbit.weil_formula | exact GlobalTheory.WeilOrbit.weil_formula | (intros; apply GlobalTheory.WeilOrbit.weil_formula <;> assumption)
end

section
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.LocalUnitaryHaar

open PI.VolSemiDirect.W.Cj Measure
open scoped NNReal Matrix

theorem stableRankOne_field (K : Type) [Field K] : HasStableRangeOne K := by
  intro a b x y h
  by_cases ha : a = 0
  · refine ⟨1, ?_⟩
    subst ha
    have hb : b ≠ 0 := by
      rintro rfl
      simp at h
    simpa using isUnit_iff_ne_zero.2 hb
  · exact ⟨0, by simpa using isUnit_iff_ne_zero.2 ha⟩

theorem map_mulVec_eq_of_preserves_form {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A]
    [BorelSpace A] (hA : HasStableRangeOne A) (k : ℕ) (G X : Matrix (Fin k) (Fin k) A)
    (hG : IsUnit G.det) (hXG : X.transpose * G * X = G)
    (μ : Measure (Fin k → A)) [μ.IsAddHaarMeasure] : μ.map X.mulVec = μ := by
  have hd := congrArg Matrix.det hXG
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  have hdd : X.det * X.det = 1 := by
    have : (X.det * X.det) * G.det = 1 * G.det := by
      calc (X.det * X.det) * G.det = X.det * G.det * X.det := by ring
        _ = 1 * G.det := by rw [hd, one_mul]
    exact hG.mul_left_inj.1 this
  have hX : IsUnit X.det := ⟨⟨X.det, X.det, hdd, hdd⟩, rfl⟩
  let Xu : GL (Fin k) A := Matrix.nonsingInvUnit X hX
  let Gu : GL (Fin k) A := Matrix.nonsingInvUnit G hG
  have hrel : trG Xu * Gu * Xu = Gu := by
    ext1
    exact hXG
  have hm := congrArg modM hrel
  rw [modM_mul, modM_mul, modM_tr_of_mem transvection_preserves_haar Xu (gl_generated_transvections_diag A hA k Xu)] at hm
  have hpos : 0 < modM Gu := addEquivAddHaarChar_pos (phi Gu)
  have hsq : modM Xu * modM Xu = 1 := by
    have : (modM Xu * modM Xu) * modM Gu = 1 * modM Gu := by
      calc (modM Xu * modM Xu) * modM Gu = modM Xu * modM Gu * modM Xu := by ring
        _ = 1 * modM Gu := by rw [hm, one_mul]
    exact mul_right_cancel₀ hpos.ne' this
  have hmod := nnreal_eq_one_of_mul_self hsq
  have e := map_phi_of_modM Xu hmod μ
  have e2 : (phi Xu : (Fin k → A) → (Fin k → A)) = Matrix.mulVec X := by
    funext v
    rfl
  rw [e2] at e
  exact e

theorem map_lin_eq_of_stableRankOne (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    [MeasurableSpace R] [BorelSpace R] (hR1 : HasStableRangeOne R) (g : HA R σ J)
    (μ : Measure (Fin M → R ⊗[F] E)) [μ.IsAddHaarMeasure] :
    μ.map (lin R σ J g) = μ := by
  classical
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hCM.2.2.1
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  obtain ⟨eh⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) R
  haveI : LocallyCompactSpace (R ⊗[F] E) := eh.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (R ⊗[F] E) := eh.secondCountableTopology
  haveI : T2Space (R ⊗[F] E) := eh.isEmbedding.t2Space
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  set k := Fintype.card (Σ _ : Fin M, Fin (Module.finrank F E))
  set b := bV F E M
  set bR := bVR F E M R
  set e : (Fin M → R ⊗[F] E) ≃ₗ[R] (Fin k → R) := bR.equivFun
  have c1 : Continuous e.toLinearMap := IsModuleTopology.continuous_of_linearMap (R := R) _
  have c2 : Continuous e.symm.toLinearMap :=
    IsModuleTopology.continuous_of_linearMap (R := R) _
  let ec : (Fin M → R ⊗[F] E) ≃ₜ+ (Fin k → R) :=
    { e.toAddEquiv with
      continuous_toFun := by simpa using c1
      continuous_invFun := by simpa using c2 }
  have hec : ∀ u, ec u = e u := fun _ => rfl
  have hecs : ∀ x, ec.symm x = e.symm x := fun _ => rfl
  set μ' := μ.map ec
  have hμ' : μ'.IsAddHaarMeasure := ec.isAddHaarMeasure_map μ
  let L : (Fin k → R) →ₗ[R] (Fin k → R) :=
    e.toLinearMap ∘ₗ ((lin R σ J g).restrictScalars R) ∘ₗ e.symm.toLinearMap
  set X := LinearMap.toMatrix' L
  have hX : ∀ x, X.mulVec x = e (lin R σ J g (e.symm x)) := fun x =>
    LinearMap.toMatrix'_mulVec L x
  set G0 : Matrix (Fin k) (Fin k) F := Matrix.of fun i j => Algebra.trace F E (hE σ J (b i) (b j))
  set G := G0.map (algebraMap F R)
  have hGu : IsUnit G.det := by
    have hd : G.det = algebraMap F R G0.det := by
      rw [RingHom.map_det]
      rfl
    rw [hd]
    exact (isUnit_iff_ne_zero.2 (trace_gram_nondegenerate F E σ hCM M J hJ k b)).map _
  have hBG : ∀ i j, Bf σ J (bR i) (bR j) = G i j := by
    intro i j
    rw [bVR_apply, bVR_apply, Bf, trace_basis_holds F E R σ M J]
    rfl
  have key : ∀ x y : Fin k → R, Bf σ J (e.symm x) (e.symm y) = x ⬝ᵥ (G *ᵥ y) := by
    intro x y
    rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply, Bf_expand]
    simp only [hBG, dotProduct, Matrix.mulVec, Finset.mul_sum]
    rfl
  have e1 : ∀ u w : Fin k → R, u ⬝ᵥ ((X.transpose * G * X) *ᵥ w) = u ⬝ᵥ (G *ᵥ w) := by
    intro u w
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose, ← key, hX, hX, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply, Bf_lin, key]
  have hXG : X.transpose * G * X = G := by
    ext i j
    simpa using e1 (Pi.single i 1) (Pi.single j 1)
  have hinv := map_mulVec_eq_of_preserves_form hR1 k G X hGu hXG μ'
  have hlin : (lin R σ J g : (Fin M → R ⊗[F] E) → (Fin M → R ⊗[F] E)) =
      ec.symm ∘ X.mulVec ∘ ec := by
    funext u
    simp only [Function.comp_apply, hec, hecs, hX, LinearEquiv.symm_apply_apply]
  have mec : Measurable ec := ec.continuous.measurable
  have mecs : Measurable ec.symm := ec.symm.continuous.measurable
  have mX : Measurable X.mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  rw [hlin, ← Measure.map_map mecs (mX.comp mec), ← Measure.map_map mX mec, hinv,
    Measure.map_map mecs mec]
  have : (ec.symm ∘ ec : (Fin M → R ⊗[F] E) → _) = id := by
    funext u
    simp
  rw [this, Measure.map_id]

theorem haar_tuple_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (a : ℕ) (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)), μ.IsAddHaarMeasure → ∀ g : HA (Fv F v) σ J, μ.map (fun X => g • X) = μ := by
  intro F E _ _ _ _ _ σ hCM n J hJ v a μ hμ g
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hCM.2.2.1
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  obtain ⟨eh⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Fv F v)
  haveI : LocallyCompactSpace (Fv F v ⊗[F] E) := eh.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Fv F v ⊗[F] E) := eh.secondCountableTopology
  haveI : T2Space (Fv F v ⊗[F] E) := eh.isEmbedding.t2Space
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  let ν : Measure (Fin n → Fv F v ⊗[F] E) := addHaar
  have hmeas : Measurable (lin (Fv F v) σ J g : (Fin n → Fv F v ⊗[F] E) → _) :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hν : ∀ _ : Fin a, MeasurePreserving (lin (Fv F v) σ J g : (Fin n → Fv F v ⊗[F] E) → _) ν ν :=
    fun _ => ⟨hmeas, map_lin_eq_of_stableRankOne F E σ hCM n J hJ (Fv F v) (stableRankOne_field _) g ν⟩
  have hpi := measurePreserving_pi (fun _ : Fin a => ν) (fun _ => ν) hν
  have e1 : (fun X : Fin a → Fin n → Fv F v ⊗[F] E => g • X) =
      fun X i => lin (Fv F v) σ J g (X i) := rfl
  rw [isAddLeftInvariant_eq_smul μ (Measure.pi fun _ : Fin a => ν), Measure.map_smul, e1,
    hpi.map_eq]

end GlobalTheory.LocalUnitaryHaar
end
end

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localUnitaryGroup_tuple_haar_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (a : ℕ) (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)), μ.IsAddHaarMeasure → ∀ g : HA (Fv F v) σ J, μ.map (fun X => g • X) = μ := by
  atlas_forward_decl GlobalTheory.LocalUnitaryHaar.haar_tuple_invariant
end

section
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalFibreInvariant

theorem fibre_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ (S : HermR (Fv F v) σ a) (g : HA (Fv F v) σ J), (fib S).map (fun X => g • X) = fib S := by
  intro F E _ _ _ _ _ σ hCM n J hJ v a μ ν hμ hν fib hfib S g
  obtain ⟨-, -, -, h4, -, -, -, -, ha⟩ := GlobalTheory.LocalUnitaryTop.top_facts F E σ hCM n J hJ v
  obtain ⟨-, hact⟩ := ha a
  haveI := h4
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have hc : ∀ k : HA (Fv F v) σ J,
      Continuous (fun X : Fin a → Fin n → Fv F v ⊗[F] E => k • X) :=
    fun k => hact.comp (Continuous.prodMk continuous_const continuous_id)
  let T : (Fin a → Fin n → Fv F v ⊗[F] E) ≃ₜ (Fin a → Fin n → Fv F v ⊗[F] E) :=
    { toFun := fun X => g • X
      invFun := fun X => g⁻¹ • X
      left_inv := fun X => inv_smul_smul g X
      right_inv := fun X => smul_inv_smul g X
      continuous_toFun := hc g
      continuous_invFun := hc g⁻¹ }
  let Tm := T.toMeasurableEquiv
  have hTm : ∀ X, Tm X = g • X := fun X => rfl
  have hgram : ∀ X : Fin a → Fin n → Fv F v ⊗[F] E,
      gramR (Fv F v) σ J (g • X) = gramR (Fv F v) σ J X := by
    intro X
    funext i j
    exact hR_lin g (X i) (X j)
  have hli : ∀ (k : HA (Fv F v) σ J) (X : Fin a → Fin n → Fv F v ⊗[F] E),
      LinearIndependent (Fv F v ⊗[F] E) X → LinearIndependent (Fv F v ⊗[F] E) (k • X) := by
    intro k X hX
    have hinj : Function.Injective (lin (Fv F v) σ J k) :=
      Function.LeftInverse.injective (g := lin (Fv F v) σ J k⁻¹) (fun x => lin_inv_lin (g := k) (x := x))
    exact hX.map' (lin (Fv F v) σ J k) (LinearMap.ker_eq_bot.mpr hinj)
  have hpre : ∀ b : HermR (Fv F v) σ a,
      Tm ⁻¹' (gramR (Fv F v) σ J ⁻¹' {Subtype.val b} ∩ {X | LinearIndependent (Fv F v ⊗[F] E) X}) =
        gramR (Fv F v) σ J ⁻¹' {Subtype.val b} ∩ {X | LinearIndependent (Fv F v ⊗[F] E) X} := by
    intro b
    ext X
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, hTm, hgram]
    refine and_congr_right fun _ => ⟨fun h => ?_, hli g X⟩
    have := hli g⁻¹ _ h
    rwa [inv_smul_smul] at this
  have hU : Tm ⁻¹' {X | LinearIndependent (Fv F v ⊗[F] E) X} =
      {X | LinearIndependent (Fv F v ⊗[F] E) X} := by
    ext X
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hTm]
    refine ⟨fun h => ?_, hli g X⟩
    have := hli g⁻¹ _ h
    rwa [inv_smul_smul] at this
  have hμT : μ.map Tm = μ := GlobalTheory.T.localUnitaryGroup_tuple_haar_invariant F E σ hCM n J hJ v a μ hμ g
  let fib' : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E) := fun b => (fib b).map Tm
  have hfib' : IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib' := by
    refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩
    · show (fib b).map Tm _ = 0
      rw [Tm.map_apply, Set.preimage_compl, hpre]
      exact hfib.1 b
    · have e1 : ∀ b, ∫⁻ x, φ x ∂(fib' b) = ∫⁻ x, φ (Tm x) ∂(fib b) := fun b =>
        lintegral_map_equiv φ Tm (μ := fib b)
      simp only [e1]
      rw [← hfib.2.1 (fun x => φ (Tm x)) (hφ.comp Tm.measurable)]
      conv_lhs => rw [← hμT]
      rw [Tm.restrict_map, lintegral_map_equiv, hU]
    · have h3 := hfib.2.2 (φ ∘ Tm) (hφc.comp T.continuous) (hφs.comp_homeomorph T) (by
        show tsupport (φ ∘ T) ⊆ _
        rw [tsupport_comp_eq_preimage φ T]
        intro X hX
        have : Tm X ∈ {X | LinearIndependent (Fv F v ⊗[F] E) X} := hφU hX
        rw [← Set.mem_preimage, hU] at this
        exact this)
      refine ⟨fun b hb => (integrable_map_equiv Tm φ).mpr (h3.1 b hb), ?_⟩
      refine h3.2.congr fun b _ => ?_
      exact MeasureTheory.integral_map_equiv Tm φ
  have hu := GlobalTheory.LocalFibreUnique.fibre_family_unique F E σ hCM n J hJ v a μ ν hμ hν fib hfib fib' hfib'
  show (fib S).map Tm = fib S
  exact (congrFun hu S).symm

end GlobalTheory.LocalFibreInvariant
end

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramMap_fibreMeasure_localUnitary_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ (S : HermR (Fv F v) σ a) (g : HA (Fv F v) σ J), (fib S).map (fun X => g • X) = fib S := by
  atlas_forward_decl GlobalTheory.LocalFibreInvariant.fibre_invariant
end

section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramFibreMeasure_freeTuple_ne_zero_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ (x : Fin a → Fin n → Fv F v ⊗[F] E) (S : HermR (Fv F v) σ a), LinearIndependent (Fv F v ⊗[F] E) x → gramR (Fv F v) σ J x = (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) → fib S ≠ 0 ∧ ∀ K : Set (Fin a → Fin n → Fv F v ⊗[F] E), IsCompact K → K ⊆ {X | LinearIndependent (Fv F v ⊗[F] E) X} → fib S K < ⊤ := by
  first | exact @GlobalTheory.LocalFibreNonzero.fibre_nonzero_finite | exact GlobalTheory.LocalFibreNonzero.fibre_nonzero_finite | (intros; apply GlobalTheory.LocalFibreNonzero.fibre_nonzero_finite <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardFrame_gram_det_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → (gramE σ J (tupH P)).det ≠ 0 ∧ (∀ i j, σ (gramE σ J (tupH P) j i) = gramE σ J (tupH P) i j) ∧ (∀ i j, σ (gramE σ J (F0 P) j i) = gramE σ J (F0 P) i j) ∧ (∀ i j, gramE σ J (F0 P) i j = if i = Fin.last r ∧ j = Fin.last r then algebraMap F E (-T) else 0) ∧ ∀ v : HeightOneSpectrum (𝓞 F), LinearIndependent (Fv F v ⊗[F] E) (ratTup (F := F) (Fv F v) (F0 P)) := by
  first | exact @GlobalTheory.FrameGram.std_frame_gram | exact GlobalTheory.FrameGram.std_frame_gram | (intros; apply GlobalTheory.FrameGram.std_frame_gram <;> assumption)
end

section
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.FrameExtend

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem hR_sub_sum_right {m : ℕ} (x w : Fin n → R ⊗[F] E) (c : Fin m → R ⊗[F] E)
    (u : Fin m → Fin n → R ⊗[F] E) :
    hR R σ J x (w - ∑ a, c a • u a) = hR R σ J x w - ∑ a, c a * hR R σ J x (u a) := by
  simp only [hR, Formalism.UG.hform, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end Alg

open GlobalTheory.FrameGram in

theorem extend_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ y : Fin (r + 1) → Fin n → Fv F v ⊗[F] E, LinearIndependent (Fv F v ⊗[F] E) y → gramR (Fv F v) σ J y = (gramE σ J (F0 P)).map (inclR (Fv F v)) → ∃ f : Fin r → Fin n → Fv F v ⊗[F] E, gramR (Fv F v) σ J (Fin.append y f) = (gramE σ J (tupH P)).map (inclR (Fv F v)) := by
  intro F E _ _ _ _ _ σ hσ n J hJ v r P T hP y hy hgram
  have hinv : ∀ x, σ (σ x) = x := conj_invol hσ
  obtain ⟨_, hGh, _, hG0, _⟩ := std_frame_gram F E σ hσ n J hJ r P T hP
  have hPs := hP
  obtain ⟨_, hff0, hef, _, hfz, _, _⟩ := hPs
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsArtinianRing (Fv F v ⊗[F] E) := IsArtinianRing.of_finite (Fv F v) (Fv F v ⊗[F] E)
  have : IsReduced (Fv F v ⊗[F] E) := PI.VolStabS.isReduced_tens_field F E (Fv F v)
  have : IsSemisimpleRing (Fv F v ⊗[F] E) := IsArtinianRing.isSemisimpleRing_of_isReduced _
  let s := sigR (Fv F v) σ
  have hsw : ∀ x w, s (hR (Fv F v) σ J x w) = hR (Fv F v) σ J w x :=
    PI.VolStabS.hR_herm (Fv F v) σ hinv J hJ.1
  have hss : ∀ x, s (s x) = x := PI.VolStabS.sigR_invol (Fv F v) σ hinv

  let Z : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun i => Matrix.vecMul (fun l => s (y i l)) (JR (F := F) (Fv F v) J)
  have hZh : ∀ i w, hR (Fv F v) σ J (y i) w = ∑ k, Z i k * w k := by
    intro i w
    simp only [hR, Formalism.UG.hform, Z, Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hZ : LinearIndependent (Fv F v ⊗[F] E) Z := by
    have hJu : IsUnit (JR (F := F) (Fv F v) J).det := by
      have e := RingHom.map_det (inclR (F := F) (E := E) (Fv F v)) J
      rw [RingHom.mapMatrix_apply] at e
      show IsUnit (J.map (inclR (Fv F v))).det
      rw [← e]
      exact (isUnit_iff_ne_zero.2 hJ.2).map _
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    let w : Fin n → Fv F v ⊗[F] E := fun l => ∑ i, g i * s (y i l)
    have hv0 : Matrix.vecMul w (JR (F := F) (Fv F v) J) = 0 := by
      funext j
      have := congrFun hg j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Z, Matrix.vecMul, dotProduct,
        Finset.mul_sum, Pi.zero_apply] at this
      simp only [Matrix.vecMul, dotProduct, w, Finset.sum_mul, Pi.zero_apply]
      rw [Finset.sum_comm]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
    have hv : w = 0 := by
      have := congrArg (fun u => Matrix.vecMul u (JR (F := F) (Fv F v) J)⁻¹) hv0
      simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJu, Matrix.vecMul_one,
        Matrix.zero_vecMul] at this
      exact this
    have hX0 : ∑ i, s (g i) • y i = 0 := by
      funext l
      have := congrArg s (congrFun hv l)
      simp only [w, map_sum, map_mul, hss, Pi.zero_apply, map_zero] at this
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    have := Fintype.linearIndependent_iff.1 hy _ hX0 i
    have e2 := congrArg s this
    simp only [hss, map_zero] at e2
    exact e2
  obtain ⟨q, hq⟩ := PI.VolStabS.exists_leftInv_of_linIndep Z hZ

  let f' : Fin r → Fin n → Fv F v ⊗[F] E := fun b k => q k b.castSucc
  have hyf' : ∀ i b, hR (Fv F v) σ J (y i) (f' b) = if i = b.castSucc then 1 else 0 := by
    intro i b
    rw [hZh]
    exact hq i b.castSucc
  have hyy : ∀ i j, hR (Fv F v) σ J (y i) (y j) =
      inclR (Fv F v) (if i = Fin.last r ∧ j = Fin.last r then algebraMap F E (-T) else 0) := by
    intro i j
    have := congrFun (congrFun hgram i) j
    simp only [Matrix.map_apply, hG0] at this
    exact this
  have hyy0 : ∀ i (a : Fin r), hR (Fv F v) σ J (y i) (y a.castSucc) = 0 := by
    intro i a
    rw [hyy]
    simp [Fin.castSucc_ne_last]
  let h2 : Fv F v ⊗[F] E := algebraMap F (Fv F v ⊗[F] E) (1 / 2)
  have hh : h2 + h2 = 1 := by
    rw [← map_add, show (1 / 2 : F) + 1 / 2 = 1 by norm_num, map_one]
  have hsh : s h2 = h2 := (Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) σ).commutes _
  let c : Fin r → Fin r → Fv F v ⊗[F] E := fun a b => h2 * hR (Fv F v) σ J (f' a) (f' b)
  let f : Fin r → Fin n → Fv F v ⊗[F] E := fun b => f' b - ∑ a, c a b • y a.castSucc
  have hyf : ∀ i b, hR (Fv F v) σ J (y i) (f b) = if i = b.castSucc then 1 else 0 := by
    intro i b
    simp only [f]
    rw [GlobalTheory.FrameExtend.hR_sub_sum_right, hyf']
    simp [hyy0]
  have hfy : ∀ b i, hR (Fv F v) σ J (f b) (y i) = if i = b.castSucc then 1 else 0 := by
    intro b i
    rw [← hsw, hyf]
    split_ifs <;> simp
  have hf'y : ∀ b (d : Fin r), hR (Fv F v) σ J (f' b) (y d.castSucc) = if d = b then 1 else 0 := by
    intro b d
    rw [← hsw, hyf']
    split_ifs with h1 h2 h2 <;> simp_all [Fin.castSucc_inj]
  have hff : ∀ a b, hR (Fv F v) σ J (f a) (f b) = 0 := by
    intro a b
    have e1 : hR (Fv F v) σ J (f a) (f b) = hR (Fv F v) σ J (f a) (f' b) - c a b := by
      simp only [f]
      rw [GlobalTheory.FrameExtend.hR_sub_sum_right]
      congr 1
      have := fun d => hfy a (Fin.castSucc d)
      simp only [f] at this
      simp [this, Fin.castSucc_inj]
    have e2 : hR (Fv F v) σ J (f' b) (f a) = hR (Fv F v) σ J (f' b) (f' a) - c b a := by
      simp only [f]
      rw [GlobalTheory.FrameExtend.hR_sub_sum_right]
      congr 1
      simp [hf'y]
    have e3 : hR (Fv F v) σ J (f a) (f' b) = hR (Fv F v) σ J (f' a) (f' b) - h2 * hR (Fv F v) σ J (f' a) (f' b) := by
      rw [← hsw, e2, map_sub, hsw]
      simp only [c, map_mul, hsh, hsw]
    rw [e1, e3]
    simp only [c]
    linear_combination (-(hR (Fv F v) σ J (f' a) (f' b))) * hh
  refine ⟨f, ?_⟩
  have hTL : ∀ i (b : Fin r), gramE σ J (tupH P) (Fin.castAdd r i) (Fin.natAdd (r + 1) b) =
      if i = b.castSucc then 1 else 0 := by
    intro i b
    simp only [gramE, tupH, Fin.append_left, Fin.append_right, F0]
    refine Fin.lastCases ?_ (fun a => ?_) i
    · rw [Fin.snoc_last, ← hE_swap hinv hJ.1 P.z (P.f b), hfz, map_zero]
      exact (if_neg (Fin.castSucc_ne_last b).symm).symm
    · rw [Fin.snoc_castSucc, hef]
      simp only [Fin.castSucc_inj]
  funext i j
  simp only [Matrix.map_apply]
  show hR (Fv F v) σ J (Fin.append y f i) (Fin.append y f j) = _
  refine Fin.addCases (fun i => ?_) (fun a => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun b => ?_) j
  · rw [Fin.append_left, Fin.append_left, hyy, ← hG0]
    simp [gramE, tupH, Fin.append_left]
  · rw [Fin.append_left, Fin.append_right, hyf, hTL]
    split_ifs <;> simp
  · rw [Fin.append_right, Fin.append_left, hfy, ← hGh, hTL]
    split_ifs <;> simp
  · rw [Fin.append_right, Fin.append_right, hff]
    simp [gramE, tupH, Fin.append_right, hff0]

end GlobalTheory.FrameExtend
end
end

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extend_free_tuple_gram_hermitian_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ y : Fin (r + 1) → Fin n → Fv F v ⊗[F] E, LinearIndependent (Fv F v ⊗[F] E) y → gramR (Fv F v) σ J y = (gramE σ J (F0 P)).map (inclR (Fv F v)) → ∃ f : Fin r → Fin n → Fv F v ⊗[F] E, gramR (Fv F v) σ J (Fin.append y f) = (gramE σ J (tupH P)).map (inclR (Fv F v)) := by
  atlas_forward_decl GlobalTheory.FrameExtend.extend_frame
end

section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal Matrix

namespace GlobalTheory.LocalWittND

theorem exists_gl {K S : Type} [Field K] [CommRing S] (s : S →+* S) (hs : ∀ x, s (s x) = x)
    (h2 : (2 : S) ≠ 0) (hS : IsField S ∨ ∃ φ : S ≃+* K × K, ∀ x, φ (s x) = (φ x).swap)
    {n a : ℕ} (J : Matrix (Fin n) (Fin n) S) (hJ : ∀ i j, s (J j i) = J i j) (hd : IsUnit J.det)
    (X Y : Matrix (Fin n) (Fin a) S) (hX : IsUnit (Formalism.UG.cT s X * J * X).det)
    (hXY : Formalism.UG.cT s Y * J * Y = Formalism.UG.cT s X * J * X) :
    ∃ γ : GL (Fin n) S, Formalism.UG.cT s γ.1 * J * γ.1 = J ∧ γ.1 * X = Y := by
  have key : ∀ {m : ℕ} (Z : Matrix (Fin n) (Fin m) S),
      Zᵀ * Jᵀ * Z.map s = (Formalism.UG.cT s Z * J * Z)ᵀ := by
    intro m Z
    simp only [Formalism.UG.cT, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hX' : IsUnit (Xᵀ * Jᵀ * X.map s).det := by rw [key, Matrix.det_transpose]; exact hX
  have hXY' : Yᵀ * Jᵀ * Y.map s = Xᵀ * Jᵀ * X.map s := by rw [key, key, hXY]
  have : ∃ γ : Matrix (Fin n) (Fin n) S, γᵀ * Jᵀ * γ.map s = Jᵀ ∧ γ * X = Y := by
    rcases hS with hF | ⟨φ, hφ⟩
    · letI := hF.toField
      obtain ⟨γ, h1, h3⟩ := GlobalTheory.HermWitt.exists_gl_isometry_mul_eq_of_det_ne_zero (c := s)
        h2 hs (G := Jᵀ) (fun i j => hJ i j) (X := X) (Y := Y) hX'.ne_zero hXY'
      exact ⟨γ, h1, h3⟩
    · exact GlobalTheory.HermTuple.exists_matrix_split s φ hφ Jᵀ (fun i j => hJ i j)
        (by rwa [Matrix.det_transpose]) X Y hX' hXY'
  obtain ⟨γ, h1, h3⟩ := this
  rw [key] at h1
  have h4 := Matrix.transpose_injective h1
  have hγ : IsUnit γ.det := by
    rw [← h4, Matrix.det_mul] at hd
    exact isUnit_of_mul_isUnit_right hd
  obtain ⟨G, hG⟩ := (Matrix.isUnit_iff_isUnit_det γ).2 hγ
  exact ⟨G, by rw [hG]; exact h4, by rw [hG]; exact h3⟩

theorem gram_eq {S : Type} [CommRing S] (s : S →+* S) {n a : ℕ} (J : Matrix (Fin n) (Fin n) S)
    (Z : Fin a → Fin n → S) :
    (Matrix.of fun k l => Formalism.UG.hform s J (Z k) (Z l)) =
      Formalism.UG.cT s (Matrix.of Z)ᵀ * J * (Matrix.of Z)ᵀ := by
  ext k l
  simp only [Formalism.UG.hform, Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.of_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem gramR_ratTup {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {n a : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (X : Fin a → Fin n → E) :
    gramR R σ J (ratTup (F := F) R X) = (gramE σ J X).map (inclR (F := F) R) := by
  ext k l
  simp only [gramR, gramE, hR, hE, Formalism.UG.hform, map_sum, map_mul, ratTup, JR, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 2

theorem invol_of_isCMExt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : (∀ a, σ (σ a) = a) ∧ ∃ a, σ a ≠ a := by
  obtain ⟨-, hE, -, hσ⟩ := h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  refine ⟨fun a => τ.injective (by rw [hσ, hσ, star_star]), ?_⟩
  by_contra hc
  push Not at hc
  refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := hσ τ x
  rw [hc] at this
  exact this.symm

theorem exists_smul_eq_field {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (K : Type) [Field K] [Algebra F K]
    {n a : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    (X Y : Fin a → Fin n → K ⊗[F] E) (hX : IsUnit (gramR K σ J X).det)
    (hXY : gramR K σ J Y = gramR K σ J X) : ∃ g : HA K σ J, g • X = Y := by
  obtain ⟨hi, hne⟩ := invol_of_isCMExt hcm
  have hS := (GlobalTheory.quadBaseChange_isField_or_split F E K σ hcm.2.2.1 hi hne).1
  have hg : ∀ Z : Fin a → Fin n → K ⊗[F] E, gramR K σ J Z = _ :=
    fun Z => gram_eq (sigR K σ) (JR K J) Z
  have h2 : (2 : K ⊗[F] E) ≠ 0 := by
    have : inclR (F := F) K (2 : E) ≠ 0 := by
      rw [map_ne_zero]; exact two_ne_zero
    rwa [map_ofNat] at this
  obtain ⟨γ, h1, h3⟩ := exists_gl (sigR K σ)
    (fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul k e => exact congrArg (k ⊗ₜ[F] ·) (hi e)
      | add x y hx hy => simp only [map_add, hx, hy])
    h2 hS (JR K J)
    (fun i j => by
      show (1 : K) ⊗ₜ[F] σ (J j i) = (1 : K) ⊗ₜ[F] J i j
      rw [hJ.1])
    (by
      have := (hJ.2.isUnit).map (inclR (F := F) K)
      rwa [RingHom.map_det] at this)
    (Matrix.of X)ᵀ (Matrix.of Y)ᵀ (by rw [← hg]; exact hX) (by rw [← hg, ← hg]; exact hXY)
  refine ⟨(⟨γ, h1⟩ : HR K σ J), ?_⟩
  funext k i
  exact congrFun (congrFun h3 i) k

theorem exists_smul_ratTup_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (a : ℕ) (X0 : Fin a → Fin n → E), (gramE σ J X0).det ≠ 0 → ∀ y : Fin a → Fin n → Fv F v ⊗[F] E, gramR (Fv F v) σ J y = (gramE σ J X0).map (inclR (Fv F v)) → ∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) X0 = y := by
  intro F E _ _ _ _ _ σ hcm n J hJ v a X0 hX y hy
  refine exists_smul_eq_field hcm (Fv F v) hJ _ _ ?_ (by rw [hy, gramR_ratTup])
  have := hX.isUnit.map (inclR (F := F) (Fv F v))
  rw [gramR_ratTup]
  rwa [RingHom.map_det] at this

end GlobalTheory.LocalWittND
end

section
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalWittFree

theorem exists_smul_ratTup_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ y : Fin (r + 1) → Fin n → Fv F v ⊗[F] E, LinearIndependent (Fv F v ⊗[F] E) y → gramR (Fv F v) σ J y = (gramE σ J (F0 P)).map (inclR (Fv F v)) → ∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) (F0 P) = y := by
  intro F E _ _ _ _ _ σ hcm n J hJ v r P T hP y hy hgram

  obtain ⟨f, hf⟩ := GlobalTheory.T.extend_free_tuple_gram_hermitian_frame F E σ hcm n J hJ v r P T hP y hy hgram

  have hdet := (GlobalTheory.FrameGram.std_frame_gram F E σ hcm n J hJ r P T hP).1

  obtain ⟨g, hg⟩ := GlobalTheory.LocalWittND.exists_smul_ratTup_eq F E σ hcm n J hJ v (r + 1 + r)
    (tupH P) hdet (Fin.append y f) hf
  refine ⟨g, funext fun i => ?_⟩

  have hF : (fun j => tupH P (Fin.castAdd r j)) = F0 P :=
    funext fun j => by simp [tupH, Fin.append_left]
  have h1 : (g • ratTup (F := F) (Fv F v) (tupH P)) (Fin.castAdd r i) =
      (g • ratTup (F := F) (Fv F v) (F0 P)) i := by
    rw [← hF]; rfl
  rw [← h1, hg, Fin.append_left]

end GlobalTheory.LocalWittFree
end

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smul_localWitt_free_tuple_gram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ y : Fin (r + 1) → Fin n → Fv F v ⊗[F] E, LinearIndependent (Fv F v ⊗[F] E) y → gramR (Fv F v) σ J y = (gramE σ J (F0 P)).map (inclR (Fv F v)) → ∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) (F0 P) = y := by
  atlas_forward_decl GlobalTheory.LocalWittFree.exists_smul_ratTup_eq
end

section
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalStabiliserHaar

theorem gramR_ratTup {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {n a : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (X : Fin a → Fin n → E) :
    gramR R σ J (ratTup (F := F) R X) = (gramE σ J X).map (inclR R) := by
  ext i j
  simp [gramR, gramE, hE, hR, Formalism.UG.hform, ratTup, JR, sigR, inclR, Matrix.map_apply, mul_assoc]

theorem linearIndependent_smul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type)
    [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n a : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (g : HA R σ J) {X : Fin a → Fin n → R ⊗[F] E} (hX : LinearIndependent (R ⊗[F] E) X) :
    LinearIndependent (R ⊗[F] E) (g • X) := by
  have hker : LinearMap.ker (lin R σ J g) = ⊥ := by
    refine LinearMap.ker_eq_bot.2 fun x y hxy => ?_
    rw [← lin_inv_lin R σ J g x, hxy, lin_inv_lin]
  exact hX.map' (lin R σ J g) hker

theorem exists_haar_stabiliser : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ (hT : ∀ i j, σ (gramE σ J (F0 P) j i) = gramE σ J (F0 P) i j), ∀ (μ : Measure (Fin (r + 1) → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ (r + 1))), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ (r + 1) → Measure (Fin (r + 1) → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ μG : Measure (HA (Fv F v) σ J), μG.IsHaarMeasure → ∃ μ0 : Measure (S0 (Fv F v) σ J P), μ0.IsHaarMeasure ∧ ((fib (hermOf (Fv F v) σ (gramE σ J (F0 P)) hT)) {y | ¬ ∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) (F0 P) = y} = 0 ∧ ∀ f : HA (Fv F v) σ J → ℝ≥0∞, Measurable f → ∀ s : (Fin (r + 1) → Fin n → Fv F v ⊗[F] E) → HA (Fv F v) σ J, (∀ y, (∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) (F0 P) = y) → s y • ratTup (Fv F v) (F0 P) = y) → ∫⁻ g, f g ∂μG = ∫⁻ y, ∫⁻ h', f (s y * (h' : HA (Fv F v) σ J)) ∂μ0 ∂(fib (hermOf (Fv F v) σ (gramE σ J (F0 P)) hT))) := by
  intro F E _ _ _ _ _ σ hCM n J hJ v r P T hP hT μ ν hμ hν fib hfib μG hμG
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := GlobalTheory.T.localUnitaryGroup_tuples_topological_facts F E σ hCM n J hJ v
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI := h5
  haveI := h6
  haveI := h7
  haveI := h8
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (HA (Fv F v) σ J) := ⟨rfl⟩
  obtain ⟨-, -, -, -, hfree⟩ := GlobalTheory.T.standardFrame_gram_det_ne_zero F E σ hCM n J hJ r P T hP
  have hx0 := hfree v
  set x0 := ratTup (F := F) (Fv F v) (F0 P) with hx0def
  set S := hermOf (Fv F v) σ (gramE σ J (F0 P)) hT with hS
  have hgram : gramR (Fv F v) σ J x0 = (S : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) :=
    gramR_ratTup (Fv F v) σ J (F0 P)
  obtain ⟨hne, hfin⟩ := GlobalTheory.T.gramFibreMeasure_freeTuple_ne_zero_finite F E σ hCM n J hJ v (r + 1) μ ν hμ hν fib hfib x0 S hx0 hgram
  have hinv := GlobalTheory.T.gramMap_fibreMeasure_localUnitary_invariant F E σ hCM n J hJ v (r + 1) μ ν hμ hν fib hfib S
  have hcont := (h9 (r + 1)).2
  have hnull : (fib S) {y | ¬ ∃ g : HA (Fv F v) σ J, g • x0 = y} = 0 := by
    refine measure_mono_null (fun y hy => ?_) (hfib.1 S)
    intro hmem
    exact hy (GlobalTheory.T.exists_smul_localWitt_free_tuple_gram F E σ hCM n J hJ v r P T hP y hmem.2 hmem.1)
  have hsmul : ∀ g : HA (Fv F v) σ J, Continuous
      (fun y : Fin (r + 1) → Fin n → Fv F v ⊗[F] E => g • y) := fun g =>
    hcont.comp (Continuous.prodMk continuous_const continuous_id)
  have hinv' : ∀ (g : HA (Fv F v) σ J) (s : Set (Fin (r + 1) → Fin n → Fv F v ⊗[F] E)),
      MeasurableSet s → (fib S) ((fun y => g • y) ⁻¹' s) = (fib S) s := by
    intro g s hs
    rw [← Measure.map_apply (hsmul g).measurable hs, hinv g]
  have hcpt : ∀ K : Set (HA (Fv F v) σ J), IsCompact K →
      (fib S) ((fun g => g • x0) '' K) < ⊤ := by
    intro K hK
    refine hfin _ (hK.image ?_) ?_
    · exact hcont.comp (Continuous.prodMk continuous_id continuous_const)
    · rintro _ ⟨g, -, rfl⟩
      exact linearIndependent_smul (Fv F v) σ J g hx0
  obtain ⟨μ0, hμ0, hw⟩ := GlobalTheory.T.weil_integration_formula_orbit (HA (Fv F v) σ J) (Fin (r + 1) → Fin n → Fv F v ⊗[F] E) x0
    hcont μG hμG (fib S) hnull hinv' hcpt hne
  exact ⟨μ0, hμ0, hnull, hw⟩

end GlobalTheory.LocalStabiliserHaar
end

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_frameStabiliser_compatible_fibre : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ (hT : ∀ i j, σ (gramE σ J (F0 P) j i) = gramE σ J (F0 P) i j), ∀ (μ : Measure (Fin (r + 1) → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ (r + 1))), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ (r + 1) → Measure (Fin (r + 1) → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ μG : Measure (HA (Fv F v) σ J), μG.IsHaarMeasure → ∃ μ0 : Measure (S0 (Fv F v) σ J P), μ0.IsHaarMeasure ∧ ((fib (hermOf (Fv F v) σ (gramE σ J (F0 P)) hT)) {y | ¬ ∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) (F0 P) = y} = 0 ∧ ∀ f : HA (Fv F v) σ J → ℝ≥0∞, Measurable f → ∀ s : (Fin (r + 1) → Fin n → Fv F v ⊗[F] E) → HA (Fv F v) σ J, (∀ y, (∃ g : HA (Fv F v) σ J, g • ratTup (Fv F v) (F0 P) = y) → s y • ratTup (Fv F v) (F0 P) = y) → ∫⁻ g, f g ∂μG = ∫⁻ y, ∫⁻ h', f (s y * (h' : HA (Fv F v) σ J)) ∂μ0 ∂(fib (hermOf (Fv F v) σ (gramE σ J (F0 P)) hT))) := by
  atlas_forward_decl GlobalTheory.LocalStabiliserHaar.exists_haar_stabiliser
end
