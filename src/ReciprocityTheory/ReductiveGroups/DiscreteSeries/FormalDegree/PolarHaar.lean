import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarRight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntMuCD
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.AdKMeasurePreserving
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarBasic
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KinstSecondCountable

section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem polarInv_pmat_neg {ε : Fin n → Bool} (z : PCoord ε → ℂ) : pmat (-z) = -pmat z := by
  ext a b
  simp only [pmat, Matrix.neg_apply, Pi.neg_apply]
  split_ifs <;> simp [star_neg]

theorem polarInv_Jm_pmat {ε : Fin n → Bool} (z : PCoord ε → ℂ) : Jm ε * pmat z * Jm ε = -pmat z := by
  ext a b
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply]
  by_cases hab : ε a = ε b
  · have h0 : pmat z a b = 0 := by simp [pmat, hab]
    rw [h0]; simp
  · have hs : (if ε a then (1:ℂ) else -1) * (if ε b then 1 else -1) = -1 := by
      cases ha : ε a <;> cases hb : ε b <;> simp_all
    calc (if ε a then (1:ℂ) else -1) * pmat z a b * (if ε b then 1 else -1)
        = ((if ε a then (1:ℂ) else -1) * (if ε b then 1 else -1)) * pmat z a b := by ring
      _ = -pmat z a b := by rw [hs]; ring

theorem polarInv_toMK_inv {ε : Fin n → Bool} (k : KG ε) : toMK k⁻¹ = (toMK k)ᴴ := by
  have hu : toMK k ∈ Matrix.unitaryGroup (Fin n) ℂ := k.2.1
  exact Units.inv_eq_of_mul_eq_one_right (Matrix.mem_unitaryGroup_iff.mp hu)

private theorem pmat_conjTranspose_eq_self {ε : Fin n → Bool} (z : PCoord ε → ℂ) : (pmat z)ᴴ = pmat z := by
  ext a b
  simp only [Matrix.conjTranspose_apply, pmat]
  by_cases h1 : b < a ∧ ε a ≠ ε b
  · have h2 : ¬ (a < b ∧ ε b ≠ ε a) := fun h => lt_asymm h1.1 h.1
    simp only [dif_neg h2, dif_pos h1, star_star]
  · by_cases h3 : a < b ∧ ε b ≠ ε a
    · simp only [dif_neg h1, dif_pos h3]
    · simp only [dif_neg h1, dif_neg h3, star_zero]

private theorem Jm_mul_Jm_eq_oneFormalDegree (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

private theorem conjTranspose_Jm_eq_Jm (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem polarInv_key {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) :
    Jm ε * (polarM (k, z))ᴴ * Jm ε = polarM (k⁻¹, adK k (-z)) := by
  have hK : toMK k ∈ Matrix.unitaryGroup (Fin n) ℂ := k.2.1
  have hKJ : toMK k * Jm ε = Jm ε * toMK k := k.2.2
  have hJJ : Jm ε * Jm ε = 1 := Jm_mul_Jm_eq_oneFormalDegree ε
  have hJh : (Jm ε)ᴴ = Jm ε := conjTranspose_Jm_eq_Jm ε
  have hKKh : toMK k * (toMK k)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hK
  have hKhK : (toMK k)ᴴ * toMK k = 1 := Matrix.mem_unitaryGroup_iff'.mp hK
  have hKhJ : (toMK k)ᴴ * Jm ε = Jm ε * (toMK k)ᴴ := by
    have h := congrArg Matrix.conjTranspose hKJ
    simp only [Matrix.conjTranspose_mul, hJh] at h
    exact h.symm
  have hKu : IsUnit (toMK k) := ⟨⟨toMK k, (toMK k)ᴴ, hKKh, hKhK⟩, rfl⟩
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩
  have hKinv : (toMK k)⁻¹ = (toMK k)ᴴ := Matrix.inv_eq_right_inv hKKh
  have hJinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_right_inv hJJ
  have hE : (NormedSpace.exp (pmat z))ᴴ = NormedSpace.exp (pmat z) := by
    rw [← Matrix.exp_conjTranspose, pmat_conjTranspose_eq_self]
  have h1 : NormedSpace.exp (Jm ε * pmat z * (Jm ε)⁻¹) =
      Jm ε * NormedSpace.exp (pmat z) * (Jm ε)⁻¹ := Matrix.exp_conj _ _ hJu
  have h2 : NormedSpace.exp (toMK k * pmat (-z) * (toMK k)⁻¹) =
      toMK k * NormedSpace.exp (pmat (-z)) * (toMK k)⁻¹ := Matrix.exp_conj _ _ hKu
  rw [hJinv, polarInv_Jm_pmat] at h1
  rw [hKinv] at h2
  rw [show polarM (k, z) = toMK k * NormedSpace.exp (pmat z) from rfl,
    show polarM (k⁻¹, adK k (-z)) = toMK k⁻¹ * NormedSpace.exp (pmat (adK k (-z))) from rfl,
    polarInv_toMK_inv, pmat_adK, h2, Matrix.conjTranspose_mul, hE, polarInv_pmat_neg, h1]
  calc Jm ε * (NormedSpace.exp (pmat z) * (toMK k)ᴴ) * Jm ε
      = Jm ε * NormedSpace.exp (pmat z) * ((toMK k)ᴴ * Jm ε) := by simp only [Matrix.mul_assoc]
    _ = Jm ε * NormedSpace.exp (pmat z) * (Jm ε * (toMK k)ᴴ) := by rw [hKhJ]
    _ = ((toMK k)ᴴ * toMK k) * (Jm ε * NormedSpace.exp (pmat z) * Jm ε) * (toMK k)ᴴ := by
        rw [hKhK, Matrix.one_mul]; simp only [Matrix.mul_assoc]
    _ = (toMK k)ᴴ * (toMK k * (Jm ε * NormedSpace.exp (pmat z) * Jm ε) * (toMK k)ᴴ) := by
        simp only [Matrix.mul_assoc]

theorem polarInv_apply (ε : Fin n → Bool) (S : Set (UJ ε)) (hS : MeasurableSet S) :
    muPolar ε S = ∫⁻ k, ∫⁻ z, (intMuCD_eM ε '' S).indicator (1 : (Fin n → Fin n → ℂ) → ENNReal)
      (intMuCD_pM ε (k, z)) * ENNReal.ofReal (Jac z) ∂volume ∂(dk ε) := by
  have hce : Topology.IsClosedEmbedding (intMuCD_eM ε) := isClosedEmbedding_toM ε
  have he : MeasurableEmbedding (intMuCD_eM ε) := hce.measurableEmbedding
  have hT : MeasurableSet (intMuCD_eM ε '' S) := he.measurableSet_image.2 hS
  have hF : Measurable ((intMuCD_eM ε '' S).indicator (1 : (Fin n → Fin n → ℂ) → ENNReal)) :=
    measurable_one.indicator hT
  have h := lintegral_muPolar ε _ hF
  rw [← lintegral_indicator_one hS]
  refine Eq.trans ?_ h
  refine lintegral_congr (fun g => ?_)
  change S.indicator 1 g = (intMuCD_eM ε '' S).indicator 1 (intMuCD_eM ε g)
  classical
  simp only [Set.indicator_apply, he.injective.mem_set_image, Pi.one_apply]

theorem muPolar_inv (ε : Fin n → Bool) : Measure.map (fun x : UJ ε => x⁻¹) (muPolar ε) = muPolar ε := by
  have hinv : Measurable (fun x : UJ ε => x⁻¹) := continuous_inv.measurable
  have hinvK : Measurable (fun x : KG ε => x⁻¹) := continuous_inv.measurable
  have hce : Topology.IsClosedEmbedding (intMuCD_eM ε) := isClosedEmbedding_toM ε
  have he : MeasurableEmbedding (intMuCD_eM ε) := hce.measurableEmbedding
  ext S hS
  rw [Measure.map_apply hinv hS, polarInv_apply ε _ (hinv hS), polarInv_apply ε S hS]
  have hT : MeasurableSet (intMuCD_eM ε '' S) := he.measurableSet_image.2 hS
  have hpt : ∀ (k : KG ε) (z : PCoord ε → ℂ),
      (intMuCD_eM ε '' ((fun x : UJ ε => x⁻¹) ⁻¹' S)).indicator
          (1 : (Fin n → Fin n → ℂ) → ENNReal) (intMuCD_pM ε (k, z)) =
        (intMuCD_eM ε '' S).indicator 1 (intMuCD_pM ε (k⁻¹, adK k (-z))) := by
    intro k z
    obtain ⟨g, hg⟩ : polarM (k, z) ∈ Set.range (fun g : UJ ε => toM g) := by
      rw [range_toM]; exact polarM_inUJ (k, z)
    have hg' : toM g = polarM (k, z) := hg
    have e1 : intMuCD_pM ε (k, z) = intMuCD_eM ε g := hg'.symm
    have e2 : intMuCD_pM ε (k⁻¹, adK k (-z)) = intMuCD_eM ε g⁻¹ := by
      show polarM _ = toM g⁻¹
      rw [toM_inv, hg', polarInv_key]
    rw [e1, e2]
    classical
    simp only [Set.indicator_apply, he.injective.mem_set_image, Set.mem_preimage, Pi.one_apply]
  let G : KG ε × (PCoord ε → ℂ) → ENNReal := fun kz =>
    (intMuCD_eM ε '' S).indicator 1 (intMuCD_pM ε kz) * ENNReal.ofReal (Jac kz.2)
  have hG : Measurable G :=
    ((measurable_one.indicator hT).comp (intMuCD_measurable_pM ε)).mul
      (ENNReal.measurable_ofReal.comp ((jac_continuous ε).measurable.comp measurable_snd))
  have hH : Measurable fun k => ∫⁻ w, G (k, w) := hG.lintegral_prod_right'
  have step : ∀ k : KG ε, ∫⁻ z, (intMuCD_eM ε '' ((fun x : UJ ε => x⁻¹) ⁻¹' S)).indicator 1
      (intMuCD_pM ε (k, z)) * ENNReal.ofReal (Jac z) = ∫⁻ w, G (k⁻¹, w) := by
    intro k
    have hφ : MeasurePreserving (fun z : PCoord ε → ℂ => adK k (-z)) volume volume :=
      (adK_measurePreserving k).comp (Measure.measurePreserving_neg volume)
    have hm : Measurable (fun w => G (k⁻¹, w)) := hG.comp measurable_prodMk_left
    refine Eq.trans ?_ (hφ.lintegral_comp hm)
    refine lintegral_congr fun z => ?_
    show _ = G (k⁻¹, adK k (-z))
    simp only [G, hpt, jac_adK, jac_neg]
  calc ∫⁻ k, ∫⁻ z, (intMuCD_eM ε '' ((fun x : UJ ε => x⁻¹) ⁻¹' S)).indicator 1
        (intMuCD_pM ε (k, z)) * ENNReal.ofReal (Jac z) ∂volume ∂(dk ε)
      = ∫⁻ k, (fun k => ∫⁻ w, G (k, w)) ((fun x : KG ε => x⁻¹) k) ∂(dk ε) := lintegral_congr step
    _ = ∫⁻ k, (∫⁻ w, G (k, w)) ∂(Measure.map (fun x : KG ε => x⁻¹) (dk ε)) := by
        rw [lintegral_map hH hinvK]
    _ = _ := by rw [(dk_props ε).2.2.2]

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset Matrix MeasureTheory Topology
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma fdph_muK_univ_ne_zero (ε : Fin n → Bool) : muK ε Set.univ ≠ 0 := by
  exact isOpen_univ.measure_ne_zero (muK ε) Set.univ_nonempty

lemma fdph_muK_univ_ne_top (ε : Fin n → Bool) : muK ε Set.univ ≠ ⊤ := by
  exact (isCompact_univ.measure_lt_top (μ := muK ε)).ne

instance fdph_dk_finite (ε : Fin n → Bool) : IsFiniteMeasure (dk ε) := by
  refine ⟨?_⟩
  rw [dk, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr (fdph_muK_univ_ne_zero ε)))
    isCompact_univ.measure_lt_top

instance fdph_dk_openPos (ε : Fin n → Bool) : Measure.IsOpenPosMeasure (dk ε) := by
  unfold dk
  exact Measure.isOpenPosMeasure_smul _ (ENNReal.inv_ne_zero.mpr (fdph_muK_univ_ne_top ε))

lemma fdph_shc_pos (u : ℝ) : 0 < shc u := by
  unfold shc
  split_ifs with h
  · exact one_pos
  · rcases lt_or_gt_of_ne h with h' | h'
    · exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr h') h'
    · exact div_pos (Real.sinh_pos_iff.mpr h') h'

lemma fdph_jac_pos {ε : Fin n → Bool} (z : PCoord ε → ℂ) : 0 < Jac z := by
  unfold Jac
  exact Finset.prod_pos fun a _ => Finset.prod_pos fun b _ => fdph_shc_pos _

abbrev fdphNu (ε : Fin n → Bool) : Measure (PCoord ε → ℂ) :=
  (volume : Measure (PCoord ε → ℂ)).withDensity fun z => ENNReal.ofReal (Jac z)

instance fdph_nu_openPos (ε : Fin n → Bool) : Measure.IsOpenPosMeasure (fdphNu ε) := by
  refine ⟨fun U hU hne => ?_⟩
  have hm : Measurable fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z) :=
    ENNReal.measurable_ofReal.comp (jac_continuous ε).measurable
  rw [Ne, fdphNu, withDensity_apply_eq_zero hm]
  have hu : {x : PCoord ε → ℂ | ENNReal.ofReal (Jac x) ≠ 0} = Set.univ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, Ne, ENNReal.ofReal_eq_zero, not_le]
    exact fdph_jac_pos x
  rw [hu, Set.univ_inter]
  exact hU.measure_ne_zero volume hne

instance fdph_nu_finCpt (ε : Fin n → Bool) : IsFiniteMeasureOnCompacts (fdphNu ε) := by
  refine ⟨fun K hK => ?_⟩
  rw [fdphNu, withDensity_apply' _ K]
  exact setLIntegral_lt_top_of_isCompact hK.measure_lt_top.ne hK (f := fun z => (Jac z).toNNReal)
    (continuous_real_toNNReal.comp (jac_continuous ε))

def fdphPhi (ε : Fin n → Bool) (kz : KG ε × (PCoord ε → ℂ)) : UJ ε :=
  ⟨⟨polarM kz, Jm ε * (polarM kz)ᴴ * Jm ε,
    mul_eq_one_comm.mp (left_inv_of_inUJ ε _ (polarM_inUJ kz)), left_inv_of_inUJ ε _ (polarM_inUJ kz)⟩,
    polarM_inUJ kz⟩

lemma fdph_toM_phi (ε : Fin n → Bool) (kz : KG ε × (PCoord ε → ℂ)) : toM (fdphPhi ε kz) = polarM kz := rfl

lemma fdph_phi_continuous (ε : Fin n → Bool) : Continuous (fdphPhi ε) := by
  unfold fdphPhi
  have hexp : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => NormedSpace.exp M) := by
    letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
    exact NormedSpace.exp_continuous
  have htoMK : Continuous (fun k : KG ε => toMK k) := by
    fun_prop
  have hpmat : Continuous (fun z : PCoord ε → ℂ => pmat z) := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    by_cases h : b < a ∧ ε a ≠ ε b
    · simp only [pmat, dif_pos h]
      exact continuous_apply _
    · by_cases h' : a < b ∧ ε b ≠ ε a
      · simp only [pmat, dif_neg h, dif_pos h']
        exact (continuous_apply _).star
      · simp only [pmat, dif_neg h, dif_neg h']
        exact continuous_const
  have hpol : Continuous (fun kz : KG ε × (PCoord ε → ℂ) => polarM kz) := by
    unfold polarM
    exact (htoMK.comp continuous_fst).matrix_mul (hexp.comp (hpmat.comp continuous_snd))
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  exact ⟨hpol, (continuous_const.matrix_mul hpol.matrix_conjTranspose).matrix_mul continuous_const⟩

lemma fdph_preimage (ε : Fin n → Bool) (S : Set (UJ ε)) :
    Set.preimage (β := Fin n → Fin n → ℂ) polarM (Set.image (β := Fin n → Fin n → ℂ) (fun g : UJ ε => toM g) S) =
      fdphPhi ε ⁻¹' S := by
  ext kz
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨g, hg, hgeq⟩
    have hge : g = fdphPhi ε kz :=
      Subtype.ext (Units.ext (hgeq.trans (fdph_toM_phi ε kz).symm))
    rw [← hge]
    exact hg
  · intro h
    exact ⟨fdphPhi ε kz, h, fdph_toM_phi ε kz⟩

lemma fdph_apply (ε : Fin n → Bool) {S : Set (UJ ε)} (hS : MeasurableSet S) :
    muPolar ε S = ((dk ε).prod (fdphNu ε)) (fdphPhi ε ⁻¹' S) := by
  have hC : IsClosedEmbedding (Y := Fin n → Fin n → ℂ) (fun g : UJ ε => toM g) := isClosedEmbedding_toM ε
  have hE : MeasurableEmbedding (β := Fin n → Fin n → ℂ) (fun g : UJ ε => toM g) := hC.measurableEmbedding
  have hPc : Continuous (Y := Fin n → Fin n → ℂ) (polarM (ε := ε)) := (polarM_isClosedEmbedding ε).continuous
  have hP : Measurable (β := Fin n → Fin n → ℂ) (polarM (ε := ε)) := hPc.measurable
  unfold muPolar muPolarMat
  rw [hE.comap_apply, Measure.map_apply hP (hE.measurableSet_image' hS), fdph_preimage]


end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem muPolar_isHaar (ε : Fin n → Bool) : (muPolar ε).IsHaarMeasure := by
  haveI hR : (muPolar ε).IsMulRightInvariant := ⟨fun g => muPolar_mul_right ε g⟩
  have hinv : (muPolar ε).inv = muPolar ε := muPolar_inv ε
  haveI hL : (muPolar ε).IsMulLeftInvariant := by
    rw [← hinv]; infer_instance

  have hsurj : Function.Surjective (fdphPhi ε) := by
    intro g
    have hg : toM g ∈ UJset ε := g.2
    refine ⟨polarInv ε ⟨toM g, hg⟩, ?_⟩
    have h := fdph_toM_phi ε (polarInv ε ⟨toM g, hg⟩)
    rw [polarM_polarInv] at h
    exact Subtype.ext (Units.ext h)
  haveI hF : IsFiniteMeasureOnCompacts (muPolar ε) := by
    refine ⟨fun K hK => ?_⟩
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    rw [fdph_apply ε hKm, ← fdph_preimage]
    exact ((polarM_isClosedEmbedding ε).isCompact_preimage
      (hK.image (by fun_prop))).measure_lt_top
  haveI hO : (muPolar ε).IsOpenPosMeasure := by
    refine ⟨fun U hU hne => ?_⟩
    rw [fdph_apply ε hU.measurableSet]
    exact ((hU.preimage (fdph_phi_continuous ε)).measure_ne_zero _
      (hne.preimage hsurj))
  exact {}

end ReciprocityTheory.ChartRestriction.DS
end
end
