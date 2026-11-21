import Mathlib
import GroundTheory.GlobalFields.TateThesis.GlobalZetaSplit
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform

section
open NumberField IsDedekindDomain Topology Filter MeasureTheory
open scoped NumberField.AdeleRing Pointwise

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

def adelicTheta (F : 𝔸[K] → ℂ) (a : IdeleGroup K) : ℂ :=
  ∑' ξ : K, F (a • algebraMap K 𝔸[K] ξ)

theorem adelicTheta_eq {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) (a : IdeleGroup K) :
    adelicTheta F a =
      ((ideleModule K a : ℝ)⁻¹ : ℂ) * adelicTheta (adelicFourier K F) a⁻¹ :=
  tsum_smul_algebraMap_eq a hF

theorem adelicTheta_diagonal_mul (F : 𝔸[K] → ℂ) (δ : Kˣ) (a : IdeleGroup K) :
    adelicTheta F (diagonal K δ * a) = adelicTheta F a := by
  unfold adelicTheta
  conv_rhs => rw [← (Equiv.mulLeft₀ (δ : K) δ.ne_zero).tsum_eq]
  refine tsum_congr fun ξ ↦ congrArg F ?_
  change ((diagonal K δ * a : IdeleGroup K) : 𝔸[K]) * algebraMap K 𝔸[K] ξ =
    (a : 𝔸[K]) * algebraMap K 𝔸[K] ((δ : K) * ξ)
  rw [Units.val_mul, coe_diagonal, map_mul]
  ring

theorem adelicTheta_neg (F : 𝔸[K] → ℂ) (a : IdeleGroup K) :
    adelicTheta (fun x ↦ F (-x)) a = adelicTheta F a := by
  unfold adelicTheta
  rw [← (Equiv.neg K).tsum_eq]
  refine tsum_congr fun ξ ↦ congrArg F ?_
  change -((a : 𝔸[K]) * algebraMap K 𝔸[K] (-ξ)) = (a : 𝔸[K]) * algebraMap K 𝔸[K] ξ
  rw [map_neg, mul_neg, neg_neg]

theorem smul_algebraMap_zero (a : IdeleGroup K) : a • algebraMap K 𝔸[K] 0 = 0 := by
  rw [map_zero, smul_zero]

theorem continuousOn_adelicTheta {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    {C : Set (IdeleGroup K)} (hC : IsCompact C) : ContinuousOn (adelicTheta F) C := by
  obtain ⟨u, hu, hFu⟩ := exists_summable_bound_smul_algebraMap hF hC
  refine continuousOn_tsum (fun ξ ↦ ?_) hu (fun ξ a ha ↦ hFu a ha ξ)
  have h : Continuous fun a : IdeleGroup K ↦ F ((a : 𝔸[K]) * algebraMap K 𝔸[K] ξ) :=
    (continuous_of_mem_schwartzBruhat hF).comp (Units.continuous_val.mul continuous_const)
  exact h.continuousOn

theorem continuous_adelicTheta {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) :
    Continuous (adelicTheta F) := by
  refine continuous_iff_continuousAt.2 fun a ↦ ?_
  obtain ⟨C, hC, haC⟩ := exists_compact_mem_nhds a
  exact (continuousOn_adelicTheta hF hC).continuousAt haC

theorem isFundamentalDomain_of_existsUnique {S : Set (normOneSubgroup K)} (hS : MeasurableSet S)
    (h : ∀ u, ∃! ξ : Kˣ, u * diagonalToNormOne K ξ ∈ S) (μ : Measure (normOneSubgroup K)) :
    IsFundamentalDomain (diagonalNormOne K).op S μ := by
  refine IsFundamentalDomain.mk' hS.nullMeasurableSet fun u ↦ ?_
  let e : Kˣ ≃ (diagonalNormOne K).op :=
    (diagonalNormOneEquiv K).trans (diagonalNormOne K).equivOp
  have he : ∀ ξ : Kˣ, e ξ • u = u * diagonalToNormOne K ξ := fun _ ↦ rfl
  obtain ⟨ξ, hξ, huniq⟩ := h u
  refine ⟨e ξ, ?_, fun γ hγ ↦ ?_⟩
  · show e ξ • u ∈ S
    rw [he]
    exact hξ
  change γ • u ∈ S at hγ
  rw [← e.apply_symm_apply γ, he] at hγ
  rw [← e.apply_symm_apply γ, huniq _ hγ]

theorem setIntegral_eq_of_existsUnique {S : Set (normOneSubgroup K)} (hS : MeasurableSet S)
    (hSu : ∀ u, ∃! ξ : Kˣ, u * diagonalToNormOne K ξ ∈ S) {h : normOneSubgroup K → ℂ}
    (hh : ∀ (ξ : Kˣ) (u : normOneSubgroup K), h (u * diagonalToNormOne K ξ) = h u) :
    ∫ u in S, h u ∂normOneMeasure K = ∫ u in normOneFundamentalDomain K, h u ∂normOneMeasure K := by
  refine (isFundamentalDomain_of_existsUnique hS hSu _).setIntegral_eq
    (isFundamentalDomain_normOneFundamentalDomain K _) fun γ u ↦ ?_
  let e : Kˣ ≃ (diagonalNormOne K).op :=
    (diagonalNormOneEquiv K).trans (diagonalNormOne K).equivOp
  rw [← e.apply_symm_apply γ]
  exact hh _ u

theorem existsUnique_mul_mem_inv_normOneFundamentalDomain (u : normOneSubgroup K) :
    ∃! ξ : Kˣ, u * diagonalToNormOne K ξ ∈ (normOneFundamentalDomain K)⁻¹ := by
  obtain ⟨η, hη, huniq⟩ := existsUnique_mul_mem_normOneFundamentalDomain K u⁻¹
  have key : ∀ ξ : Kˣ, u * diagonalToNormOne K ξ ∈ (normOneFundamentalDomain K)⁻¹ ↔
      u⁻¹ * diagonalToNormOne K ξ⁻¹ ∈ normOneFundamentalDomain K := fun ξ ↦ by
    rw [Set.mem_inv, mul_inv, map_inv]
  refine ⟨η⁻¹, (key _).2 (by rwa [inv_inv]), fun ξ hξ ↦ ?_⟩
  have := huniq _ ((key ξ).1 hξ)
  rw [← this, inv_inv]

theorem existsUnique_mul_mem_preimage_normOneFundamentalDomain (v u : normOneSubgroup K) :
    ∃! ξ : Kˣ, u * diagonalToNormOne K ξ ∈ (v * ·) ⁻¹' normOneFundamentalDomain K := by
  obtain ⟨η, hη, huniq⟩ := existsUnique_mul_mem_normOneFundamentalDomain K (v * u)
  refine ⟨η, ?_, fun ξ hξ ↦ huniq _ ?_⟩
  · show v * (u * diagonalToNormOne K η) ∈ normOneFundamentalDomain K
    rwa [← mul_assoc]
  · change v * (u * diagonalToNormOne K ξ) ∈ normOneFundamentalDomain K at hξ
    show v * u * diagonalToNormOne K ξ ∈ normOneFundamentalDomain K
    rwa [← mul_assoc] at hξ

theorem setIntegral_inv_eq {h : normOneSubgroup K → ℂ}
    (hh : ∀ (ξ : Kˣ) (u : normOneSubgroup K), h (u * diagonalToNormOne K ξ) = h u) :
    ∫ u in normOneFundamentalDomain K, h u⁻¹ ∂normOneMeasure K =
      ∫ u in normOneFundamentalDomain K, h u ∂normOneMeasure K := by
  have hpre : (Inv.inv ⁻¹' (normOneFundamentalDomain K)⁻¹ : Set (normOneSubgroup K)) =
      normOneFundamentalDomain K := inv_inv _
  have h1 := (Measure.measurePreserving_inv (normOneMeasure K)).setIntegral_preimage_emb
    (MeasurableEquiv.inv (normOneSubgroup K)).measurableEmbedding h (normOneFundamentalDomain K)⁻¹
  rw [hpre] at h1
  rw [h1]
  exact setIntegral_eq_of_existsUnique (measurableSet_normOneFundamentalDomain K).inv
    existsUnique_mul_mem_inv_normOneFundamentalDomain hh

theorem setIntegral_mul_left_eq {h : normOneSubgroup K → ℂ}
    (hh : ∀ (ξ : Kˣ) (u : normOneSubgroup K), h (u * diagonalToNormOne K ξ) = h u)
    (v : normOneSubgroup K) :
    ∫ u in normOneFundamentalDomain K, h (v * u) ∂normOneMeasure K =
      ∫ u in normOneFundamentalDomain K, h u ∂normOneMeasure K := by
  have hS : MeasurableSet ((v * ·) ⁻¹' normOneFundamentalDomain K) :=
    (measurable_const_mul v) (measurableSet_normOneFundamentalDomain K)
  have h1 := (measurePreserving_mul_left (normOneMeasure K) v).setIntegral_preimage_emb
    (MeasurableEquiv.mulLeft v).measurableEmbedding h (normOneFundamentalDomain K)
  have h2 := setIntegral_eq_of_existsUnique hS
    (existsUnique_mul_mem_preimage_normOneFundamentalDomain v)
    (h := fun u ↦ h (v * u)) fun ξ u ↦ by simp only [← mul_assoc, hh]
  rw [← h2, h1]

theorem toIdele_mul_diagonalToNormOne (χ : HeckeCharacter K) (ξ : Kˣ) (u : normOneSubgroup K) :
    (χ.toIdele ((u * diagonalToNormOne K ξ : normOneSubgroup K) : IdeleGroup K) : ℂ) =
      χ.toIdele (u : IdeleGroup K) := by
  rw [Subgroup.coe_mul, coe_diagonalToNormOne, map_mul, HeckeCharacter.toIdele_diagonal, mul_one]

theorem setIntegral_char_eq_zero {χ : HeckeCharacter K}
    (hχ : ∃ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) ≠ 1) :
    ∫ u in normOneFundamentalDomain K, (χ.toIdele (u : IdeleGroup K) : ℂ) ∂normOneMeasure K = 0 := by
  obtain ⟨v, hv⟩ := hχ
  have h := setIntegral_mul_left_eq (h := fun u ↦ (χ.toIdele (u : IdeleGroup K) : ℂ))
    (fun ξ u ↦ toIdele_mul_diagonalToNormOne χ ξ u) v
  simp only [Subgroup.coe_mul, map_mul, Circle.coe_mul] at h
  rw [integral_const_mul] at h
  have hv' : (χ.toIdele (v : IdeleGroup K) : ℂ) ≠ 1 := fun h1 ↦ hv (Circle.ext (by simpa using h1))
  have h3 : ((χ.toIdele (v : IdeleGroup K) : ℂ) - 1) *
      ∫ u in normOneFundamentalDomain K, (χ.toIdele (u : IdeleGroup K) : ℂ) ∂normOneMeasure K = 0 := by
    rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hv')

theorem normOneClassMeasure_univ :
    normOneClassMeasure K Set.univ = normOneMeasure K (normOneFundamentalDomain K) := by
  rw [normOneClassMeasure, Measure.map_apply QuotientGroup.measurable_coe MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply_univ]

theorem setIntegral_char_eq_volume {χ : HeckeCharacter K}
    (hχ : ∀ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) = 1) :
    ∫ u in normOneFundamentalDomain K, (χ.toIdele (u : IdeleGroup K) : ℂ) ∂normOneMeasure K =
      ((normOneClassMeasure K Set.univ).toReal : ℂ) := by
  simp only [hχ, Circle.coe_one]
  rw [setIntegral_const, normOneClassMeasure_univ, Measure.real_def, Complex.real_smul, mul_one]

def thetaIntegrand (w : InfinitePlace K) (F : 𝔸[K] → ℂ) (χ : HeckeCharacter K)
    (t : {r : ℝ // 0 < r}) (u : normOneSubgroup K) : ℂ :=
  adelicTheta F (moduleSection w t * (u : IdeleGroup K)) * (χ.toIdele (u : IdeleGroup K) : ℂ)

def thetaIntegral (w : InfinitePlace K) (F : 𝔸[K] → ℂ) (χ : HeckeCharacter K)
    (t : {r : ℝ // 0 < r}) : ℂ :=
  ∫ u in normOneFundamentalDomain K, thetaIntegrand w F χ t u ∂normOneMeasure K

theorem thetaIntegrand_mul_diagonalToNormOne (w : InfinitePlace K) (F : 𝔸[K] → ℂ)
    (χ : HeckeCharacter K) (t : {r : ℝ // 0 < r}) (ξ : Kˣ) (u : normOneSubgroup K) :
    thetaIntegrand w F χ t (u * diagonalToNormOne K ξ) = thetaIntegrand w F χ t u := by
  unfold thetaIntegrand
  rw [toIdele_mul_diagonalToNormOne]
  congr 1
  rw [Subgroup.coe_mul, coe_diagonalToNormOne, ← mul_assoc, mul_comm _ (diagonal K ξ)]
  exact adelicTheta_diagonal_mul F ξ _

theorem continuous_thetaIntegrand (w : InfinitePlace K) {F : 𝔸[K] → ℂ}
    (hF : F ∈ schwartzBruhat K) (χ : HeckeCharacter K) (t : {r : ℝ // 0 < r}) :
    Continuous (thetaIntegrand w F χ t) := by
  have h1 : Continuous fun u : normOneSubgroup K ↦ moduleSection w t * (u : IdeleGroup K) :=
    continuous_const.mul continuous_subtype_val
  have h2 : Continuous fun u : normOneSubgroup K ↦ (χ.toIdele (u : IdeleGroup K) : ℂ) :=
    continuous_subtype_val.comp (χ.continuous_toIdele.comp continuous_subtype_val)
  exact ((continuous_adelicTheta hF).comp h1).mul h2

theorem integrableOn_thetaIntegrand (w : InfinitePlace K) {F : 𝔸[K] → ℂ}
    (hF : F ∈ schwartzBruhat K) (χ : HeckeCharacter K) (t : {r : ℝ // 0 < r}) :
    IntegrableOn (thetaIntegrand w F χ t) (normOneFundamentalDomain K) (normOneMeasure K) :=
  ((continuous_thetaIntegrand w hF χ t).continuousOn.integrableOn_compact
    (isCompact_closure_normOneFundamentalDomain K)).mono_set subset_closure

theorem integrableOn_char (χ : HeckeCharacter K) :
    IntegrableOn (fun u : normOneSubgroup K ↦ (χ.toIdele (u : IdeleGroup K) : ℂ))
      (normOneFundamentalDomain K) (normOneMeasure K) :=
  ((continuous_subtype_val.comp (χ.continuous_toIdele.comp
    continuous_subtype_val)).continuousOn.integrableOn_compact
    (isCompact_closure_normOneFundamentalDomain K)).mono_set subset_closure

theorem toIdele_inv (χ : HeckeCharacter K) (x : IdeleGroup K) :
    (χ⁻¹).toIdele x = (χ.toIdele x)⁻¹ :=
  rfl

theorem thetaIntegrand_inv (w : InfinitePlace K) {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    (χ : HeckeCharacter K) (t : {r : ℝ // 0 < r}) (u : normOneSubgroup K) :
    thetaIntegrand w F χ t⁻¹ u =
      ((t : ℝ) : ℂ) * thetaIntegrand w (adelicFourier K F) χ⁻¹ t u⁻¹ := by
  unfold thetaIntegrand
  have hmod : (ideleModule K (moduleSection w t⁻¹ * (u : IdeleGroup K)) : ℝ) = (t : ℝ)⁻¹ := by
    have hu : ideleModule K (u : IdeleGroup K) = 1 := u.2
    rw [map_mul, hu, mul_one, ideleModule_moduleSection]
    rfl
  have hinv : (moduleSection w t⁻¹ * (u : IdeleGroup K))⁻¹ =
      moduleSection w t * ((u⁻¹ : normOneSubgroup K) : IdeleGroup K) := by
    rw [mul_inv, map_inv, inv_inv, InvMemClass.coe_inv, mul_comm]
  have hχ : (χ.toIdele (u : IdeleGroup K) : ℂ) =
      ((χ⁻¹).toIdele ((u⁻¹ : normOneSubgroup K) : IdeleGroup K) : ℂ) := by
    rw [toIdele_inv, InvMemClass.coe_inv, map_inv, inv_inv]
  rw [adelicTheta_eq hF, hmod, hinv, hχ, Complex.ofReal_inv, inv_inv]
  ring

theorem thetaIntegral_inv (w : InfinitePlace K) {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    (χ : HeckeCharacter K) (t : {r : ℝ // 0 < r}) :
    thetaIntegral w F χ t⁻¹ = ((t : ℝ) : ℂ) * thetaIntegral w (adelicFourier K F) χ⁻¹ t := by
  unfold thetaIntegral
  simp_rw [thetaIntegrand_inv w hF χ t]
  rw [integral_const_mul]
  congr 1
  exact setIntegral_inv_eq (h := thetaIntegrand w (adelicFourier K F) χ⁻¹ t)
    (thetaIntegrand_mul_diagonalToNormOne w _ χ⁻¹ t)

theorem thetaIntegral_neg (w : InfinitePlace K) (F : 𝔸[K] → ℂ) (χ : HeckeCharacter K) :
    thetaIntegral w (fun x ↦ F (-x)) χ = thetaIntegral w F χ := by
  funext t
  unfold thetaIntegral thetaIntegrand
  simp only [adelicTheta_neg]

end

end GroundTheory.Global
end

section
open NumberField NumberField.mixedEmbedding IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical nonZeroDivisors Pointwise

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

theorem coe_moduleSection (w : InfinitePlace K) (t : {r : ℝ // 0 < r}) :
    ((moduleSection w t : IdeleGroup K) : 𝔸[K]) = (infiniteAdeleSingle w (posRealElem w t), 1) :=
  coe_infiniteEmbedding w _

theorem toFinite_moduleSection (w : InfinitePlace K) (t : {r : ℝ // 0 < r}) :
    toFinite K (moduleSection w t) = 1 := by
  refine Units.ext ?_
  rw [Units.val_one]
  change ((moduleSection w t : IdeleGroup K) : 𝔸[K]).2 = 1
  rw [coe_moduleSection]

theorem norm_moduleSection_apply (w : InfinitePlace K) (t : {r : ℝ // 0 < r}) (v : InfinitePlace K) :
    ‖((moduleSection w t : IdeleGroup K) : 𝔸[K]).1 v‖ = if v = w then ‖posRealElem w t‖ else 1 := by
  rw [coe_moduleSection]
  change ‖infiniteAdeleSingle w (posRealElem w t) v‖ = _
  rw [infiniteAdeleSingle_apply]
  split_ifs with h
  · subst h
    rw [Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne h, norm_one]

theorem infiniteModule_moduleSection (w : InfinitePlace K) (t : {r : ℝ // 0 < r}) :
    infiniteModule (moduleSection w t) = t := by
  rw [infiniteModule, Finset.prod_eq_single w (fun v _ hv ↦ by
    rw [norm_moduleSection_apply, if_neg hv, one_pow]) (fun h ↦ absurd (Finset.mem_univ w) h),
    norm_moduleSection_apply, if_pos rfl]
  exact norm_posRealElem_pow w t.2.le

theorem norm_moduleSection_apply_le_one (w : InfinitePlace K) {t : {r : ℝ // 0 < r}}
    (ht : (t : ℝ) ≤ 1) (v : InfinitePlace K) :
    ‖((moduleSection w t : IdeleGroup K) : 𝔸[K]).1 v‖ ≤ 1 := by
  rw [norm_moduleSection_apply]
  split_ifs
  · have h := norm_posRealElem_pow w t.2.le
    have hm : w.mult ≠ 0 := by unfold InfinitePlace.mult; split_ifs <;> norm_num
    have h2 : ‖posRealElem w t‖ ^ w.mult ≤ 1 := by rw [h]; exact ht
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hm).1 h2
  · exact le_rfl

theorem normAtPlace_le_norm' (v : InfinitePlace K) (z : mixedSpace K) : normAtPlace v z ≤ ‖z‖ := by
  rw [norm_eq_sup'_normAtPlace]
  exact Finset.le_sup' (fun v ↦ normAtPlace v z) (Finset.mem_univ v)

theorem mixedEmbedding_norm_le_norm_pow (z : mixedSpace K) :
    mixedEmbedding.norm z ≤ ‖z‖ ^ Module.finrank ℚ K := by
  rw [mixedEmbedding.norm_apply, ← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun v _ ↦ pow_nonneg (normAtPlace_nonneg _ _) _)
    fun v _ ↦ pow_le_pow_left₀ (normAtPlace_nonneg _ _) (normAtPlace_le_norm' v z) _

theorem norm_mul_le_of_normAtPlace_le_one {e : mixedSpace K} (he : ∀ v, normAtPlace v e ≤ 1)
    (z : mixedSpace K) : ‖e * z‖ ≤ ‖z‖ := by
  rw [norm_eq_sup'_normAtPlace (e * z)]
  refine Finset.sup'_le _ _ fun v _ ↦ ?_
  rw [map_mul]
  exact (mul_le_of_le_one_left (normAtPlace_nonneg _ _) (he v)).trans (normAtPlace_le_norm' v z)

theorem mixedEmbedding_norm_toInfinite (x : IdeleGroup K) :
    mixedEmbedding.norm (homeomorphMixedSpace K
      ((toInfinite K x : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) = infiniteModule x := by
  rw [mixedEmbedding.norm_apply]
  simp only [normAtPlace_homeomorphMixedSpace]
  rfl

theorem one_le_abs_norm_of_ne_zero {r : 𝓞 K} (hr : r ≠ 0) :
    (1 : ℝ) ≤ |((Algebra.norm ℚ (r : K) : ℚ) : ℝ)| := by
  rw [← Algebra.coe_norm_int]
  have h : Algebra.norm ℤ r ≠ 0 := Algebra.norm_ne_zero_iff.2 hr
  have h1 : (1 : ℤ) ≤ |Algebra.norm ℤ r| := Int.one_le_abs h
  exact_mod_cast h1

theorem exists_decay_bound_tensor_cosetIndicator (w : InfinitePlace K) (φ : 𝓢(mixedSpace K, ℂ))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : 𝔸ᶠ[K]) {C : Set (IdeleGroup K)} (hC : IsCompact C)
    (r : ℕ) :
    ∃ u : K → ℝ, Summable u ∧ ∀ a ∈ C, ∀ t : {x : ℝ // 0 < x}, 1 ≤ (t : ℝ) → ∀ ξ : K, ξ ≠ 0 →
      ‖schwartzBruhatTensor φ (cosetIndicator I b)
        ((moduleSection w t * a) • algebraMap K 𝔸[K] ξ)‖ ≤ ((t : ℝ) ^ r)⁻¹ * u ξ := by

  set S : Set 𝔸ᶠ[K] := (fun p : IdeleGroup K × 𝔸ᶠ[K] ↦
      ((IdeleGroup.toFinite K p.1⁻¹ : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * p.2) ''
    (C ×ˢ (b +ᵥ (idealFiniteAdeles I : Set 𝔸ᶠ[K])))
  have hS : IsCompact S := (hC.prod ((isCompact_idealFiniteAdeles I).vadd b)).image
    ((Units.continuous_val.comp ((IdeleGroup.continuous_toFinite (K := K)).comp
      (continuous_inv.comp continuous_fst))).mul continuous_snd)
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hS
  set dK := algebraMap (𝓞 K) K d
  have hdK : dK ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0
  set J : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ dK⁻¹)
    ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr (inv_ne_zero hdK))
  have hJ : ∀ a ∈ C, ∀ ξ : K,
      ((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ - b ∈
        idealFiniteAdeles I → ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K) := by
    intro a ha ξ hξ
    have hmem : algebraMap K 𝔸ᶠ[K] ξ ∈ S := by
      refine ⟨(a, ((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ),
        ⟨ha, mem_vadd_idealFiniteAdeles.mpr hξ⟩, ?_⟩
      simp only [map_inv, Units.inv_mul_cancel_left]
    have h1 := hd _ hmem
    rw [← map_mul] at h1
    have h2 : dK * ξ ∈ ((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [← algebraMap_mem_idealFiniteAdeles_iff, ← SetLike.mem_coe, idealFiniteAdeles_one]
      exact h1
    rw [Units.val_one] at h2
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp h2
    refine (FractionalIdeal.mem_spanSingleton _).mpr ⟨r, ?_⟩
    rw [Algebra.smul_def, hr, mul_comm dK, mul_assoc, mul_inv_cancel₀ hdK, mul_one]

  have hNd : ((Algebra.norm ℚ dK : ℚ) : ℝ) ≠ 0 := by
    rw [Rat.cast_ne_zero]
    exact (Algebra.norm_ne_zero_iff).2 hdK
  set κ₀ : ℝ := |((Algebra.norm ℚ dK : ℚ) : ℝ)|⁻¹
  have hκ₀ : 0 < κ₀ := inv_pos.2 (abs_pos.2 hNd)
  have hNξ : ∀ ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K), ξ ≠ 0 →
      κ₀ ≤ mixedEmbedding.norm (mixedEmbedding K ξ) := by
    intro ξ hξ hξ0
    obtain ⟨r', hr'⟩ := (FractionalIdeal.mem_spanSingleton _).1 hξ
    have hr'0 : r' ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hr'
      exact hξ0 hr'.symm
    have hmul : Algebra.norm ℚ dK * Algebra.norm ℚ ξ = Algebra.norm ℚ (r' : K) := by
      rw [← map_mul, ← hr', Algebra.smul_def, mul_left_comm, mul_inv_cancel₀ hdK, mul_one]
    have hξN : ((Algebra.norm ℚ ξ : ℚ) : ℝ) =
        ((Algebra.norm ℚ (r' : K) : ℚ) : ℝ) * ((Algebra.norm ℚ dK : ℚ) : ℝ)⁻¹ := by
      rw [← hmul, Rat.cast_mul]
      field_simp
    rw [mixedEmbedding.norm_eq_norm, Rat.cast_abs, hξN, abs_mul, abs_inv]
    exact le_mul_of_one_le_left (by positivity) (one_le_abs_norm_of_ne_zero hr'0)

  have hcm : Continuous fun a : IdeleGroup K ↦ (infiniteModule a)⁻¹ :=
    continuous_infiniteModule.inv₀ fun a ↦ (infiniteModule_pos a).ne'
  obtain ⟨B₂, hB₂⟩ := hC.exists_bound_of_continuousOn hcm.continuousOn
  set m : ℝ := (max B₂ 1)⁻¹
  have hm0 : 0 < m := inv_pos.2 (zero_lt_one.trans_le (le_max_right _ _))
  have hmC : ∀ a ∈ C, m ≤ infiniteModule a := by
    intro a ha
    have h1 : (infiniteModule a)⁻¹ ≤ max B₂ 1 := by
      have := hB₂ a ha
      rw [Real.norm_of_nonneg (inv_nonneg.2 (infiniteModule_pos a).le)] at this
      exact this.trans (le_max_left _ _)
    exact inv_le_of_inv_le₀ (infiniteModule_pos a) h1

  set k := Module.finrank ℤ (idealLattice K J) + 1
  set n := Module.finrank ℚ K
  obtain ⟨A, hA, hφ⟩ := exists_norm_le_inv_one_add_pow φ (k + n * r)
  have hcont : Continuous fun a : IdeleGroup K ↦ ‖homeomorphMixedSpace K
      ((IdeleGroup.toInfinite K a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)‖ :=
    continuous_norm.comp ((homeomorphMixedSpace K).continuous.comp (Units.continuous_val.comp
      ((IdeleGroup.continuous_toInfinite (K := K)).comp continuous_inv)))
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
  set B' := max B 1
  have hB'1 : 1 ≤ B' := le_max_right _ _
  have hB'0 : 0 < B' := zero_lt_one.trans_le hB'1
  set κ := m * κ₀
  have hκ : 0 < κ := mul_pos hm0 hκ₀
  refine ⟨fun ξ ↦ if ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K) then
      A * B' ^ k * (κ ^ r)⁻¹ * ((1 + ‖mixedEmbedding K ξ‖) ^ k)⁻¹ else 0, ?_, ?_⟩
  · exact summable_ite_mem_of_summable_idealLattice J
      (h := fun x ↦ A * B' ^ k * (κ ^ r)⁻¹ * ((1 + ‖x‖) ^ k)⁻¹)
      ((summable_inv_one_add_norm_pow_idealLattice J).mul_left (A * B' ^ k * (κ ^ r)⁻¹))
  intro a ha t ht ξ hξ0
  set y := moduleSection w t * a
  set c := homeomorphMixedSpace K
    ((IdeleGroup.toInfinite K y : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)
  set c' := homeomorphMixedSpace K
    ((IdeleGroup.toInfinite K a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)
  set e' := homeomorphMixedSpace K
    ((IdeleGroup.toInfinite K (moduleSection w t⁻¹) : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)
  have hcc : c' * (e' * c) = 1 := by
    rw [← homeomorphMixedSpace_mul, ← homeomorphMixedSpace_mul, ← Units.val_mul, ← Units.val_mul,
      ← map_mul, ← map_mul, map_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel_right, inv_mul_cancel,
      map_one, Units.val_one, homeomorphMixedSpace_apply, map_one]
  have he' : ∀ v, normAtPlace v e' ≤ 1 := by
    intro v
    rw [normAtPlace_homeomorphMixedSpace]
    refine norm_moduleSection_apply_le_one w ?_ v
    change (t : ℝ)⁻¹ ≤ 1
    exact inv_le_one_of_one_le₀ ht
  have hval : schwartzBruhatTensor φ (cosetIndicator I b) (y • algebraMap K 𝔸[K] ξ) =
      φ (c * mixedEmbedding K ξ) * cosetIndicator I b
        (((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ) := by
    have h1 : (y • algebraMap K 𝔸[K] ξ).1 = ((IdeleGroup.toInfinite K y : (InfiniteAdeleRing K)ˣ) :
        InfiniteAdeleRing K) * algebraMap K (InfiniteAdeleRing K) ξ := rfl
    have h2 : (y • algebraMap K 𝔸[K] ξ).2 =
        ((IdeleGroup.toFinite K y : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ := rfl
    have h3 : IdeleGroup.toFinite K y = IdeleGroup.toFinite K a := by
      rw [map_mul, toFinite_moduleSection, one_mul]
    simp only [schwartzBruhatTensor]
    rw [h1, h2, h3, homeomorphMixedSpace_mul, homeomorphMixedSpace_algebraMap]
  rw [hval, cosetIndicator_apply]
  beta_reduce
  by_cases hm : ((IdeleGroup.toFinite K a : (𝔸ᶠ[K])ˣ) : 𝔸ᶠ[K]) * algebraMap K 𝔸ᶠ[K] ξ - b ∈
      idealFiniteAdeles I
  · have hξJ := hJ a ha ξ hm
    rw [if_pos hm, if_pos hξJ, mul_one]
    set x := mixedEmbedding K ξ
    set z := c * x
    have hx : ‖x‖ ≤ B' * ‖z‖ := by
      calc ‖x‖ = ‖c' * (e' * z)‖ := by rw [← mul_assoc, ← mul_assoc, mul_assoc c', hcc, one_mul]
        _ ≤ ‖c'‖ * ‖e' * z‖ := norm_mul_le _ _
        _ ≤ B' * ‖z‖ :=
          mul_le_mul (((norm_norm _).symm.trans_le (hB a ha)).trans (le_max_left _ _))
            (norm_mul_le_of_normAtPlace_le_one he' z) (norm_nonneg _) hB'0.le
    have hN : (t : ℝ) * κ ≤ mixedEmbedding.norm z := by
      rw [map_mul, mixedEmbedding_norm_toInfinite, infiniteModule_mul,
        infiniteModule_moduleSection]
      have h1 := hmC a ha
      have h2 := hNξ ξ hξJ hξ0
      have ht0 : (0 : ℝ) ≤ t := t.2.le
      calc (t : ℝ) * κ = (t : ℝ) * m * κ₀ := by rw [mul_assoc]
        _ ≤ (t : ℝ) * infiniteModule a * mixedEmbedding.norm x :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 ht0) h2 hκ₀.le
            (mul_nonneg ht0 (infiniteModule_pos a).le)
    have htκ : 0 < (t : ℝ) * κ := mul_pos t.2 hκ
    have hz : (t : ℝ) * κ ≤ (1 + ‖z‖) ^ n :=
      hN.trans ((mixedEmbedding_norm_le_norm_pow z).trans
        (pow_le_pow_left₀ (norm_nonneg _) (by linarith [norm_nonneg z]) n))
    have hx' : (1 + ‖x‖) / B' ≤ 1 + ‖z‖ := by
      rw [div_le_iff₀ hB'0]
      nlinarith [norm_nonneg z]
    have h1 : ((1 + ‖z‖) ^ k)⁻¹ ≤ (((1 + ‖x‖) / B') ^ k)⁻¹ :=
      inv_anti₀ (pow_pos (div_pos (by positivity) hB'0) k)
        (pow_le_pow_left₀ (div_pos (by positivity) hB'0).le hx' k)
    have h2 : (((1 + ‖z‖) ^ n) ^ r)⁻¹ ≤ (((t : ℝ) * κ) ^ r)⁻¹ :=
      inv_anti₀ (pow_pos htκ r) (pow_le_pow_left₀ htκ.le hz r)
    calc ‖φ z‖ ≤ A * ((1 + ‖z‖) ^ (k + n * r))⁻¹ := hφ z
      _ = A * (((1 + ‖z‖) ^ k)⁻¹ * (((1 + ‖z‖) ^ n) ^ r)⁻¹) := by
          rw [pow_add, pow_mul, mul_inv]
      _ ≤ A * ((((1 + ‖x‖) / B') ^ k)⁻¹ * (((t : ℝ) * κ) ^ r)⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (inv_nonneg.2 (pow_nonneg (pow_nonneg
            (by positivity) n) r)) (inv_nonneg.2 (pow_nonneg (div_pos (by positivity) hB'0).le k))) hA
      _ = ((t : ℝ) ^ r)⁻¹ * (A * B' ^ k * (κ ^ r)⁻¹ * ((1 + ‖x‖) ^ k)⁻¹) := by
          rw [div_pow, inv_div, mul_pow, mul_inv]
          ring
  · rw [if_neg hm, mul_zero, norm_zero]
    split_ifs
    · exact mul_nonneg (inv_nonneg.2 (pow_nonneg t.2.le r)) (mul_nonneg (mul_nonneg (mul_nonneg hA
        (pow_nonneg hB'0.le k)) (inv_nonneg.2 (pow_nonneg hκ.le r))) (inv_nonneg.2 (by positivity)))
    · rw [mul_zero]

theorem exists_decay_bound (w : InfinitePlace K) {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    {C : Set (IdeleGroup K)} (hC : IsCompact C) (r : ℕ) :
    ∃ u : K → ℝ, Summable u ∧ ∀ a ∈ C, ∀ t : {x : ℝ // 0 < x}, 1 ≤ (t : ℝ) → ∀ ξ : K, ξ ≠ 0 →
      ‖F ((moduleSection w t * a) • algebraMap K 𝔸[K] ξ)‖ ≤ ((t : ℝ) ^ r)⁻¹ * u ξ := by
  have hF' := schwartzBruhat_le_span_cosetIndicator hF
  clear hF
  induction hF' using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, I, b, rfl⟩ := hG
    exact exists_decay_bound_tensor_cosetIndicator w φ I b hC r
  | zero => exact ⟨0, summable_zero, fun _ _ _ _ _ _ ↦ by simp⟩
  | add G H _ _ hG hH =>
    obtain ⟨u, hu, hGu⟩ := hG
    obtain ⟨v, hv, hHv⟩ := hH
    refine ⟨u + v, hu.add hv, fun a ha t ht ξ hξ ↦ ?_⟩
    rw [Pi.add_apply, Pi.add_apply, mul_add]
    exact (norm_add_le _ _).trans (add_le_add (hGu a ha t ht ξ hξ) (hHv a ha t ht ξ hξ))
  | smul c G _ hG =>
    obtain ⟨u, hu, hGu⟩ := hG
    refine ⟨fun ξ ↦ ‖c‖ * u ξ, hu.mul_left _, fun a ha t ht ξ hξ ↦ ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hGu a ha t ht ξ hξ) (norm_nonneg c)

theorem exists_norm_adelicTheta_sub_le (w : InfinitePlace K) {F : 𝔸[K] → ℂ}
    (hF : F ∈ schwartzBruhat K) {C : Set (IdeleGroup K)} (hC : IsCompact C) (r : ℕ) :
    ∃ M : ℝ, ∀ a ∈ C, ∀ t : {x : ℝ // 0 < x}, 1 ≤ (t : ℝ) →
      ‖adelicTheta F (moduleSection w t * a) - F 0‖ ≤ ((t : ℝ) ^ r)⁻¹ * M := by
  obtain ⟨u, hu, hFu⟩ := exists_decay_bound w hF hC r
  refine ⟨∑' ξ, |u ξ|, fun a ha t ht ↦ ?_⟩
  have hs : Summable fun ξ : K ↦ F ((moduleSection w t * a) • algebraMap K 𝔸[K] ξ) :=
    (summable_norm_smul_algebraMap _ hF).of_norm
  rw [adelicTheta, hs.tsum_eq_add_tsum_ite 0, smul_algebraMap_zero, add_sub_cancel_left,
    ← tsum_mul_left]
  refine tsum_of_norm_bounded ((hu.abs.mul_left _).hasSum) fun ξ ↦ ?_
  have ht0 : 0 < ((t : ℝ) ^ r)⁻¹ := inv_pos.2 (pow_pos t.2 r)
  split_ifs with h
  · rw [norm_zero]
    exact mul_nonneg ht0.le (abs_nonneg _)
  · exact (hFu a ha t ht ξ h).trans (mul_le_mul_of_nonneg_left (le_abs_self _) ht0.le)

def thetaConstant (F : 𝔸[K] → ℂ) (χ : HeckeCharacter K) : ℂ :=
  F 0 * ∫ u in normOneFundamentalDomain K, (χ.toIdele (u : IdeleGroup K) : ℂ) ∂normOneMeasure K

theorem thetaIntegral_sub_thetaConstant (w : InfinitePlace K) {F : 𝔸[K] → ℂ}
    (hF : F ∈ schwartzBruhat K) (χ : HeckeCharacter K) (t : {r : ℝ // 0 < r}) :
    thetaIntegral w F χ t - thetaConstant F χ =
      ∫ u in normOneFundamentalDomain K, (adelicTheta F (moduleSection w t * (u : IdeleGroup K)) -
        F 0) * (χ.toIdele (u : IdeleGroup K) : ℂ) ∂normOneMeasure K := by
  rw [thetaIntegral, thetaConstant, ← integral_const_mul,
    ← integral_sub (integrableOn_thetaIntegrand w hF χ t) ((integrableOn_char χ).const_mul _)]
  refine integral_congr_ae (Eventually.of_forall fun u ↦ ?_)
  simp only [thetaIntegrand]
  ring

theorem exists_norm_thetaIntegral_sub_le (w : InfinitePlace K) {F : 𝔸[K] → ℂ}
    (hF : F ∈ schwartzBruhat K) (χ : HeckeCharacter K) (r : ℕ) :
    ∃ M : ℝ, ∀ t : {x : ℝ // 0 < x}, 1 ≤ (t : ℝ) →
      ‖thetaIntegral w F χ t - thetaConstant F χ‖ ≤ ((t : ℝ) ^ r)⁻¹ * M := by
  have hC : IsCompact ((Subtype.val : normOneSubgroup K → IdeleGroup K) ''
      closure (normOneFundamentalDomain K)) :=
    (isCompact_closure_normOneFundamentalDomain K).image continuous_subtype_val
  obtain ⟨M, hM⟩ := exists_norm_adelicTheta_sub_le w hF hC r
  refine ⟨M * (normOneMeasure K).real (normOneFundamentalDomain K), fun t ht ↦ ?_⟩
  rw [thetaIntegral_sub_thetaConstant w hF χ t, ← mul_assoc]
  refine norm_setIntegral_le_of_norm_le_const (normOneMeasure_normOneFundamentalDomain_lt_top K)
    fun u hu ↦ ?_
  rw [norm_mul, Circle.norm_coe, mul_one]
  exact hM _ ⟨u, subset_closure hu, rfl⟩ t ht

theorem continuous_thetaIntegral (w : InfinitePlace K) {F : 𝔸[K] → ℂ}
    (hF : F ∈ schwartzBruhat K) (χ : HeckeCharacter K) : Continuous (thetaIntegral w F χ) := by
  refine continuous_iff_continuousAt.2 fun t₀ ↦ ?_
  obtain ⟨N, hN, ht₀N⟩ := exists_compact_mem_nhds t₀
  have hC : IsCompact ((fun p : {r : ℝ // 0 < r} × normOneSubgroup K ↦
      moduleSection w p.1 * (p.2 : IdeleGroup K)) '' (N ×ˢ closure (normOneFundamentalDomain K))) :=
    (hN.prod (isCompact_closure_normOneFundamentalDomain K)).image
      (((continuous_moduleSection w).comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd))
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (continuous_adelicTheta hF).continuousOn
  have hfin : IsFiniteMeasure ((normOneMeasure K).restrict (normOneFundamentalDomain K)) :=
    isFiniteMeasure_restrict.2 (normOneMeasure_normOneFundamentalDomain_lt_top K).ne
  show ContinuousAt (fun t ↦ ∫ u, thetaIntegrand w F χ t u
    ∂((normOneMeasure K).restrict (normOneFundamentalDomain K))) t₀
  refine continuousAt_of_dominated (bound := fun _ ↦ M) ?_ ?_ (integrable_const M) ?_
  · exact Eventually.of_forall fun t ↦ (continuous_thetaIntegrand w hF χ t).aestronglyMeasurable
  · filter_upwards [ht₀N] with t ht
    filter_upwards [ae_restrict_mem (measurableSet_normOneFundamentalDomain K)] with u hu
    rw [thetaIntegrand, norm_mul, Circle.norm_coe, mul_one]
    exact hM _ ⟨(t, u), ⟨ht, subset_closure hu⟩, rfl⟩
  · refine Eventually.of_forall fun u ↦ Continuous.continuousAt ?_
    exact ((continuous_adelicTheta hF).comp ((continuous_moduleSection w).mul continuous_const)).mul
      continuous_const

end

end GroundTheory.Global
end
