import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEmbApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogClassNumberLeLogAbsDiscrDiv
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFieldIdealsPrincipal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SzAdjoinRootOfUnity
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SzFieldRangeEmbedding
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetTypeNormPrincipal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeAdjoinKthRootStatement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsImagQuadraticHost
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeMonotone
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeSupAdd
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberLeAbsDiscrOfFinrankEqTwo
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NatCastMulFinrankMemDifferentIdeal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeckeIdealEqOfRay
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LogRootDiscrLeOfNatCastMemDifferentIdeal

section
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_field_ideals_principal : ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (F : IntermediateField ℚ ℂ) (a b : ℝ), Sz F a b → (∀ x, φ x ∈ F) → ∃ F' : IntermediateField ℚ ℂ, F ≤ F' ∧ Sz F' (a + Real.log (classNumber E)) (b + Real.log (classNumber E)) ∧ ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K], F' ≤ K → ∀ 𝔞 : Ideal (𝓞 E), ∃ β : K, Submodule.span (𝓞 K) {β} = Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = φ (a : E)} := by
  first | exact @GlobalTheory.FieldSize.exists_sz_capitulation | exact GlobalTheory.FieldSize.exists_sz_capitulation | (intros; apply GlobalTheory.FieldSize.exists_sz_capitulation <;> assumption)
end

section
section
open NumberField IsDedekindDomain GlobalTheory.FieldSize GlobalTheory.Mem
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory.FieldSize

theorem exists_eq_top_of_root_step {G ι : Type} [CommGroup G] [Finite G] [Preorder ι] (C : ι → Subgroup G)
    (hC : Monotone C) (S : ι → ℝ → Prop) (hS : ∀ i s t, s ≤ t → S i s → S i t)
    (step : ∀ i t (c : G) (k : ℕ), S i t → 0 < k → c ^ k ∈ C i → ∃ j, i ≤ j ∧ S j (t + Real.log k) ∧ c ∈ C j) :
    ∀ (m : ℕ) (i : ι) (t : ℝ), (C i).index = m → S i t → ∃ j, i ≤ j ∧ S j (t + Real.log m) ∧ C j = ⊤ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i t hm hi
    by_cases htop : C i = ⊤
    · exact ⟨i, le_rfl, hS i t _ (le_add_of_nonneg_right (Real.log_natCast_nonneg m)) hi, htop⟩
    obtain ⟨c, hc⟩ : ∃ c, c ∉ C i := by
      by_contra h
      push Not at h
      exact htop (eq_top_iff.2 fun x _ => h x)
    set D : Subgroup G := C i ⊔ Subgroup.zpowers c with hD
    have hle : C i ≤ D := le_sup_left
    have hcD : c ∈ D := (le_sup_right : Subgroup.zpowers c ≤ D) (Subgroup.mem_zpowers c)
    have hmul := Subgroup.relIndex_mul_index hle
    set k := (C i).relIndex D with hk
    have hm0 : m ≠ 0 := hm ▸ Subgroup.index_ne_zero_of_finite
    have hk0 : k ≠ 0 := by
      intro h
      rw [h, zero_mul, hm] at hmul
      exact hm0 hmul.symm
    have hk1 : k ≠ 1 := fun h => hc (Subgroup.relIndex_eq_one.1 h hcD)
    obtain ⟨j, hij, hj, hcj⟩ := step i t c k hi (Nat.pos_of_ne_zero hk0) (Subgroup.pow_relIndex_mem _ hcD)
    have hDj : D ≤ C j := sup_le (hC hij) ((Subgroup.zpowers_le_of_mem hcj))
    have hD0 : D.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hj0 : (C j).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hidx : (C j).index ≤ D.index := Nat.le_of_dvd (Nat.pos_of_ne_zero hD0) (Subgroup.index_dvd_of_le hDj)
    have hlt : (C j).index < m := by
      rw [← hm, ← hmul]
      have : 2 ≤ k := by omega
      have := Nat.pos_of_ne_zero hD0
      nlinarith
    obtain ⟨l, hjl, hl, hl'⟩ := ih _ hlt j _ rfl hj
    refine ⟨l, hij.trans hjl, hS l _ _ ?_ hl, hl'⟩
    rw [add_assoc, ← Real.log_mul (by exact_mod_cast hk0) (by exact_mod_cast hj0)]
    refine add_le_add le_rfl (Real.log_le_log (by positivity) ?_)
    rw [← hm, ← hmul]
    exact_mod_cast Nat.mul_le_mul_left k hidx

theorem Sz.weaken {F : IntermediateField ℚ ℂ} {a b a' b' : ℝ} (h : Sz F a b) (ha : a ≤ a') (hb : b ≤ b') :
    Sz F a' b' := by
  obtain ⟨h0, h1, h2⟩ := h
  exact ⟨h0, h1.trans ha, h2.trans hb⟩

section

variable {E : Type} [Field E] [NumberField E] (r : (E →+* ℂ) → ℕ) (n : ℕ)

noncomputable def typeNormMod (K : IntermediateField ℚ ℂ) (𝔞 : Ideal (𝓞 E)) : Submodule (𝓞 K) K :=
  ∏ τ : E →+* ℂ, Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} ^ r τ

def GenTypeNorm (K : IntermediateField ℚ ℂ) (β : K) (𝔞 : Ideal (𝓞 E)) : Prop :=
  Submodule.span (𝓞 K) {β} = typeNormMod r K 𝔞 ∧ ∀ σ : K →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ n

variable {r n}

theorem typeNormMod_eq (K : IntermediateField ℚ ℂ) [NumberField K] (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K)
    (𝔞 : Ideal (𝓞 E)) :
    typeNormMod r K 𝔞 = ∏ τ : E →+* ℂ, extendIdealHom (τ.codRestrict K (hK τ)) 𝔞 ^ r τ := by
  refine Finset.prod_congr rfl fun τ _ => ?_
  congr 1
  refine Eq.trans ?_ (span_image_eq_coeSubmodule_map (τ.codRestrict K (hK τ)) 𝔞)
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Subtype.ext_iff]
  rfl

theorem typeNormMod_mul (K : IntermediateField ℚ ℂ) [NumberField K] (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K)
    (I J : Ideal (𝓞 E)) : typeNormMod r K (I * J) = typeNormMod r K I * typeNormMod r K J := by
  simp only [typeNormMod_eq K hK, map_mul, mul_pow, Finset.prod_mul_distrib]

theorem typeNormMod_pow (K : IntermediateField ℚ ℂ) [NumberField K] (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K)
    (I : Ideal (𝓞 E)) (k : ℕ) : typeNormMod r K (I ^ k) = typeNormMod r K I ^ k := by
  simp only [typeNormMod_eq K hK, map_pow, ← Finset.prod_pow, ← pow_mul, mul_comm]

theorem GenTypeNorm.mul {K : IntermediateField ℚ ℂ} [NumberField K] (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K)
    {I J : Ideal (𝓞 E)} {β γ : K} (h1 : GenTypeNorm r n K β I) (h2 : GenTypeNorm r n K γ J) :
    GenTypeNorm r n K (β * γ) (I * J) := by
  refine ⟨?_, fun σ => ?_⟩
  · rw [typeNormMod_mul K hK, ← h1.1, ← h2.1, Submodule.span_mul_span, Set.singleton_mul_singleton]
  · rw [map_mul, map_mul, norm_mul, mul_pow, h1.2, h2.2, Nat.cast_mul, mul_pow]

theorem GenTypeNorm.cancel {K : IntermediateField ℚ ℂ} [NumberField K] (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K)
    {I J : Ideal (𝓞 E)} {β γ : K} (hβ : β ≠ 0) (h1 : GenTypeNorm r n K β I) (h2 : GenTypeNorm r n K γ (I * J)) :
    GenTypeNorm r n K (β⁻¹ * γ) J := by
  refine ⟨?_, fun σ => ?_⟩
  · rw [← Set.singleton_mul_singleton, ← Submodule.span_mul_span, h2.1, typeNormMod_mul K hK, ← h1.1, ← mul_assoc,
      Submodule.span_mul_span, Set.singleton_mul_singleton, inv_mul_cancel₀ hβ, ← Submodule.one_eq_span, one_mul]
  · have h3 := h2.2 σ
    rw [map_mul, Nat.cast_mul, mul_pow, ← h1.2 σ] at h3
    have h4 : ‖σ β‖ ≠ 0 := by
      rw [norm_ne_zero_iff, map_ne_zero]; exact hβ
    rw [map_mul, map_inv₀, norm_mul, norm_inv, mul_pow, h3]
    field_simp

theorem GenTypeNorm.root {K : IntermediateField ℚ ℂ} [NumberField K] (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K)
    {I : Ideal (𝓞 E)} {β : K} {k : ℕ} (hk : 0 < k) (hβ : β ≠ 0) (h : GenTypeNorm r n K (β ^ k) (I ^ k)) :
    GenTypeNorm r n K β I := by
  refine ⟨?_, fun σ => ?_⟩
  · refine (GlobalTheory.submodule_eq_span_of_pow_eq_span_pow K _ β k hk hβ ?_ ?_).symm
    · rw [typeNormMod_eq K hK]
      exact fg_prod_pow _ _ _ fun τ => extendIdealHom_fg _ _
    · rw [← typeNormMod_pow K hK, h.1]
  · have := h.2 σ
    rw [map_pow, map_pow, norm_pow, Nat.cast_pow, ← pow_mul, ← pow_mul,
      mul_comm _ 2, mul_comm _ n, pow_mul, pow_mul] at this
    exact (pow_left_inj₀ (by positivity) (by positivity) hk.ne').1 this

theorem genTypeNorm_span [IsCMField E] [IsGalois ℚ E] (hr : ∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n)
    (K : IntermediateField ℚ ℂ) [NumberField K] (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K) (a : 𝓞 E) :
    GenTypeNorm r n K (∏ τ : E →+* ℂ, (⟨τ (a : E), hK τ _⟩ : K) ^ r τ) (Ideal.span {a}) := by
  refine ⟨?_, fun σ => ?_⟩
  · simp only [typeNormMod_eq K hK, extendIdealHom_span, span_singleton_prod_pow]
    rfl
  · have := norm_typeNorm_sq_eq E r n hr K hK (a : E) σ
    rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs]
    rw [← Algebra.coe_norm_int] at this
    rw [Rat.cast_intCast] at this
    exact this

variable (r n)

def HasTypeNormGen (F : IntermediateField ℚ ℂ) (𝔞 : Ideal (𝓞 E)) : Prop :=
  ∃ β : F, β ≠ 0 ∧ ∀ (K : IntermediateField ℚ ℂ) [NumberField K] (h : F ≤ K),
    GenTypeNorm r n K (IntermediateField.inclusion h β) 𝔞

variable {r n}

theorem HasTypeNormGen.mono {F F' : IntermediateField ℚ ℂ} (h : F ≤ F') {I : Ideal (𝓞 E)}
    (hI : HasTypeNormGen r n F I) : HasTypeNormGen r n F' I := by
  obtain ⟨β, h0, hβ⟩ := hI
  exact ⟨IntermediateField.inclusion h β, (map_ne_zero _).2 h0, fun K _ hK => hβ K (h.trans hK)⟩

theorem HasTypeNormGen.mul {F : IntermediateField ℚ ℂ} (hF : ∀ (τ : E →+* ℂ) x, τ x ∈ F) {I J : Ideal (𝓞 E)}
    (hI : HasTypeNormGen r n F I) (hJ : HasTypeNormGen r n F J) : HasTypeNormGen r n F (I * J) := by
  obtain ⟨β, h0, hβ⟩ := hI
  obtain ⟨γ, h1, hγ⟩ := hJ
  refine ⟨β * γ, mul_ne_zero h0 h1, fun K _ hK => ?_⟩
  rw [map_mul]
  exact (hβ K hK).mul (fun τ x => hK (hF τ x)) (hγ K hK)

theorem HasTypeNormGen.cancel {F : IntermediateField ℚ ℂ} (hF : ∀ (τ : E →+* ℂ) x, τ x ∈ F) {I J : Ideal (𝓞 E)}
    (hI : HasTypeNormGen r n F I) (hJ : HasTypeNormGen r n F (I * J)) : HasTypeNormGen r n F J := by
  obtain ⟨β, h0, hβ⟩ := hI
  obtain ⟨γ, h1, hγ⟩ := hJ
  refine ⟨β⁻¹ * γ, mul_ne_zero (inv_ne_zero h0) h1, fun K _ hK => ?_⟩
  rw [map_mul, map_inv₀]
  exact (hβ K hK).cancel (fun τ x => hK (hF τ x)) ((map_ne_zero _).2 h0) (hγ K hK)

theorem hasTypeNormGen_span [IsCMField E] [IsGalois ℚ E] (hr : ∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n)
    {F : IntermediateField ℚ ℂ} (hF : ∀ (τ : E →+* ℂ) x, τ x ∈ F) {a : 𝓞 E} (ha : a ≠ 0) :
    HasTypeNormGen r n F (Ideal.span {a}) := by
  refine ⟨∏ τ : E →+* ℂ, (⟨τ (a : E), hF τ _⟩ : F) ^ r τ, ?_, fun K _ hK => ?_⟩
  · refine Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ ?_
    intro h
    have h' : τ (a : E) = 0 := congrArg Subtype.val h
    rw [map_eq_zero] at h'
    exact ha (by exact_mod_cast h')
  · rw [map_prod]
    simp only [map_pow]
    exact genTypeNorm_span hr K (fun τ x => hK (hF τ x)) a

theorem HasTypeNormGen.hasTypeNormGen_of_class_eq [IsCMField E] [IsGalois ℚ E]
    (hr : ∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n)
    {F : IntermediateField ℚ ℂ} (hF : ∀ (τ : E →+* ℂ) x, τ x ∈ F) {I J : (Ideal (𝓞 E))⁰}
    (h : ClassGroup.mk0 I = ClassGroup.mk0 J) (hJ : HasTypeNormGen r n F (J : Ideal (𝓞 E))) :
    HasTypeNormGen r n F (I : Ideal (𝓞 E)) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 h
  refine (hasTypeNormGen_span hr hF hx).cancel hF ?_
  rw [hxy]
  exact (hasTypeNormGen_span hr hF hy).mul hF hJ

def typeNormClasses [IsCMField E] [IsGalois ℚ E] (hr : ∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n)
    (F : {F : IntermediateField ℚ ℂ // ∀ (τ : E →+* ℂ) x, τ x ∈ F}) : Subgroup (ClassGroup (𝓞 E)) where
  carrier := {c | ∃ I : (Ideal (𝓞 E))⁰, ClassGroup.mk0 I = c ∧ HasTypeNormGen r n F.1 (I : Ideal (𝓞 E))}
  one_mem' := ⟨1, map_one _, by
    have := hasTypeNormGen_span hr F.2 (a := 1) one_ne_zero
    rw [Ideal.span_singleton_one, ← Ideal.one_eq_top] at this
    exact this⟩
  mul_mem' := by
    rintro _ _ ⟨I, rfl, hI⟩ ⟨J, rfl, hJ⟩
    exact ⟨I * J, map_mul _ _ _, hI.mul F.2 hJ⟩
  inv_mem' := by
    rintro _ ⟨I, rfl, hI⟩
    obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective (ClassGroup.mk0 I)⁻¹
    refine ⟨J, hJ, hI.cancel F.2 ?_⟩
    have h1 := hasTypeNormGen_span hr F.2 (a := 1) one_ne_zero
    rw [Ideal.span_singleton_one, ← Ideal.one_eq_top] at h1
    exact HasTypeNormGen.hasTypeNormGen_of_class_eq hr F.2 (I := I * J) (J := 1) (by rw [map_mul, hJ, mul_inv_cancel, map_one]) h1

end

theorem exists_sz_typeNorm_principal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (r : (E →+* ℂ) → ℕ) (n : ℕ), (∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n) → ∀ (F : IntermediateField ℚ ℂ) (a b : ℝ), Sz F a b → (∀ (τ : E →+* ℂ) x, τ x ∈ F) → ∃ F' : IntermediateField ℚ ℂ, F ≤ F' ∧ Sz F' (a + Real.log (classNumber E)) (b + Real.log (classNumber E)) ∧ ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K], F' ≤ K → ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → ∃ β : K, β ≠ 0 ∧ Submodule.span (𝓞 K) {β} = ∏ τ : E →+* ℂ, Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} ^ r τ ∧ ∀ σ : K →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ n := by
  intro E _ _ _ _ r n hr F a b hF hE
  have key := exists_eq_top_of_root_step (typeNormClasses hr)
    (fun i j hij c ⟨I, hI, h⟩ => ⟨I, hI, h.mono hij⟩) (fun i t => Sz i.1 (a + t) (b + t))
    (fun i s t hst h => h.weaken (by linarith) (by linarith)) ?_ _ ⟨F, hE⟩ 0 rfl (by simpa using hF)
  · obtain ⟨j, hj, hS, htop⟩ := key
    have hle : Real.log ((typeNormClasses hr ⟨F, hE⟩).index) ≤ Real.log (classNumber E) := by
      refine Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) ?_
      have := Nat.le_of_dvd Nat.card_pos (typeNormClasses hr ⟨F, hE⟩).index_dvd_card
      rw [Nat.card_eq_fintype_card] at this
      exact_mod_cast this
    refine ⟨j.1, hj, Sz.weaken hS (by linarith) (by linarith), fun K _ hK 𝔞 h𝔞 => ?_⟩
    have : NumberField K := NumberField.mk
    let I : (Ideal (𝓞 E))⁰ := ⟨𝔞, mem_nonZeroDivisors_of_ne_zero h𝔞⟩
    obtain ⟨J, hJ, hJ'⟩ : ClassGroup.mk0 I ∈ typeNormClasses hr j := htop ▸ Subgroup.mem_top _
    obtain ⟨β, h0, hβ⟩ := HasTypeNormGen.hasTypeNormGen_of_class_eq hr j.2 hJ.symm hJ'
    exact ⟨IntermediateField.inclusion hK β, (map_ne_zero _).2 h0, hβ K hK⟩
  · rintro ⟨L, hL⟩ t c k hS hk ⟨J, hJ, hJ'⟩
    obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
    obtain ⟨y, hy0, hy⟩ := HasTypeNormGen.hasTypeNormGen_of_class_eq hr hL (I := I ^ k) (by rw [map_pow, hJ]) hJ'
    obtain ⟨z, hz⟩ : ∃ z : ℂ, z ^ k = (y : ℂ) := IsAlgClosed.exists_pow_nat_eq _ hk
    have : FiniteDimensional ℚ L := hS.1
    have : NumberField L := NumberField.mk
    have h1 : typeNormMod r L (I : Ideal (𝓞 E)) ^ k = Submodule.span (𝓞 L) {y} := by
      rw [← typeNormMod_pow L hL]
      exact (hy L le_rfl).1.symm
    have h2 := GlobalTheory.T.field_size_adjoin_kth_root L _ _ k y _ z hS hk hy0 h1 hz
    have hzm : z ∈ L ⊔ ℚ⟮z⟯ := (le_sup_right : ℚ⟮z⟯ ≤ L ⊔ ℚ⟮z⟯) (IntermediateField.mem_adjoin_simple_self ℚ z)
    have hle : L ≤ L ⊔ ℚ⟮z⟯ := le_sup_left
    have hz0 : (⟨z, hzm⟩ : (L ⊔ ℚ⟮z⟯ : IntermediateField ℚ ℂ)) ≠ 0 := by
      intro h
      have h' : z = 0 := congrArg Subtype.val h
      rw [h', zero_pow hk.ne'] at hz
      exact hy0 (Subtype.ext hz.symm)
    refine ⟨⟨L ⊔ ℚ⟮z⟯, fun τ x => hle (hL τ x)⟩, hle, by simpa only [add_assoc] using h2, I, rfl,
      ⟨z, hzm⟩, hz0, fun K _ hK => ?_⟩
    refine GenTypeNorm.root (fun τ x => hK (hle (hL τ x))) hk ((map_ne_zero _).2 hz0) ?_
    have h3 := hy K (hle.trans hK)
    have h4 : IntermediateField.inclusion hK ⟨z, hzm⟩ ^ k = IntermediateField.inclusion (hle.trans hK) y :=
      Subtype.ext hz
    rw [h4]
    exact h3

end GlobalTheory.FieldSize
end

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_capitulation_field_size : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (r : (E →+* ℂ) → ℕ) (n : ℕ), (∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n) → ∀ (F : IntermediateField ℚ ℂ) (a b : ℝ), Sz F a b → (∀ (τ : E →+* ℂ) x, τ x ∈ F) → ∃ F' : IntermediateField ℚ ℂ, F ≤ F' ∧ Sz F' (a + Real.log (classNumber E)) (b + Real.log (classNumber E)) ∧ ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K], F' ≤ K → ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → ∃ β : K, β ≠ 0 ∧ Submodule.span (𝓞 K) {β} = ∏ τ : E →+* ℂ, Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} ^ r τ ∧ ∀ σ : K →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ n := by
  atlas_forward_decl GlobalTheory.FieldSize.exists_sz_typeNorm_principal
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_imag_quadratic_host : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), ∃ (K : IntermediateField ℚ ℂ) (_ : NumberField K) (_ : IsTotallyComplex K), Module.finrank ℚ K = 2 ∧ discr K = -(H.d : ℤ) ∧ discr K < -4 ∧ K ≤ H.φ₀.toRatAlgHom.fieldRange ∧ (∀ z : ℂ, (∃ s : ℤ × ℤ, z = s.1 + s.2 * ((1 + H.φ₀ H.sqrtMinusD) / 2)) ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) ∧ Module.finrank ℚ H.E = 2 * R.f := by
  first | exact @GlobalTheory.FieldSize.exists_hostK | exact GlobalTheory.FieldSize.exists_hostK | (intros; apply GlobalTheory.FieldSize.exists_hostK <;> assumption)
end

section
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.field_size_monotone : (∀ (F : IntermediateField ℚ ℂ) (a b a' b' : ℝ), Sz F a b → a ≤ a' → b ≤ b' → Sz F a' b') ∧ ∀ (F F' : IntermediateField ℚ ℂ) (a b : ℝ), F ≤ F' → Sz F' a b → Sz F a b := by
  first | exact @GlobalTheory.FieldSize.sz_mono_and_of_le | exact GlobalTheory.FieldSize.sz_mono_and_of_le | (intros; apply GlobalTheory.FieldSize.sz_mono_and_of_le <;> assumption)
end

section
open Real

namespace GlobalTheory

theorem sum_sizes_le_ring_polynomial :
    ∀ (f r m L lE lh lG : ℝ), 8 ≤ f → 62 ≤ r → 2 * m ≤ r → 0 ≤ m → 4 ≤ L → lE ≤ 2 * L → 0 ≤ lE →
      log f ≤ L → lh ≤ f * lE + 2 * f * log (1 + f * lE) → lG ≤ f * r ^ 2 * (18 * L + 2) →
      lG + (m + 5) * lh + (4 * f + 20) * (21 * L) + 100 * L
        ≤ 19 * f * r ^ 2 * L + 198 * f ^ 2 * L := by
  intro f r m L lE lh lG hf hr hm hm0 hL hE hE0 hlog hlh hlG
  have hf0 : 0 < f := by linarith
  have hL0 : 0 < L := by linarith
  have hfE0 : 0 ≤ f * lE := mul_nonneg hf0.le hE0
  have hfE : f * lE ≤ f * (2 * L) := mul_le_mul_of_nonneg_left hE hf0.le
  have hfL : 32 ≤ f * L := by nlinarith
  have h1 : log (1 + f * lE) ≤ log (f * (3 * L)) :=
    log_le_log (by linarith) (by nlinarith)
  have h2 : log (f * (3 * L)) = log f + log (3 * L) :=
    log_mul hf0.ne' (by positivity)
  have h3 : log (3 * L) ≤ 3 * L - 1 := log_le_sub_one_of_pos (by positivity)
  have h4 : log (1 + f * lE) ≤ 4 * L := by linarith
  have h5 : 2 * f * log (1 + f * lE) ≤ 2 * f * (4 * L) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  have h6 : lh ≤ 10 * (f * L) := by nlinarith
  have h7 : (m + 5) * lh ≤ (m + 5) * (10 * (f * L)) :=
    mul_le_mul_of_nonneg_left h6 (by linarith)
  have h8 : (m + 5) * (10 * (f * L)) ≤ (r / 2 + 5) * (10 * (f * L)) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h9 : f * r ^ 2 * 4 ≤ f * r ^ 2 * L :=
    mul_le_mul_of_nonneg_left hL (by positivity)
  have h10 : 8 * L ≤ f * L := mul_le_mul_of_nonneg_right hf hL0.le
  have h11 : 5 * r + 200 ≤ r ^ 2 / 2 := by nlinarith
  have h12 : (5 * r + 200) * (f * L) ≤ r ^ 2 / 2 * (f * L) :=
    mul_le_mul_of_nonneg_right h11 (by linarith)
  have h13 : 0 ≤ f ^ 2 * L := by positivity
  nlinarith

end GlobalTheory
end

section
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize

theorem card_GL_zmod_le (r g : ℕ) (hg : g ≠ 0) : Nat.card (GL (Fin r) (ZMod g)) ≤ g ^ (r ^ 2) := by
  have : NeZero g := ⟨hg⟩
  have h := Nat.card_le_card_of_injective (Units.val : GL (Fin r) (ZMod g) → Matrix (Fin r) (Fin r) (ZMod g))
    Units.val_injective
  refine h.trans (le_of_eq ?_)
  unfold Matrix
  rw [Nat.card_fun, Nat.card_fun, Nat.card_zmod, ← pow_mul]
  simp [sq]

theorem card_units_quot_le (E : Type) [Field E] [NumberField E] (N : ℕ) (hN : N ≠ 0) :
    0 < Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ ∧
      Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ ≤ N ^ Module.finrank ℚ E := by
  have hc : Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) = N ^ Module.finrank ℚ E := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  exact ⟨Nat.card_pos, hc ▸ Nat.card_le_card_of_injective _ Units.val_injective⟩

theorem roots_sizes (P : Pre) (L : ℝ) (h : HostSz P.host L) :
    Real.log P.restRowsFiniteGroupCard ≤ P.R.f * (P.R.r : ℝ) ^ 2 * (18 * L + 2) ∧
      (∀ p ∈ [P.host.pde, P.host.pde'], 0 < xiOrd P.host (P.host.g 0 * P.host.g 1 * p) ∧
        Real.log (xiOrd P.host (P.host.g 0 * P.host.g 1 * p)) ≤
          1 + Real.log (classNumber P.host.E) + 2 * P.R.f * (21 * L)) ∧ 8 ≤ P.R.f ∧ 2 * P.R.m ≤ P.R.r := by
  have hg : ∀ k, P.host.g k ≠ 0 := fun k => (P.host.g_prime k).ne_zero
  have hg' : ∀ k, (P.host.g k : ℝ) ≠ 0 := fun k => Nat.cast_ne_zero.2 (hg k)
  have h0 := h.g 0
  have h1 := h.g 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hle : P.restRowsFiniteGroupCard ≤ (P.host.g 0 * P.host.g 1) ^ (P.R.f * P.R.r ^ 2) := by
      unfold Pre.restRowsFiniteGroupCard
      rw [Fin.prod_univ_two, mul_pow, mul_comm P.R.f, pow_mul, pow_mul]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (card_GL_zmod_le _ _ (hg 0)) _)
        (Nat.pow_le_pow_left (card_GL_zmod_le _ _ (hg 1)) _)
    have hpos : (0 : ℝ) < P.restRowsFiniteGroupCard := Nat.cast_pos.2 P.restRowsFiniteGroupCard_pos
    refine (Real.log_le_log hpos (Nat.cast_le.2 hle)).trans ?_
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_mul (P.host.g 0), Real.log_mul (hg' 0) (hg' 1)]
    push_cast
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · intro p hp
    have hp' : p ≠ 0 ∧ Real.log p ≤ L := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨(P.level_prime _ P.host.pde_level.1).ne_zero, h.p.1⟩
      · exact ⟨(P.level_prime _ P.host.pde_level.2).ne_zero, h.p.2⟩
    have hN : P.host.g 0 * P.host.g 1 * p ≠ 0 := mul_ne_zero (mul_ne_zero (hg 0) (hg 1)) hp'.1
    obtain ⟨hu, hu'⟩ := card_units_quot_le P.host.E _ hN
    have hE : Module.finrank ℚ P.host.E = 2 * P.R.f := by
      rw [P.host.finrank_cmField, Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
      ring
    have hh : 0 < classNumber P.host.E := classNumber_pos _
    refine ⟨by unfold xiOrd; positivity, ?_⟩
    unfold xiOrd
    generalize Nat.card (𝓞 P.host.E ⧸
        Ideal.span {((P.host.g 0 * P.host.g 1 * p : ℕ) : 𝓞 P.host.E)})ˣ = c at hu hu' ⊢
    have hu1 : (0 : ℝ) < c := Nat.cast_pos.2 hu
    have hh1 : (0 : ℝ) < classNumber P.host.E := Nat.cast_pos.2 hh
    have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have h3 := Real.log_le_log hu1 (Nat.cast_le.2 hu')
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp'.1
    rw [hE, Nat.cast_pow, Real.log_pow, Nat.cast_mul (P.host.g 0 * P.host.g 1), Nat.cast_mul (P.host.g 0),
      Real.log_mul (mul_ne_zero (hg' 0) (hg' 1)) hp0, Real.log_mul (hg' 0) (hg' 1), Nat.cast_mul,
      Nat.cast_ofNat] at h3
    have h4 : 2 * (P.R.f : ℝ) * (Real.log (P.host.g 0) + Real.log (P.host.g 1) + Real.log p) ≤
        2 * P.R.f * (21 * L) :=
      mul_le_mul_of_nonneg_left (by linarith [h.len, hp'.2]) (by positivity)
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by positivity) hu1.ne',
      Real.log_mul two_ne_zero hh1.ne']
    linarith
  · have he := P.host.two_le_e
    have : 2 ^ 2 ≤ 2 ^ P.R.e := Nat.pow_le_pow_right two_pos he
    have h2 := P.R.toFrame.two_pow_le_ord
    unfold Ranks.f Ranks.n
    omega
  · have := P.R.m_add_three_le_k
    unfold Ranks.r
    omega

end GlobalTheory.FieldSize
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.host_xi_order_bounds : ∀ (P : Pre) (L : ℝ), HostSz P.host L → Real.log P.restRowsFiniteGroupCard ≤ P.R.f * (P.R.r : ℝ) ^ 2 * (18 * L + 2) ∧ (∀ p ∈ [P.host.pde, P.host.pde'], 0 < xiOrd P.host (P.host.g 0 * P.host.g 1 * p) ∧ Real.log (xiOrd P.host (P.host.g 0 * P.host.g 1 * p)) ≤ 1 + Real.log (classNumber P.host.E) + 2 * P.R.f * (21 * L)) ∧ 8 ≤ P.R.f ∧ 2 * P.R.m ≤ P.R.r := by
  first | exact @GlobalTheory.FieldSize.roots_sizes | exact GlobalTheory.FieldSize.roots_sizes | (intros; apply GlobalTheory.FieldSize.roots_sizes <;> assumption)
end

section
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.field_size_sup_add : ∀ (F F' : IntermediateField ℚ ℂ) (a b a' b' : ℝ), Sz F a b → Sz F' a' b' → Sz (F ⊔ F') (a + a') (b + b') := by
  first | exact @GlobalTheory.FieldSize.sz_sup | exact GlobalTheory.FieldSize.sz_sup | (intros; apply GlobalTheory.FieldSize.sz_sup <;> assumption)
end

section
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize

theorem log_sizes_of_isRay_natCast (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M]
    [NumberField M] [Algebra K M] [IsAbelianGalois K M] (h2 : Module.finrank ℚ K = 2) (n : ℕ) (hn : 0 < n)
    (hR : IsRay M (Ideal.span {(n : 𝓞 K)})) :
    Real.log (Module.finrank ℚ M) ≤ Real.log (8 * |(discr K : ℝ)|) + 2 * Real.log n ∧
      Real.log |((discr M : ℤ) : ℝ)| / Module.finrank ℚ M ≤
        Real.log (4 * |(discr K : ℝ)|) + Real.log |(discr K : ℝ)| / 2 + 3 * Real.log n := by
  have hq : Ideal.span {(n : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn.ne'
  have hE : IsEmpty (K →+* ℝ) := ⟨fun φ =>
    IsTotallyComplex.complexEmbedding_not_isReal (Complex.ofRealHom.comp φ) (by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      simp)⟩
  have h1 := GlobalTheory.FieldSize.RayDegree.finrank_le K M _ hq hR
  rw [Fintype.card_eq_zero, pow_zero, mul_one, Ideal.absNorm_span_natCast, RingOfIntegers.rank, h2] at h1
  have hcl := GlobalTheory.classNumber_le_four_mul_abs_discr K h2
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : (0 : ℝ) < |((discr K : ℤ) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero K)
  have hr : 0 < Module.finrank K M := Module.finrank_pos
  have hr' : (0 : ℝ) < Module.finrank K M := by exact_mod_cast hr
  have h3 : (Module.finrank K M : ℝ) ≤ 4 * |(discr K : ℝ)| * (n : ℝ) ^ 2 := by
    have : (Module.finrank K M : ℝ) ≤ (classNumber K : ℝ) * (n : ℝ) ^ 2 := by exact_mod_cast h1
    exact this.trans (mul_le_mul_of_nonneg_right hcl (by positivity))
  have h4 : (Module.finrank ℚ M : ℝ) = 2 * Module.finrank K M := by
    rw [← Module.finrank_mul_finrank ℚ K M, h2]; push_cast; ring
  have h5 := Real.log_le_log hr' h3
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h5
  refine ⟨?_, ?_⟩
  · rw [h4, show 8 * |(discr K : ℝ)| = 2 * (4 * |(discr K : ℝ)|) by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (x := 2) (by positivity) (by positivity)]
    push_cast at h5
    linarith
  · have h6 := GlobalTheory.DifferentBound.natCast_mul_finrank_mem_differentIdeal K M n hn (fun 𝔭 h => hR.1 𝔭 (fun hd => h (by
      rwa [Ideal.dvd_span_singleton] at hd)))
    have h7 := GlobalTheory.log_rootDiscr_le_of_natCast_mem_differentIdeal K M _ (Nat.mul_pos hn hr) h6
    rw [h2, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)] at h7
    push_cast at h5 h7
    linarith

end GlobalTheory.FieldSize
end

section
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.SmallField

theorem sz_mono {F : IntermediateField ℚ ℂ} {a b a' b' : ℝ} (h : Sz F a b) (ha : a ≤ a') (hb : b ≤ b') :
    Sz F a' b' := GlobalTheory.T.field_size_monotone.1 F a b a' b' h ha hb

theorem sz_cyc (n : ℕ) : Sz ℚ⟮Complex.exp (2 * Real.pi * Complex.I / n)⟯ (Real.log n) (Real.log n) := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · have h1 := sz_adjoin_rootOfUnity 1 one_pos
    simp only [Nat.cast_one, div_one, Complex.exp_two_pi_mul_I, Real.log_one] at h1
    simpa only [Nat.cast_zero, div_zero, Complex.exp_zero, Real.log_zero] using h1
  · exact sz_adjoin_rootOfUnity n h

theorem exists_roots (l : List ℕ) (F : IntermediateField ℚ ℂ) (a : ℝ) (h : Sz F a a) :
    ∃ F' : IntermediateField ℚ ℂ, F ≤ F' ∧
      Sz F' (a + (l.map fun N : ℕ => Real.log N).sum) (a + (l.map fun N : ℕ => Real.log N).sum) ∧
      ∀ N ∈ l, Complex.exp (2 * Real.pi * Complex.I / (N : ℕ)) ∈ F' := by
  induction l with
  | nil => exact ⟨F, le_rfl, by simpa using h, by simp⟩
  | cons n l ih =>
    obtain ⟨F', h1, h2, h3⟩ := ih
    refine ⟨F' ⊔ ℚ⟮Complex.exp (2 * Real.pi * Complex.I / n)⟯, h1.trans le_sup_left, ?_, ?_⟩
    · refine sz_mono (GlobalTheory.T.field_size_sup_add _ _ _ _ _ _ h2 (sz_cyc n)) (le_of_eq ?_) (le_of_eq ?_) <;>
      · simp only [List.map_cons, List.sum_cons]; ring
    · intro N hN
      rcases List.mem_cons.1 hN with rfl | hN
      · exact (le_sup_right : _ ≤ F' ⊔ _) (IntermediateField.mem_adjoin_simple_self ℚ _)
      · exact (le_sup_left : F' ≤ _) (h3 N hN)

theorem weberSet_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) (n : ℕ) : weberSet L n = weberSet L' n := by
  have hG : ∀ k, L.G k = L'.G k := fun k => by unfold PeriodPair.G; rw [h]
  have h2 : L.g₂ = L'.g₂ := by unfold PeriodPair.g₂; rw [hG]
  have h3 : L.g₃ = L'.g₃ := by unfold PeriodPair.g₃; rw [hG]
  have hP : ∀ z, L.weierstrassP z = L'.weierstrassP z := fun z => by unfold PeriodPair.weierstrassP; rw [h]
  unfold weberSet
  simp only [h2, h3, hP, h]

theorem exists_chain (Q : ℕ → IntermediateField ℚ ℂ → Prop) (c : ℝ) (F : IntermediateField ℚ ℂ) (a : ℝ) (h : Sz F a a)
    (step : ∀ j (G : IntermediateField ℚ ℂ) (b : ℝ), F ≤ G → Sz G b b → ∃ G' : IntermediateField ℚ ℂ, G ≤ G' ∧
      Sz G' (b + c) (b + c) ∧ ∀ K : IntermediateField ℚ ℂ, FiniteDimensional ℚ K → G' ≤ K → Q j K) (m : ℕ) :
    ∃ F' : IntermediateField ℚ ℂ, F ≤ F' ∧ Sz F' (a + m * c) (a + m * c) ∧
      ∀ K : IntermediateField ℚ ℂ, FiniteDimensional ℚ K → F' ≤ K → ∀ j, 1 ≤ j → j ≤ m → Q j K := by
  induction m with
  | zero => exact ⟨F, le_rfl, by simpa using h, fun K _ _ j h1 h2 => by omega⟩
  | succ m ih =>
    obtain ⟨F', h1, h2, h3⟩ := ih
    obtain ⟨G, g1, g2, g3⟩ := step (m + 1) F' _ h1 h2
    refine ⟨G, h1.trans g1, sz_mono g2 (le_of_eq (by push_cast; ring)) (le_of_eq (by push_cast; ring)),
      fun K hK hG j j1 j2 => ?_⟩
    rcases j2.lt_or_eq with hlt | rfl
    · exact h3 K hK (g1.trans hG) j j1 (by omega)
    · exact g3 K hK hG

theorem log_mul_pred_le (g : ℕ) : Real.log ((g * (g - 1) : ℕ) : ℝ) ≤ 2 * Real.log g := by
  rcases Nat.lt_or_ge g 2 with h | h
  · interval_cases g <;> simp
  · have h1 : ((g * (g - 1) : ℕ) : ℝ) ≤ (g : ℝ) ^ 2 := by
      have : g * (g - 1) ≤ g ^ 2 := by rw [sq]; exact Nat.mul_le_mul_left g (Nat.sub_le g 1)
      exact_mod_cast this
    have h0 : (0 : ℝ) < ((g * (g - 1) : ℕ) : ℝ) := by
      have : 0 < g * (g - 1) := Nat.mul_pos (by omega) (by omega)
      exact_mod_cast this
    simpa using Real.log_le_log h0 h1

end GlobalTheory.FieldSize.SmallField

namespace GlobalTheory.FieldSize

open SmallField GlobalTheory.Mem.BaseExt

end GlobalTheory.FieldSize
end
