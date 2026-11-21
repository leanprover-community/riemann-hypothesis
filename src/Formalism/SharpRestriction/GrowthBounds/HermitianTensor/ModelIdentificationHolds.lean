import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TheoremIOfTwoLetterClausesContraction
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TieDefs
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsIffIntegral
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.QaNuNextAdd
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.NuOfLoZero
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.BlockSubstitutionEmbedding
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ImportsAlt
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DPsiMonomialIwh
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.QaWeightRowInd
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DetYNeZero
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DetFactsP

section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Har4 Formalism.GradedWeylDivisibility MvPolynomial

theorem ta_sumToIter_rename_inr {R S₁ S₂ : Type} [CommRing R] (q : MvPolynomial S₂ R) :
    sumRingEquiv R S₁ S₂ (rename Sum.inr q) = C q := by
  induction q using MvPolynomial.induction_on with
  | C a => rw [rename_C, MvPolynomial.sumRingEquiv_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p n hp => rw [map_mul, map_mul, hp, rename_X, MvPolynomial.sumRingEquiv_X_inr, map_mul]

section A

variable (K : Type) [Field K] (m : ℕ)

theorem Psi_xs (f : MvPolynomial (Fin (m + 1)) K) :
    PsiXY K m (rename Sum.inl f) = blockEmb K true (rename (fun i => (i, (0 : Fin (m + 1)))) f) := by
  simp only [PsiXY, blockEmb, aeval_rename, rename_rename]
  conv_rhs => rw [← aeval_X_left_apply ((rename _) f), aeval_rename]
  rfl

theorem Psi_ys (f : MvPolynomial (Fin (m + 1)) K) :
    PsiXY K m (rename Sum.inr f) = blockEmb K false (aeval (covY K m) f) := by
  simp only [PsiXY, blockEmb, aeval_rename]
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rfl

end A

theorem explicit_map_injective : ExplicitMapInjective := by
  intro K _ m hm
  let Φ1 : PolXY K (m + 1) →ₐ[K] MvPolynomial (Fin (m + 1) ⊕ (Fin (m + 1) × Fin (m + 1))) K :=
    aeval (Sum.elim (fun i => X (Sum.inl i)) (fun i => rename Sum.inr (covY K m i)))
  let e : Fin (m + 1) ⊕ (Fin (m + 1) × Fin (m + 1)) → Bool × (Fin (m + 1) × Fin (m + 1)) :=
    Sum.elim (fun i => (true, (i, 0))) (fun v => (false, v))
  have he : Function.Injective e := by
    rintro (a | a) (b | b) h
    · simp only [e, Sum.elim_inl, Prod.mk.injEq, true_and, and_true] at h
      rw [h]
    · simp [e] at h
    · simp [e] at h
    · simp only [e, Sum.elim_inr, Prod.mk.injEq, true_and] at h
      rw [h]
  have hfac : PsiXY K m = (rename e).comp Φ1 := by
    apply algHom_ext
    rintro (i | i)
    · simp [PsiXY, Φ1, e]
    · simp only [PsiXY, Φ1, aeval_X, Sum.elim_inr, AlgHom.comp_apply, rename_rename]
      rfl
  have hφ : Function.Injective (aeval (covY K m) : MvPolynomial (Fin (m + 1)) K →ₐ[K] _) :=
    ShapeCovering.signed_minors_alg_independent K m hm
  have hcomm : (sumRingEquiv K (Fin (m + 1)) (Fin (m + 1) × Fin (m + 1))).toRingHom.comp Φ1.toRingHom =
      (map (aeval (covY K m) : MvPolynomial (Fin (m + 1)) K →ₐ[K] _).toRingHom).comp
        (sumRingEquiv K (Fin (m + 1)) (Fin (m + 1))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [Φ1, sumRingEquiv_C]
    · rintro (i | i)
      · simp [Φ1, sumRingEquiv_X_inl]
      · simp [Φ1, ta_sumToIter_rename_inr, sumRingEquiv_X_inr]
  have h1 : Function.Injective Φ1 := by
    intro f1 f2 h
    have h2 := DFunLike.congr_fun hcomm f1
    have h3 := DFunLike.congr_fun hcomm f2
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.toRingHom_eq_coe] at h2 h3
    rw [h, h3] at h2
    have h4 := map_injective _ hφ h2
    exact ((sumRingEquiv K (Fin (m + 1)) (Fin (m + 1))).injective h4).symm
  rw [hfac]
  exact (rename_injective e he).comp h1

theorem ta_isHom_prodX {A : Type} [CommRing A] {k : ℕ} (a : Fin k → ℕ) :
    (∏ i, X i ^ a i : MvPolynomial (Fin k) A).IsHomogeneous (∑ i, a i) := by
  exact IsHomogeneous.prod Finset.univ (fun i => X i ^ a i) a (fun i _ => isHomogeneous_X_pow i (a i))

theorem ta_monomial_split {K : Type} [Field K] {k : ℕ} (v : XY k →₀ ℕ) (c : K) :
    (monomial v c : PolXY K k) = c • (rename Sum.inl (∏ i : Fin k, X i ^ v (Sum.inl i)) *
      rename Sum.inr (∏ i : Fin k, X i ^ v (Sum.inr i))) := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type, map_prod, map_prod,
    smul_eq_C_mul]
  simp only [map_pow, rename_X]

theorem ta_rename_inl_hom {K : Type} [Field K] {k P : ℕ} (f : MvPolynomial (Fin k) K) (h : f.IsHomogeneous P) :
    IsWeightedHomogeneous (wXY k) (rename Sum.inl f : PolXY K k) (P, 0) := by
  classical
  intro d hd
  have hmem : d ∈ (rename Sum.inl f : PolXY K k).support := mem_support_iff.2 hd
  rw [support_rename_of_injective Sum.inl_injective, Finset.mem_image] at hmem
  obtain ⟨d', hd', rfl⟩ := hmem
  have hP := h (mem_support_iff.1 hd')
  simp only [Finsupp.weight_apply] at hP ⊢
  rw [Finsupp.sum_mapDomain_index_inj Sum.inl_injective]
  simp only [wXY, Sum.elim_inl]
  rw [← hP]
  ext
  · simp [Finsupp.sum, Prod.fst_sum]
  · simp [Finsupp.sum, Prod.snd_sum]

theorem ta_rename_inr_hom {K : Type} [Field K] {k Q : ℕ} (f : MvPolynomial (Fin k) K) (h : f.IsHomogeneous Q) :
    IsWeightedHomogeneous (wXY k) (rename Sum.inr f : PolXY K k) (0, Q) := by
  classical
  intro d hd
  have hmem : d ∈ (rename Sum.inr f : PolXY K k).support := mem_support_iff.2 hd
  rw [support_rename_of_injective Sum.inr_injective, Finset.mem_image] at hmem
  obtain ⟨d', hd', rfl⟩ := hmem
  have hQ := h (mem_support_iff.1 hd')
  simp only [Finsupp.weight_apply] at hQ ⊢
  rw [Finsupp.sum_mapDomain_index_inj Sum.inr_injective]
  simp only [wXY, Sum.elim_inr]
  rw [← hQ]
  ext
  · simp [Finsupp.sum, Prod.fst_sum]
  · simp [Finsupp.sum, Prod.snd_sum]

theorem ta_mul_mem_PolAB {K : Type} [Field K] {k P Q : ℕ} (f1 f2 : MvPolynomial (Fin k) K)
    (h1 : f1.IsHomogeneous P) (h2 : f2.IsHomogeneous Q) :
    rename Sum.inl f1 * rename Sum.inr f2 ∈ PolAB K k P Q := by
  rw [Formalism.CountingSumsFrames.Har4.mem_PolAB_iff]
  have := (ta_rename_inl_hom f1 h1).mul (ta_rename_inr_hom f2 h2)
  simpa using this

theorem ta_nuOf_vec (m P : ℕ) (hm : 1 ≤ m) : nuOf (letterWt m P true) = fun t => if t = 0 then P else 0 := by
  funext t
  unfold nuOf letterWt
  simp only [if_true]
  have hl : Fin.last m ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  rw [if_neg hl]
  split_ifs <;> simp

theorem ta_nuOf_cov (m Q : ℕ) : nuOf (letterWt m Q false) = fun t => if t = Fin.last m then 0 else Q := by
  funext t
  unfold nuOf letterWt
  simp only [Bool.false_eq_true, if_false, if_true]
  split_ifs <;> simp

theorem explicit_map_onto_two_letter_space : ExplicitMapOntoTwoLetters := by
  intro K _ m hm P Q x
  constructor
  · intro hx
    unfold twoSp tensorLat at hx
    refine Submodule.span_induction (p := fun x _ => ∃ f ∈ PolAB K (m + 1) P Q, PsiXY K m f = x) ?_
      ⟨0, Submodule.zero_mem _, map_zero _⟩ ?_ ?_ hx
    · rintro y ⟨F, hF, rfl⟩
      have ht := hF true
      have hf := hF false
      simp only [if_true, Bool.false_eq_true, if_false] at ht hf
      rw [ta_nuOf_vec m P hm] at ht
      rw [ta_nuOf_cov m Q] at hf
      obtain ⟨f1, h1, e1⟩ := (ShapeCovering.first_column_polynomials_characterize K m P (F true) hm).1 ht
      obtain ⟨f2, h2, e2⟩ := (ShapeCovering.signed_minor_polynomials_characterize K m Q (F false) hm).1 hf
      refine ⟨rename Sum.inl f1 * rename Sum.inr f2, ta_mul_mem_PolAB f1 f2 h1 h2, ?_⟩
      rw [covY_eq] at e2
      rw [map_mul, Psi_xs, Psi_ys, e1, e2, Fintype.prod_bool]
    · rintro x y _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
      exact ⟨f + g, Submodule.add_mem _ hf hg, map_add _ _ _⟩
    · rintro c x _ ⟨f, hf, rfl⟩
      exact ⟨c • f, Submodule.smul_mem _ _ hf, map_smul _ _ _⟩
  · rintro ⟨f, hf, rfl⟩
    rw [f.as_sum, map_sum]
    refine Submodule.sum_mem _ fun v hv => ?_
    rw [ta_monomial_split, map_smul, map_mul, Psi_xs, Psi_ys]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine ⟨fun b : Bool => (cond b (rename (fun i : Fin (m + 1) => (i, (0 : Fin (m + 1))))
        (∏ i : Fin (m + 1), (X i : MvPolynomial (Fin (m + 1)) K) ^ v (Sum.inl i)))
      (aeval (covY K m) (∏ i : Fin (m + 1), (X i : MvPolynomial (Fin (m + 1)) K) ^ v (Sum.inr i))) :
        MvPolynomial (Fin (m + 1) × Fin (m + 1)) K), ?_, ?_⟩
    · intro b
      cases b
      · simp only [Bool.false_eq_true, if_false, cond_false]
        rw [ta_nuOf_cov m Q]
        refine (ShapeCovering.signed_minor_polynomials_characterize K m Q _ hm).2 ⟨_, ?_, rfl⟩
        have := ta_isHom_prodX (A := K) (fun i : Fin (m + 1) => v (Sum.inr i))
        rwa [show ∑ i : Fin (m + 1), v (Sum.inr i) = Q from (hf v hv).2] at this
      · simp only [if_true, cond_true]
        rw [ta_nuOf_vec m P hm]
        refine (ShapeCovering.first_column_polynomials_characterize K m P _ hm).2 ⟨_, ?_, rfl⟩
        have := ta_isHom_prodX (A := K) (fun i : Fin (m + 1) => v (Sum.inl i))
        rwa [show ∑ i : Fin (m + 1), v (Sum.inl i) = P from (hf v hv).1] at this
    · rw [Fintype.prod_bool]
      rfl

end Formalism.MainNotions.flipOneThree.Pf

end
end

section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Har4 Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def ta_covR (A : Type) [CommRing A] (m : ℕ) (i : Fin (m + 1)) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) A :=
  (-1) ^ (i : ℕ) * Matrix.det (fun a b : Fin m => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) A))

theorem ta_covR_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (m : ℕ) (i : Fin (m + 1)) :
    map φ (ta_covR A m i) = ta_covR B m i := by
  unfold ta_covR
  rw [map_mul, map_pow, map_neg, map_one]
  congr 1
  exact (RingHom.map_det (map φ) (Matrix.of fun a b : Fin m =>
    (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) A))).trans (by
      congr 1
      ext a b
      simp)

theorem ta_covR_eq (K : Type) [Field K] (m : ℕ) : ta_covR K m = covY K m := rfl

theorem ta_aeval_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (m : ℕ) (β : MvPolynomial (Fin (m + 1)) A) :
    map φ (aeval (ta_covR A m) β) = aeval (ta_covR B m) (map φ β) := by
  induction β using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, map_X, aeval_X, ta_covR_map]

section Int

variable {O K : Type} [CommRing O] [Field K] [Algebra O K]

def ta_Int (O : Type) {K : Type} [CommRing O] [Field K] [Algebra O K] {σ : Type} (F : MvPolynomial σ K) : Prop :=
  ∃ β : MvPolynomial σ O, map (algebraMap O K) β = F

theorem ta_Int_coeff {σ : Type} {F : MvPolynomial σ K} (h : ta_Int O F) (u : σ →₀ ℕ) :
    coeff u F ∈ Set.range (algebraMap O K) := by
  obtain ⟨β, rfl⟩ := h
  exact ⟨coeff u β, (coeff_map _ _ _).symm⟩

theorem ta_Int_of_coeff {σ : Type} {F : MvPolynomial σ K} (h : ∀ u, coeff u F ∈ Set.range (algebraMap O K)) :
    ta_Int O F := by
  classical
  choose c hc using h
  refine ⟨∑ u ∈ F.support, monomial u (c u), ?_⟩
  simp only [map_sum, map_monomial, hc]
  exact F.support_sum_monomial_coeff

theorem ta_Int_add {σ : Type} {F G : MvPolynomial σ K} (h1 : ta_Int O F) (h2 : ta_Int O G) : ta_Int O (F + G) := by
  obtain ⟨a, rfl⟩ := h1
  obtain ⟨b, rfl⟩ := h2
  exact ⟨a + b, map_add _ _ _⟩

theorem ta_Int_mul {σ : Type} {F G : MvPolynomial σ K} (h1 : ta_Int O F) (h2 : ta_Int O G) : ta_Int O (F * G) := by
  obtain ⟨a, rfl⟩ := h1
  obtain ⟨b, rfl⟩ := h2
  exact ⟨a * b, map_mul _ _ _⟩

theorem ta_Int_smul {σ : Type} {F : MvPolynomial σ K} (c : O) (h : ta_Int O F) : ta_Int O (algebraMap O K c • F) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨C c * a, by rw [map_mul, map_C, smul_eq_C_mul]⟩

theorem ta_Int_rename {σ τ : Type} (e : σ → τ) {F : MvPolynomial σ K} (h : ta_Int O F) : ta_Int O (rename e F) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨rename e a, map_rename _ _ _⟩

theorem ta_Int_of_rename {σ τ : Type} (e : σ → τ) (he : Function.Injective e) {F : MvPolynomial σ K}
    (h : ta_Int O (rename e F)) : ta_Int O F := by
  refine ta_Int_of_coeff fun u => ?_
  rw [← coeff_rename_mapDomain e he]
  exact ta_Int_coeff h _

theorem ta_Int_prodX {k : ℕ} (a : Fin k → ℕ) : ta_Int O (∏ i, X i ^ a i : MvPolynomial (Fin k) K) :=
  ⟨∏ i, X i ^ a i, by simp [map_prod]⟩

theorem ta_Int_aeval (m : ℕ) {b : MvPolynomial (Fin (m + 1)) K} (h : ta_Int O b) : ta_Int O (aeval (covY K m) b) := by
  obtain ⟨β, rfl⟩ := h
  exact ⟨aeval (ta_covR O m) β, by rw [ta_aeval_map, ta_covR_eq]⟩

end Int

section Sat

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K]

theorem ta_exists_pow (w : O) (hw : Irreducible w) {σ : Type} (b : MvPolynomial σ K) :
    ∃ n : ℕ, ta_Int O ((algebraMap O K w ^ n) • b) := by
  classical
  obtain ⟨⟨s, hs⟩, hsI⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O)
    (b.support.image fun u => coeff u b)
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hw
  refine ⟨n, ta_Int_of_coeff fun u => ?_⟩
  rw [coeff_smul, smul_eq_mul]
  by_cases hu : u ∈ b.support
  · obtain ⟨r, hr⟩ := hsI _ (Finset.mem_image_of_mem _ hu)
    refine ⟨(↑v⁻¹ : O) * r, ?_⟩
    have hr' : algebraMap O K r = algebraMap O K s * coeff u b := by
      rw [hr]
      exact Algebra.smul_def _ _
    rw [map_mul, hr', hv, map_mul, map_pow, ← mul_assoc, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  · rw [mem_support_iff, not_not] at hu
    exact ⟨0, by rw [hu, mul_zero, map_zero]⟩

theorem ta_sat (w : O) (hw : Irreducible w) (m : ℕ) (hm : 1 ≤ m) (b : MvPolynomial (Fin (m + 1)) K)
    (h : ta_Int O (aeval (covY K m) b)) : ta_Int O b := by
  classical
  have hw0 : w ≠ 0 := hw.ne_zero
  have hinjOK : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hW0 : algebraMap O K w ≠ 0 := fun h0 => hw0 (hinjOK (by rw [h0, map_zero]))
  obtain ⟨γ, hγ⟩ := h
  haveI hmax : (Ideal.span {w}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hw
  letI : Field (O ⧸ Ideal.span {w}) := Ideal.Quotient.field _
  have hind : Function.Injective (aeval (R := O ⧸ Ideal.span {w}) (covY (O ⧸ Ideal.span {w}) m)) := by
    have := Formalism.MainNotions.flipOneThree.Pf.ShapeCovering.signed_minors_alg_independent (O ⧸ Ideal.span {w}) m hm
    rw [covY_eq] at this
    exact this
  have step : ∀ n : ℕ, ta_Int O (algebraMap O K w ^ (n + 1) • b) → ta_Int O (algebraMap O K w ^ n • b) := by
    intro n hn
    obtain ⟨β, hβ⟩ := hn
    have e1 : map (algebraMap O K) (aeval (ta_covR O m) β) = map (algebraMap O K) (C (w ^ (n + 1)) * γ) := by
      rw [ta_aeval_map, ta_covR_eq, hβ, map_smul, map_mul, map_C, hγ, smul_eq_C_mul]
      simp only [map_pow]
    have e2 := map_injective _ hinjOK e1
    have e3 : aeval (R := O ⧸ Ideal.span {w}) (covY (O ⧸ Ideal.span {w}) m)
        (map (Ideal.Quotient.mk (Ideal.span {w})) β) = 0 := by
      rw [← ta_covR_eq, ← ta_aeval_map, e2, map_mul, map_C, map_pow,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self w), zero_pow (Nat.succ_ne_zero n),
        C_0, zero_mul]
    have e4 : map (Ideal.Quotient.mk (Ideal.span {w})) β = 0 := hind (by rw [e3, map_zero])
    apply ta_Int_of_coeff
    intro u
    have hu : coeff u β ∈ Ideal.span {w} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have := congrArg (coeff u) e4
      rwa [coeff_map, coeff_zero] at this
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hu
    refine ⟨c, ?_⟩
    have e5 := congrArg (coeff u) hβ
    rw [coeff_map, ← hc, map_mul, coeff_smul, smul_eq_mul] at e5
    rw [coeff_smul, smul_eq_mul]
    apply mul_right_cancel₀ hW0
    rw [e5]
    ring
  obtain ⟨n, hn⟩ := ta_exists_pow w hw b
  induction n with
  | zero => simpa using hn
  | succ n ih => exact ih (step n hn)

end Sat

section Act

variable {K : Type} [Field K] {m : ℕ}

theorem ta_Psi_gl_alt (g' : GL (Fin (m + 1)) K) (a : MvPolynomial (Fin (m + 1)) K) :
    PsiXY K m (glAct g' (rename Sum.inl a)) =
      blockEmb K true (rowAct K (g' : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (rename (fun i => (i, (0 : Fin (m + 1)))) a)) := by
  have key : (PsiXY K m).comp ((Formalism.CountingSumsFrames.glAct g').comp (rename Sum.inl)) =
      (blockEmb K true).comp ((rowAct K (g' : Matrix (Fin (m + 1)) (Fin (m + 1)) K)).comp
        (rename fun i => (i, (0 : Fin (m + 1))))) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [PsiXY, Formalism.CountingSumsFrames.glAct, blockEmb, rowAct, algebraMap_eq]
  exact DFunLike.congr_fun key a

theorem ta_Psi_gl_y (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det) (g' : GL (Fin (m + 1)) K)
    (hg' : (g' : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = g⁻¹) (b : MvPolynomial (Fin (m + 1)) K) :
    PsiXY K m (glAct g' (rename Sum.inr b)) =
      blockEmb K false (aeval (fun i => C g.det * rowAct K g⁻¹ (covY K m i)) b) := by
  have hinv : IsUnit (g⁻¹).det := Matrix.isUnit_nonsing_inv_det g hg
  have hd0 : g.det ≠ 0 := hg.ne_zero
  have key : (PsiXY K m).comp ((Formalism.CountingSumsFrames.glAct g').comp (rename Sum.inr)) =
      (blockEmb K false).comp (aeval fun i => C g.det * rowAct K g⁻¹ (covY K m i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    have h5 := Formalism.MainNotions.flipOneThree.Pf.ShapeCovering.signed_minors_cofactor_transform K m g⁻¹ i hinv
    rw [covY_eq] at h5
    have hgg : ((g'⁻¹ : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = g := by
      rw [Matrix.coe_units_inv, hg', Matrix.nonsing_inv_nonsing_inv g hg]
    simp only [AlgHom.comp_apply, rename_X, aeval_X, Formalism.CountingSumsFrames.glAct, Sum.elim_inr, map_sum, map_mul, hgg]
    rw [h5, ← map_mul, ← mul_assoc, ← C_mul, Matrix.nonsing_inv_nonsing_inv g hg, Matrix.det_nonsing_inv,
      Ring.inverse_eq_inv', mul_inv_cancel₀ hd0, C_1, one_mul, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    unfold PsiXY blockEmb
    rw [aeval_C, aeval_X, Sum.elim_inr, rename_C, algebraMap_eq]
  exact DFunLike.congr_fun key b

theorem ta_aeval_scale {τ : Type} {k Q : ℕ} (d : K) (z : Fin k → MvPolynomial τ K) (b : MvPolynomial (Fin k) K)
    (hb : b.IsHomogeneous Q) : aeval (fun i => C d * z i) b = d ^ Q • aeval z b := by
  classical
  conv_lhs => rw [b.as_sum]
  conv_rhs => rw [b.as_sum]
  simp only [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hdeg := hb (mem_support_iff.mp hu)
  simp only [aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [smul_eq_C_mul, ← map_pow]
  have hQ : ∑ i ∈ u.support, u i = Q := by
    rw [← hdeg]
    simp [Finsupp.weight_apply, Finsupp.sum]
  rw [hQ]
  ring

theorem ta_aeval_rowAct (h : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (b : MvPolynomial (Fin (m + 1)) K) :
    aeval (fun i => rowAct K h (covY K m i)) b = rowAct K h (aeval (covY K m) b) := by
  exact (DFunLike.congr_fun (comp_aeval (covY K m) (rowAct K h)) b).symm

theorem ta_Psi_gl (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hg : IsUnit g.det) (g' : GL (Fin (m + 1)) K)
    (hg' : (g' : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = g⁻¹) (Q : ℕ) (a b : MvPolynomial (Fin (m + 1)) K)
    (hb : b.IsHomogeneous Q) :
    PsiXY K m (glAct g' (rename Sum.inl a * rename Sum.inr b)) =
      blockEmb K true (rowAct K g⁻¹ (rename (fun i => (i, (0 : Fin (m + 1)))) a)) *
        blockEmb K false (g.det ^ Q • rowAct K g⁻¹ (aeval (covY K m) b)) := by
  rw [map_mul, map_mul, ta_Psi_gl_alt, ta_Psi_gl_y g hg g' hg', hg', ta_aeval_scale g.det _ b hb, ta_aeval_rowAct]

end Act

end Formalism.MainNotions.flipOneThree.Pf

end
end

section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Har4 Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem ta_last_ne (m : ℕ) (hm : 1 ≤ m) : Fin.last m ≠ 0 := by
  intro h
  have h2 := congrArg Fin.val h
  simp at h2
  omega

section L

variable {p n' : ℕ} (R : RS p n') (m : ℕ) (hm : 1 ≤ m) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf) (hg : IsUnit g.det)

include hm hg

theorem ta_vec_mem (P : ℕ) (a : MvPolynomial (Fin (m + 1)) R.Kf) (ha : a.IsHomogeneous P) (hI : ta_Int R.O a) :
    rowAct R.Kf g⁻¹ (rename (fun i => (i, (0 : Fin (m + 1)))) a) ∈ H0 R.O m (letterWt m P true) (colSpan R.O g) := by
  have := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  refine (mem_invariant_sections_iff_integral hinj m _ (letterWt_anti m P true) g hg _).2 ?_
  have h0 : letterWt m P true (Fin.last m) = 0 := by simp [letterWt, ta_last_ne m hm]
  rw [h0, zpow_zero, one_smul, rowAct_inv_cancel g hg]
  refine intCapP R.O R.Kf hinj (m + 1) _ _ ?_ (fun u => ta_Int_coeff (ta_Int_rename _ hI) u)
  rw [ta_nuOf_vec m P hm]
  exact (ShapeCovering.first_column_polynomials_characterize R.Kf m P _ hm).2 ⟨a, ha, rfl⟩

theorem ta_cov_mem (Q : ℕ) (b : MvPolynomial (Fin (m + 1)) R.Kf) (hb : b.IsHomogeneous Q) (hI : ta_Int R.O b) :
    g.det ^ Q • rowAct R.Kf g⁻¹ (aeval (covY R.Kf m) b) ∈ H0 R.O m (letterWt m Q false) (colSpan R.O g) := by
  have := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  refine (mem_invariant_sections_iff_integral hinj m _ (letterWt_anti m Q false) g hg _).2 ?_
  have h0 : letterWt m Q false (Fin.last m) = -(Q : ℤ) := by simp [letterWt]
  rw [h0, map_smul, rowAct_inv_cancel g hg, smul_smul, zpow_neg, zpow_natCast,
    inv_mul_cancel₀ (pow_ne_zero _ hg.ne_zero), one_smul]
  refine intCapP R.O R.Kf hinj (m + 1) _ _ ?_ (fun u => ta_Int_coeff (ta_Int_aeval m hI) u)
  rw [ta_nuOf_cov m Q]
  exact (ShapeCovering.signed_minor_polynomials_characterize R.Kf m Q _ hm).2 ⟨b, hb, rfl⟩

theorem ta_vec_of (P : ℕ) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf)
    (hF : F ∈ H0 R.O m (letterWt m P true) (colSpan R.O g)) :
    ∃ a : MvPolynomial (Fin (m + 1)) R.Kf, a.IsHomogeneous P ∧ ta_Int R.O a ∧
      F = rowAct R.Kf g⁻¹ (rename (fun i => (i, (0 : Fin (m + 1)))) a) := by
  have := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  have h1 := (mem_invariant_sections_iff_integral hinj m _ (letterWt_anti m P true) g hg _).1 hF
  have h0 : letterWt m P true (Fin.last m) = 0 := by simp [letterWt, ta_last_ne m hm]
  rw [h0, zpow_zero, one_smul] at h1
  have h2 := intO_le _ _ _ h1
  rw [ta_nuOf_vec m P hm] at h2
  obtain ⟨a, ha, e⟩ := (ShapeCovering.first_column_polynomials_characterize R.Kf m P _ hm).1 h2
  refine ⟨a, ha, ta_Int_of_rename (fun i : Fin (m + 1) => (i, (0 : Fin (m + 1)))) ?_ ?_, ?_⟩
  · intro i j hij
    exact (Prod.mk.inj hij).1
  · rw [e]
    obtain ⟨f, -, hf⟩ := h1
    exact ⟨f, hf⟩
  · rw [e, rowAct_cancel_inv g hg]

theorem ta_cov_of (Q : ℕ) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf)
    (hF : F ∈ H0 R.O m (letterWt m Q false) (colSpan R.O g)) :
    ∃ b : MvPolynomial (Fin (m + 1)) R.Kf, b.IsHomogeneous Q ∧ ta_Int R.O b ∧
      F = g.det ^ Q • rowAct R.Kf g⁻¹ (aeval (covY R.Kf m) b) := by
  have := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  have h1 := (mem_invariant_sections_iff_integral hinj m _ (letterWt_anti m Q false) g hg _).1 hF
  have h0 : letterWt m Q false (Fin.last m) = -(Q : ℤ) := by simp [letterWt]
  rw [h0] at h1
  have h2 := intO_le _ _ _ h1
  rw [ta_nuOf_cov m Q] at h2
  obtain ⟨b, hb, e⟩ := (ShapeCovering.signed_minor_polynomials_characterize R.Kf m Q _ hm).1 h2
  rw [covY_eq] at e
  refine ⟨b, hb, ta_sat R.w R.std.2.1 m hm b ?_, ?_⟩
  · rw [e]
    obtain ⟨f, -, hf⟩ := h1
    exact ⟨f, hf⟩
  · rw [e, map_smul, rowAct_cancel_inv g hg, smul_smul, zpow_neg, zpow_natCast,
      mul_inv_cancel₀ (pow_ne_zero _ hg.ne_zero), one_smul]

end L

theorem two_letter_lattice_gauss_inverse : TwoLetterLatticeGaussInverse := by
  intro p n' R m hm g hg g' hg' P Q f hf
  constructor
  · intro hx
    have key : ∀ x ∈ twoLat R.O m P Q (colSpan R.O g),
        ∃ f₀ : PolXY R.Kf (m + 1), ta_Int R.O f₀ ∧ PsiXY R.Kf m (glAct g' f₀) = x := by
      intro x hx
      unfold twoLat tensorLat at hx
      refine Submodule.span_induction
        (p := fun x _ => ∃ f₀ : PolXY R.Kf (m + 1), ta_Int R.O f₀ ∧ PsiXY R.Kf m (glAct g' f₀) = x) ?_ ?_ ?_ ?_ hx
      · rintro y ⟨F, hF, rfl⟩
        have ht := hF true
        have hf' := hF false
        simp only [if_true, Bool.false_eq_true, if_false] at ht hf'
        obtain ⟨a, ha, hIa, ea⟩ := ta_vec_of R m hm g hg P _ ht
        obtain ⟨b, hb, hIb, eb⟩ := ta_cov_of R m hm g hg Q _ hf'
        refine ⟨rename Sum.inl a * rename Sum.inr b, ta_Int_mul (ta_Int_rename _ hIa) (ta_Int_rename _ hIb), ?_⟩
        rw [ta_Psi_gl g hg g' hg' Q a b hb, ← ea, ← eb, Fintype.prod_bool]
      · exact ⟨0, ⟨0, map_zero _⟩, by simp⟩
      · rintro x y _ _ ⟨f1, h1, rfl⟩ ⟨f2, h2, rfl⟩
        exact ⟨f1 + f2, ta_Int_add h1 h2, by rw [map_add, map_add]⟩
      · rintro c x _ ⟨f1, h1, rfl⟩
        exact ⟨algebraMap R.O R.Kf c • f1, ta_Int_smul c h1, by rw [map_smul, map_smul, algebraMap_smul]⟩
    obtain ⟨f₀, hI, he⟩ := key _ hx
    have h1 := explicit_map_injective R.Kf m hm he
    refine ⟨f₀, fun u => ?_, h1⟩
    obtain ⟨c, hc⟩ := ta_Int_coeff hI u
    rw [← hc]
    exact R.mem_Ov c
  · rintro ⟨f₀, hG, rfl⟩
    have hf₀ : f₀ ∈ PolAB R.Kf (m + 1) P Q := by
      have := glAct_mem_PolAB g'⁻¹ _ hf
      rwa [glAct_inv_glAct] at this
    rw [f₀.as_sum, map_sum, map_sum]
    refine Submodule.sum_mem _ fun v hv => ?_
    obtain ⟨c, hc⟩ : ∃ c : R.O, algebraMap R.O R.Kf c = coeff v f₀ := hG v
    rw [ta_monomial_split, map_smul, map_smul, ← hc, algebraMap_smul]
    refine Submodule.smul_mem _ _ ?_
    have hP : (∏ i : Fin (m + 1), (X i : MvPolynomial (Fin (m + 1)) R.Kf) ^ v (Sum.inl i)).IsHomogeneous P := by
      have := ta_isHom_prodX (A := R.Kf) (fun i : Fin (m + 1) => v (Sum.inl i))
      rwa [show ∑ i : Fin (m + 1), v (Sum.inl i) = P from (hf₀ v hv).1] at this
    have hQ : (∏ i : Fin (m + 1), (X i : MvPolynomial (Fin (m + 1)) R.Kf) ^ v (Sum.inr i)).IsHomogeneous Q := by
      have := ta_isHom_prodX (A := R.Kf) (fun i : Fin (m + 1) => v (Sum.inr i))
      rwa [show ∑ i : Fin (m + 1), v (Sum.inr i) = Q from (hf₀ v hv).2] at this
    rw [ta_Psi_gl g hg g' hg' Q _ _ hQ]
    refine Submodule.subset_span ⟨fun b : Bool => (cond b
      (rowAct R.Kf g⁻¹ (rename (fun i : Fin (m + 1) => (i, (0 : Fin (m + 1))))
        (∏ i : Fin (m + 1), (X i : MvPolynomial (Fin (m + 1)) R.Kf) ^ v (Sum.inl i))))
      (g.det ^ Q • rowAct R.Kf g⁻¹ (aeval (covY R.Kf m)
        (∏ i : Fin (m + 1), (X i : MvPolynomial (Fin (m + 1)) R.Kf) ^ v (Sum.inr i)))) :
        MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf), ?_, ?_⟩
    · intro b
      cases b
      · simp only [Bool.false_eq_true, if_false, cond_false]
        exact ta_cov_mem R m hm g hg Q _ hQ (ta_Int_prodX _)
      · simp only [if_true, cond_true]
        exact ta_vec_mem R m hm g hg P _ hP (ta_Int_prodX _)
    · rw [Fintype.prod_bool]
      rfl

end Formalism.MainNotions.flipOneThree.Pf

end
end

section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem contraction_of_pairing_lemmas (hPh : QPh) (hSC : SubCoeffP) (hSM : SubMapP) (hSR : SubRowP) (hLC : LamCoeffP) (hLE : LamEquivP)
    (hLM : LamMulP) (hLV : LamEvalP) (hMem : LamMemP) (hMu : SubMuP) (hTop : TopLineP) (hLift : LiftP) (hDD : DetDivP)
    (hIC : IntCapP) (hHw : HwMulP) : ContractionStandardLattice := by
  classical
  intro p n' R mm hmm a ccl P Q lam hlam h0 hl hmid h8
  have hfr := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  have := R.charZero
  have : Infinite R.Kf := inferInstance
  have hloA : Antitone (lam - wtPQ (mm + 1) P Q) := caLo_anti mm ccl P Q lam hlam h0 hl hmid
  have hlo'A : Antitone (dualWt (lam - wtPQ (mm + 1) P Q)) := qsDualWt_anti _ hloA
  have hαZ := nuOf_lam_mid mm ccl Q lam hl hmid
  have hβZ := nuOf_lo_mid mm ccl P Q lam h0 hl hmid
  have hβ'Z := nuOf_lo'_mid mm ccl P Q lam h0 hl hmid
  have hbd := lam_mid_bd mm ccl lam hmid
  have hαA : Antitone (fun j => nuOf lam (midI mm j)) := fun i j hij => nuOf_anti lam hlam (midI_mono mm hij)
  have hαN : ∀ i, (fun j => nuOf lam (midI mm j)) i ≤ Q + 2 * ccl := by
    intro i
    show nuOf lam (midI mm i) ≤ Q + 2 * ccl
    have := hαZ i; have := hbd i; omega
  have hαc : ∀ i j, (fun j => nuOf lam (midI mm j)) i ≤ (fun j => nuOf lam (midI mm j)) j + 2 * ccl := by
    intro i j
    show nuOf lam (midI mm i) ≤ nuOf lam (midI mm j) + 2 * ccl
    have := hαZ i; have := hαZ j; have := hbd i; have := hbd j; omega
  obtain ⟨L, hInv, hInt, nb, u, u', ka, hnb, hka, hu, hu', hdiag⟩ :=
    hPh p n' R mm hmm a (2 * ccl) (Q + 2 * ccl) (fun j => nuOf lam (midI mm j)) hαA hαN hαc h8
  have hα' : (fun i : Fin mm => Q + 2 * ccl - (fun j => nuOf lam (midI mm j)) i.rev) =
      fun j => nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j) := by
    funext j
    show Q + 2 * ccl - nuOf lam (midI mm j.rev) = _
    have h1 := hβ'Z j; have h2 := hαZ j.rev; have h3 := hbd j.rev; omega
  rw [hα'] at hInv hInt hu'
  have hαβ : (fun j => nuOf lam (midI mm j)) = fun j => nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j) + Q := by
    funext j
    have := hαZ j; have := hβZ j; omega
  have hwA : ∀ a b, Antitone (nuOf (wtPQ (mm + 1) a b)) := fun a b => nuOf_anti _ (wtPQ_anti (mm + 1) a b (by omega))
  have hK : ∀ v ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf lam),
      ∀ t ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))),
        lamOf R.Kf mm L (blockEmb R.Kf true v * blockEmb R.Kf false t) ∈
          dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl))) :=
    hMem R.Kf mm (Q + 2 * ccl) (nuOf lam) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q)))
      (nuOf (wtPQ (mm + 1) (P + 2 * ccl) (Q + 2 * ccl))) L (nuOf_last _) (nuOf_last _) (nuOf_last _)
      (by rw [nuOf_wt_zero, nuOf_lam_zero mm ccl P Q lam h0 hl, nuOf_lo'_zero mm ccl P Q lam h0 hl]; omega)
      (fun j => nuOf_wt_mid mm _ _ j) hInv
  refine ⟨lamOf R.Kf mm L, hK, fun g _ v _ t _ => hLE R.Kf mm L g v t, ?_, ?_⟩
  · intro v hv t ht
    refine hIC R.O R.Kf hinj _ _ _ (hK v (intO_le _ _ v hv) t (intO_le _ _ t ht)) ?_
    intro x
    obtain ⟨v0, hv0, rfl⟩ := hv
    obtain ⟨t0, ht0, rfl⟩ := ht
    have e1 : (mapAlgHom (Algebra.ofId R.O R.Kf)).toLinearMap v0 = map (algebraMap R.O R.Kf) v0 := rfl
    have e2 : (mapAlgHom (Algebra.ofId R.O R.Kf)).toLinearMap t0 = map (algebraMap R.O R.Kf) t0 := rfl
    rw [hLC, e1, e2, hSM, hSM]
    have : (∑ y ∈ Finset.HasAntidiagonal.antidiagonal x,
        L (blockEmb R.Kf true (coeff y.1 (map (map (algebraMap R.O R.Kf)) (subY R.O mm v0))) *
          blockEmb R.Kf false (coeff y.2 (map (map (algebraMap R.O R.Kf)) (subY R.O mm t0))))) ∈
        (algebraMap R.O R.Kf).range := by
      refine sum_mem fun y _ => ?_
      rw [coeff_map, coeff_map]
      exact hInt _ ⟨coeff y.1 (subY R.O mm v0), hSC R.O mm _ v0 hv0 _, rfl⟩ _
        ⟨coeff y.2 (subY R.O mm t0), hSC R.O mm _ t0 ht0 _, rfl⟩
    exact this
  · have hβA : Antitone (fun j => nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j)) :=
      fun i j hij => nuOf_anti _ hloA (midI_mono mm hij)
    have hβc : ∀ j, (fun j => nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j)) j ≤ 2 * ccl := by
      intro j
      show nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j) ≤ 2 * ccl
      have := hβZ j; have := hbd j; omega
    have hβ'A : Antitone (fun j => nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j)) :=
      fun i j hij => nuOf_anti _ hlo'A (midI_mono mm hij)
    have hβ'c : ∀ j, (fun j => nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j)) j ≤ 2 * ccl := by
      intro j
      show nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j) ≤ 2 * ccl
      have := hβ'Z j; have := hbd j.rev; omega
    have hS : ∀ b, ∃ s0 ∈ dualWeyl R.O (mm + 1 + 1) (mm + 1 + 1) (nuOf (lam - wtPQ (mm + 1) P Q)),
        RowA 0 s0 (2 * ccl) ∧ RowA (Fin.last (mm + 1)) s0 0 ∧
          map (algebraMap R.O R.Kf) (detY R.O mm ^ Q * resY R.O mm s0) = u b := by
      intro b
      obtain ⟨f, hf, hfe⟩ := hu b
      rw [hαβ] at hf
      obtain ⟨w0, hw0, rfl⟩ := hDD R.O mm Q _ hmm hβA f hf
      obtain ⟨s0, hs0, hr0, hrl, hres⟩ := hLift R.O mm (2 * ccl) _ hβA hβc w0 hw0
      rw [shapeC_lo mm ccl P Q lam h0 hl] at hs0
      exact ⟨s0, hs0, hr0, hrl, by rw [hres]; exact hfe⟩
    have hS' : ∀ a', ∃ s0 ∈ dualWeyl R.O (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))),
        RowA 0 s0 (2 * ccl) ∧ RowA (Fin.last (mm + 1)) s0 0 ∧ map (algebraMap R.O R.Kf) (resY R.O mm s0) = u' a' := by
      intro a'
      obtain ⟨f, hf, hfe⟩ := hu' a'
      obtain ⟨s0, hs0, hr0, hrl, hres⟩ := hLift R.O mm (2 * ccl) _ hβ'A hβ'c f hf
      rw [shapeC_lo' mm ccl P Q lam h0 hl] at hs0
      exact ⟨s0, hs0, hr0, hrl, by rw [hres]; exact hfe⟩
    choose s0 hs0 hs0r hs0l hs0e using hS
    choose t0 ht0 ht0r ht0l ht0e using hS'
    refine ⟨nb, fun b => map (algebraMap R.O R.Kf) (s0 b), fun a' => map (algebraMap R.O R.Kf) (t0 a'), ka, ?_, hka,
      fun b => ⟨⟨s0 b, hs0 b, rfl⟩, rowA_map _ 0 _ _ (hs0r b)⟩, fun a' => ⟨⟨t0 a', ht0 a', rfl⟩, rowA_map _ 0 _ _ (ht0r a')⟩, ?_⟩
    · have e : (fun j : Fin mm => ((nuOf lam (midI mm j) : ℕ) : ℤ)) = fun j => lam (midI mm j) + ((Q : ℤ) + ccl) := by
        funext j
        rw [hαZ j]; ring
      rw [hnb, e]
      exact weylDim_add_const mm (fun j => lam (midI mm j)) ((Q : ℤ) + ccl)
    · intro a' b F hF
      have e1 := hLM R.Kf mm Q L F (map (algebraMap R.O R.Kf) (s0 b)) (map (algebraMap R.O R.Kf) (t0 a'))
        (hMu p n' R mm hmm P Q F hF)
      have hF0 : hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q)) ∈
          dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (wtPQ (mm + 1) 0 Q)) := hwMem R.Kf _ _ le_rfl _ (hwA 0 Q)
      have hF0sub := hMu p n' R mm hmm 0 Q _ hF0
      have e2 := hLM R.Kf mm Q L _ (map (algebraMap R.O R.Kf) (s0 b)) (map (algebraMap R.O R.Kf) (t0 a')) hF0sub
      have hSK : map (algebraMap R.O R.Kf) (s0 b) ∈ dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (lam - wtPQ (mm + 1) P Q)) :=
        dualWeylMap R.O R.Kf _ _ _ _ _ (hs0 b)
      have hTK : map (algebraMap R.O R.Kf) (t0 a') ∈
          dualWeyl R.Kf (mm + 1 + 1) (mm + 1 + 1) (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))) :=
        dualWeylMap R.O R.Kf _ _ _ _ _ (ht0 a')
      have hInv' : PhInv R.Kf mm (Q + 2 * ccl)
          (fun j => (nuOf (wtPQ (mm + 1) 0 Q) + nuOf (lam - wtPQ (mm + 1) P Q)) (midI mm j))
          (fun j => nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j)) L := by
        have e : (fun j => (nuOf (wtPQ (mm + 1) 0 Q) + nuOf (lam - wtPQ (mm + 1) P Q)) (midI mm j)) =
            fun j => nuOf lam (midI mm j) := by
          funext j
          rw [Pi.add_apply, nuOf_wt_mid]
          have := hαZ j; have := hβZ j; omega
        rw [e]; exact hInv
      have hΨmem := hMem R.Kf mm (Q + 2 * ccl) (nuOf (wtPQ (mm + 1) 0 Q) + nuOf (lam - wtPQ (mm + 1) P Q))
        (nuOf (dualWt (lam - wtPQ (mm + 1) P Q))) (nuOf (wtPQ (mm + 1) (2 * ccl) (Q + 2 * ccl))) L
        (by rw [Pi.add_apply, nuOf_last, nuOf_last]) (nuOf_last _) (nuOf_last _)
        (by rw [nuOf_wt_zero, Pi.add_apply, nuOf_wt_zero, nuOf_lo_zero mm ccl P Q lam h0 hl,
              nuOf_lo'_zero mm ccl P Q lam h0 hl]; omega)
        (fun j => nuOf_wt_mid mm _ _ j) hInv' _ (dualWeyl_mul R.Kf _ _ _ _ hF0 hSK) _ hTK
      have hr0 : RowA 0 (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q))) Q := by
        have h := rowA_hw R.Kf _ _ (hwA 0 Q) 0
        rwa [nuOf_wt_zero, zero_add] at h
      have hrl : RowA (Fin.last (mm + 1)) (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q))) 0 := by
        have h := rowA_hw R.Kf _ _ (hwA 0 Q) (Fin.last (mm + 1))
        rwa [nuOf_last] at h
      have hΨ0 := rowA_lam hLC hSR R.Kf mm L 0 _ _ _ _
        (rowA_mul 0 _ _ _ _ hr0 (rowA_map (algebraMap R.O R.Kf) 0 _ _ (hs0r b)))
        (rowA_map (algebraMap R.O R.Kf) 0 _ _ (ht0r a'))
      have hΨl := rowA_lam hLC hSR R.Kf mm L (Fin.last (mm + 1)) _ _ _ _
        (rowA_mul (Fin.last (mm + 1)) _ _ _ _ hrl (rowA_map (algebraMap R.O R.Kf) _ _ _ (hs0l b)))
        (rowA_map (algebraMap R.O R.Kf) _ _ _ (ht0l a'))
      have ed : Q + 2 * ccl + 2 * ccl = 2 * ccl + (Q + 2 * ccl) := by omega
      rw [ed] at hΨ0
      have hΨ := hTop p n' R mm hmm (2 * ccl) (Q + 2 * ccl) _ hΨmem hΨ0 hΨl
      have hres0 : resY R.Kf mm (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q))) = detY R.Kf mm ^ Q := by
        unfold resY
        rw [hF0sub, map_mul, eval_C, evalId_map, (hHw R.Kf _ _ _ (hwA 0 Q) (hwA 0 Q)).2, map_one, mul_one]
      have hκ : eval (idPoint R.Kf (mm + 1 + 1) (mm + 1 + 1))
          (lamOf R.Kf mm L (blockEmb R.Kf true (hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q)) *
            map (algebraMap R.O R.Kf) (s0 b)) * blockEmb R.Kf false (map (algebraMap R.O R.Kf) (t0 a')))) =
          if a' = b then (p : R.Kf) ^ ka b else 0 := by
        have hub : u b = detY R.Kf mm ^ Q * map (algebraMap R.O R.Kf) (resY R.O mm (s0 b)) := by
          rw [← hs0e b, map_mul, map_pow, detY_map]
        rw [hLV, resY_mul, hres0, resY_map hSM, resY_map hSM, ht0e, ← hub, hdiag a' b]
      have hsh : nuOf (wtPQ (mm + 1) (2 * ccl) (Q + 2 * ccl)) =
          nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl)) + nuOf (wtPQ (mm + 1) 0 Q) := by
        have := nuOf_wt_add mm (2 * ccl) (2 * ccl) 0 Q
        rwa [add_zero, add_comm (2 * ccl) Q] at this
      rw [hκ, hsh, (hHw R.Kf _ _ _ (hwA (2 * ccl) (2 * ccl)) (hwA 0 Q)).1] at hΨ
      have hne : hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q)) ≠ 0 := hwNe R.Kf _ _ le_rfl _
      have hΦ := mul_left_cancel₀ hne (a := hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) 0 Q)))
        (c := C (if a' = b then (p : R.Kf) ^ ka b else 0) * hw R.Kf (le_refl (mm + 1 + 1)) (nuOf (wtPQ (mm + 1) (2 * ccl) (2 * ccl))))
        (by rw [← e2, hΨ]; ring)
      rw [e1, hΦ]
      split_ifs
      · rw [smul_eq_C_mul]; ring
      · rw [C_0, zero_mul, mul_zero]

end Formalism.MainNotions.flipOneThree.Pf

end
end

section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf.QB

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

variable {K : Type} [Field K] {r : ℕ}

theorem caseN (t0 : Fin (r + 1 + 1)) (h0 : midOf t0 = none) (c : K) (b : Bool)
    (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) :
    psiB (MvPolynomial (Bool × (Fin r × Fin r)) K) (scCol K (r + 1 + 1) t0 c) (th K r b v) =
      th K r b (scCol K (r + 1 + 1) t0 c v) := by
  have key := hom_eq_on
    ((psiB (MvPolynomial (Bool × (Fin r × Fin r)) K) (scCol K (r + 1 + 1) t0 c)).comp (th K r b).toRingHom)
    ((th K r b).toRingHom.comp (scCol K (r + 1 + 1) t0 c).toRingHom) ?_ ?_ v
  · simpa using key
  · intro a
    simp [th_C, psiB_C]
  · rintro ⟨a, t⟩
    rcases midOf_cases t with ⟨j, rfl⟩ | ⟨ht, -⟩
    · have hne : ∀ i : Fin r, midI r i ≠ t0 := fun i => midOf_none_ne h0 i
      simp [th_X_mid, psiB_X, scCol_X, hne, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [psiB_C]
    · simp [th_X_none _ _ _ _ _ ht, psiB_X, scCol_X]

theorem lam_scaleN (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K) (t0 : Fin (r + 1 + 1)) (h0 : midOf t0 = none)
    (c : K) (ν ν' : Fin (r + 1 + 1) → ℕ) (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (hv : IsWeightedHomogeneous (colW (r + 1 + 1) (r + 1 + 1)) v ν)
    (ht : IsWeightedHomogeneous (colW (r + 1 + 1) (r + 1 + 1)) t ν') :
    scCol K (r + 1 + 1) t0 c (lamOf K r L (blockEmb K true v * blockEmb K false t)) =
      c ^ (ν t0 + ν' t0) • lamOf K r L (blockEmb K true v * blockEmb K false t) := by
  rw [lam_eq, lcoef_comm, map_mul, caseN t0 h0, caseN t0 h0, scCol_of_hom _ _ _ _ hv, scCol_of_hom _ _ _ _ ht,
    map_smul, map_smul, smul_mul_smul_comm, ← pow_add, map_smul]

def thR (K : Type) [Field K] (r : ℕ) (ρ : MvPolynomial (Fin r × Fin r) K →ₐ[K] MvPolynomial (Fin r × Fin r) K) (b : Bool) :
    MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K →ₐ[K]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K) :=
  (mapAlgHom ((blockEmb K (k := r) (n := r) b).comp ρ)).comp (subY K r)

theorem thR_coeff (ρ : MvPolynomial (Fin r × Fin r) K →ₐ[K] MvPolynomial (Fin r × Fin r) K) (b : Bool)
    (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) (u : Fin (r + 1 + 1) × Fin (r + 1 + 1) →₀ ℕ) :
    coeff u (thR K r ρ b v) = blockEmb K b (ρ (coeff u (subY K r v))) := by
  simp only [thR, AlgHom.comp_apply, mAH_coeff]

theorem caseM (ψ : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K →ₐ[K] MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (ρ : MvPolynomial (Fin r × Fin r) K →ₐ[K] MvPolynomial (Fin r × Fin r) K)
    (hgen : ∀ (b : Bool) (a : Fin (r + 1 + 1)) (j' : Fin r),
      ∑ i : Fin r, (C (X (b, (i, j'))) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K)) *
          map (algebraMap K (MvPolynomial (Bool × (Fin r × Fin r)) K)) (ψ (X (a, midI r i))) =
        ∑ i : Fin r, C (blockEmb K b (ρ (X (i, j')))) * X (a, midI r i))
    (hnone : ∀ a t, midOf t = none → ψ (X (a, t)) = X (a, t)) (b : Bool)
    (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) :
    psiB (MvPolynomial (Bool × (Fin r × Fin r)) K) ψ (th K r b v) = thR K r ρ b v := by
  have key := hom_eq_on
    ((psiB (MvPolynomial (Bool × (Fin r × Fin r)) K) ψ).comp (th K r b).toRingHom)
    (thR K r ρ b).toRingHom ?_ ?_ v
  · simpa using key
  · intro a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, th_C]
    rw [psiB_C]
    simp only [thR, AlgHom.comp_apply, subY_C, mAH_C, AlgHom.commutes]
    simp
  · rintro ⟨a, t⟩
    rcases midOf_cases t with ⟨j, rfl⟩ | ⟨ht, -⟩
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, th_X_mid, map_sum, map_mul]
      simp only [thR, AlgHom.comp_apply, mAH_subY_mid]
      rw [← hgen b a j]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [psiB_C, psiB_X]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, th_X_none _ _ _ _ _ ht]
      simp only [thR, AlgHom.comp_apply, mAH_subY_none _ _ _ _ ht]
      rw [psiB_X, hnone a t ht, map_X]

theorem lam_caseM (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K) (N : ℕ) (α α' : Fin r → ℕ)
    (hInv : PhInv K r N α α' L)
    (ψ : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K →ₐ[K] MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (l : Matrix (Fin r) (Fin r) K) (hl : IsUnit l.det)
    (hgen : ∀ (b : Bool) (a : Fin (r + 1 + 1)) (j' : Fin r),
      ∑ i : Fin r, (C (X (b, (i, j'))) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K)) *
          map (algebraMap K (MvPolynomial (Bool × (Fin r × Fin r)) K)) (ψ (X (a, midI r i))) =
        ∑ i : Fin r, C (blockEmb K b (rowAct K l (X (i, j')))) * X (a, midI r i))
    (hnone : ∀ a t, midOf t = none → ψ (X (a, t)) = X (a, t))
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (hv : ∀ u, coeff u (subY K r v) ∈ dualWeyl K r r α) (ht : ∀ u, coeff u (subY K r t) ∈ dualWeyl K r r α') :
    ψ (lamOf K r L (blockEmb K true v * blockEmb K false t)) =
      l.det ^ N • lamOf K r L (blockEmb K true v * blockEmb K false t) := by
  have hc : ∀ (h : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K))
      (u : Fin (r + 1 + 1) × Fin (r + 1 + 1) →₀ ℕ), coeff u (lcoef L h) = L (coeff u h) := by
    intro h u
    exact coeff_sum_monomial_linear L h u
  rw [lam_eq, lcoef_comm, map_mul, caseM ψ (rowAct K l) hgen hnone, caseM ψ (rowAct K l) hgen hnone]
  ext u
  rw [coeff_smul, hc, hc, coeff_mul, coeff_mul, map_sum, map_sum, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [thR_coeff, thR_coeff, th_coeff, th_coeff]
  exact hInv l hl _ (hv p.1) _ (ht p.2)

theorem lam_scaleM (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K) (N : ℕ) (α α' : Fin r → ℕ)
    (hInv : PhInv K r N α α' L) (j : Fin r) (c : K) (hc : c ≠ 0)
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (hv : ∀ u, coeff u (subY K r v) ∈ dualWeyl K r r α) (ht : ∀ u, coeff u (subY K r t) ∈ dualWeyl K r r α') :
    scCol K (r + 1 + 1) (midI r j) c (lamOf K r L (blockEmb K true v * blockEmb K false t)) =
      c ^ N • lamOf K r L (blockEmb K true v * blockEmb K false t) := by
  classical
  have hdet : (Matrix.diagonal (fun i : Fin r => if i = j then c else 1)).det = c := by
    rw [Matrix.det_diagonal, Finset.prod_ite_eq']
    simp
  have key := lam_caseM L N α α' hInv (scCol K (r + 1 + 1) (midI r j) c)
    (Matrix.diagonal (fun i : Fin r => if i = j then c else 1)) (by rw [hdet]; exact hc.isUnit) ?_ ?_ v t hv ht
  · rw [hdet] at key
    exact key
  · intro b a j'
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [scCol_X, midI_inj, rowAct, aeval_X, Matrix.diagonal_apply, blockEmb, map_mul, map_C, map_X,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_sum, rename_C, rename_X]
    rw [Finset.sum_eq_single i (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
    simp only [if_true, MvPolynomial.algebraMap_eq]
    ring
  · intro a t' ht'
    rw [scCol_X]
    have hne : t' ≠ midI r j := fun e => midOf_none_ne ht' j e.symm
    simp [hne]

theorem rowAct_transv (l j : Fin r) (c : K) (i t : Fin r) :
    rowAct K (Matrix.transvection l j c) (X (i, t)) = X (i, t) + if i = l then C c * X (j, t) else 0 := by
  classical
  simp only [rowAct, aeval_X, Matrix.transvection, Matrix.add_apply, Matrix.one_apply]
  simp only [map_add, add_mul, Finset.sum_add_distrib, apply_ite C, ite_mul, map_one, map_zero, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1
  by_cases h : i = l
  · subst h
    simp only [Matrix.single_apply, true_and]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  · have h' : ¬ l = i := fun e => h e.symm
    simp [Matrix.single_apply, h, h']

theorem lam_addM (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K) (N : ℕ) (α α' : Fin r → ℕ)
    (hInv : PhInv K r N α α' L) (l j : Fin r) (hlj : l ≠ j) (c : K)
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (hv : ∀ u, coeff u (subY K r v) ∈ dualWeyl K r r α) (ht : ∀ u, coeff u (subY K r t) ∈ dualWeyl K r r α') :
    colAdd K (midI r l) (midI r j) c (lamOf K r L (blockEmb K true v * blockEmb K false t)) =
      lamOf K r L (blockEmb K true v * blockEmb K false t) := by
  classical
  have hdet : (Matrix.transvection l j c).det = 1 := Matrix.det_transvection_of_ne l j hlj c
  have key := lam_caseM L N α α' hInv (colAdd K (midI r l) (midI r j) c) (Matrix.transvection l j c)
    (by rw [hdet]; exact isUnit_one) ?_ ?_ v t hv ht
  · rw [hdet, one_pow, one_smul] at key
    exact key
  · intro b a j'
    simp only [rowAct_transv, colAdd, aeval_X, midI_inj]
    have e : ∀ i : Fin r, (if i = j then X (a, midI r i) + C c * X (a, midI r l) else X (a, midI r i) :
        MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) =
        X (a, midI r i) + if i = j then C c * X (a, midI r l) else 0 := by
      intro i
      split_ifs <;> simp
    simp only [e, map_add, map_mul, map_C, map_X, blockEmb, rename_X, rename_C, mul_add, add_mul,
      Finset.sum_add_distrib, apply_ite, map_zero, mul_ite, ite_mul, mul_zero, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hs : ∀ (k : Fin r)
        (f g : Fin r → MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K)),
        (∑ x : Fin r, if x = k then f x + g x else f x + 0) = (∑ x : Fin r, f x) + g k := by
      intro k f g
      have h1 : ∀ x, (if x = k then f x + g x else f x + 0) = f x + if x = k then g x else 0 := by
        intro x
        split_ifs <;> simp
      simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hs j (fun x => C (X (b, x, j')) * X (a, midI r x))
        (fun x => C (X (b, x, j')) * (C ((algebraMap K (MvPolynomial (Bool × Fin r × Fin r) K)) c) * X (a, midI r l))),
      hs l (fun x => C (X (b, x, j')) * X (a, midI r x)) (fun x => C (C c) * C (X (b, j, j')) * X (a, midI r x))]
    simp only [MvPolynomial.algebraMap_eq]
    ring
  · intro a t' ht'
    have hne : t' ≠ midI r j := fun e => midOf_none_ne ht' j e.symm
    simp [colAdd, hne]

end Formalism.MainNotions.flipOneThree.Pf.QB

end
end

section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf.QB

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

theorem multiInv {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (r : ℕ)
    (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A)
    (hv : ∀ l j : Fin (r + 1 + 1), l < j → colAddGen A l j v = rename some v)
    (θ : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A →ₐ[A] S) (e : Fin r → S) (J : Finset (Fin r)) :
    aeval (fun w : Fin (r + 1 + 1) × Fin (r + 1 + 1) =>
      θ (X w) + (∑ j ∈ J, if w.2 = midI r j then e j else 0) * θ (X (w.1, 0))) v = θ v := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, zero_mul, add_zero]
    exact (congrArg (fun ψ => ψ v) (MvPolynomial.aeval_unique θ)).symm
  | @insert j0 J hj0 ih =>
    have h0 := hv 0 (midI r j0) (Fin.succ_pos _)
    set f : Fin (r + 1 + 1) × Fin (r + 1 + 1) → S := fun w =>
      θ (X w) + (∑ j ∈ J, if w.2 = midI r j then e j else 0) * θ (X (w.1, 0)) with hf
    have hz : ∀ j : Fin r, ((0 : Fin (r + 1 + 1)) = midI r j) ↔ False :=
      fun j => ⟨fun h => Fin.succ_ne_zero _ h.symm, False.elim⟩
    have hφ : (aeval (Option.elim' (e j0) f)).comp (colAddGen A 0 (midI r j0)) =
        aeval (fun w : Fin (r + 1 + 1) × Fin (r + 1 + 1) =>
          θ (X w) + (∑ j ∈ insert j0 J, if w.2 = midI r j then e j else 0) * θ (X (w.1, 0))) := by
      rw [colAddGen, MvPolynomial.comp_aeval]
      congr 1
      funext w
      by_cases hw : w.2 = midI r j0
      · simp [hw, hf, Finset.sum_insert hj0, hz]
        try ring
      · simp [hw, hf, Finset.sum_insert hj0, hz]
        try ring
    rw [← hφ, AlgHom.comp_apply, h0, MvPolynomial.aeval_rename]
    exact ih

variable {K : Type} [Field K] {r : ℕ}

theorem caseC (j0 : Fin r) (c : K) (b : Bool) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (hv : ∀ l j : Fin (r + 1 + 1), l < j → colAddGen K l j v = rename some v) :
    psiB (MvPolynomial (Bool × (Fin r × Fin r)) K) (colAdd K 0 (midI r j0) c) (th K r b v) = th K r b v := by
  classical

  have hmidOf_midI : ∀ j : Fin r, midOf (midI r j) = some j := by
    intro j
    unfold midOf midI
    rw [dif_pos (by first | (simp [Fin.val_succ]; done) | (simp [Fin.val_succ]; omega))]
    exact congrArg some (Fin.ext (by simp [Fin.val_succ]))
  have hsome : ∀ (t : Fin (r + 1 + 1)) (j : Fin r), midOf t = some j → t = midI r j := by
    intro t j h
    unfold midOf at h
    split_ifs at h with h1
    cases h
    apply Fin.ext
    simp [midI, Fin.val_succ]
    omega
  have hnone : ∀ (t : Fin (r + 1 + 1)) (j : Fin r), midOf t = none → t ≠ midI r j := by
    intro t j h ht
    rw [ht, hmidOf_midI] at h
    cases h
  have h00 : midOf (0 : Fin (r + 1 + 1)) = none := by
    unfold midOf
    rw [dif_neg (by simp)]
  have hth0 : ∀ a, th K r b (X (a, 0)) = X (a, 0) := by
    intro a
    simp [th, Formalism.MainNotions.flipOneThree.Pf.subY, h00]
  let e : Fin r → MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K) :=
    fun j => C (C c * X (b, (j0, j)))
  have hmult := multiInv r v hv (th K r b) e Finset.univ
  have key : (psiB (MvPolynomial (Bool × (Fin r × Fin r)) K) (colAdd K 0 (midI r j0) c)).comp (th K r b).toRingHom =
      (aeval (fun w : Fin (r + 1 + 1) × Fin (r + 1 + 1) =>
        th K r b (X w) + (∑ j ∈ Finset.univ, if w.2 = midI r j then e j else 0) * th K r b (X (w.1, 0)))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro k
      simp [th, psiB, MvPolynomial.algebraMap_apply]
    · rintro ⟨a, t⟩
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, hth0]
      rcases hw : midOf t with _ | j
      · have e1 : th K r b (X (a, t)) = X (a, t) := by simp [th, Formalism.MainNotions.flipOneThree.Pf.subY, hw]
        have hz : (∑ j ∈ Finset.univ, if t = midI r j then e j else 0) = 0 :=
          Finset.sum_eq_zero fun j _ => if_neg (hnone t j hw)
        rw [e1, hz, zero_mul, add_zero]
        simp [psiB, Formalism.GradedWeylDivisibility.colAdd, hnone t j0 hw]
      · have ht : t = midI r j := hsome t j hw
        subst ht
        have e1 : th K r b (X (a, midI r j)) = ∑ i : Fin r, C (X (b, (i, j))) * X (a, midI r i) := by
          simp [th, Formalism.MainNotions.flipOneThree.Pf.subY, hmidOf_midI, Formalism.GradedWeylDivisibility.blockEmb]
        have hz : (∑ j' ∈ Finset.univ, if midI r j = midI r j' then e j' else 0) = e j := by
          rw [Finset.sum_eq_single j]
          · simp
          · intro j' _ hj'
            rw [if_neg]
            intro h
            apply hj'
            have := congrArg midOf h
            rw [hmidOf_midI, hmidOf_midI] at this
            exact (Option.some_injective _ this).symm
          · simp
        have hmid : ∀ i : Fin r, i ≠ j0 → midI r i ≠ midI r j0 := by
          intro i hi h
          apply hi
          have h2 := congrArg midOf h
          rw [hmidOf_midI, hmidOf_midI] at h2
          exact Option.some_injective _ h2
        have hterm : ∀ i : Fin r, psiB (MvPolynomial (Bool × (Fin r × Fin r)) K) (colAdd K 0 (midI r j0) c)
            (C (X (b, (i, j))) * X (a, midI r i)) =
            C (X (b, (i, j))) * X (a, midI r i) + (if i = j0 then e j * X (a, 0) else 0) := by
          intro i
          simp only [psiB, map_mul, coe_eval₂Hom, eval₂_C, eval₂_X, Formalism.GradedWeylDivisibility.colAdd, aeval_X]
          by_cases hi : i = j0
          · subst hi
            simp [e, MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
            ring
          · simp [hmid i hi, hi]
        rw [e1, hz, map_sum, Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib]
        simp
  exact (RingHom.congr_fun key v).trans hmult

theorem lam_addC (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K) (j0 : Fin r) (c : K)
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (hv : ∀ l j : Fin (r + 1 + 1), l < j → colAddGen K l j v = rename some v)
    (ht : ∀ l j : Fin (r + 1 + 1), l < j → colAddGen K l j t = rename some t) :
    colAdd K 0 (midI r j0) c (lamOf K r L (blockEmb K true v * blockEmb K false t)) =
      lamOf K r L (blockEmb K true v * blockEmb K false t) := by
  rw [lam_eq, lcoef_comm, map_mul, caseC j0 c true v hv, caseC j0 c false t ht]

end Formalism.MainNotions.flipOneThree.Pf.QB

end
end

section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.flipOneThree.Pf.QB

theorem lamMemP : LamMemP := by
  intro K _ _ r N ν ν' νp L hνl hν'l hνpl hνp0 hνpm hPh v hv t ht
  have hsv := fun u => subCoeffP K r ν v hv u
  have hst := fun u => subCoeffP K r ν' t ht u
  obtain ⟨hvw, hvi⟩ := mem_dualWeyl_iff.mp hv
  obtain ⟨htw, hti⟩ := mem_dualWeyl_iff.mp ht
  set F := lamOf K r L (blockEmb K true v * blockEmb K false t) with hF
  have hscale : ∀ t0 : Fin (r + 1 + 1), ∀ c : K, c ≠ 0 →
      scCol K (r + 1 + 1) t0 c F = c ^ νp t0 • F := by
    intro t0 c hc
    rcases midOf_cases t0 with ⟨j, rfl⟩ | ⟨hn, h0 | hl⟩
    · rw [hνpm j]
      exact lam_scaleM L N _ _ hPh j c hc v t hsv hst
    · rw [lam_scaleN L t0 hn c ν ν' v t hvw htw]
      subst h0
      rw [hνp0]
    · rw [lam_scaleN L t0 hn c ν ν' v t hvw htw]
      subst hl
      rw [hνl, hν'l, hνpl]
  have hcol : ∀ (l j : Fin (r + 1 + 1)), l < j → ∀ c : K, colAdd K l j c F = F := by
    intro l j hlj c
    rcases midOf_cases j with ⟨j', rfl⟩ | ⟨hn, h0 | hl⟩
    · rcases midOf_cases l with ⟨l', rfl⟩ | ⟨hn', h0' | hl'⟩
      · have hne : l' ≠ j' := by
          rintro rfl
          exact lt_irrefl _ hlj
        exact lam_addM L N _ _ hPh l' j' hne c v t hsv hst
      · subst h0'
        exact lam_addC L j' c v t hvi hti
      · subst hl'
        exact absurd hlj (not_lt.mpr (Fin.le_last _))
    · subst h0
      exact absurd hlj (Fin.not_lt_zero _)
    · subst hl
      apply colAdd_trivial
      intro m hm
      rw [wt_of_scale (Fin.last (r + 1)) (νp (Fin.last (r + 1))) F (hscale _) m hm, hνpl]
  rw [mem_dualWeyl_iff]
  refine ⟨?_, ?_⟩
  · intro m hm
    funext t0
    exact wt_of_scale t0 (νp t0) F (hscale t0) m hm
  · intro l j hlj
    apply MvPolynomial.funext
    intro x
    have h1 := congrArg (fun φ => φ F) (lsat_eval_colAddGen (R := K) l j x)
    simp only [AlgHom.comp_apply, hcol l j hlj] at h1
    simpa [MvPolynomial.eval_rename, MvPolynomial.coe_aeval_eq_eval] using h1

theorem subCoeffP : SubCoeffP := QB.subCoeffP

end Formalism.MainNotions.flipOneThree.Pf

end
end

section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

section LC

variable {K σ ρ : Type} [Field K]

private theorem coeff_lcoef_eq (L : MvPolynomial ρ K →ₗ[K] K) (f : MvPolynomial σ (MvPolynomial ρ K))
    (w : σ →₀ ℕ) : coeff w (lcoef L f) = L (coeff w f) :=
  coeff_sum_monomial_linear L f w


theorem qa_lcoef_C (L : MvPolynomial ρ K →ₗ[K] K) (b : MvPolynomial ρ K) :
    lcoef L (C b : MvPolynomial σ (MvPolynomial ρ K)) = C (L b) := by
  classical
  ext w
  rw [coeff_lcoef_eq, coeff_C, coeff_C]
  split_ifs <;> simp

theorem qa_lcoef_mapC_mul (L : MvPolynomial ρ K →ₗ[K] K) (G : MvPolynomial σ K)
    (h : MvPolynomial σ (MvPolynomial ρ K)) : lcoef L (map C G * h) = G * lcoef L h := by
  classical
  ext w
  rw [coeff_lcoef_eq, coeff_mul, coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coeff_map, coeff_lcoef_eq, MvPolynomial.C_mul', map_smul, smul_eq_mul]

theorem qa_eval_lcoef (L : MvPolynomial ρ K →ₗ[K] K) (x : σ → K) (h : MvPolynomial σ (MvPolynomial ρ K)) :
    eval x (lcoef L h) = L (eval (fun i => C (x i)) h) := by
  classical
  rw [show lcoef L h = ∑ u ∈ h.support, monomial u (L (coeff u h)) from rfl, map_sum]
  conv_rhs => rw [h.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [eval_monomial, eval_monomial]
  rw [show (u.prod fun n e => (C (x n) : MvPolynomial ρ K) ^ e) = C (u.prod fun n e => x n ^ e) by
    simp [Finsupp.prod, map_prod, map_pow]]
  rw [mul_comm (coeff u h), MvPolynomial.C_mul', map_smul, smul_eq_mul, mul_comm]

theorem qa_lcoef_rowAct {k n : ℕ} (L : MvPolynomial ρ K →ₗ[K] K) (g : Matrix (Fin k) (Fin k) K)
    (h : MvPolynomial (Fin k × Fin n) (MvPolynomial ρ K)) :
    lcoef L (rowAct (MvPolynomial ρ K) (g.map C) h) = rowAct K g (lcoef L h) := by
  classical
  have key : ∀ P : MvPolynomial (Fin k × Fin n) K,
      rowAct (MvPolynomial ρ K) (g.map C) (map C P) = map C (rowAct K g P) := by
    intro P
    have e := MvPolynomial.ringHom_ext
      (f := ((rowAct (MvPolynomial ρ K) (n := n) (g.map C)).toRingHom.comp (map C) :
        MvPolynomial (Fin k × Fin n) K →+* MvPolynomial (Fin k × Fin n) (MvPolynomial ρ K)))
      (g := ((map C).comp (rowAct K (n := n) g).toRingHom :
        MvPolynomial (Fin k × Fin n) K →+* MvPolynomial (Fin k × Fin n) (MvPolynomial ρ K)))
      (fun a => by simp [rowAct]) (fun i => by simp [rowAct, Matrix.map_apply, map_sum])
    simpa using RingHom.congr_fun e P
  conv_lhs => rw [h.as_sum]
  conv_rhs => rw [h.as_sum]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hm : (monomial u (coeff u h) : MvPolynomial (Fin k × Fin n) (MvPolynomial ρ K)) =
      map C (monomial u 1) * C (coeff u h) := by
    rw [map_monomial, map_one, mul_comm, C_mul_monomial, mul_one]
  have hr1 : rowAct (MvPolynomial ρ K) (n := n) (g.map C) (C (coeff u h)) = C (coeff u h) := by simp [rowAct]
  have hr2 : rowAct K (n := n) g (C (L (coeff u h))) = C (L (coeff u h)) := by simp [rowAct]
  rw [hm, map_mul, key, hr1, qa_lcoef_mapC_mul, qa_lcoef_mapC_mul, qa_lcoef_C, map_mul, hr2]

end LC

section S2

variable {K : Type} [Field K] {r : ℕ}

theorem qa_blockEmb_C {S : Type} {k n : ℕ} (b : S) (a : K) : blockEmb K (k := k) (n := n) b (C a) = C a := by
  simp [blockEmb]

theorem qa_blockEmb_X {S : Type} {k n : ℕ} (b : S) (x : Fin k × Fin n) : blockEmb K b (X x) = X (b, x) := by
  simp [blockEmb]

theorem block_substitution_C (a : K) : sub2 K r (C a) = C (C a) := by
  simp [sub2]

theorem block_substitution_X (b : Bool) (x : Fin (r + 1 + 1) × Fin (r + 1 + 1)) :
    sub2 K r (X (b, x)) = map (blockEmb K (k := r) (n := r) b).toRingHom (subY K r (X x)) := by
  simp [sub2]

theorem block_substitution_blockEmb (b : Bool) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) :
    sub2 K r (blockEmb K b v) = map (blockEmb K (k := r) (n := r) b).toRingHom (subY K r v) := by
  induction v using MvPolynomial.induction_on
  next a =>
    rw [qa_blockEmb_C, block_substitution_C]
    simp [subY, qa_blockEmb_C]
  next p q hp hq =>
    rw [map_add, map_add, hp, hq, map_add, map_add]
  next p x hp =>
    rw [map_mul, map_mul, hp, qa_blockEmb_X, block_substitution_X, map_mul, map_mul]

theorem qa_blockEmb_comp_C (b : Bool) :
    ((blockEmb K (k := r) (n := r) b).toRingHom).comp C = (C : K →+* MvPolynomial (Bool × (Fin r × Fin r)) K) := RingHom.ext fun a => by simp [qa_blockEmb_C]

theorem qa_lamOf_apply (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K)
    (x : MvPolynomial (Bool × (Fin (r + 1 + 1) × Fin (r + 1 + 1))) K) : lamOf K r L x = lcoef L (sub2 K r x) := rfl

theorem qa_eval_map_block (b : Bool)
    (h : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) K)) :
    eval (fun i => (C (idPoint K (r + 1 + 1) (r + 1 + 1) i) : MvPolynomial (Bool × (Fin r × Fin r)) K))
        (map (blockEmb K (k := r) (n := r) b).toRingHom h) =
      blockEmb K b (eval (idPoint (MvPolynomial (Fin r × Fin r) K) (r + 1 + 1) (r + 1 + 1)) h) := by
  rw [MvPolynomial.eval_map]
  show _ = (blockEmb K (k := r) (n := r) b).toRingHom
    (MvPolynomial.eval₂ (RingHom.id _) (idPoint (MvPolynomial (Fin r × Fin r) K) (r + 1 + 1) (r + 1 + 1)) h)
  rw [MvPolynomial.eval₂_comp_left, RingHom.comp_id]
  congr 1
  funext i
  simp only [idPoint, Function.comp_apply]
  split_ifs <;> simp

end S2

theorem lamCoeffP : LamCoeffP := by
  classical
  intro K _ r L v t u
  rw [qa_lamOf_apply, map_mul, block_substitution_blockEmb, block_substitution_blockEmb, coeff_lcoef_eq, coeff_mul, map_sum]
  simp only [coeff_map]
  rfl

theorem lamMulP : LamMulP := by
  classical
  intro K _ r Q L F s t hF
  rw [qa_lamOf_apply, map_mul (blockEmb K true) F s, map_mul (sub2 K r), map_mul (sub2 K r),
    block_substitution_blockEmb, block_substitution_blockEmb, block_substitution_blockEmb, hF,
    map_mul (map (blockEmb K (k := r) (n := r) true).toRingHom), map_C, MvPolynomial.map_map,
    qa_blockEmb_comp_C, ← qa_lcoef_mapC_mul]
  congr 1
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  ring

theorem lamEvalP : LamEvalP := by
  classical
  intro K _ r L v t
  rw [qa_lamOf_apply, map_mul, block_substitution_blockEmb, block_substitution_blockEmb, qa_eval_lcoef, map_mul,
    qa_eval_map_block, qa_eval_map_block]
  rfl

theorem lamEquivP : LamEquivP := by
  intro K _ r L g v t
  have hcomm : ∀ (b : Bool) (P : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) K)),
      map (blockEmb K (k := r) (n := r) b).toRingHom
          (rowAct (MvPolynomial (Fin r × Fin r) K) (n := r + 1 + 1) (g.map C) P) =
        rowAct (MvPolynomial (Bool × (Fin r × Fin r)) K) (n := r + 1 + 1) (g.map C)
          (map (blockEmb K (k := r) (n := r) b).toRingHom P) := by
    intro b P
    have e := MvPolynomial.ringHom_ext
      (f := ((map (blockEmb K (k := r) (n := r) b).toRingHom).comp
          (rowAct (MvPolynomial (Fin r × Fin r) K) (n := r + 1 + 1) (g.map C)).toRingHom :
        MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) K) →+*
          MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K)))
      (g := ((rowAct (MvPolynomial (Bool × (Fin r × Fin r)) K) (n := r + 1 + 1) (g.map C)).toRingHom.comp
          (map (blockEmb K (k := r) (n := r) b).toRingHom) :
        MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) K) →+*
          MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K)))
      (fun c => by simp [rowAct]) (fun i => by simp [rowAct, Matrix.map_apply, map_sum, qa_blockEmb_C])
    simpa using RingHom.congr_fun e P
  rw [qa_lamOf_apply, qa_lamOf_apply, map_mul (sub2 K r), map_mul (sub2 K r), block_substitution_blockEmb,
    block_substitution_blockEmb, block_substitution_blockEmb, block_substitution_blockEmb, qa_subY_rowAct, qa_subY_rowAct, hcomm, hcomm,
    ← map_mul (rowAct (MvPolynomial (Bool × (Fin r × Fin r)) K) (n := r + 1 + 1) (g.map C)), qa_lcoef_rowAct]

end Formalism.MainNotions.flipOneThree.Pf

end
end

section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

def vStar (m a b : ℕ) : XY (m + 1) →₀ ℕ :=
  Finsupp.single (Sum.inl 0) a + Finsupp.single (Sum.inr (Fin.last m)) b

theorem qt_comb (m a b : ℕ) (v : XY (m + 1) →₀ ℕ) (hx : xDeg v = a) (hy : yDeg v = b)
    (h0 : qtW m v 0 = a + b) (hl : qtW m v (Fin.last m) = 0) : v = vStar m a b := by
  classical
  have e0 := qtW_apply m v 0
  have el := qtW_apply m v (Fin.last m)
  have l0 : v (Sum.inl 0) ≤ xDeg v :=
    Finset.single_le_sum (f := fun i : Fin (m + 1) => v (Sum.inl i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
  have ll : v (Sum.inr (Fin.last m)) ≤ yDeg v :=
    Finset.single_le_sum (f := fun i : Fin (m + 1) => v (Sum.inr i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  have a1 : v (Sum.inl 0) = a := by omega
  have a2 : v (Sum.inr (Fin.last m)) = b := by omega
  have z1 : ∀ i : Fin (m + 1), i ≠ 0 → v (Sum.inl i) = 0 := by
    intro i hi
    have h := Finset.add_sum_erase Finset.univ (fun i : Fin (m + 1) => v (Sum.inl i)) (Finset.mem_univ 0)
    have h' : ∑ x ∈ Finset.univ.erase (0 : Fin (m + 1)), v (Sum.inl x) = 0 := by
      have : ∑ x : Fin (m + 1), v (Sum.inl x) = a := hx
      omega
    exact Finset.sum_eq_zero_iff.1 h' i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩)
  have z2 : ∀ i : Fin (m + 1), i ≠ Fin.last m → v (Sum.inr i) = 0 := by
    intro i hi
    have h := Finset.add_sum_erase Finset.univ (fun i : Fin (m + 1) => v (Sum.inr i)) (Finset.mem_univ (Fin.last m))
    have h' : ∑ x ∈ Finset.univ.erase (Fin.last m), v (Sum.inr x) = 0 := by
      have : ∑ x : Fin (m + 1), v (Sum.inr x) = b := hy
      omega
    exact Finset.sum_eq_zero_iff.1 h' i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩)
  ext w
  unfold vStar
  rw [Finsupp.add_apply]
  rcases w with i | i
  · by_cases hi : i = 0
    · subst hi; simp [a1]
    · have : (Sum.inl 0 : XY (m + 1)) ≠ Sum.inl i := fun h => hi (Sum.inl.inj h).symm
      simp [this, z1 i hi]
  · by_cases hi : i = Fin.last m
    · subst hi; simp [a2]
    · have : (Sum.inr (Fin.last m) : XY (m + 1)) ≠ Sum.inr i := fun h => hi (Sum.inr.inj h).symm
      simp [this, z2 i hi]

theorem qtW_vStar (m a b : ℕ) (hm : 1 ≤ m) : qtW m (vStar m a b) 0 = a + b ∧ qtW m (vStar m a b) (Fin.last m) = 0 := by
  classical
  have hne : (Fin.last m) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have e0 := qtW_apply m (vStar m a b) 0
  have el := qtW_apply m (vStar m a b) (Fin.last m)
  have y : yDeg (vStar m a b) = b := by
    unfold yDeg vStar
    simp [Finsupp.single_apply]
  have v1 : vStar m a b (Sum.inr 0) = 0 := by
    unfold vStar
    simp [hne]
  have v2 : vStar m a b (Sum.inl 0) = a := by
    unfold vStar
    simp
  have v3 : vStar m a b (Sum.inr (Fin.last m)) = b := by
    unfold vStar
    simp
  have v4 : vStar m a b (Sum.inl (Fin.last m)) = 0 := by
    unfold vStar
    simp [hne.symm]
  constructor <;> omega

theorem topCore (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hCO : CartanOnto) {p n' : ℕ} (R : RS p n') (m : ℕ) (hm : 1 ≤ m) (a b : ℕ)
    (Ψ : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) (hΨ : Ψ ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m a b)))
    (h0 : RowA 0 Ψ (a + b)) (hl : RowA (Fin.last m) Ψ 0) :
    ∃ c : R.Kf, Ψ = c • deltaB R.Kf m (PsiXY R.Kf m (monomial (vStar m a b) 1)) := by
  classical
  rw [← tie3 h2 h5 hCO R m hm a b] at hΨ
  obtain ⟨f, hf, rfl⟩ := hΨ
  refine ⟨coeff (vStar m a b) f, ?_⟩
  have hT : coeff (vStar m a b) f • deltaB R.Kf m (PsiXY R.Kf m (monomial (vStar m a b) 1)) =
      deltaB R.Kf m (PsiXY R.Kf m (monomial (vStar m a b) (coeff (vStar m a b) f))) := by
    rw [← map_smul, ← map_smul, smul_monomial, smul_eq_mul, mul_one]
  rw [hT]
  have hsum : dPsi R.Kf m f = ∑ v ∈ f.support, deltaB R.Kf m (PsiXY R.Kf m (monomial v (coeff v f))) := by
    conv_lhs => rw [dPsi_apply, f.as_sum]
    simp only [map_sum]
  obtain ⟨s0, sl⟩ := qtW_vStar m a b hm
  ext u
  by_cases hu : rowDeg u 0 = a + b ∧ rowDeg u (Fin.last m) = 0
  · rw [hsum, coeff_sum, Finset.sum_eq_single (vStar m a b)]
    · intro v hv hne
      by_contra hc
      apply hne
      have w0 := rowA_of_iwh (dPsi_monomial_iwh R.Kf m v (coeff v f)) 0 u hc
      have wl := rowA_of_iwh (dPsi_monomial_iwh R.Kf m v (coeff v f)) (Fin.last m) u hc
      exact qt_comb m a b v (hf v hv).1 (hf v hv).2 (by rw [← w0, hu.1]) (by rw [← wl, hu.2])
    · intro hv
      rw [notMem_support_iff.1 hv, monomial_zero, map_zero, map_zero, coeff_zero]
  · have c1 : coeff u (dPsi R.Kf m f) = 0 := by
      by_contra hc
      exact hu ⟨h0 u hc, hl u hc⟩
    have c2 : coeff u (deltaB R.Kf m (PsiXY R.Kf m (monomial (vStar m a b) (coeff (vStar m a b) f)))) = 0 := by
      by_contra hc
      have w0 := rowA_of_iwh (dPsi_monomial_iwh R.Kf m _ _) 0 u hc
      have wl := rowA_of_iwh (dPsi_monomial_iwh R.Kf m _ _) (Fin.last m) u hc
      exact hu ⟨by rw [w0, s0], by rw [wl, sl]⟩
    rw [c1, c2]

theorem topLineP_of (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hCO : CartanOnto) : TopLineP := by
  intro p n' R r hr a b Ψ hΨ h0 hl
  have hA : Antitone (nuOf (wtPQ (r + 1) a b)) := nuOf_anti _ (wtPQ_anti (r + 1) a b (by omega))
  obtain ⟨c, hc⟩ := topCore h2 h5 hCO R (r + 1) (by omega) a b Ψ hΨ h0 hl
  obtain ⟨c', hc'⟩ := topCore h2 h5 hCO R (r + 1) (by omega) a b (hw R.Kf (le_refl (r + 1 + 1)) (nuOf (wtPQ (r + 1) a b)))
    (hwMem R.Kf _ _ le_rfl _ hA)
    (by have h := rowA_hw R.Kf _ _ hA 0; rwa [nuOf_wt_zero] at h)
    (by have h := rowA_hw R.Kf _ _ hA (Fin.last (r + 1)); rwa [nuOf_last] at h)
  have he := (hwMulP R.Kf _ _ _ hA hA).2
  set Z := deltaB R.Kf (r + 1) (PsiXY R.Kf (r + 1) (monomial (vStar (r + 1) a b) 1)) with hZ
  rw [hc', smul_eq_C_mul, map_mul, eval_C] at he
  rw [hc', hc, smul_eq_C_mul, smul_eq_C_mul, map_mul, eval_C, ← mul_assoc, ← C_mul]
  congr 2
  rw [mul_assoc, mul_comm _ c', he, mul_one]

end Formalism.MainNotions.flipOneThree.Pf

end
end

section
namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem qPh_of_rest (hTau : TauP) (hSm : SmithP) : QPh :=
  qPh_of hTau hSm bilinP detFactsP numP detDivP

theorem contraction_of_pairing_GL (hPh : QPh) (hCO : CartanOnto) : ContractionStandardLattice :=
  contraction_of_pairing_lemmas hPh subCoeffP subMapP subRowP lamCoeffP lamEquivP lamMulP lamEvalP lamMemP
    (subMuP_of explicit_map_onto_two_letter_space two_letter_lattice_gauss_inverse hCO) (topLineP_of explicit_map_onto_two_letter_space two_letter_lattice_gauss_inverse hCO) liftP detDivP intCapP hwMulP

theorem theorem_I_of_contraction (D : Formalism.BasicNotions.D7) (hQ : ContractionStandardLattice) : SecondPartClosed D :=
  theorem_I_of_two_letter_clauses_contraction D explicit_map_injective explicit_map_onto_two_letter_space two_letter_lattice_gauss_inverse hQ

theorem theorem_I_of_pairing_GL (D : Formalism.BasicNotions.D7) (hPh : QPh) : SecondPartClosed D := by
  intro hA
  obtain ⟨T0, -, h0⟩ := hA 0 le_rfl
  obtain ⟨T1, -, h1⟩ := h0 T0 le_rfl
  obtain ⟨T2, -, h2⟩ := h1 T1 T1 T1 le_rfl le_rfl le_rfl
  obtain ⟨CA, Ckap, Ct, Cs, -, -, -, -, hB⟩ := h2 T2 le_rfl
  have hT : AdmT D := hB.2.2.2.2
  have h11 : GradedLatticeStable D := hT.2.2.2.2.2.2.1
  exact theorem_I_of_contraction D (contraction_of_pairing_GL hPh h11.2) hA

end Formalism.MainNotions.flipOneThree.Pf
end
