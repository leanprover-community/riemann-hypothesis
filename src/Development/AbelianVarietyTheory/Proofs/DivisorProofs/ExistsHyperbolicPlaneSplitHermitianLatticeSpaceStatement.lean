import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HermitianHassePrincipleHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddConjEqOneOfFormallyUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionHermitianLinearFormFgModule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicDualPartnerSelfDualHermitianLatti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualHermitianLatticeExistsNonzeroPairing
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionOfHasHermitianSignature
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHermitianSignatureComplementHyperbolicPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceBasisHyperbolicPlaneComplement

section
open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.HermIso

theorem posIndex_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) :
    GlobalTheory.Inertia.posIndex M = r := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let D : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ :=
    Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1))
  have hD : Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1) = D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [D, Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have hA' : A'ᵀ * M * A'.map (starRingEnd ℂ) = D.submatrix e.symm e.symm := by
    rw [← hD, ← hA]
    ext i j
    simp [A', Matrix.mul_apply, Matrix.transpose_apply]
  have hdet : A'.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hA'
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, Matrix.det_submatrix_equiv_self,
      Matrix.det_diagonal] at h1
    simp [Fintype.prod_sum_type] at h1
    exact pow_ne_zero s (by norm_num) h1.symm
  rw [← GlobalTheory.Inertia.posIndex_congr M hdet, hA', GlobalTheory.Inertia.posIndex_submatrix_equiv,
    GlobalTheory.Inertia.posIndex_diagonal]
  rw [Finset.card_filter, Fintype.sum_sum_type]
  simp

theorem exists_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ (n : ℕ) (Y : Spc F E n) (r s : ℕ), 3 ≤ n → 1 ≤ r → 1 ≤ s →
    Y.IsHerm σ B r s → ∃ x : Fin n → E, x ≠ 0 ∧ form σ Y.J x x = 0 := by
  intro F E _ _ _ _ _ σ B hB n Y r s hn hr hs hY
  obtain ⟨-, hEC, h2, hconj⟩ := hB.cm
  obtain ⟨w0⟩ : Nonempty (InfinitePlace E) := inferInstance
  have invol : ∀ x, σ (σ x) = x := fun x =>
    w0.embedding.injective (by rw [hconj, hconj, star_star])
  let σe : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext invol) (AlgHom.ext invol)
  have hne : σe ≠ 1 := by
    intro h
    have hid : ∀ x, σ x = x := fun x => by simpa [σe] using DFunLike.congr_fun h x
    have hre : ComplexEmbedding.IsReal w0.embedding :=
      ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => by
        rw [ComplexEmbedding.conjugate_coe_eq]
        have := hconj w0.embedding x
        rw [hid] at this
        exact this.symm)
    exact InfinitePlace.not_isReal_iff_isComplex.2 (hEC.isComplex w0) (InfinitePlace.isReal_iff.2 hre)
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  obtain ⟨hc, hF, θ, hθ0, hθ⟩ := GlobalTheory.HermGlobal.involutive_and_fixed hne
  obtain ⟨P, g, hP, hPg, hgf, hg0⟩ := GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E))
    two_ne_zero (fun t => invol t) (G := Y.J) (fun a b => hY.herm b a)
  have hgf' : ∀ i, σ (g i) = g i := fun i => hgf i
  have key : ∀ y : Fin n → E,
      form σ Y.J (P *ᵥ y) (P *ᵥ y) = y ⬝ᵥ Matrix.diagonal g *ᵥ (fun i => σ (y i)) := by
    intro y
    have h1 : (fun i => σ ((P *ᵥ y) i)) = (P.map (σ : E →+* E)) *ᵥ (fun i => σ (y i)) := by
      funext i
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [form, h1, ← hPg]
    simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mulVec_mulVec]
    rw [← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, Matrix.mul_assoc]
  by_cases hz : ∃ i, g i = 0
  · obtain ⟨i, hi⟩ := hz
    refine ⟨P *ᵥ Pi.single i 1, fun h => ?_, ?_⟩
    · have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hP h) i
      simp at this
    · rw [key]
      simp [Matrix.mulVec_diagonal, dotProduct, Pi.single_apply, hi]
  push_neg at hz
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsg : ∀ τ : E →+* ℂ, (∀ x, τ (σe x) = conj (τ x)) →
      ∃ i : Fin m, (0 < (τ (g i.succ)).re ↔ 0 < (τ (-g 0)).re) := by
    intro τ _
    have hre : ComplexEmbedding.IsReal (τ.comp (algebraMap F E)) :=
      ComplexEmbedding.isReal_iff.2 (RingHom.ext fun c => by
        rw [ComplexEmbedding.conjugate_coe_eq]
        have := hconj τ (algebraMap F E c)
        rw [AlgHom.commutes] at this
        exact this.symm)
    have hw : (InfinitePlace.mk (τ.comp (algebraMap F E))).embedding = τ.comp (algebraMap F E) :=
      InfinitePlace.embedding_mk_eq_of_isReal hre
    set w := InfinitePlace.mk (τ.comp (algebraMap F E))
    set τ' := (B.emb w).1
    have hτ' : ∀ c : F, τ' (algebraMap F E c) = τ (algebraMap F E c) := fun c => by
      have := congrArg (fun f => f c) ((B.emb w).2.trans hw)
      simpa using this
    have hgτ : ∀ k, τ' (g k) = τ (g k) := fun k => by
      obtain ⟨c, hc'⟩ := (hF (g k)).1 (hgf' k)
      rw [← hc', hτ']
    have hcong : (Matrix.diagonal g).map τ' =
        (P.map τ')ᵀ * Y.J.map τ' * (P.map τ').map (starRingEnd ℂ) := by
      rw [← hPg, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
      congr 1
      ext a b
      simp [hconj]
    have hPd : (P.map τ').det ≠ 0 := by
      rw [show (P.map τ').det = τ' P.det from (RingHom.map_det τ' P).symm]
      exact (map_ne_zero τ').2 hP
    have hcount : (Finset.univ.filter fun k => 0 < (τ (g k)).re).card = r := by
      have := GlobalTheory.Inertia.posIndex_congr (Y.J.map τ') hPd
      rw [← hcong, posIndex_of_hasSig (hY.sig w), Matrix.diagonal_map (map_zero _),
        GlobalTheory.Inertia.posIndex_diagonal] at this
      simpa [hgτ] using this
    have hrn : r < m + 1 := by have := (hY.sig w).1; omega
    have him : (τ (g 0)).im = 0 := by
      have h := hconj τ (g 0)
      rw [hgf' 0] at h
      exact Complex.conj_eq_iff_im.1 h.symm
    have hne0 : τ (g 0) ≠ 0 := (map_ne_zero τ).2 (hz 0)
    by_cases hp : 0 < (τ (g 0)).re
    · obtain ⟨k, hk⟩ : ∃ k, ¬ 0 < (τ (g k)).re := by
        by_contra hall
        push_neg at hall
        have h' : (Finset.univ.filter fun k => 0 < (τ (g k)).re) = Finset.univ :=
          Finset.filter_true_of_mem fun k _ => hall k
        rw [h', Finset.card_univ, Fintype.card_fin] at hcount
        omega
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 (show k ≠ 0 by rintro rfl; exact hk hp)
      refine ⟨i, iff_of_false hk ?_⟩
      simp only [map_neg, Complex.neg_re]
      linarith
    · have hneg : (τ (g 0)).re < 0 := by
        rcases lt_or_eq_of_le (not_lt.1 hp) with h | h
        · exact h
        · exact absurd (Complex.ext (by simpa using h) (by simpa using him)) hne0
      obtain ⟨k, hk⟩ : ∃ k, 0 < (τ (g k)).re := by
        by_contra hall
        push_neg at hall
        have h' : (Finset.univ.filter fun k => 0 < (τ (g k)).re) = ∅ :=
          Finset.filter_false_of_mem fun k _ => not_lt.2 (hall k)
        rw [h', Finset.card_empty] at hcount
        omega
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 (show k ≠ 0 by rintro rfl; exact hp hk)
      refine ⟨i, iff_of_true hk ?_⟩
      simp only [map_neg, Complex.neg_re]
      linarith
  obtain ⟨z, hz'⟩ := GlobalTheory.HermGlobal.exists_represent hc hF hθ0 hθ (r := m) (by omega)
    (g := fun i => g i.succ) (fun i => hgf' _) (fun i => hz _) (b := -g 0)
    (by simp [σe, hgf']) (neg_ne_zero.2 (hz 0)) hsg
  refine ⟨P *ᵥ Fin.cons 1 z, fun h => ?_, ?_⟩
  · have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hP h) 0
    simp at this
  · rw [key]
    simp only [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      map_one, one_mul, mul_one] at hz' ⊢
    simp only [σe, Function.comp_apply, RingHom.coe_coe, AlgEquiv.ofAlgHom_apply] at hz'
    linear_combination hz'

end GlobalTheory.HermIso
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_vector_hermitian_rank_ge_three_indefinite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n : ℕ) (Y : Spc F E n) (r s : ℕ), 3 ≤ n → 1 ≤ r → 1 ≤ s → Y.IsHerm σ B r s →
    ∃ x : Fin n → E, x ≠ 0 ∧ form σ Y.J x x = 0 := by
  first | exact @GlobalTheory.HermIso.exists_isotropic | exact GlobalTheory.HermIso.exists_isotropic | (intros; apply GlobalTheory.HermIso.exists_isotropic <;> assumption)
end

section
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

theorem GlobalTheory.adicEmbedding_integral_place (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (τ : E →ₐ[F] v.adicCompletion F) :
    (∀ a : 𝓞 E, Valued.v (τ a) ≤ 1) ∧ ∃ Q : Ideal (𝓞 E), Q.IsMaximal ∧ ∀ a : 𝓞 E, a ∈ Q ↔ Valued.v (τ a) < 1 := by
  set O := v.adicCompletionIntegers F
  have hv : (Valued.v : Valuation (v.adicCompletion F) _).Integers O := by
    have := Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _)
    exact this
  have ha : ∀ a : 𝓞 E, Valued.v (τ a) ≤ 1 := by
    intro a
    have h1 : IsIntegral ℤ (τ a) := IsIntegral.map τ (NumberField.RingOfIntegers.isIntegral_coe a)
    have h2 : IsIntegral O (τ a) := h1.tower_top
    exact hv.mem_of_integral h2
  refine ⟨ha, ?_⟩
  let φ : 𝓞 E →+* O :=
    ((τ : E →+* v.adicCompletion F).comp (algebraMap (𝓞 E) E)).codRestrict O.toSubring
      (fun a => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).2 (ha a))
  have hmem : ∀ a : 𝓞 E, a ∈ (IsLocalRing.maximalIdeal O).comap φ ↔ Valued.v (τ a) < 1 := by
    intro a
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one]
    change ¬ Valued.v (τ a) = 1 ↔ _
    exact ⟨fun h => lt_of_le_of_ne (ha a) h, fun h => ne_of_lt h⟩
  refine ⟨(IsLocalRing.maximalIdeal O).comap φ, ?_, hmem⟩
  apply Ideal.IsPrime.isMaximal inferInstance
  intro hbot
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hlt : Valued.v (algebraMap F (v.adicCompletion F) (π : F)) < 1 := by
    have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v π).2 hπ
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation] at this
    exact this
  have hne : (algebraMap (𝓞 F) (𝓞 E) π) ≠ 0 := by
    intro h
    apply hπ0
    apply FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)
    simpa using h
  apply hne
  have : algebraMap (𝓞 F) (𝓞 E) π ∈ (IsLocalRing.maximalIdeal O).comap φ := by
    rw [hmem]
    have e : ((algebraMap (𝓞 F) (𝓞 E) π : 𝓞 E) : E) = algebraMap F E (π : F) := by
      exact (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E π).symm.trans (IsScalarTower.algebraMap_apply (𝓞 F) F E π)
    rw [e, AlgHom.commutes]
    exact hlt
  rw [hbot] at this
  simpa using this
end

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitEmbedding_integral_and_maximalIdeal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (τ : E →ₐ[F] v.adicCompletion F),
    (∀ a : 𝓞 E, Valued.v (τ a) ≤ 1) ∧ ∃ Q : Ideal (𝓞 E), Q.IsMaximal ∧ ∀ a : 𝓞 E, a ∈ Q ↔ Valued.v (τ a) < 1 := by
  atlas_forward_decl GlobalTheory.adicEmbedding_integral_place
end

section
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory

theorem exists_scale_integral_not_le_maximal :
  ∀ (E : Type) [Field E] [NumberField E] (I : Submodule (𝓞 E) E), I.FG → I ≠ ⊥ →
    ∀ (ι : Type) [Fintype ι] (Q : ι → Ideal (𝓞 E)), (∀ i, (Q i).IsMaximal) →
    ∃ s : E, s ≠ 0 ∧ (∀ a ∈ I, IsIntegral ℤ (s * a)) ∧ ∀ i, ∃ a ∈ I, ∃ o : 𝓞 E, (o : E) = s * a ∧ o ∉ Q i := by
  intro E _ _ I hfg hne ι _ Q hQ
  classical
  let F : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨I, FractionalIdeal.isFractional_of_fg hfg⟩
  have hFcoe : (F : Submodule (𝓞 E) E) = I := rfl
  have hF0 : F ≠ 0 := by
    intro h
    apply hne
    rw [← hFcoe, h, FractionalIdeal.coe_zero]
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := FaithfulSMul.algebraMap_injective _ _
  have hint : ∀ s ∈ F⁻¹, ∀ a ∈ I, ∃ o : 𝓞 E, (o : E) = s * a := by
    intro s hs a ha
    have h1 := (FractionalIdeal.mem_inv_iff hF0).1 hs a ha
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_one] at h1
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 h1
    exact ⟨o, ho⟩
  have key : ∀ P : Ideal (𝓞 E), P ≠ ⊤ →
      ∃ s ∈ F⁻¹, ∃ a ∈ I, ∃ o : 𝓞 E, (o : E) = s * a ∧ o ∉ P := by
    intro P hP
    by_contra h
    push_neg at h
    apply hP
    have hle : ((F * F⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) ≤
        Submodule.map (Algebra.linearMap (𝓞 E) E) P := by
      rw [FractionalIdeal.coe_mul, Submodule.mul_le]
      intro m hm n hn
      obtain ⟨o, ho⟩ := hint n hn m hm
      refine Submodule.mem_map.2 ⟨o, h n hn m hm o ho, ?_⟩
      rw [mul_comm, ← ho]; rfl
    rw [mul_inv_cancel₀ hF0, FractionalIdeal.coe_one] at hle
    have h1 : (1 : E) ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_one.2 ⟨1, map_one _⟩
    obtain ⟨p, hp, hp1⟩ := Submodule.mem_map.1 (hle h1)
    have : p = 1 := hinj (by rw [map_one]; exact hp1)
    exact (Ideal.eq_top_iff_one P).2 (this ▸ hp)
  choose! sf hsf af haf of hof hof' using key
  have hc : ∀ P' P : Ideal (𝓞 E), P'.IsMaximal → P.IsMaximal → P' ≠ P → ∃ c ∈ P', c ∉ P := by
    intro P' P hP' hP hne'
    by_contra h
    push_neg at h
    exact hne' (hP'.eq_of_le hP.ne_top h)
  choose! c hc1 hc2 using hc
  obtain ⟨M0, hM0⟩ := Ideal.exists_maximal (𝓞 E)
  let T : Finset (Ideal (𝓞 E)) := insert M0 (Finset.univ.image Q)
  have hT : ∀ P ∈ T, P.IsMaximal := by
    intro P hP
    rcases Finset.mem_insert.1 hP with h | h
    · exact h ▸ hM0
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      exact hQ i
  let u : Ideal (𝓞 E) → 𝓞 E := fun P => ∏ P' ∈ T.erase P, c P' P
  have hu1 : ∀ P ∈ T, u P ∉ P := by
    intro P hP hmem
    haveI := (hT P hP).isPrime
    obtain ⟨P', hP', hcP⟩ := Ideal.IsPrime.prod_mem_iff.1 hmem
    exact hc2 P' P (hT P' (Finset.mem_of_mem_erase hP')) (hT P hP) (Finset.ne_of_mem_erase hP') hcP
  have hu2 : ∀ P ∈ T, ∀ P' ∈ T, P' ≠ P → u P ∈ P' := by
    intro P hP P' hP' hne'
    have hm : P' ∈ T.erase P := Finset.mem_erase.2 ⟨hne', hP'⟩
    show ∏ P'' ∈ T.erase P, c P'' P ∈ P'
    rw [← Finset.mul_prod_erase _ _ hm]
    exact Ideal.mul_mem_right _ _ (hc1 P' P (hT P' hP') (hT P hP) hne')
  let s : E := ∑ P ∈ T, (u P : E) * sf P
  have hs : s ∈ F⁻¹ := by
    refine Submodule.sum_mem _ (fun P hP => ?_)
    have := Submodule.smul_mem ((F⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) (u P) (hsf P (hT P hP).ne_top)
    rwa [Algebra.smul_def] at this

  have main : ∀ P0 ∈ T, ∃ o : 𝓞 E, (o : E) = s * af P0 ∧ o ∉ P0 := by
    intro P0 hP0
    have hP0t := (hT P0 hP0).ne_top
    have hterm : ∀ P ∈ T, ∃ o : 𝓞 E, (o : E) = sf P * af P0 :=
      fun P hP => hint _ (hsf P (hT P hP).ne_top) _ (haf P0 hP0t)
    choose! w hw using hterm
    refine ⟨∑ P ∈ T, u P * w P, ?_, ?_⟩
    · push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun P hP => ?_)
      rw [mul_assoc, ← hw P hP]
    · intro hmem
      haveI := (hT P0 hP0).isPrime
      rw [← Finset.add_sum_erase _ _ hP0] at hmem
      have hrest : ∑ P ∈ T.erase P0, u P * w P ∈ P0 :=
        Ideal.sum_mem _ (fun P hP => Ideal.mul_mem_right _ _
          (hu2 P (Finset.mem_of_mem_erase hP) P0 hP0 (Finset.ne_of_mem_erase hP).symm))
      have h2 : u P0 * w P0 ∈ P0 := by
        have := P0.sub_mem hmem hrest
        simpa using this
      have hwo : w P0 = of P0 := hinj (by
        show (w P0 : E) = (of P0 : E)
        rw [hw P0 hP0, hof P0 hP0t])
      rcases Ideal.IsPrime.mem_or_mem ‹_› h2 with h3 | h3
      · exact hu1 P0 hP0 h3
      · exact hof' P0 hP0t (hwo ▸ h3)
  refine ⟨s, ?_, ?_, ?_⟩
  · intro hs0
    obtain ⟨o, ho, hno⟩ := main M0 (Finset.mem_insert_self _ _)
    rw [hs0, zero_mul] at ho
    have : o = 0 := hinj (by rw [map_zero]; exact ho)
    exact hno (this ▸ M0.zero_mem)
  · intro a ha
    obtain ⟨o, ho⟩ := hint s hs a ha
    rw [← ho]
    exact o.isIntegral_coe
  · intro i
    have hi : Q i ∈ T := Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    obtain ⟨o, ho, hno⟩ := main (Q i) hi
    exact ⟨af (Q i), haf _ (hQ i).ne_top, o, ho, hno⟩

end GlobalTheory
end

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scale_fractionalIdeal_integral_avoid_maximals : ∀ (E : Type) [Field E] [NumberField E] (I : Submodule (𝓞 E) E), I.FG → I ≠ ⊥ →
    ∀ (ι : Type) [Fintype ι] (Q : ι → Ideal (𝓞 E)), (∀ i, (Q i).IsMaximal) →
    ∃ s : E, s ≠ 0 ∧ (∀ a ∈ I, IsIntegral ℤ (s * a)) ∧ ∀ i, ∃ a ∈ I, ∃ o : 𝓞 E, (o : E) = s * a ∧ o ∉ Q i := by
  atlas_forward_decl GlobalTheory.exists_scale_integral_not_le_maximal
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.HypPairLat

theorem form_smul_left {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (c : E) (z w : Fin n → E) : form σ J (c • z) w = c * form σ J z w := by
  simp [form, smul_dotProduct]

theorem form_smul_right {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (c : E) (z w : Fin n → E) : form σ J z (c • w) = σ c * form σ J z w := by
  have : (fun i => σ ((c • w) i)) = σ c • fun i => σ (w i) := by ext i; simp
  simp only [form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_conj {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j) (z w : Fin n → E) :
    σ (form σ J z w) = form σ J w z := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

theorem isIntegral_sigma {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {e : E}
    (h : IsIntegral ℤ e) : IsIntegral ℤ (σ e) :=
  h.map (σ.toRingHom.toIntAlgHom)

theorem exists_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n : ℕ) (Y : Spc F E n) (r s : ℕ), Y.IsHerm σ B r s →
    ∀ x : Fin n → E, x ≠ 0 → form σ Y.J x x = 0 →
    ∃ x' y : Fin n → E, form σ Y.J x' x' = 0 ∧ form σ Y.J y y = 0 ∧ form σ Y.J x' y = 1 ∧
      (∀ z ∈ Y.L, form σ Y.J z y • x' ∈ Y.L ∧ form σ Y.J z x' • y ∈ Y.L) ∧
      ∀ v : B.P, ((∀ c : E, c • x' ∈ Y.L → Valued.v (B.τ v c) ≤ 1) ∧ ∃ c : E, c • x' ∈ Y.L ∧ Valued.v (B.τ v c) = 1) ∧
        ((∀ c : E, c • y ∈ Y.L → Valued.v (B.τ v c) ≤ 1) ∧ ∃ c : E, c • y ∈ Y.L ∧ Valued.v (B.τ v c) = 1) := by
  intro F E _ _ _ _ _ σ B hB n Y r s hY x hx0 hxx
  have hσ : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hfu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E) := by haveI := hB.unram; infer_instance
  obtain ⟨θ, hθ⟩ := GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hB.cm hfu
  have hfg : Y.L.FG := hY.lat.fg
  obtain ⟨z0, hz0L, hz0⟩ := GlobalTheory.T.selfDual_hermitianLattice_exists_nonzero_pairing F E σ hσ n Y.J Y.L hfg hY.herm hY.dual x hx0
  let f : (Fin n → E) →ₗ[𝓞 E] E :=
    { toFun := fun z => form σ Y.J z x
      map_add' := fun a b => by simp [form, add_dotProduct]
      map_smul' := fun c a => by
        show form σ Y.J ((c : E) • a) x = (c : E) * form σ Y.J a x
        exact form_smul_left σ Y.J (c : E) a x }
  have hf : ∀ z, f z = form σ Y.J z x := fun z => rfl
  let I₀ : Submodule (𝓞 E) E := Y.L.map f
  have hI₀fg : I₀.FG := hfg.map f
  have hI₀ne : I₀ ≠ ⊥ := by
    intro h
    have : f z0 ∈ I₀ := Submodule.mem_map_of_mem hz0L
    rw [h, Submodule.mem_bot] at this
    exact hz0 this
  have hT4 := fun (v : B.P) (b : Bool) => GlobalTheory.T.splitEmbedding_integral_and_maximalIdeal F E v.1 (if b then (B.τ v).comp σ else B.τ v)
  choose hle Q hQmax hQ using hT4
  obtain ⟨s, hs0, hsI, hsQ⟩ := GlobalTheory.T.exists_scale_fractionalIdeal_integral_avoid_maximals E I₀ hI₀fg hI₀ne (B.P × Bool) (fun p => Q p.1 p.2) (fun p => hQmax _ _)
  set x' : Fin n → E := σ s • x with hx'def
  have hfx' : ∀ z, form σ Y.J z x' = s * form σ Y.J z x := fun z => by
    rw [hx'def, form_smul_right, hσ]
  have hx'x' : form σ Y.J x' x' = 0 := by
    rw [hfx', hx'def, form_smul_left, hxx, mul_zero, mul_zero]
  obtain ⟨y₀, hy₀1, hy₀L⟩ := GlobalTheory.T.exists_section_hermitianLinearForm_fg_module F E σ n Y.J Y.L hfg x' ⟨z0, hz0L, by rw [hfx']; exact mul_ne_zero hs0 hz0⟩
  obtain ⟨y, hyy, hx'y, hL⟩ := GlobalTheory.T.exists_isotropic_dual_partner_selfDual_hermitianLattice F E σ hσ n Y.J Y.L hY.herm hY.dual θ hθ x' y₀ hx'x' hy₀1 hy₀L
  have hint : ∀ z ∈ Y.L, IsIntegral ℤ (form σ Y.J z x') := fun z hz => by
    rw [hfx']; exact hsI _ (Submodule.mem_map_of_mem hz)
  have hx'L : x' ∈ Y.L := (hY.dual x').2 fun w hw => by
    rw [← form_conj σ hσ Y.J hY.herm]; exact isIntegral_sigma σ (hint w hw)
  have hyx' : form σ Y.J y x' = 1 := by
    rw [← form_conj σ hσ Y.J hY.herm, hx'y, map_one]

  have hval : ∀ (v : B.P) (b : Bool) (e : E), IsIntegral ℤ e →
      Valued.v ((if b then (B.τ v).comp σ else B.τ v) e) ≤ 1 := fun v b e he =>
    hle v b ⟨e, he⟩
  have hwit : ∀ (v : B.P) (b : Bool), ∃ z ∈ Y.L, IsIntegral ℤ (form σ Y.J z x') ∧
      Valued.v ((if b then (B.τ v).comp σ else B.τ v) (form σ Y.J z x')) = 1 := by
    intro v b
    obtain ⟨a, ha, o, ho, hoQ⟩ := hsQ (v, b)
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 ha
    refine ⟨z, hz, hint z hz, ?_⟩
    have h1 := hle v b o
    have h2 : ¬ Valued.v ((if b then (B.τ v).comp σ else B.τ v) (o : E)) < 1 := fun h => hoQ ((hQ v b o).2 h)
    rw [ho, hf, ← hfx'] at h1 h2
    exact le_antisymm h1 (not_lt.1 h2)
  refine ⟨x', y, hx'x', hyy, hx'y, hL, fun v => ⟨⟨fun c hc => ?_, 1, by rw [one_smul]; exact hx'L, by simp⟩,
    ⟨fun c hc => ?_, ?_⟩⟩⟩
  · obtain ⟨z, hz, -, hz1⟩ := hwit v true
    have hi : IsIntegral ℤ (form σ Y.J (c • x') z) := (hY.dual _).1 hc z hz
    rw [form_smul_left, ← form_conj σ hσ Y.J hY.herm z x'] at hi
    have := hval v false _ hi
    simp only [Bool.false_eq_true, ↓reduceIte, map_mul] at this
    simp only [↓reduceIte, AlgHom.comp_apply] at hz1
    rw [hz1, mul_one] at this
    exact this
  · have hi := hint _ hc
    rw [form_smul_left, hyx', mul_one] at hi
    simpa using hval v false c hi
  · obtain ⟨z, hz, -, hz1⟩ := hwit v false
    exact ⟨form σ Y.J z x', (hL z hz).2, by simpa using hz1⟩

end GlobalTheory.HypPairLat
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hyperbolicPair_selfDualLattice_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n : ℕ) (Y : Spc F E n) (r s : ℕ), Y.IsHerm σ B r s →
    ∀ x : Fin n → E, x ≠ 0 → form σ Y.J x x = 0 →
    ∃ x' y : Fin n → E, form σ Y.J x' x' = 0 ∧ form σ Y.J y y = 0 ∧ form σ Y.J x' y = 1 ∧
      (∀ z ∈ Y.L, form σ Y.J z y • x' ∈ Y.L ∧ form σ Y.J z x' • y ∈ Y.L) ∧
      ∀ v : B.P, ((∀ c : E, c • x' ∈ Y.L → Valued.v (B.τ v c) ≤ 1) ∧ ∃ c : E, c • x' ∈ Y.L ∧ Valued.v (B.τ v c) = 1) ∧
        ((∀ c : E, c • y ∈ Y.L → Valued.v (B.τ v c) ≤ 1) ∧ ∃ c : E, c • y ∈ Y.L ∧ Valued.v (B.τ v c) = 1) := by
  first | exact @GlobalTheory.HypPairLat.exists_pair | exact GlobalTheory.HypPairLat.exists_pair | (intros; apply GlobalTheory.HypPairLat.exists_pair <;> assumption)
end

section
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory

theorem exists_orthCompl_hypPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n n₁ : ℕ) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E),
    n = n₁ + 2 → (∀ i j, σ (J j i) = J i j) → form σ J x x = 0 → form σ J y y = 0 → form σ J x y = 1 →
    ∃ (ι : Matrix (Fin n) (Fin n₁) E) (P : Matrix (Fin n₁) (Fin n) E), P * ι = 1 ∧
      (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) ∧
      ∀ z, form σ J z x = 0 → form σ J z y = 0 → ∃ u, z = ι *ᵥ u := by
  intro F E _ _ _ _ _ σ n n₁ J x y hn hJ hxx hyy hxy
  classical
  set a : Fin n → E := J *ᵥ fun i => σ (x i) with ha_def
  set b : Fin n → E := J *ᵥ fun i => σ (y i) with hb_def
  have hfa : ∀ z, form σ J z x = z ⬝ᵥ a := fun z => rfl
  have hfb : ∀ z, form σ J z y = z ⬝ᵥ b := fun z => rfl
  have hxa : x ⬝ᵥ a = 0 := hxx
  have hxb : x ⬝ᵥ b = 1 := hxy
  have ha : a ≠ 0 := by
    intro h0
    have hv : x ᵥ* J = 0 := by
      funext j
      apply σ.toRingHom.injective
      have h1 := congrFun h0 j
      simp only [ha_def, Matrix.mulVec, dotProduct, Pi.zero_apply] at h1
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, map_zero, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul]
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hJ j i, mul_comm]
    apply one_ne_zero (α := E)
    rw [← hxb, hb_def, Matrix.dotProduct_mulVec, hv, zero_dotProduct]
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h; push_neg at h; exact ha (funext h)
  set w : Fin n → E := (a i)⁻¹ • (Pi.single i 1 - (b i) • x) with hw
  have hwa : w ⬝ᵥ a = 1 := by
    rw [hw, smul_dotProduct, sub_dotProduct, smul_dotProduct, hxa, single_dotProduct]
    simp [hi]
  have hwb : w ⬝ᵥ b = 0 := by
    rw [hw, smul_dotProduct, sub_dotProduct, smul_dotProduct, hxb, single_dotProduct]
    simp
  let M : Matrix (Fin 2) (Fin n) E := Matrix.of ![a, b]
  have hM : ∀ z, M *ᵥ z = ![z ⬝ᵥ a, z ⬝ᵥ b] := by
    intro z; funext k; fin_cases k <;> simp [M, Matrix.mulVec, dotProduct_comm]
  have hsurj : LinearMap.range (Matrix.mulVecLin M) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro v
    refine ⟨v 0 • w + v 1 • x, ?_⟩
    rw [Matrix.mulVecLin_apply, hM]
    funext k; fin_cases k <;> simp [add_dotProduct, smul_dotProduct, hwa, hwb, hxa, hxb]
  have hrank : Module.finrank E (LinearMap.ker (Matrix.mulVecLin M)) = n₁ := by
    have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin M)
    rw [hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
    omega
  set K := LinearMap.ker (Matrix.mulVecLin M) with hK
  have hmemK : ∀ z, z ∈ K ↔ z ⬝ᵥ a = 0 ∧ z ⬝ᵥ b = 0 := by
    intro z
    rw [hK, LinearMap.mem_ker, Matrix.mulVecLin_apply, hM]
    constructor
    · intro h; exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
    · rintro ⟨h1, h2⟩; funext k; fin_cases k <;> simp [h1, h2]
  let bK : Module.Basis (Fin n₁) E K := Module.finBasisOfFinrankEq E K hrank
  let f : (Fin n₁ → E) →ₗ[E] (Fin n → E) := K.subtype ∘ₗ bK.equivFun.symm.toLinearMap
  have hfinj : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.val_injective.comp bK.equivFun.symm.injective
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hfinj
  refine ⟨LinearMap.toMatrix' f, LinearMap.toMatrix' g, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  · intro u
    rw [LinearMap.toMatrix'_mulVec, hfa, hfb]
    exact (hmemK _).1 (bK.equivFun.symm u).2
  · intro z h1 h2
    have hz : z ∈ K := (hmemK z).2 ⟨h1, h2⟩
    refine ⟨bK.equivFun ⟨z, hz⟩, ?_⟩
    rw [LinearMap.toMatrix'_mulVec]
    simp [f]

end GlobalTheory
end

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonalComplement_embedding_hyperbolicPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n n₁ : ℕ) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E),
    n = n₁ + 2 → (∀ i j, σ (J j i) = J i j) → form σ J x x = 0 → form σ J y y = 0 → form σ J x y = 1 →
    ∃ (ι : Matrix (Fin n) (Fin n₁) E) (P : Matrix (Fin n₁) (Fin n) E), P * ι = 1 ∧
      (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) ∧
      ∀ z, form σ J z x = 0 → form σ J z y = 0 → ∃ u, z = ι *ᵥ u := by
  atlas_forward_decl GlobalTheory.exists_orthCompl_hypPair
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory

theorem isLattice_comap_mulVecLin_of_leftInverse (E : Type) [Field E] [NumberField E] (n n₁ : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (ι : Matrix (Fin n) (Fin n₁) E)
    (P : Matrix (Fin n₁) (Fin n) E) (hPι : P * ι = 1) (hL : L.IsLattice E) :
    (L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))).IsLattice E := by
  set f : (Fin n₁ → E) →ₗ[𝓞 E] (Fin n → E) := (Matrix.mulVecLin ι).restrictScalars (𝓞 E) with hf
  set g : (Fin n → E) →ₗ[𝓞 E] (Fin n₁ → E) := (Matrix.mulVecLin P).restrictScalars (𝓞 E) with hg
  have hgf : ∀ u, g (f u) = u := by
    intro u
    simp [hf, hg, Matrix.mulVec_mulVec, hPι]
  constructor
  · have hN : IsNoetherian (𝓞 E) L := isNoetherian_of_fg_of_noetherian L hL.fg
    have h1 : ((L.comap f).map f).FG :=
      isNoetherian_submodule.1 hN _ (Submodule.map_comap_le f L)
    have h2 : ((L.comap f).map f).map g = L.comap f := by
      rw [← Submodule.map_comp]
      ext u
      simp only [Submodule.mem_map, LinearMap.coe_comp, Function.comp_apply, hgf]
      exact ⟨fun ⟨v, hv, he⟩ => he ▸ hv, fun hu => ⟨u, hu, rfl⟩⟩
    rw [← h2]
    exact h1.map g
  · rw [eq_top_iff]
    intro u _
    have hu : f u ∈ Submodule.span E (L : Set (Fin n → E)) := by
      rw [hL.span_eq_top]; trivial
    obtain ⟨y, hy, z, hz⟩ := (IsLocalization.mem_span_iff (nonZeroDivisors (𝓞 E))).1 hu
    rw [Submodule.span_eq] at hy
    have hz0 : (algebraMap (𝓞 E) E (z : 𝓞 E)) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors z.2
    have hmem : (z : 𝓞 E) • u ∈ L.comap f := by
      have hc : (z : 𝓞 E) • IsLocalization.mk' E (1 : 𝓞 E) z = 1 := by
        rw [Algebra.smul_def, mul_comm, IsLocalization.mk'_spec, map_one]
      rw [Submodule.mem_comap, LinearMap.map_smul, hz, ← smul_assoc, hc, one_smul]
      exact hy
    have hsp : (z : 𝓞 E) • u ∈ Submodule.span E ((L.comap f : Submodule (𝓞 E) (Fin n₁ → E)) : Set (Fin n₁ → E)) :=
      Submodule.subset_span hmem
    have hu' : u = (algebraMap (𝓞 E) E (z : 𝓞 E))⁻¹ • ((z : 𝓞 E) • u) := by
      rw [← algebraMap_smul E (z : 𝓞 E) u, smul_smul, inv_mul_cancel₀ hz0, one_smul]
    rw [hu']
    exact Submodule.smul_mem _ _ hsp

end GlobalTheory
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLattice_comap_mulVecLin_of_leftInverse_matrix : ∀ (E : Type) [Field E] [NumberField E] (n n₁ : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (ι : Matrix (Fin n) (Fin n₁) E)
    (P : Matrix (Fin n₁) (Fin n) E), P * ι = 1 → L.IsLattice E →
    (L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))).IsLattice E := by
  first | exact @GlobalTheory.isLattice_comap_mulVecLin_of_leftInverse | exact GlobalTheory.isLattice_comap_mulVecLin_of_leftInverse | (intros; apply GlobalTheory.isLattice_comap_mulVecLin_of_leftInverse <;> assumption)
end

section
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory

theorem latticeLine_fractionalIdeal : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.IsLattice E →
    ∀ x : Fin n → E, x ≠ 0 → ∃ 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E, ∀ s : E, s ∈ 𝔟 ↔ s • x ∈ L := by
  intro E _ _ n L hL x hx
  let f : E →ₗ[𝓞 E] (Fin n → E) :=
    (LinearMap.toSpanSingleton E (Fin n → E) x).restrictScalars (𝓞 E)
  have hf : Function.Injective f := by
    intro a b h
    have h' : a • x = b • x := h
    exact smul_left_injective E hx h'
  have hLfg : L.FG := hL.fg
  have hmapfg : ((L.comap f).map f).FG :=
    Submodule.FG.of_le hLfg (Submodule.map_comap_le f L)
  have hS : (L.comap f).FG := Submodule.fg_of_fg_map_injective f hf hmapfg
  exact ⟨⟨L.comap f, FractionalIdeal.isFractional_of_fg hS⟩, fun s => Iff.rfl⟩

end GlobalTheory
end

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fractionalIdeal_lattice_line_coefficients : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.IsLattice E →
    ∀ x : Fin n → E, x ≠ 0 → ∃ 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E, ∀ s : E, s ∈ 𝔟 ↔ s • x ∈ L := by
  atlas_forward_decl GlobalTheory.latticeLine_fractionalIdeal
end

section
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.CartanPlane

open Matrix

theorem star_mulVec_map {m k : Type} [Fintype k] (B : Matrix m k ℂ) (v : k → ℂ) :
    star (B *ᵥ v) = B.map star *ᵥ star v := by
  ext i
  simp [mulVec, dotProduct, star_sum]

theorem form_mulVec {m k l : Type} [Fintype m] [Fintype k] [Fintype l] (A : Matrix m k ℂ) (B : Matrix m l ℂ)
    (M : Matrix m m ℂ) (u : k → ℂ) (v : l → ℂ) :
    (A *ᵥ u) ⬝ᵥ M *ᵥ star (B *ᵥ v) = u ⬝ᵥ (Aᵀ * M * B.map star) *ᵥ star v := by
  rw [star_mulVec_map, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose, dotProduct_comm (A *ᵥ u),
    dotProduct_mulVec, dotProduct_comm]

theorem herm_swap {m : Type} [Fintype m] (M : Matrix m m ℂ) (hM : Mᴴ = M) (x y : m → ℂ) :
    y ⬝ᵥ M *ᵥ star x = star (x ⬝ᵥ M *ᵥ star y) := by
  have h : ∀ i j, star (M i j) = M j i := fun i j => by rw [← conjTranspose_apply, hM]
  simp only [dotProduct, mulVec, star_sum, star_mul', star_star, Pi.star_apply, Finset.mul_sum, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem ext_form {m : Type} [Fintype m] [DecidableEq m] (A B : Matrix m m ℂ)
    (h : ∀ x y : m → ℂ, x ⬝ᵥ A *ᵥ star y = x ⬝ᵥ B *ᵥ star y) : A = B := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simpa [single_dotProduct, mulVec_single] using this

end GlobalTheory.CartanPlane

namespace GlobalTheory.CartanPlane
open Matrix

theorem extend_swap : ∀ (n n₁ : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (X Yv : Fin n → ℂ) (ι : Matrix (Fin n) (Fin n₁) ℂ)
    (P : Matrix (Fin n₁) (Fin n) ℂ) (θ₁ : Matrix (Fin n₁) (Fin n₁) ℂ), n = n₁ + 2 → Mᴴ = M →
    X ⬝ᵥ M *ᵥ star X = 0 → Yv ⬝ᵥ M *ᵥ star Yv = 0 → X ⬝ᵥ M *ᵥ star Yv = 1 →
    ιᵀ *ᵥ (M *ᵥ star X) = 0 → ιᵀ *ᵥ (M *ᵥ star Yv) = 0 → P * ι = 1 →
    IsCartan (ιᵀ * M * ι.map star) θ₁ → ∃ θ, IsCartan M θ ∧ θ * ι = ι * θ₁ ∧ θ *ᵥ X = Yv := by
  intro n n₁ M X Yv ι P θ₁ hn hM hXX hYY hXY hιX hιY hPι hθ₁
  subst hn
  set M₁ := ιᵀ * M * ι.map star with hM₁
  have hYX : Yv ⬝ᵥ M *ᵥ star X = 1 := by rw [herm_swap M hM, hXY]; simp
  have hιuX : ∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0 := by
    intro u; rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hιX, zero_dotProduct]
  have hιuY : ∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star Yv = 0 := by
    intro u; rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hιY, zero_dotProduct]
  have hXιu : ∀ u, X ⬝ᵥ M *ᵥ star (ι *ᵥ u) = 0 := by intro u; rw [herm_swap M hM, hιuX, star_zero]
  have hYιu : ∀ u, Yv ⬝ᵥ M *ᵥ star (ι *ᵥ u) = 0 := by intro u; rw [herm_swap M hM, hιuY, star_zero]
  have hιι : ∀ u u', (ι *ᵥ u) ⬝ᵥ M *ᵥ star (ι *ᵥ u') = u ⬝ᵥ M₁ *ᵥ star u' := fun u u' => form_mulVec ι ι M u u'
  have hexp : ∀ u (a b : ℂ) u' (a' b' : ℂ), (ι *ᵥ u + a • X + b • Yv) ⬝ᵥ M *ᵥ star (ι *ᵥ u' + a' • X + b' • Yv) =
      u ⬝ᵥ M₁ *ᵥ star u' + a * star b' + b * star a' := by
    intro u a b u' a' b'
    simp only [add_dotProduct, star_add, mulVec_add, dotProduct_add, smul_dotProduct, star_smul, mulVec_smul,
      dotProduct_smul, hιι, hιuX, hιuY, hXιu, hYιu, hXX, hYY, hXY, hYX, smul_eq_mul]
    ring
  have hcY : ∀ u (a b : ℂ), (ι *ᵥ u + a • X + b • Yv) ⬝ᵥ M *ᵥ star Yv = a := by
    intro u a b; have := hexp u a b 0 0 1; simpa using this
  have hcX : ∀ u (a b : ℂ), (ι *ᵥ u + a • X + b • Yv) ⬝ᵥ M *ᵥ star X = b := by
    intro u a b; have := hexp u a b 0 1 0; simpa using this

  have hdec : ∀ z : Fin (n₁ + 2) → ℂ, ∃ (u : Fin n₁ → ℂ) (a b : ℂ), z = ι *ᵥ u + a • X + b • Yv := by
    let Φ : ((Fin n₁ → ℂ) × (Fin 2 → ℂ)) →ₗ[ℂ] (Fin (n₁ + 2) → ℂ) :=
      (Matrix.toLin' ι).comp (LinearMap.fst ℂ _ _) +
        ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).smulRight X).comp (LinearMap.snd ℂ _ _) +
        ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1).smulRight Yv).comp (LinearMap.snd ℂ _ _)
    have hΦ : ∀ p, Φ p = ι *ᵥ p.1 + p.2 0 • X + p.2 1 • Yv := fun p => by simp [Φ]
    have hinj : Function.Injective Φ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨u, w⟩ h0
      rw [hΦ] at h0
      have ha := hcY u (w 0) (w 1)
      have hb := hcX u (w 0) (w 1)
      simp only at h0 ha hb
      rw [h0, zero_dotProduct] at ha hb
      have hu : ι *ᵥ u = 0 := by rw [← ha, ← hb] at h0; simpa using h0
      have : u = 0 := by rw [← one_mulVec u, ← hPι, ← mulVec_mulVec, hu, mulVec_zero]
      refine Prod.ext this ?_
      ext i; fin_cases i <;> simp [← ha, ← hb]
    have hsurj : Function.Surjective Φ :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [Module.finrank_prod])).mp hinj
    intro z
    obtain ⟨p, hp⟩ := hsurj z
    exact ⟨p.1, p.2 0, p.2 1, by rw [← hp, hΦ]⟩

  set vX := M *ᵥ star X with hvX
  set vY := M *ᵥ star Yv with hvY
  set C₁ : Matrix (Fin n₁) (Fin (n₁ + 2)) ℂ := P - vecMulVec (P *ᵥ X) vY - vecMulVec (P *ᵥ Yv) vX with hC₁
  set θ : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ := ι * θ₁ * C₁ + vecMulVec Yv vY + vecMulVec X vX with hθdef
  have hθ : ∀ u (a b : ℂ), θ *ᵥ (ι *ᵥ u + a • X + b • Yv) = ι *ᵥ (θ₁ *ᵥ u) + b • X + a • Yv := by
    intro u a b
    have ha : vY ⬝ᵥ (ι *ᵥ u + a • X + b • Yv) = a := by rw [dotProduct_comm]; exact hcY u a b
    have hb : vX ⬝ᵥ (ι *ᵥ u + a • X + b • Yv) = b := by rw [dotProduct_comm]; exact hcX u a b
    have hC : C₁ *ᵥ (ι *ᵥ u + a • X + b • Yv) = u := by
      rw [hC₁, sub_mulVec, sub_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, ha, hb, mulVec_add, mulVec_add,
        mulVec_smul, mulVec_smul, mulVec_mulVec, hPι, one_mulVec]
      simp only [op_smul_eq_smul]
      abel
    rw [hθdef, add_mulVec, add_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, ha, hb, ← mulVec_mulVec, ← mulVec_mulVec, hC]
    simp only [op_smul_eq_smul]
    abel
  have hext : ∀ A B : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ,
      (∀ u (a b : ℂ), A *ᵥ (ι *ᵥ u + a • X + b • Yv) = B *ᵥ (ι *ᵥ u + a • X + b • Yv)) → A = B := by
    intro A B h
    apply ext_of_mulVec_single
    intro i
    obtain ⟨u, a, b, hz⟩ := hdec (Pi.single i 1)
    rw [hz, h]
  have hθ₁θ₁ : ∀ u, θ₁ *ᵥ (θ₁ *ᵥ u) = u := fun u => by rw [mulVec_mulVec, hθ₁.1, one_mulVec]
  have hiso₁ : ∀ u u', (θ₁ *ᵥ u) ⬝ᵥ M₁ *ᵥ star (θ₁ *ᵥ u') = u ⬝ᵥ M₁ *ᵥ star u' := fun u u' => by
    rw [form_mulVec, hθ₁.2.1]
  have hre : ∀ c : ℂ, (c * star c).re = Complex.normSq c := fun c => by
    simp [Complex.mul_re, Complex.normSq_apply]
  refine ⟨θ, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · apply hext
    intro u a b
    rw [← mulVec_mulVec, hθ, hθ, hθ₁θ₁, one_mulVec]
  · apply ext_form
    intro x y
    rw [← form_mulVec]
    obtain ⟨u, a, b, rfl⟩ := hdec x
    obtain ⟨u', a', b', rfl⟩ := hdec y
    rw [hθ, hθ, hexp, hexp, hiso₁]
    ring
  · intro x hx
    obtain ⟨u, a, b, rfl⟩ := hdec x
    rw [hθ, hexp, Complex.add_re, Complex.add_re, hre, hre]
    by_cases hu : u = 0
    · subst hu
      have hab : a ≠ 0 ∨ b ≠ 0 := by
        by_contra h
        push_neg at h
        apply hx
        simp [h.1, h.2]
      simp only [mulVec_zero, zero_dotProduct, Complex.zero_re, zero_add]
      rcases hab with h | h
      · have := Complex.normSq_pos.mpr h; have := Complex.normSq_nonneg b; linarith
      · have := Complex.normSq_pos.mpr h; have := Complex.normSq_nonneg a; linarith
    · have := hθ₁.2.2 u hu
      have := Complex.normSq_nonneg b; have := Complex.normSq_nonneg a; linarith
  · apply ext_of_mulVec_single
    intro j
    have := hθ (Pi.single j 1) 0 0
    simp only [zero_smul, add_zero] at this
    rw [← mulVec_mulVec, ← mulVec_mulVec, this]
  · have := hθ 0 1 0
    simpa using this

end GlobalTheory.CartanPlane
end

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartanInvolution_extend_swapping_hyperbolicPair : ∀ (n n₁ : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (X Yv : Fin n → ℂ) (ι : Matrix (Fin n) (Fin n₁) ℂ)
    (P : Matrix (Fin n₁) (Fin n) ℂ) (θ₁ : Matrix (Fin n₁) (Fin n₁) ℂ), n = n₁ + 2 → Mᴴ = M →
    X ⬝ᵥ M *ᵥ star X = 0 → Yv ⬝ᵥ M *ᵥ star Yv = 0 → X ⬝ᵥ M *ᵥ star Yv = 1 →
    ιᵀ *ᵥ (M *ᵥ star X) = 0 → ιᵀ *ᵥ (M *ᵥ star Yv) = 0 → P * ι = 1 →
    IsCartan (ιᵀ * M * ι.map star) θ₁ → ∃ θ, IsCartan M θ ∧ θ * ι = ι * θ₁ ∧ θ *ᵥ X = Yv := by
  atlas_forward_decl GlobalTheory.CartanPlane.extend_swap
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartanInvolution_of_hasHermitianSignature : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (r s : ℕ), HasSig M r s → ∃ θ, IsCartan M θ := by
  first | exact @GlobalTheory.CartanEx.exists_isCartan | exact GlobalTheory.CartanEx.exists_isCartan | (intros; apply GlobalTheory.CartanEx.exists_isCartan <;> assumption)
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasHermitianSignature_complement_hyperbolicPlane : ∀ (n n₁ : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (X Yv : Fin n → ℂ) (ι : Matrix (Fin n) (Fin n₁) ℂ)
    (P : Matrix (Fin n₁) (Fin n) ℂ) (r s : ℕ), n = n₁ + 2 → Mᴴ = M →
    X ⬝ᵥ M *ᵥ star X = 0 → Yv ⬝ᵥ M *ᵥ star Yv = 0 → X ⬝ᵥ M *ᵥ star Yv = 1 →
    ιᵀ *ᵥ (M *ᵥ star X) = 0 → ιᵀ *ᵥ (M *ᵥ star Yv) = 0 → P * ι = 1 →
    HasSig M r s → HasSig (ιᵀ * M * ι.map star) (r - 1) (s - 1) := by
  first | exact @GlobalTheory.PlaneSig.hasSig_complement_plane | exact GlobalTheory.PlaneSig.hasSig_complement_plane | (intros; apply GlobalTheory.PlaneSig.hasSig_complement_plane <;> assumption)
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPlace_basis_hyperbolicPlane_complement : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (τ : E →ₐ[F] v.adicCompletion F) (n n₁ : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E)
    (β₁ : GL (Fin n₁) (v.adicCompletion F)) (i₀ i₁ : ℕ), n = n₁ + 2 → i₀ < i₁ → i₁ < n → L.IsLattice E →
    (∀ z ∈ L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ L ∧ t • y ∈ L ∧ ι *ᵥ u ∈ L ∧ z = s • x + ι *ᵥ u + t • y) →
    ((∀ c : E, c • x ∈ L → Valued.v (τ c) ≤ 1) ∧ ∃ c : E, c • x ∈ L ∧ Valued.v (τ c) = 1) →
    ((∀ c : E, c • y ∈ L → Valued.v (τ c) ≤ 1) ∧ ∃ c : E, c • y ∈ L ∧ Valued.v (τ c) = 1) →
    IsSplitBasis τ (L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))) β₁ →
    ∃ β : GL (Fin n) (v.adicCompletion F), (∀ i : Fin n, (i.1 = i₀ → ∀ r, β.1 r i = τ (x r)) ∧
      (i.1 = i₁ → ∀ r, β.1 r i = τ (y r)) ∧ ∀ j : Fin n₁, i.1 = skip i₀ i₁ j → ∀ r, β.1 r i = (ι.map τ * β₁.1) r j) ∧
      IsSplitBasis τ L β := by
  first | exact @GlobalTheory.PlaneBasis.exists_isSplitBasis_plane | exact GlobalTheory.PlaneBasis.exists_isSplitBasis_plane | (intros; apply GlobalTheory.PlaneBasis.exists_isSplitBasis_plane <;> assumption)
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.KTowerPlane

section Help
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sigma_sigma (h : IsCMExt F E σ) (a : E) : σ (σ a) = a := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem form_swap (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = J i j)
    (a b : Fin n → E) : form σ J b a = σ (form σ J a b) := by
  have hJ' : ∀ i j, σ (J i j) = J j i := fun i j => hJ j i
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, sigma_sigma h, hJ', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem form_add_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J (a + b) c = form σ J a c + form σ J b c := by simp [form, add_dotProduct]

theorem form_sub_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J (a - b) c = form σ J a c - form σ J b c := by simp [form, sub_dotProduct]

theorem form_smul_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (s : E) (a c : Fin n → E) :
    form σ J (s • a) c = s * form σ J a c := by simp [form, smul_dotProduct]

theorem form_add_right {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J c (a + b) = form σ J c a + form σ J c b := by
  have : (fun i => σ ((a + b) i)) = (fun i => σ (a i)) + fun i => σ (b i) := funext fun i => by simp
  simp only [form, this, Matrix.mulVec_add, dotProduct_add]

theorem form_smul_right {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (s : E) (a c : Fin n → E) :
    form σ J c (s • a) = σ s * form σ J c a := by
  have : (fun i => σ ((s • a) i)) = σ s • fun i => σ (a i) := funext fun i => by simp
  simp only [form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_gram {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin n₁) E) (u u' : Fin n₁ → E) :
    form σ (ιᵀ * J * ι.map σ) u u' = form σ J (ι *ᵥ u) (ι *ᵥ u') := by
  have e1 : (fun i => σ ((ι *ᵥ u') i)) = ι.map σ *ᵥ fun i => σ (u' i) :=
    funext fun i => RingHom.map_mulVec (σ : E →+* E) ι u' i
  simp only [form, e1, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem map_form (h : IsCMExt F E σ) (e : E →+* ℂ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b : Fin n → E) :
    e (form σ J a b) = (fun i => e (a i)) ⬝ᵥ J.map e *ᵥ star (fun i => e (b i)) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply, Pi.star_apply, h.2.2.2 e]

theorem transpose_mulVec_eq_zero {n n₁ : ℕ} {R : Type} [CommRing R] (ι : Matrix (Fin n) (Fin n₁) R) (w : Fin n → R)
    (hw : ∀ u, (ι *ᵥ u) ⬝ᵥ w = 0) : ιᵀ *ᵥ w = 0 := by
  funext k
  have := hw (Pi.single k 1)
  rwa [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_single, mul_one, ← Matrix.mulVec_transpose] at this

theorem map_herm (h : IsCMExt F E σ) (e : E →+* ℂ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) : (J.map e)ᴴ = J.map e := by
  ext i j
  simp [Matrix.conjTranspose_apply, ← h.2.2.2 e, hJ]

theorem map_orth (h : IsCMExt F E σ) (e : E →+* ℂ) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (ι : Matrix (Fin n) (Fin n₁) E) (x : Fin n → E) (hx : ∀ u, form σ J (ι *ᵥ u) x = 0) :
    (ι.map e)ᵀ *ᵥ (J.map e *ᵥ star (fun i => e (x i))) = 0 := by
  have h0 : ιᵀ *ᵥ (J *ᵥ fun i => σ (x i)) = 0 := transpose_mulVec_eq_zero ι _ hx
  have hs : star (fun i => e (x i)) = fun i => e (σ (x i)) := funext fun i => by simp [h.2.2.2 e]
  have e2 : (J.map e *ᵥ fun i => e (σ (x i))) = fun i => e ((J *ᵥ fun i => σ (x i)) i) :=
    funext fun i => (RingHom.map_mulVec e J _ i).symm
  have e3 : (ιᵀ.map e *ᵥ fun i => e ((J *ᵥ fun i => σ (x i)) i)) = fun k => e ((ιᵀ *ᵥ (J *ᵥ fun i => σ (x i))) k) :=
    funext fun k => (RingHom.map_mulVec e ιᵀ _ k).symm
  rw [hs, ← Matrix.transpose_map, e2, e3, h0]
  funext k
  simp

theorem map_gram (h : IsCMExt F E σ) (e : E →+* ℂ) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (ι : Matrix (Fin n) (Fin n₁) E) : (ι.map e)ᵀ * J.map e * (ι.map e).map star = (ιᵀ * J * ι.map σ).map e := by
  have : (ι.map e).map star = (ι.map σ).map e := by ext i j; simp [h.2.2.2 e]
  rw [this, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]

end Help

section Help2
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem form_single {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    form σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  have : (fun k => σ ((Pi.single j (1 : E) : Fin n → E) k)) = Pi.single j 1 := by
    funext k; by_cases h : k = j <;> simp [h]
  simp [form, this, Matrix.mulVec_single, single_dotProduct]
end Help2

theorem exists_hyperbolic_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ), n = n₁ + 2 → 1 ≤ n₁ → ∀ (Y : Spc F E n) (r s : ℕ), 1 ≤ r → 1 ≤ s →
    Y.IsHerm σ B r s → ∀ i₀ i₁ : ℕ, i₀ < i₁ → i₁ < n → ∃ (Y' : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
      (GlobalTheory.ThK.reS Y Y').IsHerm σ B r s ∧ Y₁.IsHerm σ B (r - 1) (s - 1) ∧ H.IsAdapted σ B (GlobalTheory.ThK.reS Y Y') Y₁ i₀ i₁ := by
  intro F E _ _ _ _ _ σ B hB n n₁ hn hn₁ Y r s hr hs hY i₀ i₁ h01 h1n
  classical
  have hcm : IsCMExt F E σ := hB.cm
  obtain ⟨x₀, hx₀, hx₀x₀⟩ := GlobalTheory.T.exists_isotropic_vector_hermitian_rank_ge_three_indefinite F E σ B hB n Y r s (by omega) hr hs hY
  obtain ⟨x, y, hxx, hyy, hxy, hL, hP⟩ := GlobalTheory.T.exists_hyperbolicPair_selfDualLattice_isotropic F E σ B hB n Y r s hY x₀ hx₀ hx₀x₀
  obtain ⟨ι, P, hPι, horth, hcomp⟩ := GlobalTheory.T.exists_orthogonalComplement_embedding_hyperbolicPair F E σ n n₁ Y.J x y hn hY.herm hxx hyy hxy
  have hyx : form σ Y.J y x = 1 := by rw [form_swap hcm hY.herm, hxy, map_one]
  have hsplit : ∀ z ∈ Y.L, ∃ u, ι *ᵥ u ∈ Y.L ∧ z = form σ Y.J z y • x + ι *ᵥ u + form σ Y.J z x • y := by
    intro z hz
    obtain ⟨u, hu⟩ := hcomp (z - form σ Y.J z y • x - form σ Y.J z x • y) (by
        rw [form_sub_left, form_sub_left, form_smul_left, form_smul_left, hxx, hyx]; ring) (by
        rw [form_sub_left, form_sub_left, form_smul_left, form_smul_left, hxy, hyy]; ring)
    refine ⟨u, ?_, ?_⟩
    · rw [← hu]; exact Y.L.sub_mem (Y.L.sub_mem hz (hL z hz).1) (hL z hz).2
    · rw [← hu]; abel
  set L₁ := Y.L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E)) with hL₁def
  have hlat₁ : L₁.IsLattice E := GlobalTheory.T.isLattice_comap_mulVecLin_of_leftInverse_matrix E n n₁ Y.L ι P hPι hY.lat
  have hx0 : x ≠ 0 := by rintro rfl; simp [form] at hxy
  obtain ⟨𝔟, h𝔟⟩ := GlobalTheory.T.exists_fractionalIdeal_lattice_line_coefficients E n Y.L hY.lat x hx0
  set J₁ := ιᵀ * Y.J * ι.map σ with hJ₁
  have hform₁ : ∀ u u', form σ J₁ u u' = form σ Y.J (ι *ᵥ u) (ι *ᵥ u') := form_gram Y.J ι
  let e : InfinitePlace F → E →+* ℂ := fun w => (B.emb w).1
  have hMh : ∀ w, (Y.J.map (e w))ᴴ = Y.J.map (e w) := fun w => map_herm hcm _ hY.herm
  have cxx : ∀ w, (fun i => e w (x i)) ⬝ᵥ Y.J.map (e w) *ᵥ star (fun i => e w (x i)) = 0 := fun w => by
    rw [← map_form hcm, hxx, map_zero]
  have cyy : ∀ w, (fun i => e w (y i)) ⬝ᵥ Y.J.map (e w) *ᵥ star (fun i => e w (y i)) = 0 := fun w => by
    rw [← map_form hcm, hyy, map_zero]
  have cxy : ∀ w, (fun i => e w (x i)) ⬝ᵥ Y.J.map (e w) *ᵥ star (fun i => e w (y i)) = 1 := fun w => by
    rw [← map_form hcm, hxy, map_one]
  have cox : ∀ w, (ι.map (e w))ᵀ *ᵥ (Y.J.map (e w) *ᵥ star (fun i => e w (x i))) = 0 := fun w =>
    map_orth hcm _ Y.J ι x (fun u => (horth u).1)
  have coy : ∀ w, (ι.map (e w))ᵀ *ᵥ (Y.J.map (e w) *ᵥ star (fun i => e w (y i))) = 0 := fun w =>
    map_orth hcm _ Y.J ι y (fun u => (horth u).2)
  have cP : ∀ w, P.map (e w) * ι.map (e w) = 1 := fun w => by
    rw [← Matrix.map_mul, hPι, Matrix.map_one _ (map_zero _) (map_one _)]
  have cg : ∀ w, (ι.map (e w))ᵀ * Y.J.map (e w) * (ι.map (e w)).map star = J₁.map (e w) := fun w =>
    map_gram hcm _ Y.J ι
  have hsig₁ : ∀ w, HasSig (J₁.map (e w)) (r - 1) (s - 1) := fun w => by
    rw [← cg w]
    exact GlobalTheory.T.hasHermitianSignature_complement_hyperbolicPlane n n₁ _ _ _ _ _ r s hn (hMh w) (cxx w) (cyy w) (cxy w) (cox w) (coy w) (cP w) (hY.sig w)
  have hθ₁ : ∀ w, ∃ θ, IsCartan (J₁.map (e w)) θ := fun w => GlobalTheory.T.exists_cartanInvolution_of_hasHermitianSignature n₁ _ _ _ (hsig₁ w)
  choose θ₁ hθ₁ using hθ₁
  have hθ : ∀ w, ∃ θ, IsCartan (Y.J.map (e w)) θ ∧ θ * ι.map (e w) = ι.map (e w) * θ₁ w ∧
      θ *ᵥ (fun i => e w (x i)) = fun i => e w (y i) := fun w =>
    GlobalTheory.T.exists_cartanInvolution_extend_swapping_hyperbolicPair n n₁ _ _ _ _ _ _ hn (hMh w) (cxx w) (cyy w) (cxy w) (cox w) (coy w) (cP w) (by rw [cg w]; exact hθ₁ w)
  choose θ hθ using hθ
  haveI := hlat₁
  have hb₁ : ∀ v : B.P, ∃ β, IsSplitBasis (B.τ v) L₁ β := fun v => exists_isSplitBasis (B.τ v) L₁ hcm
  choose β₁ hβ₁ using hb₁
  let bas₁ : ∀ v : Pl F, GL (Fin n₁) (Fv F v) := fun v => if h : v ∈ B.P then β₁ ⟨v, h⟩ else 1
  have hbas₁ : ∀ v : B.P, bas₁ v = β₁ v := fun v => by simp only [bas₁, dif_pos v.2]
  have hb : ∀ v : B.P, ∃ β : GL (Fin n) (Fv F v), (∀ i : Fin n, (i.1 = i₀ → ∀ r, β.1 r i = B.τ v (x r)) ∧
      (i.1 = i₁ → ∀ r, β.1 r i = B.τ v (y r)) ∧
      ∀ j : Fin n₁, i.1 = skip i₀ i₁ j → ∀ r, β.1 r i = (ι.map (B.τ v) * (β₁ v).1) r j) ∧
      IsSplitBasis (B.τ v) Y.L β := fun v =>
    GlobalTheory.T.exists_splitPlace_basis_hyperbolicPlane_complement F E σ hcm v (B.τ v) n n₁ Y.L x y ι (β₁ v) i₀ i₁ hn h01 h1n hY.lat
      (fun z hz => by
        obtain ⟨u, hu, hz'⟩ := hsplit z hz
        exact ⟨_, _, u, (hL z hz).1, (hL z hz).2, hu, hz'⟩) (hP v).1 (hP v).2 (hβ₁ v)
  choose β hβ using hb
  let bas : ∀ v : Pl F, GL (Fin n) (Fv F v) := fun v => if h : v ∈ B.P then β ⟨v, h⟩ else Y.bas v
  have hbas : ∀ v : B.P, bas v = β v := fun v => by simp only [bas, dif_pos v.2]
  let Y₁ : Spc F E n₁ := ⟨J₁, L₁, θ₁, bas₁⟩
  let Y' : Spc F E n := ⟨Y.J, Y.L, θ, bas⟩
  refine ⟨Y', Y₁, ⟨x, y, ι, 𝔟⟩, ?_, ?_, ?_⟩
  · exact { herm := hY.herm, sig := hY.sig, lat := hY.lat, dual := hY.dual, cartan := fun w => (hθ w).1
            bas := fun v => by
              rw [show (GlobalTheory.ThK.reS Y Y').bas v = β v from hbas v]
              exact (hβ v).2 }
  · exact { herm := fun i j => by
              show σ (J₁ j i) = J₁ i j
              rw [← form_single (σ := σ) J₁ j i, ← form_single (σ := σ) J₁ i j, hform₁, hform₁,
                form_swap hcm hY.herm (ι *ᵥ Pi.single j 1) (ι *ᵥ Pi.single i 1)]
            sig := hsig₁
            lat := hlat₁
            dual := fun u => by
              show u ∈ L₁ ↔ ∀ u' ∈ L₁, IsIntegral ℤ (form σ J₁ u u')
              refine ⟨fun hu u' hu' => ?_, fun H => ?_⟩
              · rw [hform₁]; exact (hY.dual _).1 hu _ hu'
              · show ι *ᵥ u ∈ Y.L
                refine (hY.dual _).2 fun z hz => ?_
                obtain ⟨u', hu', hz'⟩ := hsplit z hz
                rw [hz', form_add_right, form_add_right, form_smul_right, form_smul_right, (horth u).1,
                  (horth u).2, mul_zero, mul_zero, zero_add, add_zero, ← hform₁]
                exact H u' hu'
            cartan := hθ₁
            bas := fun v => by
              rw [show Y₁.bas v = β₁ v from hbas₁ v]
              exact hβ₁ v }
  · exact { rank := hn, xx := hxx, yy := hyy, xy := hxy, orth := horth, gram := rfl, low := fun u => Iff.rfl
            split := fun z hz => by
              obtain ⟨u, hu, hz'⟩ := hsplit z hz
              exact ⟨_, _, u, (hL z hz).1, (hL z hz).2, hu, hz'⟩
            ideal := h𝔟
            cartan := fun w => ⟨(hθ w).2.1, 1, one_ne_zero, by rw [one_smul]; exact (hθ w).2.2.symm⟩
            bas := fun v i => by
              rw [show (GlobalTheory.ThK.reS Y Y').bas v = β v from hbas v, show Y₁.bas v = β₁ v from hbas₁ v]
              exact (hβ v).1 i }

end GlobalTheory.KTowerPlane
end
end

section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hyperbolicPlane_split_hermitianLatticeSpace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ), n = n₁ + 2 → 1 ≤ n₁ → ∀ (Y : Spc F E n) (r s : ℕ), 1 ≤ r → 1 ≤ s →
    Y.IsHerm σ B r s → ∀ i₀ i₁ : ℕ, i₀ < i₁ → i₁ < n → ∃ (Y' : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
      (GlobalTheory.ThK.reS Y Y').IsHerm σ B r s ∧ Y₁.IsHerm σ B (r - 1) (s - 1) ∧ H.IsAdapted σ B (GlobalTheory.ThK.reS Y Y') Y₁ i₀ i₁ := by
  first | exact @GlobalTheory.KTowerPlane.exists_hyperbolic_split | exact GlobalTheory.KTowerPlane.exists_hyperbolic_split | (intros; apply GlobalTheory.KTowerPlane.exists_hyperbolic_split <;> assumption)
end
