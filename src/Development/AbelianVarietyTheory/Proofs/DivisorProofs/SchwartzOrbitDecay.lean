import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorusUOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzThetaDistributionSumNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsGoodModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenSchwartzSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticBlockBasisOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFrameModelEvaluationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFrameModelVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaSumNormLePolynomialScale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelDomainReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormAdelicThetaSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

namespace GlobalTheory.ThKTorus

open Module

theorem exists_isSymplecticBasis_extend_family {R M ι : Type} [Field R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Fintype ι] {B : LinearMap.BilinForm R M} (hB : B.IsAlt) (hp : Function.Injective B)
    {v f : ι → M} (hf : IsSymplecticFamily B v f fun _ => 1) :
    ∃ (g : ℕ) (b : Basis ((ι ⊕ Fin g) ⊕ (ι ⊕ Fin g)) R M), IsSymplecticBasis B b ∧
      (∀ i, b (.inl (.inl i)) = v i) ∧ ∀ i, b (.inr (.inl i)) = f i := by
  classical
  let N : Submodule R M := (⨅ i, LinearMap.ker (B (v i))) ⊓ ⨅ i, LinearMap.ker (B (f i))
  have hmem : ∀ y, y ∈ N ↔ (∀ i, B (v i) y = 0) ∧ ∀ i, B (f i) y = 0 := fun y => by
    simp [N, Submodule.mem_iInf]
  have hdec : ∀ y, ∃ a b : ι → R, ∃ y' ∈ N, y = ∑ i, a i • v i + ∑ i, b i • f i + y' := by
    intro y
    refine ⟨fun i => B y (f i), fun i => B (v i) y,
      y - ∑ i, B y (f i) • v i - ∑ i, B (v i) y • f i, (hmem _).2 ⟨fun k => ?_, fun k => ?_⟩,
      by abel⟩
    · simp [hf.left_left, hf.left_right]
    · simp [hf.right_right, hf.right_left hB, ← hB.neg_eq y]
  obtain ⟨g, e', f', d, h', hd, -, hspan⟩ := exists_isSymplecticFamily_span_eq hB N (by
    intro x hx hx0
    refine (injective_iff_map_eq_zero B).1 hp x (LinearMap.ext fun y => ?_)
    obtain ⟨a, b, y', hy', rfl⟩ := hdec y
    simp [hx0 y' hy', fun i => hB.eq_iff.1 (((hmem x).1 hx).1 i),
      fun i => hB.eq_iff.1 (((hmem x).1 hx).2 i)])
  have he' : ∀ i, e' i ∈ N := fun i => hspan ▸ Submodule.subset_span ⟨Sum.inl i, rfl⟩
  have hf' : ∀ i, f' i ∈ N := fun i => hspan ▸ Submodule.subset_span ⟨Sum.inr i, rfl⟩
  have h'' : IsSymplecticFamily B e' (fun i => (d i)⁻¹ • f' i) fun _ => 1 :=
    ⟨h'.left_left, fun i j => by simp [h'.right_right], fun i => by simp [h'.left_right_self, hd i],
      fun i j hij => by simp [h'.left_right_ne i j hij]⟩
  have hs := IsSymplecticFamily.sum hB hf h'' (fun i j => ((hmem _).1 (he' j)).1 i)
    (fun i j => ((hmem _).1 (N.smul_mem _ (hf' j))).1 i) (fun i j => ((hmem _).1 (he' j)).2 i)
    (fun i j => ((hmem _).1 (N.smul_mem _ (hf' j))).2 i)
  have h1 : (Sum.elim (fun _ : ι => (1 : R)) fun _ : Fin g => (1 : R)) = fun _ => 1 := by
    funext i; cases i <;> rfl
  rw [h1] at hs
  have hsp : ⊤ ≤ Submodule.span R (Set.range (Sum.elim (Sum.elim v e')
      (Sum.elim f fun i => (d i)⁻¹ • f' i))) := by
    intro y _
    obtain ⟨a, b, y', hy', rfl⟩ := hdec y
    refine Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)) ?_
    · exact Submodule.subset_span ⟨Sum.inl (Sum.inl i), rfl⟩
    · exact Submodule.subset_span ⟨Sum.inr (Sum.inl i), rfl⟩
    · rw [← hspan] at hy'
      refine Submodule.span_le.2 ?_ hy'
      rintro _ ⟨i | i, rfl⟩
      · exact Submodule.subset_span ⟨Sum.inl (Sum.inr i), rfl⟩
      · have : Sum.elim e' f' (Sum.inr i) = d i • (d i)⁻¹ • f' i := by simp [smul_smul, hd i]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr (Sum.inr i), rfl⟩)
  refine ⟨g, Basis.mk (hs.linearIndependent fun _ => one_ne_zero) hsp, ?_, fun i => by simp, fun i => by simp⟩
  simpa [IsSymplecticBasis, IsSymplecticBasisOfType] using hs

section

variable {F E : Type} [Field F] [Field E] [Algebra F E]

noncomputable def colTraceBil (σ : E →ₐ[F] E) {d : ℕ} (K : Matrix (Fin d) (Fin d) E) :
    LinearMap.BilinForm F (Fin d → E) :=
  LinearMap.mk₂ F (fun f g => Algebra.trace F E (-1 * form σ K f g))
    (fun x x' y => by simp only [form, add_dotProduct, mul_add, map_add])
    (fun a x y => by simp only [form, smul_dotProduct, mul_smul_comm, map_smul])
    (fun x y y' => by
      simp only [form, dotProduct, Matrix.mulVec, Pi.add_apply, Finset.sum_add_distrib, mul_add, map_add])
    (fun a x y => by
      simp only [form, dotProduct, Matrix.mulVec, Pi.smul_apply, ← Finset.smul_sum, mul_smul_comm, map_smul])

theorem colTraceBil_apply (σ : E →ₐ[F] E) {d : ℕ} (K : Matrix (Fin d) (Fin d) E) (f g : Fin d → E) :
    colTraceBil σ K f g = Algebra.trace F E (-1 * form σ K f g) := rfl

theorem nondegenerate_colTraceBil [CharZero F] [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a)
    {d : ℕ} {K : Matrix (Fin d) (Fin d) E} (hK : K.det ≠ 0) : (colTraceBil σ K).Nondegenerate := by
  rw [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  refine Matrix.eq_zero_of_vecMul_eq_zero hK (funext fun l => ?_)
  refine (traceForm_nondegenerate F E).1 _ fun a => ?_
  have := LinearMap.congr_fun hf (Pi.single l (σ (-a)))
  rw [colTraceBil_apply, LinearMap.zero_apply] at this
  rw [Algebra.traceForm_apply, ← this]
  congr 1
  have h : (fun i => σ ((Pi.single l (σ (-a)) : Fin d → E) i)) = Pi.single l (-a) := by
    funext i
    by_cases hi : i = l
    · subst hi; simp only [Pi.single_eq_same, hσ]
    · simp [hi]
  rw [form, h, Matrix.dotProduct_mulVec, dotProduct_single]
  ring

theorem symp_vecMulVec_right (σ : E →ₐ[F] E) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (K : Matrix (Fin d) (Fin d) E) (m : Matrix (Fin n) (Fin d) E) (v : Fin n → E) (w : Fin d → E) :
    symp σ (-1) J K m (Matrix.vecMulVec v w) = colTraceBil σ K (fun l => form σ J (fun r => m r l) v) w := by
  rw [colTraceBil_apply, symp]
  congr 2
  simp only [hTens, form, dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem symp_vecMulVec (σ : E →ₐ[F] E) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (K : Matrix (Fin d) (Fin d) E) (u v : Fin n → E) (f w : Fin d → E) :
    symp σ (-1) J K (Matrix.vecMulVec u f) (Matrix.vecMulVec v w) = colTraceBil σ K (form σ J u v • f) w := by
  rw [symp_vecMulVec_right]
  congr 2
  funext l
  simp only [form, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem form_swap (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (u v : Fin n → E) : form σ J u v = σ (form σ J v u) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end

theorem exists_frame_symplectic_basis : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d q : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin d) (Fin d) E) (x y : Fin q → Fin n → E),
    (∀ a, σ (σ a) = a) → Module.finrank F E = 2 → (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    (∀ i j, σ (K j i) = -K i j) → K.det ≠ 0 → IsFrameU σ J x y →
    ∃ (b : Module.Basis ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F (Matrix (Fin n) (Fin d) E))
      (blk : Fin q → Finset (Fin n × Fin d)),
      (∀ i j, i ≠ j → Disjoint (blk i) (blk j)) ∧
      (∀ k l, symp σ (-1) J K (b (.inl k)) (b (.inl l)) = 0) ∧
      (∀ k l, symp σ (-1) J K (b (.inr k)) (b (.inr l)) = 0) ∧
      (∀ k l, symp σ (-1) J K (b (.inl k)) (b (.inr l)) = if k = l then 1 else 0) ∧
      (∀ k l, symp σ (-1) J K (b (.inr k)) (b (.inl l)) = if k = l then -1 else 0) ∧
      (∀ i, ∀ k ∈ blk i, ∃ w : Fin d → E, b (.inl k) = Matrix.vecMulVec (y i) w) ∧
      (∀ i, ∀ k ∈ blk i, ∃ w : Fin d → E, b (.inr k) = Matrix.vecMulVec (x i) w) ∧
      (∀ k, (∀ i, k ∉ blk i) → ∀ (l : Fin d) (i : Fin q),
        form σ J (fun r => b (.inl k) r l) (x i) = 0 ∧ form σ J (fun r => b (.inl k) r l) (y i) = 0 ∧
        form σ J (fun r => b (.inr k) r l) (x i) = 0 ∧ form σ J (fun r => b (.inr k) r l) (y i) = 0) := by
  intro F E _ _ _ _ _ σ n d q J K x y hσ h2 hJ hJ' hK hK' hfr
  classical
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have halt := GlobalTheory.RatDarboux.isAlt_sympBil σ hσ hJ hK
  have hinj := (GlobalTheory.RatDarboux.bijective_sympBil σ hσ hJ' hK').1
  have hnd := nondegenerate_colTraceBil σ hσ hK'
  set B := GlobalTheory.RatDarboux.sympBil σ (-1) J K with hBdef
  have hB : ∀ a b, B a b = symp σ (-1) J K a b := fun _ _ => rfl
  let g := Module.finBasis F (Fin d → E)
  let f := (colTraceBil σ K).dualBasis hnd g
  have hfg : ∀ k l, colTraceBil σ K (f k) (g l) = if l = k then 1 else 0 :=
    LinearMap.BilinForm.apply_dualBasis_left hnd g
  have hyx : ∀ i j, form σ J (y i) (x j) = if i = j then 1 else 0 := fun i j => by
    rw [form_swap σ hσ hJ, hfr.2.2]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  have hfam : IsSymplecticFamily B
      (fun p : Fin q × Fin (Module.finrank F (Fin d → E)) => Matrix.vecMulVec (y p.1) (f p.2))
      (fun p => Matrix.vecMulVec (x p.1) (g p.2)) fun _ => 1 := by
    refine ⟨fun p r => ?_, fun p r => ?_, fun p => ?_, fun p r hpr => ?_⟩
    · simp [hB, symp_vecMulVec, hfr.2.1]
    · simp [hB, symp_vecMulVec, hfr.1]
    · simp [hB, symp_vecMulVec, hyx, hfg]
    · rw [hB, symp_vecMulVec, hyx]
      by_cases h : p.1 = r.1
      · have h' : ¬ r.2 = p.2 := fun h' => hpr (Prod.ext h h'.symm)
        simp [h, hfg, h']
      · simp [h]
  obtain ⟨s, b₀, hb₀, hl, hr⟩ := exists_isSymplecticBasis_extend_family halt hinj hfam
  have hcard : Fintype.card ((Fin q × Fin (Module.finrank F (Fin d → E))) ⊕ Fin s) =
      Fintype.card (Fin n × Fin d) := by
    have h1 := IsSymplecticBasisOfType.finrank_eq b₀
    rw [Module.finrank_matrix, h2] at h1
    rw [Fintype.card_prod (Fin n)]
    omega
  let ε := Fintype.equivOfCardEq hcard
  have hb := hb₀.reindex ε
  have hbl : ∀ k, b₀.reindex (ε.sumCongr ε) (.inl (ε k)) = b₀ (.inl k) := fun k => by simp
  have hbr : ∀ k, b₀.reindex (ε.sumCongr ε) (.inr (ε k)) = b₀ (.inr k) := fun k => by simp
  have hcol : ∀ (m : Matrix (Fin n) (Fin d) E) (v : Fin n → E)
      (c : Basis (Fin (Module.finrank F (Fin d → E))) F (Fin d → E)),
      (∀ k, B m (Matrix.vecMulVec v (c k)) = 0) → ∀ l, form σ J (fun r => m r l) v = 0 := by
    intro m v c h l
    have h0 : colTraceBil σ K (fun l => form σ J (fun r => m r l) v) = 0 :=
      c.ext fun k => by rw [← symp_vecMulVec_right, ← hB, h, LinearMap.zero_apply]
    exact congrFun (hnd.1 _ fun w => by rw [h0, LinearMap.zero_apply]) l
  refine ⟨b₀.reindex (ε.sumCongr ε), fun i => Finset.univ.image fun k => ε (.inl (i, k)), ?_,
    hb.left_left, hb.right_right, hb.left_right, hb.right_left halt, ?_, ?_, ?_⟩
  · intro i j hij
    rw [Finset.disjoint_left]
    intro a ha ha'
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨k', -, h⟩ := Finset.mem_image.1 ha'
    exact hij (congrArg Prod.fst (Sum.inl_injective (ε.injective h))).symm
  · intro i k hk
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hk
    exact ⟨f k, by rw [hbl, hl]⟩
  · intro i k hk
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hk
    exact ⟨g k, by rw [hbr, hr]⟩
  · intro k hk l i
    obtain ⟨k, rfl⟩ := ε.surjective k
    rcases k with ⟨j, k⟩ | k
    · exact absurd (Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩) (hk j)
    rw [hbl, hbr]
    refine ⟨hcol _ _ g (fun k' => ?_) l, hcol _ _ f (fun k' => ?_) l, hcol _ _ g (fun k' => ?_) l,
      hcol _ _ f (fun k' => ?_) l⟩
    · rw [← hr (i, k'), hb₀.left_right]; simp
    · rw [← hl (i, k'), hb₀.left_left]
    · rw [← hr (i, k'), hb₀.right_right]
    · rw [← hl (i, k'), hb₀.right_left halt]; simp

end GlobalTheory.ThKTorus
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_basis_of_unitary_frame : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d q : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin d) (Fin d) E) (x y : Fin q → Fin n → E),
    (∀ a, σ (σ a) = a) → Module.finrank F E = 2 → (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    (∀ i j, σ (K j i) = -K i j) → K.det ≠ 0 → IsFrameU σ J x y →
    ∃ (b : Module.Basis ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F (Matrix (Fin n) (Fin d) E))
      (blk : Fin q → Finset (Fin n × Fin d)),
      (∀ i j, i ≠ j → Disjoint (blk i) (blk j)) ∧
      (∀ k l, symp σ (-1) J K (b (.inl k)) (b (.inl l)) = 0) ∧
      (∀ k l, symp σ (-1) J K (b (.inr k)) (b (.inr l)) = 0) ∧
      (∀ k l, symp σ (-1) J K (b (.inl k)) (b (.inr l)) = if k = l then 1 else 0) ∧
      (∀ k l, symp σ (-1) J K (b (.inr k)) (b (.inl l)) = if k = l then -1 else 0) ∧
      (∀ i, ∀ k ∈ blk i, ∃ w : Fin d → E, b (.inl k) = Matrix.vecMulVec (y i) w) ∧
      (∀ i, ∀ k ∈ blk i, ∃ w : Fin d → E, b (.inr k) = Matrix.vecMulVec (x i) w) ∧
      (∀ k, (∀ i, k ∉ blk i) → ∀ (l : Fin d) (i : Fin q),
        form σ J (fun r => b (.inl k) r l) (x i) = 0 ∧ form σ J (fun r => b (.inl k) r l) (y i) = 0 ∧
        form σ J (fun r => b (.inr k) r l) (x i) = 0 ∧ form σ J (fun r => b (.inr k) r l) (y i) = 0) := by
  atlas_forward_decl GlobalTheory.ThKTorus.exists_frame_symplectic_basis
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_block_basis_orthogonal : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d q : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin d) (Fin d) E) (x y : Fin q → Fin n → E)
    (b : Module.Basis ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F (Matrix (Fin n) (Fin d) E))
    (blk : Fin q → Finset (Fin n × Fin d)),
    (∀ i j, i ≠ j → Disjoint (blk i) (blk j)) →
    (∀ k l, symp σ (-1) J K (b (.inl k)) (b (.inl l)) = 0) →
    (∀ k l, symp σ (-1) J K (b (.inr k)) (b (.inr l)) = 0) →
    (∀ k l, symp σ (-1) J K (b (.inl k)) (b (.inr l)) = if k = l then 1 else 0) →
    (∀ k l, symp σ (-1) J K (b (.inr k)) (b (.inl l)) = if k = l then -1 else 0) →
    (∀ i, ∀ k ∈ blk i, ∃ w : Fin d → E, b (.inl k) = Matrix.vecMulVec (y i) w) →
    (∀ i, ∀ k ∈ blk i, ∃ w : Fin d → E, b (.inr k) = Matrix.vecMulVec (x i) w) →
    (∀ k, (∀ i, k ∉ blk i) → ∀ (l : Fin d) (i : Fin q),
        form σ J (fun r => b (.inl k) r l) (x i) = 0 ∧ form σ J (fun r => b (.inl k) r l) (y i) = 0 ∧
        form σ J (fun r => b (.inr k) r l) (x i) = 0 ∧ form σ J (fun r => b (.inr k) r l) (y i) = 0) →
    ∃ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F K)) (Fin n × Fin d),
      (∀ m : Matrix (Fin n) (Fin d) E, ∃ u v : Fin n × Fin d → F,
        co.e (incM F m) = (fun i => algebraMap F (AF F) (u i), fun i => algebraMap F (AF F) (v i))) ∧
      IsFrameCo σ J K x y co blk := by
  first | exact @GlobalTheory.ThKTorus.exists_frameCo_of_basis | exact GlobalTheory.ThKTorus.exists_frameCo_of_basis | (intros; apply GlobalTheory.ThKTorus.exists_frameCo_of_basis <;> assumption)
end

section
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

namespace GlobalTheory.ThKFrameModel

theorem exists_frame_model : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∃ (M₁ : Model σ X W) (blk : Fin q → Finset (Fin n × Fin d)) (e : Fn F n d →ₗ[ℂ] Fn F n d) (c : ℂ),
      M₁.IsGood B.ψ ∧ IsFrameCo σ X.J W.J x y M₁.co blk ∧ IsEv B M M₁ 1 1 ∅ e ∧ c ≠ 0 ∧
      ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (e Φ) = c * thetaSum F Φ := by
  have hA1 := @GlobalTheory.T.symplectic_basis_of_unitary_frame
  have hA2 := @GlobalTheory.T.symplectic_block_basis_orthogonal

  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair q x y hxy
  have hB := hpair.base
  have hX := hpair.herm
  have hW := hpair.skew
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ a, σ (σ a) = a := fun a => by
    apply ((B.emb w).1 : E →+* ℂ).injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hXd : X.J.det ≠ 0 := fun h0 => by
    apply GlobalTheory.RatDarboux.det_ne_zero_of_isCartan (hX.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det X.J
    rw [h0, map_zero] at this
    exact this.symm
  have hWd : W.J.det ≠ 0 := fun h0 => by
    apply GlobalTheory.RatDarboux.det_ne_zero_of_isCartan (hW.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det W.J
    rw [h0, map_zero] at this
    rw [Matrix.det_smul]
    exact mul_eq_zero_of_right _ this.symm
  obtain ⟨b, blk, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    hA1 σ X.J W.J x y hσ hB.cm.2.2.1 hX.herm hXd hW.skew hWd hxy
  obtain ⟨co, hco, hfr⟩ := hA2 σ X.J W.J x y b blk h1 h2 h3 h4 h5 h6 h7 h8
  obtain ⟨e, ei, ev, hei, hmaps, hheis, hSB, hvac, hstd, hpure, hbij⟩ :=
    GlobalTheory.T.darboux_coords_good_model F E σ B n d X W M r s r' s' hpair.base hpair.herm hpair.skew hpair.good co hco
  let M₁ : Model σ X W := ⟨co, fun v => ev v (M.vac v), M.μ, M.dom⟩
  have hM₁ : M₁.IsGood B.ψ := ⟨hco, hvac, hstd, hpair.good.haar, hpair.good.dom⟩
  have hne : ∃ f : SInf F (Fin n × Fin d), f ≠ 0 := by
    by_contra hall
    push_neg at hall
    obtain ⟨φ, hφ, hθ⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F (Fin n × Fin d)
    have hle : schA F (Fin n × Fin d) ≤ ⊥ := by
      refine Submodule.span_le.2 ?_
      rintro Φ ⟨f, g, -, rfl⟩
      rw [hall f]
      show pureA F 0 g = 0
      funext x
      simp [pureA]
    have h0 : φ = 0 := (Submodule.mem_bot ℂ).1 (hle hφ)
    exact hθ (by rw [h0]; simp [thetaSum])
  have hev : IsEv B M M₁ 1 1 ∅ e := by
    refine ⟨hmaps, fun z Φ hΦ => ?_, fun u hu => hu.elim, ei, ev, ?_, fun v => ⟨rfl, hSB v⟩, hpure⟩
    · have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
      have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
      rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
      exact hheis z Φ hΦ
    · obtain ⟨f, hf⟩ := hne
      obtain ⟨g, rfl⟩ := hei f
      intro h
      exact hf (by rw [h]; rfl)
  obtain ⟨c₀, hc₀, hth⟩ := GlobalTheory.T.weil_eigen_schwartz_surjective F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij
  exact ⟨M₁, blk, e, c₀, hM₁, hfr, hev, hc₀, hth⟩

end GlobalTheory.ThKFrameModel

end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_model_blocks_unitary_frame : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∃ (M₁ : Model σ X W) (blk : Fin q → Finset (Fin n × Fin d)) (e : Fn F n d →ₗ[ℂ] Fn F n d) (c : ℂ),
      M₁.IsGood B.ψ ∧ IsFrameCo σ X.J W.J x y M₁.co blk ∧ IsEv B M M₁ 1 1 ∅ e ∧ c ≠ 0 ∧
      ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (e Φ) = c * thetaSum F Φ := by
  atlas_forward_decl GlobalTheory.ThKFrameModel.exists_frame_model
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section
namespace GlobalTheory.ThKTorusLatSum
open mixedEmbedding
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

theorem exists_one_le_place (x : F) (hx : IsIntegral ℤ x) (h0 : x ≠ 0) : ∃ w : InfinitePlace F, 1 ≤ w x := by
  by_contra h
  push_neg at h
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have ha : (⟨x, hx⟩ : 𝓞 F) ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  have := InfinitePlace.one_le_of_lt_one (w := w) ha (fun z _ => h z)
  exact absurd this (not_le.mpr (h w))

theorem place_natCast_mul (w : InfinitePlace F) (m : ℕ) (x : F) : w ((m : F) * x) = m * w x := by
  rw [← InfinitePlace.norm_embedding_eq, ← InfinitePlace.norm_embedding_eq, map_mul, map_natCast, norm_mul,
    Complex.norm_natCast]

theorem inv_le_sum_places (m : ℕ) (hm : 1 ≤ m) (x : F) (hint : IsIntegral ℤ ((m : F) * x)) (h0 : x ≠ 0) :
    (m : ℝ)⁻¹ ≤ ∑ w : InfinitePlace F, w x := by
  have hm0 : (m : F) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hm)
  obtain ⟨w, hw⟩ := exists_one_le_place _ hint (mul_ne_zero hm0 h0)
  rw [place_natCast_mul, mul_comm] at hw
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  calc (m : ℝ)⁻¹ ≤ w x := by rw [inv_le_iff_one_le_mul₀ hmpos]; exact hw
    _ ≤ _ := Finset.single_le_sum (f := fun w : InfinitePlace F => w x) (fun w _ => apply_nonneg w x) (Finset.mem_univ w)

theorem norm_mixedEmbedding_le (x : F) : ‖(mixedEmbedding F x : NumberField.mixedEmbedding.mixedSpace F)‖ ≤ ∑ w : InfinitePlace F, w x := by
  have hs : 0 ≤ ∑ w : InfinitePlace F, w x := Finset.sum_nonneg fun w _ => apply_nonneg w x
  rw [Prod.norm_def]
  refine max_le ((pi_norm_le_iff_of_nonneg hs).mpr fun w => ?_) ((pi_norm_le_iff_of_nonneg hs).mpr fun w => ?_)
  · rw [mixedEmbedding_apply_isReal, InfinitePlace.norm_embedding_of_isReal]
    exact Finset.single_le_sum (f := fun w : InfinitePlace F => w x) (fun w _ => apply_nonneg w x) (Finset.mem_univ _)
  · rw [mixedEmbedding_apply_isComplex, InfinitePlace.norm_embedding_eq]
    exact Finset.single_le_sum (f := fun w : InfinitePlace F => w x) (fun w _ => apply_nonneg w x) (Finset.mem_univ _)

theorem norm_pi_mixedEmbedding_le {κ : Type} [Fintype κ] (ξ : κ → F) :
    ‖((fun j => mixedEmbedding F (ξ j)) : κ → NumberField.mixedEmbedding.mixedSpace F)‖ ≤ ∑ j, ∑ w : InfinitePlace F, w (ξ j) := by
  have hs : 0 ≤ ∑ j, ∑ w : InfinitePlace F, w (ξ j) :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun w _ => apply_nonneg w _
  refine (pi_norm_le_iff_of_nonneg hs).mpr fun j => (norm_mixedEmbedding_le (ξ j)).trans ?_
  exact Finset.single_le_sum (f := fun j => ∑ w : InfinitePlace F, w (ξ j))
    (fun j _ => Finset.sum_nonneg fun w _ => apply_nonneg w _) (Finset.mem_univ j)

theorem stepB (P P0 : ℝ) (hP0 : 0 < P0) (h : P0 ≤ P) (A N₀ D : ℕ) :
    P ^ A * (1 + P) ^ N₀ * (P ^ (A + N₀ + D))⁻¹ ≤ (1 + P0⁻¹) ^ N₀ * (P0 ^ D)⁻¹ := by
  have hP : 0 < P := hP0.trans_le h
  have e : P ^ A * (1 + P) ^ N₀ * (P ^ (A + N₀ + D))⁻¹ = (1 + P⁻¹) ^ N₀ * (P ^ D)⁻¹ := by
    have hP' : P ≠ 0 := hP.ne'
    rw [show (1 : ℝ) + P⁻¹ = (1 + P) * P⁻¹ by rw [add_mul, one_mul, mul_inv_cancel₀ hP', add_comm], mul_pow, pow_add, pow_add, inv_pow]
    field_simp
  rw [e]
  gcongr

theorem latG_tsum_le : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (q : ℕ) (blk : Fin q → Finset κ)
    (A N₀ : ℕ) (c : ℝ), 0 < c → ∃ (N : ℕ) (C : ℝ) (K : ℕ), ∀ (m : ℕ) (t : Fin q → ℝ), 1 ≤ m → (∀ i, c ≤ t i) →
      Summable (latG (F := F) blk A N m t) ∧ (∑' ξ, latG (F := F) blk A N m t ξ) * (1 + ∏ i, t i) ^ N₀ ≤ C * (m : ℝ) ^ K := by
  intro F _ _ κ _ _ q blk A N₀ c hc
  set L := GlobalTheory.LatScaleSum.latPi F κ with hL
  set D : ℕ := Module.finrank ℤ L + 1 with hD
  set H : (κ → mixedSpace F) → ℝ := fun v => ((1 + ‖v‖) ^ D)⁻¹ with hH
  have hHs : Summable fun z : L => H z := GlobalTheory.LatScaleSum.summable_inv_one_add_pow F κ
  set P0 : ℝ := c ^ q with hP0def
  have hP0 : 0 < P0 := pow_pos hc q
  set B : ℝ := (1 + P0⁻¹) ^ N₀ * (P0 ^ D)⁻¹ with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨A + N₀ + D, B * ∑' z : L, H z, q * (A + N₀ + D) + D, ?_⟩
  intro m t hm ht
  set N := A + N₀ + D with hN
  set P : ℝ := ∏ i, t i with hPdef
  have ht0 : ∀ i, 0 < t i := fun i => hc.trans_le (ht i)
  have hPP0 : P0 ≤ P := by
    rw [hP0def, hPdef]
    calc c ^ q = ∏ _i : Fin q, c := by simp
      _ ≤ ∏ i, t i := Finset.prod_le_prod (fun i _ => hc.le) (fun i _ => ht i)
  have hP : 0 < P := hP0.trans_le hPP0
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hm0 : (m : F) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hm)
  set ψ : (κ → F) → (κ → mixedSpace F) := fun ξ i => mixedEmbedding F (ξ i) with hψdef
  set g : (κ → F) → (κ → mixedSpace F) := fun ξ => ψ (fun i => (m : F) * ξ i) with hgdef
  have hginj : Function.Injective g := by
    intro ξ η h
    funext i
    have := congrFun h i
    simp only [hgdef, hψdef] at this
    exact mul_left_cancel₀ hm0 (mixedEmbedding_injective F this)
  have hgsmul : ∀ ξ, g ξ = m • ψ ξ := by
    intro ξ
    funext i
    simp only [hgdef, hψdef, Pi.smul_apply]
    rw [← nsmul_eq_mul, map_nsmul]
  set Lind : (κ → mixedSpace F) → ℝ := (L : Set (κ → mixedSpace F)).indicator H with hLind
  have hLs : Summable Lind := summable_subtype_iff_indicator.mp hHs
  have hLnn : ∀ v, 0 ≤ Lind v := fun v => Set.indicator_nonneg (fun v _ => by positivity) v
  have key : ∀ ξ, latG (F := F) blk A N m t ξ * (1 + P) ^ N₀ ≤ B * (m : ℝ) ^ (q * N + D) * Lind (g ξ) := by
    intro ξ
    have hR : 0 ≤ B * (m : ℝ) ^ (q * N + D) * Lind (g ξ) := mul_nonneg (by positivity) (hLnn _)
    unfold latG
    split_ifs with hblk
    swap
    · simpa using hR
    unfold majI
    split_ifs with hint
    swap
    · simpa using hR
    have hmem : g ξ ∈ L := GlobalTheory.LatScaleSum.mem_latPi F κ _ hint
    rw [hLind, Set.indicator_of_mem hmem]
    set S : Fin q → ℝ := fun i => ∑ j ∈ blk i, ∑ w : InfinitePlace F, w (ξ j) with hS
    set s : ℝ := ∑ j, ∑ w : InfinitePlace F, w (ξ j) with hs
    have hS0 : ∀ i, (m : ℝ)⁻¹ ≤ S i := by
      intro i
      obtain ⟨j, hj, hξ⟩ := hblk i
      exact (inv_le_sum_places m hm (ξ j) (hint j) hξ).trans
        (Finset.single_le_sum (f := fun j => ∑ w : InfinitePlace F, w (ξ j))
          (fun j _ => Finset.sum_nonneg fun w _ => apply_nonneg w _) hj)
    set Q : ℝ := ∏ i, (1 + t i * S i) with hQ
    have hQge : P * ((m : ℝ) ^ q)⁻¹ ≤ Q := by
      calc P * ((m : ℝ) ^ q)⁻¹ = ∏ i, (t i * (m : ℝ)⁻¹) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]
        _ ≤ Q := Finset.prod_le_prod (fun i _ => by have := ht0 i; positivity) (fun i _ => by
              have := mul_le_mul_of_nonneg_left (hS0 i) (ht0 i).le
              exact le_add_of_nonneg_of_le zero_le_one this)
    have hs0 : 0 ≤ s := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun w _ => apply_nonneg w _
    have hQpos : 0 < P * ((m : ℝ) ^ q)⁻¹ := by positivity
    have hmaj : majW blk A N t ξ = P ^ A * ((Q ^ N) * (1 + s) ^ N)⁻¹ := by
      unfold majW
      rw [Finset.prod_pow]
    rw [hmaj]
    have hψn : ‖ψ ξ‖ ≤ s := norm_pi_mixedEmbedding_le ξ
    have hgn : ‖g ξ‖ ≤ m * ‖ψ ξ‖ := by rw [hgsmul]; exact norm_nsmul_le
    have hcc : ((1 + s) ^ N)⁻¹ ≤ (m : ℝ) ^ D * H (g ξ) := by
      have h1 : ((1 + s) ^ N)⁻¹ ≤ ((1 + s) ^ D)⁻¹ := by
        apply inv_anti₀ (by positivity)
        exact pow_le_pow_right₀ (by linarith) (by omega)
      calc ((1 + s) ^ N)⁻¹ ≤ ((1 + s) ^ D)⁻¹ := h1
        _ ≤ ((1 + ‖ψ ξ‖) ^ D)⁻¹ := by gcongr
        _ = (m : ℝ) ^ D * (((m : ℝ) * (1 + ‖ψ ξ‖)) ^ D)⁻¹ := by
            rw [mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hmpos.ne'), one_mul]
        _ ≤ (m : ℝ) ^ D * ((1 + ‖g ξ‖) ^ D)⁻¹ := by
            gcongr
            have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
            nlinarith [norm_nonneg (ψ ξ), hgn]
    have ha : (Q ^ N)⁻¹ ≤ (m : ℝ) ^ (q * N) * (P ^ N)⁻¹ := by
      calc (Q ^ N)⁻¹ ≤ ((P * ((m : ℝ) ^ q)⁻¹) ^ N)⁻¹ := by gcongr
        _ = _ := by rw [mul_pow, mul_inv, inv_pow, inv_inv, ← pow_mul, mul_comm]
    have hb := stepB P P0 hP0 hPP0 A N₀ D
    have hHg : 0 ≤ H (g ξ) := by positivity
    calc P ^ A * ((Q ^ N) * (1 + s) ^ N)⁻¹ * (1 + P) ^ N₀
        = P ^ A * (1 + P) ^ N₀ * (Q ^ N)⁻¹ * ((1 + s) ^ N)⁻¹ := by rw [mul_inv]; ring
      _ ≤ P ^ A * (1 + P) ^ N₀ * ((m : ℝ) ^ (q * N) * (P ^ N)⁻¹) * ((m : ℝ) ^ D * H (g ξ)) := by
          gcongr
      _ = (P ^ A * (1 + P) ^ N₀ * (P ^ N)⁻¹) * (m : ℝ) ^ (q * N + D) * H (g ξ) := by rw [pow_add]; ring
      _ ≤ B * (m : ℝ) ^ (q * N + D) * H (g ξ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (by positivity)) hHg
  have hnn : ∀ ξ, 0 ≤ latG (F := F) blk A N m t ξ := fun ξ => latG_nonneg blk A N m t ξ (fun i => (ht0 i).le)
  have hpow : 0 < (1 + P) ^ N₀ := by positivity
  have key' : ∀ ξ, latG (F := F) blk A N m t ξ ≤ ((1 + P) ^ N₀)⁻¹ * (B * (m : ℝ) ^ (q * N + D)) * Lind (g ξ) := by
    intro ξ
    calc latG (F := F) blk A N m t ξ = ((1 + P) ^ N₀)⁻¹ * (latG (F := F) blk A N m t ξ * (1 + P) ^ N₀) := by
          field_simp
      _ ≤ ((1 + P) ^ N₀)⁻¹ * (B * (m : ℝ) ^ (q * N + D) * Lind (g ξ)) := mul_le_mul_of_nonneg_left (key ξ) (by positivity)
      _ = _ := by ring
  have hu : Summable fun ξ => Lind (g ξ) := hLs.comp_injective hginj
  have hsum : Summable (latG (F := F) blk A N m t) := Summable.of_nonneg_of_le hnn key' (hu.mul_left _)
  refine ⟨hsum, ?_⟩
  have hcomp : ∑' ξ, Lind (g ξ) ≤ ∑' v, Lind v := tsum_comp_le_tsum_of_inj hLs hLnn hginj
  have hsub : ∑' v, Lind v = ∑' z : L, H z := (tsum_subtype (L : Set (κ → mixedSpace F)) H).symm
  rw [← tsum_mul_right]
  calc ∑' ξ, latG (F := F) blk A N m t ξ * (1 + P) ^ N₀ ≤ ∑' ξ, B * (m : ℝ) ^ (q * N + D) * Lind (g ξ) :=
        (hsum.mul_right _).tsum_le_tsum key (hu.mul_left _)
    _ = B * (m : ℝ) ^ (q * N + D) * ∑' ξ, Lind (g ξ) := tsum_mul_left
    _ ≤ B * (m : ℝ) ^ (q * N + D) * ∑' z : L, H z := by
        rw [← hsub]; exact mul_le_mul_of_nonneg_left hcomp (by positivity)
    _ = B * (∑' z : L, H z) * (m : ℝ) ^ (q * N + D) := by ring

end GlobalTheory.ThKTorusLatSum
end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_sum_polynomial_bound : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (q : ℕ) (blk : Fin q → Finset κ)
    (A N₀ : ℕ) (c : ℝ), 0 < c → ∃ (N : ℕ) (C : ℝ) (K : ℕ), ∀ (m : ℕ) (t : Fin q → ℝ), 1 ≤ m → (∀ i, c ≤ t i) →
      Summable (latG (F := F) blk A N m t) ∧ (∑' ξ, latG (F := F) blk A N m t ξ) * (1 + ∏ i, t i) ^ N₀ ≤ C * (m : ℝ) ^ K := by
  atlas_forward_decl GlobalTheory.ThKTorusLatSum.latG_tsum_le
end

section
section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

namespace GlobalTheory.ThKTorus

theorem torusDecay : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∀ Cc : Set (UA σ X.J), IsCompact Cc → ∀ c : ℝ, 0 < c →
    ∀ φ ∈ SB (Fin n × Fin d → Af F), (∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ M.So B.ψ B.τ₁) →
    ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ (f : SInf F (Fin n × Fin d)) (t : Fin q → ℝ) (a κ : UA σ X.J) (h : UA σ W.J),
      (∀ i, c ≤ t i) → IsTorusU x y t a → κ ∈ Cc →
      ‖theta om (pureA F f φ) (a * κ) h‖ * (1 + ∏ i, t i) ^ N ≤ C * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair q x y hxy Cc hCc c hc φ hφ hφS N
  obtain ⟨M₁, blk, e, c₀, hM₁, hF, hE, hc₀, hθ⟩ := GlobalTheory.T.exists_model_blocks_unitary_frame hP F E σ B n d X W M χX χW om r s r' s' hPair q x y hxy
  obtain ⟨A, hA⟩ := GlobalTheory.T.norm_weil_action_pure_tensor_le_majorant hP F E σ B n d X W M χX χW om r s r' s' hPair q x y hxy M₁ blk e hM₁ hF hE Cc hCc c hc φ hφ
  obtain ⟨N₁, C₅, K, h5⟩ := GlobalTheory.T.lattice_sum_polynomial_bound F (Fin n × Fin d) q blk A N c hc
  obtain ⟨C₄, k, h4⟩ := hA N₁
  refine ⟨‖c₀⁻¹‖ * max C₄ 0 * max C₅ 0 * (max C₄ 0) ^ K, k * (K + 1), fun f t a κ h htc ha hκ => ?_⟩
  obtain ⟨m, hm1, hmC, hb⟩ := h4 f t a κ h htc ha hκ
  obtain ⟨hsum, hle⟩ := h5 m t hm1 htc
  have hΦ : pureA F f φ ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  have hΨ : om (a * κ, h) (pureA F f φ) ∈ schA F (Fin n × Fin d) := hPair.weil.isUSplitting.pres _ _ hΦ
  have ht0 : ∀ i, 0 ≤ t i := fun i => hc.le.trans (htc i)
  have hsk : 0 ≤ semK (Fin n × Fin d) k f := apply_nonneg _ _
  have hhk : (0 : ℝ) ≤ (ht h : ℝ) ^ k := pow_nonneg (NNReal.coe_nonneg _) _
  have hC4 : (0 : ℝ) ≤ max C₄ 0 := le_max_right _ _
  have hB' : 0 ≤ max C₄ 0 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k := mul_nonneg (mul_nonneg hC4 hsk) hhk
  have hpt : ∀ ξ : Fin n × Fin d → F, ‖e (om (a * κ, h) (pureA F f φ)) (fun j => algebraMap F (AF F) (ξ j))‖ ≤
      max C₄ 0 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * latG (F := F) blk A N₁ m t ξ := by
    intro ξ
    unfold latG
    split_ifs with hnz
    · calc _ ≤ C₄ * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * majI blk A N₁ m t ξ := hb ξ
        _ ≤ max C₄ 0 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * majI blk A N₁ m t ξ := by
          apply mul_le_mul_of_nonneg_right _ (majI_nonneg _ _ _ _ _ _ ht0)
          apply mul_le_mul_of_nonneg_right _ hhk
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hsk
    · push_neg at hnz
      rw [GlobalTheory.T.unitary_frame_model_evaluation hP F E σ B n d X W M χX χW om r s r' s' hPair q x y hxy M₁ blk e hM₁ hF hE _ (hφS f) (a * κ) h ξ hnz]
      simp
  have hs : Summable fun ξ : Fin n × Fin d → F =>
      ‖e (om (a * κ, h) (pureA F f φ)) (fun j => algebraMap F (AF F) (ξ j))‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hsum.mul_left _)
  have hT : ‖thetaSum F (e (om (a * κ, h) (pureA F f φ)))‖ ≤
      max C₄ 0 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * ∑' ξ, latG (F := F) blk A N₁ m t ξ := by
    rw [← tsum_mul_left]
    exact (norm_tsum_le_tsum_norm hs).trans (Summable.tsum_le_tsum hpt hs (hsum.mul_left _))
  have e1 : theta om (pureA F f φ) (a * κ) h = c₀⁻¹ * thetaSum F (e (om (a * κ, h) (pureA F f φ))) := by
    rw [hθ _ hΨ, ← mul_assoc, inv_mul_cancel₀ hc₀, one_mul]; rfl
  have hP0 : (0 : ℝ) ≤ (1 + ∏ i, t i) ^ N := pow_nonneg (add_nonneg zero_le_one (Finset.prod_nonneg fun i _ => ht0 i)) _
  have hmK : (m : ℝ) ^ K ≤ (max C₄ 0 * (ht h : ℝ) ^ k) ^ K :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (hmC.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hhk)) K
  have hsemi : semK (Fin n × Fin d) k f ≤ semK (Fin n × Fin d) (k * (K + 1)) f := by
    have hk : k ≤ k * (K + 1) := Nat.le_mul_of_pos_right k (Nat.succ_pos K)
    have hle' : semK (F := F) (Fin n × Fin d) k ≤ semK (F := F) (Fin n × Fin d) (k * (K + 1)) :=
      Finset.sup_mono (Finset.Iic_subset_Iic.2 (Prod.mk_le_mk.2 ⟨hk, hk⟩))
    exact hle' f
  have hS0 : 0 ≤ ∑' ξ, latG (F := F) blk A N₁ m t ξ := tsum_nonneg fun ξ => latG_nonneg _ _ _ _ _ _ ht0
  calc ‖theta om (pureA F f φ) (a * κ) h‖ * (1 + ∏ i, t i) ^ N
      ≤ ‖c₀⁻¹‖ * (max C₄ 0 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * ∑' ξ, latG (F := F) blk A N₁ m t ξ) *
          (1 + ∏ i, t i) ^ N := by
        rw [e1, norm_mul]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT (norm_nonneg _)) hP0
    _ = ‖c₀⁻¹‖ * (max C₄ 0 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k) *
          ((∑' ξ, latG (F := F) blk A N₁ m t ξ) * (1 + ∏ i, t i) ^ N) := by ring
    _ ≤ ‖c₀⁻¹‖ * (max C₄ 0 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k) * (max C₅ 0 * (m : ℝ) ^ K) :=
        mul_le_mul_of_nonneg_left (hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (Nat.cast_nonneg _) _)))
          (mul_nonneg (norm_nonneg _) hB')
    _ ≤ ‖c₀⁻¹‖ * (max C₄ 0 * semK (Fin n × Fin d) (k * (K + 1)) f * (ht h : ℝ) ^ k) *
          (max C₅ 0 * (max C₄ 0 * (ht h : ℝ) ^ k) ^ K) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsemi hC4) hhk)
          (norm_nonneg _)) (mul_le_mul_of_nonneg_left hmK (le_max_right _ _))
          (mul_nonneg (le_max_right _ _) (pow_nonneg (Nat.cast_nonneg _) _))
        exact mul_nonneg (norm_nonneg _) (mul_nonneg (mul_nonneg hC4 (apply_nonneg _ _)) hhk)
    _ = ‖c₀⁻¹‖ * max C₄ 0 * max C₅ 0 * (max C₄ 0) ^ K * semK (Fin n × Fin d) (k * (K + 1)) f *
          (ht h : ℝ) ^ (k * (K + 1)) := by
        rw [mul_pow, ← pow_mul, show k * (K + 1) = k + k * K by ring, pow_add]; ring

end GlobalTheory.ThKTorus
end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_siegel_domain_decay : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∀ Cc : Set (UA σ X.J), IsCompact Cc → ∀ c : ℝ, 0 < c →
    ∀ φ ∈ SB (Fin n × Fin d → Af F), (∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ M.So B.ψ B.τ₁) →
    ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ (f : SInf F (Fin n × Fin d)) (t : Fin q → ℝ) (a κ : UA σ X.J) (h : UA σ W.J),
      (∀ i, c ≤ t i) → IsTorusU x y t a → κ ∈ Cc →
      ‖theta om (pureA F f φ) (a * κ) h‖ * (1 + ∏ i, t i) ^ N ≤ C * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k := by
  atlas_forward_decl GlobalTheory.ThKTorus.torusDecay
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegel_domain_reduction : GlobalTheory.Published.SiegelSetUnitary → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∃ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y ∧ ∃ (Cc : Set (UA σ X.J)) (c C : ℝ) (A : ℕ),
      IsCompact Cc ∧ 0 < c ∧ ∀ g : UA σ X.J, ∃ γ ∈ ratU σ X.J, ∃ (t : Fin q → ℝ) (a κ : UA σ X.J),
        (∀ i, c ≤ t i) ∧ IsTorusU x y t a ∧ κ ∈ Cc ∧ γ * g = a * κ ∧ (ht (a * κ) : ℝ) ≤ C * (1 + ∏ i, t i) ^ A := by
  first | exact @GlobalTheory.SiegelHt.siegel_reduction | exact GlobalTheory.SiegelHt.siegel_reduction | (intros; apply GlobalTheory.SiegelHt.siegel_reduction <;> assumption)
end

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay

namespace GlobalTheory.ThKSoSpan

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem one_le_ht {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : UA σ J) : (1 : ℝ) ≤ (ht h : ℝ) := by
  unfold ht
  exact_mod_cast one_le_heightGL F h.1

theorem soDecay_of_unif : GlobalTheory.FunPr.Hypotheses₂ → SoDecayUnif → SoDecay := by
  intro _ hU F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair Φ hΦ
  have hS := hPair.weil.isUSplitting
  obtain ⟨l, -, hlt⟩ := GlobalTheory.T.exists_admissibleForm_adelicThetaSum F (Fin n × Fin d)
  have hsch : M.So B.ψ B.τ₁ ≤ schA F (Fin n × Fin d) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, φ, h1, h2, -, rfl⟩
    have h3 := (h2.and hPair.good.std).mono fun w hw => hw.1.trans hw.2
    exact Submodule.subset_span ⟨f, _, ⟨isLocallyConstant_finprod_evalV φ h1 h3,
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ h1 h3⟩, rfl⟩
  have hlin : ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ g h, theta om Ψ g h = l (om (g, h) Ψ) :=
    fun Ψ hΨ g h => (hlt _ (hS.pres _ _ hΨ)).symm
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, h1, h2, h3, rfl⟩ := hx
    have hstd := (h2.and hPair.good.std).mono fun w hw => hw.1.trans hw.2
    have hφ : (fun y : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => evalV F v (y i)) ∈
        SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) :=
      ⟨isLocallyConstant_finprod_evalV φ h1 hstd, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ h1 hstd⟩
    have hall : ∀ f' : SInf F (Fin n × Fin d),
        pureA F f' (fun y : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => evalV F v (y i)) ∈
          M.So B.ψ B.τ₁ :=
      fun f' => Submodule.subset_span ⟨f', φ, h1, h2, h3, rfl⟩
    intro N
    obtain ⟨C, k, hC⟩ := hU F E σ B n d X W M χX χW om r s r' s' hPair _ hφ hall N
    exact ⟨C * semK (Fin n × Fin d) k f, k, fun g h => hC f g h⟩
  | zero =>
    intro N
    refine ⟨0, 0, fun g h => ?_⟩
    simp [theta, thetaSum]
  | add x y hx hy ihx ihy =>
    intro N
    obtain ⟨C1, k1, h1⟩ := ihx N
    obtain ⟨C2, k2, h2⟩ := ihy N
    refine ⟨max C1 0 + max C2 0, max k1 k2, fun g h => ?_⟩
    have e : theta om (x + y) g h = theta om x g h + theta om y g h := by
      rw [hlin _ (add_mem (hsch hx) (hsch hy)), hlin _ (hsch hx), hlin _ (hsch hy), map_add, map_add]
    have hh := one_le_ht h
    have hh0 : (0 : ℝ) ≤ (ht h : ℝ) := zero_le_one.trans hh
    have q0 : (0 : ℝ) ≤ (qht g : ℝ) ^ N := pow_nonneg (NNReal.coe_nonneg _) N
    have b1 : C1 * (ht h : ℝ) ^ k1 ≤ max C1 0 * (ht h : ℝ) ^ max k1 k2 :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hh0 _)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hh (le_max_left _ _)) (le_max_right _ _))
    have b2 : C2 * (ht h : ℝ) ^ k2 ≤ max C2 0 * (ht h : ℝ) ^ max k1 k2 :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hh0 _)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hh (le_max_right _ _)) (le_max_right _ _))
    calc ‖theta om (x + y) g h‖ * (qht g : ℝ) ^ N
        ≤ ‖theta om x g h‖ * (qht g : ℝ) ^ N + ‖theta om y g h‖ * (qht g : ℝ) ^ N := by
          rw [e, ← add_mul]
          exact mul_le_mul_of_nonneg_right (norm_add_le _ _) q0
      _ ≤ C1 * (ht h : ℝ) ^ k1 + C2 * (ht h : ℝ) ^ k2 := add_le_add (h1 g h) (h2 g h)
      _ ≤ max C1 0 * (ht h : ℝ) ^ max k1 k2 + max C2 0 * (ht h : ℝ) ^ max k1 k2 := add_le_add b1 b2
      _ = (max C1 0 + max C2 0) * (ht h : ℝ) ^ max k1 k2 := by ring
  | smul c x hx ihx =>
    intro N
    obtain ⟨C, k, h1⟩ := ihx N
    refine ⟨‖c‖ * C, k, fun g h => ?_⟩
    have e : theta om (c • x) g h = c * theta om x g h := by
      rw [hlin _ (Submodule.smul_mem _ c (hsch hx)), hlin _ (hsch hx), map_smul, map_smul, smul_eq_mul]
    rw [e, norm_mul, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h1 g h) (norm_nonneg c)

end GlobalTheory.ThKSoSpan
end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.soDecay_of_prints_of_soDecayUnif : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThKSoDecay.SoDecayUnif → GlobalTheory.ThK.SoDecay := by
  first | exact @GlobalTheory.ThKSoSpan.soDecay_of_unif | exact GlobalTheory.ThKSoSpan.soDecay_of_unif | (intros; apply GlobalTheory.ThKSoSpan.soDecay_of_unif <;> assumption)
end

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay

namespace GlobalTheory.ThKSoDecay

theorem soDecayUnif (hP : KP) : SoDecayUnif := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair φ hφ hφS N
  obtain ⟨q, x, y, hxy, Cc, c, C0, A, hCc, hc, hcov⟩ :=
    GlobalTheory.T.exists_siegel_domain_reduction hP.siegelSetUnitary F E σ B n X r s hPair.base hPair.herm
  obtain ⟨C1, k, hC1⟩ := GlobalTheory.T.schwartz_siegel_domain_decay hP F E σ B n d X W M χX χW om r s r' s' hPair q x y hxy Cc hCc c hc φ hφ hφS (A * N)
  have hB := GlobalTheory.T.theta_basic_properties hP.base F E σ B n d X W M χX χW om r s r' s' hPair
  refine ⟨max C0 0 ^ N * C1, k, fun f g h => ?_⟩
  obtain ⟨γ, hγ, t, a, κ, ht', ha, hκ, hg, hht⟩ := hcov g
  have hΦ : pureA F f φ ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  have e : theta om (pureA F f φ) g h = theta om (pureA F f φ) (a * κ) h := by
    rw [← hg]
    have := (hB.1 _ hΦ).2.1 γ hγ 1 (one_mem _) g h
    rw [one_mul] at this
    exact this.symm
  have hP0 : (0 : ℝ) ≤ 1 + ∏ i, t i :=
    add_nonneg zero_le_one (Finset.prod_nonneg fun i _ => hc.le.trans (ht' i))
  have hq : (qht g : ℝ) ≤ max C0 0 * (1 + ∏ i, t i) ^ A := by
    have h1 : qht g ≤ ht (a * κ) := by
      rw [← hg]
      exact ciInf_le (OrderBot.bddBelow _) (⟨γ, hγ⟩ : ratU σ X.J)
    exact (NNReal.coe_le_coe.2 h1).trans (hht.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hP0 A)))
  have hC0 : (0 : ℝ) ≤ max C0 0 := le_max_right _ _
  calc ‖theta om (pureA F f φ) g h‖ * (qht g : ℝ) ^ N
      ≤ ‖theta om (pureA F f φ) (a * κ) h‖ * (max C0 0 * (1 + ∏ i, t i) ^ A) ^ N := by
        rw [e]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) hq N) (norm_nonneg _)
    _ = max C0 0 ^ N * (‖theta om (pureA F f φ) (a * κ) h‖ * (1 + ∏ i, t i) ^ (A * N)) := by
        rw [mul_pow, pow_mul]; ring
    _ ≤ max C0 0 ^ N * (C1 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left (hC1 f t a κ h ht' ha hκ) (pow_nonneg hC0 N)
    _ = max C0 0 ^ N * C1 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k := by ring

theorem soDecay (hP : KP) : SoDecay := GlobalTheory.T.soDecay_of_prints_of_soDecayUnif hP.base (soDecayUnif hP)

end GlobalTheory.ThKSoDecay
end
end
