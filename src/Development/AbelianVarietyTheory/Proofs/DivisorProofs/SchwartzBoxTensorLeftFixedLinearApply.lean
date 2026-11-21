import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumLatticeStabilizerBigCellFactorizati
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixTrivialOffInertPlaceUnitaryAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicLatticeAtFinitePlaceIffInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeSelfDualEverywhere

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuumLatticeStabilizer_bigCell_factorization : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : Spc F E d) (v : Pl F), (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
    IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols d).det →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v,
      ((GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols d)⁻¹ *ᵥ z ∈
        GlobalTheory.InertSph.latAt W v) →
    ∃ p q : GlobalTheory.DblVac.UD σ W, p ∈ GlobalTheory.DblVac.KD σ W v ∧ p ∈ GlobalTheory.DblVac.PDiag σ W ∧
      q ∈ GlobalTheory.DblVac.KD σ W v ∧ q ∈ GlobalTheory.DblVac.PAnti σ W ∧ g = p * q := by
  first | exact @GlobalTheory.DblVacFactor.factor | exact GlobalTheory.DblVacFactor.factor | (intros; apply GlobalTheory.DblVacFactor.factor <;> assumption)
end

section
section
open scoped Matrix

namespace GlobalTheory

theorem lift_mod_maximal_skew : ∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ Z₀ : Matrix (Fin n) (Fin n) O, (∀ i j, (Z₀ᵀ * J + J * Z₀.map c) i j ∈ IsLocalRing.maximalIdeal O) →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ ∀ i j, Z i j - Z₀ i j ∈ IsLocalRing.maximalIdeal O := by
  intro O _ _ c hc h2 n J hJ hdet Z₀ hZ
  obtain ⟨u, hu⟩ : ∃ u : O, u * 2 = 1 := ⟨h2.unit⁻¹.val, h2.val_inv_mul⟩
  have hcu : c u = u := by
    have h1 : c u * 2 = 1 := by
      have := congrArg c hu
      simpa [map_mul, map_ofNat] using this
    calc c u = c u * (u * 2) := by rw [hu, mul_one]
      _ = (c u * 2) * u := by ring
      _ = u := by rw [h1, one_mul]
  set E := Z₀ᵀ * J + J * Z₀.map c with hE
  have hJc : (J.map c)ᵀ = J := by
    ext i j; simp [Matrix.transpose_apply, Matrix.map_apply, hJ]
  have hEc : (E.map c)ᵀ = E := by
    ext i j
    simp only [hE, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, map_add, map_sum, map_mul, hc, hJ]
    rw [add_comm]
    congr 1 <;> refine Finset.sum_congr rfl (fun k _ => ?_) <;> ring
  have hJinv : J * ((J⁻¹).map c)ᵀ = 1 := by
    calc J * ((J⁻¹).map c)ᵀ = (J.map c)ᵀ * ((J⁻¹).map c)ᵀ := by rw [hJc]
      _ = ((J⁻¹).map c * J.map c)ᵀ := by rw [Matrix.transpose_mul]
      _ = ((J⁻¹ * J).map c)ᵀ := by rw [Matrix.map_mul]
      _ = 1 := by rw [Matrix.nonsing_inv_mul J hdet, Matrix.map_one c c.map_zero c.map_one, Matrix.transpose_one]
  set D := (u • (E * J⁻¹))ᵀ with hD
  have hDT : Dᵀ * J = u • E := by
    rw [hD, Matrix.transpose_transpose, Matrix.smul_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul J hdet, Matrix.mul_one]
  have hDmap : D.map c = u • (((J⁻¹).map c)ᵀ * (E.map c)ᵀ) := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hD]
    ext i j
    simp [Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, map_sum, map_mul, hcu]
  have hDc : J * D.map c = u • E := by
    rw [hDmap, Matrix.mul_smul, ← Matrix.mul_assoc, hJinv, Matrix.one_mul, hEc]
  refine ⟨Z₀ - D, ?_, ?_⟩
  · have hmap : (Z₀ - D).map c = Z₀.map c - D.map c := by
      ext i j; simp [Matrix.map_apply]
    rw [Matrix.transpose_sub, Matrix.sub_mul, hmap, Matrix.mul_sub, hDT, hDc]
    have : E - u • E - u • E = 0 := by
      rw [sub_sub, ← add_smul, ← two_mul, mul_comm, hu, one_smul, sub_self]
    rw [← this, hE]; abel
  · intro i j
    have : (Z₀ - D) i j - Z₀ i j = -(u * ∑ k, E j k * J⁻¹ k i) := by
      simp [hD, Matrix.transpose_apply, Matrix.mul_apply, Matrix.smul_apply, mul_comm]
    rw [this]
    exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.sum_mem _ (fun k _ => Ideal.mul_mem_right _ _ (hZ j k))))

end GlobalTheory
end

open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_skew_lift_mod_maximalIdeal : ∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ Z₀ : Matrix (Fin n) (Fin n) O, (∀ i j, (Z₀ᵀ * J + J * Z₀.map c) i j ∈ IsLocalRing.maximalIdeal O) →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ ∀ i j, Z i j - Z₀ i j ∈ IsLocalRing.maximalIdeal O := by
  atlas_forward_decl GlobalTheory.lift_mod_maximal_skew
end

section
open scoped Matrix

namespace GlobalTheory

theorem rank_normal_form_field : ∀ (k : Type) [Field k] (n : ℕ) (C : Matrix (Fin n) (Fin n) k),
    ∃ (U P : Matrix (Fin n) (Fin n) k) (e : Fin n → k), U.det ≠ 0 ∧ P.det ≠ 0 ∧ (∀ i, e i = 0 ∨ e i = 1) ∧
      U * C * P = Matrix.diagonal e := by
  intro k _ n C
  classical
  obtain ⟨L, L', d, hd⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal C
  refine ⟨Matrix.diagonal (fun i => if d i = 0 then 1 else (d i)⁻¹) * (L.map Matrix.TransvectionStruct.toMatrix).prod,
    (L'.map Matrix.TransvectionStruct.toMatrix).prod, fun i => if d i = 0 then 0 else 1, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.TransvectionStruct.det_toMatrix_prod, mul_one, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    by_cases h : d i = 0 <;> simp [h]
  · rw [Matrix.TransvectionStruct.det_toMatrix_prod]; exact one_ne_zero
  · intro i; by_cases h : d i = 0 <;> simp [h]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ C, hd, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; by_cases h : d i = 0 <;> simp [h]

end GlobalTheory

alias _root_.GlobalTheory.T.exists_rank_normal_form_matrix_field := _root_.GlobalTheory.rank_normal_form_field
end

section
section
open scoped Matrix

namespace GlobalTheory

theorem skewHermitian_perturb_idempotent_det_ne_zero :
    ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → ∀ ε : k, ε ≠ 0 → σ ε = -ε →
    ∀ (n : ℕ) (E D : Matrix (Fin n) (Fin n) k), E * E = E → (E.map σ)ᵀ = E → E * (D.map σ)ᵀ + D * E = 0 →
    (∀ a : Fin n → k, a ᵥ* E = 0 → a ᵥ* D = 0 → a = 0) →
      ∃ V : Matrix (Fin n) (Fin n) k, (V.map σ)ᵀ = -V ∧ (E * V + D).det ≠ 0 := by
  intro k _ σ hσ ε hε hσε n E D hEE hEh hED hrank
  have h1 : E * (D.map σ)ᵀ = -(D * E) := eq_neg_of_add_eq_zero_left hED
  have h2 : E * (D.map σ)ᵀ = -(E * D * E) := by
    calc E * (D.map σ)ᵀ = E * (E * (D.map σ)ᵀ) := by rw [← Matrix.mul_assoc, hEE]
      _ = E * (-(D * E)) := by rw [h1]
      _ = -(E * D * E) := by rw [Matrix.mul_neg, Matrix.mul_assoc]
  have hDE : D * E = E * D * E := by
    have := h1.symm.trans h2
    exact neg_inj.mp this
  have h3 : E * (D.map σ)ᵀ * E = -(E * D * E) := by
    rw [h2, Matrix.neg_mul, Matrix.mul_assoc (E * D) E E, hEE]
  have hV : E * (ε • (1 : Matrix (Fin n) (Fin n) k) - D) * E = ε • E - E * D * E := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hEE]
  refine ⟨E * (ε • 1 - D) * E, ?_, ?_⟩
  · rw [hV]
    have hm : ((ε • E - E * D * E).map σ)ᵀ = (σ ε) • (E.map σ)ᵀ - (E.map σ)ᵀ * (D.map σ)ᵀ * (E.map σ)ᵀ := by
      ext i j
      have hs : ((ε • E).map σ)ᵀ = σ ε • (E.map σ)ᵀ := by
        ext i j
        simp
      rw [Matrix.map_sub _ (map_sub σ), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_sub, Matrix.transpose_mul,
        Matrix.transpose_mul, ← Matrix.mul_assoc, hs]
    rw [hm, hEh, h3, hσε, neg_smul, sub_neg_eq_add, neg_sub]
    abel
  · have hM : E * (E * (ε • 1 - D) * E) + D = ε • E - E * D * E + D := by
      rw [hV, Matrix.mul_sub, Matrix.mul_smul, hEE, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hEE]
    rw [hM]
    have hME : (ε • E - E * D * E + D) * E = ε • E := by
      rw [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, hEE, Matrix.mul_assoc (E * D) E E, hEE, hDE]
      abel
    intro hdet
    obtain ⟨a, ha0, ha⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
    have haE : a ᵥ* E = 0 := by
      have : a ᵥ* ((ε • E - E * D * E + D) * E) = 0 := by rw [← Matrix.vecMul_vecMul, ha, Matrix.zero_vecMul]
      rw [hME, Matrix.vecMul_smul] at this
      exact (smul_eq_zero.mp this).resolve_left hε
    have haD : a ᵥ* D = 0 := by
      have hx : a ᵥ* (E * D * E) = 0 := by
        rw [Matrix.mul_assoc, ← Matrix.vecMul_vecMul, haE, Matrix.zero_vecMul]
      rw [Matrix.vecMul_add, Matrix.vecMul_sub, Matrix.vecMul_smul, haE, hx] at ha
      simpa using ha
    exact ha0 (hrank a haE haD)

end GlobalTheory
end

open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_skewHermitian_det_mul_add_ne_zero_of_idempotent : ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → ∀ ε : k, ε ≠ 0 → σ ε = -ε →
    ∀ (n : ℕ) (E D : Matrix (Fin n) (Fin n) k), E * E = E → (E.map σ)ᵀ = E → E * (D.map σ)ᵀ + D * E = 0 →
    (∀ a : Fin n → k, a ᵥ* E = 0 → a ᵥ* D = 0 → a = 0) →
      ∃ V : Matrix (Fin n) (Fin n) k, (V.map σ)ᵀ = -V ∧ (E * V + D).det ≠ 0 := by
  atlas_forward_decl GlobalTheory.skewHermitian_perturb_idempotent_det_ne_zero
end

section
section
open scoped Matrix

namespace GlobalTheory

theorem exists_skewHermitian_mul_add_det_ne_zero_of_pair :
    ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → ∀ ε : k, ε ≠ 0 → σ ε = -ε →
    ∀ (n : ℕ) (C D : Matrix (Fin n) (Fin n) k), C * (D.map σ)ᵀ + D * (C.map σ)ᵀ = 0 →
    (∀ a : Fin n → k, a ᵥ* C = 0 → a ᵥ* D = 0 → a = 0) →
      ∃ V : Matrix (Fin n) (Fin n) k, (V.map σ)ᵀ = -V ∧ (C * V + D).det ≠ 0 := by
  intro k _ σ hσ ε hε hσε n C D hCD hrk
  obtain ⟨U, P, e, hU, hP, he, hE⟩ := GlobalTheory.T.exists_rank_normal_form_matrix_field k n C
  have hmul : ∀ A B : Matrix (Fin n) (Fin n) k,
      ((A * B).map σ)ᵀ = (B.map σ)ᵀ * (A.map σ)ᵀ := by
    intro A B
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have hinv : ∀ A : Matrix (Fin n) (Fin n) k, (((A.map σ)ᵀ).map σ)ᵀ = A := by
    intro A
    ext i j
    simp [hσ]
  have hone : (((1 : Matrix (Fin n) (Fin n) k).map σ)ᵀ) = 1 := by
    rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  have hUu : IsUnit U.det := isUnit_iff_ne_zero.mpr hU
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPu
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPu
  have h3 : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hUu
  set E : Matrix (Fin n) (Fin n) k := Matrix.diagonal e with hEdef
  have hEE : E * E = E := by
    rw [hEdef, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rcases he i with h | h <;> simp [h]
  have hEs : (E.map σ)ᵀ = E := by
    rw [hEdef, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose]
    congr 1
    funext i
    rcases he i with h | h <;> simp [h]
  set Q : Matrix (Fin n) (Fin n) k := (P⁻¹.map σ)ᵀ with hQ
  set Ps : Matrix (Fin n) (Fin n) k := (P.map σ)ᵀ with hPs
  have hPQ : Ps * Q = 1 := by rw [hPs, hQ, ← hmul, h2, hone]
  have hQP : Q * Ps = 1 := by rw [hPs, hQ, ← hmul, h1, hone]
  have hQs : (Q.map σ)ᵀ = P⁻¹ := hinv _
  have hE' : E = Ps * ((C.map σ)ᵀ * (U.map σ)ᵀ) := by
    rw [← hEs, ← hE, hmul, hmul]
  have hA : E * ((U * D * Q).map σ)ᵀ = U * (C * (D.map σ)ᵀ) * (U.map σ)ᵀ := by
    rw [hmul, hmul, hQs, ← hE]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P, h1, Matrix.one_mul]
  have hB : U * D * Q * E = U * (D * (C.map σ)ᵀ) * (U.map σ)ᵀ := by
    rw [hE']
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q, hQP, Matrix.one_mul]
  have hsum : E * ((U * D * Q).map σ)ᵀ + U * D * Q * E = 0 := by
    rw [hA, hB, ← Matrix.add_mul, ← Matrix.mul_add, hCD, Matrix.mul_zero, Matrix.zero_mul]
  have hrk' : ∀ a : Fin n → k, a ᵥ* E = 0 → a ᵥ* (U * D * Q) = 0 → a = 0 := by
    intro a ha hb
    have e1 : U * C = E * P⁻¹ := by
      rw [← hE, Matrix.mul_assoc, h1, Matrix.mul_one]
    have e2 : U * D = (U * D * Q) * Ps := by
      rw [Matrix.mul_assoc, hQP, Matrix.mul_one]
    have h0 : a ᵥ* U = 0 := by
      apply hrk
      · rw [Matrix.vecMul_vecMul, e1, ← Matrix.vecMul_vecMul, ha, Matrix.zero_vecMul]
      · rw [Matrix.vecMul_vecMul, e2, ← Matrix.vecMul_vecMul, hb, Matrix.zero_vecMul]
    have : a ᵥ* (U * U⁻¹) = 0 := by
      rw [← Matrix.vecMul_vecMul, h0, Matrix.zero_vecMul]
    rwa [h3, Matrix.vecMul_one] at this
  obtain ⟨V', hV', hdet⟩ := GlobalTheory.T.exists_skewHermitian_det_mul_add_ne_zero_of_idempotent k σ hσ ε hε hσε n E (U * D * Q) hEE hEs hsum hrk'
  refine ⟨P * V' * Ps, ?_, ?_⟩
  · have hPss : (Ps.map σ)ᵀ = P := hinv _
    rw [hmul, hmul, hV', hPss, ← hPs]
    simp [Matrix.mul_assoc]
  · intro h
    apply hdet
    have : E * V' + U * D * Q = U * (C * (P * V' * Ps) + D) * Q := by
      rw [← hE, Matrix.mul_add, Matrix.add_mul]
      simp only [Matrix.mul_assoc]
      rw [hPQ, Matrix.mul_one]
    rw [this, Matrix.det_mul, Matrix.det_mul, h, mul_zero, zero_mul]

end GlobalTheory
end

open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_skewHermitian_mul_add_det_ne_zero : ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → ∀ ε : k, ε ≠ 0 → σ ε = -ε →
    ∀ (n : ℕ) (C D : Matrix (Fin n) (Fin n) k), C * (D.map σ)ᵀ + D * (C.map σ)ᵀ = 0 →
    (∀ a : Fin n → k, a ᵥ* C = 0 → a ᵥ* D = 0 → a = 0) →
      ∃ V : Matrix (Fin n) (Fin n) k, (V.map σ)ᵀ = -V ∧ (C * V + D).det ≠ 0 := by
  atlas_forward_decl GlobalTheory.exists_skewHermitian_mul_add_det_ne_zero_of_pair
end

section
section
open scoped Matrix

namespace GlobalTheory

theorem exists_isotropic_graph_det_lowerRow_ne_zero_field :
    ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → (∃ ε : k, ε ≠ 0 ∧ σ ε = -ε) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) k), (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k, g.det ≠ 0 →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map σ = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) k, Zᵀ * J + J * Z.map σ = 0 ∧
        (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det ≠ 0 := by
  intro k _ σ hσ hε n J hJ hJd g hg hQ
  obtain ⟨ε, hε0, hε⟩ := hε
  have hmm : ∀ A : Matrix (Fin n) (Fin n) k, (A.map σ).map σ = A := by
    intro A; ext i j; simp [hσ]
  have hJu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJd
  set K : Matrix (Fin n) (Fin n) k := J⁻¹ with hK
  have hJK : J * K = 1 := Matrix.mul_nonsing_inv J hJu
  have hKJ : K * J = 1 := Matrix.nonsing_inv_mul J hJu
  have hJh : (J.map σ)ᵀ = J := by ext i j; simp [hJ]
  have hKh : (K.map σ)ᵀ = K := by
    have h1 : (K.map σ)ᵀ * J = 1 := by
      conv_lhs => rw [← hJh]
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hJK]
      simp
    calc (K.map σ)ᵀ = (K.map σ)ᵀ * (J * K) := by rw [hJK, Matrix.mul_one]
      _ = K := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hKt : Kᵀ = K.map σ := by
    conv_lhs => rw [← hKh]
    simp
  have hQR : Matrix.fromBlocks 0 K K 0 * Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) k) J J 0
      = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) := by
    rw [Matrix.fromBlocks_multiply]
    simp [hKJ]
  have hRQ : Matrix.fromBlocks 0 J J 0 * Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) k) K K 0
      = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) := mul_eq_one_comm.mp hQR
  have h2 : (Matrix.fromBlocks 0 K K 0 * gᵀ * Matrix.fromBlocks 0 J J 0) * g.map σ = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᵀ, hQ, hQR]
  have h3 := mul_eq_one_comm.mp h2
  have h4 : g.map σ * Matrix.fromBlocks 0 K K 0 * gᵀ = Matrix.fromBlocks 0 K K 0 := by
    calc g.map σ * Matrix.fromBlocks 0 K K 0 * gᵀ
        = g.map σ * Matrix.fromBlocks 0 K K 0 * gᵀ *
          (Matrix.fromBlocks 0 J J 0 * Matrix.fromBlocks 0 K K 0) := by rw [hRQ, Matrix.mul_one]
      _ = (g.map σ * (Matrix.fromBlocks 0 K K 0 * gᵀ * Matrix.fromBlocks 0 J J 0)) *
          Matrix.fromBlocks 0 K K 0 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h3, Matrix.one_mul]
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, g = Matrix.fromBlocks A B C D :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks g).symm⟩
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at h4
  have h5 := h4.2.2.2
  simp only [Matrix.mul_zero, zero_add, add_zero] at h5
  have h6 : D * K.map σ * (C.map σ)ᵀ + C * K.map σ * (D.map σ)ᵀ = 0 := by
    have := congrArg (fun M : Matrix (Fin n) (Fin n) k => M.map σ) h5
    simp only [Matrix.map_add σ (map_add σ), Matrix.map_mul, hmm, Matrix.map_zero σ (map_zero σ)] at this
    simpa [Matrix.transpose_map] using this
  have hJσ : K.map σ * J.map σ = 1 := by
    rw [← Matrix.map_mul, hKJ]; simp
  obtain ⟨V, hV, hdet⟩ := GlobalTheory.T.exists_skewHermitian_mul_add_det_ne_zero k σ hσ ε hε0 hε n (C * K.map σ) D
    (by
      rw [Matrix.map_mul, hmm, Matrix.transpose_mul, hKt, ← Matrix.mul_assoc, add_comm]
      exact h6)
    (by
      intro a ha hD
      have hC : a ᵥ* C = 0 := by
        have : a ᵥ* (C * K.map σ * J.map σ) = 0 := by
          rw [← Matrix.vecMul_vecMul, ha, Matrix.zero_vecMul]
        rwa [Matrix.mul_assoc, hJσ, Matrix.mul_one] at this
      have h7 : (Sum.elim 0 a) ᵥ* Matrix.fromBlocks A B C D = 0 := by
        rw [Matrix.vecMul_fromBlocks]
        simp [hC, hD]
      have h8 := Matrix.eq_zero_of_vecMul_eq_zero hg h7
      funext i
      exact congrFun h8 (Sum.inr i))
  refine ⟨K.map σ * V, ?_, ?_⟩
  · rw [Matrix.transpose_mul, hKh, Matrix.mul_assoc, hKJ, Matrix.mul_one, Matrix.map_mul, hmm,
      ← Matrix.mul_assoc, hJK, Matrix.one_mul]
    have : V.map σ = -Vᵀ := by
      rw [← Matrix.transpose_neg, ← hV, Matrix.transpose_transpose]
    rw [this, add_neg_cancel]
  · simpa [Matrix.mul_assoc] using hdet

end GlobalTheory
end

open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_graph_det_ne_zero : ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → (∃ ε : k, ε ≠ 0 ∧ σ ε = -ε) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) k), (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k, g.det ≠ 0 →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map σ = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) k, Zᵀ * J + J * Z.map σ = 0 ∧ (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det ≠ 0 := by
  atlas_forward_decl GlobalTheory.exists_isotropic_graph_det_lowerRow_ne_zero_field
end

section
section
open scoped Matrix

namespace GlobalTheory

theorem exists_isotropic_graph_isUnit_lowerRow : ∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    (∃ x : O, IsUnit (c x - x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det := by
  have hfield := GlobalTheory.T.exists_isotropic_graph_det_ne_zero
  have hlift := GlobalTheory.T.exists_skew_lift_mod_maximalIdeal

  intro O _ _ c hc h2 hx0 n J hJ hJdet g hg hgu
  obtain ⟨x, hx⟩ := hx0
  haveI : IsLocalHom c := ⟨fun a ha => by simpa [hc] using ha.map c⟩
  set π := IsLocalRing.residue O with hπ
  set σ : IsLocalRing.ResidueField O →+* IsLocalRing.ResidueField O := IsLocalRing.ResidueField.map c with hσ
  have hσπ : ∀ a, σ (π a) = π (c a) := fun a => IsLocalRing.ResidueField.map_residue c a
  have hσσ : ∀ y, σ (σ y) = y := by
    intro y; obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y; rw [hσπ, hσπ, hc]
  have hε : ∃ ε, ε ≠ 0 ∧ σ ε = -ε := ⟨π (c x - x), (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hx, by
    rw [hσπ, map_sub, hc, ← neg_sub, map_neg]⟩
  have hmapc : ∀ {m : Type} (M : Matrix m m O), (M.map c).map π = (M.map π).map σ := by
    intro m M; ext i j; simp [hσπ]
  have hJ' : ∀ i j, σ (J.map π j i) = J.map π i j := by intro i j; simp [hσπ, hJ]
  have hJdet' : (J.map π).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hJdet
  have hg' : (g.map π).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hg
  have hgu' : (g.map π)ᵀ * Matrix.fromBlocks 0 (J.map π) (J.map π) 0 * (g.map π).map σ
      = Matrix.fromBlocks 0 (J.map π) (J.map π) 0 := by
    have := congrArg (fun M => M.map π) hgu
    simpa only [Matrix.map_mul, Matrix.transpose_map, hmapc, Matrix.fromBlocks_map,
      Matrix.map_zero _ (map_zero π)] using this
  obtain ⟨Zb, hZb, hdet⟩ := hfield _ σ hσσ hε n _ hJ' hJdet' _ hg' hgu'
  obtain ⟨Z₀, hZ₀⟩ : ∃ Z₀ : Matrix (Fin n) (Fin n) O, Z₀.map π = Zb :=
    ⟨fun i j => (IsLocalRing.residue_surjective (Zb i j)).choose, by
      ext i j; exact (IsLocalRing.residue_surjective (Zb i j)).choose_spec⟩
  have hZ₀m : ∀ i j, (Z₀ᵀ * J + J * Z₀.map c) i j ∈ IsLocalRing.maximalIdeal O := by
    intro i j
    rw [← IsLocalRing.residue_eq_zero_iff]
    have := congrArg (fun M => M i j) hZb
    simp only [Matrix.zero_apply] at this
    rw [← this, ← hZ₀, ← hmapc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add π)]
    rfl
  obtain ⟨Z, hZ, hZm⟩ := hlift O c hc h2 n J hJ hJdet Z₀ hZ₀m
  refine ⟨Z, hZ, ?_⟩
  have hZπ : Z.map π = Zb := by
    rw [← hZ₀]; ext i j
    simp only [Matrix.map_apply]
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hZm i j
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← hπ, RingHom.map_det, RingHom.mapMatrix_apply,
    Matrix.map_add _ (map_add π), Matrix.map_mul, hZπ]
  exact hdet

end GlobalTheory
end

open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_graph_unitary_isUnit_lowerBlock : ∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    (∃ x : O, IsUnit (c x - x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det := by
  atlas_forward_decl GlobalTheory.exists_isotropic_graph_isUnit_lowerRow
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocDict

open GlobalTheory.InertBigCell

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)}

theorem isConjAt_conjW (σ : E →ₐ[F] E) (hw : Formalism.UG.IsInertAt F E v w) :
    IsConjAt σ (under_eq_of_isInertAt hw) (conjW σ hw) := fun y => by
  show toCompl _ (sigR (Fv F v) σ ((InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm (toCompl _ y))) = _
  congr 2
  exact (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm_apply_apply y

theorem conjW_conjW (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (hw : Formalism.UG.IsInertAt F E v w)
    (x : w.adicCompletion E) : conjW σ hw (conjW σ hw x) = x := by
  obtain ⟨y, rfl⟩ := InertChart.toCompl_surjective (under_eq_of_isInertAt hw) x
  rw [isConjAt_conjW σ hw, isConjAt_conjW σ hw]
  congr 1
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem iotaW_mulVec (hw : Formalism.UG.IsInertAt F E v w) {l m : Type} [Fintype m]
    (M : Matrix l m (w.adicCompletion E)) (y : m → w.adicCompletion E) :
    (fun i => iotaW hw ((M *ᵥ y) i)) = M.map (iotaW hw) *ᵥ fun i => iotaW hw (y i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, iotaW_mul]

theorem map_iotaW_mul (hw : Formalism.UG.IsInertAt F E v w) {l m p : Type} [Fintype m]
    (M : Matrix l m (w.adicCompletion E)) (N : Matrix m p (w.adicCompletion E)) :
    M.map (iotaW hw) * N.map (iotaW hw) = (M * N).map (iotaW hw) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, iotaW_mul]

theorem one_map_iotaW (hw : Formalism.UG.IsInertAt F E v w) (n : ℕ) :
    (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map (iotaW hw) =
      iotaW hw 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem herm_gram {R : Type} [CommRing R] (τ : R →+* R) (hτ : ∀ x, τ (τ x) = x) {n : ℕ}
    (A M : Matrix (Fin n) (Fin n) R) (hM : ∀ i j, τ (M i j) = M j i) (i j : Fin n) :
    τ ((Formalism.UG.cT τ A * M * A) i j) = (Formalism.UG.cT τ A * M * A) j i := by
  simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hτ, hM,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem isUnit_of_val_eq_one {t : Formalism.UG.Ov E w} (ht : Valued.v (t : w.adicCompletion E) = 1) : IsUnit t := by
  have h0 : (t : w.adicCompletion E) ≠ 0 := fun h0 => by rw [h0, map_zero] at ht; exact zero_ne_one ht
  have hm : (t : w.adicCompletion E)⁻¹ ∈ Formalism.UG.Ov E w := by
    show _ ∈ w.adicCompletionIntegers E
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, ht, inv_one]
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hm⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

end GlobalTheory.InertLocDict

namespace GlobalTheory.InertLocDict

open GlobalTheory.InertBigCell

theorem exists_local_dictionary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∃ (O : Type) (_ : CommRing O) (c : O →+* O) (ι : O →ₙ+* AE F E) (P Q : Matrix (Fin n) (Fin n) (AE F E))
      (JL : Matrix (Fin n) (Fin n) O),
      IsLocalRing O ∧ (∀ x, c (c x) = x) ∧ IsUnit (2 : O) ∧ (∃ x : O, IsUnit (c x - x)) ∧
      Function.Injective ι ∧ At (evFin F v) (ι 1) ∧ (∀ y : AE F E, At (evFin F v) y → ι 1 * y = y) ∧
      (∀ x, cA σ (ι x) = ι (c x)) ∧
      P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧ Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧
      ι 1 • P = P ∧ ι 1 • Q = Q ∧
      (∀ i j, c (JL j i) = JL i j) ∧ IsUnit JL.det ∧ Pᵀ * incM F X.J * P.map (cA σ) = JL.map ι ∧
      ∀ z : Fin n → AE F E, z ∈ GlobalTheory.InertSph.latAt X v ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i) := by
  intro F E _ _ _ _ _ σ B n r s X hB hX v w hw
  have h := under_eq_of_isInertAt hw
  have hc : IsConjAt σ h (conjW σ hw) := isConjAt_conjW σ hw
  have hσ : ∀ x, σ (σ x) = x := InertChart.conj_conj hB.cm
  haveI : IsLocalRing (Formalism.UG.Ov E w) := inferInstanceAs (IsLocalRing (w.adicCompletionIntegers E))
  let c : Formalism.UG.Ov E w →+* Formalism.UG.Ov E w :=
    ((conjW σ hw).comp (Formalism.UG.Ov E w).subtype).codRestrict (Formalism.UG.Ov E w)
      (fun x => InertChart.conj_mem hw hc x.2)
  let ι : Formalism.UG.Ov E w →ₙ+* AE F E :=
    { toFun := fun x => iotaW hw (x : w.adicCompletion E)
      map_mul' := fun x y => iotaW_mul hw _ _
      map_zero' := map_zero _
      map_add' := fun x y => map_add _ _ _ }
  have hι : ∀ x, ι x = iotaW hw (x : w.adicCompletion E) := fun _ => rfl
  have hι1 : ι 1 = iotaW hw 1 := rfl
  have hcv : ∀ x, ((c x : Formalism.UG.Ov E w) : w.adicCompletion E) = conjW σ hw x := fun _ => rfl
  obtain ⟨a, ha⟩ := InertChart.exists_isFrameAt (L := X.L) hw hX.lat.fg hX.lat.span_eq_top
  have hJ : (X.Jᵀ).det ≠ 0 := by
    rw [Matrix.det_transpose]; exact GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm σ B hX
  obtain ⟨Bm, ⟨k, hk⟩, eB⟩ := InertChart.exists_gram hw hc hJ
    (GlobalTheory.HermSelfDualLoc.isSelfDualAt_transpose F E σ B n X r s hB hX v) ha
  have hkij : ∀ i j, ((k.1 i j : Formalism.UG.Ov E w) : w.adicCompletion E) = Bm.1 i j := fun i j => by
    rw [← hk]; rfl
  have hBt : Bm.1ᵀ = a.1ᵀ * X.J.map (algebraMap E (w.adicCompletion E)) * a.1.map (conjW σ hw) := by
    rw [eB, Matrix.transpose_mul, Matrix.transpose_mul, Formalism.UG.cT, Matrix.transpose_transpose, Matrix.transpose_map,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  refine ⟨Formalism.UG.Ov E w, inferInstance, c, ι, a.1.map (iotaW hw), (a⁻¹).1.map (iotaW hw), k.1ᵀ, inferInstance,
    fun x => Subtype.ext (conjW_conjW σ hσ hw x), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have h2 : (2 : w.adicCompletion E) ≠ 0 := by
      rw [← map_ofNat (algebraMap E (w.adicCompletion E)) 2]
      exact (map_ne_zero _).2 two_ne_zero
    have hm : (2 : w.adicCompletion E)⁻¹ ∈ Formalism.UG.Ov E w := by
      have := complMap_mem h (GlobalTheory.InertLocField.half_mem v (hB.inert v w hw).1)
      rwa [complMap_algebraMap, map_inv₀, map_inv₀, map_ofNat, map_ofNat] at this
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hm⟩, Subtype.ext (mul_inv_cancel₀ h2)⟩
  ·
    obtain ⟨x, hx⟩ := InertChart.exists_conj_sub_unit hB.cm hw
    have hval : ∀ a : E, Valued.v (algebraMap E (w.adicCompletion E) a) = w.valuation E a := fun a =>
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    have hxm : algebraMap E (w.adicCompletion E) (x : E) ∈ Formalism.UG.Ov E w := by
      show _ ∈ w.adicCompletionIntegers E
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval]; exact w.valuation_le_one x
    refine ⟨⟨_, hxm⟩, ?_⟩
    refine isUnit_of_val_eq_one ?_
    show Valued.v (conjW σ hw (algebraMap E _ (x : E)) - algebraMap E _ (x : E)) = 1
    rw [InertChart.conj_algebraMap hc, ← map_sub, hval, hx]
  · exact fun x y hxy => Subtype.ext (iotaW_injective hw hxy)
  · rw [hι1, iotaW_apply]; exact GlobalTheory.InertLocField.at_liftT v _
  · intro y hy
    have h1 := hy _ (GlobalTheory.InertLocField.evFin_one_sub v)
    rw [sub_smul, one_smul, sub_eq_zero] at h1
    rw [hι1, iotaW_one, ← Algebra.smul_def]
    exact h1.symm
  · intro x
    rw [hι, hι, hcv, iotaW_conjW]
  · rw [map_iotaW_mul, Units.mul_inv, one_map_iotaW, hι1]
  · rw [map_iotaW_mul, Units.inv_mul, one_map_iotaW, hι1]
  · ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, hι1, ← iotaW_mul, one_mul]
  · ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, hι1, ← iotaW_mul, one_mul]
  · intro i j
    apply Subtype.ext
    rw [hcv, Matrix.transpose_apply, Matrix.transpose_apply, hkij, hkij, eB]
    refine herm_gram (conjW σ hw) (conjW_conjW σ hσ hw) a.1 (X.Jᵀ.map (algebraMap E (w.adicCompletion E)))
      (fun p q => ?_) i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, InertChart.conj_algebraMap hc, hX.herm]
  · rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).1 k.isUnit
  · have e1 : (a.1.map (iotaW hw))ᵀ = (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • (0 : Matrix (Fin n) (Fin n) (AE F E)) +
        a.1ᵀ.map (iotaW hw) := by
      rw [smul_zero, zero_add, Matrix.transpose_map]
    have e2 : (a.1.map (iotaW hw)).map (cA σ) = (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • (0 : Matrix (Fin n) (Fin n) (AE F E)) +
        (a.1.map (conjW σ hw)).map (iotaW hw) := by
      rw [smul_zero, zero_add]
      ext i j
      simp only [Matrix.map_apply, iotaW_conjW]
    rw [e1, e2, incM_split hw X.J,
      idem_split_mul _ (iotaW hw) (one_sub_idem v) (one_sub_mul_iotaW hw) (iotaW_mul hw),
      idem_split_mul _ (iotaW hw) (one_sub_idem v) (one_sub_mul_iotaW hw) (iotaW_mul hw),
      Matrix.zero_mul, Matrix.zero_mul, smul_zero, zero_add, ← hBt]
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, hι, hkij]
  · intro z
    rw [GlobalTheory.InertSphLat.mem_latAt_iff hw X z]
    constructor
    · rintro ⟨u, hu, rfl⟩
      have e : a.1 *ᵥ ((a⁻¹).1 *ᵥ u) = u := by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      have hint := (ha ((a⁻¹).1 *ᵥ u)).2 (by rw [e]; exact hu)
      refine ⟨fun i => ⟨_, hint i⟩, ?_⟩
      show (fun i => iotaW hw (u i)) = a.1.map (iotaW hw) *ᵥ fun i => iotaW hw (((a⁻¹).1 *ᵥ u) i)
      rw [← iotaW_mulVec, e]
    · rintro ⟨b, rfl⟩
      refine ⟨a.1 *ᵥ fun i => (b i : w.adicCompletion E), (ha _).1 fun i => (b i).2, ?_⟩
      rw [iotaW_mulVec]
      rfl

end GlobalTheory.InertLocDict
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_dictionary_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∃ (O : Type) (_ : CommRing O) (c : O →+* O) (ι : O →ₙ+* AE F E) (P Q : Matrix (Fin n) (Fin n) (AE F E))
      (JL : Matrix (Fin n) (Fin n) O),
      IsLocalRing O ∧ (∀ x, c (c x) = x) ∧ IsUnit (2 : O) ∧ (∃ x : O, IsUnit (c x - x)) ∧
      Function.Injective ι ∧ At (evFin F v) (ι 1) ∧ (∀ y : AE F E, At (evFin F v) y → ι 1 * y = y) ∧
      (∀ x, cA σ (ι x) = ι (c x)) ∧
      P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧ Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧
      ι 1 • P = P ∧ ι 1 • Q = Q ∧
      (∀ i j, c (JL j i) = JL i j) ∧ IsUnit JL.det ∧ Pᵀ * incM F X.J * P.map (cA σ) = JL.map ι ∧
      ∀ z : Fin n → AE F E, z ∈ GlobalTheory.InertSph.latAt X v ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i) := by
  atlas_forward_decl GlobalTheory.InertLocDict.exists_local_dictionary
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.LatticeStab

variable {A O : Type} [CommRing A] [CommRing O] (ι : O →ₙ+* A) {n : ℕ}

theorem map_mul_of_nonUnital {m : Type} [Fintype m] (G H : Matrix m m O) :
    (G * H).map ι = G.map ι * H.map ι := by
  ext i j
  simp [Matrix.mul_apply, map_sum, map_mul]

theorem exists_matrix_of_keeps (P : Matrix (Fin n) (Fin n) A) (Λ : Set (Fin n → A))
    (hP : ι 1 • P = P)
    (hΛ : ∀ z, z ∈ Λ ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i))
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A)
    (hM : ∀ z : Fin n ⊕ Fin n → A, z ∘ Sum.inl ∈ Λ → z ∘ Sum.inr ∈ Λ →
      (M *ᵥ z) ∘ Sum.inl ∈ Λ ∧ (M *ᵥ z) ∘ Sum.inr ∈ Λ) :
    ∃ G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O,
      M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι := by
  have h0 : (0 : Fin n → A) ∈ Λ :=
    (hΛ 0).2 ⟨0, by ext i; simp [Matrix.mulVec, dotProduct]⟩
  have hcol : ∀ k : Fin n, (fun r => P r k) ∈ Λ := by
    intro k
    refine (hΛ _).2 ⟨Pi.single k 1, ?_⟩
    ext r
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single k]
    · have := congrFun (congrFun hP r) k
      simp only [Matrix.smul_apply, smul_eq_mul] at this
      simp only [Pi.single_eq_same]
      rw [mul_comm]; exact this.symm
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · simp
  have hDcol : ∀ j, (fun k => Matrix.fromBlocks P 0 0 P k j) ∘ Sum.inl ∈ Λ ∧
      (fun k => Matrix.fromBlocks P 0 0 P k j) ∘ Sum.inr ∈ Λ := by
    intro j
    rcases j with k | k
    · have e1 : (fun k' => Matrix.fromBlocks P 0 0 P k' (Sum.inl k)) ∘ Sum.inl = fun r => P r k := by
        ext r; simp
      have e2 : (fun k' => Matrix.fromBlocks P 0 0 P k' (Sum.inl k)) ∘ Sum.inr = 0 := by
        ext r; simp
      rw [e1, e2]; exact ⟨hcol k, h0⟩
    · have e1 : (fun k' => Matrix.fromBlocks P 0 0 P k' (Sum.inr k)) ∘ Sum.inl = 0 := by
        ext r; simp
      have e2 : (fun k' => Matrix.fromBlocks P 0 0 P k' (Sum.inr k)) ∘ Sum.inr = fun r => P r k := by
        ext r; simp
      rw [e1, e2]; exact ⟨h0, hcol k⟩
  have ex : ∀ j, ∃ a b : Fin n → O,
      (M *ᵥ fun k => Matrix.fromBlocks P 0 0 P k j) ∘ Sum.inl = P *ᵥ (fun i => ι (a i)) ∧
      (M *ᵥ fun k => Matrix.fromBlocks P 0 0 P k j) ∘ Sum.inr = P *ᵥ (fun i => ι (b i)) := by
    intro j
    obtain ⟨h1, h2⟩ := hM _ (hDcol j).1 (hDcol j).2
    obtain ⟨a, ha⟩ := (hΛ _).1 h1
    obtain ⟨b, hb⟩ := (hΛ _).1 h2
    exact ⟨a, b, ha, hb⟩
  choose a b hab using ex
  refine ⟨Matrix.of fun i j => Sum.elim (a j) (b j) i, ?_⟩
  ext i j
  have hMD : (M * Matrix.fromBlocks P 0 0 P) i j = (M *ᵥ fun k => Matrix.fromBlocks P 0 0 P k j) i := rfl
  rw [hMD]
  rcases i with r | r
  · have := congrFun (hab j).1 r
    simp only [Function.comp] at this
    rw [this]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  · have := congrFun (hab j).2 r
    simp only [Function.comp] at this
    rw [this]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

end GlobalTheory.LatticeStab

theorem GlobalTheory.LatticeStab.matrix_in_diag_basis : ∀ (A O : Type) [CommRing A] [CommRing O] (ι : O →ₙ+* A) (n : ℕ) (P Q : Matrix (Fin n) (Fin n) A)
    (Λ : Set (Fin n → A)), Function.Injective ι → P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) A) →
    Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) A) → ι 1 • P = P → ι 1 • Q = Q →
    (∀ z, z ∈ Λ ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i)) →
    ∀ M M' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A, M * M' = 1 →
    (∀ z : Fin n ⊕ Fin n → A, z ∘ Sum.inl ∈ Λ → z ∘ Sum.inr ∈ Λ →
      (M *ᵥ z) ∘ Sum.inl ∈ Λ ∧ (M *ᵥ z) ∘ Sum.inr ∈ Λ ∧ (M' *ᵥ z) ∘ Sum.inl ∈ Λ ∧ (M' *ᵥ z) ∘ Sum.inr ∈ Λ) →
    ∃ G G' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, G * G' = 1 ∧
      M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι := by
  intro A O _ _ ι n P Q Λ hinj _hPQ hQP hP _hQ hΛ M M' hMM' hM
  obtain ⟨G, hG⟩ := GlobalTheory.LatticeStab.exists_matrix_of_keeps ι P Λ hP hΛ M
    (fun z h1 h2 => ⟨(hM z h1 h2).1, (hM z h1 h2).2.1⟩)
  obtain ⟨G', hG'⟩ := GlobalTheory.LatticeStab.exists_matrix_of_keeps ι P Λ hP hΛ M'
    (fun z h1 h2 => ⟨(hM z h1 h2).2.2.1, (hM z h1 h2).2.2.2⟩)
  refine ⟨G, G', ?_, hG⟩
  have hDD : Matrix.fromBlocks P 0 0 P * (G * G').map ι = Matrix.fromBlocks P 0 0 P := by
    rw [GlobalTheory.LatticeStab.map_mul_of_nonUnital, ← Matrix.mul_assoc, ← hG, Matrix.mul_assoc, ← hG',
      ← Matrix.mul_assoc, hMM', Matrix.one_mul]
  have hQD : Matrix.fromBlocks Q 0 0 Q * Matrix.fromBlocks P 0 0 P =
      ι 1 • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A) := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_multiply]
    simp [hQP]
  have key : ι 1 • (G * G').map ι = ι 1 • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A) := by
    have := congrArg (fun X => Matrix.fromBlocks Q 0 0 Q * X) hDD
    simp only [← Matrix.mul_assoc, hQD] at this
    rwa [Matrix.smul_mul, Matrix.one_mul] at this
  ext i j
  apply hinj
  have := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, ← map_mul, one_mul] at this
  rw [this]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inverse_integral_matrices_preserving_doubled_lattice : ∀ (A O : Type) [CommRing A] [CommRing O] (ι : O →ₙ+* A) (n : ℕ) (P Q : Matrix (Fin n) (Fin n) A)
    (Λ : Set (Fin n → A)), Function.Injective ι → P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) A) →
    Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) A) → ι 1 • P = P → ι 1 • Q = Q →
    (∀ z, z ∈ Λ ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i)) →
    ∀ M M' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A, M * M' = 1 →
    (∀ z : Fin n ⊕ Fin n → A, z ∘ Sum.inl ∈ Λ → z ∘ Sum.inr ∈ Λ →
      (M *ᵥ z) ∘ Sum.inl ∈ Λ ∧ (M *ᵥ z) ∘ Sum.inr ∈ Λ ∧ (M' *ᵥ z) ∘ Sum.inl ∈ Λ ∧ (M' *ᵥ z) ∘ Sum.inr ∈ Λ) →
    ∃ G G' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, G * G' = 1 ∧
      M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι := by
  atlas_forward_decl GlobalTheory.LatticeStab.matrix_in_diag_basis
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

theorem GlobalTheory.fromBlocks_unitary_transfer : ∀ (A O : Type) [CommRing A] [CommRing O] (ι : O →ₙ+* A) (γ : A →+* A) (c : O →+* O) (n : ℕ)
    (P K : Matrix (Fin n) (Fin n) A) (JL : Matrix (Fin n) (Fin n) O),
    Function.Injective ι → (∀ x, γ (ι x) = ι (c x)) → Pᵀ * K * P.map γ = JL.map ι →
    ∀ (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O),
    Mᵀ * Matrix.fromBlocks K 0 0 (-K) * M.map γ = Matrix.fromBlocks K 0 0 (-K) →
    M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι →
    Gᵀ * Matrix.fromBlocks JL 0 0 (-JL) * G.map c = Matrix.fromBlocks JL 0 0 (-JL) := by
  intro A O _ _ ι γ c n P K JL hinj hγ hP M G hM hG
  have hmul : ∀ {m : Type} [Fintype m] (X Y : Matrix m m O), (X * Y).map ι = X.map ι * Y.map ι := by
    intro m _ X Y; ext i j; simp [Matrix.mul_apply, map_sum]
  have hneg : (-JL).map ι = -(JL.map ι) := by ext i j; simp
  have hD : (Matrix.fromBlocks P 0 0 P)ᵀ * Matrix.fromBlocks K 0 0 (-K) * (Matrix.fromBlocks P 0 0 P).map γ
      = (Matrix.fromBlocks JL 0 0 (-JL)).map ι := by
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_map,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_map, hneg, ← hP]
    simp [Matrix.mul_neg, Matrix.neg_mul]
  have hc : (G.map c).map ι = (G.map ι).map γ := by
    ext i j; simp [hγ]
  apply Matrix.map_injective hinj
  show (Gᵀ * Matrix.fromBlocks JL 0 0 (-JL) * G.map c).map ι = (Matrix.fromBlocks JL 0 0 (-JL)).map ι
  rw [hmul, hmul, Matrix.transpose_map, hc]
  conv_lhs => rw [← hD]
  have hG' : (Matrix.fromBlocks P 0 0 P * G.map ι).map γ = (Matrix.fromBlocks P 0 0 P).map γ * (G.map ι).map γ := by
    rw [Matrix.map_mul]
  calc (G.map ι)ᵀ * ((Matrix.fromBlocks P 0 0 P)ᵀ * Matrix.fromBlocks K 0 0 (-K) * (Matrix.fromBlocks P 0 0 P).map γ) * (G.map ι).map γ
      = (Matrix.fromBlocks P 0 0 P * G.map ι)ᵀ * Matrix.fromBlocks K 0 0 (-K) * (Matrix.fromBlocks P 0 0 P * G.map ι).map γ := by
        rw [hG', Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = (M * Matrix.fromBlocks P 0 0 P)ᵀ * Matrix.fromBlocks K 0 0 (-K) * (M * Matrix.fromBlocks P 0 0 P).map γ := by rw [hG]
    _ = (Matrix.fromBlocks P 0 0 P)ᵀ * (Mᵀ * Matrix.fromBlocks K 0 0 (-K) * M.map γ) * (Matrix.fromBlocks P 0 0 P).map γ := by
        rw [Matrix.map_mul, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hM, hD]
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_fromBlocks_neg_of_diag_basis_transport : ∀ (A O : Type) [CommRing A] [CommRing O] (ι : O →ₙ+* A) (γ : A →+* A) (c : O →+* O) (n : ℕ)
    (P K : Matrix (Fin n) (Fin n) A) (JL : Matrix (Fin n) (Fin n) O),
    Function.Injective ι → (∀ x, γ (ι x) = ι (c x)) → Pᵀ * K * P.map γ = JL.map ι →
    ∀ (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O),
    Mᵀ * Matrix.fromBlocks K 0 0 (-K) * M.map γ = Matrix.fromBlocks K 0 0 (-K) →
    M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι →
    Gᵀ * Matrix.fromBlocks JL 0 0 (-JL) * G.map c = Matrix.fromBlocks JL 0 0 (-JL) := by
  atlas_forward_decl GlobalTheory.fromBlocks_unitary_transfer
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

theorem GlobalTheory.HermBlockChange.exists_unit_lower_block : ∀ (O : Type) [CommRing O] (c : O →+* O), IsUnit (2 : O) →
    (∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
      ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
        gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
        ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det) →
    ∀ (n : ℕ) (JL : Matrix (Fin n) (Fin n) O) (G G' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O),
    (∀ i j, c (JL j i) = JL i j) → IsUnit JL.det → G * G' = 1 →
    Gᵀ * Matrix.fromBlocks JL 0 0 (-JL) * G.map c = Matrix.fromBlocks JL 0 0 (-JL) →
    ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * JL + JL * Z.map c = 0 ∧
      IsUnit (((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) +
        ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) * Z).det := by
  intro O _ c h2 hcore n JL G G' hJL hdet hGG' hG
  obtain ⟨a, ha⟩ : ∃ a : O, a * 2 = 1 := ⟨↑(h2.unit⁻¹), by simp⟩
  have ha' : (2 : O) * a = 1 := by rw [mul_comm, ha]
  have hca : c a = a := by
    have h1 : c a * 2 = 1 := by
      have := congrArg c ha
      rwa [map_mul, map_one, map_ofNat] at this
    calc c a = c a * (2 * a) := by rw [ha', mul_one]
      _ = (c a * 2) * a := by ring
      _ = a := by rw [h1, one_mul]
  set Δ : Matrix (Fin n ⊕ Fin n) (Fin n) O := Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) 1 with hΔ
  set Nb : Matrix (Fin n ⊕ Fin n) (Fin n) O := Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1) with hNb
  set T : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O := Matrix.fromCols Δ Nb with hTdef
  have hT : T = Matrix.fromBlocks 1 1 1 (-1) := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [T, Δ, Nb]
  have hTt : Tᵀ = T := by
    rw [hT, Matrix.fromBlocks_transpose]; simp
  have hTc : T.map c = T := by
    rw [hT, Matrix.fromBlocks_map]; simp
    ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hTT : T * T = (2 : O) • 1 := by
    rw [hT, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
    simp [two_smul]
  set J : Matrix (Fin n) (Fin n) O := (2 : O) • JL with hJ
  set K : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O := Matrix.fromBlocks 0 J J 0 with hK
  set D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O := Matrix.fromBlocks JL 0 0 (-JL) with hD
  have hTKT : T * K * T = (4 : O) • D := by
    rw [hT, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]
    simp [J]
    exact ⟨by rw [← add_smul]; norm_num, by rw [← neg_add, ← add_smul]; norm_num⟩
  have hTDT : T * D * T = K := by
    rw [hT, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [K, J, two_smul]
  have h4 : a * a * 4 = (1 : O) := by linear_combination (2 * a + 1) * ha
  set g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O := a • (Tᵀ * G * T) with hg
  have hmapsmul : ∀ (b : O) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O), (b • M).map c = c b • M.map c := by
    intro b M; ext i j; simp
  have hgt : gᵀ = a • (T * Gᵀ * T) := by
    simp only [hg, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose, hTt, Matrix.mul_assoc]
  have hgc : g.map c = a • (T * G.map c * T) := by
    rw [hg, hTt, hmapsmul, Matrix.map_mul, Matrix.map_mul, hTc, hca]
  have hgK : gᵀ * K * g.map c = K := by
    rw [hgt, hgc]
    calc a • (T * Gᵀ * T) * K * a • (T * G.map c * T)
        = (a * a) • (T * Gᵀ * (T * K * T) * G.map c * T) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = (a * a * 4) • (T * (Gᵀ * D * G.map c) * T) := by
          rw [hTKT]; simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = K := by rw [hG, h4, one_smul, hTDT]
  have hgdet : g * (a • (T * G' * T)) = 1 := by
    rw [hg, hTt]
    calc a • (T * G * T) * a • (T * G' * T)
        = (a * a) • (T * G * (T * T) * G' * T) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = (a * a * 2) • (T * (G * G') * T) := by
          rw [hTT]; simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, Matrix.one_mul]
      _ = 1 := by
          rw [hGG', Matrix.mul_one, hTT, smul_smul, show a * a * 2 * 2 = (1 : O) by linear_combination (2 * a + 1) * ha, one_smul]
  have hJherm : ∀ i j, c (J j i) = J i j := by intro i j; simp only [J, Matrix.smul_apply, smul_eq_mul, map_mul, map_ofNat, hJL]
  have hJdet : IsUnit J.det := by
    rw [hJ, Matrix.det_smul]; exact (h2.pow _).mul hdet
  obtain ⟨Z, hZ1, hZ2⟩ := hcore n J hJherm hJdet g (Matrix.isUnit_det_of_right_inverse hgdet) hgK
  refine ⟨Z, ?_, ?_⟩
  · have h := congrArg (fun M => a • M) hZ1
    simp only [J, Matrix.mul_smul, Matrix.smul_mul, ← smul_add, smul_smul, ha, one_smul, smul_zero] at h
    exact h
  · have hblk : Tᵀ * G * T = Matrix.fromBlocks (Δᵀ * G * Δ) (Δᵀ * G * Nb) (Nbᵀ * G * Δ) (Nbᵀ * G * Nb) := by
      rw [hTdef, Matrix.transpose_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
    have h21 : g.toBlocks₂₁ = a • (Nbᵀ * G * Δ) := by
      rw [hg, hblk, Matrix.fromBlocks_smul, Matrix.toBlocks_fromBlocks₂₁]
    have h22 : g.toBlocks₂₂ = a • (Nbᵀ * G * Nb) := by
      rw [hg, hblk, Matrix.fromBlocks_smul, Matrix.toBlocks_fromBlocks₂₂]
    have hE : Nbᵀ * G * Nb + Nbᵀ * G * Δ * Z = (2 : O) • (g.toBlocks₂₁ * Z + g.toBlocks₂₂) := by
      rw [h21, h22, Matrix.smul_mul, ← smul_add, smul_smul, ha', one_smul, add_comm]
    rw [hE, Matrix.det_smul]; exact (h2.pow _).mul hZ2
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_skewHermitian_correction_isUnit_antidiag_corner : ∀ (O : Type) [CommRing O] (c : O →+* O), IsUnit (2 : O) →
    (∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
      ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
        gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
        ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det) →
    ∀ (n : ℕ) (JL : Matrix (Fin n) (Fin n) O) (G G' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O),
    (∀ i j, c (JL j i) = JL i j) → IsUnit JL.det → G * G' = 1 →
    Gᵀ * Matrix.fromBlocks JL 0 0 (-JL) * G.map c = Matrix.fromBlocks JL 0 0 (-JL) →
    ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * JL + JL * Z.map c = 0 ∧
      IsUnit (((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) +
        ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) * Z).det := by
  atlas_forward_decl GlobalTheory.HermBlockChange.exists_unit_lower_block
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.TransportBack

open Matrix

theorem map_mul_gen {R S Fh : Type*} [CommRing R] [CommRing S] [FunLike Fh R S]
    [NonUnitalRingHomClass Fh R S] (f : Fh) {m k p : Type*} [Fintype k]
    (X : Matrix m k R) (Y : Matrix k p R) : (X * Y).map f = X.map f * Y.map f := by
  ext i j; simp [Matrix.mul_apply, map_sum, map_mul]

theorem map_mulVec_gen {R S Fh : Type*} [CommRing R] [CommRing S] [FunLike Fh R S]
    [NonUnitalRingHomClass Fh R S] (f : Fh) {m k : Type*} [Fintype k]
    (X : Matrix m k R) (a : k → R) : X.map f *ᵥ (fun i => f (a i)) = fun i => f ((X *ᵥ a) i) := by
  ext i; simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem map_add_gen {R S Fh : Type*} [CommRing R] [CommRing S] [FunLike Fh R S]
    [NonUnitalRingHomClass Fh R S] (f : Fh) {m k : Type*}
    (X Y : Matrix m k R) : (X + Y).map f = X.map f + Y.map f := by
  ext i j; simp

theorem map_one_eq {R S : Type*} [CommRing R] [CommRing S] (ι : R →ₙ+* S) {n : Type*} [DecidableEq n] :
    (1 : Matrix n n R).map ι = ι 1 • (1 : Matrix n n S) := by
  ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem map_neg_one_eq {R S : Type*} [CommRing R] [CommRing S] (ι : R →ₙ+* S) {n : Type*} [DecidableEq n] :
    (-1 : Matrix n n R).map ι = -(ι 1 • (1 : Matrix n n S)) := by
  ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem assoc_a {R : Type*} [CommRing R] {a b c d e : Type*} [Fintype b] [Fintype c] [Fintype d]
    (A : Matrix a b R) (B : Matrix b c R) (C : Matrix c d R) (D : Matrix d e R) :
    A * B * C * D = A * (B * (C * D)) := by simp only [Matrix.mul_assoc]

theorem assoc_b {R : Type*} [CommRing R] {a b c d : Type*} [Fintype b] [Fintype c] [Fintype d]
    (A : Matrix a b R) (B : Matrix b c R) (C : Matrix c d R) (P₁ Y Q₁ P₂ : Matrix d d R) :
    A * B * C * (P₁ * Y * Q₁) * P₂ = A * (B * (C * (P₁ * (Y * (Q₁ * P₂))))) := by
  simp only [Matrix.mul_assoc]

theorem smul_mid_of {R : Type*} [CommRing R] {a b d : Type*} [Fintype b] [DecidableEq b]
    (s : R) (A : Matrix a b R) (B : Matrix b b R) (C : Matrix b d R) (h : s • B = s • 1) :
    s • (A * B * C) = s • (A * C) := by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

theorem smul_last_of {R : Type*} [CommRing R] {a b c d e : Type*} [Fintype b] [Fintype c] [Fintype d]
    (s : R) (A : Matrix a b R) (B : Matrix b c R) (C : Matrix c d R) (Z : Matrix d e R) (h : s • Z = 0) :
    s • (A * B * C * Z) = 0 := by
  rw [← Matrix.mul_smul, h, Matrix.mul_zero]

end GlobalTheory.TransportBack

namespace GlobalTheory.TransportBack
open Matrix

theorem transport_back : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (X : Spc F E n) (v : Pl F) (O : Type) [CommRing O] (c : O →+* O) (ι : O →ₙ+* AE F E)
    (P Q : Matrix (Fin n) (Fin n) (AE F E)) (JL : Matrix (Fin n) (Fin n) O),
    At (evFin F v) (ι 1) → (∀ y : AE F E, At (evFin F v) y → ι 1 * y = y) → (∀ x, cA σ (ι x) = ι (c x)) →
    P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) → Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) →
    ι 1 • P = P → ι 1 • Q = Q → Pᵀ * incM F X.J * P.map (cA σ) = JL.map ι →
    (∀ z : Fin n → AE F E, z ∈ GlobalTheory.InertSph.latAt X v ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i)) →
    ∀ (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O)
      (ZL : Matrix (Fin n) (Fin n) O),
    At (evFin F v) (M - 1) → M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι →
    ZLᵀ * JL + JL * ZL.map c = 0 →
    IsUnit (((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) +
        ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) * ZL).det →
    ∃ Z : Matrix (Fin n) (Fin n) (AE F E), At (evFin F v) Z ∧
      (∀ z ∈ GlobalTheory.InertSph.latAt X v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt X v) ∧
      Zᵀ * incM F X.J + incM F X.J * Z.map (cA σ) = 0 ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * GlobalTheory.DblVac.antiCols n +
        (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * Z).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * GlobalTheory.DblVac.antiCols n +
          (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * Z)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  intro F E _ _ _ _ _ σ n X v O _ c ι P Q JL hAe he hc hPQ hQP heP heQ hJ hlat M G ZL hM hMG hZL hN
  have heι : ∀ x, ι 1 * ι x = ι x := fun x => by rw [← map_mul, one_mul]
  have hιe : ∀ x, ι x * ι 1 = ι x := fun x => by rw [← map_mul, mul_one]
  have hee : ι 1 * ι 1 = ι 1 := heι 1
  have hce : cA σ (ι 1) = ι 1 := by rw [hc, map_one]
  have hmapE : ∀ {m k : Type} (Y : Matrix m k O), ι 1 • Y.map ι = Y.map ι := by
    intro m k Y; ext i j; simp [heι]
  have hePY : ∀ {k : Type} [Fintype k] (Y : Matrix (Fin n) k (AE F E)), ι 1 • (P * Y) = P * Y := by
    intro k _ Y; rw [← Matrix.smul_mul, heP]
  have hZP : P * ZL.map ι * Q * P = P * ZL.map ι := by
    rw [Matrix.mul_assoc, hQP, Matrix.mul_smul, Matrix.mul_one, hePY]
  have hvec : ∀ a : Fin n → O, Q *ᵥ (P *ᵥ fun i => ι (a i)) = fun i => ι (a i) := by
    intro a; rw [Matrix.mulVec_mulVec, hQP, Matrix.smul_mulVec, Matrix.one_mulVec]
    ext i; simp [heι]

  have hAtZ : At (evFin F v) (P * ZL.map ι * Q) := by
    intro u hu
    have hu' : u • Q = 0 := by rw [← heQ, ← smul_assoc, hAe u hu, zero_smul]
    rw [← Matrix.mul_smul, hu', Matrix.mul_zero]

  have hlatZ : ∀ z ∈ GlobalTheory.InertSph.latAt X v, (P * ZL.map ι * Q) *ᵥ z ∈ GlobalTheory.InertSph.latAt X v := by
    intro z hz
    obtain ⟨a, rfl⟩ := (hlat z).1 hz
    refine (hlat _).2 ⟨ZL *ᵥ a, ?_⟩
    rw [Matrix.mulVec_mulVec, hZP, ← Matrix.mulVec_mulVec, map_mulVec_gen]

  have hPcQc : P.map (cA σ) * Q.map (cA σ) = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [← map_mul_gen, hPQ]; ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h, hce]
  have h1 : Pᵀ * incM F X.J = JL.map ι * Q.map (cA σ) := by
    calc Pᵀ * incM F X.J = ι 1 • (Pᵀ * incM F X.J) := by
            rw [← Matrix.smul_mul, ← Matrix.transpose_smul, heP]
      _ = Pᵀ * incM F X.J * (P.map (cA σ) * Q.map (cA σ)) := by
            rw [hPcQc, Matrix.mul_smul, Matrix.mul_one]
      _ = JL.map ι * Q.map (cA σ) := by rw [← Matrix.mul_assoc, hJ]
  have hPc : ι 1 • P.map (cA σ) = P.map (cA σ) := by
    conv_rhs => rw [← heP]
    ext i j; simp [hce]
  have h2 : incM F X.J * P.map (cA σ) = Qᵀ * JL.map ι := by
    calc incM F X.J * P.map (cA σ) = ι 1 • (incM F X.J * P.map (cA σ)) := by
            rw [← Matrix.mul_smul, hPc]
      _ = (P * Q)ᵀ * incM F X.J * P.map (cA σ) := by
            rw [hPQ, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.smul_mul,
              Matrix.one_mul]
      _ = Qᵀ * JL.map ι := by
            rw [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Pᵀ, hJ]
  have hmapc : (ZL.map ι).map (cA σ) = (ZL.map c).map ι := by
    rw [Matrix.map_map, Matrix.map_map]; congr 1; funext x; exact hc x
  have hJZ : (P * ZL.map ι * Q)ᵀ * incM F X.J + incM F X.J * (P * ZL.map ι * Q).map (cA σ) = 0 := by
    have hz0 : (ZLᵀ * JL + JL * ZL.map c).map ι = 0 := by rw [hZL]; ext i j; simp
    rw [map_add_gen, map_mul_gen, map_mul_gen, Matrix.transpose_map] at hz0
    rw [map_mul_gen, map_mul_gen, hmapc, Matrix.transpose_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [h1, ← Matrix.mul_assoc (incM F X.J), h2]
    calc _ = Qᵀ * ((ZL.map ι)ᵀ * JL.map ι + JL.map ι * (ZL.map c).map ι) * Q.map (cA σ) := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hz0]; simp

  set N := ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) +
        ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) * ZL with hNdef
  set K := (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * GlobalTheory.DblVac.antiCols n +
        (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * (P * ZL.map ι * Q) with hK
  have hNab : (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O)).map ι = Matrix.fromRows (ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E))) (-(ι 1 • 1)) := by
    rw [Matrix.fromRows_map, map_one_eq, map_neg_one_eq]
  have hDel : (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O)).map ι = Matrix.fromRows (ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E))) (ι 1 • 1) := by
    rw [Matrix.fromRows_map, map_one_eq]
  have hanti : GlobalTheory.DblVac.antiCols (F := F) (E := E) n * P = Matrix.fromBlocks P 0 0 P * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O)).map ι := by
    rw [hNab, GlobalTheory.DblVac.antiCols, Matrix.fromRows_mul, Matrix.fromBlocks_mul_fromRows]
    simp [Matrix.mul_smul, heP]
  have hdiag : ∀ Y : Matrix (Fin n) (Fin n) (AE F E), (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * (P * Y) = Matrix.fromBlocks P 0 0 P * ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O)).map ι * Y) := by
    intro Y
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hDel, diagCols, Matrix.fromRows_mul, Matrix.fromBlocks_mul_fromRows]
    simp [Matrix.mul_smul, heP]
  have hantiT : ∀ {k : Type} [Fintype k] (Y : Matrix (Fin n ⊕ Fin n) k (AE F E)), (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * (Matrix.fromBlocks P 0 0 P * Y) = P * (((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O)).map ι)ᵀ * Y) := by
    intro k _ Y
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hNab, GlobalTheory.DblVac.antiCols, Matrix.transpose_fromRows, Matrix.transpose_fromRows,
      Matrix.fromCols_mul_fromBlocks, Matrix.mul_fromCols]
    simp [Matrix.mul_smul, heP]
  have hMG' : ∀ {k : Type} [Fintype k] (Y : Matrix (Fin n ⊕ Fin n) k (AE F E)), M * (Matrix.fromBlocks P 0 0 P * Y) = Matrix.fromBlocks P 0 0 P * (G.map ι * Y) := by
    intro k _ Y; rw [← Matrix.mul_assoc, hMG, Matrix.mul_assoc]
  have hQPι : ZL.map ι * (Q * P) = ZL.map ι := by rw [hQP, Matrix.mul_smul, Matrix.mul_one, hmapE]
  have hKP : K * P = P * N.map ι := by
    rw [hK, Matrix.add_mul]
    refine (congrArg₂ (· + ·) (assoc_a _ _ _ _) (assoc_b _ _ _ _ _ _ _)).trans ?_
    rw [hanti, hQPι, hdiag, hMG', hMG', hantiT, hantiT, hNdef]
    simp only [map_add_gen, map_mul_gen, Matrix.transpose_map, Matrix.mul_add, Matrix.mul_assoc]

  have hN1 : N * N⁻¹ = 1 := Matrix.mul_nonsing_inv N hN
  have h2inv : algebraMap F (AE F E) 2⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap F (AE F E)) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  have hMe : ι 1 • (M - 1) = M - 1 := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    apply he
    intro u hu
    have := congrFun (congrFun (hM u hu) i) j
    simpa using this
  have hM1 : (1 - ι 1) • M = (1 - ι 1) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) := by
    rw [sub_smul, one_smul, sub_smul, one_smul, ← sub_eq_zero,
      show M - ι 1 • M - (1 - ι 1 • 1) = (M - 1) - (ι 1 • M - ι 1 • 1) by abel, ← smul_sub, hMe, sub_self]
  have hZe : (1 - ι 1) • (P * ZL.map ι * Q) = 0 := by
    rw [sub_smul, one_smul, ← Matrix.smul_mul, ← Matrix.smul_mul, heP, sub_self]
  have hAA : (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.antiCols n = (2 : AE F E) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [GlobalTheory.DblVac.antiCols, Matrix.transpose_fromRows]
    refine (Matrix.fromCols_mul_fromRows _ _ _ _).trans ?_
    simp [two_smul]
  have hKe : (1 - ι 1) • K = (1 - ι 1) • ((2 : AE F E) • (1 : Matrix (Fin n) (Fin n) (AE F E))) := by
    rw [hK, smul_add]
    refine (congrArg₂ (· + ·) (smul_mid_of _ _ _ _ hM1) (smul_last_of _ _ _ _ _ hZe)).trans ?_
    rw [add_zero]
    exact congrArg _ hAA
  set R := (algebraMap F (AE F E) 2⁻¹ * (1 - ι 1)) • (1 : Matrix (Fin n) (Fin n) (AE F E)) + P * N⁻¹.map ι * Q with hR
  have hKR : K * R = 1 := by
    have hsec : K * (P * N⁻¹.map ι * Q) = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hKP, Matrix.mul_assoc P, ← map_mul_gen, hN1, map_one_eq,
        Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPQ, smul_smul, hee]
    rw [hR, Matrix.mul_add, hsec, Matrix.mul_smul, Matrix.mul_one, mul_smul, hKe, smul_smul, smul_smul, ← add_smul,
      show algebraMap F (AE F E) 2⁻¹ * (1 - ι 1) * 2 + ι 1 = (1 - ι 1) * (algebraMap F (AE F E) 2⁻¹ * 2) + ι 1 by ring,
      h2inv, mul_one, sub_add_cancel, one_smul]
  have hPz : ∀ w : Fin n → AE F E, (1 - ι 1) • (P *ᵥ w) = 0 := by
    intro w; rw [← Matrix.smul_mulVec, sub_smul, one_smul, heP, sub_self, Matrix.zero_mulVec]
  refine ⟨P * ZL.map ι * Q, hAtZ, hlatZ, hJZ, Matrix.isUnit_det_of_right_inverse hKR, ?_⟩
  intro z hz
  obtain ⟨a, rfl⟩ := (hlat z).1 hz
  rw [Matrix.inv_eq_right_inv hKR]
  refine (hlat _).2 ⟨N⁻¹ *ᵥ a, ?_⟩
  rw [hR, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, mul_smul, hPz, smul_zero, zero_add,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hvec, map_mulVec_gen]

end GlobalTheory.TransportBack
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_skewHermitian_correction_of_local_solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (X : Spc F E n) (v : Pl F) (O : Type) [CommRing O] (c : O →+* O) (ι : O →ₙ+* AE F E)
    (P Q : Matrix (Fin n) (Fin n) (AE F E)) (JL : Matrix (Fin n) (Fin n) O),
    At (evFin F v) (ι 1) → (∀ y : AE F E, At (evFin F v) y → ι 1 * y = y) → (∀ x, cA σ (ι x) = ι (c x)) →
    P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) → Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) →
    ι 1 • P = P → ι 1 • Q = Q → Pᵀ * incM F X.J * P.map (cA σ) = JL.map ι →
    (∀ z : Fin n → AE F E, z ∈ GlobalTheory.InertSph.latAt X v ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i)) →
    ∀ (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O)
      (ZL : Matrix (Fin n) (Fin n) O),
    At (evFin F v) (M - 1) → M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι →
    ZLᵀ * JL + JL * ZL.map c = 0 →
    IsUnit (((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) +
        ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) * ZL).det →
    ∃ Z : Matrix (Fin n) (Fin n) (AE F E), At (evFin F v) Z ∧
      (∀ z ∈ GlobalTheory.InertSph.latAt X v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt X v) ∧
      Zᵀ * incM F X.J + incM F X.J * Z.map (cA σ) = 0 ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * GlobalTheory.DblVac.antiCols n +
        (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * Z).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * GlobalTheory.DblVac.antiCols n +
          (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * Z)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  atlas_forward_decl GlobalTheory.TransportBack.transport_back
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.TransvChoose

theorem exists_transversal : (∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    (∃ x : O, IsUnit (c x - x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ X v,
    ∃ Z : Matrix (Fin n) (Fin n) (AE F E), At (evFin F v) Z ∧ (∀ z ∈ GlobalTheory.InertSph.latAt X v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt X v) ∧
      Zᵀ * incM F X.J + incM F X.J * Z.map (cA σ) = 0 ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols n +
        (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * Z).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols n +
          (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * Z)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  intro core F E _ _ _ _ _ σ B n r s X hB hX v w hw g hg
  obtain ⟨O, _, c, ι, P, Q, JL, hloc, hcc, h2, hcx, hinj, hAt, hsupp, hcι, hPQ, hQP, hP, hQ, hJh, hJu, hJ, hlat⟩ :=
    GlobalTheory.T.exists_local_dictionary_inertPlace F E σ B n r s X hB hX v w hw
  haveI := hloc
  obtain ⟨hg1, hg2⟩ := hg
  have hinv : GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.matD g⁻¹ = 1 := by
    simp [GlobalTheory.DblVac.matD]
  obtain ⟨G, G', hGG, hMG⟩ := GlobalTheory.T.exists_inverse_integral_matrices_preserving_doubled_lattice (AE F E) O ι n P Q (GlobalTheory.InertSph.latAt X v : Set (Fin n → AE F E)) hinj hPQ hQP hP hQ
    (fun z => hlat z) (GlobalTheory.DblVac.matD g) (GlobalTheory.DblVac.matD g⁻¹) hinv (fun z h1 h2 => by
      obtain ⟨ha, hb⟩ := hg2 z ⟨h1, h2⟩
      exact ⟨ha.1, ha.2, hb.1, hb.2⟩)
  have hgU : (GlobalTheory.DblVac.matD g)ᵀ * Matrix.fromBlocks (incM F X.J) 0 0 (-incM F X.J) * (GlobalTheory.DblVac.matD g).map (cA σ).toRingHom =
      Matrix.fromBlocks (incM F X.J) 0 0 (-incM F X.J) := g.2
  have hU := GlobalTheory.T.unitary_fromBlocks_neg_of_diag_basis_transport (AE F E) O ι (cA σ).toRingHom c n P (incM F X.J) JL hinj hcι hJ (GlobalTheory.DblVac.matD g) G hgU hMG
  obtain ⟨ZL, hZL1, hZL2⟩ := GlobalTheory.T.exists_skewHermitian_correction_isUnit_antidiag_corner O c h2 (fun n J hJ hJd g hgd hgu => core O c hcc h2 hcx n J hJ hJd g hgd hgu)
    n JL G G' hJh hJu hGG hU
  exact GlobalTheory.T.exists_adelic_skewHermitian_correction_of_local_solution F E σ n X v O c ι P Q JL hAt hsupp hcι hPQ hQP hP hQ hJ hlat (GlobalTheory.DblVac.matD g) G ZL hg1 hMG hZL1 hZL2

end GlobalTheory.TransvChoose
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertPlace_transversal_of_localCore : (∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    (∃ x : O, IsUnit (c x - x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ X v,
    ∃ Z : Matrix (Fin n) (Fin n) (AE F E), At (evFin F v) Z ∧ (∀ z ∈ GlobalTheory.InertSph.latAt X v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt X v) ∧
      Zᵀ * incM F X.J + incM F X.J * Z.map (cA σ) = 0 ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols n +
        (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * Z).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols n +
          (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * Z)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  atlas_forward_decl GlobalTheory.TransvChoose.exists_transversal
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblVacUnip

open Matrix GlobalTheory.DblVac GlobalTheory.BigCell GlobalTheory.DblVacFactor

section Abstract

variable {R : Type} [CommRing R] {β : Type} [Fintype β] [DecidableEq β] [Invertible (2 : R)]

theorem mem_unitary_of_skew (f : R →+* R) (J : Matrix β β R) (K : Matrix (β ⊕ β) (β ⊕ β) R)
    (Δ N : Matrix (β ⊕ β) β R) (Δt Nt : Matrix β (β ⊕ β) R) (x : Matrix β β R)
    (hΔT : Δᵀ = Δt) (hNT : Nᵀ = Nt) (hΔf : Δ.map f = Δ) (hNtf : Nt.map f = Nt)
    (e3 : Δt * K = J * Nt) (e4 : K * Δ = N * J) (e5 : Δt * K * Δ = 0)
    (hZ : xᵀ * J + J * x.map f = 0) :
    (1 + ⅟(2 : R) • (Δ * x * Nt))ᵀ * K * (1 + ⅟(2 : R) • (Δ * x * Nt)).map f = K := by
  have hNtT : Ntᵀ = N := by rw [← hNT, transpose_transpose]
  have hMT : (Δ * x * Nt)ᵀ = N * (xᵀ * Δt) := by simp only [transpose_mul, hNtT, hΔT, Matrix.mul_assoc]
  have hMf : (Δ * x * Nt).map f = Δ * (x.map f * Nt) := by simp only [Matrix.map_mul, hΔf, hNtf, Matrix.mul_assoc]
  have hPT : (1 + ⅟(2 : R) • (Δ * x * Nt))ᵀ = 1 + ⅟(2 : R) • (N * (xᵀ * Δt)) := by
    rw [transpose_add, transpose_one, transpose_smul, hMT]
  have hPf : (1 + ⅟(2 : R) • (Δ * x * Nt)).map f = 1 + ⅟(2 : R) • (Δ * (x.map f * Nt)) := by
    rw [Matrix.map_add f (map_add f), Matrix.map_one f (map_zero f) (map_one f), Matrix.map_smul' _ _ _ (map_mul f),
      map_half, hMf]
  have A1 : N * (xᵀ * Δt) * K * (Δ * (x.map f * Nt)) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [show Δt * (K * (Δ * (x.map f * Nt))) = 0 by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e5, Matrix.zero_mul]]
    simp
  have A2 : N * (xᵀ * Δt) * K + K * (Δ * (x.map f * Nt)) = 0 := by
    calc _ = N * ((xᵀ * J + J * x.map f) * Nt) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, e3, ← Matrix.mul_assoc K Δ, e4]
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
      _ = 0 := by rw [hZ]; simp
  have expand : ∀ U V : Matrix (β ⊕ β) (β ⊕ β) R, (1 + ⅟(2 : R) • U) * K * (1 + ⅟(2 : R) • V) =
      K + ⅟(2 : R) • (U * K + K * V) + (⅟(2 : R) * ⅟(2 : R)) • (U * K * V) := by
    intro U V
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      smul_add, smul_smul]
    abel
  rw [hPT, hPf, expand, A2, A1]
  simp

end Abstract

theorem unip_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : Spc F E d) (v : Pl F), (2 : 𝓞 F) ∉ v.asIdeal → ∀ Z : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) Z →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    Zᵀ * incM F W.J + incM F W.J * Z.map (cA σ) = 0 →
    ∃ u ∈ GlobalTheory.DblVac.KD σ W v, u ∈ GlobalTheory.DblVac.PDiag σ W ∧
      GlobalTheory.DblVac.matD u = 1 + (⅟(2 : AF F)) • ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * Z * (GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ) := by
  intro F E _ _ _ _ _ σ d W v h2 Z hZat hZlat hZskew
  letI : Invertible (2 : AE F E) := invTwoE
  set f : AE F E →+* AE F E := ((cA σ : AE F E →ₐ[AF F] AE F E) : AE F E →+* AE F E) with hf
  set J : Matrix (Fin d) (Fin d) (AE F E) := incM F W.J with hJ
  have h1 : (1 : Matrix (Fin d) (Fin d) (AE F E)).map f = 1 := Matrix.map_one f (map_zero f) (map_one f)
  have hm1 : (-1 : Matrix (Fin d) (Fin d) (AE F E)).map f = -1 := by rw [Matrix.map_neg _ (map_neg f), h1]
  have hΔT : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ =
      fromCols 1 1 := by
    rw [transpose_fromRows, transpose_one]
  have hNT : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ =
      fromCols 1 (-1) := by
    rw [transpose_fromRows, transpose_one, transpose_neg, transpose_one]
  have hΔf : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)).map f =
      fromRows 1 1 := by rw [fromRows_map, h1]
  have hNtf : (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)).map f =
      fromCols 1 (-1) := by rw [fromCols_map, h1, hm1]
  have hskew : Zᵀ * J + J * Z.map f = 0 := hZskew
  set M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) :=
    (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * Z *
    (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) with hMdef
  have hinv := mul_inv_eq (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))
    (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) e1 Z
  have hmem := mem_unitary_of_skew f J (dbl J) _ _ _ _ Z hΔT hNT hΔf hNtf (e3 J) (e4 J) (e5 J) hskew
  let P : GL (Fin d ⊕ Fin d) (AE F E) := ⟨1 + ⅟(2 : AE F E) • M, 1 - ⅟(2 : AE F E) • M, hinv.1, hinv.2⟩
  let p : UD σ W := ⟨P, hmem⟩
  have hMu : ∀ u : AF F, evFin F v u = 0 → u • M = 0 := by
    intro u hu
    have hu' : u • Z = 0 := hZat u hu
    calc u • M = (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * (u • Z) *
        (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) := by
          rw [hMdef]; simp only [Matrix.mul_smul, Matrix.smul_mul]
      _ = 0 := by rw [hu']; simp
  have hpK : p ∈ KD σ W v := by
    refine ⟨fun u hu => ?_, fun z hz => ⟨?_, ?_⟩⟩
    · show u • ((1 + ⅟(2 : AE F E) • M) - 1) = 0
      rw [add_sub_cancel_left, smul_comm, hMu u hu, smul_zero]
    · show (1 + ⅟(2 : AE F E) • M) *ᵥ z ∈ latD W v
      rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hMdef]
      simp only [← Matrix.mulVec_mulVec]
      exact latD_add hz (latD_half h2 (latD_diag (hZlat _ (lat_antiT hz))))
    · show (1 - ⅟(2 : AE F E) • M) *ᵥ z ∈ latD W v
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hMdef]
      simp only [← Matrix.mulVec_mulVec]
      exact latD_sub hz (latD_half h2 (latD_diag (hZlat _ (lat_antiT hz))))
  refine ⟨p, hpK, ⟨1, ?_⟩, ?_⟩
  · have key : ((1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) + ⅟(2 : AE F E) • M) *
        (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
        (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) := by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hMdef, Matrix.mul_assoc _ _
        (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)), e1,
        Matrix.mul_zero, smul_zero, add_zero]
    show ((1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) + ⅟(2 : AE F E) • M) *
        (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
      (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) *
        ((1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E))
    rw [Units.val_one, Matrix.mul_one]
    exact key
  · have hNt : (antiCols (F := F) (E := E) d)ᵀ = fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) := by
      rw [antiCols, transpose_fromRows, transpose_one, transpose_neg, transpose_one]
    show (1 + ⅟(2 : AE F E) • M) = _
    rw [hNt, invOf_two_eq, algebraMap_smul]
    rfl

end GlobalTheory.DblVacUnip
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfSkewUnipotent_mem_doubledLatticeStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : Spc F E d) (v : Pl F), (2 : 𝓞 F) ∉ v.asIdeal → ∀ Z : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) Z →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    Zᵀ * incM F W.J + incM F W.J * Z.map (cA σ) = 0 →
    ∃ u ∈ GlobalTheory.DblVac.KD σ W v, u ∈ GlobalTheory.DblVac.PDiag σ W ∧
      GlobalTheory.DblVac.matD u = 1 + (⅟(2 : AF F)) • ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * Z * (GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ) := by
  atlas_forward_decl GlobalTheory.DblVacUnip.unip_mem
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertTransv

theorem exists_unip_corner_isUnit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ X v,
    ∃ u ∈ GlobalTheory.DblVac.KD σ X v, u ∈ GlobalTheory.DblVac.PDiag σ X ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD (g * u) * GlobalTheory.DblVac.antiCols n).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD (g * u) * GlobalTheory.DblVac.antiCols n)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  intro F E _ _ _ _ _ σ B n r s X hB hX v w hvw g hg
  obtain ⟨Z, hZs, hZl, hZn, hdet, hinv⟩ := GlobalTheory.T.exists_inertPlace_transversal_of_localCore GlobalTheory.T.exists_isotropic_graph_unitary_isUnit_lowerBlock F E σ B n r s X hB hX v w hvw g hg
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hB.inert v w hvw).1
  obtain ⟨u, huK, huP, hu⟩ := GlobalTheory.T.halfSkewUnipotent_mem_doubledLatticeStabilizer F E σ n X v h2 Z hZs hZl hZn
  set N : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) := GlobalTheory.DblVac.antiCols (F := F) (E := E) n with hN
  set Δ : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) := diagCols (Fin n) with hΔ
  have hNN : Nᵀ * N = (2 : AF F) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [hN, GlobalTheory.DblVac.antiCols, Matrix.transpose_fromRows, Matrix.transpose_one, Matrix.transpose_neg,
      Matrix.transpose_one, Matrix.fromCols_mul_fromRows]
    simp [two_smul]
  have hmul : GlobalTheory.DblVac.matD (g * u) = GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.matD u := rfl
  have key : Nᵀ * GlobalTheory.DblVac.matD (g * u) * N = Nᵀ * GlobalTheory.DblVac.matD g * N + Nᵀ * GlobalTheory.DblVac.matD g * Δ * Z := by
    rw [hmul, hu]
    have : Nᵀ * (GlobalTheory.DblVac.matD g * (1 + (⅟(2 : AF F)) • (Δ * Z * Nᵀ))) * N =
        Nᵀ * GlobalTheory.DblVac.matD g * N + (⅟(2 : AF F)) • (Nᵀ * GlobalTheory.DblVac.matD g * Δ * Z * (Nᵀ * N)) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [this, hNN, Matrix.mul_smul, smul_smul, invOf_mul_self, one_smul, Matrix.mul_one]
  refine ⟨u, huK, huP, ?_, ?_⟩
  · convert hdet using 2
    exact congrArg Matrix.det key
  · intro z hz; convert hinv z hz using 3
    exact key

end GlobalTheory.InertTransv
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unipotent_corner_isUnit_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ X v,
    ∃ u ∈ GlobalTheory.DblVac.KD σ X v, u ∈ GlobalTheory.DblVac.PDiag σ X ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD (g * u) * GlobalTheory.DblVac.antiCols n).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD (g * u) * GlobalTheory.DblVac.antiCols n)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  atlas_forward_decl GlobalTheory.InertTransv.exists_unip_corner_isUnit
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblGenV

open Matrix GlobalTheory.DblVac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem matD_mul {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g h : UD σ W) : matD (g * h) = matD g * matD h := rfl

theorem matD_inv_mul {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g : UD σ W) : matD g⁻¹ * matD g = 1 := by
  rw [← matD_mul, inv_mul_cancel]; rfl

theorem KD_mul {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl F} {g h : UD σ W} (hg : g ∈ KD σ W v)
    (hh : h ∈ KD σ W v) : g * h ∈ KD σ W v := by
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · have e : matD (g * h) - 1 = matD g * (matD h - 1) + (matD g - 1) := by
      rw [matD_mul, Matrix.mul_sub, Matrix.mul_one]; abel
    show u • (matD (g * h) - 1) = 0
    have h1 : u • (matD h - 1) = 0 := hh.1 u hu
    have h2 : u • (matD g - 1) = 0 := hg.1 u hu
    rw [e, smul_add, ← Matrix.mul_smul, h1, h2, Matrix.mul_zero, add_zero]
  · refine ⟨?_, ?_⟩
    · rw [matD_mul, ← Matrix.mulVec_mulVec]; exact (hg.2 _ (hh.2 z hz).1).1
    · rw [_root_.mul_inv_rev, matD_mul, ← Matrix.mulVec_mulVec]; exact (hh.2 _ (hg.2 z hz).2).2

theorem KD_inv {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl F} {g : UD σ W} (hg : g ∈ KD σ W v) :
    g⁻¹ ∈ KD σ W v := by
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · have e : matD g⁻¹ - 1 = -(matD g⁻¹ * (matD g - 1)) := by
      rw [Matrix.mul_sub, matD_inv_mul, Matrix.mul_one]; abel
    show u • (matD g⁻¹ - 1) = 0
    have h2 : u • (matD g - 1) = 0 := hg.1 u hu
    rw [e, smul_neg, ← Matrix.mul_smul, h2, Matrix.mul_zero, neg_zero]
  · rw [inv_inv]; exact ⟨(hg.2 z hz).2, (hg.2 z hz).1⟩

theorem PDiag_inv {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {p : UD σ W} (hp : p ∈ PDiag σ W) :
    p⁻¹ ∈ PDiag σ W := by
  obtain ⟨t, ht⟩ := hp
  refine ⟨t⁻¹, ?_⟩
  set D : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E) := diagCols (Fin d) with hDdef
  set T : Matrix (Fin d) (Fin d) (AE F E) := (t : Matrix (Fin d) (Fin d) (AE F E)) with hT
  set Ti : Matrix (Fin d) (Fin d) (AE F E) := ((t⁻¹ : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) with hTi
  have hTT : T * Ti = 1 := by rw [hT, hTi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have ht' : matD p * D = D * T := ht
  have key : matD p⁻¹ * (D * T) = D := by
    rw [← ht', ← Matrix.mul_assoc, matD_inv_mul, Matrix.one_mul]
  show matD p⁻¹ * D = D * Ti
  calc matD p⁻¹ * D = matD p⁻¹ * (D * T) * Ti := by
        rw [Matrix.mul_assoc (matD p⁻¹), Matrix.mul_assoc D, hTT, Matrix.mul_one]
    _ = D * Ti := by rw [key]

end GlobalTheory.DblGenV

namespace GlobalTheory.DblGenV

theorem mem_of_KD_diag_anti : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ H : Subgroup (GlobalTheory.DblVac.UD σ G.V),
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → p ∈ H) →
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PAnti σ G.V → p ∈ H) → ∀ g ∈ GlobalTheory.DblVac.KD σ G.V v, g ∈ H := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin _ H hD hA g hg
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hT.base.inert v w hin).1
  obtain ⟨u, hu, huP, hdet, hlat⟩ := GlobalTheory.T.exists_unipotent_corner_isUnit_inertPlace F E σ B a (a - G.p) G.p G.V hT.base hT.geo.hV v w hin g hg
  obtain ⟨p, q, hp, hpP, hq, hqA, hpq⟩ := GlobalTheory.T.doubledVacuumLatticeStabilizer_bigCell_factorization F E σ a G.V v h2 (g * u) (KD_mul hg hu) hdet hlat
  have e : g = p * q * u⁻¹ := by rw [← hpq]; group
  rw [e]
  exact H.mul_mem (H.mul_mem (hD p hp hpP) (hA q hq hqA)) (hD _ (KD_inv hu) (PDiag_inv huP))

end GlobalTheory.DblGenV
end
end
