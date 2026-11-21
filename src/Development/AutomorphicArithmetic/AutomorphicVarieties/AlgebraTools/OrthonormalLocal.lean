import Mathlib

section
open Polynomial Matrix IsLocalRing TensorProduct

namespace UpperTheory.V.AlgebraTools

private def DGood {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι R) : Prop :=
  ∃ P : Matrix ι ι R, IsUnit P.det ∧ (Pᵀ * H * P).IsDiag

private theorem dgood_congr {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (H Q : Matrix ι ι R) (hQ : IsUnit Q.det) (h : DGood (Qᵀ * H * Q)) : DGood H := by
  obtain ⟨P, hP, hD⟩ := h
  refine ⟨Q * P, by rw [det_mul]; exact hQ.mul hP, ?_⟩
  rw [transpose_mul]
  simpa only [Matrix.mul_assoc] using hD

private theorem dgood_reindex {R : Type} [CommRing R] {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : κ ≃ ι)
    (H : Matrix ι ι R) (h : DGood (H.submatrix e e)) : DGood H := by
  obtain ⟨P, hP, hD⟩ := h
  refine ⟨P.submatrix e.symm e.symm, by rw [det_submatrix_equiv_self]; exact hP, ?_⟩
  have key : (P.submatrix e.symm e.symm)ᵀ * H * P.submatrix e.symm e.symm
      = (Pᵀ * H.submatrix e e * P).submatrix e.symm e.symm := by
    rw [← submatrix_mul_equiv _ _ _ e.symm _, ← submatrix_mul_equiv _ _ _ e.symm _,
      transpose_submatrix, submatrix_submatrix]
    simp
  rw [key]
  exact hD.submatrix e.symm.injective

private theorem pivot {R : Type} [CommRing R] [IsLocalRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι R) (h2 : IsUnit (2 : R)) (hs : Hᵀ = H) (hd : IsUnit H.det) (i : ι) :
    ∃ Q : Matrix ι ι R, IsUnit Q.det ∧ IsUnit ((Qᵀ * H * Q) i i) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, IsUnit (H i j) := by
    by_contra hne
    push_neg at hne
    have key : ∑ j, H i j * adjugate H j i = H.det := by
      have := congrFun (congrFun (mul_adjugate H) i) i
      simpa [Matrix.mul_apply] using this
    have hm : ∑ j, H i j * adjugate H j i ∈ maximalIdeal R :=
      Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _
        (by rw [mem_maximalIdeal, mem_nonunits_iff]; exact hne j)
    rw [key, mem_maximalIdeal, mem_nonunits_iff] at hm
    exact hm hd
  by_cases hij : j = i
  · subst hij
    exact ⟨1, by simp, by simpa using hj⟩
  · have hji : H j i = H i j := by
      have := congrFun (congrFun hs i) j
      simpa using this
    have hent : ∀ c : R, ((transvection j i c)ᵀ * H * transvection j i c) i i
        = H i i + 2 * c * H i j + c * c * H j j := by
      intro c
      simp [transvection, Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
        add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite, Ne.symm hij, hij, hji]
      ring
    by_cases hp : IsUnit (H i i + 2 * 1 * H i j + 1 * 1 * H j j)
    · exact ⟨transvection j i 1, by rw [det_transvection_of_ne j i hij]; exact isUnit_one,
        by rw [hent]; exact hp⟩
    · refine ⟨transvection j i (-1), by rw [det_transvection_of_ne j i hij]; exact isUnit_one, ?_⟩
      rw [hent]
      by_contra hm
      have hx : (H i i + 2 * 1 * H i j + 1 * 1 * H j j)
          - (H i i + 2 * (-1) * H i j + (-1) * (-1) * H j j) ∈ maximalIdeal R :=
        Ideal.sub_mem _ ((mem_maximalIdeal _).2 hp) ((mem_maximalIdeal _).2 hm)
      have e4 : (H i i + 2 * 1 * H i j + 1 * 1 * H j j)
          - (H i i + 2 * (-1) * H i j + (-1) * (-1) * H j j) = 2 * 2 * H i j := by ring
      rw [e4, mem_maximalIdeal, mem_nonunits_iff] at hx
      exact hx ((h2.mul h2).mul hj)

private theorem step {R : Type} [CommRing R] {κ : Type} [Fintype κ] [DecidableEq κ]
    (ih : ∀ H : Matrix κ κ R, Hᵀ = H → IsUnit H.det → DGood H)
    (H : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R) (hs : Hᵀ = H) (hd : IsUnit H.det)
    (h0 : IsUnit (H (Sum.inl ()) (Sum.inl ()))) : DGood H := by
  classical
  have hH : H = fromBlocks (H (Sum.inl ()) (Sum.inl ()) • (1 : Matrix Unit Unit R))
      H.toBlocks₁₂ H.toBlocks₁₂ᵀ H.toBlocks₂₂ := by
    ext (⟨⟩ | k) (⟨⟩ | l)
    · simp
    · simp [toBlocks₁₂]
    · have := congrFun (congrFun hs (Sum.inl ())) (Sum.inr k)
      simp only [transpose_apply] at this
      simp [toBlocks₁₂, this]
    · simp [toBlocks₂₂]
  generalize H (Sum.inl ()) (Sum.inl ()) = a at hH h0
  generalize H.toBlocks₁₂ = B at hH
  generalize H.toBlocks₂₂ = D at hH
  subst hH
  have hDs : Dᵀ = D := by
    have := hs
    rw [fromBlocks_transpose] at this
    exact (fromBlocks_inj.1 this).2.2.2
  obtain ⟨b, hab⟩ := h0.exists_right_inv
  have hba : b * a = 1 := by rw [mul_comm]; exact hab
  have hE : (fromBlocks 1 (-(b • B)) 0 1 : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R)ᵀ
      * fromBlocks (a • 1) B Bᵀ D * fromBlocks 1 (-(b • B)) 0 1
      = fromBlocks (a • 1) 0 0 (D - b • (Bᵀ * B)) := by
    simp [fromBlocks_transpose, fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      hba, hab, sub_eq_neg_add]
  have hQ : IsUnit (fromBlocks 1 (-(b • B)) 0 1 : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R).det := by
    rw [det_fromBlocks_zero₂₁]; simp
  apply dgood_congr _ _ hQ
  rw [hE]
  have hSs : (D - b • (Bᵀ * B))ᵀ = D - b • (Bᵀ * B) := by
    rw [transpose_sub, transpose_smul, transpose_mul, transpose_transpose, hDs]
  have hSd : IsUnit (D - b • (Bᵀ * B)).det := by
    have h1 : IsUnit (fromBlocks (a • 1) 0 0 (D - b • (Bᵀ * B)) :
        Matrix (Unit ⊕ κ) (Unit ⊕ κ) R).det := by
      rw [← hE, det_mul, det_mul, det_transpose]
      exact (hQ.mul hd).mul hQ
    rw [det_fromBlocks_zero₂₁] at h1
    exact isUnit_of_mul_isUnit_right h1
  obtain ⟨P₀, hP₀, hP₀d⟩ := ih _ hSs hSd
  refine ⟨fromBlocks 1 0 0 P₀, ?_, ?_⟩
  · rw [det_fromBlocks_zero₂₁, det_one, one_mul]; exact hP₀
  · have hF : (fromBlocks 1 0 0 P₀ : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R)ᵀ
        * fromBlocks (a • 1) 0 0 (D - b • (Bᵀ * B)) * fromBlocks 1 0 0 P₀
        = fromBlocks (a • 1) 0 0 (P₀ᵀ * (D - b • (Bᵀ * B)) * P₀) := by
      simp [fromBlocks_transpose, fromBlocks_multiply]
    rw [hF]
    exact IsDiag.fromBlocks (fun i j h => absurd (Subsingleton.elim i j) h) hP₀d

private theorem dgood_fin {R : Type} [CommRing R] [IsLocalRing R] (h2 : IsUnit (2 : R)) (n : ℕ) :
    ∀ H : Matrix (Fin n) (Fin n) R, Hᵀ = H → IsUnit H.det → DGood H := by
  induction n with
  | zero =>
    intro H _ _
    exact ⟨1, by simp, fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro H hs hd
    have e : Unit ⊕ Fin n ≃ Fin (n + 1) := Fintype.equivFinOfCardEq (by simp [add_comm])
    obtain ⟨Q, hQ, hQi⟩ := pivot H h2 hs hd (e (Sum.inl ()))
    apply dgood_congr H Q hQ
    apply dgood_reindex e
    apply step ih
    · simp [transpose_submatrix, transpose_mul, hs, Matrix.mul_assoc]
    · rw [det_submatrix_equiv_self, det_mul, det_mul, det_transpose]
      exact (hQ.mul hd).mul hQ
    · exact hQi

end UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.diag_local :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] {n : ℕ} (H : Matrix (Fin n) (Fin n) R), IsUnit (2 : R) → Hᵀ = H → IsUnit H.det → ∃ (P : GL (Fin n) R) (c : Fin n → Rˣ), (P : Matrix (Fin n) (Fin n) R)ᵀ * H * P = diagonal fun i => (c i : R) := by
  intro R _ _ n H h2 hs hd
  obtain ⟨P, hP, hD⟩ := UpperTheory.V.AlgebraTools.dgood_fin h2 n H hs hd
  have hDu : IsUnit (Pᵀ * H * P).det := by
    rw [det_mul, det_mul, det_transpose]
    exact (hP.mul hd).mul hP
  have hdiag : ∀ i, IsUnit ((Pᵀ * H * P) i i) := by
    intro i
    rw [← hD.diagonal_diag, det_diagonal] at hDu
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (Pᵀ * H * P).diag (Finset.mem_univ i)) hDu
  refine ⟨((isUnit_iff_isUnit_det P).2 hP).unit, fun i => (hdiag i).unit, ?_⟩
  simp only [IsUnit.unit_spec]
  exact hD.diagonal_diag.symm
end

section
open Polynomial Matrix IsLocalRing TensorProduct

private theorem UpperTheory.V.AlgebraTools.sqrt_of_residue {R' : Type} [CommRing R'] [HenselianLocalRing R']
    (h2 : IsUnit (2 : R')) (u : R') (hu : IsUnit u) (hs : IsSquare (residue R' u)) :
    ∃ a : R', a * a = u := by
  obtain ⟨b, hb⟩ := hs
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective b
  have hres : residue R' (a₀ ^ 2 - u) = 0 := by rw [map_sub, map_pow, hb, pow_two, sub_self]
  have ha₀ : IsUnit a₀ := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff]
    intro h0
    have hu0 : residue R' u = 0 := by rw [hb, h0, mul_zero]
    exact (hu.map (residue R')).ne_zero hu0
  have hev : eval a₀ (X ^ 2 - C u) ∈ maximalIdeal R' := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    simpa using hres
  have hd : eval a₀ (derivative (X ^ 2 - C u)) = 2 * a₀ := by
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C,
      eval_pow, eval_X]
    norm_num
  have hdu : IsUnit (eval a₀ (derivative (X ^ 2 - C u))) := by
    rw [hd]
    exact h2.mul ha₀
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (X ^ 2 - C u)
    (monic_X_pow_sub_C u two_ne_zero) a₀ hev hdu
  refine ⟨a, ?_⟩
  have h0 := ha.eq_zero
  simp only [eval_sub, eval_pow, eval_X, eval_C] at h0
  rw [← pow_two]
  exact sub_eq_zero.mp h0

theorem UpperTheory.V.AlgebraTools.orthonormal_local :
    ∀ {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [HenselianLocalRing R'] (φ : R →+* R') {n : ℕ} (H : Matrix (Fin n) (Fin n) R), IsUnit (2 : R) → Hᵀ = H → IsUnit H.det → (∀ c : Rˣ, IsSquare (residue R' (φ c))) → ∃ P : GL (Fin n) R', (P : Matrix (Fin n) (Fin n) R')ᵀ * H.map φ * P = 1 := by
  intro R R' _ _ _ _ φ n H h2 hT hdet hsq
  obtain ⟨P, c, hP⟩ := UpperTheory.V.AlgebraTools.diag_local H h2 hT hdet
  have h2' : IsUnit (2 : R') := by
    have h := h2.map φ
    rwa [map_ofNat] at h
  have hroot : ∀ i, ∃ a : R', a * a = φ (c i) := fun i =>
    UpperTheory.V.AlgebraTools.sqrt_of_residue h2' _ ((c i).isUnit.map φ) (hsq (c i))
  choose a ha using hroot
  have hau : ∀ i, IsUnit (a i) := fun i =>
    isUnit_of_mul_isUnit_left (y := a i) (by rw [ha i]; exact (c i).isUnit.map φ)
  let D : GL (Fin n) R' :=
    ⟨diagonal fun i => (((hau i).unit⁻¹ : R'ˣ) : R'), diagonal fun i => a i,
      by rw [diagonal_mul_diagonal]; convert diagonal_one using 2; simp,
      by rw [diagonal_mul_diagonal]; convert diagonal_one using 2; simp⟩
  have hmap : ((Matrix.GeneralLinearGroup.map φ P : GL (Fin n) R') : Matrix (Fin n) (Fin n) R') =
      (P : Matrix (Fin n) (Fin n) R).map φ := by
    ext i j
    exact Matrix.GeneralLinearGroup.map_apply φ i j P
  have key : ((P : Matrix (Fin n) (Fin n) R).map φ)ᵀ * H.map φ *
      (P : Matrix (Fin n) (Fin n) R).map φ = diagonal fun i => φ (c i) := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hP, diagonal_map (map_zero φ)]
  refine ⟨Matrix.GeneralLinearGroup.map φ P * D, ?_⟩
  rw [Units.val_mul, hmap, Matrix.transpose_mul]
  have hD : ((D : GL (Fin n) R') : Matrix (Fin n) (Fin n) R') =
      diagonal fun i => (((hau i).unit⁻¹ : R'ˣ) : R') := rfl
  calc ((D : Matrix (Fin n) (Fin n) R'))ᵀ * ((P : Matrix (Fin n) (Fin n) R).map φ)ᵀ * H.map φ *
        ((P : Matrix (Fin n) (Fin n) R).map φ * (D : Matrix (Fin n) (Fin n) R'))
      = ((D : Matrix (Fin n) (Fin n) R'))ᵀ * (((P : Matrix (Fin n) (Fin n) R).map φ)ᵀ * H.map φ *
        (P : Matrix (Fin n) (Fin n) R).map φ) * (D : Matrix (Fin n) (Fin n) R') := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [key, hD, diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal]
      convert diagonal_one using 2
      funext i
      rw [← ha i]
      calc ((hau i).unit⁻¹ : R'ˣ).val * (a i * a i) * ((hau i).unit⁻¹ : R'ˣ).val
          = (((hau i).unit⁻¹ : R'ˣ).val * (hau i).unit.val) *
            ((hau i).unit.val * ((hau i).unit⁻¹ : R'ˣ).val) := by
            simp only [IsUnit.unit_spec]; ring
        _ = 1 := by simp
end
