import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsRestrictionBlockEmbeddingIntertwinesLie
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsFiniteDimensionalCompactTranslatesOfLevelT

section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.finiteDimensional_map_of_separately_finite :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (X Y : Type) (S : Submodule ℂ M) (Φ : M →ₗ[ℂ] (X × Y → ℂ)) (V₁ : Submodule ℂ (X → ℂ)) (V₂ : Submodule ℂ (Y → ℂ)), FiniteDimensional ℂ V₁ → FiniteDimensional ℂ V₂ → (∀ m ∈ S, ∀ y, (fun x => Φ m (x, y)) ∈ V₁) → (∀ m ∈ S, ∀ x, (fun y => Φ m (x, y)) ∈ V₂) → FiniteDimensional ℂ (S.map Φ) := by
  intro M _ _ X Y S Φ V₁ V₂ h₁ h₂ hrow hcol
  obtain ⟨T, hT⟩ := exists_finset_eval_eq_zero V₁
  have mem : ∀ g ∈ S.map Φ, ∀ x, (fun y => g (x, y)) ∈ V₂ := by
    rintro g ⟨m, hm, rfl⟩ x
    exact hcol m hm x
  have memr : ∀ g ∈ S.map Φ, ∀ y, (fun x => g (x, y)) ∈ V₁ := by
    rintro g ⟨m, hm, rfl⟩ y
    exact hrow m hm y
  let F : S.map Φ →ₗ[ℂ] (T → V₂) :=
    LinearMap.pi fun t => LinearMap.codRestrict V₂
      ((LinearMap.funLeft ℂ ℂ (fun y : Y => ((t : X), y))).comp (S.map Φ).subtype)
      (fun g => mem g.1 g.2 t)
  have hF : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    apply Subtype.ext
    funext p
    obtain ⟨x, y⟩ := p
    have h0 := hT (fun x => g.1 (x, y)) (memr g.1 g.2 y) (by
      intro t ht
      have := congrArg (fun v : T → V₂ => ((v ⟨t, ht⟩ : V₂) : Y → ℂ) y) hg
      simpa [F, LinearMap.funLeft] using this)
    simpa using congrFun h0 x
  exact Module.Finite.of_injective F hF
end

section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem cn_ne {r s : ℕ} (i : Fin r) (j : Fin s) : Fin.castAdd s i ≠ Fin.natAdd r j := fun h => by
  have := congrArg Fin.val h
  simp at this
  omega

private theorem block_embedding_first_val {R : Type} [CommRing R] {r s : ℕ} (m : GL (Fin r) R) :
    (emb (e1 r s) m).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks m.val 0 0 1) := by
  rw [coe_emb]
  ext i j
  induction i using Fin.addCases with
  | left a =>
    induction j using Fin.addCases with
    | left c =>
      have h0 : ext0 (e1 r s) ((m : Matrix (Fin r) (Fin r) R) - 1) (Fin.castAdd s a) (Fin.castAdd s c) =
          ((m : Matrix (Fin r) (Fin r) R) - 1) a c :=
        matrixExtendByZero_apply (e1 r s) _ a c
      simp only [Matrix.add_apply, h0, Matrix.reindex_apply, Matrix.submatrix_apply,
        finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁, Matrix.sub_apply,
        Matrix.one_apply, Fin.castAdd_inj]
      ring
    | right d =>
      have := matrixExtendByZero_apply_of_outside_col (e1 r s) ((m : Matrix (Fin r) (Fin r) R) - 1) (Fin.castAdd s a)
        (j := Fin.natAdd r d) (fun k h => cn_ne k d (by simpa [e1] using h.symm))
      simp [Matrix.reindex_apply, this, Matrix.one_apply, cn_ne]
  | right b =>
    have := extendByZero_apply_eq_zero_of_row_not_mem (e1 r s) ((m : Matrix (Fin r) (Fin r) R) - 1) (i := Fin.natAdd r b)
      (fun k h => cn_ne k b (by simpa [e1] using h.symm)) j
    induction j using Fin.addCases with
    | left c => simp [Matrix.reindex_apply, this, Matrix.one_apply, (cn_ne c b).symm]
    | right d => simp [Matrix.reindex_apply, this, Matrix.one_apply]

private theorem block_embedding_second_val {R : Type} [CommRing R] {r s : ℕ} (m : GL (Fin s) R) :
    (emb (e2 r s) m).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 0 m.val) := by
  rw [coe_emb]
  ext i j
  induction i using Fin.addCases with
  | right a =>
    induction j using Fin.addCases with
    | right c =>
      have h0 : ext0 (e2 r s) ((m : Matrix (Fin s) (Fin s) R) - 1) (Fin.natAdd r a) (Fin.natAdd r c) =
          ((m : Matrix (Fin s) (Fin s) R) - 1) a c :=
        matrixExtendByZero_apply (e2 r s) _ a c
      simp only [Matrix.add_apply, h0, Matrix.reindex_apply, Matrix.submatrix_apply,
        finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂, Matrix.sub_apply,
        Matrix.one_apply, Fin.natAdd_inj]
      ring
    | left d =>
      have := matrixExtendByZero_apply_of_outside_col (e2 r s) ((m : Matrix (Fin s) (Fin s) R) - 1) (Fin.natAdd r a)
        (j := Fin.castAdd s d) (fun k h => cn_ne d k (by simpa [e2] using h))
      simp [Matrix.reindex_apply, this, Matrix.one_apply, (cn_ne d a).symm]
  | left b =>
    have := extendByZero_apply_eq_zero_of_row_not_mem (e2 r s) ((m : Matrix (Fin s) (Fin s) R) - 1) (i := Fin.castAdd s b)
      (fun k h => cn_ne b k (by simpa [e2] using h)) j
    induction j using Fin.addCases with
    | right c => simp [Matrix.reindex_apply, this, Matrix.one_apply, cn_ne b c]
    | left d => simp [Matrix.reindex_apply, this, Matrix.one_apply]

private theorem unip_val {R : Type} [CommRing R] {r s : ℕ} (Y : Matrix (Fin r) (Fin s) R) :
    ∃ X : UPos (r + s) r → R,
      unipMatrix X = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 Y 0 1) := by
  refine ⟨fun p => Y ⟨p.1.1, p.2.1⟩ ⟨p.1.2 - r, by have := p.1.2.isLt; have := p.2.2; omega⟩, ?_⟩
  ext i j
  simp only [unipMatrix, Matrix.add_apply, blockEntry_apply]
  induction i using Fin.addCases with
  | left a =>
    induction j using Fin.addCases with
    | left c =>
      have : ¬ (r ≤ ((Fin.castAdd s c : Fin (r + s)) : ℕ)) := by simp
      simp [this, Matrix.reindex_apply, Matrix.one_apply]
    | right d =>
      have h : ((Fin.castAdd s a : Fin (r + s)) : ℕ) < r ∧ r ≤ ((Fin.natAdd r d : Fin (r + s)) : ℕ) := by
        simp
      rw [dif_pos h]
      simp [Matrix.reindex_apply, Matrix.one_apply, cn_ne]
  | right b =>
    have : ¬ (((Fin.natAdd r b : Fin (r + s)) : ℕ) < r) := by simp
    induction j using Fin.addCases with
    | left c => simp [this, Matrix.reindex_apply, Matrix.one_apply, (cn_ne c b).symm]
    | right d => simp [this, Matrix.reindex_apply, Matrix.one_apply]

theorem UpperTheory.upperTriangular_eq_unipotent_mul_levi :
    ∀ (R : Type) [CommRing R] (r s : ℕ) (b : GL (Fin (r + s)) R), b.val.IsUpperTriangular → ∃ (X : UPos (r + s) r → R) (m₁ : GL (Fin r) R) (m₂ : GL (Fin s) R), b = unipGL X * blk m₁ m₂ := by
  intro R _ r s b hb
  set M : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) R :=
    Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm b.val with hMdef
  have hC : M.toBlocks₂₁ = 0 := by
    ext i j
    simp only [hMdef, Matrix.toBlocks₂₁, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      Matrix.of_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.zero_apply]
    apply hb
    simp [Fin.lt_def]
    omega
  have hM : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    rw [← hC]
    exact (Matrix.fromBlocks_toBlocks M).symm
  have hbM : b.val = Matrix.reindex finSumFinEquiv finSumFinEquiv M := by
    simp [hMdef]
  have hdet : IsUnit (Matrix.det M) := by
    rw [hMdef, Matrix.det_reindex_self]
    exact (Matrix.GeneralLinearGroup.det b).isUnit
  rw [hM, Matrix.det_fromBlocks_zero₂₁] at hdet
  have hA : IsUnit M.toBlocks₁₁.det := isUnit_of_mul_isUnit_left hdet
  have hD : IsUnit M.toBlocks₂₂.det := isUnit_of_mul_isUnit_right hdet
  obtain ⟨X, hX⟩ := unip_val (M.toBlocks₁₂ * M.toBlocks₂₂⁻¹)
  refine ⟨X, Matrix.nonsingInvUnit _ hA, Matrix.nonsingInvUnit _ hD, ?_⟩
  have hmul : ∀ P Q : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) R,
      Matrix.reindex finSumFinEquiv finSumFinEquiv P * Matrix.reindex finSumFinEquiv finSumFinEquiv Q =
        Matrix.reindex finSumFinEquiv finSumFinEquiv (P * Q) := by
    intro P Q
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  apply Units.ext
  rw [Units.val_mul, coe_unipGL, hX, blk, Units.val_mul, block_embedding_first_val, block_embedding_second_val, hbM, ← mul_assoc, hmul, hmul]
  congr 1
  conv_lhs => rw [hM]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  have h1 : (Matrix.nonsingInvUnit _ hA : Matrix (Fin r) (Fin r) R) = M.toBlocks₁₁ := rfl
  have h2 : (Matrix.nonsingInvUnit _ hD : Matrix (Fin s) (Fin s) R) = M.toBlocks₂₂ := rfl
  rw [h1, h2]
  simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hD]
end

section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.finiteDimensional_of_finiteDimensional_levi_slices :
    ∀ (K : Type) [Field K] [NumberField K] (r s : ℕ) (S : Submodule ℂ (archSmooth K (r + s))), S ≤ NInv K (r + s) r → Sat S → Level S → Types S → FiniteDimensional ℂ (slSp (e1 r s) (Set.range (emb (e2 r s))) S) → FiniteDimensional ℂ (slSp (e2 r s) (Set.range (emb (e1 r s))) S) → FiniteDimensional ℂ S := by
  intro K _ _ r s S hN hsat hlev htyp h1 h2
  obtain ⟨V, hVfd, hV⟩ := UpperTheory.exists_finiteDimensional_compact_translates_of_level_types K (r + s) S hlev htyp
  let Φ₀ : archSmooth K (r + s) →ₗ[ℂ] (AdelicGLn.AdelicGL K r × AdelicGLn.AdelicGL K s → ℂ) :=
    { toFun := fun m p => (m : AdelicGLn.AdelicGL K (r + s) → ℂ) (emb (e1 r s) p.1 * emb (e2 r s) p.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let Φ : archSmooth K (r + s) →ₗ[ℂ]
      ((AdelicGLn.AdelicGL K r × AdelicGLn.AdelicGL K s) × (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K (r + s))) → ℂ) :=
    { toFun := fun m p => (m : AdelicGLn.AdelicGL K (r + s) → ℂ) (emb (e1 r s) p.1.1 * emb (e2 r s) p.1.2 * (p.2 : AdelicGLn.AdelicGL K (r + s)))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hfd0 : FiniteDimensional ℂ (Submodule.map Φ₀ S) := by
    refine UpperTheory.finiteDimensional_map_of_separately_finite _ _ _ S Φ₀ ((slSp (e1 r s) (Set.range (emb (e2 r s))) S).map (archSmooth K r).subtype)
      ((slSp (e2 r s) (Set.range (emb (e1 r s))) S).map (archSmooth K s).subtype) inferInstance inferInstance ?_ ?_
    · intro m hm y
      obtain ⟨f, hf, -⟩ := UpperTheory.exists_restriction_blockEmbedding_intertwines_lie K r (r + s) (e1 r s) (emb (e2 r s) y)
      refine Submodule.mem_map.mpr ⟨f m, Submodule.subset_span ⟨m, hm, emb (e2 r s) y, ⟨y, rfl⟩, fun x => hf m x⟩, ?_⟩
      funext x
      change (f m : AdelicGLn.AdelicGL K r → ℂ) x = _
      rw [hf, ← emb_comm]
      rfl
    · intro m hm x
      obtain ⟨f, hf, -⟩ := UpperTheory.exists_restriction_blockEmbedding_intertwines_lie K s (r + s) (e2 r s) (emb (e1 r s) x)
      refine Submodule.mem_map.mpr ⟨f m, Submodule.subset_span ⟨m, hm, emb (e1 r s) x, ⟨x, rfl⟩, fun y => hf m y⟩, ?_⟩
      funext y
      change (f m : AdelicGLn.AdelicGL K s → ℂ) y = _
      rw [hf]
      rfl
  have hfd : FiniteDimensional ℂ (Submodule.map Φ S) := by
    refine UpperTheory.finiteDimensional_map_of_separately_finite _ _ _ S Φ (Submodule.map Φ₀ S) V hfd0 hVfd ?_ ?_
    · intro m hm k
      refine Submodule.mem_map.mpr ⟨rt (k : AdelicGLn.AdelicGL K (r + s)) m, hsat _ k.2 m hm, ?_⟩
      funext x
      change ((rt (k : AdelicGLn.AdelicGL K (r + s)) m : archSmooth K (r + s)) : AdelicGLn.AdelicGL K (r + s) → ℂ) _ = _
      rw [rt_apply]
      rfl
    · intro m hm x
      exact hV m hm (emb (e1 r s) x.1 * emb (e2 r s) x.2)
  refine FiniteDimensional.of_injective (Φ.submoduleMap S) ?_
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hx' : ∀ p, Φ x p = 0 := fun p => congrFun (congrArg Subtype.val hx) p
  apply Subtype.ext
  apply Subtype.ext
  funext g
  obtain ⟨b, hb, k, hk, rfl⟩ := Reduction.exists_adelicBorel_mul_maxCompact g
  obtain ⟨X, m₁, m₂, rfl⟩ := UpperTheory.upperTriangular_eq_unipotent_mul_levi _ r s b (Reduction.mem_adelicBorel.mp hb)
  have hxN := hN x.2
  change ((x : archSmooth K (r + s)) : AdelicGLn.AdelicGL K (r + s) → ℂ) (unipGL X * blk m₁ m₂ * k) = 0
  rw [mul_assoc]
  change (∀ (X : UPos (r + s) r → AdeleRing (𝓞 K) K) g, ((x : archSmooth K (r + s)) : AdelicGLn.AdelicGL K (r + s) → ℂ) (unipGL X * g) = _) at hxN
  rw [hxN]
  exact hx' ((m₁, m₂), ⟨k, hk⟩)
end
