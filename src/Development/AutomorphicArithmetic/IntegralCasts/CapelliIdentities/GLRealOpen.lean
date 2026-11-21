import Mathlib

section
noncomputable def UpperTheory.Reformulated.B.GeneralLinearGroupOverSubring.glR :
    {K : Type} → [inst : CommRing K] → Subring K → (n : ℕ) → Subgroup (GL (Fin n) K) :=
  fun {K} _ R n =>
  { carrier := {g | (∀ i j, (g : Matrix (Fin n) (Fin n) K) i j ∈ R) ∧
      ∀ i j, ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ R}
    one_mem' := by
      have h : ∀ i j : Fin n, (1 : Matrix (Fin n) (Fin n) K) i j ∈ R := fun i j => by
        rw [Matrix.one_apply]
        split_ifs
        exacts [R.one_mem, R.zero_mem]
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · rw [Units.val_one]
        exact h i j
      · rw [inv_one, Units.val_one]
        exact h i j
    mul_mem' := by
      rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · rw [Units.val_mul, Matrix.mul_apply]
        exact R.sum_mem fun k _ => R.mul_mem (ha i k) (hb k j)
      · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
        exact R.sum_mem fun k _ => R.mul_mem (hb' i k) (ha' k j)
    inv_mem' := by
      rintro a ⟨ha, ha'⟩
      refine ⟨ha', fun i j => ?_⟩
      rw [inv_inv]
      exact ha i j }
end

section
theorem UpperTheory.Reformulated.B.GLRealOpen.glR_open :
    ∀ {K : Type} [inst : CommRing K] [inst_1 : TopologicalSpace K] [IsTopologicalRing K] (R : Subring K),
      IsOpen (↑R : Set K) → ∀ (n : ℕ), IsOpen (↑(UpperTheory.Reformulated.B.GeneralLinearGroupOverSubring.glR R n) : Set (GL (Fin n) K)) := by
  intro K _ _ _ R hR n
  have hM : IsOpen {M : Matrix (Fin n) (Fin n) K | ∀ i j, M i j ∈ R} := by
    have e : {M : Matrix (Fin n) (Fin n) K | ∀ i j, M i j ∈ R}
        = ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) K => M i j) ⁻¹' (R : Set K) := by
      ext M
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rw [e]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact hR.preimage (continuous_id.matrix_elem i j)
  have h1 : Continuous fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) :=
    Units.continuous_val
  have h2 : Continuous fun g : GL (Fin n) K => ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    Units.continuous_coe_inv
  exact (hM.preimage h1).inter (hM.preimage h2)
end
