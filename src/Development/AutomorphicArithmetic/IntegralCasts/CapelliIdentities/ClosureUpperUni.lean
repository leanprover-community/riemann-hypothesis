module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.LinearAlgebra.Matrix.Block
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.LocLemma

@[expose] public section

noncomputable def UpperTheory.Reformulated.B.Qe27.upperUni :
    (k : ℕ) → (A : Type) → [inst : CommRing A] → Set (GL (Fin k) A) :=
    fun (k : ℕ) (A : Type) [CommRing A] ↦
      {x : GL (Fin k) A |
        ∀ (i j : Fin k),
          (j < i → (↑x : Matrix (Fin k) (Fin k) A) i j = (0 : A)) ∧ (↑x : Matrix (Fin k) (Fin k) A) i i = (1 : A)}

private theorem UpperTheory.Reformulated.B.Qe27.mem_iff {k : ℕ} {A : Type} [CommRing A] (x : GL (Fin k) A) :
    x ∈ UpperTheory.Reformulated.B.Qe27.upperUni k A ↔
      (x : Matrix (Fin k) (Fin k) A).BlockTriangular id ∧
        ∀ i, (x : Matrix (Fin k) (Fin k) A) i i = 1 :=
  ⟨fun h => ⟨fun i j hij => (h i j).1 hij, fun i => (h i i).2⟩,
    fun h i _ => ⟨fun hij => h.1 hij, h.2 i⟩⟩

theorem UpperTheory.Reformulated.B.Qe27.closure_upperUni :
    ∀ {k : ℕ} (A : Type) [inst : CommRing A],
      ∀ x ∈ Subgroup.closure (UpperTheory.Reformulated.B.Qe27.upperUni k A), x ∈ UpperTheory.Reformulated.B.Qe27.upperUni k A := by
  intro k A _ x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hy
  | one =>
    rw [UpperTheory.Reformulated.B.Qe27.mem_iff]
    exact ⟨Matrix.blockTriangular_one, fun i => Matrix.one_apply_eq i⟩
  | mul y z _ _ hy hz =>
    rw [UpperTheory.Reformulated.B.Qe27.mem_iff] at hy hz ⊢
    rw [Units.val_mul]
    refine ⟨hy.1.mul hz.1, fun i => ?_⟩
    rw [UpperTheory.Reformulated.B.Qk9.tri_diag _ _ hy.1 hz.1, hy.2, hz.2, one_mul]
  | inv y _ hy =>
    rw [UpperTheory.Reformulated.B.Qe27.mem_iff] at hy ⊢
    have hinv : ((y⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A).BlockTriangular id := by
      letI : Invertible (y : Matrix (Fin k) (Fin k) A) := y.invertible
      rw [Matrix.coe_units_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular hy.1
    refine ⟨hinv, fun i => ?_⟩
    have h := UpperTheory.Reformulated.B.Qk9.tri_diag _ _ hy.1 hinv i
    rw [Units.mul_inv, Matrix.one_apply_eq, hy.2, one_mul] at h
    exact h.symm
