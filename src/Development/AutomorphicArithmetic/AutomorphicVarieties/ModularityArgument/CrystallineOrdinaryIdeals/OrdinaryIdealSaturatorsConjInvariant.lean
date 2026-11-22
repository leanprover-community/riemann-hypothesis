module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.GaloisSubgroupLBasicProperties
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ChosenFrobeniusIsFrobenius

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

section Conj

variable {C : Type} [CommRing C]

theorem ent_mem_mul {J : Ideal C} {N : Matrix (Fin 3) (Fin 3) C} (hN : ∀ i j, N i j ∈ J)
    (A B : Matrix (Fin 3) (Fin 3) C) (i j : Fin 3) : (A * N * B) i j ∈ J := by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _
    (Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ (hN m k))

theorem conj_sub_scalar (h : GL (Fin 3) C) (M : Matrix (Fin 3) (Fin 3) C) (c : C) :
    (h : Matrix (Fin 3) (Fin 3) C) * M * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) - Matrix.scalar _ c =
      (h : Matrix (Fin 3) (Fin 3) C) * (M - Matrix.scalar _ c) * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
  have e : (h : Matrix (Fin 3) (Fin 3) C) * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Matrix.mul_sub, Matrix.sub_mul, ← (Matrix.scalar_commute c (fun _ => Commute.all _ _) (h : Matrix (Fin 3) (Fin 3) C)),
    Matrix.mul_assoc (Matrix.scalar _ c), e, Matrix.mul_one]

theorem conj_mul_three_alt (h : GL (Fin 3) C) (A B E : Matrix (Fin 3) (Fin 3) C) :
    ((h : Matrix (Fin 3) (Fin 3) C) * A * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)) *
      ((h : Matrix (Fin 3) (Fin 3) C) * B * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)) *
      ((h : Matrix (Fin 3) (Fin 3) C) * E * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)) =
      (h : Matrix (Fin 3) (Fin 3) C) * (A * B * E) * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
  have e : ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * (h : Matrix (Fin 3) (Fin 3) C) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) (h : Matrix (Fin 3) (Fin 3) C), e, Matrix.one_mul,
    ← Matrix.mul_assoc ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) (h : Matrix (Fin 3) (Fin 3) C), e, Matrix.one_mul]

theorem unconj (h : GL (Fin 3) C) (M : Matrix (Fin 3) (Fin 3) C) :
    M = ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) *
      ((h : Matrix (Fin 3) (Fin 3) C) * M * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)) * (h : Matrix (Fin 3) (Fin 3) C) := by
  have e : ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) * (h : Matrix (Fin 3) (Fin 3) C) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [Matrix.mul_assoc]
  rw [e, Matrix.mul_one, ← Matrix.mul_assoc, e, Matrix.one_mul]

theorem trace_conj (h : GL (Fin 3) C) (M : Matrix (Fin 3) (Fin 3) C) :
    ((h : Matrix (Fin 3) (Fin 3) C) * M * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)).trace = M.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem charpoly_conj (h : GL (Fin 3) C) (M : Matrix (Fin 3) (Fin 3) C) :
    ((h : Matrix (Fin 3) (Fin 3) C) * M * ((h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C)).charpoly = M.charpoly := by
  rw [Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj h M

end Conj

end GlobalTheory.OrdLoc

namespace GlobalTheory.OrdLoc

end GlobalTheory.OrdLoc
