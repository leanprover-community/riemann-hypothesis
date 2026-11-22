module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsEigvec

@[expose] public section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.V.UnitaryThreeInertia.exists_canon :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (X : Matrix (Fin 3) (Fin 3) R), (∀ a b, a ≠ b → IsUnit (X a a - X b b)) → (∀ a b, a ≠ b → X a b ∈ maximalIdeal R) → ∃ h, Canon X h :=
  _root_.UpperTheory.Reformulated.B.Qf19.exists_canon
