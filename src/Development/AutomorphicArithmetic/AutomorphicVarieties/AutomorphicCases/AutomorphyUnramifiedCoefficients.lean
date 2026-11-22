module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.RhoKApply

@[expose] public section

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.U3

namespace UpperTheory.V.Aut

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
  {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ)

set_option synthInstance.maxHeartbeats 200000 in
def FinA (g₁ : G ℚ Ω) : Prop :=
  ∀ (U : D.ULoc) (S : D.Ring U g₁), Module.Finite c.O (weightZeroSubalgebra c.O S.r.hom)

end UpperTheory.V.Aut

end
