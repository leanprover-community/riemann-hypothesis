module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published

namespace UpperTheory.V.Z.Bc

instance factTwo : Fact ((2 : ℕ) = 2) := ⟨rfl⟩

def QuadBC2 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E],
    Module.finrank F E = 2 → ∀ π : TR.CuspSub F 2, π.IsRegAlg →
      (∃ η : HChar F, IsQuadCharOf E η ∧ IsoTwist π η) ∨ ∃ P : CuspSub E 2, IsBC π P

end UpperTheory.V.Z.Bc
