module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.GalN.V UpperTheory.V.Z.Win

set_option linter.unusedVariables false

namespace UpperTheory.V.Z.Win.Dn

local instance tf (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] : Module.IsTorsionFree L Ω := DivisionSemiring.to_moduleIsTorsionFree

def IneOfKer : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)), (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∃ χ : G F Ω →* (Qbar l)ˣ, Continuous χ ∧
      (χ '' (Ine (F := F) A : Set (G F Ω))).Finite ∧ ∀ g ∈ Ine (F := F) A, χ g = 1 → r g = 1) → IneAb r

def FlagAll : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)), (∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ A : ValuationSubring Ω,
      IsPlaceOver A w ∧ ∃ κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ, IsFlagOn r (Dec (F := F) A) κ) → Flagged r

end UpperTheory.V.Z.Win.Dn
