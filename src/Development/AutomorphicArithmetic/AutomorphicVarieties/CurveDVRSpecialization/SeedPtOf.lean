import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ExistsDeterminantPairOverAlgebraicIntegers
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ShapeFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.UniversalMapsPointOfPolarizedFlaggedRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ExistsFrameFactorizationOfTrivialOnInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.DiagonalCharactersRegularAlgebraicOfInertiaWeigh
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqOneOfNear

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr
open Polynomial
open scoped Matrix

set_option linter.overlappingInstances false

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime]















variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
  {k : GalLink η Ψ σ g₁ B M L Φ} {c₁ : Coef l} [Fr.IsCoef l c₁.O] {f : ResidueField c.O →+* ResidueField c₁.O}
  {n : ℕ} {ka : G L Ω →* (Qbar l)ˣ}

private def prT (R : CReal k c₁ f n ka) : G L Ω →* R.T.G.G₀ := R.V.pr



end SlopeTestRemainingChoices

