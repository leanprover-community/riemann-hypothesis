module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.RedAbs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.PlaceFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.DenseOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.RedBChiComap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.CharpolyPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.IrrSmall
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PhiMaps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoAdicCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CrDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.CocRel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.AeComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.CocExt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.OrbitCount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.UnipTorsion
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.FixLe
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.IrrArithPointsAutomorphicAway

@[expose] public section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J UpperTheory.V.Th

namespace UpperTheory.Gal.projectedFormsSystemPart

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
  {k : GalLink η Ψ σ g₁ B M L Φ} {c₁ : Coef l} [Fr.IsCoef l c₁.O] {f : ResidueField c.O →+* ResidueField c₁.O}
  {ka : G L Ω →* (Qbar l)ˣ}

@[reducible] def setS (R : CReal k c₁ f 3 ka) (S : Fr.Space c₁.O (Φ.ext f) 3) : CReal k c₁ f 3 ka := { R with S := S }

end

end UpperTheory.Gal.projectedFormsSystemPart
