module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadraticInductionGL2Alt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ResFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusPowerCompatibility
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SchurTwistHolds
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepIrreducibilityCriterion
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.GaloisRepRankTwoRealOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadBC0OfQuadBaseChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.BcAtt0
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusEigenvaluesTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticSignCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusSignCompatibility
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BaseChangeNoSelfTwistOfFrobeniusSignIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd Formalism.L2.Host.CT UpperTheory.V.Z.Bc

def UpperTheory.V.Z.Bc.CyclicBaseChangeLiftRankTwo : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    [IsGalois F E], (Module.finrank F E).Prime → ∀ π : CuspSub F 2, (CG.mk π).IsRegAlg →
      (∃ η : HChar F, IsNormChar E η ∧ SelfTw (CG.mk π).HasSat η) ∨ ∃ P : CuspSub E 2,
        (∀ (τ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar (τ.comp (algebraMap F E)) m → P.HasInfChar τ m) ∧
        WeakBC (CG.mk π).HasSat (CG.mk P).HasSat

def UpperTheory.V.Z.Bc.QuadLiftRealToComplexRankTwo : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E],
    Module.finrank F E = 2 → ∀ π : TR.CuspSub F 2, π.IsRegAlg →
      (∃ η : HChar F, IsQuadCharOf E η ∧ IsoTwist π η) ∨ ∃ P : CuspSub E 2, Br.IsBC0 π P

theorem UpperTheory.V.Z.Bc.quadLiftRealToComplex_of_base_change (h : Br.QuadBC0) : QuadLiftRealToComplexRankTwo := fun F E _ _ _ _ _ _ _ h2 π hr => h F E h2 2 one_le_two π hr

