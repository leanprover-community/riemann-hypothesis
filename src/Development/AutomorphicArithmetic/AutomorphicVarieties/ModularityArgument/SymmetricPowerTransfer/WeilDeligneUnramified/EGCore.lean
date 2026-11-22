module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PrOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PlainAtRTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ClosedHeckeCosets.IsClosedSmall
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.PropEC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.TieS
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.NeZeroRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.GoodHalf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.BadAbs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.RootOfSmul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.SplitTwo
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RwOfOrdForm
public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SeedDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.DirOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EPrim
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdAway
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdAbove
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ShapeFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
public import Mathlib.Topology.Algebra.ClopenNhdofOne

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published

namespace UpperTheory.V.Sd.EG

section Norm

variable {l : ℕ} [hl : Fact l.Prime]

end Norm

section Gal

variable {l : ℕ} [hl : Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

end Gal

end UpperTheory.V.Sd.EG

open UpperTheory.V.Sd in
def UpperTheory.V.Z.Sym.W.PropEGc : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω), UpperTheory.V.Sd.IsCC c →
    ∀ (N w : ℕ) (φ θ : G ℚ Ω →* (Qbar l)ˣ), SlopeTestRemainingChoices N w θ → SplitAt N w φ → φ ≠ 1 → ∃ k₀ : ℕ, ∀ k ≥ k₀, φ c = (-1) ^ k →
      ∃ ρ, EisRep ι φ θ k ρ ∧ UpperTheory.V.Z.Win.Birth.PR ι ρ ∧ UpperTheory.GalN.V.RW ι ρ ∧ UpperTheory.V.Z.Sym.Unl.NoHalf ι ρ
