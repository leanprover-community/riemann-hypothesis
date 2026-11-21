import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.RankFourAutomorphyOfTensor
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PlainAtRTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PotOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SymmetricCubeUnits.Sym3AutKOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.NormOneOfFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.IsAlgOfPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.FrobDual
open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published
open scoped Matrix

namespace UpperTheory.V.Sd

section CongLemmas

variable {l : ℕ} [Fact l.Prime]













variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]





end CongLemmas

section Gal

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]


omit [IsAlgClosure ℚ Ω] in
private theorem cc_sq {c : G ℚ Ω} (h : IsCC c) : c * c = 1 := by
  obtain ⟨j, hj⟩ := h
  ext x
  apply j.injective
  rw [AlgEquiv.mul_apply, hj, hj]; simp

omit [IsAlgClosure ℚ Ω] in
private theorem cc_not_mem (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Algebra K Ω] {c : G ℚ Ω} (h : IsCC c) :
    c ∉ galOf ℚ K Ω := by
  obtain ⟨j, hj⟩ := h
  intro hc
  refine IsTotallyComplex.complexEmbedding_not_isReal (j.comp (algebraMap K Ω)) ?_
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hj, hc x]




end Gal

section Shape

variable {l : ℕ} [Fact l.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]








end Shape

section Up

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]





end Up

end UpperTheory.V.Sd
