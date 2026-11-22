module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2Compat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2Glue

@[expose] public section

section Helpers
open IsLocalRing Matrix UpperTheory.V.Hi

section Top

variable {Q : Type} {G : Q → Type} [∀ q, Group (G q)] [∀ q, TopologicalSpace (G q)] [∀ q, IsTopologicalGroup (G q)]

end Top

end Helpers

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ)
  (a : H.Op → c.O) {R : Type} [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq)
  (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ)

end

