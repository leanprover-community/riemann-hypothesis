import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthCharacterEquality
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
noncomputable section

namespace GlobalTheory.HeckeCharacterEquality

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

def _root_.UpperTheory.GalS.HeckeCharacterEqualityOfRealisation : Prop :=
  ∀ D : D7, Formalism.MainNotions.SumRepresentations.admitted D → ∀ (i : D.nd.Loc) (χ χ' : D.naut.CG 1) (s : ℝ)
    (ρ : G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i))),
    (∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
      UpperTheory.GalS.RelW D.nd D.naut (D.naut.wdOf i ρ w) (D.naut.lpTw (D.naut.locG χ w) s)) →
    (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG χ' w) s) →
    χ = χ'


end GlobalTheory.HeckeCharacterEquality

end
