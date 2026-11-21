import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.DenseRangeUnitsR
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.AlgCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticSignCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusSignCompatibility
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSSRepTraceNondegenerate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusRestrictScalarsPowModInertia

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V.Base
open scoped Pointwise

private def IndCh {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] (e : Γ' →* Γ) (r : Γ' →* GL (Fin 2) k)
    (R : Γ →* GL (Fin 4) k) : Prop :=
  ∀ t : Γ, t ∉ e.range →
    (∀ g g' : Γ', e g' = t⁻¹ * e g * t → (R (e g) : Matrix (Fin 4) (Fin 4) k).charpoly =
      (r g : Matrix (Fin 2) (Fin 2) k).charpoly * (r g' : Matrix (Fin 2) (Fin 2) k).charpoly) ∧
    ∀ g : Γ', e g = t * t →
      (R t : Matrix (Fin 4) (Fin 4) k).charpoly = (r g : Matrix (Fin 2) (Fin 2) k).charpoly.comp (X ^ 2)

section Grp

variable {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {e : Γ' →* Γ} {δ : Γ →* kˣ}




end Grp

section Places

variable {F E Ω : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
  [IsScalarTower F E Ω]

omit [NumberField F] in
private theorem val_lt (A : ValuationSubring Ω) (t : G F Ω) (y : Ω) :
    (t⁻¹ • A).valuation y < 1 ↔ A.valuation (t y) < 1 := by
  have hm : ∀ x, x ∈ t⁻¹ • A ↔ t x ∈ A := fun x => ValuationSubring.mem_inv_pointwise_smul_iff
  rw [valuation_lt_one_iff', valuation_lt_one_iff', hm, hm, map_inv₀, map_eq_zero_iff _ t.injective]




omit [NumberField F] [NumberField E] in
private theorem frob_emb {A : ValuationSubring Ω} {q : ℕ} {g : G E Ω} (h : IsFrob (F := F) A q (galEmb F E Ω g)) :
    IsFrob (F := E) A q g := ⟨h.1, h.2⟩








end Places








