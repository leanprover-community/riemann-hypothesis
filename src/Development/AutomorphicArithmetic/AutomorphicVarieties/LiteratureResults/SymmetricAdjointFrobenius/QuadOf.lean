import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.SymmetricAdjointFrobenius.PullPar
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.SymmetricAdjointFrobenius.IndInf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.SymmetricAdjointFrobenius.InfEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.SymmetricAdjointFrobenius.UnitTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompR
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsGalRepOfOfIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticSignCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusSignCompatibility

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Lit

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]





private def PlRel (σ : E ≃ₐ[F] E) (w w' : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ x y : 𝓞 E, (y : E) = σ x → (x ∈ w'.asIdeal ↔ y ∈ w.asIdeal)

end Places

section Main

variable {F E : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsTotallyReal E] [Algebra F E] {a : ℕ}

variable (F) in
private def Concl (π : TR.CuspSub E a) : Prop :=
  ((∀ (v v' : InfinitePlace E) (m : Multiset ℂ), v.comap (algebraMap F E) = v'.comap (algebraMap F E) →
      π.HasInfChar v m → π.HasInfChar v' m) ∧
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) →
      ∃ B, π.HasSat w B ∧ π.HasSat w' B) ∨
  ∃ P : TR.CuspSub F (2 * a),
    (∀ (v v' : InfinitePlace E) (m m' : Multiset ℂ), v ≠ v' → v.comap (algebraMap F E) = v'.comap (algebraMap F E) →
      π.HasInfChar v m → π.HasInfChar v' m' → P.HasInfChar (v.comap (algebraMap F E)) (m + m')) ∧
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
      (∀ w' : HeightOneSpectrum (𝓞 E), w' ≠ w → w'.under (𝓞 F) = w.under (𝓞 F) →
        ∃ B B', π.HasSat w B ∧ π.HasSat w' B' ∧ P.HasSat (w.under (𝓞 F)) (B + B')) ∧
      (normV w = normV (w.under (𝓞 F)) ^ 2 → ∃ B B' : Multiset ℂˣ, π.HasSat w (B'.map (· ^ 2)) ∧
        B = B' + B'.map (fun b => -b) ∧ P.HasSat (w.under (𝓞 F)) B)

end Main
