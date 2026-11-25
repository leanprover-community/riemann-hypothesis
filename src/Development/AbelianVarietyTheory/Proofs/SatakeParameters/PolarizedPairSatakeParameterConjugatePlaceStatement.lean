module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairSatakeParameterConjugatePlace
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.Published

theorem _root_.GlobalTheory.T.polarizedPair_satakeParameter_conjugatePlace : AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), GlobalTheory.ContraPair.PolarizedPair π χ → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ B : Multiset ℂˣ, (CG.mk π).HasSat w B → (CG.mk π).HasSat (UpperTheory.V.Af.Bc.cPl w) (B.map fun α => α⁻¹ * (compNorm E χ).val w) := by
  first | exact @GlobalTheory.PolarizedSat.hasSat_conjPlace
