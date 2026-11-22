module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymmStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinMapUniqueTransportPlaceIsoStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonUniqueOfInductiveStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalExtensionOfFiniteIndexWeilSubgroupStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneSemisimpleStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateEpsilonTransportStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupRestrictionStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalTraceCompletionStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupTransportStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceBaseChangeFieldStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionBaseChangePlacesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyLinearEquivOfCharpolyEq

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.EpsUnique

section One

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem exists_place (h : IsPlaceOver A w) (L : Type) [Field L] [NumberField L] [Algebra L Ω] [Algebra E L]
    [IsScalarTower E L Ω] : ∃ v : HeightOneSpectrum (𝓞 L), IsPlaceOver A v := by
  have hint : ∀ x : 𝓞 L, algebraMap L Ω x ∈ A := fun x => by
    have h1 : IsIntegral ℤ (algebraMap L Ω x) := x.2.map (algebraMap L Ω).toIntAlgHom
    have h2 : IsIntegral A (algebraMap L Ω x) := h1.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    exact hy ▸ y.2
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A hint
  have hf : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω x) < 1 ↔ x ∈ (IsLocalRing.maximalIdeal A).comap f := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  refine ⟨⟨(IsLocalRing.maximalIdeal A).comap f, inferInstance, fun h0 => ?_⟩, hf⟩
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  have h3 := (hf (algebraMap (𝓞 E) (𝓞 L) x)).1 (by
    have := (h x).2 hx
    rwa [IsScalarTower.algebraMap_apply E L Ω] at this)
  rw [h0, Ideal.mem_bot] at h3
  exact hx0 (FaithfulSMul.algebraMap_injective (𝓞 E) (𝓞 L) (by simpa using h3))

end One

section Two

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
  {φ : Ω ≃+* Ω'} {j : E →+* E'} {i : w.adicCompletion E ≃+* w'.adicCompletion E'}

end Two

end GlobalTheory.LocLanglands.EpsUnique

end
