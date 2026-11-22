module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramOfHermitianSelfDualLatticeSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop

@[expose] public section

noncomputable section

namespace GlobalTheory.LatHatClosed

open scoped TensorProduct RestrictedProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU Topology

variable (F : Type) [Field F] [NumberField F]

theorem isCompact_integralFinite :
    IsCompact {b : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), b.1 v ∈ v.adicCompletionIntegers F} := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

end GlobalTheory.LatHatClosed
