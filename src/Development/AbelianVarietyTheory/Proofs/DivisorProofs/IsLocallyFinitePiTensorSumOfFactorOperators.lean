module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilRepresentationExists
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.PrimesInProgressionNonempty
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SiegelWeilAnisotropicUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LowerLiftsZeroOfWittIdxEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableEmbeddingEquiv
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BorelCasselman
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsIrrKSubOfIsKTypeOf
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesLowestKTypeOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KudlaSplittingSplitUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ExistsMemIdealInvariants
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HermitianHassePrincipleHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.PlaneFormNondegenerate
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.ThetaRationalInvarianceHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RealLift

theorem atPl_mem_range_map {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (L : ∀ i, Module.End ℂ (V i)) (N : ∀ i, Submodule ℂ (V i)) (hN : ∀ i, ∀ y ∈ N i, L i y ∈ N i)
    (w : ι) (y : ⨂[ℂ] i, V i) (hy : y ∈ LinearMap.range (PiTensorProduct.map fun i => (N i).subtype)) :
    atPl w (L w) y ∈ LinearMap.range (PiTensorProduct.map fun i => (N i).subtype) := by
  obtain ⟨t, rfl⟩ := hy
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    have hx : ∀ j, (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w (L w) j) (x j : V j) ∈ N j := by
      intro j
      by_cases h : j = w
      · subst h
        simp only [Function.update_self]
        exact hN j _ (x j).2
      · simp only [Function.update_of_ne h, LinearMap.id_apply]
        exact (x j).2
    refine ⟨r • PiTensorProduct.tprod ℂ (fun j => (⟨_, hx j⟩ : N j)), ?_⟩
    simp [atPl, PiTensorProduct.map_tprod]
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _)]
    exact Submodule.add_mem _ ha hb

theorem locFin_sumPl : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (L : ∀ i, Module.End ℂ (V i)), (∀ i, GlobalTheory.RealLift.LocFin (L i)) →
    GlobalTheory.RealLift.LocFin (GlobalTheory.RealLift.sumPl L) := by
  intro ι _ _ V _ _ L hL v
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    choose N hNf hfN hN using fun i => hL i (f i)
    refine ⟨LinearMap.range (PiTensorProduct.map fun i => (N i).subtype), inferInstance, ?_, ?_⟩
    · exact ⟨r • PiTensorProduct.tprod ℂ (fun i => (⟨f i, hfN i⟩ : N i)), by simp [PiTensorProduct.map_tprod]⟩
    · intro y hy
      rw [sumPl, LinearMap.sum_apply]
      exact Submodule.sum_mem _ fun w _ => atPl_mem_range_map L N hN w y hy
  | add a b ha hb =>
    obtain ⟨N₁, h₁, ha₁, hs₁⟩ := ha
    obtain ⟨N₂, h₂, hb₂, hs₂⟩ := hb
    refine ⟨N₁ ⊔ N₂, inferInstance, Submodule.add_mem_sup ha₁ hb₂, ?_⟩
    intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hs₁ y₁ hy₁) (hs₂ y₂ hy₂)

end GlobalTheory.RealLift
