module

public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.LocConstChar
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset
public import GroundTheory.AutomorphicForms.FiniteLengthLattice
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreRepresentationSmoothStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible

@[expose] public section

noncomputable section

namespace PositivityTheory.KCo

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
open scoped TensorProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem top_of_map {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (Φ : V →ₗ[ℂ] U) {R N : Submodule ℂ V}
    (hK : ∀ f, Φ f = 0 → f ∈ R) (hR : R ≤ N) (h : N.map Φ = ⊤) : N = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv : Φ v ∈ N.map Φ := by rw [h]; exact Submodule.mem_top
  obtain ⟨n, hn, hnv⟩ := hv
  have hker : v - n ∈ N := hR (hK _ (by rw [map_sub, hnv, sub_self]))
  have := N.add_mem hker hn
  simpa using this

end PositivityTheory.KCo
