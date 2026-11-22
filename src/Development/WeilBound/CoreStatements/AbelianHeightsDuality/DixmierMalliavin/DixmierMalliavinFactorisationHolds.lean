module

public import GroundTheory.AutomorphicForms.DixmierMalliavin
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedMatrixSubgroupTheorem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlueSmoothOfCompactSupportStatement
import CompanionTheory.AutomorphicTheory.PadicUnitaryWeights.DixmierMalliavin.DixmierMalliavinFactorisationHolds

@[expose] public section

namespace PositivityTheory.DM

open GroundTheory.Automorphic GroundTheory.Automorphic.IsExpLieAlgebra GlobalTheory.Orb
open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory Filter

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]

theorem factor_abs {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (ι : G →* 𝔸) (hι : Topology.IsClosedEmbedding (ι.toHomUnits : G → 𝔸ˣ)) (μ : Measure G) [μ.IsHaarMeasure]
    {V : Set G} (hV : V ∈ 𝓝 1) {f : G → ℂ} (hf : f ∈ CcSmooth fun g => ι g) :
    ∃ (N : ℕ) (g k : Fin N → G → ℂ),
      (∀ i, g i ∈ CcSmooth (fun g => ι g) ∧ k i ∈ CcSmooth (fun g => ι g) ∧ tsupport (g i) ⊆ V ∧
        tsupport (k i) ⊆ tsupport f) ∧ f = ∑ i, GlobalTheory.AutomorphicL2Unitary.conv μ (g i) (k i) :=
  by apply _root_.CompanionTheory.DM.factor_abs <;> assumption

end PositivityTheory.DM

open GlobalTheory.Orb in
theorem PositivityTheory.DM.dixmierMalliavinFactorisation_holds : GlobalTheory.Published.DixmierMalliavinFactorisation := by
  intro G _ _ _ _ _ n _ _ ι hι μ _ V hV f hf
  letI := Matrix.linftyOpNormedRing (n := n) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := n) (α := ℂ)
  haveI : CompleteSpace (Matrix n n ℂ) := FiniteDimensional.complete ℝ _
  let T : (n → n → ℂ) ≃L[ℝ] Matrix n n ℂ := (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv
  have e : CcMat ι = CcSmooth fun g => ι g :=
    le_antisymm (ccSmooth_le (p := T.symm) T.symm.contDiff fun _ => rfl) (ccSmooth_le (p := T) T.contDiff fun _ => rfl)
  rw [e] at hf ⊢
  exact PositivityTheory.DM.factor_abs ι hι μ hV hf
