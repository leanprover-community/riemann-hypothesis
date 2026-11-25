module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularRepresentationContinuous

@[expose] public section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
open scoped Matrix.Norms.Elementwise
noncomputable section

theorem _root_.GlobalTheory.T.regular_representation_continuous : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ x : Lp V 2 μ, Continuous (fun h : G n => rR μ V h x) ∧ Continuous (fun y : G n => lT μ V y x) := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.translations_strongly_continuous
