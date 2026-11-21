import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjGelfValOfIsHerm

section
theorem GlobalTheory.CompanionTheory.ModelS.gelfVal_perm :
    ∀ (n : ℕ) (χ : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (k : ℕ),
      GlobalTheory.Dec.gelfVal (fun a => χ (σ a)) k = GlobalTheory.Dec.gelfVal χ k :=
  fun _ χ σ k => GlobalTheory.CompanionTheory.WaveMult.gelfVal_comp_perm χ σ k
end

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_value_perm_invariant : ∀ (n : ℕ) (χ : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (k : ℕ), GlobalTheory.Dec.gelfVal (fun a => χ (σ a)) k = GlobalTheory.Dec.gelfVal χ k := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ModelS.gelfVal_perm
