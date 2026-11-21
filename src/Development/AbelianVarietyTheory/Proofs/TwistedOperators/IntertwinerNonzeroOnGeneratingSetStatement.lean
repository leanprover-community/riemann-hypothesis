import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerNonzeroOnGeneratingSet
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactUnitaryFiniteInvariantSubspaceStatement
import BuildAid.ForwardExisting

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intertwiner_nonzero_on_generating_set : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsURepOn (UJset ε) ρ → IsIrredOn (UJset ε) ρ → IsURepOn (UJset ε) π → ∀ (T : H →ₗ[ℂ] V) (Y₀ : Set H) (y₀ a₀ : H), y₀ ∈ Y₀ → T y₀ ≠ 0 → (∀ y ∈ Y₀, ∀ g ∈ UJset ε, ⟪a₀, ρ g y⟫_ℂ = ⟪T y₀, π g (T y)⟫_ℂ) → ∃ B : H →L[ℂ] V, B ≠ 0 ∧ ∀ g ∈ UJset ε, ∀ x, B (ρ g x) = π g (B x) := by
  atlas_forward_decl GlobalTheory.GraphIntertwiner.exists_intertwiner
