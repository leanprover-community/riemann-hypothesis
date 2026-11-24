module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MatrixCoefficientFrameChangeDiscreteSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.matrix_coefficient_frame_change_discrete_series : GlobalTheory.Published.DiscreteSeriesUpqUnique → ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ),
    Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
    IsDS ε lam σ → IsDS ε lam σ' →
    ∀ (P P' G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → IsUnit P' → Pᴴ * Formalism.REAL.Jm ε * P = G →
      P'ᴴ * Formalism.REAL.Jm ε * P' = G →
    ∀ (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (ℓ : H' →ₗ[ℂ] ℂ) (v : H'), Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ' ℓ →
      SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ' v → (∀ y ∈ UJset ε, F (P'⁻¹ * y * P') = ℓ (σ' y v)) →
    ∃ (ℓ' : H →ₗ[ℂ] ℂ) (v' : H), Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ ℓ' ∧
      SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ v' ∧ ∀ y ∈ UJset ε, F (P⁻¹ * y * P) = ℓ' (σ y v') := by
  first | exact @GlobalTheory.TypeSum.FrameChange.coef_frame_change | exact GlobalTheory.TypeSum.FrameChange.coef_frame_change | (intros; apply GlobalTheory.TypeSum.FrameChange.coef_frame_change <;> assumption)
