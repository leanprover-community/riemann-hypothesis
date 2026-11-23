module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Trace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualFrameSpanUnitaryRepresentation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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


theorem _root_.GlobalTheory.T.exists_dual_frame_span_unitary_representation : ∀ {G H : Type} [Mul G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (K : Set G) (ρ : G → (H →ₗ[ℂ] H)) (hmul : ∀ g ∈ K, ∀ h ∈ K, g * h ∈ K)
    (hρ : ∀ g ∈ K, ∀ h ∈ K, ρ (g * h) = ρ g ∘ₗ ρ h)
    (hadj : ∀ g ∈ K, ∃ g' ∈ K, LinearMap.adjoint (ρ g) = ρ g'), ∃ (m : ℕ) (k : Fin m → G) (B : Fin m → (H →ₗ[ℂ] H)), (∀ j, k j ∈ K) ∧
      (∀ A : H →ₗ[ℂ] H, ∀ g ∈ K, LinearMap.trace ℂ H (ρ g ∘ₗ A) =
        ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ A) * LinearMap.trace ℂ H (ρ g ∘ₗ B j)) ∧
      (∀ i, ∀ h ∈ K, B i ∘ₗ ρ h = ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ (B i ∘ₗ ρ h)) • B j) := by
  first | exact @GlobalTheory.DualFrameSpan.dual_frame | exact GlobalTheory.DualFrameSpan.dual_frame | (intros; apply GlobalTheory.DualFrameSpan.dual_frame <;> assumption)
