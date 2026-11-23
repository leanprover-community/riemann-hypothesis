module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BilinearBoundOfDenseSecondSlot
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


theorem _root_.GlobalTheory.T.exists_seminorm_bound_of_dense_second_slot : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E]
    {p : ℕ → Seminorm ℂ E}, WithSeminorms p →
    ∀ {X₁ X₂ : Type} [AddCommGroup X₁] [Module ℂ X₁] [AddCommGroup X₂] [Module ℂ X₂]
    (j₁ : X₁ →ₗ[ℂ] E) (j₂ : X₂ →ₗ[ℂ] E), Function.Injective j₁ → IsClosed (Set.range j₁) →
    ∀ (D₂ : Submodule ℂ X₂), (∀ x, j₂ x ∈ closure (j₂ '' (D₂ : Set X₂))) →
    ∀ (F : X₁ →ₗ[ℂ] X₂ →ₗ[ℂ] E),
    (∀ w i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ b, p i (F w b) ≤ q (j₂ b)) →
    (∀ a ∈ D₂, ∀ i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, p i (F w a) ≤ q (j₁ w)) →
    ∀ b i, ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, p i (F w b) ≤ q (j₁ w) := by
  first | exact @GlobalTheory.bilinear_bound_of_dense_right | exact GlobalTheory.bilinear_bound_of_dense_right | (intros; apply GlobalTheory.bilinear_bound_of_dense_right <;> assumption)
