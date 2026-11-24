module

public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbstractCompleteReducibility
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


theorem _root_.GlobalTheory.T.mem_iSup_irreducible_of_fixed_projector : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] (P : Submodule ℂ E → Prop),
    (∀ s : Set (Submodule ℂ E), (∀ A ∈ s, P A) → P (sInf s)) →
    ∀ (N : Submodule ℂ E), P N → ∀ (b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ), (∀ x ∈ N, x ≠ 0 → 0 < (b x x).re) →
    (∀ x ∈ N, ∀ y ∈ N, star (b x y) = b y x) →
    (∀ A : Submodule ℂ E, A ≤ N → P A → P (N ⊓ ⨅ a ∈ A, LinearMap.ker (b a))) →
    ∀ (e : E →ₗ[ℂ] E), (∀ A : Submodule ℂ E, A ≤ N → P A → ∀ x ∈ A, e x ∈ A) → (∀ x ∈ N, e (e x) = e x) →
    (∀ x ∈ N, ∀ y ∈ N, b (e x) y = b x (e y)) → FiniteDimensional ℂ (N.map e) →
    ∀ ψ ∈ N, e ψ = ψ →
    ψ ∈ ⨆ (A : Submodule ℂ E) (_ : A ≤ N ∧ P A ∧ A ≠ ⊥ ∧ ∀ B : Submodule ℂ E, B ≤ A → P B → B = ⊥ ∨ B = A), A := by
  first | exact @GlobalTheory.abstract_complete_reducibility | exact GlobalTheory.abstract_complete_reducibility | (intros; apply GlobalTheory.abstract_complete_reducibility <;> assumption)
