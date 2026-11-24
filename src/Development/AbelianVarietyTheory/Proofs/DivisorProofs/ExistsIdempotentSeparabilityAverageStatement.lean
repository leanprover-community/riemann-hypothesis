module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Ideal.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentSeparabilityAverage
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_idempotent_separability_average : ∀ (C O : Type) [CommRing C] [Ring O] (I : Ideal C), I ^ 2 = ⊥ → ∀ (N : ℤ) (k : ℕ) (x y : Fin k → O), ∑ j, x j * y j = (N : O) → (∀ c : O, ∑ j, (c * x j) ⊗ₜ[ℤ] y j = ∑ j, x j ⊗ₜ[ℤ] (y j * c)) → IsUnit (N : C) → ∀ (H : Type*) [AddCommGroup H] [Module C H] (ρ : O →+* Module.End C H) (ε : Module.End C H), ε * ε = ε → (∀ c, ρ c * ε = ε * ρ c) → ∀ F : Submodule C H, I • ⊤ ≤ F → (∀ c, ∀ x ∈ F, ρ c x ∈ F) → (∀ x ∈ F, ε x ∈ F) → (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) → ∃ π : Module.End C H, π * π = π ∧ (∀ c, ρ c * π = π * ρ c) ∧ π * ε = π ∧ ε * π = π ∧ (∀ z, ε z = z → z - π z ∈ F) ∧ (∀ z ∈ F, ε z = z → π z ∈ I • (⊤ : Submodule C H)) := by
  first | exact @GlobalTheory.SepAverage.exists_idempotent_average | exact GlobalTheory.SepAverage.exists_idempotent_average | (intros; apply GlobalTheory.SepAverage.exists_idempotent_average <;> assumption)
