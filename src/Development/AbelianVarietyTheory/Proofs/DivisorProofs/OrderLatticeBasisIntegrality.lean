module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Fintype.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogPeriodFamily
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.order_lattice_basis_integrality : ∀ {A B : Type} [Ring A] [CommRing B] (j : B →+* A) (Λ : Set A) (R : Set B) (r : ℕ) (e : Fin r → A),
    (0 : A) ∈ Λ → (1 : A) ∈ Λ → (∀ x ∈ Λ, ∀ y ∈ Λ, x + y ∈ Λ) → (∀ x ∈ Λ, -x ∈ Λ) →
    (∀ x ∈ Λ, ∀ y ∈ Λ, x * y ∈ Λ) →
    (0 : B) ∈ R → (1 : B) ∈ R → (∀ x ∈ R, ∀ y ∈ R, x + y ∈ R) → (∀ x ∈ R, -x ∈ R) →
    (∀ x ∈ R, ∀ y ∈ R, x * y ∈ R) →
    (∀ a : A, ∃! β : Fin r → B, a = ∑ i, j (β i) * e i) →
    (∀ β : Fin r → B, (∑ i, j (β i) * e i ∈ Λ) ↔ ∀ i, β i ∈ R) →
    (∀ i i' : Fin r, ∃ (N : ℕ) (ρ : Fin N → B) (μ : Fin N → A), (∀ k, ρ k ∈ R) ∧ (∀ k, μ k ∈ Λ) ∧
      ∀ β : Fin r → B, ∑ k, j (ρ k) * (∑ i'', j (β i'') * e i'') * μ k = j (β i') * e i) →
    (∀ a : A, ∃ D : ℤ, D ≠ 0 ∧ (D : A) * a ∈ Λ) →
    (∀ I : Set B, (0 : B) ∈ I → (∀ x ∈ I, ∀ y ∈ I, x + y ∈ I) → (∀ ρ ∈ R, ∀ x ∈ I, ρ * x ∈ I) →
      (∃ D : ℤ, D ≠ 0 ∧ (∀ x ∈ R, (D : B) * x ∈ I) ∧ ∀ x ∈ I, (D : B) * x ∈ R) →
      ∃ m : Bˣ, ∀ x, x ∈ I ↔ ∃ ρ ∈ R, x = ↑m * ρ) →
    ∀ X : Aˣ, (∀ ρ ∈ R, (X : A) * j ρ * ↑X⁻¹ ∈ Λ) → ∃ m : Bˣ, (X : A) * j ↑m ∈ Λ ∧ j ↑m⁻¹ * ↑X⁻¹ ∈ Λ := by
  first | (exact @GlobalTheory.AbsLattice.exists_unit_of_conj_stable) | (exact GlobalTheory.AbsLattice.exists_unit_of_conj_stable) | (intros; apply GlobalTheory.AbsLattice.exists_unit_of_conj_stable  <;> assumption)
