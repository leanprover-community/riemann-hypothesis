module

public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableLatticeEqZpowStdInertCompletion
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

@[expose] public section

open IsDedekindDomain NumberField
open scoped Matrix

theorem _root_.GlobalTheory.T.stable_lattice_eq_zpow_std_inert_completion : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (σ : P.adicCompletion E →+* P.adicCompletion E), (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → (∃ x, Valued.v x ≤ 1 ∧ Valued.v (σ x - x) = 1) → ∀ (ϖ : P.adicCompletion E), Valued.v ϖ = WithZero.exp (-1 : ℤ) → ∀ (n : ℕ) (L : AddSubgroup (Fin n → P.adicCompletion E)) (N : P.adicCompletion E), N ≠ 0 → (∀ a : P.adicCompletion E, Valued.v a ≤ 1 → ∀ w ∈ L, a • w ∈ L) → (∀ w : Fin n → P.adicCompletion E, (∀ i, Valued.v (w i) ≤ 1) → N • w ∈ L) → (∀ w ∈ L, ∀ i, Valued.v (N * w i) ≤ 1) → (∀ U : GL (Fin n) (P.adicCompletion E), U ∈ Formalism.UG.UJ σ 1 → (∀ i j, Valued.v (U.1 i j) ≤ 1) → (∀ i j, Valued.v ((U⁻¹).1 i j) ≤ 1) → ∀ w ∈ L, U.1 *ᵥ w ∈ L) → ∃ k : ℤ, ∀ w, w ∈ L ↔ ∀ i, Valued.v (ϖ ^ k * w i) ≤ 1 := by
  first | exact @GlobalTheory.LocLatInert.stable_lattice_eq_zpow_std | exact GlobalTheory.LocLatInert.stable_lattice_eq_zpow_std | (intros; apply GlobalTheory.LocLatInert.stable_lattice_eq_zpow_std <;> assumption)
