module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WordDerivatives
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuadraticGelfandInvariantEqNegSumSqDefinite
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.quadraticGelfandInvariant_eq_neg_sum_sq_definite : ∀ (n : ℕ) (J B : Matrix (Fin n) (Fin n) ℂ), IsUnit B.det → (J = Bᴴ * B ∨ J = -(Bᴴ * B)) → ∃ X : Fin n × Fin n × Bool → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, Submodule.span ℝ (Set.range X) = ⊤ ∧ ∀ P Q : Fin n → Fin n → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J, (∀ a b, (P a b).1 = (1 / 2 : ℂ) • (Matrix.single a b 1 + -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J)) ∧ (Q a b).1 = (1 / (2 * Complex.I)) • (Matrix.single a b 1 - -(J⁻¹ * (Matrix.single a b (1 : ℂ))ᴴ * J))) → ∀ (A : Type) [Ring A] [Algebra ℂ A] (ρ : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU J → A), (∀ Y Z, ρ (Y + Z) = ρ Y + ρ Z) → (∀ (c : ℝ) Y, ρ (c • Y) = (c : ℂ) • ρ Y) → ∑ a, ∑ b, (ρ (P a b) + Complex.I • ρ (Q a b)) * (ρ (P b a) + Complex.I • ρ (Q b a)) = -∑ i, ρ (X i) * ρ (X i) := by
  exact @GlobalTheory.DefiniteUnitaryCasimir.casimir_eq_neg_sum_sq
