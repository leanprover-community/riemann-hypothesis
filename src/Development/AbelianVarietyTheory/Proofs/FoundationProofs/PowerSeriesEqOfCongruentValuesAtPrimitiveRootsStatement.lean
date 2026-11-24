module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HTLawAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesEqOfCongruentValuesAtPrimitiveRoots
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod

@[expose] public section

open GlobalTheory.KZ GlobalTheory.Ord2 UpperTheory.V.HV Formalism.ConjugateSelfDual PowerSeries

theorem _root_.GlobalTheory.T.powerSeries_eq_of_congruent_values_at_primitiveRoots : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (A B : PowerSeries (Qbar l)) (u : Qbar l) (w : ℕ → Qbar l) (c₀ m₀ : ℕ), (∀ n, A.coeff n ∈ c.O) → (∀ n, B.coeff n ∈ c.O) → B ≠ 0 → ‖u‖ = 1 → (∀ m, ‖w m‖ = 1 ∧ Cg m (w (m + 1)) (w m)) → (∀ m, m₀ ≤ m → ∀ z : Qbar l, IsPrimitiveRoot z (l ^ m) → Cg (m / 2 - c₀) (tval A (l ^ (3 * m)) z) (w m * u ^ m * tval B (l ^ (3 * m)) z)) → u = 1 ∧ ∀ k : ℕ, ∃ m₁ : ℕ, ∀ m, m₁ ≤ m → ∀ n, Cg k (A.coeff n) (w m * B.coeff n) := by
  first | exact @GlobalTheory.KZ.autoPin_congr | exact GlobalTheory.KZ.autoPin_congr | (intros; apply GlobalTheory.KZ.autoPin_congr <;> assumption)
