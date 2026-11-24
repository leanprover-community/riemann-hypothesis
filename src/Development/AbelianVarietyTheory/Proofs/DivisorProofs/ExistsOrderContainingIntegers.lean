module

public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTChartExistsHolds
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

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_order_containing_integers : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] (OB : Subring B), Module.Finite ℤ OB →
    (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ OB) →
    ∃ Λ : Subring B, OB ≤ Λ ∧ (∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) ∧
      Module.Finite ℤ Λ ∧ ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Λ, (N : B) * x ∈ OB := by
  first | (exact @GlobalTheory.exists_order_integers_mul_finite_index) | (exact GlobalTheory.exists_order_integers_mul_finite_index) | (intros; apply GlobalTheory.exists_order_integers_mul_finite_index  <;> assumption)
