module

public import Mathlib.RingTheory.Ideal.Height
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureHeightEqOneOfLiesOver
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CupPair
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap

@[expose] public section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.height_eq_one_of_liesOver_height_one : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (A : Subalgebra k F) [IsFractionRing A F] (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → Q.height = 1 := by
  first | (exact @GlobalTheory.integralClosure_height_eq_one_of_liesOver) | (exact GlobalTheory.integralClosure_height_eq_one_of_liesOver) | (intros; apply GlobalTheory.integralClosure_height_eq_one_of_liesOver  <;> assumption)
