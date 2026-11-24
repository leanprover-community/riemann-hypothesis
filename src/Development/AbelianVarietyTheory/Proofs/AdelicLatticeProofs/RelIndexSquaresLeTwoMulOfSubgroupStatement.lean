module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexSquaresLeTwoMulOfSubgroup
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

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.relIndex_squares_le_two_mul_of_subgroup : ∀ (G : Type) [CommGroup G] (U H : Subgroup G) (ε : G), H ≤ U → H.relIndex U ≠ 0 → (∀ a : G, a ^ 2 = 1 → a = 1 ∨ a = ε) → (sqs H).relIndex H ≠ 0 → (sqs U).relIndex U ≠ 0 ∧ (sqs U).relIndex U ≤ 2 * (sqs H).relIndex H := by
  first | exact @GlobalTheory.QNorm.relIndex_sqs_le_two_mul | exact GlobalTheory.QNorm.relIndex_sqs_le_two_mul | (intros; apply GlobalTheory.QNorm.relIndex_sqs_le_two_mul <;> assumption)
