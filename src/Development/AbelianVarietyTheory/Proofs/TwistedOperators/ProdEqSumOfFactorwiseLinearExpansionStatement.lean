module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdEqSumOfFactorwiseLinearExpansion
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


theorem _root_.GlobalTheory.T.prod_eq_sum_of_factorwise_linear_expansion : ∀ (K : Type) [Fintype K] (X : K → Type) (I : Type) (S : Finset I) (x : I → ℂ) (a : ∀ n, I → X n → ℂ) (b : K → I → ℂ) (A : ∀ n, X n → ℂ) (B : K → ℂ), (∀ n (y : I → ℂ), (∀ q, ∑ i ∈ S, y i * a n i q = 0) → ∑ i ∈ S, y i * b n i = 0) → (∀ n (y : I → ℂ), (∀ q, A n q = ∑ i ∈ S, y i * a n i q) → B n = ∑ i ∈ S, y i * b n i) → (∀ q : ∀ n, X n, ∏ n, A n (q n) = ∑ i ∈ S, x i * ∏ n, a n i (q n)) → (∀ n, Nonempty (X n)) → ∏ n, B n = ∑ i ∈ S, x i * ∏ n, b n i := by
  first | exact @GlobalTheory.prod_eq_sum_of_factorwise_expansion | exact GlobalTheory.prod_eq_sum_of_factorwise_expansion | (intros; apply GlobalTheory.prod_eq_sum_of_factorwise_expansion <;> assumption)
