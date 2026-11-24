module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftColumnsMulVecInjectiveOfRankEqCard
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
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

theorem _root_.GlobalTheory.T.leftColumns_mulVec_injective_of_rank_eq_card : ∀ (k m a b n : Type) [Field k] [Fintype m] [Fintype a] [Fintype b] [Fintype n] (e : a ⊕ b ≃ n) (x : Matrix m n k), x.rank = Fintype.card a → (∀ i j, x i (e (Sum.inr j)) = 0) → ∀ v : a → k, (x.submatrix id (fun i => e (Sum.inl i))) *ᵥ v = 0 → v = 0 := by
  first | exact @GlobalTheory.mulVec_firstCols_eq_zero_of_rank_eq_card | exact GlobalTheory.mulVec_firstCols_eq_zero_of_rank_eq_card | (intros; apply GlobalTheory.mulVec_firstCols_eq_zero_of_rank_eq_card <;> assumption)
