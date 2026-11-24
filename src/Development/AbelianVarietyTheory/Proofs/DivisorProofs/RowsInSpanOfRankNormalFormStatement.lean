module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowsInSpanOfRankNormalForm
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

open ValuativeRel Matrix


theorem _root_.GlobalTheory.T.rows_in_span_of_rank_normal_form : ∀ (K : Type) [Field K] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (r : ℕ) (X : Matrix A D K) (H : Matrix (Fin r) A K) (Q : Matrix D (Fin r) K), X.rank ≤ r → IsUnit (H * X * Q) → ∀ i, ∃ s : Fin r → K, X i = s ᵥ* (H * X) := by
  first | exact @GlobalTheory.rows_mem_span_of_isUnit_mul | exact GlobalTheory.rows_mem_span_of_isUnit_mul | (intros; apply GlobalTheory.rows_mem_span_of_isUnit_mul <;> assumption)
