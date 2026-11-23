module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubstDualWeylExpressibleMatrixMulClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

theorem _root_.GlobalTheory.T.rowSubstDualWeylExpressible_matrix_mul_closed : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (R : Type) [CommRing R] [Algebra O R] (Y Y' : Matrix (Fin N) (Fin N) R), Expr O N ν R Y → Expr O N ν R Y' → Expr O N ν R (Y * Y') := by
  first | exact @GlobalTheory.GenCoef.expr_mul | exact GlobalTheory.GenCoef.expr_mul | (intros; apply GlobalTheory.GenCoef.expr_mul <;> assumption)
