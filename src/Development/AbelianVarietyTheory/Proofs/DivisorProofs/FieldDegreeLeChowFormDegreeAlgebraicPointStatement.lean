module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FieldDegreeLeChowFormDegreeAlgebraicPoint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

theorem _root_.GlobalTheory.T.field_degree_le_chowForm_degree_algebraic_point : ∀ (K : Type) [Field K] [CharZero K] (N δ : ℕ) (y : Fin N → AlgebraicClosure K) (j : Fin N) (f : MvPolynomial (Fin (0 + 1) × Fin N) K), y j = 1 → IsChowFormInt (coneIdeal K y) 0 δ f → Module.finrank K (IntermediateField.adjoin K (Set.range y)) ≤ δ := by
  first | exact @GlobalTheory.CompHt.PointLow.finrank_le_of_isChowFormInt | exact GlobalTheory.CompHt.PointLow.finrank_le_of_isChowFormInt | (intros; apply GlobalTheory.CompHt.PointLow.finrank_le_of_isChowFormInt <;> assumption)
