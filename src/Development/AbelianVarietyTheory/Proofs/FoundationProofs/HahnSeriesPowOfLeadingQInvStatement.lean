module

public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesPowOfLeadingQInv
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ

theorem _root_.GlobalTheory.T.hahnSeries_pow_of_leading_qInv : ∀ {R : Type} [CommRing R] (x : HahnSeries ℚ R), x.coeff (-1) = 1 → (∀ r : ℚ, r < -1 → x.coeff r = 0) → ∀ m : ℕ, (x ^ m).coeff (-(m : ℚ)) = 1 ∧ ∀ r : ℚ, r < -(m : ℚ) → (x ^ m).coeff r = 0 := by
  first | exact @GlobalTheory.hahn_pow_neg_one_lead | exact GlobalTheory.hahn_pow_neg_one_lead | (intros; apply GlobalTheory.hahn_pow_neg_one_lead <;> assumption)
