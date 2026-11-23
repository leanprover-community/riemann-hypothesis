module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulNormDualWeylTensorEvaluationLeFibreNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

theorem _root_.GlobalTheory.T.mul_norm_dualWeylTensorEvaluation_le_fibreNorm : ∀ (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ), (∀ t, Antitone (la t)) → ∀ (x : TIdx la → ℂ) (X : ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ) (u : ∀ t, UN (N t)) (s : ℝ), 0 ≤ s → s * ‖tval la x (fun t => X t * (u t).1)‖ ≤ Real.sqrt (∑ I, ‖(fibY la s X *ᵥ x) I‖ ^ 2) := by
  first | exact @GlobalTheory.TSup.mul_norm_tval_le_fibNorm | exact GlobalTheory.TSup.mul_norm_tval_le_fibNorm | (intros; apply GlobalTheory.TSup.mul_norm_tval_le_fibNorm <;> assumption)
