module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorEvaluationTranslateKronecker
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

theorem _root_.GlobalTheory.T.dualWeylTensorEvaluation_translate_kronecker : ∀ (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ) (K S : Type) [Field K] [CharZero K] [CommRing S] (φ : K →+* S) (x : TIdx la → K) (g : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) S), tval la (fun I => φ (x I)) (fun t => (g t).map φ * y t) = tval la (fun I => φ (((kron fun t => rhoMat (la t) (g t)) *ᵥ x) I)) y := by
  first | exact @GlobalTheory.DefPt.tval_translate | exact GlobalTheory.DefPt.tval_translate | (intros; apply GlobalTheory.DefPt.tval_translate <;> assumption)
