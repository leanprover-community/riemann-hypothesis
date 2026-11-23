module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorValueOfTriangularLaw
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

theorem _root_.GlobalTheory.T.exists_tensor_value_of_triangular_law : ∀ (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ) (K : Type) [Field K] [CharZero K] (G : MvPolynomial (Formalism.L2.LamCM.FrVar N) K), (∀ y b : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K, (∀ t, (y t).det ≠ 0) → (∀ t, (b t).BlockTriangular id ∧ ∀ i, b t i i ≠ 0) → Formalism.L2.LamCM.evalFr G (fun t => y t * b t) = (∏ t, diagChar (la t) (b t)) * Formalism.L2.LamCM.evalFr G y) → ∃ x : TIdx la → K, ∀ (S : Type) [CommRing S] (φ : K →+* S) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) S), Formalism.L2.LamCM.evalFr (MvPolynomial.map φ G) y = tval la (fun I => φ (x I)) y := by
  first | exact @GlobalTheory.TensorValue.exists_tval_of_triangular | exact GlobalTheory.TensorValue.exists_tval_of_triangular | (intros; apply GlobalTheory.TensorValue.exists_tval_of_triangular <;> assumption)
