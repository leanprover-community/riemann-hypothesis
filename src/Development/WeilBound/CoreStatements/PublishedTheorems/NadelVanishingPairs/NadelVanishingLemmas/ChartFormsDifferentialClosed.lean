module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFormsDifferentialClosed
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open GlobalTheory GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.chart_forms_differential_closed : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (r : Fin n → ℕ), AlgChart A x → ∀ q, ∀ η ∈ chartForms A x J (t ^ p * ∏ j ∈ J, x j ^ r j) q, extD K η ∈ chartForms A x J (t ^ p * ∏ j ∈ J, x j ^ r j) (q + 1) := by
  first | exact @_root_.GlobalTheory.LogDR.extD_mem_chartForms_twist | exact _root_.GlobalTheory.LogDR.extD_mem_chartForms_twist | (intros; apply _root_.GlobalTheory.LogDR.extD_mem_chartForms_twist <;> assumption)
