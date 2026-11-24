module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.GM

open Finset Polynomial

def DetBlockLead : Prop :=
  ∀ (K : Type) [CommRing K] (n : ℕ) (A : Matrix (Fin n) (Fin n) K[X]) (D : ℕ) (e : Fin n → ℕ),
    (∀ i, e i ≤ D) → (∀ i j, (A i j).natDegree + max (e i) (e j) ≤ D) →
      (A.det).natDegree ≤ ∑ i, (D - e i) ∧
      (A.det).coeff (∑ i, (D - e i)) =
        (Matrix.of fun i j => if e i = e j then (A i j).coeff (D - e i) else 0).det ∧
      ((Matrix.of fun i j => if e i = e j then (A i j).coeff (D - e i) else 0).det ≠ 0 →
        (A.det).natDegree = ∑ i, (D - e i) ∧
        (A.det).leadingCoeff = (Matrix.of fun i j => if e i = e j then (A i j).coeff (D - e i) else 0).det)

noncomputable def vmin (p : ℕ) {K : Type} [NormedField K] (h : ℕ) (x : K) : ℝ :=
  -Real.logb p (max ‖x‖ ((p : ℝ) ^ (-(h : ℤ))))




end Formalism.GM
