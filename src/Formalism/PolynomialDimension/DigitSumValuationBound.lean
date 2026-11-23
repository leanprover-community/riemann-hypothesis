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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

def lgSeg (p : ℕ) (a : ℝ) (r : ℕ) : ℝ := Real.logb p (8 * a + r) + 1

def kapSeg (p : ℕ) (a : ℝ) (r s : ℕ) : ℝ := 3 * ((s : ℝ) + 2) * (r : ℝ) ^ 2 * lgSeg p a r

def epsSeg (S Y' κ lg E : ℝ) : ℝ := 2 * S / Y' + (2 * κ + 2 * S * lg / Y') / E

def DetLeadDiag : Prop :=
  ∀ (K : Type) [Field K] (n J : ℕ) (A : Matrix (Fin n) (Fin n) (Polynomial K)) (d : Fin n → K),
    (∀ a b, (A a b).natDegree ≤ J) → (∀ a b, (A a b).coeff J = if a = b then d a else 0) →
    A.det.natDegree ≤ n * J ∧ A.det.coeff (n * J) = ∏ a, d a

end Formalism.CountingSumsFrames
