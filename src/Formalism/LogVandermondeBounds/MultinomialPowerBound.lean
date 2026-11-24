module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Factorial.Basic
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

namespace Formalism.LogVandermondeBounds.flipTwoThree

open Finset

def Interlace {n : ℕ} (lam : Fin (n + 1) → ℤ) (nu : Fin n → ℤ) : Prop :=
  Antitone lam ∧ ∀ i : Fin n, lam i.succ ≤ nu i ∧ nu i ≤ lam i.castSucc

def B0 {n : ℕ} (lam : Fin (n + 1) → ℤ) (nu : Fin n → ℤ) : ℤ := ∑ i, (nu i - lam i.succ)

def len {n : ℕ} (lam : Fin (n + 1) → ℤ) (i : Fin n) : ℤ := lam i.castSucc - lam i.succ

noncomputable def hookF {N : ℕ} (nu : Fin N → ℕ) : ℝ :=
  (∏ i : Fin N, ((nu i + N - 1 - i : ℕ).factorial : ℝ)) /
    ∏ i : Fin N, ∏ j ∈ univ.filter (fun j => i < j), (((nu i : ℤ) - nu j + j - i : ℤ) : ℝ)

end Formalism.LogVandermondeBounds.flipTwoThree
