module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Interval.Finset.Nat
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

namespace Formalism.CG

open Finset

def HCrank (k t j : ℕ) : ℕ := k + j * (t + 1)

def HCparam (k t : ℕ) (u e : ℕ → ℚ) (l : ℕ) : ℚ :=
  if l ≤ k then u l
  else -e ((l - k - 1) / (t + 1) + 1) + (t : ℚ) / 2 - (((l - k - 1) % (t + 1) : ℕ) : ℚ)

def HCnu (k t : ℕ) (u e : ℕ → ℚ) (j l : ℕ) : ℚ :=
  HCparam k t u e l - ((HCrank k t (j - 1) : ℚ) + 1 - 2 * (l : ℚ)) / 2 + e j
    - (HCrank k t j : ℚ) / 2

def HCdeg (k t : ℕ) (u e : ℕ → ℚ) (j : ℕ) : ℚ :=
  ∑ l ∈ Icc 1 (HCrank k t (j - 1)), HCnu k t u e j l

def HCsparam (k t j : ℕ) (v b e : ℕ → ℚ) (l : ℕ) : ℚ :=
  if l + 1 ≤ k then v (l + 1)
  else if l + 1 ≤ k + j then -b (l + 1 - k)
  else if l + 1 ≤ k + j + t then -e j + ((t : ℚ) - 1) / 2 - (((l + 1 - (k + j) : ℕ) : ℚ) - 1)
  else -b (l + 1 - k - t)

def HCkap (k t m j : ℕ) (v b e : ℕ → ℚ) (l : ℕ) : ℚ :=
  HCsparam k t j v b e l - (((k : ℚ) + m + t - 1) + 1 - 2 * (l : ℚ)) / 2
    + (e j - (t : ℚ) / 2 + ((k : ℚ) + m + t - 1) / 2 - ((k : ℚ) + j - 1))

def HCDplus (k t m j : ℕ) (v b e : ℕ → ℚ) : ℚ := ∑ l ∈ Ico 1 (k + j), HCkap k t m j v b e l

def HCDminus (k t m j : ℕ) (v b e : ℕ → ℚ) : ℚ :=
  ∑ l ∈ Ico (k + j + t) (k + m + t), -HCkap k t m j v b e l

end Formalism.CG
