module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
public import Formalism.PairingDivisors.StatementH
import Formalism.PairingDivisors.StatementN
public import Formalism.PairingDivisors.StatementX
import Formalism.QuotientMetricDivisors.Statement

@[expose] public section

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw)
open Formalism.PairingDivisionLocalBalance (Pl wt HtLe meanInf)
open Formalism.L2.Indef Formalism.L2.Indef.Tree

noncomputable section

namespace GlobalTheory.LeafRestExamples

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K}

def truncZero (y : ℝ) : ℤ := if 0 ≤ y then ⌊y⌋ else ⌈y⌉

theorem abs_truncZero_le (y : ℝ) (a : ℤ) :
    |(truncZero y : ℝ)| ≤ |y| ∧ |((a + truncZero y : ℤ) : ℝ)| ≤ |(a : ℝ) + y| + |y| := by
  have key : |(truncZero y : ℝ)| ≤ |y| ∧ |(truncZero y : ℝ) - y| ≤ |y| := by
    unfold truncZero
    split_ifs with h
    · have h1 := Int.floor_le y
      have h2 : (0 : ℝ) ≤ (⌊y⌋ : ℤ) := by exact_mod_cast Int.floor_nonneg.mpr h
      rw [abs_of_nonneg h, abs_of_nonneg h2, abs_of_nonpos (by linarith)]
      constructor <;> linarith
    · push Not at h
      have h1 := Int.le_ceil y
      have h2 : ((⌈y⌉ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast Int.ceil_nonpos.mpr h.le
      rw [abs_of_neg h, abs_of_nonpos h2, abs_of_nonneg (by linarith)]
      constructor <;> linarith
  refine ⟨key.1, ?_⟩
  push_cast
  calc |(a : ℝ) + truncZero y| = |((a : ℝ) + y) + (truncZero y - y)| := by ring_nf
    _ ≤ |(a : ℝ) + y| + |(truncZero y : ℝ) - y| := abs_add_le _ _
    _ ≤ _ := by linarith [key.2]

end GlobalTheory.LeafRestExamples
