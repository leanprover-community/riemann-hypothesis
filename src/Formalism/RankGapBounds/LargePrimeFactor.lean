module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
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

open Real Finset

namespace Formalism.RankGapBounds.ChebyshevFactorialBounds

noncomputable section

def primesUpTo (X : ℕ) : Finset ℕ := (Finset.range (X + 1)).filter Nat.Prime

structure Data (ι : Type) where

  T2 : Finset ι

  Nr : ℕ
  k : ℕ
  t : ℕ
  m : ℕ
  h : ℕ
  S : ℕ
  eta' : ℕ
  Wthin : ℕ
  D0 : ℕ
  lJ : ℝ
  Kexc : ℝ
  q : ι → ℕ
  j : ι → ℕ
  xlo : ι → ℤ
  xhi : ι → ℤ
  maxB : ι → ℤ
  Exc : Finset ℕ
  Bad : Finset ℕ
  J : ℕ → ℕ
  ex : ι → ℕ → ℕ
  ecl : ι → ℕ → ℕ
  erest : ι → ℕ → ℕ
  mw : ι → ℕ → ℕ
  mwF : ι → ℕ → ℕ

namespace Data

end Data

def ChebyshevTheta : Prop :=
  ∀ n : ℕ, ∑ p ∈ primesUpTo n, Real.log (p : ℝ) ≤ Real.log 4 * (n : ℝ)

end

end Formalism.RankGapBounds.ChebyshevFactorialBounds
