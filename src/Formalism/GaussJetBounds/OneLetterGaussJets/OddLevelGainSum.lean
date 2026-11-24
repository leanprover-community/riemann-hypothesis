module

public import Formalism.IncomingBounds.IncomingBound
public import Mathlib.Data.Set.Card
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

noncomputable section
open scoped BigOperators

universe u v w

namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds

open Formalism.IncomingBounds

section TopData

variable (l d : ℕ) [NeZero d] (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ)

def WcapOneLetter (s : ZMod d) : ℕ :=
  sSup ((fun i : ℕ => capL d TT nu1 nu2 (s - (i : ZMod d))) ''
    {i : ℕ | Odd i ∧ l ^ i ≤ Dl d TT nu1 size (s - (i : ZMod d))})

def IsLabOneLetter (s s0 : ZMod d) (j : ℤ) : Prop :=
  s0 ∈ TT ∧ Odd j ∧ s = s0 + (j : ZMod d) ∧ (0 < j → l ^ j.toNat ≤ nu1 s0) ∧
    (j < 0 → l ^ (-j).toNat ≤ Dl d TT nu1 size s)

def JnumOneLetter (s : ZMod d) : ℕ :=
  Set.ncard {q : ZMod d × ℤ | IsLabOneLetter l d TT nu1 size s q.1 q.2}

def kaMaxOneLetter : ℕ := max (TT.sup nu1) (Finset.univ.sup (capL d TT nu1 nu2))


open Classical in
def oddLevelGainSum (s : ZMod d) : ℝ :=
  ∑' e : ℕ,
    if Odd e ∧ ¬ (∃ s' ∈ TT, IsLeast {e' : ℕ | Odd e' ∧ s + (e' : ZMod d) = s'} e) then
      max (((nu1 s : ℝ) - nu2 s) / (l : ℝ) ^ e - capL d TT nu1 nu2 (s + (e : ZMod d))) 0
    else 0

end TopData

end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
