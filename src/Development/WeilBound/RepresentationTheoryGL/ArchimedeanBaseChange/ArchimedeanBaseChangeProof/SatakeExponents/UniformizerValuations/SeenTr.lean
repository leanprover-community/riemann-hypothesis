module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameL
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace PositivityTheory.Rg.BcB.F

def LocData.IsLetter {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (d : LocData E n) (a : ℕ) (ha : a ≤ n)
    (L : LM d.kap a (n - a)) : Prop :=
  d.IsGen a ha L ∨ (∃ L', d.IsGen a ha L' ∧ L = L'.adj) ∨ L = d.betaL a ha ∨ L = d.fixL a

def SeenTr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : LocData E n), d.Ok → ∀ a (ha : a ≤ n)
  (ls : List (LM d.kap a (n - a))) (N : ∀ w, d.kap w → d.kap w → ℂ), (∀ L ∈ ls, d.IsLetter a ha L) → ∀ w ∈ d.B,
    (ls.foldr LM.mul (d.eL a)).t w = idem (d.lev₂ a w) ∧
    ((w ∈ d.T → ¬ GlobalTheory.UnitaryBC.IsSplitAt w) →
      seen ((ls.foldr LM.mul (d.eL a)).tr d.P N) (ls.foldr LM.mul (d.eL a)).t w = (ls.foldr LM.mul (d.eL a)).tr d.P N w)

end PositivityTheory.Rg.BcB.F

end
