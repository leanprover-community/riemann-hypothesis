module

public import Formalism.GaussJetBounds.OneLetterGaussJets.OddLevelGainSum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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

def PropSix7 : Prop :=
  ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d →
    ∀ (TT : Finset (ZMod d)) (k : ℕ) (D w E : ZMod d → ℝ), 3 ≤ k →
      (∀ s, 0 < w s) → (∀ s, 0 ≤ E s ∧ E s ≤ 4 * w s) →
      (∀ s, s ∉ TT → D s = ((k : ℝ) - 1) * w s + E s) →
      (∀ s, s ∈ TT → D s = ((k : ℝ) - 1) * w s - 2 * w s + E s) →
      Fnum l d (fun s => ((k : ℝ) - 1) * w s) - 2 * gam l * (∑ s ∈ TT, w s) -
          8 / (l : ℝ) * (∑ s : ZMod d, w s) ≤ Fnum l d D ∧
        Fnum l d (fun s => ((k : ℝ) - 1) * w s) - 11 / (l : ℝ) * (∑ s : ZMod d, w s) ≤
          Fnum l d (fun s => ((k : ℝ) - 1) * w s) - 2 * gam l * (∑ s ∈ TT, w s) -
            8 / (l : ℝ) * (∑ s : ZMod d, w s)

def GainDominatesInnerSum : Prop :=
  ∀ (l d : ℕ) [NeZero d], 2 ≤ l → ∀ (TT : Finset (ZMod d)) (nu1 nu2 : ZMod d → ℕ) (s : ZMod d),
    oddLevelGainSum l d TT nu1 nu2 s ≤ topTerm l d TT nu1 nu2 s

def NormCor7 : Prop :=
  ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d →
    ∀ (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ) (k : ℕ) (L : ℝ)
      (w E : ZMod d → ℝ) (pi y : ℝ), 0 < pi → pi < 1 → 3 ≤ k →
      (∀ s, 0 < w s) → (∀ s, 0 ≤ E s ∧ E s ≤ 4 * w s) →
      (∀ s, s ∉ TT → (Dl d TT nu1 size s : ℝ) = ((k : ℝ) - 1) * w s + E s) →
      (∀ s, s ∈ TT → (Dl d TT nu1 size s : ℝ) = ((k : ℝ) - 1) * w s - 2 * w s + E s) →
      y ≤ pi ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s - gam l * (WcapOneLetter l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) - L) →
      y ≤ pi ^ ((∑ s ∈ TT, oddLevelGainSum l d TT nu1 nu2 s) + Fnum l d (fun s => ((k : ℝ) - 1) * w s) -
          11 / (l : ℝ) * (∑ s : ZMod d, w s) -
          gam l * (∑ s ∈ TT, (WcapOneLetter l d TT nu1 nu2 size s : ℝ)) - L)

end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
