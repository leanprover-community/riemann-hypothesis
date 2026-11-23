module

public import Formalism.GaussJetBounds.OneLetterGaussJets.StatementN
public import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.CompanionTheory
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

universe u v w

namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds

open Formalism.IncomingBounds

theorem propSix7 : PropSix7 := proposition_six
theorem gain_dominates_oddLevel_sum : GainDominatesInnerSum := gain_ge_inner_sum
theorem normCor7 : NormCor7 := by
  intro l d _ hl hd he TT nu1 nu2 size k L w E pi y hpi0 hpi1 hk hw hE hD1 hD2 hy
  refine hy.trans (Real.rpow_le_rpow_of_exponent_ge hpi0 hpi1.le ?_)
  have h6 := propSix7 l d hl hd he TT k (fun s => (Dl d TT nu1 size s : ℝ)) w E hk hw hE hD1 hD2
  have hsum : ∑ s ∈ TT, oddLevelGainSum l d TT nu1 nu2 s ≤ ∑ s ∈ TT, topTerm l d TT nu1 nu2 s :=
    Finset.sum_le_sum fun s _ => gain_dominates_oddLevel_sum l d (by omega) TT nu1 nu2 s
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  linarith [h6.1, h6.2]

end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
