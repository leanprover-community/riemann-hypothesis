module

public import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem dens (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hCut : CutoffStatement n M) (hUR : UnweightRelStatement n M)
    (hUB : UnweightBackStatement n M) (hLoc : LocalizeStatement n M)
    (hCh : ChartFlatStatement n M) : DensStatement n M := by
  intro z hz e ph ψ he hph hψ hcut f w σ hf hw hσ hadj hone
  refine hCut z hz e ph ψ he hph hψ hcut ?_ f w σ hf hw hσ hadj hone
  intro f w σ hf hw hσ hadj hone hcf hcw hcσ
  obtain ⟨hG, hD, hS, hdiv, hdbar, hcG, hcD, hcS⟩ :=
    hUR z hz ph ψ f w σ hph hψ hf hw hσ hadj hone
  refine hUB z hz ph ψ f w σ hph hψ hf hw hσ hcf hcw hcσ ?_
  exact hLoc z hz (fun e' G D S he' => hCh z hz e' G D S he') _ _ _ hG hD hS hdiv hdbar
    (hcG hcf) (hcD hcw) (hcS hcf hcσ)

end

end ReciprocityTheory.L2DbarEstimates.F
