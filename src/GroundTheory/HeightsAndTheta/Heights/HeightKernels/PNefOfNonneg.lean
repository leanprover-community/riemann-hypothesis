module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

namespace NefOfNonnegAlt

theorem geoNum_zero_nonneg {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (V : Ideal (MRing ι)) (a : Fin 0 → K → ℤ) : 0 ≤ geoNum 0 V a := by
  unfold geoNum
  split_ifs
  · exact Int.natCast_nonneg _
  · exact le_rfl

theorem geoNum_one_nonneg {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (V : Ideal (MRing ι)) (a : K → ℤ) (ha : ∀ k, 0 ≤ a k) : 0 ≤ geoNum 1 V (fun _ => a) := by
  unfold geoNum
  split_ifs
  · refine Finset.sum_nonneg fun k _ => mul_nonneg (ha k) ?_
    refine finsum_nonneg fun W => finsum_nonneg fun _ => ?_
    exact mul_nonneg (Int.natCast_nonneg _) (geoNum_zero_nonneg _ _)
  · exact le_rfl

end NefOfNonnegAlt

theorem NefOfNonneg.proof : NefOfNonneg.Statement := by
  intro K _ ι _ P a ha W _ _ _ _
  exact NefOfNonnegAlt.geoNum_one_nonneg W a ha

end GroundTheory.Heights₂.Heights
