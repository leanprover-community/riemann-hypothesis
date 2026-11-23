module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionMixedIntegral
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionMixedBridge
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionInterpIntegral
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

namespace ResolutionMixedIntegral

theorem proof (hB : ResolutionMixedBridge.Statement) (hI : ResolutionInterpIntegral.Statement) :
    ResolutionMixedIntegral.Statement := by
  intro D Ω _ _ κ _ d m₁ hm₁
  rw [hI D Ω κ d m₁ hm₁]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hM : ∀ j : Fin D, IsSmoothMetric (if j.val < i then m₁ else d.m) := fun j => by
    split_ifs
    · exact hm₁
    · exact d.smooth
  have hpot : mixPot d.m m₁ D i = fun j z => Real.log ((if j.val < i then m₁ else d.m).ρ z) := by
    funext j z
    unfold mixPot
    split_ifs <;> rfl
  have hres : (fun j : Fin D => resPot d (if j.val < i then m₁ else d.m)) =
      fun j : Fin D => if j.val < i then resPot d m₁ else resPot d d.m := by
    funext j
    split_ifs <;> rfl
  rw [hpot, hB D Ω κ d (fun j => if j.val < i then m₁ else d.m) m₁ hM hm₁, hres]

end ResolutionMixedIntegral

end GroundTheory.Heights₂.Heights.HilbertSamuel
