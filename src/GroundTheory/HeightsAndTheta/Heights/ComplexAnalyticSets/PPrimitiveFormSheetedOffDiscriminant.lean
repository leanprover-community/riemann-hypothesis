module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormSheetedLocusCutOut
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormSheetedPointsNear
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormSheetedOffDiscriminant
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem PrimitiveFormSheetedOffDiscriminant.proof (hcut : PrimitiveFormSheetedLocusCutOut.Statement)
    (hnear : PrimitiveFormSheetedPointsNear.Statement) : PrimitiveFormSheetedOffDiscriminant.Statement := by
  intro σ _ X w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hP hsep hQ
  obtain ⟨c, e, hc, he, hce, hsh⟩ := hcut σ X w d A hX hiso ℓ N a δ q ha hδ hq hδ0 hP hsep hQ
  rcases hirr.2 c e hc he hce with hc0 | he0
  · exact ⟨_, hc0.and hsh, fun y hy hyδ => ((hy.2.2 hy.1 hyδ).1).2 (hy.2.1 hy.1)⟩
  · exfalso
    obtain ⟨z, hz, hzδ, hzs⟩ :=
      hnear σ X w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hP hsep hQ _ (he0.and hsh)
    exact (hz.2.2 hz.1 hzδ).2 hzs (hz.2.1 hz.1)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
