module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.BesselNVG
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG
public import Formalism.SharpRestriction.CuspSpanNormBounds.DiscreteSeriesWeylDimension
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DiscreteSeriesUniqueLargeGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FinalClosed
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CoefLoc
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HWExists
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.BesselVectors.Closed
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.BesselVectors.DecLow

@[expose] public section

namespace Formalism.L2.SG.OwnFacts

open Formalism.MainNotions Formalism.MainNotions.S

instance factCoefWeightedLoc : Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc := ⟨ReciprocityTheory.ChartRestriction.DS.coefWeightedLoc⟩

instance factBesselNVGap : Fact Formalism.L2.SG.SplitPrimeNormLemmas.BesselNVGap := ⟨ReciprocityTheory.ChartRestriction.DS.Lap.TopClosed.besselNVG⟩

instance factBesselNVG : Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG := ⟨ReciprocityTheory.ChartRestriction.DS.Lap.TopClosed.besselNVG⟩

instance factDecLow : Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow :=
  ⟨fun k r hk ε lam h H _ _ _ σ hlam hDS hgap hh P hP w₁ w₂ h₁ h₂ =>
    ReciprocityTheory.ChartRestriction.DS.Lap.DecLow.decLow k r hk ε lam h H σ hlam hDS hgap hh P hP w₁ w₂ h₁ h₂⟩

instance factExists : Fact DiscreteSeriesWeylDimension.DiscreteSeriesExistsG := ⟨by
  intro n ε lam hp h hg hthr
  obtain ⟨H, i1, i2, σ, hσ, -⟩ := ReciprocityTheory.ChartRestriction.DS.dsExistsG_closed n ε lam hp h hg hthr
  exact ⟨H, i1, i2, σ, hσ⟩⟩

instance factMultOne : Fact DiscreteSeriesWeylDimension.LowKMultOneG := ⟨ReciprocityTheory.ChartRestriction.DS.final_lowKMultOneG⟩

instance factHighestWeight : Fact DiscreteSeriesWeylDimension.HighestWeightExists :=
  ⟨fun k u h => ReciprocityTheory.ChartRestriction.DS.HW.highest_weight_exists k u h⟩

end Formalism.L2.SG.OwnFacts
