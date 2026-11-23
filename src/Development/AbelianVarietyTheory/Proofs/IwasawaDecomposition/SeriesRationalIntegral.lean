module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaSeriesIntegralUniformPrimePowerStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaSeriesRationalOnGoodCoversOfUntwistedStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UntwistedThetaRationalOnGoodCoversStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace GlobalTheory

theorem seriesRatS_and_serInt_of_globalArtin :
    GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.SerStd.SeriesRatS ∧ GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt :=
  fun hA => ⟨GlobalTheory.T.thetaSeriesRationalOnGoodCovers_of_untwisted (GlobalTheory.Published.GlobalArtinReciprocity.rayClassFieldSt hA) GlobalTheory.T.untwisted_theta_rational_on_good_covers,
    GlobalTheory.T.thetaSeries_integral_uniform_prime_power⟩

end GlobalTheory
