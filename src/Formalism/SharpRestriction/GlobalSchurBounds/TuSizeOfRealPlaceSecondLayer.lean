module

public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
public import Formalism.SharpRestriction.GlobalSchurBounds.LogXLowerFamilyOfTheorems
public import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
public import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.SecondBranchAllMembers
public import Formalism.LocalToGlobal.GlobalTheory.GL4.LowerSlopeInequalityFamily
public import Formalism.LocalToGlobal.GlobalTheory.GL4.PStmtFree
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PacketStatementOfIndependence
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IntegralAtT0Lattice
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalLinkOfBranchIdentitiesAndMultiplicity
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Formalism.SharpRestriction.GlobalSchurBounds.RamifiedLevelZeroHolds
public import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfGappedMultiplicity
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

@[expose] public section

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT

variable {eps : ℝ}


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem Wire.famGLmin_of_realPlaceSecondLayer (𝒞 : FamClass) (tie : Closed 𝒞 fun Fm _ => RealPlaceSecondLayerConditions Fm)
    (hU : ∀ D, MassRatioUnderVolume D) (hG : ∀ D, GenusMassVolumes.GenusMassAt D 2) :
    Wire.FamGLmin 𝒞 4 := by
  exact {
    h2b := Closed.of_all fun Fm _ => GenusMassVolumes.siegel_mass_ratio_family Fm
    h2v := tie.imp fun Fm _ _ t => family_property_mono (family_conditions_of_layer_two Fm t).1 fun D hT =>
      GenusMassVolumes.volume_eq_mass_rank_two D (StandardLattice.volumeMass_of_unfolding D (hU D hT)) (GenusMassVolumes.volume_mass_of_genus_rank D 2 hT (hG D))
    h3 := Closed.of_all fun Fm _ => GappedMultiplicityBounds.explicit_bound_family Fm
    hZa := Closed.of_all fun Fm _ => TraceIntegrality.lower_slope_inequality_family Fm
    hZb := Closed.of_all fun Fm _ => TraceIntegrality.slope_inequality_family_four Fm
    tCV := tie.imp fun Fm _ _ t => tCV_of_ties Fm (family_conditions_of_layer_two Fm t).2.1
    hW := tie.imp fun Fm _ _ t =>
      (slope_free_branch_family Fm (family_conditions_of_layer_two Fm t).2.2 freeTT_holds slopeLineT_holds LemB.second_branch_all_members).1
    hμ := tie.imp fun Fm _ _ t =>
      (slope_free_branch_family Fm (family_conditions_of_layer_two Fm t).2.2 freeTT_holds slopeLineT_holds LemB.second_branch_all_members).2.1
    hI := tie.imp fun Fm _ _ t => hI_tied Fm (family_conditions_of_layer_two Fm t).2.2 PI.IntegralAtBasePointLattice.integral_at_t0_lattice
    hR := tie.imp fun Fm _ _ t => ramified_level_zero_holds Fm (family_conditions_of_layer_two Fm t).2.2
    hB := tie.imp fun Fm _ _ t =>
      (slope_free_branch_family Fm (family_conditions_of_layer_two Fm t).2.2 freeTT_holds slopeLineT_holds LemB.second_branch_all_members).2.2
  }

end Formalism.MainNotions

end
