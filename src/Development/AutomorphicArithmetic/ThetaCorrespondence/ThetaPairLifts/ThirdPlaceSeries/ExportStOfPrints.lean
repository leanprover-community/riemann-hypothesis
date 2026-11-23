module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdaptExStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseGeOfStepsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CanExHoldsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CanProjStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjBaseOfStepsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSeriesStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowAtHoldsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecSideOfTwAdmStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieRatOfStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwAdmStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwChrOfTwAdmStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwGeStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwLeStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwOneOfStepsStatement
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



section
set_option autoImplicit false
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp
theorem exportSt_of_hypotheses_alt (hC : GlobalTheory.Published.CuspRapidDecay) (hA : GlobalTheory.Published.GlobalArtinReciprocity)
    (hR : GlobalTheory.Published.RayClassFieldSt) (hD : GlobalTheory.Published.DiscreteSeriesCover) (hW : GlobalTheory.Published.CasselmanWallach)
    (hS : GlobalTheory.SerStd.SeriesRatS) : _root_.GlobalTheory.BigOn.ExportedStatement :=
  have tA := _root_.GlobalTheory.T.twist_admissible'
  have tC := _root_.GlobalTheory.T.twist_character_of_artin' hA tA
  have row := _root_.GlobalTheory.T.at_statement_of_low_weight_twAdm hC hA hR hS _root_.GlobalTheory.T.lowAt tA
  _root_.GlobalTheory.BigOn.Exp.InductionConditions.exportSt ⟨_root_.GlobalTheory.T.bigOn_canEx, _root_.GlobalTheory.T.bigOn_canProj, tA, row, _root_.GlobalTheory.T.tieRat_of_twAdm_and_at tA row, _root_.GlobalTheory.T.reciprocity_side_of_twAdm tA, _root_.GlobalTheory.T.adaptEx',
    _root_.GlobalTheory.T.conjBase_of_ray_class_field_and_seriesRat hC hA hR hS, _root_.GlobalTheory.T.conjTw_of_discrete_series_and_casselman_wallach hC hA hR hD hW hS tA tC, _root_.GlobalTheory.T.baseLe_of_cuspRapidDecay_artin_rayClassField hC hA hR, _root_.GlobalTheory.T.baseGe_of_cuspRapidDecay_artin_rayClassField_seriesRat hC hA hR hS,
    _root_.GlobalTheory.T.twist_upper_bound_of_prints hC hA hR tA tC, _root_.GlobalTheory.T.twist_lower_bound_of_prints hC hA hR hS tA tC⟩
end GlobalTheory.BigOn.Exp
end
