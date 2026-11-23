module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HypA
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OfClassification
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsFinDimLink
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MassRatioAllUnramifiedCmFields
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscreteSeriesThreeOfHyp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalIdealSt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW

@[expose] public section

section
open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.LiteralAutomorphy
namespace GlobalTheory
theorem compatibleSystem_hypotheses_of_localInputs : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.DiscreteSeriesCoverExists → GlobalTheory.Published.FormalDegreeCompactDual → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Mem.Top.Bl.HypAAlt :=
  fun ar cm we hm cd cw hf cl ce fd sw =>
    have c := GlobalTheory.DiscreteSeriesConsequences.of_classification cl
    have u : GlobalTheory.Published.DiscreteSeriesUpqUnique := GlobalTheory.Published.discreteSeriesUpqUnique_of_classification cl
    have d := GlobalTheory.discreteSeries_three_of_hypotheses ce c.2.2.2.2 u
    ⟨ar.rayClassFieldSt, ar.principalIdealSt, cm, hm, cd, cw, GlobalTheory.weilRepresentationUnitaryPair, c.2.2.1, hf, c.2.1, u,
      GlobalTheory.rowsFinDim_link, sw, c.2.2.2.2, fd, GlobalTheory.Mass.massRatio_all_unramified_cmFields,
      d.1, d.2.1, d.2.2, ar, we⟩
end GlobalTheory
end

section
open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.LiteralAutomorphy

theorem _root_.GlobalTheory.T.compatibleSystem_member_hypotheses : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.DiscreteSeriesCoverExists → GlobalTheory.Published.FormalDegreeCompactDual → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Mem.Top.Bl.HypAAlt := by
  first | exact @_root_.GlobalTheory.compatibleSystem_hypotheses_of_localInputs | exact _root_.GlobalTheory.compatibleSystem_hypotheses_of_localInputs | (intros; apply _root_.GlobalTheory.compatibleSystem_hypotheses_of_localInputs <;> assumption)
end
