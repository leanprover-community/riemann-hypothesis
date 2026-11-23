module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesRationalIntegral
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BadStOfBadW
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BadWStOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompareOffOwnAtRuns
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExponentBoundOfUnitaryThetaStandardTheorems
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportStOfReadingStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoStOfPageSt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MaxSt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModelSt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OntoXOfTwistSharesExp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PageSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankAtPlacesRec
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShareStOfShareWSt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShareWStOfModelSt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistStOf
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf

@[expose] public section



section
section
open GlobalTheory.BigOn
namespace GlobalTheory.BigOn
theorem ontoX_of_hypotheses_alt_alt : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.HeckeLAdicCharacter → GlobalTheory.Published.ChebotarevDegreeOne → _root_.UpperTheory.GalS.CuspUAlt → _root_.GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup → GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.CuspRapidDecay → _root_.UpperTheory.Zero.LLC.RecTExists → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → _root_.GlobalTheory.BigOn.SurjectiveOntoX := by
  intro hGreen hCoh hHecke hCheb hGal hBC hBS hAbove hDecay hLL hCover hCW
  have hArtin : GlobalTheory.Published.GlobalArtinReciprocity :=
    GlobalTheory.Published.HeckeLAdicCharacter.globalArtin hHecke
  have hRay : GlobalTheory.Published.RayClassFieldSt :=
    GlobalTheory.Published.GlobalArtinReciprocity.rayClassFieldSt hArtin
  have hSer : GlobalTheory.SerStd.SeriesRatS := (GlobalTheory.seriesRatS_and_serInt_of_globalArtin hArtin).1
  have hExport : _root_.GlobalTheory.BigOn.ExportedStatement := by
    apply _root_.GlobalTheory.T.exportSt_of_reciprocity_and_casselman_wallach <;> with_reducible assumption
  have hPage : _root_.GlobalTheory.BigOn.PageStatement := _root_.GlobalTheory.BigOn.pageSt_alt
  have hGeo : _root_.GlobalTheory.BigOn.GeometricStatement' := _root_.GlobalTheory.BigOn.geoSt_of_pageSt_alt hPage
  have hRank := _root_.GlobalTheory.BigOn.rankLocSt_of_max_geo_runs _root_.GlobalTheory.BigOn.maxSt_alt hGeo _root_.GlobalTheory.BigOn.compareOffOwn_atRuns_alt
  have hTwist : _root_.GlobalTheory.BigOn.TwistStatement' := _root_.GlobalTheory.BigOn.TwistBoundAtPlace.twistSt_of_alt hExport hGeo hRank
  have hModel := _root_.GlobalTheory.ShareOn.modelSt_alt
  have hShare : _root_.GlobalTheory.BigOn.ShareStatement := _root_.GlobalTheory.ShareOn.shareSt_of_shareWSt_alt (_root_.GlobalTheory.ShareOn.shareWSt_of_modelSt_alt hModel)
  have hBad : _root_.GlobalTheory.BigOn.BadPlacesStatement := _root_.GlobalTheory.BigOn.badSt_of_badW_alt (_root_.GlobalTheory.BadWOn.badWSt_of_greenCuspidal_of_modelSt hGreen hModel)
  have hExp : _root_.GlobalTheory.BigOn.ExponentStatement := _root_.GlobalTheory.T.expSt_of_base_change_and_crystalline_lattices hCoh hHecke hCheb hGal hBC hBS hAbove hLL
  exact _root_.GlobalTheory.BigOn.ontoX_of_twist_shares_exp_alt hExport hTwist hShare hBad hExp
end GlobalTheory.BigOn
end
end
