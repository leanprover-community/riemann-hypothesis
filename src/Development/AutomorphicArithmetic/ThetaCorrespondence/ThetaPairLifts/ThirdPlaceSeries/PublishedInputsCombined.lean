module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TotallyDisjointProductIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.MoyPrasadJacquetIsoTrivial
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelPurity
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TemperedProductOfSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.EssSquareIntegrableSegments
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.RecT
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsPowValEqZpow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DepthZeroJacquetInjectiveOfAdmissible
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RegularAlgebraicPurityOfClozel
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeLAdicParameterAboveOfAlgebraicCharacterWDAl
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SOneRow
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SPairs
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section



section
section
namespace GlobalTheory.NRows.HypothesesBridge
theorem locComp_of_isRc_classMapD_cenLoc : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.BernsteinUnitaryProductIrreducible → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.TotallyDisjointProductIrreducible → GlobalTheory.Published.MoyPrasadJacquetIso → GlobalTheory.Published.JacquetShalika → GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.TemperedProductOfSquareIntegrable → GlobalTheory.Published.EssSquareIntegrableSegments → GlobalTheory.Published.GelfandKazhdanDual → _root_.UpperTheory.GalS.PairUAlt → _root_.UpperTheory.One.M.Row → GlobalTheory.Published.ClozelPurity → GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.AlgebraicCharacterWD → GlobalTheory.Published.DeRhamPotSemistable → GlobalTheory.Published.ChebotarevDegreeOne → _root_.UpperTheory.Zero.LLC.RecTExists → _root_.GlobalTheory.NRows.ThetaLocalInputsAlt := by
  intro hBZ hBern hGeo hTD hMP hJS hFin hTSI hESS hGK hGRP hCLGD hCP hCC hArt hChA hAlg hBerger hCheb hLL
  have hCSD := _root_.UpperTheory.GalS.bridgeStar_alt hGK
  exact
    { bz := hBZ
      bern := hBern
      geo := hGeo
      unl := GlobalTheory.TotDisjUnlinked.main hTD
      mp := GlobalTheory.depthZeroJacquetInjective_of_admissible hBZ hMP
      js := hJS
      fin := hFin
      gal := hCSD.2 hGRP
      car := _root_.UpperTheory.GalS.carU_of_finite_gl_recT hFin hLL (hCSD.1 hCLGD)
      clo := GlobalTheory.regularAlgebraicPurity_of_clozel hCP hCC
      art := hArt
      chA := hChA
      chP := _root_.GlobalTheory.heckeLAdicParameterAbove_of_algebraicCharacterWD_alt hAlg
      berger := hBerger
      cheb := hCheb }
end GlobalTheory.NRows.HypothesesBridge
end
section

theorem _root_.GlobalTheory.T.published_inputs_combined_alt_alt : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.BernsteinUnitaryProductIrreducible → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.TotallyDisjointProductIrreducible → GlobalTheory.Published.MoyPrasadJacquetIso → GlobalTheory.Published.JacquetShalika → GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.TemperedProductOfSquareIntegrable → GlobalTheory.Published.EssSquareIntegrableSegments → GlobalTheory.Published.GelfandKazhdanDual → _root_.UpperTheory.GalS.PairUAlt → _root_.UpperTheory.One.M.Row → GlobalTheory.Published.ClozelPurity → GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.AlgebraicCharacterWD → GlobalTheory.Published.DeRhamPotSemistable → GlobalTheory.Published.ChebotarevDegreeOne → _root_.UpperTheory.Zero.LLC.RecTExists → _root_.GlobalTheory.NRows.ThetaLocalInputsAlt := by
  exact @_root_.GlobalTheory.NRows.HypothesesBridge.locComp_of_isRc_classMapD_cenLoc
end
end
