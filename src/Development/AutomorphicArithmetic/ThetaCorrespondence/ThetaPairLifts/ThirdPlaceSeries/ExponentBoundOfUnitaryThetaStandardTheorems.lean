module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylLatticeExactExponentBlockCutStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExpStOfStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrameStOfSmallStStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisAtPlaceOfAutomorphicAtPlace
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModelStOfFramesStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumSt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallStStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SumExpStStatement
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

@[expose] public section



section
section
set_option autoImplicit false
namespace GlobalTheory.BigOn
theorem exponent_bound_of_unitaryThetaStandardTheorems_alt :
    GlobalTheory.Published.ClozelCohomological →
      GlobalTheory.Published.HeckeLAdicCharacter →
      GlobalTheory.Published.ChebotarevDegreeOne →
      _root_.UpperTheory.GalS.CuspUAlt →
      _root_.GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup →
      GlobalTheory.Published.BhattScholzeCrystallineLattices →
      GlobalTheory.Published.HeckeLAdicCharacterAbove →
      _root_.UpperTheory.Zero.LLC.RecTExists →
      _root_.GlobalTheory.BigOn.ExponentStatement :=
  fun hCoh hHecke hCheb hGal hBC hBS hAbove hLL =>
    _root_.GlobalTheory.T.expSt_of_num_sumExp_model GlobalTheory.T.weylLattice_exact_exponent_block_cut _root_.GlobalTheory.ExpTie.numSt_alt _root_.GlobalTheory.T.sum_expansion'
      (_root_.GlobalTheory.T.model_statement_of_crystalline_chebotarev_frame_gal hBS hCheb _root_.GlobalTheory.T.small_estimate (_root_.GlobalTheory.T.frame_statement_of_small_statement _root_.GlobalTheory.T.small_estimate)
        (_root_.GlobalTheory.T.galois_frame_compatibility_alt hCoh hHecke hCheb hGal hBC hBS hAbove hLL _root_.GlobalTheory.T.small_estimate))
end GlobalTheory.BigOn
end
section

theorem _root_.GlobalTheory.T.expSt_of_base_change_and_crystalline_lattices : GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.HeckeLAdicCharacter → GlobalTheory.Published.ChebotarevDegreeOne → _root_.UpperTheory.GalS.CuspUAlt → _root_.GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup → GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.HeckeLAdicCharacterAbove → _root_.UpperTheory.Zero.LLC.RecTExists → _root_.GlobalTheory.BigOn.ExponentStatement := by
  first | exact @_root_.GlobalTheory.BigOn.exponent_bound_of_unitaryThetaStandardTheorems_alt | exact _root_.GlobalTheory.BigOn.exponent_bound_of_unitaryThetaStandardTheorems_alt | (intros; apply _root_.GlobalTheory.BigOn.exponent_bound_of_unitaryThetaStandardTheorems_alt <;> assumption)
end
end
