module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelMultK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BaseKnownTheoremsE
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisBLOfK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinHalfPlaneHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelMultiplicityOfLaws
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFactorisationHolomorphic
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.SiegelMultOf
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section



section
noncomputable section
namespace PositivityTheory.RgEis.Hd
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem siegelMult_of_k : SecLaw → WallLaw → Dict → DictInf → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw → SgAll →
    _root_.SiegelEisensteinSeries.BRoad.SiegelMult_k := _root_.GlobalTheory.T.siegel_multiplicity_of_laws
theorem eisBL_k : _root_.GlobalTheory.ThK.Dbl.EisBL_k :=
  have hW := wallLaw_of secLaw
  have hP := parLaw_of bdetLaw extLaw grpTop
  have hG := cmGood_of stdGood dict dictInf
  have hM := mirGen_of secLaw stdGood bdetLaw epConv (epMain_of epConv) testFun testSph
  _root_.SiegelEisensteinSeries.BRoad.eisBL_of_k _root_.GlobalTheory.T.eisenstein_half_plane_holds
    (_root_.PositivityTheory.RgEis.Hd.siegelMult_of_k secLaw hW dict dictInf hG grpTop bdetLaw extLaw hP
      (sgAll_of hG (cmMir_of dict hG grpTop bdetLaw extLaw hP hM)
        (sgOne_of secLaw hW scale stdGood dict dictInf hG grpTop bdetLaw extLaw hP hM)
        (sgStep_of (gallery_of secLaw idTube tubeChain (cross_of secLaw htLip stage hW)) (transfer_of secLaw hW)
          (twist_of secLaw) grpTop hP (leviS_of bdetLaw extLaw grpTop) (leviQ_of bdetLaw extLaw grpTop)
          (convGrOf_of bdetLaw extLaw) (convU_of hP))))
    GlobalTheory.CompanionTheory.Entire.local_factorisation
end PositivityTheory.RgEis.Hd
end
end
