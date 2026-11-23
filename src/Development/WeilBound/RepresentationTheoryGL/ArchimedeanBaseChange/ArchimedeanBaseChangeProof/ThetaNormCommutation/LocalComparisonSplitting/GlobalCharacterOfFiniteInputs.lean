module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCoordinate
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOfRightInvariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountIsInvInvariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConjEqSign
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEigenbasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsScalarOfCentral
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactOfBounded
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLocallyConstantOfRightInv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsRegEllIffMemEll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPFinThetaGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemRatCentTwConj
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialFiniteAdeles
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormaliserUnconj
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitPreimageEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableUnits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwConjugateEquivalence
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.PTermOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.PWeylAt
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

@[expose] public section

namespace PositivityTheory.Rg.BcB.G8

open GlobalTheory.CompanionTheory

theorem translation_existence_holds : TranslEx := LocalThetaTranslation.translEx

theorem lefschetz_pair_holds : LefPair := GlobalTheory.CompanionTheory.LefPair.lefPairOf EllipticTwist.ellDiag weylAt_holds LocalThetaTopology.topo

theorem global_character_of_finite_inputs (hK : KfOC) (hL : FinLevel) (hF : FinHalf) : G4 :=
  have hA : AdelEq := AdelEqProof.adelEqOf TranslAdele.translAd
  global_character_of_holds
    (termOf_holds (QSplitPf.qSplitOf QuotNorm.qIndep) HaarProd.haarSplit LocalThetaTopology.topo CompIsoProof.compIso hK hL hF hA
      TwistCent.centEq NormPoly.polEq (EllProp.ellProperOf EllipticTwist.ellDiag DiagProperProof.diagProper LocalThetaTopology.topo))
    (GlobalTheory.CompanionTheory.OrbInv.orbInvOf (QConjug.qConjOf_holds QuotNorm.qIndep) LocalThetaTopology.topo)
    (GlobalTheory.CompanionTheory.AdelCont.adelContOf hA hL CompIsoProof.compIso LocalThetaTopology.topo) GlobalTheory.CompanionTheory.ClassBij.classBij NormPoly.polEq

end PositivityTheory.Rg.BcB.G8
