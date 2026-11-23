module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundOfNatDegree
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountLeOfDvd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetLIntegralLeOfBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SingleVecMulUnipMatrix
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UpdateLeUpdate
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.AutomorphicLipschitz.NiceAut
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ConjugationDifferences.ExpDivExpEq
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ConstantTermSteps.CtstepglueHolds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExponentialGluing.ExpNegGlueHolds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.GapPairings.GapGlue
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2Gluing.IntegralLeToReal
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SquareIntegrableCovers.SetLIntegralLeOfCover
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

namespace PositivityTheory.Rg.Rs

theorem expNeg_of (h : An.Count) : ExpNeg :=
  expNegGlue_holds dict_holds (l2glue_holds h GlobalTheory.CompanionTheory.SiegelEscape.escape)

theorem sqIntCrit_of (h1 : InitBnd) (h2 : FinTr) (h3 : An.BoxVol) : SqIntCrit :=
  sqIntGlue_holds dict_holds niceAut_holds h1 h2 killPoly_holds
    (GlobalTheory.CompanionTheory.AnBoot.bootGlue diffstep_holds (ctstepglue_holds GlobalTheory.CompanionTheory.LinRec.recBound)) (GlobalTheory.CompanionTheory.SlabGlue.slabGlue h3)

theorem gap_of (h1 : LatOf) (h2 : GapOp) : Gap :=
  gapGlue_holds h1 (gapAbs_of h2 GlobalTheory.CompanionTheory.GapPolyProof.gapPoly)

end PositivityTheory.Rg.Rs
