module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SqIntCritHolds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.TopNeg
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ContinuousAT
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.InfInd2Holds
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PAscAll
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PChord
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpFin
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpTw
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceTens
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStages
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ProjOf
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PositivityTheory.Rg.Rs

theorem ascAll_of_rest (hS : Slice) (hP : Pr) (hI : IndMap) (hT : StringStep) : AscAll :=
  ascAll_of (dich_of dict_holds finTr_holds killPoly_holds) (expFin_of dict_holds finTr_holds) expNeg_holds hS
    (chord_of expTw_holds sqIntCrit_holds) (proj_of hP sliceTens_holds hI) infInd2_holds hT (stages_of hI)

end PositivityTheory.Rg.Rs
