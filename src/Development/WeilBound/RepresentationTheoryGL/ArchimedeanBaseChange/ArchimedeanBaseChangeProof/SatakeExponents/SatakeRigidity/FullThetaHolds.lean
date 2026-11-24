module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.StFull
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LInertSatExb
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LPermSub
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LRCuspCsd
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LRFull
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LRSplit
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LSplitConj
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LStrSat
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LWeightEx
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.OfEqOfIsSpeh
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

namespace PositivityTheory.Rg.BcB.F.Rig

open PositivityTheory.Rg.BcB.One

theorem strings_holds : Strings := rStrings regPart

theorem cuspCsd_holds : CuspCsd := rCuspCsd PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity strSat strings_holds

theorem locRigid_holds : LocRigid := rLoc PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity strSat strings_holds

theorem unrAE_holds : UnrAE := fun _ _ _ _ _ _ hπ => eventually_isUnramU hπ

theorem fullSat_holds : FullSat := rFullSat unrAE_holds B.inertSatEx splitSatPre

theorem fullTheta_holds : FullTheta := rFullTheta unrAE_holds B.inertSatEx splitConj

theorem fieldN_of_run (hR : RunFin) : PositivityTheory.Rg.BcN.BaseChangeIsobaricN :=
  fieldN_of hR fullSat_holds fullTheta_holds weightEx strings_holds cuspCsd_holds locRigid_holds permSub

end PositivityTheory.Rg.BcB.F.Rig
