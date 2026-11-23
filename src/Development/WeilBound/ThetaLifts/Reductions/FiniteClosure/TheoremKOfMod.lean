module

public import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesS
public import Development.WeilBound.ThetaLifts.SphericalLattices.FunDefs
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.SiegelSetUnitaryHolds
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.EvIHalfTrace
public import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinNarrowness.BernsteinClosure.RamifiedMultiplicityOne
public import Development.WeilBound.ThetaLifts.Reductions.ArchLie
public import Development.WeilBound.ThetaLifts.Reductions.KReal
import Development.WeilBound.ThetaLifts.Reductions.LieScalar2
public import Development.WeilBound.ThetaLifts.Reductions.LocalLift
import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilEx
public import Development.WeilBound.ThetaLifts.SphericalLattices.ExistsFixedSum
public import Development.WeilBound.ThetaLifts.SphericalLattices.FinInert
public import Development.WeilBound.ThetaLifts.SphericalLattices.FunTop
public import Development.WeilBound.ThetaLifts.SphericalLattices.HoweDuality
public import Development.WeilBound.ThetaLifts.SphericalLattices.ModSt2
public import Development.WeilBound.ThetaLifts.SphericalLattices.SphericalClosure.CloseSph
public import Development.WeilBound.ThetaLifts.SphericalSplitting.SphSplitGeo
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

namespace PositivityTheory.ThKR

open PositivityTheory.Sph GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem theoremK_head2_of_mod (hM : PositivityTheory.Sph.ModSt) (h11 : GlobalTheory.ThK.Dbl.EisBL) (h12 : GlobalTheory.ThK.Dbl.SiegelWeilStd) :
    ThetaIntegralsAgree ∧ LocalMatching :=
  Tr.closeSph PositivityTheory.BernsteinRamification.Close.kCoinv PositivityTheory.BernsteinRamification.Close.soCoinv PositivityTheory.BernsteinRamification.Close.ramifiedMultiplicityOne PositivityTheory.BernsteinRamification.Close.finRam
    PositivityTheory.BernsteinRamification.Close.finSplit (sphTri_of sphSplit_geo (vacInert howeInert))
    (finInert_of (vacInert howeInert) (sphFun_of_modSt hM) PositivityTheory.ThKH.Locrep.locRepEx)
    (lieSecond2 localLift_holds PositivityTheory.RL.derEx) (archLie' localLift_holds) (kReal' localLift_holds)
    (siegel_of_core PositivityTheory.Prw.siegelCore_holds) h11 h12 PositivityTheory.ThKW.weilEx

theorem theoremK_head2 (h11 : GlobalTheory.ThK.Dbl.EisBL) (h12 : GlobalTheory.ThK.Dbl.SiegelWeilStd) : ThetaIntegralsAgree ∧ LocalMatching :=
  theoremK_head2_of_mod PositivityTheory.Sph.modSt2 h11 h12

end PositivityTheory.ThKR
