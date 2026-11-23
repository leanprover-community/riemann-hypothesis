module

public import Development.WeilBound.ThetaLifts.LocalTheory.AdmissiblePureTensorSchwartz
public import Development.WeilBound.ThetaLifts.CartanFactorisation.CuspidalClassOfWeilConvergence
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Kills0Of
import Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod
public import Development.WeilBound.ThetaLifts.LatticeBasics.PolDense
public import Development.WeilBound.ThetaLifts.LeviDeterminants.ActsEx
public import Development.WeilBound.ThetaLifts.TowerModels.LeviEx
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
public import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsBeta

@[expose] public section

namespace PositivityTheory.ThKG.Loc

open GlobalTheory.ThK PositivityTheory.ThKF

theorem hyp_of (hT : ThetaBasic) (hW : WeilConv) (hS : SoCont) (hD : KDecay) (hC : KCoinv) (hK : Kills) (hO : ArchOp) (hL : ArchLie)
    (hU : ArchUniq) (hE : SplitEx) (hI : SplitInv2) (h0 : EvZero) (hF : FacNe) : Hyp :=
  ⟨PositivityTheory.ThKF0.actsEx, hW, hS, hD, hC, hK, kills0_of hT hW hC hK, hO, hL, hU,
    injPure_of hO hL hU PositivityTheory.ThKF0.actsEx hW hS hD hC hK (kills0_of hT hW hC hK), hE, hI, PositivityTheory.ThKG.Tow.leviEx, h0,
    GlobalTheory.ThK.Dbl.polDense, hF, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp _ hΦ g => I_left unimodularity_holds hT hp hΦ g⟩

end PositivityTheory.ThKG.Loc
