module

public import Development.WeilBound.ThetaLifts.SphericalLattices.FunDefs
public import Development.WeilBound.ThetaLifts.SphericalLattices.HoweInert
public import Development.WeilBound.ThetaLifts.SphericalLattices.FunAsm
public import Development.WeilBound.ThetaLifts.SphericalLattices.FunAvg
public import Development.WeilBound.ThetaLifts.SphericalLattices.FunChar
public import Development.WeilBound.ThetaLifts.SphericalLattices.FunCount
public import Development.WeilBound.ThetaLifts.SphericalLattices.FunEvInv
public import Development.WeilBound.ThetaLifts.SphericalLattices.FunFin
public import Development.WeilBound.ThetaLifts.SphericalLattices.FunSieg
public import Development.WeilBound.ThetaLifts.SphericalLattices.InvMemKgKCart2
public import Development.WeilBound.ThetaLifts.SphericalLattices.UnitLiftSt
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

namespace PositivityTheory.Sph

theorem sphFun_of_modSt (hM : ModSt) : SphFun :=
  sphFun_of countSt avgSt pInvSt unitLiftSt charSt evInvSt siegSt hM cartanSt2 finSt

end PositivityTheory.Sph
