module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.IsInvForm
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.DetPfTrGL
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.DetUpdateRowOneLast
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.EventuallyConjGL
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.FiniteImageOfEventually
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.FormTraceDistrGL
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.IsLocallyConstantIndicatorOne
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.MemSBIffSupportedIn
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

namespace PositivityTheory.RgUd.AB.Final

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem thmA : ThmT k → ThmA k :=
  Pf.thmA_of_core k (Pf.coreX k (Pf.recover k (Pf.phiIndep (k := k)) (Pf.phiLin (k := k)) (Pf.phiInt (k := k)) (Pf.phiNear (k := k)) (Pf.pfAct (k := k))
    (Pf.ltEquiv (k := k) (Pf.phiEquiv (k := k)))))

theorem thmB : ThmA k → ThmB k := Pf.thmB k

end PositivityTheory.RgUd.AB.Final
