module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.IsInvForm
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.CentralCharacterTheta.HasCentralCharCompThetaW
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.CentralCharacterZero.AsmCentralZero
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.ContragredientSwap.IsIrreducibleOfContraSwap
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.FirstPairExistence.ExistsPairFirst
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.IrreducibleFactors.FactorIrr
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.ThetaProducts.ThetaProd
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

namespace PositivityTheory.RgUd.Exp.Final

open PositivityTheory.RgUd.Exp

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem expBound (hL : ExpLow k) : ExpBound k :=
  PositivityTheory.RgUd.Exp.expBound_of k
    (Move2.moveLast k (Fact.factorIrr k) (Comm.comm2Irr k)) (Move2.moveFirst k (Fact.factorIrr k) (Comm.comm2Irr k))
    (ThetaPf.thetaProd k) (thetaFacts k) (centralProd2 k) hL

theorem expBound_of : ExpLow k → ExpBound k := expBound k

end PositivityTheory.RgUd.Exp.Final
