module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.HasFiniteLengthJacSub
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.BoundB
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Compact
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ComplementaryOf
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ConjDual
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ConjProd
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.CuspPairIrr
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.PiTensorTwist
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.PosMkIff
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.RhoNuRhoOfC
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SomeRed
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ThetaContra
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

namespace PositivityTheory.RgGu.NR

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem redClC : RedCl k :=
  redCl_ofC k (someRed_of k (complementary_of signature) (compact k) (boundB k) (herm_ofB k (conjProd k) (conjDual k))
    (prodModel k)) (cuspUnit k) (cuspPairIrr k)

theorem rhoNuRhoReducibleC : PositivityTheory.Pf1.SegRepC.SegTwo.RhoNuRhoReducible := rhoNuRho_ofC fun k _ _ _ _ => redClC k

end PositivityTheory.RgGu.NR
