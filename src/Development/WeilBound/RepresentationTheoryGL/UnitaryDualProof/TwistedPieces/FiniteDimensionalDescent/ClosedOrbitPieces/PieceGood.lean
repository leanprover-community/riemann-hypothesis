module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.PieceGood
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.FrobeniusReciprocity.FrobProof
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.IsClosedRank
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.RatioOf
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.RootsFinite
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.Transfer
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.TwFin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

namespace PositivityTheory.RgUd.TP.Desc.Piece.Final

open PositivityTheory.RgUd.TP.Desc

theorem pieceGood (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PieceGood k :=
  PositivityTheory.RgUd.TP.Desc.Piece.PAsm2.pieceGood_of k PositivityTheory.PfBern.Frob.frobeniusReciprocity (PositivityTheory.RgUd.TP.Desc.Piece.PSect.sect k)
    (PositivityTheory.RgUd.TP.Desc.Piece.PTop.pieceTop k) (PositivityTheory.RgUd.TP.Desc.Piece.PDich.dich k)
    (PositivityTheory.RgUd.TP.Desc.Piece.PTr.transfer k)

end PositivityTheory.RgUd.TP.Desc.Piece.Final
