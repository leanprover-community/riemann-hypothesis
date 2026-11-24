module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.IsClosedGzS
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.TraceForm
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.PieceGood
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.DescOf
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.RestrL
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

namespace PositivityTheory.RgUd.TP.Desc.Final

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem desc (p : ℕ) [Fact p.Prime] [CharP k p] (hU : PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k)) : Desc k :=
  Asm.desc_of k (Restr.Final.restr k) (Piece.Final.pieceGood k) p hU

end PositivityTheory.RgUd.TP.Desc.Final
