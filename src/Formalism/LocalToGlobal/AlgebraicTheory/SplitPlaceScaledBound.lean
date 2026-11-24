module

public import Formalism.LocalToGlobal.AlgebraicTheory.StatementD
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementEig
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.EigenFrameDualOf
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.XiConn
public import Formalism.LocalToGlobal.AlgebraicTheory.ColBoundOfPaths
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import ReciprocityTheory.EigenFrames.EigenPf

@[expose] public section

namespace Formalism.L2.AlgTh

theorem xiConn : XiConn := xiConn_of etLoc scalarConst xiSwap
theorem split_place_scaled_bound : SelfDualLatticeThetaPadicIntegrality := split_bound_of_xi_lemmas xiEt xiConn
theorem eigenFrameDual : EigenFrameDual := eigenFrameDual_of ReciprocityTheory.EigenFramesTheory.eigenFrameDual
theorem kerFrame : KerFrame := kerFrame_of eigenFrameDual

end Formalism.L2.AlgTh
