module

public import Formalism.SubspaceCounting.Statement
public import Formalism.SubspaceCounting.GoodOrbitIntervalTileCondition
public import Formalism.SubspaceCounting.SubspaceCountingProofs.MarkedRun
public import Formalism.SubspaceCounting.SubspaceCountingProofs.SubspaceCount
public import Formalism.SubspaceCounting.SubspaceCountingProofs.TypeIIDown
public import Formalism.SubspaceCounting.SubspaceCountingProofs.WalkSharp
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

namespace Formalism.G0.Top

theorem walkSharp : Formalism.G0.WalkSharp := Formalism.G0.walkSharp_true

theorem subspaceCount : Formalism.G0.SubspaceCount := Formalism.G0.countSubspacesEq

theorem typeIIDown : Formalism.G0.TypeIIDown := Formalism.G0.countAboveRangeCodimFormula

theorem markedRun : Formalism.G0.MarkedRun := Formalism.G0.marked_run

end Formalism.G0.Top
