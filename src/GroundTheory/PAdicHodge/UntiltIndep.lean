module

public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.PAdicHodge.PerfectoidField

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

section

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]



omit [NontriviallyNormedField K] [IsUltrametricDist K] [NontriviallyNormedField C] [NormedAlgebra K C]
  [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p] in
theorem norm_eq_of_norm_sub_lt {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E]
    {x y : E} (h : ‖x - y‖ < ‖y‖) : ‖x‖ = ‖y‖ := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne
  rw [sub_add_cancel, max_eq_right h.le] at this
  exact this

end

end GroundTheory.PAdicHodge
