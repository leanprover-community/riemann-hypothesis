module

public import GroundTheory.PAdicHodge.UnramifiedClosure
public import GroundTheory.PAdicHodge.BCrisNewtonFrac
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

set_option maxSynthPendingDepth 1

noncomputable section




namespace GroundTheory.PAdicHodge

namespace ACris

variable {p : ℕ} [hp : Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

section Frob

variable [FiniteDimensional ℚ_[p] K]

end Frob

section Valuation

variable {K}

theorem exists_norm_eq_zpow_maxUnramified {x : maxUnramified p K} (hx : x ≠ 0) :
    ∃ D : ℤ, ‖(x : PadicAlgCl p)‖ = ‖(p : PadicAlgCl p)‖ ^ D :=
  (isACrisFraction_of_mem (mem_maxUnramified.1 x.2).2).exists_norm_eq_zpow
    (fun h => hx (Subtype.ext h))

theorem norm_p_algCl_pos : 0 < ‖(p : PadicAlgCl p)‖ :=
  norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.out.ne_zero)



end Valuation

section FrobValuation

variable [FiniteDimensional ℚ_[p] K]

end FrobValuation

end ACris

end GroundTheory.PAdicHodge
