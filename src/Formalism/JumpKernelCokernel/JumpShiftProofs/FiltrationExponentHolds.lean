module

public import Formalism.JumpKernelCokernel.Statement
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

theorem Formalism.KernelCokernelLengths.filtration_exponent_holds : Formalism.KernelCokernelLengths.FExp := by
  intro R _ u π₀ q ℓ hℓ Mi h hMi
  set m := h / (ℓ - 1) with hm
  have hpos : 0 < ℓ - 1 := by omega
  have hk : Mi + 1 ≤ (ℓ - 1) * (m + 1) := by
    have := Nat.lt_mul_div_succ h hpos
    exact Nat.succ_le_of_lt (lt_of_le_of_lt hMi this)
  obtain ⟨d, hd⟩ : ∃ d, (ℓ - 1) * (m + 1) = Mi + 1 + d := ⟨_, (Nat.add_sub_cancel' hk).symm⟩
  rw [Ideal.mem_span_singleton]
  refine ⟨u ^ (m + 1) * q ^ d, ?_⟩
  rw [mul_pow, mul_pow, ← pow_mul, hd, pow_add]
  ring
