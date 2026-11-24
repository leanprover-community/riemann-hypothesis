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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.KernelCokernelLengths

theorem fil_eq_of_noJump {K D : Type} [Field K] [AddCommGroup D] [Module K D]
    (Fil : ℤ → Submodule K D) (b η : ℕ)
    (hj : ∀ j : ℤ, -(b : ℤ) < j → j < -(η : ℤ) → Fil j = Fil (j + 1)) :
    ∀ k : ℕ, ∀ j : ℤ, -(b : ℤ) < j → j + k = -(η : ℤ) → Fil j = Fil (-(η : ℤ)) := by
  intro k
  induction k with
  | zero =>
    intro j _ hjk
    simp only [Nat.cast_zero, add_zero] at hjk
    rw [hjk]
  | succ k ih =>
    intro j hjb hjk
    have hlt : j < -(η : ℤ) := by push_cast at hjk; omega
    rw [hj j hjb hlt]
    exact ih (j + 1) (by omega) (by push_cast at hjk ⊢; omega)

theorem exists_fixed_add_of_sub_mem : InvConst := by
  intro K _ D _ _ Fil hA χ hχ b η w hj hw
  have h1 : ∀ i : ℤ, i ≠ 0 → w i ∈ Fil (-i) := by
    intro i hi
    have hne : χ ^ i - 1 ≠ 0 := sub_ne_zero.mpr (hχ i hi)
    have h2 := (Fil (-i)).smul_mem (χ ^ i - 1)⁻¹ (hw i)
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
  refine ⟨h1, fun i hi hib => ?_⟩
  by_cases hη : (η : ℤ) ≤ i
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, -i + k = -(η : ℤ) := ⟨(i - η).toNat, by omega⟩
    rw [← fil_eq_of_noJump Fil b η hj k (-i) (by omega) hk]
    exact h1 i hi
  · exact hA (by omega : -(η : ℤ) ≤ -i) (h1 i hi)

end Formalism.KernelCokernelLengths
