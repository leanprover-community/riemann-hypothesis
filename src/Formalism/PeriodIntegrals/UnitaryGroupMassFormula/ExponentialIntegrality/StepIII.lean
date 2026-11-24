module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.Development
public import Mathlib.Analysis.Normed.Field.Instances
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.InvNatCastMemWittIntegers
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.ExpIntWProof

open PI

theorem div_pow_mem (h : KeyW) (p : ℕ) [hp : Fact p.Prime] :
    ∀ k : ℕ, ∀ y : ℂ_[p], y ∈ Wp p → ‖y‖ ≤ ((p : ℝ)⁻¹) ^ k → y / (p : ℂ_[p]) ^ k ∈ Wp p := by
  intro k
  induction k with
  | zero => intro y hy _; simpa using hy
  | succ k ih =>
    intro y hy hnorm
    have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.out.pos)
    have hpinv : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
    have hlt : ‖y‖ < 1 :=
      lt_of_le_of_lt hnorm (pow_lt_one₀ hpos.le hpinv (Nat.succ_ne_zero k))
    have h1 : y / (p : ℂ_[p]) ∈ PI.Wp p := h p y hy hlt
    have h2 : ‖y / (p : ℂ_[p])‖ ≤ ((p : ℝ)⁻¹) ^ k := by
      rw [norm_div, norm_p, div_le_iff₀ hpos, ← pow_succ]
      exact hnorm
    have h3 := ih _ h1 h2
    rwa [div_div, ← pow_succ'] at h3

theorem stepIII_of_key (h : KeyW) : StepIII := by
  intro p hp x hx hnorm
  obtain ⟨k, hk⟩ := hx
  have hp0 : (p : ℂ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hn : ‖(p : ℂ_[p]) ^ k * x‖ ≤ ((p : ℝ)⁻¹) ^ k := by
    rw [norm_mul, norm_pow, norm_p]
    exact mul_le_of_le_one_right (by positivity) hnorm
  have h3 := div_pow_mem h p k _ hk hn
  rwa [mul_div_cancel_left₀ _ (pow_ne_zero k hp0)] at h3

theorem expIntW_of_key (h1 : StepI) (h : KeyW) : ExpIntW :=
  expIntW_of_steps h1 (stepIII_of_key h)

end PI.ExpIntWProof

end
