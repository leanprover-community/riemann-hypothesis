module

public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAddValuation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

namespace GlobalTheory.PadicVal

theorem _root_.GlobalTheory.PadicVal.exists_addValuation_le_iff_eq_iff : ∀ (p : ℕ) [Fact p.Prime] (π : PadicAlgCl p),
    0 < ‖π‖ → ‖π‖ < 1 → ∃ v : AddValuation (PadicAlgCl p) (WithTop ℚ),
      (∀ (c : PadicAlgCl p) (r : ℚ), (r : WithTop ℚ) ≤ v c ↔
        ‖c‖ ≤ Real.exp (-(-Real.log ‖π‖ * r))) ∧
      ∀ (c : PadicAlgCl p) (r : ℚ), v c = (r : WithTop ℚ) ↔
        ‖c‖ = Real.exp (-(-Real.log ‖π‖ * r)) := by
  intro p _ π h0 h1
  have hL : Real.log ‖π‖ < 0 := Real.log_neg h0 h1
  obtain ⟨v, hv⟩ := _root_.GlobalTheory.PadicVal.exists_addValuation π h0 h1
  refine ⟨v, fun c r => ?_, fun c r => ?_⟩
  · by_cases hc : c = 0
    · simp [hc, (Real.exp_pos _).le]
    obtain ⟨q, hvq, hlog⟩ := hv c hc
    rw [hvq, WithTop.coe_le_coe, neg_mul, neg_neg,
      ← Real.log_le_iff_le_exp (norm_pos_iff.2 hc), hlog, mul_comm (Real.log ‖π‖),
      mul_le_mul_right_of_neg hL]
    exact_mod_cast Iff.rfl
  · by_cases hc : c = 0
    · simp [hc, (Real.exp_pos _).ne]
    obtain ⟨q, hvq, hlog⟩ := hv c hc
    rw [hvq, WithTop.coe_inj, neg_mul, neg_neg]
    constructor
    · rintro rfl
      rw [mul_comm, ← hlog, Real.exp_log (norm_pos_iff.2 hc)]
    · intro h
      have h2 := congrArg Real.log h
      rw [Real.log_exp, hlog, mul_comm (Real.log ‖π‖)] at h2
      exact Rat.cast_injective (mul_right_cancel₀ hL.ne h2)

end GlobalTheory.PadicVal
