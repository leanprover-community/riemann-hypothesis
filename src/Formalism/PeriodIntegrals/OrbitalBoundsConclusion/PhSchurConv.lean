module

public import Formalism.PeriodIntegrals.PhSchurConv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurConvolution.MapMulApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem schur_orthogonality_idempotent : PI.PhSchurConv.SchurConv := by
  open MeasureTheory in
  open scoped InnerProductSpace in
  intro G _ _ _ _ _ _ μ _ _ _ Hσ _ _ σ d w hU hF hw
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hF.1)
  have hstard : star (d : ℂ) = d := Complex.conj_ofReal d
  have hinv : (d : ℂ) * (d : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hd
  have h1 : σ 1 = 1 := hU.1
  refine ⟨?_, ?_⟩
  · unfold PI.PhSchurConv.PhConv
    refine ⟨?_, ?_, ?_⟩
    · simp only [PI.PhSchurConv.coefM]
      rw [h1, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, hw]
      simp
    · intro g
      simp only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]
      rw [(PI.UnitaryGroupMassFormula.PhSchurConv.Main.coef_inv hU)]
      simp only [star_mul', star_star, hstard]
      try ring
    · intro x y
      have key : ∀ g, PI.PhSchurConv.phOf σ w d g * PI.PhSchurConv.phOf σ w d (x⁻¹ * g⁻¹ * y)
          = ((d : ℂ) * d) * (⟪σ y w, σ g (σ x w)⟫_ℂ * star ⟪w, σ g w⟫_ℂ) := by
        intro g
        simp only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]
        rw [(PI.UnitaryGroupMassFormula.PhSchurConv.Main.coef_conv hU), PI.UnitaryGroupMassFormula.PhSchurConv.Main.star_inner (σ g (σ x w)) (σ y w)]
        ring
      obtain ⟨hi, he⟩ := hF.2 (σ x w) (σ y w) w w
      simp_rw [key]
      refine ⟨hi.const_mul _, ?_⟩
      rw [integral_const_mul, he]
      simp only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]
      rw [PI.UnitaryGroupMassFormula.PhSchurConv.Main.star_inner w (σ y w), div_eq_mul_inv]
      linear_combination (⟪w, σ x w⟫_ℂ * ⟪σ y w, w⟫_ℂ * d) * hinv
  · intro u u'
    have key : ∀ g, PI.PhSchurConv.phOf σ w d g * ⟪u', σ g u⟫_ℂ
        = (d : ℂ) * (⟪u', σ g u⟫_ℂ * star ⟪w, σ g w⟫_ℂ) := by
      intro g
      simp only [PI.PhSchurConv.phOf, PI.PhSchurConv.coefM]
      ring
    obtain ⟨hi, he⟩ := hF.2 u u' w w
    simp_rw [key]
    refine ⟨hi.const_mul _, ?_⟩
    rw [integral_const_mul, he, div_eq_mul_inv]
    linear_combination (⟪w, u⟫_ℂ * ⟪u', w⟫_ℂ) * hinv
