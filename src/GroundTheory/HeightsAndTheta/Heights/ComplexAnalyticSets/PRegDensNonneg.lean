module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegDensNonneg
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFormIntPos
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGradDensSheetBound
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix ComplexSets
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open scoped ComplexOrder

noncomputable section

namespace RegularizedDensityNonneg

theorem half_log_eq_phi (a : ℂ) {ε : ℝ} (hε : 0 ≤ ε) :
    Real.log (‖a‖ ^ 2 + ε) / 2 = phi (![a, ((√ε : ℝ) : ℂ)] : Fin 2 → ℂ) := by
  simp only [phi, sqSum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hε]
  ring

end RegularizedDensityNonneg

theorem RegDensNonneg.proof : RegDensNonneg.Statement := by
  intro n d J A u ε x s hε hs
  have han : AnalyticAt ℂ s (A *ᵥ x) := FormIntegralPositivity.analyticAt_sheet hs
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun k => ?_
  refine Fin.cases ?_ (fun j => ?_) k
  · simp only [Matrix.cons_val_zero]
    set y := A *ᵥ x
    have hh : AnalyticAt ℂ (fun w => linEval u (s w)) y := by
      unfold linEval
      exact Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul ((analyticAt_pi_iff.1 han) j)
    let τ : (Fin (d + 1) → ℂ) → (Fin 2 → ℂ) := fun w => ![linEval u (s w), ((√ε : ℝ) : ℂ)]
    have hτ : AnalyticAt ℂ τ y := by
      refine analyticAt_pi_iff.2 fun i => ?_
      fin_cases i
      · simpa [τ] using hh
      · simpa [τ] using (analyticAt_const : AnalyticAt ℂ (fun _ : Fin (d + 1) → ℂ => ((√ε : ℝ) : ℂ)) y)
    have hS : sqSum (τ y) ≠ 0 := by
      have : sqSum (τ y) = ‖linEval u (s y)‖ ^ 2 + ε := by
        simp only [τ, sqSum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hε.le]
      rw [this]
      positivity
    have hφ : ContDiffAt ℝ 2 phi (τ y) := contDiffAt_phi hS
    have hfun : logReg u ε ∘ s = phi ∘ τ := by
      funext w
      exact RegularizedDensityNonneg.half_log_eq_phi _ hε.le
    rw [hfun]
    refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ (hφ.comp _ hτ.restrictScalars.contDiffAt) fun v => ?_
    rw [ReciprocityTheory.AnForm.levi_comp v hτ hφ]
    exact GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi.leviForm_phi_nonneg hS _
  · simp only [Matrix.cons_val_succ]
    have hE : ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s (A *ᵥ x)) :=
      ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    have e : (euclPot : (Fin n → ℂ) → ℝ) = fun w => ∑ i, Complex.normSq (w i) := by
      funext w; simp [euclPot, Complex.normSq_eq_norm_sq]
    rw [ReciprocityTheory.AnForm.A.hessC_comp _ _ _ han hE, e, ReciprocityTheory.AnForm.A.hessC_sum_normSq]
    exact GradDensSheetBound.posSemidef_transpose_mul_mul_conj _ PosSemidef.one

end

end GroundTheory.Heights₂.Heights
