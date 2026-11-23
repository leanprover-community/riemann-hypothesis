module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegLogDensNonneg
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFormIntPos
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegDensNonneg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix ComplexSets
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open scoped ComplexOrder

noncomputable section

namespace RegularizedLogDensityNonneg

theorem hessC_logDistSq_comp_posSemidef {n e : ℕ} (x : Fin n → ℂ) (s : (Fin e → ℂ) → Fin n → ℂ)
    (y : Fin e → ℂ) (han : AnalyticAt ℂ s y) (hne : s y ≠ x) :
    (ReciprocityTheory.AnForm.hessC (logDistSq x ∘ s) y).PosSemidef := by
  let τ : (Fin e → ℂ) → Fin n → ℂ := fun w => s w - x
  have hτ : AnalyticAt ℂ τ y := han.sub analyticAt_const
  have hS : sqSum (τ y) ≠ 0 := by
    intro h0
    apply hne
    have hj : ∀ j ∈ Finset.univ, ‖(s y - x) j‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).1 h0
    funext j
    have := hj j (Finset.mem_univ j)
    simpa [sub_eq_zero] using this
  have hφ : ContDiffAt ℝ 2 phi (τ y) := contDiffAt_phi hS
  have hfun : logDistSq x ∘ s = fun w => 2 * (phi ∘ τ) w := by
    funext w
    simp only [Function.comp_apply, logDistSq, phi, τ, euclPot, sqSum]
    ring
  have hP : (ReciprocityTheory.AnForm.hessC (phi ∘ τ) y).PosSemidef := by
    refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ (hφ.comp _ hτ.restrictScalars.contDiffAt) fun v => ?_
    rw [ReciprocityTheory.AnForm.levi_comp v hτ hφ]
    exact GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi.leviForm_phi_nonneg hS _
  rw [hfun, ReciprocityTheory.AnForm.M.hessC_const_mul']
  exact hP.smul (by norm_num)

end RegularizedLogDensityNonneg

theorem RegLogDensNonneg.proof : RegLogDensNonneg.Statement := by
  intro n d J A u ε x z s hε hzx hs
  have han : AnalyticAt ℂ s (A *ᵥ z) := FormIntegralPositivity.analyticAt_sheet hs
  have hsz : s (A *ᵥ z) = z := by
    obtain ⟨U, -, -, -, h, -⟩ := hs
    exact h
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun k => ?_
  refine Fin.cases ?_ (fun j => ?_) k
  · simp only [Matrix.cons_val_zero]
    set y := A *ᵥ z
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
    exact RegularizedLogDensityNonneg.hessC_logDistSq_comp_posSemidef x s _ han (hsz.symm ▸ hzx)

end

end GroundTheory.Heights₂.Heights
