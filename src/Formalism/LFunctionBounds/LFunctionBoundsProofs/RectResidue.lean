module

import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BdIntEqZeroOfPrimitive
public import Formalism.LFunctionBounds.ExpSumLowerBound
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.Linter.Style

@[expose] public section

open Complex

noncomputable section

namespace Formalism.FX

theorem rectRes_edge (g G : ℂ → ℂ) (P : Finset ℂ) (b : ℂ → ℂ) (γ : ℝ → ℂ) (a c : ℝ)
    (hγ : Continuous γ) (hG : ContinuousOn (fun t => G (γ t)) (Set.uIcc a c))
    (hP : ∀ t ∈ Set.uIcc a c, ∀ p ∈ P, γ t ≠ p)
    (hg : ∀ w : ℂ, w ∉ P → g w = G w + ∑ p ∈ P, b p / (w - p)) :
    ∫ t in a..c, g (γ t) =
      (∫ t in a..c, G (γ t)) + ∑ p ∈ P, b p * ∫ t in a..c, 1 / (γ t - p) := by
  have hγP : ∀ t ∈ Set.uIcc a c, γ t ∉ P := fun t ht hmem => hP t ht _ hmem rfl
  have hcont : ∀ p ∈ P, ContinuousOn (fun t => 1 / (γ t - p)) (Set.uIcc a c) := fun p hp =>
    continuousOn_const.div (hγ.continuousOn.sub continuousOn_const)
      (fun t ht => sub_ne_zero.2 (hP t ht p hp))
  calc ∫ t in a..c, g (γ t)
      = ∫ t in a..c, (G (γ t) + ∑ p ∈ P, b p * (1 / (γ t - p))) := by
        refine intervalIntegral.integral_congr (fun t ht => ?_)
        show g (γ t) = G (γ t) + ∑ p ∈ P, b p * (1 / (γ t - p))
        rw [hg _ (hγP t ht)]
        congr 1
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [mul_one_div]
    _ = (∫ t in a..c, G (γ t)) + ∫ t in a..c, ∑ p ∈ P, b p * (1 / (γ t - p)) := by
        refine intervalIntegral.integral_add hG.intervalIntegrable ?_
        exact (continuousOn_finsetSum P (fun p hp => continuousOn_const.mul (hcont p hp))).intervalIntegrable
    _ = (∫ t in a..c, G (γ t)) + ∑ p ∈ P, b p * ∫ t in a..c, 1 / (γ t - p) := by
        rw [intervalIntegral.integral_finsetSum]
        · simp_rw [intervalIntegral.integral_const_mul]
        · intro p hp
          exact ((hcont p hp).intervalIntegrable).const_mul (b p)

theorem rectRes_sum_combo (P : Finset ℂ) (b A B C D : ℂ → ℂ) :
    ∑ p ∈ P, b p * (A p - B p + I * C p - I * D p) =
      ∑ p ∈ P, b p * A p - ∑ p ∈ P, b p * B p + I * ∑ p ∈ P, b p * C p - I * ∑ p ∈ P, b p * D p := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem rectangle_residue : RectResidue := by
  unfold RectResidue
  intro g G P b x0 x1 y0 y1 _ _ hPin hU hg
  obtain ⟨U, -, hsub, hGd⟩ := hU
  have hGc : ContinuousOn G U := hGd.continuousOn
  have hG0 : ((∫ x in x0..x1, G ((x : ℂ) + (y0 : ℂ) * I)) - (∫ x in x0..x1, G ((x : ℂ) + (y1 : ℂ) * I))
      + I * (∫ y in y0..y1, G ((x1 : ℂ) + (y : ℂ) * I))) - I * (∫ y in y0..y1, G ((x0 : ℂ) + (y : ℂ) * I))
      = 0 := by
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G ⟨x0, y0⟩ ⟨x1, y1⟩
      (hGd.mono hsub)
    simp only [smul_eq_mul] at h
    exact h
  have eB := rectRes_edge g G P b (fun x : ℝ => (x : ℂ) + (y0 : ℂ) * I) x0 x1
    (Complex.continuous_ofReal.add continuous_const)
    (hGc.comp (Complex.continuous_ofReal.add continuous_const).continuousOn
      (fun t ht => hsub (Complex.mem_reProdIm.2 ⟨by simpa using ht, by simp⟩)))
    (fun t _ p hp h => by
      have h' := congrArg Complex.im h
      simp at h'
      linarith [(hPin p hp).2.2.1]) hg
  have eT := rectRes_edge g G P b (fun x : ℝ => (x : ℂ) + (y1 : ℂ) * I) x0 x1
    (Complex.continuous_ofReal.add continuous_const)
    (hGc.comp (Complex.continuous_ofReal.add continuous_const).continuousOn
      (fun t ht => hsub (Complex.mem_reProdIm.2 ⟨by simpa using ht, by simp⟩)))
    (fun t _ p hp h => by
      have h' := congrArg Complex.im h
      simp at h'
      linarith [(hPin p hp).2.2.2]) hg
  have eR := rectRes_edge g G P b (fun y : ℝ => (x1 : ℂ) + (y : ℂ) * I) y0 y1
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
    (hGc.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
      (fun t ht => hsub (Complex.mem_reProdIm.2 ⟨by simp, by simpa using ht⟩)))
    (fun t _ p hp h => by
      have h' := congrArg Complex.re h
      simp at h'
      linarith [(hPin p hp).2.1]) hg
  have eL := rectRes_edge g G P b (fun y : ℝ => (x0 : ℂ) + (y : ℂ) * I) y0 y1
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
    (hGc.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
      (fun t ht => hsub (Complex.mem_reProdIm.2 ⟨by simp, by simpa using ht⟩)))
    (fun t _ p hp h => by
      have h' := congrArg Complex.re h
      simp at h'
      linarith [(hPin p hp).1]) hg
  have hc := rectRes_sum_combo P b
    (fun p => ∫ t in x0..x1, 1 / ((t : ℂ) + (y0 : ℂ) * I - p))
    (fun p => ∫ t in x0..x1, 1 / ((t : ℂ) + (y1 : ℂ) * I - p))
    (fun p => ∫ t in y0..y1, 1 / ((x1 : ℂ) + (t : ℂ) * I - p))
    (fun p => ∫ t in y0..y1, 1 / ((x0 : ℂ) + (t : ℂ) * I - p))
  have hsum : ∑ p ∈ P, b p * ((∫ t in x0..x1, 1 / ((t : ℂ) + (y0 : ℂ) * I - p))
      - (∫ t in x0..x1, 1 / ((t : ℂ) + (y1 : ℂ) * I - p))
      + I * (∫ t in y0..y1, 1 / ((x1 : ℂ) + (t : ℂ) * I - p))
      - I * (∫ t in y0..y1, 1 / ((x0 : ℂ) + (t : ℂ) * I - p)))
      = 2 * (Real.pi : ℂ) * I * ∑ p ∈ P, b p := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have h := GlobalTheory.ResRect.bdInt_inv (hPin p hp).1 (hPin p hp).2.1 (hPin p hp).2.2.1
      (hPin p hp).2.2.2 (1 : ℂ)
    simp only [GlobalTheory.ResRect.bdInt, mul_one] at h
    rw [h]
    ring
  unfold rectInt
  linear_combination eB - eT + I * eR - I * eL + hG0 + hsum - hc

end Formalism.FX
