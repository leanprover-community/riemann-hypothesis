module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivRemCompLe

@[expose] public section

noncomputable section

open GlobalTheory.ArchSch
open MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff

namespace GlobalTheory.SchwartzHadamard

section Param

variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

end Param

section Box

variable {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem norm_iteratedFDeriv_comp_le (e : A →L[ℝ] B) (he : ‖e‖ ≤ 1) (f : 𝓢(B, ℂ)) (i : ℕ) (x : A) :
    ‖iteratedFDeriv ℝ i (fun y => f (e y)) x‖ ≤ ‖iteratedFDeriv ℝ i f (e x)‖ := by
  have h := ContinuousLinearMap.iteratedFDeriv_comp_right e (f.smooth ⊤) x (i := i) (by exact_mod_cast le_top)
  have h' : (fun y => f (e y)) = (f ∘ e) := rfl
  rw [h', h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  calc ‖iteratedFDeriv ℝ i f (e x)‖ * ∏ _j : Fin i, ‖e‖
      ≤ ‖iteratedFDeriv ℝ i f (e x)‖ * 1 := by
        gcongr
        exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => he
    _ = _ := mul_one _

theorem exists_schwartz_prod (f₁ : 𝓢(A, ℂ)) (f₂ : 𝓢(B, ℂ)) :
    ∃ f : 𝓢(A × B, ℂ), ∀ x, f x = f₁ x.1 * f₂ x.2 := by
  have hs₁ : ContDiff ℝ ∞ (fun y : A × B => f₁ y.1) := (f₁.smooth ⊤).comp contDiff_fst
  have hs₂ : ContDiff ℝ ∞ (fun y : A × B => f₂ y.2) := (f₂.smooth ⊤).comp contDiff_snd
  refine ⟨⟨fun x => f₁ x.1 * f₂ x.2, hs₁.mul hs₂, fun k n => ?_⟩, fun _ => rfl⟩
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
    (SchwartzMap.seminorm ℝ k i f₁ * SchwartzMap.seminorm ℝ 0 (n - i) f₂ +
      SchwartzMap.seminorm ℝ 0 i f₁ * SchwartzMap.seminorm ℝ k (n - i) f₂), fun x => ?_⟩
  have hx : ‖x‖ ^ k ≤ ‖x.1‖ ^ k + ‖x.2‖ ^ k := by
    rw [Prod.norm_def]
    have p1 := pow_nonneg (norm_nonneg x.1) k
    have p2 := pow_nonneg (norm_nonneg x.2) k
    rcases le_total ‖x.1‖ ‖x.2‖ with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hL := norm_iteratedFDeriv_mul_le hs₁ hs₂ x (n := n) (by exact_mod_cast le_top)
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y : A × B => f₁ y.1 * f₂ y.2) x‖
      ≤ (‖x.1‖ ^ k + ‖x.2‖ ^ k) * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f₁ x.1‖ * ‖iteratedFDeriv ℝ (n - i) f₂ x.2‖ := by
        refine mul_le_mul hx (hL.trans ?_) (norm_nonneg _) (by positivity)
        refine Finset.sum_le_sum fun i _ => ?_
        gcongr
        · exact norm_iteratedFDeriv_comp_le (ContinuousLinearMap.fst ℝ A B) (ContinuousLinearMap.norm_fst_le ..) f₁ i x
        · exact norm_iteratedFDeriv_comp_le (ContinuousLinearMap.snd ℝ A B) (ContinuousLinearMap.norm_snd_le ..) f₂
            (n - i) x
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ((‖x.1‖ ^ k * ‖iteratedFDeriv ℝ i f₁ x.1‖) * ‖iteratedFDeriv ℝ (n - i) f₂ x.2‖ +
           ‖iteratedFDeriv ℝ i f₁ x.1‖ * (‖x.2‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f₂ x.2‖)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ _ := by
        refine Finset.sum_le_sum fun i _ => ?_
        gcongr
        · exact SchwartzMap.le_seminorm ℝ k i f₁ _
        · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ f₂ _ _
        · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ f₁ _ _
        · exact SchwartzMap.le_seminorm ℝ k (n - i) f₂ _

end Box

section Main

variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

end Main

end GlobalTheory.SchwartzHadamard
