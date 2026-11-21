import Formalism.HermitianCurvature.HermitianCurvatureProofs.GramProductIdentities
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagScalarCommuteOfEntries
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PartialFlipCommuteDiagScalarOfFree
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagScalarCommuteTransposedRMatrix

namespace Formalism.FourierDecayAlt.P.DualKernelLemmas

open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities
open scoped Matrix

section Rep

variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]

theorem pair_smul_left (ρ : Rep A V) (c : ℂ) (X X' : Ix S → V) :
    pair ρ (c • X) X' = c * pair ρ X X' := by
  simp [pair, Finset.mul_sum]

end Rep

theorem star_ofReal (Y : ℝ) : star (Y : ℂ) = Y := Complex.conj_ofReal Y

theorem real_bound (u v c b : ℂ) (hc : c ≠ 0) (hu : u.im = 0) (hv : v.im = 0)
    (hb : ‖b‖ ^ 2 ≤ u.re * v.re) :
    (u * (c * v) / c).im = 0 ∧ ‖b‖ ^ 2 ≤ (u * (c * v) / c).re := by
  have h : u * (c * v) / c = u * v := by field_simp <;> ring
  rw [h]
  constructor
  · simp [Complex.mul_im, hu, hv]
  · simpa [Complex.mul_re, hu, hv] using hb

theorem d1a : DualityPairingFormula := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ Ω RR TT q a Y hD X₁ X₂
  obtain ⟨hM, hFR, hFT, hY, hY1, hq⟩ := hD
  have hd := Formalism.FourierDecayAlt.P.duality_plus ℂ A S Ω RR TT q a (Y : ℂ) hM hFR hFT hY hY1
    (star_ofReal Y) hq
  simp only [frm]
  rw [pair_act', ← act_mul, hd.2.2.2.1]

theorem d1b : DualityIsometry := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ Ω RR TT q a Y hD X₂ X₂'
  obtain ⟨hM, hFR, hFT, hY, hY1, hq⟩ := hD
  have hd := Formalism.FourierDecayAlt.P.duality_plus ℂ A S Ω RR TT q a (Y : ℂ) hM hFR hFT hY hY1
    (star_ofReal Y) hq
  simp only [frm]
  rw [pair_act', ← act_mul, ← act_mul, hd.2.2.2.2.1, act_csmul, pair_smul_left]

theorem d1c : DualityCauchySchwarz := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ Ω RR TT q a Y hD hP X₁ X₂
  have ha := d1a A S V ρ Ω RR TT q a Y hD X₁ X₂
  have hb := d1b A S V ρ Ω RR TT q a Y hD X₂ X₂
  have hq : q Y ≠ 0 := hD.2.2.2.2.2
  have hm : frm ρ (RR * ins a (TT (↑Y + 1))ᵀ) X₂ X₂ =
      q Y * frm ρ (RR * ins a (TT ↑Y)) (act (PsiP TT q a ↑Y) X₂) (act (PsiP TT q a ↑Y) X₂) := by
    rw [hb]; field_simp
  rw [hm, ha]
  refine real_bound _ _ _ _ hq (hP X₁).2 (hP _).2 ?_
  exact csPos A S V ρ _ X₁ _ hP



theorem qw_append_ne {S : Type} (q : ℂ → ℂ) (w : List (Letter ℂ S)) (Y : ℂ) (hq : qw q w Y ≠ 0) :
    ∀ L : List (Letter ℂ S), (∀ l ∈ L, l.plus = true ∧ Y - l.pt ≠ 0 ∧ Y - l.pt + 1 ≠ 0) →
      qw q (L ++ w) Y ≠ 0 := by
  intro L hL
  induction L with
  | nil => simpa using hq
  | cons l L ih =>
    have hl := hL l (by simp)
    rw [List.cons_append]
    simp only [qw]
    rw [if_pos hl.1]
    exact mul_ne_zero (ih fun l' hl' => hL l' (by simp [hl'])) (div_ne_zero hl.2.2 hl.2.1)

theorem good_tail {S : Type} {l : Letter ℂ S} {w : List (Letter ℂ S)} (h : Good (l :: w)) : Good w := by
  unfold Good at *
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, fun l' hl' => h2 l' (List.mem_cons_of_mem _ hl'), (List.pairwise_cons.1 h3).2⟩
  simp only [List.map_cons, List.nodup_cons] at h1
  exact h1.2

theorem dkDualOK : DKDualOK := by
  intro S _ _ q w L hD
  induction L with
  | nil => trivial
  | cons l L ih =>
    obtain ⟨hP, hG, hGd, hPw, hq⟩ := hD
    have hl : l.plus = true := hP l (by simp)
    have hG' : Good (L ++ w) := good_tail hG
    have hGd' : Good (L.map dl ++ w) := good_tail (by simpa using hGd)
    have hpw := List.pairwise_cons.mp hPw
    refine ⟨?_, ?_, ih ⟨fun l' h => hP l' (by simp [h]), hG', hGd', hpw.2,
      fun l' h => hq l' (by simp [h])⟩⟩
    ·
      intro l' hl'
      have hdl : dl l = ⟨false, l.intersection_update_fsHerm_neg_one, l.pt + 1⟩ := by simp [dl, hl]
      rw [hdl]
      rcases List.mem_append.mp hl' with h | h
      · have hpl : l'.plus = true := hP l' (by simp [h])
        have := (hpw.1 l' h).1
        simp only [RegL, hpl, if_true]
        intro h0; apply this; linear_combination h0
      · have hgd : Good (dl l :: (L.map dl ++ w)) := by simpa using hGd
        have := (List.pairwise_cons.mp hgd.2.2).1 l' (by simp [h])
        rw [hdl] at this
        exact this
    · simp only [ypt, hl, if_true]
      refine qw_append_ne q w l.pt (hq l (by simp)) L fun l' hl' => ⟨hP l' (by simp [hl']), ?_, ?_⟩
      · exact (hpw.1 l' hl').1
      · intro h0; exact (hpw.1 l' hl').2.2 (by linear_combination h0)







end Formalism.FourierDecayAlt.P.DualKernelLemmas

