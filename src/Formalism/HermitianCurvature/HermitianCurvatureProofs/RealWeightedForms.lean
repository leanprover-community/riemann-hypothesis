import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualKernelLemmas

namespace Formalism.FourierDecayAlt.P.RealWeightedForms

open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas
open scoped Matrix

theorem qwOfReal : QwOfReal := by
  intro S _ _ q w Y hq hw
  induction w with
  | nil =>
    simp only [qw, List.map_nil]
    exact Complex.ext (by simp) (by simpa using hq)
  | cons l w ih =>
    have him := hw l (List.mem_cons_self ..)
    have ih' := ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨plus, intersection_update_fsHerm_neg_one, pt⟩ := l
    obtain ⟨p, rfl⟩ : ∃ p : ℝ, pt = p := ⟨pt.re, Complex.ext (by simp) (by simpa using him)⟩
    cases plus <;> simp [qw, ih']

section admitted

variable {S : Type}

def Cnd (l l' : Letter ℂ S) : Prop :=
  if l'.plus then
    2 < |l.pt.re - l'.pt.re| ∧ 2 < |l.pt.re - l'.pt.re + 1| ∧ 2 < |l.pt.re - l'.pt.re - 1|
  else
    2 < |l'.pt.re - l.pt.re| ∧ 2 < |l'.pt.re - l.pt.re - 1| ∧ 2 < |l'.pt.re - l.pt.re - 2|

theorem admissible_word_pairwise_condition {α β : ℝ} {w : List (Letter ℂ S)} (h : GrowthHypotheses α β w) :
    w.Pairwise (fun l l' => Cnd l l' ∧ Cnd l' l) := by
  rw [List.pairwise_iff_get]
  intro i j hij
  exact ⟨h.2.2 i j (ne_of_lt hij), h.2.2 j i (ne_of_lt hij).symm⟩

theorem regL_of_cnd {l l' : Letter ℂ S} (h : Cnd l l') : RegL l' l.pt := by
  unfold Cnd at h
  unfold RegL
  cases hp : l'.plus
  · simp only [hp, Bool.false_eq_true, if_false] at h ⊢
    intro he
    have hre := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.one_re] at hre
    rw [hre] at h
    norm_num at h
  · simp only [hp, if_true] at h ⊢
    intro he
    have hre := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.one_re] at hre
    rw [hre] at h
    norm_num at h

theorem good_of_adm {α β : ℝ} {w : List (Letter ℂ S)} (h : GrowthHypotheses α β w) : Good w := by
  refine ⟨h.1, fun l hl => ?_, (admissible_word_pairwise_condition h).imp fun hc => regL_of_cnd hc.1⟩
  rw [Complex.star_def]
  exact Complex.conj_eq_iff_im.2 (h.2.1 l hl).1

theorem pos_mul_ofReal {z : ℂ} {r : ℝ} (hz : z.im = 0 ∧ 0 < z.re) (hr : 0 < r) :
    (z * r).im = 0 ∧ 0 < (z * r).re := by
  refine ⟨by simp [hz.1], ?_⟩
  have e : (z * r).re = z.re * r := by simp [hz.1]
  rw [e]
  exact mul_pos hz.2 hr

theorem same_sign_pos {a b : ℝ} (ha : 2 < |a|) (hb : 2 < |b|) (hab : b = a + 1 ∨ b = a - 1) :
    0 < a / b := by
  rcases lt_abs.1 ha with ha' | ha' <;> rcases hab with rfl | rfl
  · exact div_pos (by linarith) (by linarith)
  · exact div_pos (by linarith) (by linarith)
  · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · exact div_pos_of_neg_of_neg (by linarith) (by linarith)

def CndY (Y : ℝ) (l' : Letter ℂ S) : Prop :=
  if l'.plus then
    2 < |Y - l'.pt.re| ∧ 2 < |Y - l'.pt.re + 1| ∧ 2 < |Y - l'.pt.re - 1|
  else
    2 < |l'.pt.re - Y| ∧ 2 < |l'.pt.re - Y - 1| ∧ 2 < |l'.pt.re - Y - 2|

theorem qw_pos (q : ℂ → ℂ) (Y : ℝ) (hq : (q Y).im = 0 ∧ 0 < (q Y).re) :
    ∀ w : List (Letter ℂ S), (∀ l' ∈ w, l'.pt.im = 0 ∧ CndY Y l') →
      (qw q w (Y : ℂ)).im = 0 ∧ 0 < (qw q w (Y : ℂ)).re := by
  intro w
  induction w with
  | nil =>
    intro _
    simpa [qw] using hq
  | cons l w ih =>
    intro hw
    obtain ⟨hl, hc⟩ := hw l (List.mem_cons_self ..)
    have ih' := ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨plus, intersection_update_fsHerm_neg_one, pt⟩ := l
    obtain ⟨p, rfl⟩ : ∃ p : ℝ, pt = p := ⟨pt.re, Complex.ext (by simp) (by simpa using hl)⟩
    cases plus
    · simp only [CndY, Bool.false_eq_true, if_false, Complex.ofReal_re] at hc
      have hpos := same_sign_pos hc.1 hc.2.1 (Or.inr rfl)
      have e : qw q ({ plus := false, intersection_update_fsHerm_neg_one := intersection_update_fsHerm_neg_one, pt := (p : ℂ) } :: w) (Y : ℂ) =
          qw q w (Y : ℂ) * (((p - Y) / (p - Y - 1) : ℝ) : ℂ) := by
        simp [qw]
      rw [e]
      exact pos_mul_ofReal ih' hpos
    · simp only [CndY, if_true, Complex.ofReal_re] at hc
      have hpos := same_sign_pos hc.2.1 hc.1 (Or.inr (by ring))
      have e : qw q ({ plus := true, intersection_update_fsHerm_neg_one := intersection_update_fsHerm_neg_one, pt := (p : ℂ) } :: w) (Y : ℂ) =
          qw q w (Y : ℂ) * (((Y - p + 1) / (Y - p) : ℝ) : ℂ) := by
        simp [qw]
      rw [e]
      exact pos_mul_ofReal ih' hpos

end admitted



section Rep

variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]


end Rep







end Formalism.FourierDecayAlt.P.RealWeightedForms

theorem Formalism.FourierDecayAlt.P.weighted_quadratic_of_real : Formalism.FourierDecayAlt.FormPairingAction.QwOfReal := Formalism.FourierDecayAlt.P.RealWeightedForms.qwOfReal
