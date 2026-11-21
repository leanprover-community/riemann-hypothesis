import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerAntidiagonalExact
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerFourthCondition

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace C2x4

variable {m : ℕ}

def Cond (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) : Prop :=
  ∀ a b : Fin m, a < b → w b < w a →
    ((b.val = a.val + 1 ↔ (w a).val = (w b).val + 1) ∧ (b.val = a.val + 1 → d a = d b))

def IsCut (w : Equiv.Perm (Fin m)) (c : Fin m) : Prop := ∀ x y : Fin m, x ≤ c → c < y → w x < w y

lemma cut_of_ascent (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hC : Cond w d) (a : Fin m)
    (ha : a.val + 1 < m) (hasc : w a < w ⟨a.val + 1, ha⟩) : IsCut w a := by
  have key : ∀ n : ℕ, ∀ x y : Fin m, x ≤ a → a < y → w y < w x → (w x).val - (w y).val = n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x y hx hy hxy hn
      have hxy' : x < y := lt_of_le_of_lt hx hy
      by_cases h1 : (w x).val = (w y).val + 1
      · have := ((hC x y hxy' hxy).1).mpr h1
        have hxa : x = a := by
          apply Fin.ext; rw [Fin.le_def] at hx; rw [Fin.lt_def] at hy; omega
        have hya : y = ⟨a.val + 1, ha⟩ := by
          apply Fin.ext; simp only; rw [Fin.le_def] at hx; rw [Fin.lt_def] at hy; omega
        rw [hxa, hya] at hxy
        exact absurd hasc (not_lt.mpr (le_of_lt hxy))
      · have hlt : (w y).val + 1 < (w x).val := by
          rw [Fin.lt_def] at hxy; omega
        set v : Fin m := ⟨(w y).val + 1, by omega⟩ with hv
        set z := w.symm v with hz
        have hwz : w z = v := by rw [hz, Equiv.apply_symm_apply]
        by_cases hza : z ≤ a
        · apply ih ((w z).val - (w y).val) (by rw [hwz]; simp only [hv]; omega) z y hza hy
            (by rw [hwz, Fin.lt_def]; simp only [hv]; omega) rfl
        · push_neg at hza
          apply ih ((w x).val - (w z).val) (by rw [hwz]; simp only [hv]; omega) x z hx hza
            (by rw [hwz, Fin.lt_def]; simp only [hv]; omega) rfl
  intro x y hx hy
  by_contra hcon
  push_neg at hcon
  have hne : w y ≠ w x := fun e => (ne_of_lt (lt_of_le_of_lt hx hy)) (w.injective e).symm
  exact key _ x y hx hy (lt_of_le_of_ne hcon hne) rfl


open Classical in

noncomputable def blk (w : Equiv.Perm (Fin m)) (a : Fin m) : ℕ :=
  (Finset.univ.filter (fun c : Fin m => c < a ∧ IsCut w c)).card

lemma blk_mono (w : Equiv.Perm (Fin m)) : Monotone (blk w) := by
  intro a b hab
  unfold blk
  apply Finset.card_le_card
  intro c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
  exact ⟨lt_of_lt_of_le hc.1 hab, hc.2⟩


lemma no_cut_between (w : Equiv.Perm (Fin m)) (a b j : Fin m) (hab : blk w a = blk w b)
    (hj1 : a ≤ j) (hj2 : j < b) : ¬ IsCut w j := by
  intro hcut
  classical
  have hss : Finset.univ.filter (fun c : Fin m => c < a ∧ IsCut w c) ⊂
      Finset.univ.filter (fun c : Fin m => c < b ∧ IsCut w c) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨j, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hj2, hcut⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
        intro h; exact absurd h (not_lt.mpr hj1)
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact ⟨lt_trans hc.1 (lt_of_le_of_lt hj1 hj2), hc.2⟩
  have := Finset.card_lt_card hss
  unfold blk at hab
  rw [hab] at this
  exact lt_irrefl _ this

lemma desc_in_block (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hC : Cond w d) (a b : Fin m)
    (hab : blk w a = blk w b) (j : Fin m) (hj1 : a ≤ j) (hj2 : j.val + 1 ≤ b.val) :
    ∃ h : j.val + 1 < m, w ⟨j.val + 1, h⟩ < w j := by
  have h : j.val + 1 < m := lt_of_le_of_lt hj2 b.isLt
  refine ⟨h, ?_⟩
  have hne : w ⟨j.val + 1, h⟩ ≠ w j := fun e => by
    have := congrArg Fin.val (w.injective e); simp at this
  rcases lt_or_gt_of_ne hne with h1 | h1
  · exact h1
  · exfalso
    exact no_cut_between w a b j hab hj1 (by rw [Fin.lt_def]; omega) (cut_of_ascent w d hC j h h1)

lemma chain (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hC : Cond w d) (a : Fin m) :
    ∀ n : ℕ, ∀ b : Fin m, b.val = a.val + n + 1 → blk w a = blk w b → w b < w a ∧ d a = d b := by
  intro n
  induction n with
  | zero =>
    intro b hb hab
    obtain ⟨h, hd⟩ := desc_in_block w d hC a b hab a le_rfl (by omega)
    have hbe : b = ⟨a.val + 1, h⟩ := Fin.ext (by simp only; omega)
    subst hbe
    refine ⟨hd, ?_⟩
    exact (hC a _ (by rw [Fin.lt_def]; simp) hd).2 rfl
  | succ n ih =>
    intro b hb hab
    set j : Fin m := ⟨a.val + n + 1, by omega⟩ with hj
    have hmono := blk_mono w
    have haj : blk w a = blk w j := by
      apply le_antisymm (hmono (by rw [Fin.le_def]; simp only [hj]; omega))
      rw [hab]; exact hmono (by rw [Fin.le_def]; simp only [hj]; omega)
    obtain ⟨h1, h2⟩ := ih j rfl haj
    obtain ⟨h, hd⟩ := desc_in_block w d hC a b hab j (by rw [Fin.le_def]; simp only [hj]; omega)
      (by simp only [hj]; omega)
    have hbe : b = ⟨j.val + 1, h⟩ := Fin.ext (by simp only [hj]; omega)
    rw [hbe] at hab ⊢
    refine ⟨lt_trans hd h1, ?_⟩
    rw [h2]
    exact (hC j _ (by rw [Fin.lt_def]; simp) hd).2 rfl

end C2x4

open C2x4








end Formalism.FourierDecayAlt.P
