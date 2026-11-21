import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.HJSumSmulRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Transfer

section
noncomputable section

open Matrix

namespace PI.ScPiFrameW

open PI.ScPiExists

variable {n : ℕ}

private theorem nonneg_term_lemma (ε : Fin n → Bool) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (hσ : ∀ i, ε i = false → ∃ j, σ j = i) (w : Fin n → ℂ) (hw0 : ∀ j, w (σ j) = 0) (i : Fin n) :
    0 ≤ (if ε i then (1 : ℝ) else -1) * Complex.normSq (w i) := by
  cases hi : ε i
  · obtain ⟨k, hk⟩ := hσ i hi
    subst hk
    simp [hw0]
  · simp [Complex.normSq_nonneg]

private theorem pos_of_vanish_lemma_2 (ε : Fin n → Bool) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (hσ : ∀ i, ε i = false → ∃ j, σ j = i) (w : Fin n → ℂ) (hw0 : ∀ j, w (σ j) = 0)
    (hw : w ≠ 0) : 0 < (hJ ε w w).re := by
  rw [hJ_self_re]
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw (funext h)
  have hεi : ε i = true := by
    cases hj : ε i
    · obtain ⟨k, hk⟩ := hσ i hj
      exact (hi (by rw [← hk]; exact hw0 k)).elim
    · rfl
  calc (0 : ℝ) < (if ε i then (1 : ℝ) else -1) * Complex.normSq (w i) := by
        rw [if_pos hεi, one_mul]
        exact Complex.normSq_pos.mpr hi
    _ ≤ ∑ j, (if ε j then (1 : ℝ) else -1) * Complex.normSq (w j) :=
        Finset.single_le_sum (fun j _ => nonneg_term_lemma ε σ hσ w hw0 j) (Finset.mem_univ i)

theorem pos_of_perp (ε : Fin n → Bool) {r : ℕ} (σ : Fin (r + 1) → Fin n)
    (hσ : ∀ i, ε i = false → ∃ j, σ j = i)
    (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (t : ℝ) (ht : 0 < t)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(t : ℂ))
    (y : Fin n → ℂ) (hey : ∀ c, hJ ε (e c) y = 0) (hfy : ∀ c, hJ ε (f c) y = 0)
    (hzy : hJ ε z y = 0) (hy : y ≠ 0) : 0 < (hJ ε y y).re := by
  by_contra hcon
  have hle : (hJ ε y y).re ≤ 0 := not_lt.mp hcon
  obtain ⟨m, hm⟩ : ∃ m : Fin r ⊕ Bool → Fin n → ℂ,
      m = Sum.elim (fun a => e a - f a) (fun b => if b then y else z) := ⟨_, rfl⟩
  have hmi : ∀ a, m (Sum.inl a) = e a - f a := fun a => by rw [hm]; rfl
  have hmf : m (Sum.inr false) = z := by rw [hm]; rfl
  have hmt : m (Sum.inr true) = y := by rw [hm]; rfl
  obtain ⟨D, hD⟩ : ∃ D : Fin r ⊕ Bool → ℂ,
      D = Sum.elim (fun _ => (-2 : ℂ)) (fun b => if b then hJ ε y y else -(t : ℂ)) := ⟨_, rfl⟩
  have hDi : ∀ a, D (Sum.inl a) = -2 := fun a => by rw [hD]; rfl
  have hDf : D (Sum.inr false) = -(t : ℂ) := by rw [hD]; rfl
  have hDt : D (Sum.inr true) = hJ ε y y := by rw [hD]; rfl
  have hG : ∀ k l, hJ ε (m k) (m l) = if k = l then D k else 0 := by
    intro k l
    rcases k with a | i <;> rcases l with b | j
    · simp only [hmi, hJ_sub_left, hJ_sub_right, hee, hff, hef, hJ_conj ε (e b) (f a), hDi]
      by_cases hab : a = b
      · subst hab
        norm_num
      · simp [hab, Ne.symm hab]
    · cases j <;> simp [hmi, hmf, hmt, hJ_sub_left, hez, hfz, hey, hfy]
    · cases i <;> simp [hmi, hmf, hmt, hJ_sub_right, hJ_conj ε (e b) z, hJ_conj ε (f b) z,
        hJ_conj ε (e b) y, hJ_conj ε (f b) y, hez, hfz, hey, hfy]
    · cases i <;> cases j <;> simp [hmf, hmt, hDf, hDt, hzz, hzy, hJ_conj ε z y]
  obtain ⟨g, hg, k0, hk0⟩ := exists_rel (fun k : Fin r ⊕ Bool => fun j : Fin (r + 1) => m k (σ j))
    (by simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool]; omega)
  obtain ⟨v, hv⟩ : ∃ v : Fin n → ℂ, v = ∑ k, g k • m k := ⟨_, rfl⟩
  have hv0 : ∀ j, v (σ j) = 0 := by
    intro j
    have h := congrFun hg j
    rw [hv]
    simpa [Finset.sum_apply] using h
  have hvv : (hJ ε v v).re = ∑ k, Complex.normSq (g k) * (D k).re := by
    rw [hv, hJ_sum_smul_left, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hJ_sum_smul_right]
    simp only [hG, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact re_star_mul_mul _ _
  have hterm : ∀ k, Complex.normSq (g k) * (D k).re ≤ 0 := by
    intro k
    refine mul_nonpos_iff.mpr (Or.inl ⟨Complex.normSq_nonneg _, ?_⟩)
    rcases k with a | b
    · rw [hDi]
      norm_num
    · cases b
      · rw [hDf]
        simp [ht.le]
      · rw [hDt]
        exact hle
  have hsum : 0 ≤ ∑ k, Complex.normSq (g k) * (D k).re := by
    rw [← hvv, hJ_self_re]
    exact Finset.sum_nonneg fun i _ => nonneg_term_lemma ε σ hσ v hv0 i
  have hzero : ∀ k, Complex.normSq (g k) * (D k).re = 0 := by
    have h0 : ∑ k, Complex.normSq (g k) * (D k).re = 0 :=
      le_antisymm (Finset.sum_nonpos fun k _ => hterm k) hsum
    intro k
    exact (Finset.sum_eq_zero_iff_of_nonpos fun k _ => hterm k).mp h0 k (Finset.mem_univ k)
  have hga : ∀ a, g (Sum.inl a) = 0 := by
    intro a
    simpa [hDi] using hzero (Sum.inl a)
  have hgf : g (Sum.inr false) = 0 := by
    simpa [hDf, ht.ne'] using hzero (Sum.inr false)
  have hvy : v = g (Sum.inr true) • y := by
    rw [hv, Fintype.sum_sum_type, Fintype.sum_bool]
    simp [hga, hgf, hmt]
  have hgt : g (Sum.inr true) ≠ 0 := by
    rcases k0 with a | b
    · exact absurd (hga a) hk0
    · cases b
      · exact absurd hgf hk0
      · exact hk0
  have hy0 : ∀ j, y (σ j) = 0 := by
    intro j
    have h := hv0 j
    rw [hvy, Pi.smul_apply, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hgt
  exact hcon (pos_of_vanish_lemma_2 ε σ hσ y hy0 hy)

end PI.ScPiFrameW
end
end

section
noncomputable section

open Matrix

namespace PI.ScPiFrameW

open PI.ScPiExists

variable {n : ℕ}

theorem gs_step (ε : Fin n → Bool) {r k : ℕ} (hn : n = 2 * r + k + 1) (σ : Fin (r + 1) → Fin n)
    (hσ : ∀ i, ε i = false → ∃ j, σ j = i)
    (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (t : ℝ) (ht : 0 < t)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(t : ℂ))
    (m : ℕ) (hm : m < k) (w : Fin m → Fin n → ℂ)
    (hwo : ∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0)
    (hwp : ∀ a, (∀ c, hJ ε (e c) (w a) = 0 ∧ hJ ε (f c) (w a) = 0) ∧ hJ ε z (w a) = 0) :
    ∃ w' : Fin (m + 1) → Fin n → ℂ, (∀ a b, hJ ε (w' a) (w' b) = if a = b then 1 else 0) ∧
      ∀ a, (∀ c, hJ ε (e c) (w' a) = 0 ∧ hJ ε (f c) (w' a) = 0) ∧ hJ ε z (w' a) = 0 := by
  obtain ⟨y, hy, hperp⟩ := exists_perp ε
    (Sum.elim e (Sum.elim f (Sum.elim (fun _ : Unit => z) w)))
    (by simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]; omega)
  have hey : ∀ c, hJ ε (e c) y = 0 := fun c => hperp (Sum.inl c)
  have hfy : ∀ c, hJ ε (f c) y = 0 := fun c => hperp (Sum.inr (Sum.inl c))
  have hzy : hJ ε z y = 0 := hperp (Sum.inr (Sum.inr (Sum.inl ())))
  have hwy : ∀ a, hJ ε (w a) y = 0 := fun a => hperp (Sum.inr (Sum.inr (Sum.inr a)))
  have hs0 : 0 < (hJ ε y y).re :=
    pos_of_perp ε σ hσ e f z t ht hee hff hef hez hfz hzz y hey hfy hzy hy
  obtain ⟨s, hs_eq⟩ : ∃ s : ℝ, s = (hJ ε y y).re := ⟨_, rfl⟩
  have hs : 0 < s := hs_eq ▸ hs0
  have hyy : hJ ε y y = (s : ℂ) := by
    rw [hs_eq, hJ_self, Complex.ofReal_re]
  have hμ : star (((Real.sqrt s)⁻¹ : ℝ) : ℂ) * ((((Real.sqrt s)⁻¹ : ℝ) : ℂ) * hJ ε y y) = 1 := by
    rw [hyy, show star (((Real.sqrt s)⁻¹ : ℝ) : ℂ) = (starRingEnd ℂ) (((Real.sqrt s)⁻¹ : ℝ) : ℂ)
      from rfl, Complex.conj_ofReal]
    have hsq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
    have h1 : (Real.sqrt s)⁻¹ * ((Real.sqrt s)⁻¹ * s) = 1 := by
      rw [← mul_assoc, ← mul_inv, hsq, inv_mul_cancel₀ hs.ne']
    exact_mod_cast h1
  refine ⟨Fin.cons ((((Real.sqrt s)⁻¹ : ℝ) : ℂ) • y) w, ?_, ?_⟩
  · intro a b
    refine Fin.cases ?_ (fun a' => ?_) a <;> refine Fin.cases ?_ (fun b' => ?_) b
    · rw [if_pos rfl]
      simp only [Fin.cons_zero, hJ_smul_left, hJ_smul_right]
      rw [mul_left_comm]
      exact hμ
    · rw [if_neg (Fin.succ_ne_zero b').symm]
      simp only [Fin.cons_zero, Fin.cons_succ, hJ_smul_left, hJ_conj ε (w b') y, hwy, star_zero,
        mul_zero]
    · rw [if_neg (Fin.succ_ne_zero a')]
      simp only [Fin.cons_zero, Fin.cons_succ, hJ_smul_right, hwy, mul_zero]
    · simp only [Fin.cons_succ, Fin.succ_inj]
      exact hwo a' b'
  · intro a
    refine Fin.cases ?_ (fun a' => ?_) a
    · simp [hJ_smul_right, hey, hfy, hzy]
    · simp only [Fin.cons_succ]
      exact hwp a'

theorem frame_core (ε : Fin n → Bool) {r k : ℕ} (hn : n = 2 * r + k + 1) (σ : Fin (r + 1) → Fin n)
    (hσ : ∀ i, ε i = false → ∃ j, σ j = i)
    (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (t : ℝ) (ht : 0 < t)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(t : ℂ)) :
    ∃ w : Fin k → Fin n → ℂ, (∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0) ∧
      ∀ a, (∀ c, hJ ε (e c) (w a) = 0 ∧ hJ ε (f c) (w a) = 0) ∧ hJ ε z (w a) = 0 := by
  have key : ∀ m, m ≤ k → ∃ w : Fin m → Fin n → ℂ,
      (∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0) ∧
      ∀ a, (∀ c, hJ ε (e c) (w a) = 0 ∧ hJ ε (f c) (w a) = 0) ∧ hJ ε z (w a) = 0 := by
    intro m
    induction m with
    | zero => intro _; exact ⟨fun a => a.elim0, fun a => a.elim0, fun a => a.elim0⟩
    | succ m ih =>
      intro hm
      obtain ⟨w, h1, h2⟩ := ih (by omega)
      exact gs_step ε hn σ hσ e f z t ht hee hff hef hez hfz hzz m (by omega) w h1 h2
  exact key k le_rfl

end PI.ScPiFrameW
end
end

section
noncomputable section

namespace PI.ScPiFrameW

open PI.ScPiExists

theorem frame_holds : PI.ScPiExists.Frame := by
  intro I r k e f z hn hfr ⟨t, ht, hzz⟩ hε v
  obtain ⟨hee, hff, hef, hz⟩ := hfr
  have hσ : ∃ σ : Fin (r + 1) → Fin I.n, ∀ i, I.ε v i = false → ∃ j, σ j = i := by
    refine ⟨fun j => ⟨min ((k - 1) + 2 * j.val + 1) (I.n - 1), by omega⟩, ?_⟩
    intro i hi
    rw [hε v i] at hi
    have h2 : ¬ i.val < k - 1 ∧ (i.val - (k - 1)) % 2 ≠ 0 := by
      by_cases h1 : i.val < k - 1
      · simp [h1] at hi
      · simp [h1] at hi
        exact ⟨h1, by omega⟩
    have hi' := i.isLt
    refine ⟨⟨(i.val - (k - 1)) / 2, by omega⟩, ?_⟩
    apply Fin.ext
    show min ((k - 1) + 2 * ((i.val - (k - 1)) / 2) + 1) (I.n - 1) = i.val
    omega
  obtain ⟨σ, hσ⟩ := hσ
  obtain ⟨w, hw1, hw2⟩ := frame_core (I.ε v) hn σ hσ (fun a => rv I v (e a))
    (fun a => rv I v (f a)) (rv I v z) (t : ℝ) (by exact_mod_cast ht)
    (fun a b => by rw [hJ_rv, hee a b, map_zero]) (fun a b => by rw [hJ_rv, hff a b, map_zero])
    (fun a b => by rw [hJ_rv, hef a b]; split_ifs <;> simp)
    (fun a => by rw [hJ_rv, (hz a).1, map_zero]) (fun a => by rw [hJ_rv, (hz a).2, map_zero])
    (by rw [hJ_rv, hzz]; simp)
  exact ⟨w, hw1, hw2⟩

end PI.ScPiFrameW
end
end
