import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.NonvanishingHypotheses
import Mathlib

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

def hNum (n q : ℕ) : ℝ :=
  max (2 + max (3 * (n : ℝ) / 2) (1 + (n : ℝ) * ((n - q : ℕ) : ℝ) * (q : ℝ)))
    (max (16 * (n : ℝ) * (min (n - q) q : ℕ) + 8 * Real.sqrt (2 * ((min (n - q) q : ℕ) : ℝ)) + 2)
      (8 * Real.sqrt (2 * ((min (n - q) q : ℕ) : ℝ)) *
        (4 * max (2 * (n : ℝ) * ((min (n - q) q : ℕ) : ℝ)) (2 * ((q : ℝ) - 1) * (n : ℝ) ^ 2) + 1)))

def GapNumStatement : Prop :=
  ∀ (n q t : ℕ) (x : ℝ), 2 ≤ n → 1 ≤ q → 2 * q ≤ n + 1 → n + 5 ≤ t →
    2 * ((n + 2 * q * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3 < x → hNum n q < x

theorem gapNum_key (Q Nn T : ℝ) (hQ : 1 ≤ Q) (hN : 2 ≤ Nn) (hT : Nn + 5 ≤ T) :
    160 * Q ^ 2 * Nn ^ 2 ≤ 2 * (Nn + 2 * Q * T) ^ 3 := by
  have hQ0 : 0 ≤ Q := by linarith
  have hN0 : 0 ≤ Nn := by linarith
  have hT0 : 0 ≤ T := by linarith
  have h1 : (2 * Q * T) ^ 3 ≤ (Nn + 2 * Q * T) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 3
  have h2 : 17 * Nn ^ 2 ≤ T ^ 3 := by
    have : (Nn + 5) ^ 3 ≤ T ^ 3 := pow_le_pow_left₀ (by linarith) hT 3
    nlinarith [sq_nonneg Nn]
  have h3 : Q ^ 2 ≤ Q ^ 3 := by nlinarith [sq_nonneg Q]
  have h4 : 16 * Q ^ 2 * (17 * Nn ^ 2) ≤ 16 * Q ^ 3 * T ^ 3 := by
    have := mul_le_mul h3 h2 (by positivity) (by positivity)
    nlinarith
  nlinarith [sq_nonneg Q, sq_nonneg Nn]

theorem gapNum_real (Q Nn T P Q0 x : ℝ) (hQ : 1 ≤ Q) (hN : 2 ≤ Nn) (hT : Nn + 5 ≤ T)
    (hP : P ≤ Nn) (hQ00 : 0 ≤ Q0) (hQ0 : Q0 ≤ Q)
    (hx : 2 * (Nn + 2 * Q * T) ^ 3 + T + 3 < x) :
    max (2 + max (3 * Nn / 2) (1 + Nn * P * Q))
      (max (16 * Nn * Q0 + 8 * Real.sqrt (2 * Q0) + 2)
        (8 * Real.sqrt (2 * Q0) * (4 * max (2 * Nn * Q0) (2 * (Q - 1) * Nn ^ 2) + 1))) < x := by
  have key := gapNum_key Q Nn T hQ hN hT
  have hQp : 0 ≤ Q := by linarith
  have hNp : 0 ≤ Nn := by linarith
  have hTp : 0 ≤ T := by linarith
  set S := Nn + 2 * Q * T with hS
  have hSN : Nn ≤ S := by nlinarith
  have hS3 : Nn ≤ 2 * S ^ 3 := by nlinarith [sq_nonneg S, sq_nonneg Nn]
  have hs0 : 0 ≤ Real.sqrt (2 * Q0) := Real.sqrt_nonneg _
  have hs : Real.sqrt (2 * Q0) ≤ 2 * Q := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have hm0 : 0 ≤ max (2 * Nn * Q0) (2 * (Q - 1) * Nn ^ 2) :=
    le_max_of_le_left (by positivity)
  have hm : max (2 * Nn * Q0) (2 * (Q - 1) * Nn ^ 2) ≤ 2 * Q * Nn ^ 2 :=
    max_le (by nlinarith [mul_le_mul_of_nonneg_left hQ0 hNp, mul_le_mul_of_nonneg_left (show Nn ≤ Nn ^ 2 by nlinarith) (show 0 ≤ Q by linarith)]) (by nlinarith)
  have hN2 : 4 ≤ Nn ^ 2 := by nlinarith
  have hQN : 4 * Q ≤ Q ^ 2 * Nn ^ 2 := by
    calc 4 * Q ≤ Q ^ 2 * 4 := by nlinarith
      _ ≤ Q ^ 2 * Nn ^ 2 := mul_le_mul_of_nonneg_left hN2 (sq_nonneg Q)
  have hd : 8 * Real.sqrt (2 * Q0) * (4 * max (2 * Nn * Q0) (2 * (Q - 1) * Nn ^ 2) + 1)
      ≤ 8 * (2 * Q) * (4 * (2 * Q * Nn ^ 2) + 1) := by
    apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  have hNQ : Nn * Q0 ≤ Nn * Q := mul_le_mul_of_nonneg_left hQ0 hNp
  have hqn : 2 ≤ Q * Nn := by nlinarith
  have hQ2N2 : 2 * (Nn * Q) ≤ Q ^ 2 * Nn ^ 2 := by nlinarith
  have hPQ : P * Q ≤ Nn * Q := mul_le_mul_of_nonneg_right hP hQp
  have hNPQ1 : Nn * (P * Q) ≤ Nn * (Nn * Q) := mul_le_mul_of_nonneg_left hPQ hNp
  have hQQ : Q ≤ Q ^ 2 := by nlinarith
  have hNPQ2 : Nn ^ 2 * Q ≤ Nn ^ 2 * Q ^ 2 := mul_le_mul_of_nonneg_left hQQ (sq_nonneg Nn)
  have hQN0 : 0 ≤ Q ^ 2 * Nn ^ 2 := by positivity
  refine max_lt ?_ (max_lt ?_ ?_)
  · have : max (3 * Nn / 2) (1 + Nn * P * Q) < x - 2 :=
      max_lt (by linarith) (by nlinarith)
    linarith
  · nlinarith
  · nlinarith

theorem gapNum : GapNumStatement := by
  intro n q t x hn hq hqn ht hx
  unfold hNum
  have hx' : 2 * ((n : ℝ) + 2 * (q : ℝ) * (t : ℝ)) ^ 3 + (t : ℝ) + 3 < x := by
    push_cast at hx; exact hx
  exact gapNum_real (q : ℝ) (n : ℝ) (t : ℝ) ((n - q : ℕ) : ℝ) ((min (n - q) q : ℕ) : ℝ) x
    (by exact_mod_cast hq) (by exact_mod_cast hn) (by exact_mod_cast ht)
    (by exact_mod_cast Nat.sub_le n q) (Nat.cast_nonneg _)
    (by exact_mod_cast min_le_right _ _) hx'

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

theorem parabolicSign_false_iff (k r : ℕ) (hk : 1 ≤ k) (i : Fin (2 * r + k + 1)) :
    Formalism.MainNotions.CayleySignature.eps48 k r i = false ↔ k ≤ i.val ∧ (i.val - k) % 2 = 0 := by
  unfold Formalism.MainNotions.CayleySignature.eps48
  split_ifs with h1
  · simp; omega
  · simp; omega

theorem noncompactCount_parabolicSign (k r : ℕ) (hk : 1 ≤ k) : qOf (Formalism.MainNotions.CayleySignature.eps48 k r) = r + 1 := by
  unfold qOf
  have hs : (Finset.univ.filter fun a : Fin (2 * r + k + 1) => Formalism.MainNotions.CayleySignature.eps48 k r a = false) =
      Finset.univ.image (fun j : Fin (r + 1) => (⟨k + 2 * j.val, by omega⟩ : Fin (2 * r + k + 1))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, parabolicSign_false_iff k r hk]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨(i.val - k) / 2, by omega⟩, ?_⟩
      ext; simp only; omega
    · rintro ⟨j, rfl⟩
      simp only
      omega
  rw [hs, Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    simp only [Fin.mk.injEq] at hxy
    ext; omega

theorem compactCount_parabolicSign (k r : ℕ) (hk : 1 ≤ k) :
    pOf (Formalism.MainNotions.CayleySignature.eps48 k r) = 2 * r + k + 1 - (r + 1) := by
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2 * r + k + 1))))
    (fun a => Formalism.MainNotions.CayleySignature.eps48 k r a = true)
  simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at this
  have hq := noncompactCount_parabolicSign k r hk
  unfold qOf at hq
  unfold pOf
  omega

theorem gapBound_parabolicSign (k r : ℕ) (hk : 1 ≤ k) :
    hNeed (Formalism.MainNotions.CayleySignature.eps48 k r) = hNum (2 * r + k + 1) (r + 1) := by
  unfold hNeed hNum
  rw [compactCount_parabolicSign k r hk, noncompactCount_parabolicSign k r hk]
  simp only [Nat.cast_min]

theorem parabolicWeight_sub_succ (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (hk : 1 ≤ k)
    (y : Fin (2 * r + k + 1)) (hy : k ≤ y.val) :
    Formalism.MainNotions.CayleySignature.lam48 k r v b ⟨y.val - 1, by omega⟩ - Formalism.MainNotions.CayleySignature.lam48 k r v b y =
      b ⟨y.val - k + 1, by omega⟩ - b ⟨y.val - k, by omega⟩ := by
  unfold Formalism.MainNotions.CayleySignature.lam48
  rw [dif_neg (by simp only; omega), dif_neg (by omega)]
  have e1 : b ⟨y.val - 1 - (k - 1), by omega⟩ = b ⟨y.val - k, by omega⟩ :=
    congrArg b (Fin.ext (by simp only; omega))
  have e2 : b ⟨y.val - (k - 1), by omega⟩ = b ⟨y.val - k + 1, by omega⟩ :=
    congrArg b (Fin.ext (by simp only; omega))
  simp only at e1 e2 ⊢
  rw [e1, e2]; ring

theorem gapAtLeast_parabolicWeight (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (hk : 1 ≤ k) (h : ℝ)
    (hanti : StrictAnti (Formalism.MainNotions.CayleySignature.lam48 k r v b)) (hlow : Formalism.MainNotions.CayleySignature.LowGapGe h r b) :
    GapAtLeast (Formalism.MainNotions.CayleySignature.eps48 k r) (Formalism.MainNotions.CayleySignature.lam48 k r v b) h := by
  have key : ∀ x y : Fin (2 * r + k + 1), x < y →
      Formalism.MainNotions.CayleySignature.eps48 k r x ≠ Formalism.MainNotions.CayleySignature.eps48 k r y →
      h ≤ Formalism.MainNotions.CayleySignature.lam48 k r v b x - Formalism.MainNotions.CayleySignature.lam48 k r v b y := by
    intro x y hxy hne
    have hy : k ≤ y.val := by
      by_contra hcon
      apply hne
      have hx : ¬ (Formalism.MainNotions.CayleySignature.eps48 k r x = false) := by
        rw [parabolicSign_false_iff k r hk]; have := Fin.lt_def.mp hxy; omega
      have hy' : ¬ (Formalism.MainNotions.CayleySignature.eps48 k r y = false) := by
        rw [parabolicSign_false_iff k r hk]; omega
      simp only [Bool.not_eq_false] at hx hy'
      rw [hx, hy']
    have hst := parabolicWeight_sub_succ k r v b hk y hy
    have hle : Formalism.MainNotions.CayleySignature.lam48 k r v b ⟨y.val - 1, by omega⟩ ≤ Formalism.MainNotions.CayleySignature.lam48 k r v b x :=
      hanti.antitone (show x ≤ (⟨y.val - 1, by omega⟩ : Fin (2 * r + k + 1)) from by
        rw [Fin.le_def]; have := Fin.lt_def.mp hxy; simp only; omega)
    have hl := hlow ⟨y.val - k, by omega⟩ (by simp only; omega)
    simp only at hl
    linarith
  intro a a' hne
  rcases lt_trichotomy a a' with h1 | h1 | h1
  · exact le_trans (key a a' h1 hne) (le_abs_self _)
  · exact absurd (h1 ▸ rfl) hne
  · rw [abs_sub_comm]; exact le_trans (key a' a h1 (Ne.symm hne)) (le_abs_self _)

theorem gapBig_gapLap : GapBigLapStatement := by
  intro k r z c u v b hS
  obtain ⟨hk, hev, hz, hT, hc, hu, hlam, hint, hhalf, t, ht, htn, ht1801, hgap⟩ := hS
  let g : Fin (2 * r + 1) → ℝ := fun j => b ⟨j.val + 1, by omega⟩ - b ⟨j.val, by omega⟩
  let h : ℝ := Finset.univ.inf' Finset.univ_nonempty g
  have hlow : Formalism.MainNotions.CayleySignature.LowGapGe h r b := by
    intro j hj
    exact Finset.inf'_le g (Finset.mem_univ (⟨j.val, by omega⟩ : Fin (2 * r + 1)))
  have hX : 2 * ((Formalism.MainNotions.CayleySignature.rk48 k r + (2 * r + 2) * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3 < h := by
    rw [Finset.lt_inf'_iff]
    intro j _
    exact hgap ⟨j.val, by omega⟩ (by simp only; omega)
  have hN : hNeed (Formalism.MainNotions.CayleySignature.eps48 k r) < h := by
    rw [gapBound_parabolicSign k r hk]
    refine gapNum (2 * r + k + 1) (r + 1) t h (by omega) (by omega) (by omega)
      (by unfold Formalism.MainNotions.CayleySignature.rk48 at htn; omega) ?_
    have e : (2 * r + k + 1 + 2 * (r + 1) * t : ℕ) = Formalism.MainNotions.CayleySignature.rk48 k r + (2 * r + 2) * t := by
      unfold Formalism.MainNotions.CayleySignature.rk48; ring
    rw [e]; exact hX
  exact ⟨h, hk, hev, hz, hT, hc, hu, hlam, hint, hhalf, hlow,
    hlam.1, gapAtLeast_parabolicWeight k r v b hk h hlam.1 hlow, hN⟩

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end
