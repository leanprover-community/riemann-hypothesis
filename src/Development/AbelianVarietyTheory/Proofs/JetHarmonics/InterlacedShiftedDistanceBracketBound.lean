import Mathlib

open Finset

namespace GlobalTheory.CloudProd

theorem side_succ (c : ℝ) (δ : ℕ → ℝ) (hc : 1 ≤ c) (n : ℕ)
    (h : ∀ j : ℕ, j < n + 1 → 2 * c * (j : ℝ) ≤ δ j) :
    ∏ j ∈ Finset.range (n + 1), (1 + (1 + c) / max (δ j) 1) ≤ (2 + c) * ((n : ℝ) + 1) := by
  induction n with
  | zero =>
    have h1 : (1 + c) / max (δ 0) 1 ≤ 1 + c :=
      div_le_self (by linarith) (le_max_right _ _)
    simp only [zero_add, Finset.prod_range_one, Nat.cast_zero, mul_one]
    linarith
  | succ m ih =>
    rw [Finset.prod_range_succ]
    have ih' := ih (fun j hj => h j (by omega))
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hd := h (m + 1) (by omega)
    push_cast at hd ⊢
    have hmax : (1 + c) * ((m : ℝ) + 1) ≤ max (δ (m + 1)) 1 := by
      refine le_trans ?_ (le_trans hd (le_max_left _ _))
      nlinarith
    have hpos : (0 : ℝ) < max (δ (m + 1)) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hf : (1 + c) / max (δ (m + 1)) 1 ≤ 1 / ((m : ℝ) + 1) := by
      rw [div_le_div_iff₀ hpos (by linarith)]
      linarith
    have hf0 : 0 ≤ 1 + (1 + c) / max (δ (m + 1)) 1 := by positivity
    calc _ ≤ ((2 + c) * ((m : ℝ) + 1)) * (1 + 1 / ((m : ℝ) + 1)) :=
          mul_le_mul ih' (by linarith) hf0 (by positivity)
      _ = (2 + c) * ((m : ℝ) + 1 + 1) := by field_simp

theorem side (c : ℝ) (δ : ℕ → ℝ) (hc : 1 ≤ c) (n : ℕ)
    (h : ∀ j : ℕ, j < n → 2 * c * (j : ℝ) ≤ δ j) :
    ∏ j ∈ Finset.range n, (1 + (1 + c) / max (δ j) 1) ≤ (2 + c) * ((n : ℝ) + 1) := by
  cases n with
  | zero => simp; linarith
  | succ m =>
    refine (side_succ c δ hc m h).trans ?_
    push_cast
    nlinarith

theorem main : ∀ (k : ℕ) (c y : ℝ) (lam : ℕ → ℝ), 1 ≤ k → 1 ≤ c → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + 2 * c ≤ lam s) → ∏ s ∈ Finset.Icc 1 (k - 1), (1 + (1 + c) / max |lam s - y| 1) ≤ ((2 + c) * (k : ℝ)) ^ 2 := by
  intro k c y lam hk hc hstep
  classical
  have mono : ∀ s d : ℕ, 1 ≤ s → s + d ≤ k - 1 → lam (s + d) + 2 * c * (d : ℝ) ≤ lam s := by
    intro s d hs
    induction d with
    | zero => intro _; simp
    | succ e ih =>
      intro hle
      have h1 := ih (by omega)
      have h2 := hstep (s + e) (by omega) (by omega)
      rw [← add_assoc]
      push_cast
      linarith
  obtain ⟨p, hp, hup, hlo⟩ : ∃ p : ℕ, p ≤ k - 1 ∧ (p ≠ 0 → y < lam p) ∧
      (p + 1 ≤ k - 1 → lam (p + 1) ≤ y) := by
    refine ⟨Nat.findGreatest (fun s => y < lam s) (k - 1), Nat.findGreatest_le _, ?_, ?_⟩
    · intro h0
      exact Nat.findGreatest_of_ne_zero (P := fun s => y < lam s) rfl h0
    · intro h1
      exact not_lt.mp (Nat.findGreatest_is_greatest (P := fun s => y < lam s)
        (Nat.lt_succ_self _) h1)
  have hI : Finset.Icc 1 (k - 1) = Finset.Ico 1 k := by
    ext s; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hI, ← Finset.prod_Ico_consecutive _ (show 1 ≤ p + 1 by omega) (show p + 1 ≤ k by omega),
    Finset.prod_Ico_eq_prod_range, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel,
    ← Finset.prod_range_reflect]
  have hA := side c (fun j => |lam (1 + (p - 1 - j)) - y|) hc p (by
    intro j hj
    have h1 := mono (1 + (p - 1 - j)) j (by omega) (by omega)
    rw [show 1 + (p - 1 - j) + j = p by omega] at h1
    have h2 := hup (by omega)
    refine le_trans ?_ (le_abs_self _)
    linarith)
  have hB := side c (fun j => |lam (p + 1 + j) - y|) hc (k - (p + 1)) (by
    intro j hj
    have h1 := mono (p + 1) j (by omega) (by omega)
    have h2 := hlo (by omega)
    refine le_trans ?_ (neg_le_abs _)
    linarith)
  have e1 : ((p : ℝ) + 1) ≤ k := by exact_mod_cast (show p + 1 ≤ k by omega)
  have e2 : (((k - (p + 1) : ℕ) : ℝ) + 1) ≤ k := by
    exact_mod_cast (show k - (p + 1) + 1 ≤ k by omega)
  have hc2 : (0 : ℝ) ≤ 2 + c := by linarith
  rw [sq]
  refine mul_le_mul (hA.trans (mul_le_mul_of_nonneg_left e1 hc2))
    (hB.trans (mul_le_mul_of_nonneg_left e2 hc2)) ?_ (by positivity)
  exact Finset.prod_nonneg (fun j _ => by positivity)

end GlobalTheory.CloudProd

namespace GlobalTheory

theorem prod_le_of_interlacing_pairing :
    ∀ (k l : ℕ) (c B Y : ℝ) (lam v a : ℕ → ℝ), 0 ≤ c → 1 ≤ B → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) ≤ lam s) → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k → (s ≠ l → lam s + 1 / 2 ≤ v s) ∧ (s + 1 ≠ l → v (s + 1) + 1 / 2 ≤ lam s)) → (∀ i ∈ Finset.Icc 1 k, 1 ≤ |Y + 1 / 2 + v i|) → (∀ s ∈ Finset.Icc 1 (k - 1), 0 ≤ a s ∧ a s ≤ |lam s + Y| + 1 + c ∧ a s ≤ B) → ∏ s ∈ Finset.Icc 1 (k - 1), a s ≤ B * (∏ s ∈ Finset.Icc 1 (k - 1), (1 + (1 + c) / max |lam s + Y| 1)) * ∏ i ∈ Finset.Icc 1 k, |Y + 1 / 2 + v i| := by
  intro k l c B Y lam v a hc hB hlam hv hW ha
  classical
  obtain ⟨φ, hφ⟩ : ∃ φ : ℕ → ℕ, ∀ s, φ s = if -Y < lam s then s else s + 1 := ⟨_, fun _ => rfl⟩
  have hmem : ∀ s ∈ Finset.Icc 1 (k - 1), φ s ∈ Finset.Icc 1 k := by
    intro s hs
    rw [Finset.mem_Icc] at hs ⊢
    rw [hφ]; split_ifs <;> omega
  have hinj : ∀ s ∈ Finset.Icc 1 (k - 1), ∀ t ∈ Finset.Icc 1 (k - 1), φ s = φ t → s = t := by
    intro s hs t ht h
    rw [Finset.mem_Icc] at hs ht
    rw [hφ, hφ] at h
    split_ifs at h with h1 h2 h2
    · exact h
    · subst h
      have := hlam t ht.1 hs.2
      linarith [not_lt.mp h2]
    · subst h
      have := hlam s hs.1 ht.2
      linarith [not_lt.mp h1]
    · omega
  have hR : ∀ s, 1 ≤ 1 + (1 + c) / max |lam s + Y| 1 := by
    intro s
    have : 0 ≤ (1 + c) / max |lam s + Y| 1 := by positivity
    linarith
  have hkey : ∀ s ∈ Finset.Icc 1 (k - 1), a s ≤ (if φ s = l then B else 1) *
      (1 + (1 + c) / max |lam s + Y| 1) * |Y + 1 / 2 + v (φ s)| := by
    intro s hs
    have hw := hW _ (hmem s hs)
    obtain ⟨h0, h1, h2⟩ := ha s hs
    have hr := hR s
    split_ifs with hl
    · calc a s ≤ B * 1 * 1 := by linarith
        _ ≤ _ := by gcongr
    · rw [Finset.mem_Icc] at hs
      obtain ⟨hv1, hv2⟩ := hv s hs.1 (by omega)
      have hd : |lam s + Y| ≤ |Y + 1 / 2 + v (φ s)| := by
        rw [hφ] at hl ⊢
        split_ifs at hl ⊢ with hy
        · have := hv1 hl
          rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
        · have := hv2 hl
          have := not_lt.mp hy
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
      have hM : max |lam s + Y| 1 ≤ |Y + 1 / 2 + v (φ s)| := max_le hd hw
      have hM1 : (1 : ℝ) ≤ max |lam s + Y| 1 := le_max_right _ _
      have hM2 : |lam s + Y| ≤ max |lam s + Y| 1 := le_max_left _ _
      have e : (1 + (1 + c) / max |lam s + Y| 1) * max |lam s + Y| 1
          = max |lam s + Y| 1 + (1 + c) := by
        field_simp
      rw [one_mul]
      calc a s ≤ (1 + (1 + c) / max |lam s + Y| 1) * max |lam s + Y| 1 := by rw [e]; linarith
        _ ≤ _ := by gcongr
  have hB' : ∏ s ∈ Finset.Icc 1 (k - 1), (if φ s = l then B else 1) ≤ B := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    have hcard : ((Finset.Icc 1 (k - 1)).filter (fun s => φ s = l)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro s hs t ht
      rw [Finset.mem_filter] at hs ht
      exact hinj s hs.1 t ht.1 (hs.2.trans ht.2.symm)
    calc _ ≤ B ^ 1 := pow_le_pow_right₀ hB hcard
      _ = B := pow_one B
  have hW' : ∏ s ∈ Finset.Icc 1 (k - 1), |Y + 1 / 2 + v (φ s)|
      ≤ ∏ i ∈ Finset.Icc 1 k, |Y + 1 / 2 + v i| := by
    rw [← Finset.prod_image (f := fun i => |Y + 1 / 2 + v i|) (g := φ)
      (fun s hs t ht h => hinj s hs t ht h)]
    have hsub : (Finset.Icc 1 (k - 1)).image φ ⊆ Finset.Icc 1 k := by
      intro i hi
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hi
      exact hmem s hs
    rw [← Finset.prod_sdiff hsub]
    refine le_mul_of_one_le_left (Finset.prod_nonneg fun _ _ => abs_nonneg _) ?_
    calc (1 : ℝ) = ∏ i ∈ Finset.Icc 1 k \ (Finset.Icc 1 (k - 1)).image φ, 1 := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one)
          (fun i hi => hW i (Finset.mem_sdiff.mp hi).1)
  calc ∏ s ∈ Finset.Icc 1 (k - 1), a s
      ≤ ∏ s ∈ Finset.Icc 1 (k - 1), ((if φ s = l then B else 1) *
        (1 + (1 + c) / max |lam s + Y| 1) * |Y + 1 / 2 + v (φ s)|) :=
        Finset.prod_le_prod (fun s hs => (ha s hs).1) hkey
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ ≤ _ := by
      have h1 : 0 ≤ ∏ s ∈ Finset.Icc 1 (k - 1), (1 + (1 + c) / max |lam s + Y| 1) :=
        Finset.prod_nonneg fun s _ => zero_le_one.trans (hR s)
      have h2 : 0 ≤ ∏ s ∈ Finset.Icc 1 (k - 1), |Y + 1 / 2 + v (φ s)| :=
        Finset.prod_nonneg fun _ _ => abs_nonneg _
      exact mul_le_mul (mul_le_mul_of_nonneg_right hB' h1) hW' h2
        (mul_nonneg (by linarith) h1)

end GlobalTheory

namespace GlobalTheory.BracketBound

theorem main : ∀ (k r l : ℕ) (b c Y e : ℝ) (lam v : ℕ → ℝ), 1 ≤ k → 1 ≤ c → c + 2 ≤ b → (k : ℝ) ≤ b → |Y| ≤ b → 0 ≤ e → e ≤ 1 → (∀ s ∈ Finset.Icc 1 (k + 2 * r + 1), |lam s| ≤ b) → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + 2 * c ≤ lam s) → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k → (s ≠ l → lam s + 1 / 2 ≤ v s) ∧ (s + 1 ≠ l → v (s + 1) + 1 / 2 ≤ lam s)) → (∀ i ∈ Finset.Icc 1 k, 1 ≤ |Y + 1 / 2 + v i|) → ∏ s ∈ Finset.Icc 1 (k + 2 * r + 1), (|Y + e + lam s| + c) ≤ b ^ (4 * r + 10) * ∏ i ∈ Finset.Icc 1 k, |Y + 1 / 2 + v i| := by
  intro k r l b c Y e lam v hk hc hcb hkb hY he0 he1 hlam hgap hint hW
  have hb3 : 3 ≤ b := by linarith
  have hb0 : 0 ≤ b := by linarith
  have h3b : 3 * b ≤ b ^ 2 := by nlinarith
  have ha0 : ∀ s, 0 ≤ |Y + e + lam s| + c := fun s => by positivity
  have ha1 : ∀ s, |Y + e + lam s| + c ≤ |lam s + Y| + 1 + c := fun s => by
    have h1 : |Y + e + lam s| ≤ |lam s + Y| + |e| := by
      have : Y + e + lam s = (lam s + Y) + e := by ring
      rw [this]; exact abs_add_le _ _
    rw [abs_of_nonneg he0] at h1
    linarith
  have ha2 : ∀ s ∈ Finset.Icc 1 (k + 2 * r + 1), |Y + e + lam s| + c ≤ 3 * b := fun s hs => by
    have h1 := ha1 s
    have h2 := abs_add_le (lam s) Y
    have h3 := hlam s hs
    linarith
  have hsplit : Finset.Icc 1 (k + 2 * r + 1) = Finset.Icc 1 (k - 1) ∪ Finset.Icc k (k + 2 * r + 1) := by
    ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc 1 (k - 1)) (Finset.Icc k (k + 2 * r + 1)) := by
    rw [Finset.disjoint_left]; intro x; simp only [Finset.mem_Icc]; omega
  have hWp : 0 ≤ ∏ i ∈ Finset.Icc 1 k, |Y + 1 / 2 + v i| :=
    Finset.prod_nonneg fun i _ => abs_nonneg _
  have hpair := GlobalTheory.prod_le_of_interlacing_pairing k l c (3 * b) Y lam v (fun s => |Y + e + lam s| + c)
    (by linarith) (by linarith) (fun s h1 h2 => by have := hgap s h1 h2; linarith) hint hW
    (fun s hs => ⟨ha0 s, ha1 s, ha2 s (by rw [hsplit]; exact Finset.mem_union_left _ hs)⟩)
  have hcloud := GlobalTheory.CloudProd.main k c (-Y) lam hk hc hgap
  simp only [sub_neg_eq_add] at hcloud
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h4 : ((2 + c) * (k : ℝ)) ^ 2 ≤ b ^ 4 := by
    have h1 : (2 + c) * (k : ℝ) ≤ b * b := mul_le_mul (by linarith) hkb hk0 hb0
    calc ((2 + c) * (k : ℝ)) ^ 2 ≤ (b * b) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
      _ = b ^ 4 := by ring
  have hR0 : 0 ≤ ∏ s ∈ Finset.Icc 1 (k - 1), (1 + (1 + c) / max |lam s + Y| 1) :=
    Finset.prod_nonneg fun s _ => by positivity
  have hC : ∏ s ∈ Finset.Icc 1 (k - 1), (|Y + e + lam s| + c) ≤
      b ^ 2 * b ^ 4 * ∏ i ∈ Finset.Icc 1 k, |Y + 1 / 2 + v i| := by
    refine hpair.trans (mul_le_mul_of_nonneg_right ?_ hWp)
    exact mul_le_mul h3b (hcloud.trans h4) hR0 (by positivity)
  have hN : ∏ s ∈ Finset.Icc k (k + 2 * r + 1), (|Y + e + lam s| + c) ≤ (b ^ 2) ^ (2 * r + 2) := by
    calc ∏ s ∈ Finset.Icc k (k + 2 * r + 1), (|Y + e + lam s| + c)
        ≤ ∏ _s ∈ Finset.Icc k (k + 2 * r + 1), b ^ 2 :=
          Finset.prod_le_prod (fun s _ => ha0 s) (fun s hs =>
            (ha2 s (by rw [hsplit]; exact Finset.mem_union_right _ hs)).trans h3b)
      _ = (b ^ 2) ^ (2 * r + 2) := by
          rw [Finset.prod_const, Nat.card_Icc]
          congr 1; omega
  rw [hsplit, Finset.prod_union hdisj]
  calc _ ≤ (b ^ 2 * b ^ 4 * ∏ i ∈ Finset.Icc 1 k, |Y + 1 / 2 + v i|) * (b ^ 2) ^ (2 * r + 2) :=
        mul_le_mul hC hN (Finset.prod_nonneg fun s _ => ha0 s) (by positivity)
    _ = b ^ (4 * r + 10) * ∏ i ∈ Finset.Icc 1 k, |Y + 1 / 2 + v i| := by ring

end GlobalTheory.BracketBound
