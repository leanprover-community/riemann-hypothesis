import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Cut_BPEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF
import Formalism.HermitianCurvature.StatementM
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Interlace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume
import BuildAid.ForwardExisting

section
open Finset

namespace GlobalTheory.LamSize

theorem main : ∀ (C b T T' : ℝ) (r N : ℕ), 0 ≤ C → 3 ≤ b → (N : ℝ) ≤ b → b ^ (-(C * ((2 * r + 2 : ℕ) : ℝ))) ≤ T → b ^ (-(C * ((2 * r + 2 : ℕ) : ℝ))) ≤ T' → 1 ≤ b ^ ((6 + C) * ((2 * r + 2 : ℕ) : ℝ)) ∧ (N : ℝ) * b ^ (11 * (2 * r + 2)) ≤ (b ^ ((6 + C) * ((2 * r + 2 : ℕ) : ℝ))) ^ 2 * (T * T') := by
  intro C b T T' r N hC hb hN hT hT'
  have hm1 : 1 ≤ 2 * r + 2 := by omega
  generalize 2 * r + 2 = m at *
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  refine ⟨Real.one_le_rpow hb1 (by positivity), ?_⟩
  have hp : 0 < b ^ (-(C * (m : ℝ))) := Real.rpow_pos_of_pos hb0 _
  have hTT : b ^ (-(C * (m : ℝ))) * b ^ (-(C * (m : ℝ))) ≤ T * T' :=
    mul_le_mul hT hT' hp.le (hp.le.trans hT)
  have key : (b ^ ((6 + C) * (m : ℝ))) ^ 2 * (b ^ (-(C * (m : ℝ))) * b ^ (-(C * (m : ℝ))))
      = b ^ (12 * m) := by
    rw [sq, ← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  calc (N : ℝ) * b ^ (11 * m) ≤ b * b ^ (11 * m) := by gcongr
    _ = b ^ (11 * m + 1) := by ring
    _ ≤ b ^ (12 * m) := pow_le_pow_right₀ hb1 (by omega)
    _ = _ := key.symm
    _ ≤ _ := by gcongr

end GlobalTheory.LamSize
end

section
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
end

section
open Finset

namespace GlobalTheory

open Finset in
private lemma lam_add_two_mul_le_of_consecutive (k : ℕ) (c : ℝ) (lam : ℕ → ℝ)
    (h : ∀ s : ℕ, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + 2 * c ≤ lam s) :
    ∀ j s : ℕ, 1 ≤ s → s + j ≤ k - 1 → lam (s + j) + 2 * c * j ≤ lam s := by
  intro j
  induction j with
  | zero => intro s _ _; simp
  | succ j ih =>
    intro s hs hsj
    have h1 := ih (s + 1) (by omega) (by omega)
    have h2 := h s hs (by omega)
    rw [show s + (j + 1) = s + 1 + j by ring]
    push_cast
    linarith

open Finset in
private lemma two_mul_sub_one_mul_le_two_mul_add_one_mul (m c D a p : ℝ) (hm : 1 ≤ m) (hc : 1 ≤ c)
    (hD : 7 / 2 + 2 * c * m ≤ D) (ha : a ≤ (D + c) ^ 2) (hp : D ^ 2 ≤ p) :
    (2 * m - 1) * a ≤ (2 * m + 1) * p := by
  have hD0 : 0 ≤ D := by nlinarith
  have h1 : 2 * m * (D + c) ≤ (2 * m + 1) * D := by nlinarith
  have h2 : (2 * m * (D + c)) ^ 2 ≤ ((2 * m + 1) * D) ^ 2 :=
    pow_le_pow_left₀ (by nlinarith) h1 2
  have h2m : 0 ≤ 2 * m - 1 := by linarith
  have h3 : 4 * m ^ 2 * ((2 * m - 1) * (D + c) ^ 2) ≤ 4 * m ^ 2 * ((2 * m + 1) * D ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left h2 h2m,
      mul_nonneg (by linarith : (0:ℝ) ≤ 2 * m + 1) (sq_nonneg D)]
  have h4 : (2 * m - 1) * (D + c) ^ 2 ≤ (2 * m + 1) * D ^ 2 :=
    le_of_mul_le_mul_left h3 (by positivity)
  calc (2 * m - 1) * a ≤ (2 * m - 1) * (D + c) ^ 2 := mul_le_mul_of_nonneg_left ha h2m
    _ ≤ (2 * m + 1) * D ^ 2 := h4
    _ ≤ (2 * m + 1) * p := mul_le_mul_of_nonneg_left hp (by linarith)

open Finset in
private lemma prod_le_mul_odd_mul_prod_of_bracket_chain (c : ℝ) (hc : 1 ≤ c) (a d p : ℕ → ℝ) (n : ℕ)
    (h : ∀ j < n, 0 ≤ a j ∧ a j ≤ (d j + 1 + c) ^ 2 ∧ 5 / 2 + 2 * c * (j : ℝ) ≤ d j ∧
      (d j + 1) ^ 2 ≤ p j) :
    ∏ j ∈ range n, a j ≤ (1 + 2 * c / 7) ^ 2 * (2 * (n : ℝ) + 1) * ∏ j ∈ range n, p j := by
  have hK : 1 ≤ (1 + 2 * c / 7) ^ 2 := by nlinarith
  have hK0 : 0 ≤ (1 + 2 * c / 7) ^ 2 := by positivity
  have hp0 : ∀ m ≤ n, 0 ≤ ∏ j ∈ range m, p j := fun m hm =>
    prod_nonneg fun j hj => le_trans (sq_nonneg _) (h j (by simp at hj; omega)).2.2.2
  have key : ∀ m, m + 1 ≤ n → ∏ j ∈ range (m + 1), a j ≤
      (1 + 2 * c / 7) ^ 2 * (2 * (m : ℝ) + 1) * ∏ j ∈ range (m + 1), p j := by
    intro m
    induction m with
    | zero =>
      intro hm
      obtain ⟨_, ha, hd, hp⟩ := h 0 (by omega)
      simp only [prod_range_one, Nat.cast_zero, mul_zero, zero_add, mul_one]
      simp only [Nat.cast_zero, mul_zero, add_zero] at hd
      have h1 : d 0 + 1 + c ≤ (1 + 2 * c / 7) * (d 0 + 1) := by nlinarith
      have h2 : (d 0 + 1 + c) ^ 2 ≤ ((1 + 2 * c / 7) * (d 0 + 1)) ^ 2 :=
        pow_le_pow_left₀ (by linarith) h1 2
      calc a 0 ≤ (d 0 + 1 + c) ^ 2 := ha
        _ ≤ ((1 + 2 * c / 7) * (d 0 + 1)) ^ 2 := h2
        _ = (1 + 2 * c / 7) ^ 2 * (d 0 + 1) ^ 2 := by ring
        _ ≤ (1 + 2 * c / 7) ^ 2 * p 0 := mul_le_mul_of_nonneg_left hp hK0
    | succ m ih =>
      intro hm
      have ih' := ih (by omega)
      obtain ⟨ha0, ha, hd, hp⟩ := h (m + 1) (by omega)
      push_cast at hd
      have hstep := two_mul_sub_one_mul_le_two_mul_add_one_mul ((m : ℝ) + 1) c (d (m + 1) + 1) (a (m + 1)) (p (m + 1))
        (by have := m.cast_nonneg (α := ℝ); linarith) hc (by linarith) ha hp
      have hP := hp0 (m + 1) (by omega)
      rw [prod_range_succ a (m + 1), prod_range_succ p (m + 1)]
      calc (∏ j ∈ range (m + 1), a j) * a (m + 1)
          ≤ ((1 + 2 * c / 7) ^ 2 * (2 * (m : ℝ) + 1) * ∏ j ∈ range (m + 1), p j) * a (m + 1) :=
            mul_le_mul_of_nonneg_right ih' ha0
        _ = (1 + 2 * c / 7) ^ 2 * (∏ j ∈ range (m + 1), p j) *
            ((2 * ((m : ℝ) + 1) - 1) * a (m + 1)) := by ring
        _ ≤ (1 + 2 * c / 7) ^ 2 * (∏ j ∈ range (m + 1), p j) *
            ((2 * ((m : ℝ) + 1) + 1) * p (m + 1)) :=
            mul_le_mul_of_nonneg_left hstep (mul_nonneg hK0 hP)
        _ = _ := by push_cast; ring
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hK
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h1 := key m le_rfl
    have hP := hp0 (m + 1) le_rfl
    calc _ ≤ _ := h1
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hP
        apply mul_le_mul_of_nonneg_left _ hK0
        push_cast; linarith

open Finset in
private lemma prod_le_cube_mul_prod_of_bracket_chain (b c : ℝ) (n : ℕ) (hn : (n : ℝ) ≤ b) (hc : 1 ≤ c)
    (hcb : c + 2 ≤ b) (a d p : ℕ → ℝ)
    (h : ∀ j < n, 0 ≤ a j ∧ a j ≤ (d j + 1 + c) ^ 2 ∧ 5 / 2 + 2 * c * (j : ℝ) ≤ d j ∧
      (d j + 1) ^ 2 ≤ p j) :
    ∏ j ∈ range n, a j ≤ b ^ 3 * ∏ j ∈ range n, p j := by
  have hP : 0 ≤ ∏ j ∈ range n, p j :=
    prod_nonneg fun j hj => le_trans (sq_nonneg _) (h j (by simpa using hj)).2.2.2
  have h1 : 1 + 2 * c / 7 ≤ b / 2 := by linarith
  have h2 : (1 + 2 * c / 7) ^ 2 ≤ (b / 2) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
  have hn0 : (0:ℝ) ≤ n := n.cast_nonneg
  have hK : (1 + 2 * c / 7) ^ 2 * (2 * (n : ℝ) + 1) ≤ b ^ 3 := by
    nlinarith [mul_le_mul h2 (by linarith : 2 * (n:ℝ) + 1 ≤ 2 * b + 1) (by positivity)
      (by positivity), mul_nonneg (sq_nonneg b) (by linarith : (0:ℝ) ≤ 2 * b - 1)]
  calc _ ≤ _ := prod_le_mul_odd_mul_prod_of_bracket_chain c hc a d p n h
    _ ≤ b ^ 3 * ∏ j ∈ range n, p j := mul_le_mul_of_nonneg_right hK hP

open Finset in
private lemma sq_le_abs_mul_of_le_abs (D X X' : ℝ) (hD : 0 ≤ D) (h : D ≤ |X|) (h' : D ≤ |X'|) :
    D ^ 2 ≤ |X * X'| := by
  rw [abs_mul, sq]
  exact mul_le_mul h h' hD (abs_nonneg _)

open Finset in
private lemma bracket_product_le_of_neg_between_lemma (k r l : ℕ) (b c Y : ℝ) (lam u u' : ℕ → ℝ)
    (h1l : 1 ≤ l) (hlk : l ≤ k) (hc : 1 ≤ c) (hcb : c + 2 ≤ b) (hkb : (k : ℝ) ≤ b)
    (hul : |u l| ≤ b) (hu'l : |u' l| ≤ b)
    (hlam : ∀ s ∈ Finset.Icc 1 (k + 2 * r + 1), |lam s| ≤ b)
    (hsp : ∀ s : ℕ, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + 2 * c ≤ lam s)
    (hint : ∀ s : ℕ, 1 ≤ s → s + 1 ≤ k →
      (s ≠ l → lam s + 1 / 2 ≤ u s) ∧ (s + 1 ≠ l → u (s + 1) + 1 / 2 ≤ lam s))
    (hint' : ∀ s : ℕ, 1 ≤ s → s + 1 ≤ k →
      (s ≠ l → lam s + 1 / 2 ≤ u' s) ∧ (s + 1 ≠ l → u' (s + 1) + 1 / 2 ≤ lam s))
    (hdec : ∀ i : ℕ, 1 ≤ i → i ≤ k - 1 → u (i + 1) ≤ u i - 1 ∧ u' (i + 1) ≤ u' i - 1 ∧
      u (i + 1) ≤ u' i - 1 ∧ u' (i + 1) ≤ u i - 1)
    (hY : u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) :
    (∏ s ∈ Finset.Icc 1 (k + 2 * r + 1), (|Y + lam s| + c)) *
      (∏ s ∈ Finset.Icc 1 (k + 2 * r + 1), (|Y + 1 + lam s| + c)) ≤
      b ^ (11 * (2 * r + 2)) * ∏ i ∈ Finset.Icc 1 k, |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)| := by
  obtain ⟨hY1, hY2⟩ := hY
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hYb1 : -b + 2 ≤ -Y := by have := (abs_le.mp hul).1; linarith
  have hYb2 : -Y ≤ b - 2 := by have := (abs_le.mp hu'l).2; linarith
  have hspread := lam_add_two_mul_le_of_consecutive k c lam hsp
  have hA0 : ∀ s, 0 ≤ (|Y + lam s| + c) * (|Y + 1 + lam s| + c) := fun s =>
    mul_nonneg (by linarith [abs_nonneg (Y + lam s)]) (by linarith [abs_nonneg (Y + 1 + lam s)])
  rw [← prod_mul_distrib]
  have hLR : Disjoint (Ico 1 (l - 1)) (Ico (l + 1) k) := by
    rw [disjoint_left]; intro s h1 h2; simp only [mem_Ico] at h1 h2; omega
  have hsub : Ico 1 (l - 1) ∪ Ico (l + 1) k ⊆ Icc 1 (k + 2 * r + 1) := by
    intro s hs; simp only [mem_union, mem_Ico, mem_Icc] at hs ⊢; omega
  rw [← prod_sdiff hsub, prod_union hLR]
  have hA : ∀ s ∈ Icc 1 (k + 2 * r + 1), (|Y + lam s| + c) * (|Y + 1 + lam s| + c) ≤ b ^ 4 := by
    intro s hs
    have hl := abs_le.mp (hlam s hs)
    have e1 : |Y + lam s| ≤ 2 * b - 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have e2 : |Y + 1 + lam s| ≤ 2 * b - 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have e3 : (|Y + lam s| + c) * (|Y + 1 + lam s| + c) ≤ (3 * b) * (3 * b) :=
      mul_le_mul (by linarith) (by linarith) (by linarith [abs_nonneg (Y + 1 + lam s)])
        (by linarith)
    have hb9 : 9 ≤ b ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hb9 (sq_nonneg b)]
  have hT : ∏ s ∈ Icc 1 (k + 2 * r + 1) \ (Ico 1 (l - 1) ∪ Ico (l + 1) k),
      (|Y + lam s| + c) * (|Y + 1 + lam s| + c) ≤ b ^ (4 * (2 * r + 4)) := by
    have hcard : (Icc 1 (k + 2 * r + 1) \ (Ico 1 (l - 1) ∪ Ico (l + 1) k)).card ≤ 2 * r + 4 := by
      have h1 := card_sdiff_add_card_eq_card hsub
      rw [card_union_of_disjoint hLR, Nat.card_Icc, Nat.card_Ico, Nat.card_Ico] at h1
      omega
    calc _ ≤ ∏ s ∈ Icc 1 (k + 2 * r + 1) \ (Ico 1 (l - 1) ∪ Ico (l + 1) k), b ^ 4 :=
          prod_le_prod (fun s _ => hA0 s) (fun s hs => hA s (mem_sdiff.mp hs).1)
      _ = (b ^ 4) ^ (Icc 1 (k + 2 * r + 1) \ (Ico 1 (l - 1) ∪ Ico (l + 1) k)).card := prod_const _
      _ ≤ (b ^ 4) ^ (2 * r + 4) := pow_le_pow_right₀ (one_le_pow₀ hb1) hcard
      _ = b ^ (4 * (2 * r + 4)) := (pow_mul b 4 _).symm
  have hL : ∏ s ∈ Ico 1 (l - 1), (|Y + lam s| + c) * (|Y + 1 + lam s| + c) ≤
      b ^ 3 * ∏ i ∈ Ico 1 (l - 1), |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)| := by
    rw [prod_Ico_eq_prod_range, prod_Ico_eq_prod_range]
    have r1 : ∏ j ∈ range (l - 1 - 1), (|Y + lam (1 + (l - 1 - 1 - 1 - j))| + c) *
        (|Y + 1 + lam (1 + (l - 1 - 1 - 1 - j))| + c) =
        ∏ j ∈ range (l - 1 - 1), (|Y + lam (1 + j)| + c) * (|Y + 1 + lam (1 + j)| + c) :=
      prod_range_reflect (fun j => (|Y + lam (1 + j)| + c) * (|Y + 1 + lam (1 + j)| + c)) _
    have r2 : ∏ j ∈ range (l - 1 - 1), |(Y + 1 / 2 + u (1 + (l - 1 - 1 - 1 - j))) *
        (Y + 1 / 2 + u' (1 + (l - 1 - 1 - 1 - j)))| =
        ∏ j ∈ range (l - 1 - 1), |(Y + 1 / 2 + u (1 + j)) * (Y + 1 / 2 + u' (1 + j))| :=
      prod_range_reflect (fun j => |(Y + 1 / 2 + u (1 + j)) * (Y + 1 / 2 + u' (1 + j))|) _
    rw [← r1, ← r2]
    have hn : ((l - 1 - 1 : ℕ) : ℝ) ≤ b := by
      have : ((l - 1 - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast (by omega : l - 1 - 1 ≤ k)
      linarith
    apply prod_le_cube_mul_prod_of_bracket_chain b c (l - 1 - 1) hn hc hcb _
      (fun j => Y + lam (1 + (l - 1 - 1 - 1 - j)))
    intro j hj
    beta_reduce
    set s := 1 + (l - 1 - 1 - 1 - j) with hs
    have hs1 : 1 ≤ s := by omega
    have hsj : s + j = l - 2 := by omega
    have e0 := hspread j s hs1 (by omega)
    rw [hsj] at e0
    have e1 := (hint (l - 2) (by omega) (by omega)).2 (by omega)
    rw [show l - 2 + 1 = l - 1 by omega] at e1
    have e2 := (hdec (l - 1) (by omega) (by omega)).2.2.2
    rw [show l - 1 + 1 = l by omega] at e2
    have f1 := (hint s hs1 (by omega)).1 (by omega)
    have f2 := (hint' s hs1 (by omega)).1 (by omega)
    have hc0 : (0:ℝ) ≤ 2 * c * j := mul_nonneg (by linarith) (Nat.cast_nonneg j)
    refine ⟨hA0 s, ?_, by linarith, ?_⟩
    · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; nlinarith
    · exact sq_le_abs_mul_of_le_abs _ _ _ (by linarith) (le_abs.mpr (Or.inl (by linarith)))
        (le_abs.mpr (Or.inl (by linarith)))
  have hR : ∏ s ∈ Ico (l + 1) k, (|Y + lam s| + c) * (|Y + 1 + lam s| + c) ≤
      b ^ 3 * ∏ i ∈ Ico (l + 2) (k + 1), |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)| := by
    rw [prod_Ico_eq_prod_range, prod_Ico_eq_prod_range, show k + 1 - (l + 2) = k - (l + 1) by omega]
    have hn : ((k - (l + 1) : ℕ) : ℝ) ≤ b := by
      have : ((k - (l + 1) : ℕ) : ℝ) ≤ k := by exact_mod_cast (by omega : k - (l + 1) ≤ k)
      linarith
    apply prod_le_cube_mul_prod_of_bracket_chain b c (k - (l + 1)) hn hc hcb _
      (fun j => -Y - lam (l + 1 + j) - 1)
    intro j hj
    beta_reduce
    have e0 := hspread j (l + 1) (by omega) (by omega)
    have e1 := (hint (l + 1) (by omega) (by omega)).1 (by omega)
    have e2 := (hdec l h1l (by omega)).1
    have f1 := (hint (l + 1 + j) (by omega) (by omega)).2 (by omega)
    have f2 := (hint' (l + 1 + j) (by omega) (by omega)).2 (by omega)
    rw [show l + 1 + j + 1 = l + 2 + j by ring] at f1 f2
    have hc0 : (0:ℝ) ≤ 2 * c * j := mul_nonneg (by linarith) (Nat.cast_nonneg j)
    refine ⟨hA0 _, ?_, by linarith, ?_⟩
    · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; nlinarith
    · exact sq_le_abs_mul_of_le_abs _ _ _ (by linarith) (le_abs.mpr (Or.inr (by linarith)))
        (le_abs.mpr (Or.inr (by linarith)))
  have hLn : 0 ≤ ∏ i ∈ Ico 1 (l - 1), |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)| :=
    prod_nonneg fun _ _ => abs_nonneg _
  have hRn : 0 ≤ ∏ i ∈ Ico (l + 2) (k + 1), |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)| :=
    prod_nonneg fun _ _ => abs_nonneg _
  have hPQ : (∏ i ∈ Ico 1 (l - 1), |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)|) *
      ∏ i ∈ Ico (l + 2) (k + 1), |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)| ≤
      ∏ i ∈ Icc 1 k, |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)| := by
    have hLR' : Disjoint (Ico 1 (l - 1)) (Ico (l + 2) (k + 1)) := by
      rw [disjoint_left]; intro s h1 h2; simp only [mem_Ico] at h1 h2; omega
    have hsub' : Ico 1 (l - 1) ∪ Ico (l + 2) (k + 1) ⊆ Icc 1 k := by
      intro s hs; simp only [mem_union, mem_Ico, mem_Icc] at hs ⊢; omega
    rw [← prod_sdiff hsub', prod_union hLR']
    have hrest : (1:ℝ) ≤ ∏ i ∈ Icc 1 k \ (Ico 1 (l - 1) ∪ Ico (l + 2) (k + 1)),
        |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)| := by
      calc (1:ℝ) = ∏ i ∈ Icc 1 k \ (Ico 1 (l - 1) ∪ Ico (l + 2) (k + 1)), (1:ℝ) :=
            prod_const_one.symm
        _ ≤ _ := by
          apply prod_le_prod (fun _ _ => zero_le_one)
          intro i hi
          simp only [mem_sdiff, mem_union, mem_Ico, mem_Icc] at hi
          rw [abs_mul]
          have key : 1 ≤ |Y + 1 / 2 + u i| ∧ 1 ≤ |Y + 1 / 2 + u' i| := by
            rcases (by omega : (i = l - 1 ∧ 2 ≤ l) ∨ i = l ∨ (i = l + 1 ∧ l + 1 ≤ k))
              with ⟨hi1, hl2⟩ | hi1 | ⟨hi1, hl2⟩
            · have e := hdec (l - 1) (by omega) (by omega)
              rw [show l - 1 + 1 = l by omega] at e
              rw [hi1]
              exact ⟨le_abs.mpr (Or.inl (by linarith [e.2.2.2])),
                le_abs.mpr (Or.inl (by linarith [e.2.1]))⟩
            · rw [hi1]
              exact ⟨le_abs.mpr (Or.inr (by linarith)), le_abs.mpr (Or.inl (by linarith))⟩
            · have e := hdec l h1l (by omega)
              rw [hi1]
              exact ⟨le_abs.mpr (Or.inr (by linarith [e.1])),
                le_abs.mpr (Or.inr (by linarith [e.2.2.2]))⟩
          exact one_le_mul_of_one_le_of_one_le key.1 key.2
    calc _ = 1 * ((∏ i ∈ Ico 1 (l - 1), |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)|) *
          ∏ i ∈ Ico (l + 2) (k + 1), |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)|) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hrest (mul_nonneg hLn hRn)
  have hb3 : 0 ≤ b ^ 3 := pow_nonneg hb0 3
  calc _ ≤ b ^ (4 * (2 * r + 4)) *
        ((b ^ 3 * ∏ i ∈ Ico 1 (l - 1), |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)|) *
        (b ^ 3 * ∏ i ∈ Ico (l + 2) (k + 1), |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)|)) :=
        mul_le_mul hT (mul_le_mul hL hR (prod_nonneg fun s _ => hA0 s) (mul_nonneg hb3 hLn))
          (mul_nonneg (prod_nonneg fun s _ => hA0 s) (prod_nonneg fun s _ => hA0 s))
          (pow_nonneg hb0 _)
    _ = b ^ (4 * (2 * r + 4) + 3 + 3) *
        ((∏ i ∈ Ico 1 (l - 1), |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)|) *
        ∏ i ∈ Ico (l + 2) (k + 1), |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)|) := by
        rw [pow_add, pow_add]; ring
    _ ≤ b ^ (11 * (2 * r + 2)) * ∏ i ∈ Finset.Icc 1 k, |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)| :=
        mul_le_mul (pow_le_pow_right₀ hb1 (by omega)) hPQ (mul_nonneg hLn hRn) (pow_nonneg hb0 _)

open Finset in

theorem _root_.GlobalTheory.two_brackets_le_pow_mul_prod_entries : ∀ (k r l : ℕ) (b c Y : ℝ) (lam u u' : ℕ → ℝ), 1 ≤ l → l ≤ k → 1 ≤ c → c + 2 ≤ b → (k : ℝ) ≤ b → |u l| ≤ b → |u' l| ≤ b → (∀ s ∈ Finset.Icc 1 (k + 2 * r + 1), |lam s| ≤ b) → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + 2 * c ≤ lam s) → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k → (s ≠ l → lam s + 1 / 2 ≤ u s) ∧ (s + 1 ≠ l → u (s + 1) + 1 / 2 ≤ lam s)) → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k → (s ≠ l → lam s + 1 / 2 ≤ u' s) ∧ (s + 1 ≠ l → u' (s + 1) + 1 / 2 ≤ lam s)) → (∀ i : ℕ, 1 ≤ i → i ≤ k - 1 → u (i + 1) ≤ u i - 1 ∧ u' (i + 1) ≤ u' i - 1 ∧ u (i + 1) ≤ u' i - 1 ∧ u' (i + 1) ≤ u i - 1) → ((u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) ∨ (u' l + 2 ≤ -Y ∧ -Y ≤ u l - 2)) → (∏ s ∈ Finset.Icc 1 (k + 2 * r + 1), (|Y + lam s| + c)) * (∏ s ∈ Finset.Icc 1 (k + 2 * r + 1), (|Y + 1 + lam s| + c)) ≤ b ^ (11 * (2 * r + 2)) * ∏ i ∈ Finset.Icc 1 k, |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)| := by
  intro k r l b c Y lam u u' h1l hlk hc hcb hkb hul hu'l hlam hsp hint hint' hdec hY
  rcases hY with hY | hY
  · exact bracket_product_le_of_neg_between_lemma k r l b c Y lam u u' h1l hlk hc hcb hkb hul hu'l hlam hsp hint
      hint' hdec hY
  · have h := bracket_product_le_of_neg_between_lemma k r l b c Y lam u' u h1l hlk hc hcb hkb hu'l hul hlam hsp
      hint' hint (fun i hi hik => by
        obtain ⟨a1, a2, a3, a4⟩ := hdec i hi hik
        exact ⟨a2, a1, a4, a3⟩) hY
    calc _ ≤ _ := h
      _ = _ := by
        congr 1
        exact prod_congr rfl fun i _ => by rw [mul_comm]

end GlobalTheory
end

section
open Formalism.FourierDecayAlt Finset

namespace GlobalTheory.NormaliserCutBound

theorem prod_fin_eq_prod_Icc (n : ℕ) (f : Fin n → ℝ) (g : ℕ → ℝ)
    (h : ∀ s : Fin n, g (s.val + 1) = f s) : ∏ s, f s = ∏ s ∈ Finset.Icc 1 n, g s := by
  have h1 : ∏ s, f s = ∏ s : Fin n, g (s.val + 1) := Finset.prod_congr rfl (fun s _ => (h s).symm)
  rw [h1, Fin.prod_univ_eq_prod_range (fun s => g (s + 1)) n, ← Finset.Ico_add_one_right_eq_Icc,
    Finset.prod_Ico_eq_prod_range]
  simp [add_comm]

theorem qC_re (P : M.Par) (y : ℝ) :
    (M.qC P (y : ℂ)).re = I.qpoly P.k P.T P.T' P.u P.u' y := by
  have : M.qC P (y : ℂ) = ((I.qpoly P.k P.T P.T' P.u P.u' y : ℝ) : ℂ) := by
    unfold M.qC I.qpoly
    push_cast
    rfl
  rw [this, Complex.ofReal_re]

theorem main : ∀ (C b c : ℝ) (P : M.Par) (l : ℕ) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (nn : ℝ → ℝ) (Y : Finset ℝ), P.OK → 0 ≤ C → 1 ≤ l → l ≤ P.k → 1 ≤ c → c + 2 ≤ b → (P.k : ℝ) ≤ b → |P.u l| ≤ b → |P.u' l| ≤ b → (∀ s, |lam s| ≤ b) → (∀ s t : Fin (2 * P.r + P.k + 1), s.val + 1 = t.val → t.val + 2 ≤ P.k → lam t + 2 * c ≤ lam s) → (∀ s : Fin (2 * P.r + P.k + 1), s.val + 2 ≤ P.k → (s.val + 1 ≠ l → lam s + 1 / 2 ≤ P.u (s.val + 1)) ∧ (s.val + 2 ≠ l → P.u (s.val + 2) + 1 / 2 ≤ lam s)) → (∀ s : Fin (2 * P.r + P.k + 1), s.val + 2 ≤ P.k → (s.val + 1 ≠ l → lam s + 1 / 2 ≤ P.u' (s.val + 1)) ∧ (s.val + 2 ≠ l → P.u' (s.val + 2) + 1 / 2 ≤ lam s)) → b ^ (-(C * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T → b ^ (-(C * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T' → (∀ y, 0 ≤ nn y ∧ nn y ≤ ∏ s, (|y + lam s| + c)) → (∀ y ∈ Y, I.OnCut P.u P.u' l y) → ∀ y ∈ Y, nn y * nn (y + 1) ≤ (b ^ ((6 + C) * ((2 * P.r + 2 : ℕ) : ℝ))) ^ 2 * (M.qC P (y : ℂ)).re := by
  intro C b c P l lam nn Y hP hC hl hlk hc hcb hkb hu hu' hlam hgap hint hint' hT hT' hnn hcut y hy
  have hcy := hcut y hy
  have hb3 : 3 ≤ b := by linarith
  obtain ⟨n, hn⟩ : ∃ n, n = 2 * P.r + P.k + 1 := ⟨_, rfl⟩
  revert lam
  rw [← hn]
  intro lam hlam hgap hint hint' hnn
  let lamN : ℕ → ℝ := fun s => if h : s - 1 < n then lam ⟨s - 1, h⟩ else 0
  have hlamN : ∀ s : Fin n, lamN (s.val + 1) = lam s := by
    intro s
    simp [lamN, s.isLt]
  have hlamN' : ∀ (s : ℕ) (h : s - 1 < n), lamN s = lam ⟨s - 1, h⟩ := by
    intro s h
    simp [lamN, h]
  have hn' : P.k + 2 * P.r + 1 = n := by omega
  have hinter : I.Interlaces P.k P.u P.u' P.lo := by
    intro i hi
    have hg := hP.gap i hi
    unfold M.Par.hi at hg
    have h1 := min_le_left (P.u i) (P.u' i)
    have h2 := min_le_right (P.u i) (P.u' i)
    have h3 := le_max_left (P.u (i + 1)) (P.u' (i + 1))
    have h4 := le_max_right (P.u (i + 1)) (P.u' (i + 1))
    refine ⟨by linarith, by linarith, ?_, ?_⟩ <;> unfold M.Par.lo <;> linarith
  have hint2 : ∀ v : ℕ → ℝ, (∀ s : Fin n, s.val + 2 ≤ P.k →
      (s.val + 1 ≠ l → lam s + 1 / 2 ≤ v (s.val + 1)) ∧
        (s.val + 2 ≠ l → v (s.val + 2) + 1 / 2 ≤ lam s)) →
      ∀ s : ℕ, 1 ≤ s → s + 1 ≤ P.k → (s ≠ l → lamN s + 1 / 2 ≤ v s) ∧
        (s + 1 ≠ l → v (s + 1) + 1 / 2 ≤ lamN s) := by
    intro v hv s hs hsk
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    have ht : t < n := by omega
    have h := hv ⟨t, ht⟩ hsk
    rw [← hlamN ⟨t, ht⟩] at h
    exact h
  have hmain := GlobalTheory.two_brackets_le_pow_mul_prod_entries P.k P.r l b c y lamN P.u P.u' hl hlk hc hcb
    hkb hu hu'
    (by
      intro s hs
      rw [Finset.mem_Icc] at hs
      rw [hlamN' s (by omega)]
      exact hlam _)
    (by
      intro s hs hsk
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      have ht : t < n := by omega
      have ht' : t + 1 < n := by omega
      have h := hgap ⟨t, ht⟩ ⟨t + 1, ht'⟩ rfl (by simp only; omega)
      rw [← hlamN ⟨t, ht⟩, ← hlamN ⟨t + 1, ht'⟩] at h
      exact h)
    (hint2 _ hint) (hint2 _ hint')
    (by
      intro i hi hik
      obtain ⟨h1, h2, h3, h4⟩ := hinter i (Finset.mem_Icc.mpr ⟨hi, hik⟩)
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩)
    hcy
  rw [hn'] at hmain
  have e0 : ∏ s, (|y + lam s| + c) = ∏ s ∈ Finset.Icc 1 n, (|y + lamN s| + c) :=
    prod_fin_eq_prod_Icc n _ (fun s => |y + lamN s| + c) (fun s => by simp only [hlamN])
  have e1 : ∏ s, (|y + 1 + lam s| + c) = ∏ s ∈ Finset.Icc 1 n, (|y + 1 + lamN s| + c) :=
    prod_fin_eq_prod_Icc n _ (fun s => |y + 1 + lamN s| + c) (fun s => by simp only [hlamN])
  rw [← e0, ← e1] at hmain
  have hq := Formalism.FourierDecayAlt.P.q_positive_interlacing P.k P.u P.u' P.lo l y P.T P.T' hl hlk hinter hcy
    hP.T_pos hP.T'_pos
  have hTT : 0 < P.T * P.T' := mul_pos hP.T_pos hP.T'_pos
  have hqe : I.qpoly P.k P.T P.T' P.u P.u' y = (P.T * P.T') *
      ∏ i ∈ Finset.Icc 1 P.k, |(y + 1 / 2 + P.u i) * (y + 1 / 2 + P.u' i)| := by
    rw [← abs_of_pos hq]
    unfold I.qpoly
    rw [abs_mul, abs_neg, abs_of_pos hTT, Finset.abs_prod]
  have hsize := (GlobalTheory.LamSize.main C b P.T P.T' P.r 1 hC hb3 (by push_cast; linarith) hT hT').2
  rw [Nat.cast_one, one_mul] at hsize
  have hA : 0 ≤ ∏ i ∈ Finset.Icc 1 P.k, |(y + 1 / 2 + P.u i) * (y + 1 / 2 + P.u' i)| :=
    Finset.prod_nonneg (fun _ _ => abs_nonneg _)
  rw [qC_re, hqe, ← mul_assoc]
  calc nn y * nn (y + 1) ≤ (∏ s, (|y + lam s| + c)) * ∏ s, (|y + 1 + lam s| + c) :=
        mul_le_mul (hnn y).2 (hnn (y + 1)).2 (hnn (y + 1)).1 ((hnn y).1.trans (hnn y).2)
    _ ≤ _ := hmain
    _ ≤ _ := mul_le_mul_of_nonneg_right hsize hA

end GlobalTheory.NormaliserCutBound
end

section
open Formalism.FourierDecayAlt Finset

namespace GlobalTheory

theorem exists_grid_five_apart_on_cut :
    (∀ (u u' : ℕ → ℝ) (l M₀ : ℕ), 5 * (M₀ : ℝ) ≤ |u l - u' l| → ∃ Y : Finset ℝ, M₀ ≤ Y.card ∧
      (∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|) ∧
      ∀ y ∈ Y, I.OnCut u u' l y ∧ I.OnCut u u' l (y + 1)) ∧
    ∀ r : ℕ, 5 * (3 * (r + 1) * (2 * r + 1)) ≤ 30 * (r + 1) ^ 2 + 6 := by
  refine ⟨fun u u' l M₀ h => ?_, fun r => by nlinarith [Nat.zero_le r]⟩
  have hmax : min (u l) (u' l) + 5 * (M₀ : ℝ) ≤ max (u l) (u' l) := by
    have := max_sub_min_eq_abs (u l) (u' l)
    rw [abs_sub_comm] at h
    linarith
  refine ⟨(range M₀).image (fun i : ℕ => -(min (u l) (u' l) + 3 + 5 * (i : ℝ))), ?_, ?_, ?_⟩
  · rw [card_image_of_injective, card_range]
    intro i j hij
    have : (i : ℝ) = j := by
      simp only at hij
      linarith
    exact_mod_cast this
  · intro y hy y' hy' hne
    obtain ⟨i, -, rfl⟩ := mem_image.1 hy
    obtain ⟨j, -, rfl⟩ := mem_image.1 hy'
    have hij : i ≠ j := fun e => hne (by rw [e])
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hlt
      exact le_trans (by linarith) (le_abs_self _)
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast hlt
      exact le_trans (by linarith) (neg_le_abs _)
  · intro y hy
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hy
    have h1 : (i : ℝ) + 1 ≤ M₀ := by exact_mod_cast mem_range.1 hi
    have h0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    unfold I.OnCut
    rcases le_total (u l) (u' l) with hle | hle
    · rw [min_eq_left hle, max_eq_right hle] at hmax
      rw [min_eq_left hle]
      exact ⟨Or.inl ⟨by linarith, by linarith⟩, Or.inl ⟨by linarith, by linarith⟩⟩
    · rw [min_eq_right hle, max_eq_left hle] at hmax
      rw [min_eq_right hle]
      exact ⟨Or.inr ⟨by linarith, by linarith⟩, Or.inr ⟨by linarith, by linarith⟩⟩

end GlobalTheory
end

section
section
namespace GlobalTheory.GridsFromLayout

open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

noncomputable section

theorem cutWord_iff (P : M.Par) (l0 : ℕ) (w : List C.Letter) :
    KB.CutWord P l0 w ↔ (∀ l ∈ w, I.OnCut P.u P.u' l0 l.2) ∧ w.Pairwise (fun l l' => 2 < |l.2 - l'.2|) := by
  unfold KB.CutWord
  rw [List.pairwise_iff_get]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun l hl => ?_, fun i j hij => h2 i j hij.ne⟩
    obtain ⟨i, rfl⟩ := List.get_of_mem hl
    exact h1 i
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => h1 _ (List.get_mem _ _), fun i j hij => ?_⟩
    rcases lt_or_gt_of_ne hij with h | h
    · exact h2 i j h
    · rw [abs_sub_comm]; exact h2 j i h

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

open Finset in
private theorem two_lt_abs_sub_sub_of_five_le_of_abs_le_two {g b c : ℝ} (h : 5 ≤ |g - b|) (hc : |c| ≤ 2) :
    2 < |g - b - c| := by
  have := abs_sub_abs_le_abs_sub (g - b) c
  linarith

open Finset in
private theorem one_add_inv_pos_and_le_of_five_le_abs {x : ℝ} (hx : 5 ≤ |x|) : 0 < 1 + x⁻¹ ∧ 1 ≤ 5 / 4 * (1 + x⁻¹) := by
  have hx0 : x ≠ 0 := by intro h; rw [h, abs_zero] at hx; norm_num at hx
  have hinv : |x⁻¹| ≤ 1 / 5 := by
    rw [abs_inv, one_div]; exact inv_anti₀ (by norm_num) hx
  have := abs_le.1 hinv
  constructor <;> nlinarith [this.1, this.2]

open Finset in
private theorem exists_qw_eq_mul_pos_real_of_five_le_dist {S : Type} (q : ℂ → ℂ) (y : ℝ) :
    ∀ u : List (_root_.Formalism.FourierDecayAlt.Wd.Letter ℂ S), (∀ l ∈ u, ∃ t : ℝ, l.pt = t ∧ (l.plus = true → 5 ≤ |y - t|) ∧
      (l.plus = false → 5 ≤ |t - 1 - y|)) →
      ∃ ρ : ℝ, 0 < ρ ∧ 1 ≤ (5 / 4 : ℝ) ^ u.length * ρ ∧ _root_.Formalism.FourierDecayAlt.Wd.qw q u (y : ℂ) = q y * ρ
  | [], _ => ⟨1, one_pos, by simp, by simp [_root_.Formalism.FourierDecayAlt.Wd.qw]⟩
  | l :: w, h => by
    obtain ⟨ρ, hρ, hρ1, hρeq⟩ := exists_qw_eq_mul_pos_real_of_five_le_dist q y w (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨t, ht, hplus, hminus⟩ := h l (List.mem_cons_self)
    cases hl : l.plus
    · obtain ⟨f0, f1⟩ := one_add_inv_pos_and_le_of_five_le_abs (hminus hl)
      refine ⟨ρ * (1 + (t - 1 - y)⁻¹), mul_pos hρ f0, ?_, ?_⟩
      · rw [List.length_cons, pow_succ]
        nlinarith [mul_le_mul hρ1 f1 zero_le_one (by positivity)]
      · have hz : (t : ℂ) - y - 1 ≠ 0 := by
          have : t - 1 - y ≠ 0 := by intro h0; have := hminus hl; rw [h0, abs_zero] at this; norm_num at this
          exact_mod_cast (show (t : ℝ) - y - 1 ≠ 0 by intro h1; apply this; linarith)
        have hz' : (t : ℂ) - 1 - y ≠ 0 := by
          intro h1; apply hz; linear_combination h1
        simp only [_root_.Formalism.FourierDecayAlt.Wd.qw, hl, Bool.false_eq_true, if_false, hρeq, ht]
        push_cast
        rw [show (t : ℂ) - 1 - y = (t : ℂ) - y - 1 by ring]
        field_simp
        ring
    · obtain ⟨f0, f1⟩ := one_add_inv_pos_and_le_of_five_le_abs (hplus hl)
      refine ⟨ρ * (1 + (y - t)⁻¹), mul_pos hρ f0, ?_, ?_⟩
      · rw [List.length_cons, pow_succ]
        nlinarith [mul_le_mul hρ1 f1 zero_le_one (by positivity)]
      · have hz : (y : ℂ) - t ≠ 0 := by
          have : y - t ≠ 0 := by intro h0; have := hplus hl; rw [h0, abs_zero] at this; norm_num at this
          exact_mod_cast this
        simp only [_root_.Formalism.FourierDecayAlt.Wd.qw, hl, if_true, hρeq, ht]
        push_cast
        field_simp

open Finset in
private theorem sum_abs_lagCo_le_one_of_five_separated {d : ℕ} (y : Fin (d + 1) → ℝ)
    (hy : ∀ i j, i ≠ j → 5 ≤ |y i - y j|) : ∑ j, |_root_.Formalism.FourierDecayAlt.F7.lagCo y j| ≤ 1 := by
  have key : ∀ n : ℕ, n + 1 ≤ 5 ^ n := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ]; omega
  have h1 : ∀ j, |_root_.Formalism.FourierDecayAlt.F7.lagCo y j| ≤ (1 / 5 : ℝ) ^ d := by
    intro j
    unfold _root_.Formalism.FourierDecayAlt.F7.lagCo
    rw [Finset.abs_prod]
    calc ∏ i ∈ Finset.univ.erase j, |(y j - y i)⁻¹| ≤ ∏ i ∈ Finset.univ.erase j, (1 / 5 : ℝ) :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i hi => by
            rw [abs_inv, one_div]
            exact inv_anti₀ (by norm_num) (hy j i (Finset.ne_of_mem_erase hi).symm))
      _ = (1 / 5) ^ d := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin, Nat.add_sub_cancel]
  have h2 : ((d : ℝ) + 1) ≤ 5 ^ d := by exact_mod_cast key d
  calc ∑ j, |_root_.Formalism.FourierDecayAlt.F7.lagCo y j| ≤ ∑ _j : Fin (d + 1), (1 / 5 : ℝ) ^ d := Finset.sum_le_sum fun j _ => h1 j
    _ = ((d : ℝ) + 1) / 5 ^ d := by simp [div_eq_mul_inv]
    _ ≤ 1 := by rw [div_le_one (by positivity)]; exact h2

open Finset in
private theorem exists_grid_of_layout_lemma {P : _root_.Formalism.FourierDecayAlt.M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq) (nn : ℝ → ℝ) (Y : Finset ℝ) (Λ Λ₀ : ℝ) (K N : ℕ)
    (hnn : ∀ y, 0 < nn y) (hsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|)
    (hcard : N * (2 * P.r + 1) ≤ Y.card)
    (hcut : ∀ y ∈ Y, _root_.Formalism.FourierDecayAlt.I.OnCut P.u P.u' p.l0 y ∧ _root_.Formalism.FourierDecayAlt.I.OnCut P.u P.u' p.l0 (y + 1))
    (hq : ∀ y ∈ Y, nn y * nn (y + 1) ≤ Λ₀ ^ 2 * (_root_.Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re) (hΛ : 0 ≤ Λ)
    (hΛ₀ : Λ₀ ^ 2 * (5 / 4 : ℝ) ^ N ≤ Λ ^ 2) (d : ℕ) (hd : d ≤ 2 * P.r) (w : List _root_.Formalism.FourierDecayAlt.C.Letter)
    (hw : _root_.Formalism.FourierDecayAlt.TBB.AdmW P p.l0 Y w) (hlen : w.length + K ≤ N) : ∃ grid, _root_.Formalism.FourierDecayAlt.P.TBBx5.GridOK p nn Y Λ K w d grid := by
  classical
  unfold _root_.Formalism.FourierDecayAlt.TBB.AdmW at hw
  obtain ⟨hwcut, hwY⟩ := hw
  rw [_root_.Formalism.FourierDecayAlt.P.PBD.cutWord_iff] at hwcut
  obtain ⟨hwon, hwpair⟩ := hwcut
  let base : _root_.Formalism.FourierDecayAlt.C.Letter → ℝ := fun l => if l.1 = true then l.2 else l.2 - 1
  have hbase : ∀ l ∈ w, base l ∈ Y ∧ (l.2 = base l ∨ l.2 = base l + 1) := by
    intro l hl
    obtain ⟨y', hy', h | h⟩ := hwY l hl
    · subst h; simp [base, hy']
    · subst h; simp [base, hy']
  set B := (w.map base).toFinset with hB
  set Y' := Y \ B with hY'
  have hBcard : B.card ≤ w.length := by
    rw [hB]; exact (List.toFinset_card_le _).trans (by simp)
  have hY'card : K * (d + 1) ≤ Y'.card := by
    have h1 : Y.card - B.card ≤ Y'.card := by rw [hY']; exact Finset.le_card_sdiff B Y
    have h2 : K * (d + 1) ≤ K * (2 * P.r + 1) := Nat.mul_le_mul_left _ (by omega)
    have h3 : K * (2 * P.r + 1) + (N - K) ≤ N * (2 * P.r + 1) := by
      obtain ⟨m, hm⟩ : ∃ m, N = K + m := ⟨N - K, by omega⟩
      rw [hm, Nat.add_sub_cancel_left, Nat.add_mul]
      have : m ≤ m * (2 * P.r + 1) := Nat.le_mul_of_pos_right m (by omega)
      omega
    omega
  obtain ⟨e⟩ : Nonempty (Fin K × Fin (d + 1) ↪ Y') := Function.Embedding.nonempty_of_card_le (by
    simpa [Fintype.card_prod, Fintype.card_fin] using hY'card)
  let grid : Fin K → Fin (d + 1) → ℝ := fun a i => (e (a, i) : ℝ)
  have hgY' : ∀ a i, grid a i ∈ Y' := fun a i => (e (a, i)).2
  have hgY : ∀ a i, grid a i ∈ Y := fun a i => (Finset.mem_sdiff.1 (hgY' a i)).1
  have hgB : ∀ a i, grid a i ∉ B := fun a i => (Finset.mem_sdiff.1 (hgY' a i)).2
  have hginj : ∀ a i b j, grid a i = grid b j → (a, i) = (b, j) := fun a i b j h =>
    e.injective (Subtype.ext h)
  have hfar : ∀ a i, ∀ l ∈ w, 5 ≤ |grid a i - base l| := by
    intro a i l hl
    refine hsep _ (hgY a i) _ (hbase l hl).1 ?_
    intro h
    apply hgB a i
    rw [hB, List.mem_toFinset, h]
    exact List.mem_map_of_mem hl
  unfold _root_.Formalism.FourierDecayAlt.P.TBBx5.GridOK
  refine ⟨grid, fun a i j h => (Prod.mk.inj (hginj a i a j h)).2, hgY, ?_, ?_⟩
  · intro n
    have hys : _root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n = List.ofFn fun a => grid a (n a) := rfl
    have hpair : List.Pairwise (fun y y' => 2 < |y - y'|) (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n) := by
      rw [hys, List.pairwise_ofFn]
      intro a b hab
      have hne : grid a (n a) ≠ grid b (n b) := fun h => (ne_of_lt hab) (Prod.mk.inj (hginj _ _ _ _ h)).1
      have := hsep _ (hgY _ _) _ (hgY _ _) hne
      linarith
    have hmem : ∀ y ∈ _root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n, ∃ a, y = grid a (n a) := by
      rw [hys]
      intro y hy
      obtain ⟨a, ha⟩ := List.mem_ofFn.1 hy
      exact ⟨a, ha.symm⟩
    refine ⟨?_, ?_, hpair⟩
    · rw [_root_.Formalism.FourierDecayAlt.P.PBD.cutWord_iff, _root_.Formalism.FourierDecayAlt.P.TBBx5.plusW_eq]
      constructor
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
          obtain ⟨a, rfl⟩ := hmem y hy
          exact (hcut _ (hgY _ _)).1
        · exact hwon x hx
      · rw [List.pairwise_append]
        refine ⟨?_, hwpair, ?_⟩
        · rw [List.pairwise_map]; exact hpair
        · intro x hx l hl
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
          obtain ⟨a, rfl⟩ := hmem y hy
          have h5 := hfar a (n a) l hl
          rcases (hbase l hl).2 with h | h
          · rw [h, show grid a (n a) - base l = grid a (n a) - base l - 0 by ring]
            exact two_lt_abs_sub_sub_of_five_le_of_abs_le_two h5 (by norm_num)
          · rw [h, show grid a (n a) - (base l + 1) = grid a (n a) - base l - 1 by ring]
            exact two_lt_abs_sub_sub_of_five_le_of_abs_le_two h5 (by norm_num)
    · rw [_root_.Formalism.FourierDecayAlt.P.PBD.cutWord_iff, _root_.Formalism.FourierDecayAlt.P.TBBx5.minusW_eq]
      constructor
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
          obtain ⟨a, rfl⟩ := hmem y hy
          exact (hcut _ (hgY _ _)).2
        · exact hwon x hx
      · rw [List.pairwise_append]
        refine ⟨?_, hwpair, ?_⟩
        · rw [List.pairwise_map]
          exact hpair.imp fun {y y'} h => by simpa [show y + 1 - (y' + 1) = y - y' by ring] using h
        · intro x hx l hl
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
          obtain ⟨a, rfl⟩ := hmem y hy
          have h5 := hfar a (n a) l hl
          rcases (hbase l hl).2 with h | h
          · rw [h, show grid a (n a) + 1 - base l = grid a (n a) - base l - (-1) by ring]
            exact two_lt_abs_sub_sub_of_five_le_of_abs_le_two h5 (by norm_num)
          · rw [h, show grid a (n a) + 1 - (base l + 1) = grid a (n a) - base l - 0 by ring]
            exact two_lt_abs_sub_sub_of_five_le_of_abs_le_two h5 (by norm_num)
  · have hposition_len : (_root_.Formalism.FourierDecayAlt.D.positionted w).length = w.length := by unfold _root_.Formalism.FourierDecayAlt.D.positionted; simp
    have hF : ∀ y ∈ Y, y ∉ B → 0 ≤ nn y * nn (y + 1) / (_root_.Formalism.FourierDecayAlt.Wd.qw (_root_.Formalism.FourierDecayAlt.M.qC P) (_root_.Formalism.FourierDecayAlt.D.positionted w) (y : ℂ)).re ∧
        nn y * nn (y + 1) / (_root_.Formalism.FourierDecayAlt.Wd.qw (_root_.Formalism.FourierDecayAlt.M.qC P) (_root_.Formalism.FourierDecayAlt.D.positionted w) (y : ℂ)).re ≤ Λ ^ 2 := by
      intro y hy hyB
      have hcond : ∀ l ∈ _root_.Formalism.FourierDecayAlt.D.positionted w, ∃ t : ℝ, l.pt = t ∧ (l.plus = true → 5 ≤ |y - t|) ∧
          (l.plus = false → 5 ≤ |t - 1 - y|) := by
        intro l hl
        unfold _root_.Formalism.FourierDecayAlt.D.positionted at hl
        obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hl
        have hla : w.get a ∈ w := List.get_mem w a
        have hfar' : 5 ≤ |y - base (w.get a)| := by
          refine hsep _ hy _ (hbase _ hla).1 ?_
          intro h
          apply hyB
          rw [hB, List.mem_toFinset, h]
          exact List.mem_map_of_mem hla
        refine ⟨(w.get a).2, rfl, fun hp => ?_, fun hm => ?_⟩
        · have hp' : (w.get a).1 = true := hp
          have : base (w.get a) = (w.get a).2 := if_pos hp'
          rw [this] at hfar'
          exact hfar'
        · have hm' : (w.get a).1 = false := hm
          have : base (w.get a) = (w.get a).2 - 1 := if_neg (by rw [hm']; decide)
          rw [this, abs_sub_comm] at hfar'
          exact hfar'
      obtain ⟨ρ, hρ, hρ1, hρeq⟩ := exists_qw_eq_mul_pos_real_of_five_le_dist (_root_.Formalism.FourierDecayAlt.M.qC P) y (_root_.Formalism.FourierDecayAlt.D.positionted w) hcond
      rw [hposition_len] at hρ1
      have hre : (_root_.Formalism.FourierDecayAlt.Wd.qw (_root_.Formalism.FourierDecayAlt.M.qC P) (_root_.Formalism.FourierDecayAlt.D.positionted w) (y : ℂ)).re = (_root_.Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re * ρ := by
        rw [hρeq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      have hnum : 0 < nn y * nn (y + 1) := mul_pos (hnn _) (hnn _)
      have hqy := hq y hy
      have hqpos : 0 < (_root_.Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re := by
        by_contra hle
        push_neg at hle
        nlinarith [sq_nonneg Λ₀]
      rw [hre]
      have hden : 0 < (_root_.Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re * ρ := mul_pos hqpos hρ
      refine ⟨div_nonneg hnum.le hden.le, ?_⟩
      rw [div_le_iff₀ hden]
      have hpow : (5 / 4 : ℝ) ^ w.length ≤ (5 / 4) ^ N :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have h1 : Λ₀ ^ 2 ≤ Λ ^ 2 * ρ := by
        have : Λ₀ ^ 2 ≤ Λ₀ ^ 2 * ((5 / 4 : ℝ) ^ w.length * ρ) := le_mul_of_one_le_right (sq_nonneg _) hρ1
        nlinarith [sq_nonneg Λ₀, mul_le_mul_of_nonneg_right hpow hρ.le]
      nlinarith
    have hterm : ∀ n : Fin K → Fin (d + 1), √((List.map nn (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n)).prod *
        (List.map (fun y => nn (y + 1)) (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n)).prod /
        (List.map (fun y : ℝ => (_root_.Formalism.FourierDecayAlt.Wd.qw (_root_.Formalism.FourierDecayAlt.M.qC P) (_root_.Formalism.FourierDecayAlt.D.positionted w) (y : ℂ)).re) (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n)).prod) ≤ Λ ^ K := by
      intro n
      have hys : _root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n = List.ofFn fun a => grid a (n a) := rfl
      rw [hys]
      simp only [List.map_ofFn, List.prod_ofFn, Function.comp_def]
      rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
      calc _ ≤ √(∏ _a : Fin K, Λ ^ 2) := Real.sqrt_le_sqrt (Finset.prod_le_prod
              (fun a _ => (hF _ (hgY a (n a)) (hgB a (n a))).1)
              (fun a _ => (hF _ (hgY a (n a)) (hgB a (n a))).2))
        _ = Λ ^ K := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm, pow_mul]
          exact Real.sqrt_sq (pow_nonneg hΛ K)
    refine le_trans (Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hterm n) (abs_nonneg _)) ?_
    rw [← Finset.sum_mul]
    simp_rw [Finset.abs_prod]
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (t := fun _ => Finset.univ) (f := fun a j => |_root_.Formalism.FourierDecayAlt.F7.lagCo (grid a) j|)]
    calc (∏ a, ∑ j, |_root_.Formalism.FourierDecayAlt.F7.lagCo (grid a) j|) * Λ ^ K ≤ 1 * Λ ^ K :=
          mul_le_mul_of_nonneg_right (Finset.prod_le_one
            (fun a _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
            (fun a _ => sum_abs_lagCo_le_one_of_five_separated _ (fun i j hij =>
              hsep _ (hgY a i) _ (hgY a j) (fun h => hij (Prod.mk.inj (hginj a i a j h)).2))))
            (pow_nonneg hΛ K)
      _ = Λ ^ K := one_mul _

open Finset in

theorem _root_.GlobalTheory.GridsFromLayout.main : ∀ (P : _root_.Formalism.FourierDecayAlt.M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq) (nn : ℝ → ℝ) (Y : Finset ℝ) (Λ Λ₀ : ℝ) (K N : ℕ), (∀ y, 0 < nn y) → ((∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|) ∧ N * (2 * P.r + 1) ≤ Y.card ∧ ∀ y ∈ Y, _root_.Formalism.FourierDecayAlt.I.OnCut P.u P.u' p.l0 y ∧ _root_.Formalism.FourierDecayAlt.I.OnCut P.u P.u' p.l0 (y + 1)) → (∀ y ∈ Y, nn y * nn (y + 1) ≤ Λ₀ ^ 2 * (_root_.Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re) → 0 ≤ Λ → Λ₀ ^ 2 * (5 / 4 : ℝ) ^ N ≤ Λ ^ 2 → _root_.Formalism.FourierDecayAlt.P.TBBx5.WaveGrid p nn Y Λ K N ∧ _root_.Formalism.FourierDecayAlt.P.TBBx5.LiftGrid p nn Y Λ K N := by
  intro P Wp Wq _ _ _ _ _ _ p nn Y Λ Λ₀ K N hnn ⟨hsep, hcard, hcut⟩ hq hΛ hΛ₀
  refine ⟨?_, ?_⟩
  · unfold _root_.Formalism.FourierDecayAlt.P.TBBx5.WaveGrid
    intro j hj w hw hlen
    exact exists_grid_of_layout_lemma p nn Y Λ Λ₀ K N hnn hsep hcard hcut hq hΛ hΛ₀ _ (by omega) w hw hlen
  · unfold _root_.Formalism.FourierDecayAlt.P.TBBx5.LiftGrid
    intro b s hb hs hbs w hw hlen
    exact exists_grid_of_layout_lemma p nn Y Λ Λ₀ K N hnn hsep hcard hcut hq hΛ hΛ₀ _ (by omega) w hw hlen

end

end GlobalTheory.GridsFromLayout
end

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.waveGrid_liftGrid_of_layout_normaliserBound : ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (Y : Finset ℝ) (Λ Λ₀ : ℝ) (K N : ℕ), (∀ y, 0 < nn y) → ((∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|) ∧ N * (2 * P.r + 1) ≤ Y.card ∧ ∀ y ∈ Y, I.OnCut P.u P.u' p.l0 y ∧ I.OnCut P.u P.u' p.l0 (y + 1)) → (∀ y ∈ Y, nn y * nn (y + 1) ≤ Λ₀ ^ 2 * (M.qC P (y : ℂ)).re) → 0 ≤ Λ → Λ₀ ^ 2 * (5 / 4 : ℝ) ^ N ≤ Λ ^ 2 → TBBx5.WaveGrid p nn Y Λ K N ∧ TBBx5.LiftGrid p nn Y Λ K N := by
  atlas_forward_decl GlobalTheory.GridsFromLayout.main
end

section
section
open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants

namespace GlobalTheory.GridAtPlace

theorem pow_absorb (C b : ℝ) (r : ℕ) (hb : 3 ≤ b) :
    (b ^ ((6 + C) * ((2 * r + 2 : ℕ) : ℝ))) ^ 2 * (5 / 4 : ℝ) ^ (3 * (r + 1)) ≤
      (b ^ ((7 + C) * ((2 * r + 2 : ℕ) : ℝ))) ^ 2 := by
  have hb0 : 0 < b := by linarith
  have e : b ^ ((7 + C) * ((2 * r + 2 : ℕ) : ℝ)) =
      b ^ ((6 + C) * ((2 * r + 2 : ℕ) : ℝ)) * b ^ (2 * r + 2) := by
    rw [← Real.rpow_natCast b (2 * r + 2), ← Real.rpow_add hb0]
    congr 1
    ring
  rw [e, mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  rw [← pow_mul]
  calc (5 / 4 : ℝ) ^ (3 * (r + 1)) ≤ b ^ (3 * (r + 1)) :=
        pow_le_pow_left₀ (by norm_num) (by linarith) _
    _ ≤ b ^ ((2 * r + 2) * 2) := pow_le_pow_right₀ (by linarith) (by omega)

theorem main : ∀ (C b c : ℝ) (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ), 0 ≤ C → GridNum C b c P p.l0 lam → ((30 * (P.r + 1) ^ 2 + 6 : ℕ) : ℝ) ≤ |P.u p.l0 - P.u' p.l0| → (∀ y, 0 < Pst lam c y) ∧ 1 ≤ b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ)) ∧ ∃ Y : Finset ℝ, TBBx5.WaveGrid p (Pst lam c) Y (b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ))) 3 (3 * (P.r + 1)) ∧ TBBx5.LiftGrid p (Pst lam c) Y (b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ))) 3 (3 * (P.r + 1)) := by
  intro C b c P Wp Wq _ _ _ _ _ _ p lam hC hG hcut
  obtain ⟨hc, hcb, hkb, hu, hu', hlam, hgap, hint, hint', hT, hT'⟩ := hG
  have hb3 : 3 ≤ b := by linarith
  have hpos : ∀ y, 0 < Pst lam c y := fun y =>
    Finset.prod_pos (fun s _ => by have := abs_nonneg (y + lam s); linarith)
  have hone : 1 ≤ b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ)) :=
    Real.one_le_rpow (by linarith) (by positivity)
  refine ⟨hpos, hone, ?_⟩
  obtain ⟨Y, hcard, hsep, hon⟩ := GlobalTheory.exists_grid_five_apart_on_cut.1 P.u P.u' p.l0
    (3 * (P.r + 1) * (2 * P.r + 1)) (le_trans (by
      exact_mod_cast GlobalTheory.exists_grid_five_apart_on_cut.2 P.r) hcut)
  have hNQ := GlobalTheory.NormaliserCutBound.main C b c P p.l0 lam (Pst lam c) Y p.hP.1 hC p.hl.1 p.hl.2.1 hc hcb hkb
    hu hu' hlam (fun s t hst _ => hgap s t (by rw [Fin.lt_def]; omega)) hint hint' hT hT'
    (fun y => ⟨(hpos y).le, le_rfl⟩) (fun y hy => (hon y hy).1)
  exact ⟨Y, GlobalTheory.T.waveGrid_liftGrid_of_layout_normaliserBound P Wp Wq p (Pst lam c) Y _ _ 3 (3 * (P.r + 1)) hpos ⟨hsep, hcard, hon⟩ hNQ
    (by linarith) (pow_absorb C b P.r hb3)⟩

end GlobalTheory.GridAtPlace
end

open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grids_at_place_longCut_normaliserPositive : ∀ (C b c : ℝ) (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ), 0 ≤ C → GridNum C b c P p.l0 lam → ((30 * (P.r + 1) ^ 2 + 6 : ℕ) : ℝ) ≤ |P.u p.l0 - P.u' p.l0| → (∀ y, 0 < Pst lam c y) ∧ 1 ≤ b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ)) ∧ ∃ Y : Finset ℝ, TBBx5.WaveGrid p (Pst lam c) Y (b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ))) 3 (3 * (P.r + 1)) ∧ TBBx5.LiftGrid p (Pst lam c) Y (b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ))) 3 (3 * (P.r + 1)) := by
  atlas_forward_decl GlobalTheory.GridAtPlace.main
end
