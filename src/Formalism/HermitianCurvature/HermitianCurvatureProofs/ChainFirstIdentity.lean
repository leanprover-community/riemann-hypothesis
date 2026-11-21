import Formalism.HermitianCurvature.HermitianCurvatureProofs.AAvCongr

section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem keyS_inj (k r : ℕ) : Function.Injective (keyS k r) := by
  intro p q hpq
  apply Fin.ext
  have hp := p.isLt
  have hq := q.isLt
  unfold keyS at hpq
  split_ifs at hpq <;> omega

theorem keyS_esI (k r : ℕ) (x : Fin r) : keyS k r (esI k r x) = x.val := by
  have hx := x.isLt
  have c : r + k < 2 * r + k - x.val := by omega
  simp only [keyS, Formalism.QuantumDeterminants.esI, c, if_true]
  omega

theorem star_sgnW (m : ℕ) : star (sgnW m) = sgnW m := by
  simp [sgnW]

theorem neg_one_sq' (s : ℕ) : ((-1 : ℂ) ^ s) * ((-1) ^ s) = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

theorem zb_col_zero (i0 s' : ℕ) (h : Matrix (Fin i0) (Fin i0) ℂ) (t : ℂ) (a : ℕ) (ha : a < i0 + s') :
    Zb i0 (s' + 1) h t a i0 = 0 := by
  unfold Zb
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem sgnW_succ' (s : ℕ) : sgnW (s + 1) = (-1) ^ s * sgnW s := by
  unfold sgnW
  rw [← pow_add]
  congr 1
  cases s with
  | zero => rfl
  | succ k =>
    have e : (k + 1 + 1) * (k + 1 + 1 - 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1) := by
      simp only [Nat.add_sub_cancel]
      ring
    rw [e, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    ring

theorem first_expansion_identity : ExpansionOmittedColumn := by
  intro A _ _ M _ _ k r z' E La xi i0 s h t u hs hj hR hdet ht hxi
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hm : i0 + s' ≤ r := by omega
  rw [AAx_congr k r E xi (show i0 + (s' + 1) - 1 = i0 + s' by omega) _ hm u]
  have hhead : AAx k r E xi i0 (by omega) u =
      h.det • qminor E (xR k r i0 (by omega)) (xR k r i0 (by omega)) u := by
    apply AAx_head
    · intro a p ha hp
      rw [hxi a p (by omega)]
      split_ifs with hp'
      · unfold Zb
        rw [dif_pos ha, dif_neg (by omega)]
      · rfl
    · intro a b
      have ha := a.isLt
      have hb := b.isLt
      rw [hxi _ _ (by simp only [Fin.coe_castLE]; omega)]
      rw [if_pos (by simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE]; omega)]
      simp [Zb, xR, Formalism.QuantumDeterminants.eI, ha, hb]
  have he : StrictMono (fun l : Fin (i0 + s') =>
      xR k r (i0 + s' + 1) (by omega) ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l)) := by
    intro a b hab
    have := (Fin.strictMono_succAbove (⟨i0, by omega⟩ : Fin (i0 + s' + 1))) hab
    rw [Fin.lt_def] at this ⊢
    simpa [xR, Formalism.QuantumDeterminants.eI] using this
  have hmain : AAx k r E xi (i0 + s') hm u = (h.det * t ^ s' * sgnW s') •
      qminor E (xR k r (i0 + s') hm)
        (fun l => xR k r (i0 + s' + 1) (by omega) ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l)) u := by
    classical
    have hX : ∀ (a : Fin (i0 + s')) (p : Fin (2 * r + k + 1)),
        p ∉ {p : Fin (2 * r + k + 1) | p.val < i0 + s' + 1 ∧ p.val ≠ i0} → xi (Fin.castLE hm a) p = 0 := by
      intro a p hp
      simp only [Set.mem_setOf_eq, not_and, not_not] at hp
      have ha := a.isLt
      rw [hxi _ p (by simp only [Fin.coe_castLE]; omega)]
      split_ifs with hp1
      · rw [hp (by omega)]
        exact zb_col_zero i0 s' h t _ (by simp only [Fin.coe_castLE]; omega)
      · rfl
    have hu : ∀ c : Fin (i0 + s') → Fin (2 * r + k + 1), StrictMono c →
        (∀ l, c l ∈ {p : Fin (2 * r + k + 1) | p.val < i0 + s' + 1 ∧ p.val ≠ i0}) →
        c = fun l => xR k r (i0 + s' + 1) (by omega) ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l) := by
      intro c hc hS
      apply uniq_mono _ _ he hc
      intro l
      obtain ⟨h1, h2⟩ := hS l
      have hne : (⟨(c l).val, h1⟩ : Fin (i0 + s' + 1)) ≠ ⟨i0, by omega⟩ := fun e => h2 (congrArg Fin.val e)
      obtain ⟨j, hj'⟩ := Fin.exists_succAbove_eq hne
      refine ⟨j, ?_⟩
      apply Fin.ext
      simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE, hj']
    have hs := sum_single (M := A) StrictMono (fun a p => xi (Fin.castLE hm a) p)
      {p : Fin (2 * r + k + 1) | p.val < i0 + s' + 1 ∧ p.val ≠ i0} hX _ he hu
      (fun c => qminor E (xR k r (i0 + s') hm) c u)
    have hdet' : (Matrix.of fun a l : Fin (i0 + s') => xi (Fin.castLE hm a)
        (xR k r (i0 + s' + 1) (by omega) ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l))).det =
        h.det * t ^ s' * sgnW s' := by
      have hp := minors_first_case i0 s' h t ⟨i0, by omega⟩
      rw [if_pos rfl] at hp
      rw [← hp]
      congr 1
      ext a l
      have ha := a.isLt
      have hl := ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l).isLt
      simp only [Matrix.of_apply]
      rw [hxi _ _ (by simp only [Fin.coe_castLE]; omega)]
      rw [if_pos (by simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE]; omega)]
      simp only [xR, Formalism.QuantumDeterminants.eI, Fin.coe_castLE]
    unfold AAx
    rw [← hdet']
    convert hs using 1
  have hpeel := first_peeling_identity A k r z' E (i0 + s') (by omega) ⟨i0, by omega⟩ u
  have hL := la_congr hR hpeel
  have hsc : (h.det * t ^ (s' + 1) * sgnW (s' + 1))⁻¹ * (h.det * t ^ s' * sgnW s') =
      (-1 : ℂ) ^ (s' + 1 - 1) * t⁻¹ * (h.det⁻¹ * h.det) := by
    rw [sgnW_succ', Nat.add_sub_cancel, scal_E _ _ _ _ s' hdet ht (sgnW_sq s') (neg_one_sq' s')]
  rw [hmain, hhead, map_smul, map_smul, hL, (derivative_leading_zb i0 (s' + 1) h t).2,
    (derivative_leading_zb i0 (s' + 1) h t).1, smul_smul, smul_smul, smul_smul]
  congr 1
  rw [hsc]
  ring

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem det_star {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.of fun a b => star (M a b)).det = star M.det := by
  have e : (Matrix.of fun a b => star (M a b)) = M.conjTranspose.transpose := by
    ext a b
    simp [Matrix.conjTranspose_apply]
  rw [e, Matrix.det_transpose, Matrix.det_conjTranspose]

theorem keyS_sR (k r m : ℕ) (hm : m ≤ r) (l : Fin m) : keyS k r (sR k r m hm l) = l.val := by
  simp only [sR]
  rw [keyS_esI]
  rfl

theorem AAv_head {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (y : Fin r → Fin (2 * r + k + 1) → ℂ) (i0 : ℕ) (hi0 : i0 ≤ r) (h : Matrix (Fin i0) (Fin i0) ℂ) (ell : ℂ)
    (hz : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 → p ∉ Set.range (sR k r i0 hi0) → y a p = 0)
    (hh : ∀ a b : Fin i0, y (Fin.castLE hi0 a) (sR k r i0 hi0 b) = star (h a b)) :
    AAv k r E y i0 hi0 ell = star h.det • qminor E (sR k r i0 hi0) (sR k r i0 hi0) (ell + (i0 : ℂ) - 1) := by
  classical
  have hsv : ∀ l : Fin i0, (sR k r i0 hi0 l).val = 2 * r + k - l.val := by
    intro l
    simp [sR, Formalism.QuantumDeterminants.esI]
  have he : StrictMono (fun l => keyS k r (sR k r i0 hi0 l)) := by
    intro a b hab
    simp only [keyS_sR]
    exact hab
  have hX : ∀ (a : Fin i0) (p : Fin (2 * r + k + 1)), p ∉ Set.range (sR k r i0 hi0) →
      y (Fin.castLE hi0 a) p = 0 := by
    intro a p hp
    exact hz _ p a.isLt hp
  have hu : ∀ c : Fin i0 → Fin (2 * r + k + 1), StrictMono (fun l => keyS k r (c l)) →
      (∀ l, c l ∈ Set.range (sR k r i0 hi0)) → c = sR k r i0 hi0 := by
    intro c hc hS
    exact uniq_key (keyS k r) (keyS_inj k r) (sR k r i0 hi0) c he hc hS
  have hs := sum_single (M := A) (fun B : Fin i0 → Fin (2 * r + k + 1) => StrictMono (fun l => keyS k r (B l)))
    (fun a p => y (Fin.castLE hi0 a) p) (Set.range (sR k r i0 hi0)) hX (sR k r i0 hi0) he hu
    (fun B => qminor E B (sR k r i0 hi0) (ell + (i0 : ℂ) - 1))
  have hdet : (Matrix.of fun a l : Fin i0 => y (Fin.castLE hi0 a) (sR k r i0 hi0 l)).det = star h.det := by
    rw [← det_star]
    congr 1
    ext a b
    exact hh a b
  unfold AAv
  rw [← hdet]
  convert hs using 1

theorem second_expansion_identity : ExpansionDualColumn := by
  intro A _ _ M _ _ k r z' E La y i0 s h t ell hs hj hG hR hh ht hy
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hm : i0 + s' ≤ r := by omega
  have hm' : i0 + s' + 1 ≤ r := by omega
  rw [AAv_congr k r E y (show i0 + (s' + 1) - 1 = i0 + s' by omega) _ hm]
  set e2 : Fin (i0 + s') → Fin (2 * r + k + 1) :=
    fun l => sR k r (i0 + s' + 1) hm' ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l) with he2def
  have he2v : ∀ l, (e2 l).val = 2 * r + k - ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l).val := by
    intro l; simp [e2, sR, esI]
  have he2k : ∀ l, keyS k r (e2 l) = ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l).val := by
    intro l; simp only [e2]; rw [keyS_sR]
  have he2 : StrictMono (fun l => keyS k r (e2 l)) := by
    intro a b hab
    simp only [he2k]; exact Fin.strictMono_succAbove _ hab
  have hAA : AAv k r E y (i0 + s') hm ell =
      star (h.det * t ^ s' * sgnW s') • qminor E e2 (sR k r (i0 + s') hm) (ell + ((i0 + s' : ℕ) : ℂ) - 1) := by
    unfold AAv
    rw [sum_single (fun B => StrictMono (fun l => keyS k r (B l))) (fun a p => y (Fin.castLE hm a) p)
      (Set.range e2) ?_ e2 he2 ?_]
    · congr 1
      have hp := minors_first_case i0 s' h t ⟨i0, by omega⟩
      rw [if_pos rfl] at hp
      rw [← hp, ← det_star]
      congr 1
      ext a l
      simp only [Matrix.of_apply]
      have hl := ((⟨i0, by omega⟩ : Fin (i0 + s' + 1)).succAbove l).isLt
      rw [hy _ _ (by simp; omega), if_pos (by rw [he2v]; omega), he2v]
      congr 2 <;> (try simp) <;> omega
    · intro a p hp
      rw [hy _ _ (by simp; omega)]
      split_ifs with h1
      · by_cases hpi : 2 * r + k - p.val = i0
        · rw [hpi, zb_col_zero i0 s' h t _ (by simp), star_zero]
        · exfalso; apply hp
          refine ⟨⟨if 2 * r + k - p.val < i0 then 2 * r + k - p.val else 2 * r + k - p.val - 1,
            by split_ifs <;> omega⟩, ?_⟩
          ext; rw [he2v, succAbove_val]; simp only; split_ifs <;> omega
      · rfl
    · intro c hc hS; exact uniq_key (keyS k r) (keyS_inj k r) _ _ he2 hc hS
  have hhead : AAv k r E y i0 (by omega) ell =
      star h.det • qminor E (sR k r i0 (by omega)) (sR k r i0 (by omega)) (ell + (i0 : ℂ) - 1) := by
    apply AAv_head
    · intro a p ha hp
      rw [hy _ _ (by omega)]
      split_ifs with hc
      · have hx : ¬ (2 * r + k - p.val < i0) := by
          intro hlt; apply hp
          exact ⟨⟨2 * r + k - p.val, hlt⟩, by ext; simp [sR, esI]; omega⟩
        unfold Zb; rw [dif_pos ha, dif_neg hx, star_zero]
      · rfl
    · intro a b
      have hb := b.isLt
      rw [hy _ _ (by simp; omega)]
      rw [if_pos (by simp [sR, esI]; omega)]
      have hsv : (sR k r i0 (by omega) b).val = 2 * r + k - b.val := by simp [sR, esI]
      have hav : (Fin.castLE (by omega : i0 ≤ r) a).val = a.val := by simp
      unfold Zb
      rw [hav, hsv]
      rw [dif_pos a.isLt, dif_pos (by omega)]
      congr 2
      apply Fin.ext; simp only [Fin.val_mk]; omega
  have hP := third_peeling_identity A k r z' E hG (i0 + s') hm' ⟨i0, by omega⟩ ell
  have hLa : La (qminor E e2 (sR k r (i0 + s') hm) (ell + ((i0 + s' : ℕ) : ℂ) - 1)) =
      La (qminor E (sR k r i0 (by omega)) (sR k r i0 (by omega)) (ell + (i0 : ℂ) - 1)) := la_congr hR hP
  rw [hAA, hhead, map_smul, map_smul, hLa, (derivative_leading_zb i0 (s' + 1) h t).1, (derivative_leading_zb i0 (s' + 1) h t).2,
    smul_smul, smul_smul, smul_smul]
  congr 1
  simp only [star_mul', star_pow, star_sgnW, sgnW_succ, Nat.add_sub_cancel, star_neg, star_one]
  rw [scal_E (star h.det) (star t) (sgnW s') ((-1) ^ s') s' (star_ne_zero.mpr hh) (star_ne_zero.mpr ht)
    (sgnW_sq s') (neg_one_sq' s')]
  ring

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem det_row_sum {n : ℕ} {ι : Type} (s : Finset ι) (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (c : ι → ℂ)
    (v : ι → Fin n → ℂ) :
    (M.updateRow i (∑ w ∈ s, c w • v w)).det = ∑ w ∈ s, c w * (M.updateRow i (v w)).det := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Matrix.det_eq_zero_of_row_eq_zero i (fun j => by simp [Matrix.updateRow_self])
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.det_updateRow_add,
      Matrix.det_updateRow_smul, ih]

theorem det_row_lin {n : ℕ} {ι : Type} [Fintype ι] (X : Fin n → Fin n → ℂ) (i : Fin n) (η : ι → ℂ)
    (v : ι → Fin n → ℂ) (hrow : ∀ l, X i l = ∑ w, η w * v w l) :
    (Matrix.of X).det = ∑ w, η w * (Matrix.of fun a l => if a = i then v w l else X a l).det := by
  have h1 : Matrix.of X = (Matrix.of X).updateRow i (∑ w, η w • v w) := by
    ext a l
    by_cases h : a = i
    · subst h
      simp [Matrix.updateRow_self, hrow, Finset.sum_apply]
    · simp [Matrix.updateRow_ne h]
  have h2 : ∀ w, (Matrix.of fun a l => if a = i then v w l else X a l) =
      (Matrix.of X).updateRow i (v w) := by
    intro w
    ext a l
    by_cases h : a = i
    · subst h
      simp
    · simp [h, Matrix.updateRow_ne h]
  calc (Matrix.of X).det = ((Matrix.of X).updateRow i (∑ w ∈ Finset.univ, η w • v w)).det :=
        congrArg Matrix.det h1
    _ = ∑ w ∈ Finset.univ, η w * ((Matrix.of X).updateRow i (v w)).det := det_row_sum _ _ _ _ _
    _ = ∑ w, η w * (Matrix.of fun a l => if a = i then v w l else X a l).det :=
        Finset.sum_congr rfl (fun w _ => by rw [h2 w])

theorem sum_lin {M : Type*} [AddCommGroup M] [Module ℂ M] {m N : ℕ} {ι : Type} [Fintype ι]
    (P : (Fin m → Fin N) → Prop) [DecidablePred P] (X : Fin m → Fin N → ℂ) (i : Fin m) (η : ι → ℂ)
    (v : ι → Fin N → ℂ) (hrow : ∀ p, X i p = ∑ w, η w * v w p) (F : (Fin m → Fin N) → M) :
    (∑ c : Fin m → Fin N, if P c then (Matrix.of fun a l => X a (c l)).det • F c else 0) =
      ∑ w, η w • ∑ c : Fin m → Fin N,
        if P c then (Matrix.of fun a l => (if a = i then v w (c l) else X a (c l))).det • F c else 0 := by
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  split_ifs with hP
  · rw [det_row_lin (fun a l => X a (c l)) i η (fun w l => v w (c l)) (fun l => hrow (c l)),
      Finset.sum_smul]
    exact Finset.sum_congr rfl (fun w _ => mul_smul _ _ _)
  · simp

theorem strictMono_snoc {α : Type} [Preorder α] {m : ℕ} (f : Fin m → α) (hf : StrictMono f) (x : α)
    (hx : ∀ l, f l < x) : StrictMono (Fin.snoc (α := fun _ => α) f x : Fin (m + 1) → α) := by
  intro a b hab
  induction b using Fin.lastCases with
  | last =>
    induction a using Fin.lastCases with
    | last => exact absurd hab (lt_irrefl _)
    | cast a =>
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact hx a
  | cast b =>
    induction a using Fin.lastCases with
    | last => exact absurd hab (not_lt.2 (Fin.castSucc_lt_last b).le)
    | cast a =>
      simp only [Fin.snoc_castSucc]
      exact hf (Fin.castSucc_lt_castSucc_iff.1 hab)

theorem hpk_zero_alt (k r : ℕ) (p q : Fin (2 * r + k + 1)) (hq : r ≤ q.val ∧ q.val ≤ r + k)
    (hp : ¬ (r ≤ p.val ∧ p.val ≤ r + k)) : Hpk k r q p = 0 := by
  unfold Hpk
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem herm_bvec_sum (k r : ℕ) (yb : Fin (2 * r + k + 1) → ℂ) (hyb : inWb k r yb) (p : Fin (2 * r + k + 1)) :
    herm (Hpk k r) (bvec p) yb =
      ∑ w : Fin (k + 1), herm (Hpk k r) (bvec (wI k r w)) yb * (if p = wI k r w then 1 else 0) := by
  unfold inWb at hyb
  unfold herm bvec wI
  by_cases hp : r ≤ (p : ℕ) ∧ (p : ℕ) ≤ r + k
  · rw [Finset.sum_eq_single (⟨(p : ℕ) - r, by omega⟩ : Fin (k + 1))]
    · split_ifs with h
      · rw [mul_one, ← h]
      · exact absurd (Fin.ext (by simp only [Fin.val_mk]; omega)) h
    · intro b _ hb
      split_ifs with h
      · exact absurd (Fin.ext (by simp only [Fin.ext_iff, Fin.val_mk] at h ⊢; omega)) hb
      · exact mul_zero _
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hL : star yb ⬝ᵥ Hpk k r *ᵥ Pi.single p 1 = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : r ≤ (i : ℕ) ∧ (i : ℕ) ≤ r + k
      · have h0 : (Hpk k r *ᵥ Pi.single p 1) i = 0 := by
          simp [Matrix.mulVec, hpk_zero_alt k r p i hi hp]
        rw [h0, mul_zero]
      · have h0 : yb i = 0 := hyb i (by omega)
        simp [h0]
    rw [hL]
    symm
    apply Finset.sum_eq_zero
    intro w _
    split_ifs with h
    · have hw := w.isLt
      rw [Fin.ext_iff] at h
      simp only [Fin.val_mk] at h
      exact absurd ⟨by omega, by omega⟩ hp
    · exact mul_zero _

theorem hpk_real (k r : ℕ) (p q : Fin (2 * r + k + 1)) : star (Hpk k r p q) = Hpk k r p q := by
  unfold Hpk
  split_ifs <;> simp

theorem hpk_symm (k r : ℕ) (p q : Fin (2 * r + k + 1)) : Hpk k r p q = Hpk k r q p := by
  unfold Hpk
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_star (k r : ℕ) (p q : Fin (2 * r + k + 1)) : star (Hpk k r p q) = Hpk k r q p := by
  rw [hpk_real, hpk_symm]

theorem herm_swap (k r : ℕ) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by
  unfold herm
  have hH : (Hpk k r)ᴴ = Hpk k r := by
    ext p q
    rw [conjTranspose_apply, hpk_star]
  rw [star_dotProduct v (Hpk k r *ᵥ w), star_star, star_mulVec, hH, dotProduct_mulVec]

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem sign_alternates_add_two (s : ℕ) : sgnW (s + 2) = - sgnW s := by
  unfold sgnW
  have e : (s + 2) * (s + 2 - 1) / 2 = s * (s - 1) / 2 + (2 * s + 1) := by
    have e2 : (s + 2) * (s + 2 - 1) = s * (s - 1) + 2 * (2 * s + 1) := by
      rw [show s + 2 - 1 = s + 1 by omega]
      cases s with
      | zero => rfl
      | succ k =>
        rw [show k + 1 - 1 = k by omega]
        ring
    rw [e2, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
  rw [e, pow_add, pow_succ, pow_mul]
  norm_num

theorem column_indicator_expansion : ExpansionCovector := by
  intro A _ _ M _ _ k r z' yb E La xi i0 s h t u hs hj hR hh ht hz' hyb hzy hxa hxi0
  obtain ⟨s'', rfl⟩ : ∃ s'', s = s'' + 2 := ⟨s - 2, by omega⟩
  obtain rfl : r = i0 + s'' + 1 := by omega
  set i : Fin (i0 + s'' + 1) := ⟨i0, by omega⟩ with hidef
  set f : Fin (i0 + s'') → Fin (2 * (i0 + s'' + 1) + k + 1) :=
    fun l => xR k (i0 + s'' + 1) (i0 + s'' + 1) le_rfl (i.succAbove l) with hfdef
  have hfv : ∀ l, (f l).val = (i.succAbove l).val := by intro l; simp [f, xR, eI]
  have hf : StrictMono f := by
    intro a b hab; show (f a).val < (f b).val; rw [hfv, hfv]; exact Fin.strictMono_succAbove _ hab
  set ew : Fin (k + 1) → Fin (i0 + s'' + 1) → Fin (2 * (i0 + s'' + 1) + k + 1) :=
    fun w => Fin.snoc (α := fun _ => Fin (2 * (i0 + s'' + 1) + k + 1)) f (wI k (i0 + s'' + 1) w) with hewdef
  have hew : ∀ w, StrictMono (ew w) := by
    intro w
    apply strictMono_snoc f hf
    intro l; show (f l).val < (wI k _ w).val; rw [hfv]; simp [wI]; have := (i.succAbove l).isLt; omega
  have hew_last : ∀ w (j : Fin (i0 + s'' + 1)), ew w j = wI k _ w ↔ j = Fin.last _ := by
    intro w j
    constructor
    · intro hj
      by_contra hne
      obtain ⟨l, rfl⟩ := Fin.exists_castSucc_eq.mpr hne
      have := congrArg Fin.val hj
      simp only [ew, Fin.snoc_castSucc] at this
      rw [hfv] at this; simp [wI] at this; have := (i.succAbove l).isLt; omega
    · rintro rfl; simp [ew]

  have hdet : ∀ w, (Matrix.of fun a l => if a = i then (if ew w l = wI k _ w then (1 : ℂ) else 0)
      else xi (Fin.castLE le_rfl a) (ew w l)).det = (-1) ^ s'' * (h.det * t ^ s'' * sgnW s'') := by
    intro w
    rw [Matrix.det_succ_row _ i, Finset.sum_eq_single (Fin.last _)]
    · simp only [Matrix.of_apply, if_pos rfl, (hew_last w (Fin.last _)).mpr rfl, if_true, mul_one,
        Fin.succAbove_last]
      have hsub : (Matrix.of fun a l => if a = i then (if ew w l = wI k _ w then (1 : ℂ) else 0)
          else xi (Fin.castLE le_rfl a) (ew w l)).submatrix i.succAbove Fin.castSucc =
          Matrix.of fun a b : Fin (i0 + s'') => Zb i0 (s'' + 2) h t ((⟨i0, by omega⟩ : Fin (i0 + s'' + 1)).succAbove a).val
            ((⟨i0, by omega⟩ : Fin (i0 + s'' + 1)).succAbove b).val := by
        ext a b
        simp only [Matrix.submatrix_apply, Matrix.of_apply]
        rw [if_neg (Fin.succAbove_ne i a)]
        simp only [ew, Fin.snoc_castSucc]
        have hb := (i.succAbove b).isLt
        have hbne : (i.succAbove b).val ≠ i0 := fun h' => Fin.succAbove_ne i b (Fin.ext h')
        have hane : (i.succAbove a).val ≠ i0 := fun h' => Fin.succAbove_ne i a (Fin.ext h')
        rw [hxa _ _ (by simpa using hane), if_pos ⟨by rw [hfv]; omega, by rw [hfv]; exact hbne⟩, hfv]
        simp [i]
      rw [hsub, third_polynomial_expansion]
      simp only [Fin.val_last]
      rw [show i.val + (i0 + s'') = (i0 + i0) + s'' by simp [i]; ring, pow_add, ← two_mul, pow_mul]
      norm_num
    · intro j _ hj
      simp only [Matrix.of_apply, if_pos rfl]
      rw [if_neg (fun h' => hj ((hew_last w j).mp h'))]; simp
    · simp
  have hAA : AAx k (i0 + s'' + 1) E xi (i0 + s'' + 1) le_rfl u =
      ((-1) ^ s'' * (h.det * t ^ s'' * sgnW s'')) • ∑ w, herm (Hpk k _) (bvec (wI k _ w)) yb •
        qminor E (xR k _ (i0 + s'' + 1) le_rfl) (ew w) u := by
    unfold AAx
    rw [sum_lin (fun c => StrictMono c) (fun a p => xi (Fin.castLE le_rfl a) p) i
      (fun w => herm (Hpk k _) (bvec (wI k _ w)) yb) (fun w p => if p = wI k _ w then 1 else 0)
      (fun p => by rw [hxi0 _ _ (by simp [i])]; exact herm_bvec_sum k _ yb hyb p)]
    rw [Finset.smul_sum]
    congr 1; ext w
    rw [sum_single (fun c => StrictMono c) (fun a p => if a = i then (if p = wI k _ w then (1 : ℂ) else 0)
      else xi (Fin.castLE le_rfl a) p) (Set.range (ew w)) ?_ (ew w) (hew w) ?_, hdet w, smul_comm]
    · intro a p hp
      by_cases ha : a = i
      · rw [if_pos ha, if_neg]; intro hpw; apply hp; exact ⟨Fin.last _, by rw [hpw]; simp [ew]⟩
      · rw [if_neg ha]
        have hane : a.val ≠ i0 := fun h' => ha (Fin.ext h')
        rw [hxa _ _ (by simpa using hane)]
        rw [if_neg]
        rintro ⟨hp1, hp2⟩
        apply hp
        refine ⟨Fin.castSucc ⟨if p.val < i0 then p.val else p.val - 1, by split_ifs <;> omega⟩, ?_⟩
        ext; simp only [ew, Fin.snoc_castSucc]; rw [hfv, succAbove_val]; simp only [i]; split_ifs <;> omega
    · intro c hc hS; exact uniq_mono _ _ (hew w) hc hS
  have hhead : AAx k (i0 + s'' + 1) E xi i0 (by omega) u =
      h.det • qminor E (xR k _ i0 (by omega)) (xR k _ i0 (by omega)) u := by
    apply AAx_head
    · intro a p ha hp
      rw [hxa _ _ (by omega)]
      split_ifs
      · unfold Zb; rw [dif_pos ha, dif_neg (by omega)]
      · rfl
    · intro a b
      have hb := b.isLt
      rw [hxa _ _ (by simp; omega), if_pos (by simp [xR, eI]; omega)]
      unfold Zb
      simp [xR, eI]
  have hP := second_peeling_identity A k (i0 + s'') z' yb E i u hz'
  have hLa : (∑ w, herm (Hpk k _) (bvec (wI k _ w)) yb • La (qminor E (xR k _ (i0 + s'' + 1) le_rfl) (ew w) u)) =
      t • La (qminor E (xR k _ i0 (by omega)) (xR k _ i0 (by omega)) u) := by
    have := la_congr hR hP
    rw [map_sum] at this
    simp only [map_smul] at this
    rw [hzy] at this
    exact this
  have hD : Dlead i0 (s'' + 2) h t (i0 + s'' + 1 + 1) = h.det * t ^ (s'' + 2) * -sgnW s'' := by
    rw [show i0 + s'' + 1 + 1 = i0 + (s'' + 2) by omega, (derivative_leading_zb i0 (s'' + 2) h t).2, sign_alternates_add_two]
  rw [hAA, hhead, map_smul, map_smul, map_sum]
  simp only [map_smul]
  rw [hLa, hD, (derivative_leading_zb i0 (s'' + 2) h t).1, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  rw [show s'' + 2 - 1 = s'' + 1 by omega]
  rcases mul_self_eq_one_iff.mp (sgnW_sq s'') with h1 | h1 <;> rw [h1] <;> field_simp <;> ring

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants




end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem la_intmul {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M] (La : A →ₗ[ℂ] M) (z : ℤ) (x : A) :
    La ((z : A) * x) = (z : ℂ) • La x := by
  have hz : ((z : A) * x) = (z : ℂ) • x := by
    rw [Algebra.smul_def, map_intCast]
  rw [hz, map_smul]

theorem chain_first_identity : LastColumnChain := by
  intro A _ _ M _ _ k r z' c E La hG hc hR hL m hm u
  set a := xR k r (m + 2) hm with hadef
  have hav : ∀ l, (a l).val = l.val := by intro l; simp [a, xR, eI]
  have hcs : a ∘ Fin.castSucc = xR k r (m + 1) (by omega) := by
    funext l; ext; simp [a, xR, eI]
  have hexp := Formalism.FourierDecayAlt.P.expansion_last_column A _ (m + 1) E a a u
  rw [hexp, map_sum, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]

  have hzero : ∀ l : Fin m, La ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.castSucc l) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ (Fin.castSucc (Fin.castSucc l)).succAbove) (a ∘ Fin.castSucc) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.castSucc l))) (a (Fin.last (m + 1))))) = 0 := by
    intro l
    rw [la_intmul]
    have hne : a (Fin.castSucc (Fin.castSucc l)) ≠ a (Fin.last (m + 1)) := by
      intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this; omega
    rw [tm_offdiag _ _ hne, hR _ _ _ (by simp only [InNp, hav]; simp; omega)]
    have : dpsiP k r z' (a (Fin.castSucc (Fin.castSucc l))) (a (Fin.last (m + 1))) = 0 := by
      unfold dpsiP; simp only [hav]; simp; split_ifs <;> first | rfl | omega
    rw [this, zero_smul, smul_zero]
  rw [Finset.sum_eq_zero (fun l _ => hzero l), zero_add]

  have hlast : La ((((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ (Fin.last (m + 1)).succAbove) (a ∘ Fin.castSucc) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.last (m + 1))) (a (Fin.last (m + 1))))) =
      La (qminor E (xR k r (m + 1) (by omega)) (xR k r (m + 1) (by omega)) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) := by
    rw [la_intmul, Fin.succAbove_last, hcs]
    have h1 : a (Fin.last (m + 1)) = eI k r ⟨m + 1, by omega⟩ := by ext; rw [hav]; simp [eI]
    rw [h1]
    have h2 : ((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ))) = 1 := by
      simp only [Fin.val_last]; rw [← two_mul, pow_mul]; norm_num
    rw [h2]; simp
  rw [hlast]

  set rowsP : Fin (m + 1) → Fin (2 * r + k + 1) := Fin.cons (eI k r ⟨m + 1, by omega⟩) (xR k r m (by omega)) with hrP
  have hrows : a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove = rowsP ∘ (finRotate (m + 1)) := by
    funext q
    ext
    simp only [Function.comp_apply]
    by_cases hq : q = Fin.last m
    · subst hq
      rw [finRotate_last]
      simp only [rowsP, Fin.cons_zero]
      rw [hav, succAbove_val]; simp [eI]
    · have hq' : q.val < m := by
        have := q.isLt; have : q.val ≠ m := fun h' => hq (Fin.ext (by simp [h'])); omega
      have hr1 : finRotate (m + 1) q = Fin.succ ⟨q.val, hq'⟩ := by
        ext; rw [coe_finRotate_of_ne_last hq]; simp
      rw [hr1]
      simp only [rowsP, Fin.cons_succ]
      rw [hav, succAbove_val]; simp [xR, eI]; omega
  have hQm : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) =
      (c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩) • La (qminor E (xR k r m (by omega)) (xR k r m (by omega)) u) := by
    rw [hrows, Formalism.REAL.quantumMinorRowSkew_holds A _ (m + 1) E rowsP _ (finRotate (m + 1)) u, la_intmul, sign_finRotate]
    rw [Formalism.FourierDecayAlt.P.expansion_first_line A _ m E hG rowsP _ u, map_sum]
    rw [Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add]
    · rw [la_intmul]
      have hr0 : rowsP 0 = eI k r ⟨m + 1, by omega⟩ := by simp [rowsP]
      have hrs : rowsP ∘ Fin.succ = xR k r m (by omega) := by funext q; simp [rowsP]
      rw [hr0, hrs, Fin.succAbove_last, hcs]
      have hne : eI k r ⟨m + 1, by omega⟩ ≠ xR k r (m + 1) (by omega) (Fin.last m) := by
        intro h'; have := congrArg Fin.val h'; simp [eI, xR] at this
      rw [tm_offdiag _ _ hne]
      have hx : xR k r (m + 1) (by omega) (Fin.last m) = eI k r ⟨m, by omega⟩ := by ext; simp [xR, eI]
      rw [hx, hL _ ⟨m + 1, by omega⟩ ⟨m, by omega⟩ (by simp), if_pos rfl]
      have hcs2 : xR k r (m + 1) (by omega) ∘ Fin.castSucc = xR k r m (by omega) := by funext q; ext; simp [xR, eI]
      rw [hcs2, smul_smul, smul_smul]
      congr 1
      simp only [Fin.val_last]
      push_cast
      rw [neg_one_sq', one_mul]
    · intro q _
      rw [la_intmul]
      have hr0 : rowsP 0 = eI k r ⟨m + 1, by omega⟩ := by simp [rowsP]
      rw [hr0, hcs]
      have hqv : (xR k r (m + 1) (by omega) (Fin.castSucc q)).val = q.val := by simp [xR, eI]
      have hne : eI k r ⟨m + 1, by omega⟩ ≠ xR k r (m + 1) (by omega) (Fin.castSucc q) := by
        intro h'; have := congrArg Fin.val h'; rw [hqv] at this; simp [eI] at this; omega
      rw [tm_offdiag _ _ hne]
      have hx : xR k r (m + 1) (by omega) (Fin.castSucc q) = eI k r ⟨q.val, by omega⟩ := by ext; simp [xR, eI]
      have hq := q.isLt
      rw [hx, hL _ ⟨m + 1, by omega⟩ ⟨q.val, by omega⟩ (by simp <;> omega), if_neg (by simp <;> omega), zero_smul, smul_zero]
  have hmT : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u *
      Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.last m))) (a (Fin.last (m + 1)))) =
      La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) := by
    have hne : a (Fin.castSucc (Fin.last m)) ≠ a (Fin.last (m + 1)) := by
      intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this
    rw [tm_offdiag _ _ hne, hR _ _ _ (by simp only [InNp, hav]; simp; omega)]
    have : dpsiP k r z' (a (Fin.castSucc (Fin.last m))) (a (Fin.last (m + 1))) = 1 := by
      unfold dpsiP; simp only [hav]; simp; split_ifs <;> first | rfl | omega
    rw [this, one_smul]
  rw [la_intmul, hmT, hQm]
  have h3 : ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.last m) : Fin (m + 2)) : ℕ))) : ℤ) : ℂ) = -1 := by
    simp only [Fin.val_castSucc, Fin.val_last]
    push_cast
    rw [show m + 1 + m = 2 * m + 1 by ring, pow_succ, pow_mul]; norm_num
  rw [h3, neg_one_smul]; abel

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end
