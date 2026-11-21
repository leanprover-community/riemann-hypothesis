import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InductiveHeisenbergInputs

section
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace BL

def sg (k r i : ℕ) : ℕ := if i < r ∨ r + k < i then 2 * r + k - i else i

theorem hpk_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = sg k r i.val then (if i.val = r + k then -1 else 1) else 0 := by
  unfold Hpk sg
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1]
    rcases h1 with h1 | h1
    · by_cases h2 : i.val + j.val = 2 * r + k
      · rw [if_pos ⟨h1, h2⟩, if_pos (by omega), if_neg (by omega)]
      · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 h.2), if_neg (by omega), if_neg (by omega)]
    · by_cases h2 : i.val + j.val = 2 * r + k
      · rw [if_neg (by omega), if_pos ⟨by omega, h2⟩, if_pos (by omega), if_neg (by omega)]
      · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 h.2), if_neg (by omega), if_neg (by omega)]
  · rw [if_neg h1]
    push Not at h1
    rw [if_neg (by omega), if_neg (by omega)]
    by_cases h2 : i = j
    · subst h2; rw [if_pos ⟨h1.1, h1.2, rfl⟩, if_pos rfl]
    · rw [if_neg (fun h => h2 h.2.2), if_neg (fun h => h2 (Fin.ext h.symm))]

theorem hpk_symm (k r : ℕ) (i j : Fin (2 * r + k + 1)) : Hpk k r j i = Hpk k r i j := by
  rw [hpk_apply, hpk_apply]; unfold sg
  split_ifs <;> first | rfl | omega

theorem hpk_conjT (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [conjTranspose_apply, hpk_symm, hpk_apply]
  split_ifs <;> simp

theorem sg_lt {k r i : ℕ} (h : i < 2 * r + k + 1) : sg k r i < 2 * r + k + 1 := by
  unfold sg; split_ifs <;> omega

theorem sg_sg {k r i : ℕ} (h : i < 2 * r + k + 1) : sg k r (sg k r i) = i := by
  unfold sg; split_ifs <;> omega

theorem sg_rk {k r i : ℕ} (h : i < 2 * r + k + 1) : sg k r i = r + k ↔ i = r + k := by
  unfold sg; split_ifs <;> omega

theorem hpk_apply' (k r i : ℕ) (hi : i < 2 * r + k + 1) (j : Fin (2 * r + k + 1)) :
    Hpk k r ⟨i, hi⟩ j = if j.val = sg k r i then (if i = r + k then -1 else 1) else 0 :=
  hpk_apply k r ⟨i, hi⟩ j

theorem hpk_mul (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨sg k r i.val, sg_lt i.2⟩ : Fin _)]
  · rw [hpk_apply k r i ⟨sg k r i.val, sg_lt i.2⟩, hpk_apply' k r _ (sg_lt i.2) j, sg_sg i.2, Matrix.one_apply,
      if_pos (show ((⟨sg k r i.val, sg_lt i.2⟩ : Fin (2 * r + k + 1)).val = sg k r i.val) from rfl)]
    have hs := sg_rk (k := k) (r := r) i.2
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, if_pos rfl]
      by_cases h : i.val = r + k
      · rw [if_pos h, if_pos (hs.2 h)]; norm_num
      · rw [if_neg h, if_neg (fun h' => h (hs.1 h'))]; norm_num
    · rw [if_neg hij, if_neg (fun h : j.val = i.val => hij (Fin.ext h.symm)), mul_zero]
  · intro b _ hb; rw [hpk_apply k r i b, if_neg (fun h => hb (Fin.ext h)), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem sum_mid {n N : ℕ} (h : N = n + 2) (f : Fin N → ℂ) (h0 : ∀ q : Fin N, q.val = 0 → f q = 0)
    (h1 : ∀ q : Fin N, q.val = n + 1 → f q = 0) : ∑ q, f q = ∑ q : Fin n, f ⟨q.val + 1, by omega⟩ := by
  subst h
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, h0 0 rfl, h1 (Fin.last n).succ (by simp)]
  simp only [zero_add, add_zero]; rfl

theorem mv_bvec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (q p : Fin n) : (M *ᵥ bvec q) p = M p q := by
  unfold bvec; simp [mulVec, dotProduct, Pi.single_apply]

theorem mat_ext_bvec {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (h : ∀ q, A *ᵥ bvec q = B *ᵥ bvec q) : A = B := by
  ext i j; have := congrFun (h j) i; rwa [mv_bvec, mv_bvec] at this

section Lev
variable {k r' : ℕ}

def sh (q : Fin (2 * r' + k + 1)) : Fin (2 * (1 + r') + k + 1) := ⟨q.val + 1, by have := q.2; omega⟩

theorem sh_val (q : Fin (2 * r' + k + 1)) : (sh q).val = q.val + 1 := rfl

theorem exists_sh (p : Fin (2 * (1 + r') + k + 1)) (hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) :
    ∃ q : Fin (2 * r' + k + 1), p = sh q :=
  ⟨⟨p.val - 1, by omega⟩, Fin.ext (by simp [sh]; omega)⟩

theorem sum_sh (f : Fin (2 * (1 + r') + k + 1) → ℂ) (h0 : ∀ q : Fin _, q.val = 0 → f q = 0)
    (h1 : ∀ q : Fin _, q.val = 2 * (1 + r') + k → f q = 0) : ∑ q, f q = ∑ q : Fin (2 * r' + k + 1), f (sh q) :=
  sum_mid (n := 2 * r' + k + 1) (by omega) f h0 (fun q hq => h1 q (by omega))

theorem lv_in (v : Fin (2 * r' + k + 1) → ℂ) (q : Fin (2 * r' + k + 1)) : liftVec k 1 r' v (sh q) = v q := by
  unfold liftVec; rw [dif_pos (show 1 ≤ (sh q).val ∧ (sh q).val < 2 * r' + k + 1 + 1 from ⟨by simp [sh], by have := q.2; simp [sh]; omega⟩)]
  congr 1

theorem lv_out (v : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (1 + r') + k + 1))
    (hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k) : liftVec k 1 r' v p = 0 := by
  unfold liftVec; rw [dif_neg (by omega)]

theorem io_in (g : Mat k r') (p q : Fin (2 * r' + k + 1)) : ιLev k 1 r' g (sh p) (sh q) = g p q := by
  unfold ιLev
  rw [dif_pos (show 1 ≤ (sh p).val ∧ (sh p).val < 2 * r' + k + 1 + 1 from ⟨by simp [sh], by have := p.2; simp [sh]; omega⟩),
    dif_pos (show 1 ≤ (sh q).val ∧ (sh q).val < 2 * r' + k + 1 + 1 from ⟨by simp [sh], by have := q.2; simp [sh]; omega⟩)]
  congr 1

theorem io_out (g : Mat k r') (p q : Fin (2 * (1 + r') + k + 1))
    (hq : q.val = 0 ∨ q.val = 2 * (1 + r') + k) : ιLev k 1 r' g p q = if p = q then 1 else 0 := by
  unfold ιLev
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · rw [dif_pos hp, dif_neg (by omega), if_neg (fun h => by subst h; omega)]
  · rw [dif_neg hp]

theorem io_out' (g : Mat k r') (p q : Fin (2 * (1 + r') + k + 1))
    (hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k) : ιLev k 1 r' g p q = if p = q then 1 else 0 := by
  unfold ιLev; rw [dif_neg (by omega)]

theorem io_lv (g : Mat k r') (v : Fin (2 * r' + k + 1) → ℂ) :
    ιLev k 1 r' g *ᵥ liftVec k 1 r' v = liftVec k 1 r' (g *ᵥ v) := by
  funext p
  simp only [mulVec, dotProduct]
  rw [sum_sh _ (fun q hq => by rw [lv_out v q (by omega), mul_zero]) (fun q hq => by rw [lv_out v q (by omega), mul_zero])]
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · obtain ⟨p', rfl⟩ := exists_sh p hp
    rw [lv_in]; simp only [mulVec, dotProduct]
    exact Finset.sum_congr rfl fun q _ => by rw [io_in, lv_in]
  · rw [lv_out _ p (by omega)]
    exact Finset.sum_eq_zero fun q _ => by
      rw [io_out' g p _ (by omega), if_neg (fun h => by rw [h, sh_val] at hp; omega), zero_mul]

theorem io_bvec_out (g : Mat k r') (q : Fin (2 * (1 + r') + k + 1)) (hq : q.val = 0 ∨ q.val = 2 * (1 + r') + k) :
    ιLev k 1 r' g *ᵥ bvec q = bvec q := by
  funext p; rw [mv_bvec, io_out g p q hq]; unfold bvec; simp only [Pi.single_apply]

theorem bvec_lv (q : Fin (2 * r' + k + 1)) : (bvec (sh q) : Fin (2 * (1 + r') + k + 1) → ℂ) = liftVec k 1 r' (bvec q) := by
  funext p
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · obtain ⟨p', rfl⟩ := exists_sh p hp
    rw [lv_in]; unfold bvec; simp only [Pi.single_apply, Fin.ext_iff, sh_val]; simp
  · rw [lv_out _ p (by omega)]; unfold bvec; rw [Pi.single_apply, if_neg (fun h => by rw [h, sh_val] at hp; omega)]

theorem io_bvec_sh (g : Mat k r') (q : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g *ᵥ bvec (sh q) = liftVec k 1 r' (g *ᵥ bvec q) := by
  rw [bvec_lv, io_lv]

theorem io_mul (g h : Mat k r') : ιLev k 1 r' (g * h) = ιLev k 1 r' g * ιLev k 1 r' h := by
  apply mat_ext_bvec; intro q
  rw [← Matrix.mulVec_mulVec]
  by_cases hq : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1
  · obtain ⟨q', rfl⟩ := exists_sh q hq
    rw [io_bvec_sh, io_bvec_sh, io_lv, Matrix.mulVec_mulVec]
  · rw [io_bvec_out _ _ (by omega), io_bvec_out _ _ (by omega), io_bvec_out _ _ (by omega)]

theorem io_one : ιLev k 1 r' (1 : Mat k r') = 1 := by
  apply mat_ext_bvec; intro q
  rw [Matrix.one_mulVec]
  by_cases hq : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1
  · obtain ⟨q', rfl⟩ := exists_sh q hq
    rw [io_bvec_sh, Matrix.one_mulVec, bvec_lv]
  · rw [io_bvec_out _ _ (by omega)]

theorem io_conjT (g : Mat k r') : ιLev k 1 r' gᴴ = (ιLev k 1 r' g)ᴴ := by
  ext p q
  rw [conjTranspose_apply]; unfold ιLev
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1 <;>
    by_cases hq : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1
  · rw [dif_pos hp, dif_pos hq, dif_pos hq, dif_pos hp, conjTranspose_apply]
  · rw [dif_pos hp, dif_neg hq, dif_neg hq, if_neg (fun h => by subst h; exact hq hp), star_zero]
  · rw [dif_neg hp, dif_pos hq, dif_neg hp, if_neg (fun h => by subst h; exact hp hq), star_zero]
  · rw [dif_neg hp, dif_neg hq]; by_cases h : p = q
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), star_zero]

end Lev

end BL

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace BL

section herm
variable {n : ℕ}

theorem dot_bvec (i : Fin n) (x : Fin n → ℂ) : star (bvec i) ⬝ᵥ x = x i := by
  unfold dotProduct
  rw [Finset.sum_eq_single i]
  · simp [bvec]
  · intro b _ hb; simp [bvec, hb]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem bvec_self (i : Fin n) : bvec i i = 1 := by simp [bvec]

theorem bvec_ne (i j : Fin n) (h : i.val ≠ j.val) : bvec i j = 0 := by
  unfold bvec; rw [Pi.single_apply, if_neg (fun e => h (congrArg Fin.val e).symm)]

theorem herm_bb (H : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : herm H (bvec i) (bvec j) = H j i := by
  unfold herm; rw [dot_bvec, mv_bvec]

theorem herm_add_l (H : Matrix (Fin n) (Fin n) ℂ) (v v' w : Fin n → ℂ) :
    herm H (v + v') w = herm H v w + herm H v' w := by
  unfold herm; rw [mulVec_add, dotProduct_add]

theorem herm_smul_l (H : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (v w : Fin n → ℂ) : herm H (c • v) w = c * herm H v w := by
  unfold herm; rw [mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem herm_add_r (H : Matrix (Fin n) (Fin n) ℂ) (v w w' : Fin n → ℂ) :
    herm H v (w + w') = herm H v w + herm H v w' := by
  unfold herm; rw [star_add, add_dotProduct]

theorem herm_smul_r (H : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (v w : Fin n → ℂ) :
    herm H v (c • w) = star c * herm H v w := by
  unfold herm; rw [star_smul, smul_dotProduct, smul_eq_mul]

theorem herm_sum_l (H : Matrix (Fin n) (Fin n) ℂ) {ι : Type} (s : Finset ι) (f : ι → Fin n → ℂ) (w : Fin n → ℂ) :
    herm H (∑ i ∈ s, f i) w = ∑ i ∈ s, herm H (f i) w := by
  unfold herm; rw [Matrix.mulVec_sum, dotProduct_sum]

theorem herm_zero_l (H : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) : herm H 0 w = 0 := by
  unfold herm; rw [mulVec_zero, dotProduct_zero]

theorem herm_mul (H g : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm (gᴴ * H * g) v w := by
  unfold herm; rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

theorem herm_UH (H g : Matrix (Fin n) (Fin n) ℂ) (hg : g ∈ UH H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  rw [herm_mul, show gᴴ * H * g = H from hg]

end herm

theorem herm_hpk_r (k r : ℕ) (v w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) v (Hpk k r *ᵥ w) = star w ⬝ᵥ v := by
  unfold herm; rw [star_mulVec, ← dotProduct_mulVec, hpk_conjT, mulVec_mulVec, hpk_mul, one_mulVec]

theorem sq2_mul_sq2_eq_half : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = 1 / 2 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  try push_cast
  rw [← mul_inv, h2]; norm_num

theorem star_inv_sqrt_two : star ((Real.sqrt 2)⁻¹ : ℂ) = ((Real.sqrt 2)⁻¹ : ℂ) := by
  try push_cast
  rw [Complex.star_def, map_inv₀, Complex.conj_ofReal]

section phi
variable (k n : ℕ)

theorem hpk_ww (j j' : Fin (k + 1)) :
    Hpk k n (wI k n j) (wI k n j') = if j = j' then (if j.val = k then -1 else 1) else 0 := by
  rw [hpk_apply]
  have hj := j.2
  have e1 : (wI k n j).val = n + j.val := rfl
  have e2 : (wI k n j').val = n + j'.val := rfl
  have hs : sg k n (n + j.val) = n + j.val := by unfold sg; rw [if_neg (by omega)]
  rw [e1, e2, hs]
  by_cases h : j = j'
  · subst h; rw [if_pos rfl, if_pos rfl]
    by_cases h' : j.val = k
    · rw [if_pos (by omega : n + j.val = n + k), if_pos h']
    · rw [if_neg (by omega : ¬ n + j.val = n + k), if_neg h']
  · rw [if_neg h, if_neg (fun e => h (Fin.ext (by omega)))]

theorem phi_iso (hk : 1 ≤ k) (a b : Fin (n + 1)) : herm (Hpk k n) (phiV k n a) (phiV k n b) = 0 := by
  unfold phiV
  split_ifs with ha hb hb
  · rw [herm_bb, hpk_apply]; simp only [esI, Fin.val_mk]; unfold sg; split_ifs <;> first | omega | rfl
  · unfold epsV
    rw [herm_smul_r, herm_add_r, herm_bb, herm_bb, hpk_apply, hpk_apply]
    simp only [esI, wI, Fin.val_mk, Fin.val_zero, Fin.val_last]; unfold sg; split_ifs <;> first | omega | simp
  · unfold epsV
    rw [herm_smul_l, herm_add_l, herm_bb, herm_bb, hpk_apply, hpk_apply]
    simp only [esI, wI, Fin.val_mk, Fin.val_zero, Fin.val_last]; unfold sg; split_ifs <;> first | omega | simp
  · unfold epsV
    have h0l : (0 : Fin (k + 1)) ≠ Fin.last k := fun h => by have := congrArg Fin.val h; simp at this; omega
    rw [herm_smul_l, herm_smul_r, herm_add_l, herm_add_r, herm_add_r, herm_bb, herm_bb, herm_bb, herm_bb]
    have hk0 : (0 : ℕ) ≠ k := by omega
    simp [hpk_ww, h0l, h0l.symm, hk0]

theorem eps_dot (hk : 1 ≤ k) : star (epsV k n) ⬝ᵥ epsV k n = 1 := by
  unfold epsV
  have hne : (wI k n 0).val ≠ (wI k n (Fin.last k)).val := by simp only [wI, Fin.val_zero, Fin.val_last]; omega
  rw [star_smul, star_inv_sqrt_two, smul_dotProduct, dotProduct_smul, star_add, add_dotProduct, dot_bvec, dot_bvec]
  simp only [Pi.add_apply, bvec_self, bvec_ne _ _ hne, bvec_ne _ _ (Ne.symm hne), smul_eq_mul]
  linear_combination 2 * sq2_mul_sq2_eq_half

theorem phi_dot (hk : 1 ≤ k) (a b : Fin (n + 1)) :
    star (phiV k n b) ⬝ᵥ phiV k n a = if a = b then 1 else 0 := by
  have hv : a = b ↔ a.val = b.val := Fin.ext_iff
  unfold phiV
  split_ifs with ha hb hab hb hab hb hab hb hab
  · subst hab; rw [dot_bvec, bvec_self]
  · rw [dot_bvec, bvec_ne]; simp only [esI, Fin.val_mk]; omega
  · omega
  · unfold epsV
    rw [dot_bvec, Pi.smul_apply, Pi.add_apply, bvec_ne, bvec_ne, add_zero, smul_zero]
    · simp only [esI, wI, Fin.val_mk]; simp; omega
    · simp only [esI, wI, Fin.val_mk]; simp; omega
  · omega
  · unfold epsV
    rw [star_smul, smul_dotProduct, star_add, add_dotProduct, dot_bvec, dot_bvec, bvec_ne, bvec_ne, add_zero, smul_zero]
    · simp only [esI, wI, Fin.val_mk]; simp; omega
    · simp only [esI, wI, Fin.val_mk]; simp; omega
  · exact eps_dot k n hk
  · omega

theorem phi_pair (hk : 1 ≤ k) (a b : Fin (n + 1)) :
    herm (Hpk k n) (phiV k n a) (phiV' k n b) = if a = b then 1 else 0 := by
  unfold phiV'; rw [herm_hpk_r, phi_dot k n hk]

theorem mphi_li (hk : 1 ≤ k) (m : Mat k n) (hm : m ∈ UH (Hpk k n)) :
    LinearIndependent ℂ (fun a => m *ᵥ phiV k n a) := by
  rw [Fintype.linearIndependent_iff]; intro g hg b
  have h : herm (Hpk k n) (∑ a, g a • (m *ᵥ phiV k n a)) (m *ᵥ phiV' k n b) =
      herm (Hpk k n) 0 (m *ᵥ phiV' k n b) := by rw [hg]
  rw [herm_zero_l, herm_sum_l] at h
  simp only [herm_smul_l, herm_UH _ _ hm, phi_pair k n hk, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  exact h

theorem iw_apply (hIW : IW) (hk : 1 ≤ k) (m : Mat k n) (hm : m ∈ UH (Hpk k n)) :
    ∃ κ : Mat k n, κ ∈ GV k n ∧ κᴴ * κ = 1 ∧ ∃ τ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, τ.BlockTriangular id ∧
      (∀ a, m *ᵥ phiV k n a = ∑ b, τ b a • (κ *ᵥ phiV k n b)) ∧
      ∀ l, ∏ j ∈ Finset.Iic l, ‖τ j j‖ ^ 2 = Ga k n l (fun a => m *ᵥ phiV k n a) := by
  obtain ⟨κ0, hκ0, τ, hτ, hrep, hprod⟩ := hIW k n (fun a => m *ᵥ phiV k n a) hk (mphi_li k n hk m hm)
    (fun a b => by
      show herm (Hpk k n) (m *ᵥ phiV k n a) (m *ᵥ phiV k n b) = 0
      rw [herm_UH _ _ hm, phi_iso k n hk])
  have hG : κ0ᴴ * Hpk k n * κ0 = Hpk k n := hκ0.1
  have hU : κ0ᴴ * κ0 = 1 := hκ0.2
  refine ⟨κ0 * Hpk k n, ?_, ?_, τ, hτ, fun a => ?_, hprod⟩
  · show (κ0 * Hpk k n)ᴴ * Hpk k n * (κ0 * Hpk k n) = Hpk k n
    rw [conjTranspose_mul, hpk_conjT]
    calc Hpk k n * κ0ᴴ * Hpk k n * (κ0 * Hpk k n) = Hpk k n * (κ0ᴴ * Hpk k n * κ0) * Hpk k n := by
          simp only [Matrix.mul_assoc]
      _ = Hpk k n := by rw [hG, hpk_mul, Matrix.one_mul]
  · rw [conjTranspose_mul, hpk_conjT]
    calc Hpk k n * κ0ᴴ * (κ0 * Hpk k n) = Hpk k n * (κ0ᴴ * κ0) * Hpk k n := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, Matrix.mul_one, hpk_mul]
  · rw [show m *ᵥ phiV k n a = ∑ b, τ b a • (κ0 *ᵥ phiV' k n b) from hrep a]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold phiV'; rw [Matrix.mulVec_mulVec]

end phi

section gram

theorem sum_castLE {M : Type} [AddCommMonoid M] {n l : ℕ} (h : l + 1 ≤ n) (f : Fin n → M)
    (hf : ∀ b : Fin n, l < b.val → f b = 0) : ∑ b, f b = ∑ b : Fin (l + 1), f (Fin.castLE h b) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (Fin.castLE h)))]
  · rw [Finset.sum_image (fun a _ b _ e => Fin.castLE_injective h e)]
  · intro b _ hb; apply hf; by_contra hc; push Not at hc
    exact hb (Finset.mem_image.2 ⟨⟨b.val, by omega⟩, Finset.mem_univ _, Fin.ext (by simp)⟩)

theorem prod_Iic {M : Type} [CommMonoid M] {n : ℕ} (l : Fin (n + 1)) (f : Fin (n + 1) → M) :
    ∏ j ∈ Finset.Iic l, f j = ∏ j : Fin (l.val + 1), f (Fin.castLE (by omega) j) := by
  apply Finset.prod_nbij' (fun a => (⟨min a.val l.val, by omega⟩ : Fin (l.val + 1))) (Fin.castLE (by omega))
  · intro a _; exact Finset.mem_univ _
  · intro a _; rw [Finset.mem_Iic, Fin.le_def]; simp; omega
  · intro a ha; rw [Finset.mem_Iic, Fin.le_def] at ha; ext; simp; omega
  · intro a _; ext; simp; omega
  · intro a ha; rw [Finset.mem_Iic, Fin.le_def] at ha; congr 1; ext; simp; omega

theorem gram_mat' {N L : ℕ} (X : Fin L → Fin N → ℂ) (Xm : Matrix (Fin N) (Fin L) ℂ) (hX : ∀ p a, Xm p a = X a p) :
    (Matrix.of fun a b => star (X a) ⬝ᵥ X b) = Xmᴴ * Xm := by
  ext a b; simp [Matrix.mul_apply, dotProduct, conjTranspose_apply, hX]

theorem det_gram_tri {N L : ℕ} (Z : Fin L → Fin N → ℂ) (T : Matrix (Fin L) (Fin L) ℂ) (hT : T.BlockTriangular id) :
    (Matrix.of fun a b => star (∑ j, T j a • Z j) ⬝ᵥ ∑ j, T j b • Z j).det =
      (star (∏ j, T j j) * ∏ j, T j j) * (Matrix.of fun a b => star (Z a) ⬝ᵥ Z b).det := by
  rw [gram_mat' (fun a => ∑ j, T j a • Z j) ((Matrix.of fun p a => Z a p) * T) (fun p a => by
        simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _),
    gram_mat' Z (Matrix.of fun p a => Z a p) (fun p a => rfl), conjTranspose_mul]
  rw [show Tᴴ * (Matrix.of fun p a => Z a p)ᴴ * ((Matrix.of fun p a => Z a p) * T) =
      Tᴴ * ((Matrix.of fun p a => Z a p)ᴴ * (Matrix.of fun p a => Z a p)) * T by simp only [Matrix.mul_assoc]]
  rw [det_mul, det_mul, det_conjTranspose, det_of_upperTriangular hT]; ring

theorem ga_tri (k r : ℕ) (Z : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hτ : τ.BlockTriangular id) (l : Fin (r + 1)) :
    Ga k r l (fun a => ∑ b, τ b a • Z b) = (∏ j ∈ Finset.Iic l, ‖τ j j‖ ^ 2) * Ga k r l Z := by
  have h : l.val + 1 ≤ r + 1 := by omega
  have hs : ∀ a : Fin (l.val + 1), (∑ b, τ b (Fin.castLE h a) • Z b) =
      ∑ j : Fin (l.val + 1), τ (Fin.castLE h j) (Fin.castLE h a) • Z (Fin.castLE h j) := by
    intro a; apply sum_castLE h; intro b hb
    rw [hτ (show id (Fin.castLE h a) < id b by simp only [id, Fin.lt_def, Fin.val_castLE]; omega), zero_smul]
  have hT : (τ.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id := by
    intro i j hij; simp only [submatrix_apply]; apply hτ
    simp only [id, Fin.lt_def, Fin.val_castLE] at hij ⊢; exact hij
  unfold Ga
  simp only [hs]
  have key := det_gram_tri (fun j => Z (Fin.castLE h j)) (τ.submatrix (Fin.castLE h) (Fin.castLE h)) hT
  simp only [submatrix_apply] at key
  rw [key, prod_Iic l, show star (∏ j, τ (Fin.castLE h j) (Fin.castLE h j)) * ∏ j, τ (Fin.castLE h j) (Fin.castLE h j) =
      ((Complex.normSq (∏ j, τ (Fin.castLE h j) (Fin.castLE h j)) : ℝ) : ℂ) from (Complex.normSq_eq_conj_mul_self).symm,
    Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq, norm_prod, ← Finset.prod_pow]

theorem ga_unit (k r : ℕ) (U : Mat k r) (hU : Uᴴ * U = 1) (l : Fin (r + 1)) (Z : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    Ga k r l (fun a => U *ᵥ Z a) = Ga k r l Z := by
  unfold Ga; simp only [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hU, one_mulVec]

end gram

end BL

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace BL

theorem Iic_zero (n : ℕ) : Finset.Iic (0 : Fin (n + 1)) = {0} := by
  ext a
  simp [Fin.le_zero_iff]

section Lv
variable {k r' : ℕ}

def su (a : Fin (r' + 1)) : Fin (1 + r' + 1) := ⟨a.val + 1, by omega⟩

theorem su_val (a : Fin (r' + 1)) : (su a).val = a.val + 1 := rfl

theorem exists_su (a : Fin (1 + r' + 1)) (ha : a.val ≠ 0) : ∃ b : Fin (r' + 1), a = su b := by
  refine ⟨⟨a.val - 1, by have := a.2; omega⟩, Fin.ext ?_⟩
  show a.val = (a.val - 1) + 1
  omega

theorem prod_su {M : Type} [CommMonoid M] (f : Fin (1 + r' + 1) → M) :
    ∏ l, f l = f 0 * ∏ a : Fin (r' + 1), f (su a) := by
  rw [Fin.prod_univ_succ]
  congr 1
  exact (Fintype.prod_equiv (finCongr (by omega : r' + 1 = 1 + r')) (fun a => f (su a))
    (fun b => f b.succ) fun a => congrArg f (Fin.ext (by simp [su]))).symm

theorem sum_su {M : Type} [AddCommMonoid M] (f : Fin (1 + r' + 1) → M) :
    ∑ l, f l = f 0 + ∑ a : Fin (r' + 1), f (su a) := by
  rw [Fin.sum_univ_succ]
  congr 1
  exact (Fintype.sum_equiv (finCongr (by omega : r' + 1 = 1 + r')) (fun a => f (su a))
    (fun b => f b.succ) fun a => congrArg f (Fin.ext (by simp [su]))).symm

theorem lv_add (v w : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' (v + w) = liftVec k 1 r' v + liftVec k 1 r' w := by
  ext p
  simp only [liftVec, Pi.add_apply]
  split_ifs <;> simp

theorem lv_smul (c : ℂ) (v : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' (c • v) = c • liftVec k 1 r' v := by
  ext p
  simp only [liftVec, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem lv_sum {ι : Type} (s : Finset ι) (f : ι → Fin (2 * r' + k + 1) → ℂ) :
    liftVec k 1 r' (∑ i ∈ s, f i) = ∑ i ∈ s, liftVec k 1 r' (f i) := by
  have e : liftVec k 1 r' (∑ i ∈ s, f i) =
      (AddMonoidHom.mk' (liftVec k 1 r') fun v w => lv_add v w) (∑ i ∈ s, f i) := rfl
  rw [e, map_sum]
  rfl

theorem phi_lift (a : Fin (r' + 1)) : liftVec k 1 r' (phiV k r' a) = phiV k (1 + r') (su a) := by
  unfold phiV
  by_cases h : a.val < r'
  · have h' : (su a).val < 1 + r' := by rw [su_val]; omega
    rw [dif_pos h, dif_pos h', ← bvec_lv]
    congr 1
    ext
    simp only [sh, esI, su_val, Fin.val_mk]
    omega
  · have h' : ¬ (su a).val < 1 + r' := by rw [su_val]; omega
    rw [dif_neg h, dif_neg h']
    unfold epsV
    have e0 : sh (wI k r' 0) = wI k (1 + r') 0 := by
      ext
      simp only [sh, wI, Fin.val_mk]
      omega
    have e1 : sh (wI k r' (Fin.last k)) = wI k (1 + r') (Fin.last k) := by
      ext
      simp only [sh, wI, Fin.val_mk]
      omega
    rw [lv_smul, lv_add, ← bvec_lv, ← bvec_lv, e0, e1]

theorem besselPhi_eq_reindexConj_rootCoords : phiV k (1 + r') 0 = bvec ⟨2 * (1 + r') + k, by omega⟩ := by
  unfold phiV
  rw [dif_pos (by simp only [Fin.val_zero]; omega)]
  congr 1

theorem levelEmbedding_fixes_firstVector (g : Mat k r') : ιLev k 1 r' g *ᵥ phiV k (1 + r') 0 = phiV k (1 + r') 0 := by
  rw [besselPhi_eq_reindexConj_rootCoords]
  exact io_bvec_out g _ (Or.inr rfl)

theorem io_phi_su (g : Mat k r') (a : Fin (r' + 1)) :
    ιLev k 1 r' g *ᵥ phiV k (1 + r') (su a) = liftVec k 1 r' (g *ᵥ phiV k r' a) := by
  rw [← phi_lift, io_lv]

def tt (τ : Matrix (Fin (r' + 1)) (Fin (r' + 1)) ℂ) : Matrix (Fin (1 + r' + 1)) (Fin (1 + r' + 1)) ℂ := fun i j =>
  if i.val = 0 then (if j.val = 0 then 1 else 0)
  else if hj : j.val = 0 then 0 else τ ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩

variable (τ : Matrix (Fin (r' + 1)) (Fin (r' + 1)) ℂ)

theorem tt_su (a b : Fin (r' + 1)) : tt τ (su b) (su a) = τ b a := by
  unfold tt
  rw [if_neg (by simp [su]), dif_neg (by simp [su])]
  congr 1 <;> ext <;> simp [su]

theorem tt_00 : tt τ 0 0 = 1 := by
  simp [tt]

theorem triangularCoeff_firstColumn_zero (b : Fin (1 + r' + 1)) (hb : b.val ≠ 0) : tt τ b 0 = 0 := by
  simp [tt, hb]

theorem tt_0su (a : Fin (r' + 1)) : tt τ 0 (su a) = 0 := by
  simp [tt, su]

theorem tt_tri (hτ : τ.BlockTriangular id) : (tt τ).BlockTriangular id := by
  intro i j hij
  simp only [id] at hij
  rw [Fin.lt_iff_val_lt_val] at hij
  unfold tt
  by_cases hi : i.val = 0
  · omega
  · rw [if_neg hi]
    by_cases hj : j.val = 0
    · rw [dif_pos hj]
    · rw [dif_neg hj]
      apply hτ
      simp only [id, Fin.mk_lt_mk]
      omega

theorem tt_rep (m κ : Mat k r') (hrep : ∀ a, m *ᵥ phiV k r' a = ∑ b, τ b a • (κ *ᵥ phiV k r' b))
    (a : Fin (1 + r' + 1)) :
    ιLev k 1 r' m *ᵥ phiV k (1 + r') a = ∑ b, tt τ b a • (ιLev k 1 r' κ *ᵥ phiV k (1 + r') b) := by
  by_cases ha : a.val = 0
  · have ha0 : a = 0 := Fin.ext ha
    subst ha0
    rw [levelEmbedding_fixes_firstVector, sum_su, tt_00, levelEmbedding_fixes_firstVector, one_smul]
    rw [Finset.sum_eq_zero fun b _ => by rw [triangularCoeff_firstColumn_zero τ (su b) (by simp [su]), zero_smul], add_zero]
  · obtain ⟨a', rfl⟩ := exists_su a ha
    rw [io_phi_su, hrep a', lv_sum, sum_su, tt_0su, zero_smul, zero_add]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [tt_su, io_phi_su, lv_smul]

def suE : Fin (r' + 1) ↪ Fin (1 + r' + 1) :=
  ⟨su, fun a b h => Fin.ext (by have := congrArg Fin.val h; simp only [su_val] at this; omega)⟩

theorem Iic_su (a : Fin (r' + 1)) : Finset.Iic (su a) = insert 0 ((Finset.Iic a).map suE) := by
  ext l
  simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_map]
  constructor
  · intro hl
    by_cases h0 : l.val = 0
    · exact Or.inl (Fin.ext h0)
    · obtain ⟨b, rfl⟩ := exists_su l h0
      refine Or.inr ⟨b, ?_, rfl⟩
      rw [Fin.le_iff_val_le_val] at hl ⊢
      rw [su_val, su_val] at hl
      omega
  · rintro (rfl | ⟨b, hb, rfl⟩)
    · exact Fin.zero_le _
    · show su b ≤ su a
      rw [Fin.le_iff_val_le_val] at hb ⊢
      rw [su_val, su_val]
      omega

theorem tt_prod0 : ∏ j ∈ Finset.Iic (0 : Fin (1 + r' + 1)), ‖tt τ j j‖ ^ 2 = 1 := by
  rw [Iic_zero, Finset.prod_singleton, tt_00]
  simp

theorem tt_prodS (a : Fin (r' + 1)) :
    ∏ j ∈ Finset.Iic (su a), ‖tt τ j j‖ ^ 2 = ∏ j ∈ Finset.Iic a, ‖τ j j‖ ^ 2 := by
  rw [Iic_su, Finset.prod_insert, Finset.prod_map, tt_00]
  · rw [norm_one, one_pow, one_mul]
    refine Finset.prod_congr rfl fun x _ => ?_
    show ‖tt τ (su x) (su x)‖ ^ 2 = _
    rw [tt_su]
  · simp only [Finset.mem_map, not_exists, not_and]
    intro b _ h
    have h' := congrArg Fin.val h
    change (su b).val = (0 : Fin (1 + r' + 1)).val at h'
    rw [su_val] at h'
    simp at h'

theorem ga_lev (x : Mat k (1 + r')) (m κ : Mat k r') (hτ : τ.BlockTriangular id)
    (hrep : ∀ a, m *ᵥ phiV k r' a = ∑ b, τ b a • (κ *ᵥ phiV k r' b)) (l : Fin (1 + r' + 1)) :
    Ga k (1 + r') l (fun a => (x * ιLev k 1 r' m) *ᵥ phiV k (1 + r') a) =
      (∏ j ∈ Finset.Iic l, ‖tt τ j j‖ ^ 2) * Ga k (1 + r') l (fun a => (x * ιLev k 1 r' κ) *ᵥ phiV k (1 + r') a) := by
  have e : (fun a => (x * ιLev k 1 r' m) *ᵥ phiV k (1 + r') a) =
      fun a => ∑ b, tt τ b a • ((x * ιLev k 1 r' κ) *ᵥ phiV k (1 + r') b) := by
    funext a
    rw [← Matrix.mulVec_mulVec, tt_rep τ m κ hrep a, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  rw [e, ga_tri k (1 + r') _ (tt τ) (tt_tri τ hτ) l]

theorem levelDeterminant_of_triangular_change (x : Mat k (1 + r')) (m κ : Mat k r') (hτ : τ.BlockTriangular id)
    (hrep : ∀ a, m *ᵥ phiV k r' a = ∑ b, τ b a • (κ *ᵥ phiV k r' b)) :
    Del k (1 + r') 0 (x * ιLev k 1 r' m) = Del k (1 + r') 0 (x * ιLev k 1 r' κ) := by
  unfold Del
  rw [ga_lev τ x m κ hτ hrep 0, tt_prod0, one_mul]

theorem del_levS (x : Mat k (1 + r')) (m κ : Mat k r') (hτ : τ.BlockTriangular id)
    (hrep : ∀ a, m *ᵥ phiV k r' a = ∑ b, τ b a • (κ *ᵥ phiV k r' b))
    (hprod : ∀ l, ∏ j ∈ Finset.Iic l, ‖τ j j‖ ^ 2 = Ga k r' l (fun a => m *ᵥ phiV k r' a)) (a : Fin (r' + 1)) :
    Del k (1 + r') (su a) (x * ιLev k 1 r' m) = Del k r' a m * Del k (1 + r') (su a) (x * ιLev k 1 r' κ) := by
  unfold Del
  rw [ga_lev τ x m κ hτ hrep (su a), tt_prodS, hprod a]
  have h0 : 0 ≤ Ga k r' a (fun b => m *ᵥ phiV k r' b) := by
    rw [← hprod a]
    exact Finset.prod_nonneg fun j _ => by positivity
  exact Real.sqrt_mul h0 _

theorem del_conj (hHC : HeisConjLev) (κ : Mat k r') (hκG : κ ∈ GV k r') (hκU : κᴴ * κ = 1) (X : HPar k r')
    (l : Fin (1 + r' + 1)) :
    Del k (1 + r') l (heis0 k r' X * ιLev k 1 r' κ) = Del k (1 + r') l (heis0 k r' (κᴴ *ᵥ X.1, X.2)) := by
  have hκU' : κ * κᴴ = 1 := by
    rw [← Matrix.inv_eq_left_inv hκU]
    exact Matrix.mul_nonsing_inv κ (Matrix.isUnit_det_of_left_inverse hκU)
  have hG' : κᴴ ∈ GV k r' := by
    have hκ : κᴴ * Hpk k r' * κ = Hpk k r' := hκG
    show κᴴᴴ * Hpk k r' * κᴴ = Hpk k r'
    rw [Matrix.conjTranspose_conjTranspose]
    calc κ * Hpk k r' * κᴴ = κ * (κᴴ * Hpk k r' * κ) * κᴴ := by rw [hκ]
      _ = (κ * κᴴ) * Hpk k r' * (κ * κᴴ) := by simp only [mul_assoc]
      _ = Hpk k r' := by rw [hκU', one_mul, mul_one]
  have hinv : (ιLev k 1 r' κᴴ)⁻¹ = ιLev k 1 r' κ :=
    Matrix.inv_eq_right_inv (by rw [← io_mul, hκU, io_one])
  have hconj := hHC k r' κᴴ hG' X
  rw [hinv] at hconj
  rw [← hconj]
  have hU : (ιLev k 1 r' κᴴ)ᴴ * ιLev k 1 r' κᴴ = 1 := by
    rw [← io_conjT, Matrix.conjTranspose_conjTranspose, ← io_mul, hκU', io_one]
  unfold Del
  rw [mul_assoc]
  have e : (fun a => (ιLev k 1 r' κᴴ * (heis0 k r' X * ιLev k 1 r' κ)) *ᵥ phiV k (1 + r') a) =
      fun a => ιLev k 1 r' κᴴ *ᵥ ((heis0 k r' X * ιLev k 1 r' κ) *ᵥ phiV k (1 + r') a) := by
    funext a
    rw [Matrix.mulVec_mulVec]
  rw [e, ga_unit k (1 + r') _ hU l]

theorem rep0 (m κ : Mat k r') (hτ : τ.BlockTriangular id)
    (hrep : ∀ a, m *ᵥ phiV k r' a = ∑ b, τ b a • (κ *ᵥ phiV k r' b)) :
    m *ᵥ phiV k r' 0 = τ 0 0 • (κ *ᵥ phiV k r' 0) := by
  rw [hrep 0, Finset.sum_eq_single 0]
  · intro b _ hb
    rw [hτ (show id (0 : Fin (r' + 1)) < id b from lt_of_le_of_ne (Fin.zero_le _) (Ne.symm hb)),
      zero_smul]
  · intro h
    exact absurd (Finset.mem_univ 0) h

theorem lev_data (hIW : IW) (hHC : HeisConjLev) (hk : 1 ≤ k) (m : Mat k r') (hm : m ∈ UH (Hpk k r')) :
    ∃ κ : Mat k r', κ ∈ GV k r' ∧ κᴴ * κ = 1 ∧ ∃ t : ℂ, m *ᵥ phiV k r' 0 = t • (κ *ᵥ phiV k r' 0) ∧
      ‖t‖ = Del k r' 0 m ∧ ∀ X : HPar k r',
        Del k (1 + r') 0 (heis0 k r' X * ιLev k 1 r' m) = Del k (1 + r') 0 (heis0 k r' (κᴴ *ᵥ X.1, X.2)) ∧
        ∀ a : Fin (r' + 1), Del k (1 + r') (su a) (heis0 k r' X * ιLev k 1 r' m) =
          Del k r' a m * Del k (1 + r') (su a) (heis0 k r' (κᴴ *ᵥ X.1, X.2)) := by
  obtain ⟨κ, hκG, hκU, τ, hτ, hrep, hprod⟩ := iw_apply (k := k) (n := r') hIW hk m hm
  refine ⟨κ, hκG, hκU, τ 0 0, rep0 τ m κ hτ hrep, ?_, fun X => ⟨?_, fun a => ?_⟩⟩
  · unfold Del
    rw [← hprod 0, Iic_zero, Finset.prod_singleton, Real.sqrt_sq (norm_nonneg _)]
  · rw [levelDeterminant_of_triangular_change τ _ m κ hτ hrep, del_conj hHC κ hκG hκU X 0]
  · rw [del_levS τ _ m κ hτ hrep hprod a, del_conj hHC κ hκG hκU X (su a)]

end Lv

end BL

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace BL

theorem ell_col (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) :
    ell k r z g = ∑ a : Fin r, (g *ᵥ fvec k r z ⟨a.val + 1, by omega⟩) (eI k r a) := by
  unfold ell
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : a.val + 1 < r
  · rw [dif_pos h]
    first
      | simp [fvec, h, bvec, Matrix.mulVec_single_one]
      | simp [fvec, h, bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  · rw [dif_neg h]
    simp [fvec, h]

section Lv2
variable {k r' : ℕ}

theorem hpk_sh (p q : Fin (2 * r' + k + 1)) : Hpk k (1 + r') (sh p) (sh q) = Hpk k r' p q := by
  simp only [Hpk, sh, Fin.ext_iff, Fin.val_mk]
  have e1 : (p.val + 1 < 1 + r' ∧ p.val + 1 + (q.val + 1) = 2 * (1 + r') + k) ↔
      (p.val < r' ∧ p.val + q.val = 2 * r' + k) := by
    constructor <;> intro h <;> omega
  have e2 : (q.val + 1 < 1 + r' ∧ p.val + 1 + (q.val + 1) = 2 * (1 + r') + k) ↔
      (q.val < r' ∧ p.val + q.val = 2 * r' + k) := by
    constructor <;> intro h <;> omega
  have e3 : (1 + r' ≤ p.val + 1 ∧ p.val + 1 ≤ 1 + r' + k ∧ p.val + 1 = q.val + 1) ↔
      (r' ≤ p.val ∧ p.val ≤ r' + k ∧ p.val = q.val) := by
    constructor <;> intro h <;> omega
  have e4 : (p.val + 1 = 1 + r' + k) ↔ (p.val = r' + k) := by
    constructor <;> intro h <;> omega
  simp only [e1, e2, e3, e4]

theorem hpk_out (p : Fin (2 * (1 + r') + k + 1)) (hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k)
    (q : Fin (2 * r' + k + 1)) : Hpk k (1 + r') p (sh q) = 0 := by
  have := p.isLt
  have := q.isLt
  simp only [Hpk, sh, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | omega

private lemma sum_eq_sum_sh_of_zero_at_edges (F : Fin (2 * (1 + r') + k + 1) → ℂ)
    (hF : ∀ p : Fin (2 * (1 + r') + k + 1), (p.val = 0 ∨ p.val = 2 * (1 + r') + k) → F p = 0) :
    ∑ p, F p = ∑ q : Fin (2 * r' + k + 1), F (sh q) := by
  have hinj : Function.Injective (fun q : Fin (2 * r' + k + 1) => (sh q : Fin (2 * (1 + r') + k + 1))) := by
    intro a b h
    simp only [sh, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  rw [show ∑ q : Fin (2 * r' + k + 1), F (sh q) =
      ∑ p ∈ Finset.univ.map ⟨fun q : Fin (2 * r' + k + 1) => (sh q : Fin (2 * (1 + r') + k + 1)), hinj⟩, F p
      from (Finset.sum_map Finset.univ
        ⟨fun q : Fin (2 * r' + k + 1) => (sh q : Fin (2 * (1 + r') + k + 1)), hinj⟩ F).symm]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro p _ hp
  apply hF
  by_contra hc
  apply hp
  have := p.isLt
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  refine ⟨⟨p.val - 1, by omega⟩, ?_⟩
  ext
  simp only [sh, Fin.val_mk]
  omega

private lemma liftVec_apply_sh (v : Fin (2 * r' + k + 1) → ℂ) (q : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' v (sh q) = v q := by
  have h1 : 1 ≤ (sh q : Fin (2 * (1 + r') + k + 1)).val ∧
      (sh q : Fin (2 * (1 + r') + k + 1)).val < 2 * r' + k + 1 + 1 := by
    have := q.isLt
    simp only [sh, Fin.val_mk]
    omega
  simp only [liftVec]
  rw [dif_pos h1]
  exact congrArg v (Fin.ext (by simp [sh]))

theorem hpk_lv (v : Fin (2 * r' + k + 1) → ℂ) :
    Hpk k (1 + r') *ᵥ liftVec k 1 r' v = liftVec k 1 r' (Hpk k r' *ᵥ v) := by
  funext p
  simp only [Matrix.mulVec, dotProduct]
  refine (sum_eq_sum_sh_of_zero_at_edges _ ?_).trans ?_
  · intro j hj
    have h0 : ¬(1 ≤ j.val ∧ j.val < 2 * r' + k + 1 + 1) := by omega
    simp only [liftVec, dif_neg h0, mul_zero]
  · simp only [liftVec_apply_sh]
    by_cases hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k
    · have h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := by omega
      simp only [hpk_out p hp, zero_mul, Finset.sum_const_zero, liftVec, dif_neg h0]
    · have hp' : p = sh ⟨p.val - 1, by have := p.isLt; omega⟩ := by
        ext
        simp only [sh, Fin.val_mk]
        omega
      rw [hp']
      simp only [hpk_sh, liftVec_apply_sh, Matrix.mulVec, dotProduct]

theorem herm_lv (v w : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (liftVec k 1 r' v) (liftVec k 1 r' w) = herm (Hpk k r') v w := by
  unfold herm
  rw [hpk_lv]
  simp only [dotProduct, Pi.star_apply]
  refine (sum_eq_sum_sh_of_zero_at_edges _ ?_).trans ?_
  · intro p hp
    have h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := by omega
    simp only [liftVec, dif_neg h0, mul_zero]
  · simp only [liftVec_apply_sh]

theorem hermitianForm_liftVec_firstVector (v : Fin (2 * r' + k + 1) → ℂ) : herm (Hpk k (1 + r')) (liftVec k 1 r' v) (e0 k r') = 0 := by
  unfold herm
  rw [hpk_lv]
  simp [e0, bvec, dotProduct, Pi.single_apply, liftVec, eI, a0]
  apply Finset.sum_eq_zero
  intro x _
  split_ifs with h1 h2 <;> first | rfl | (rw [h2] at h1; simp at h1)

theorem firstVector_apply_first (h : 0 < 1 + r') : e0 k r' (eI k (1 + r') ⟨0, h⟩) = 1 := by
  simp [e0, bvec, a0, eI]

theorem firstVector_apply_succ (b : ℕ) (h : b + 1 < 1 + r') : e0 k r' (eI k (1 + r') ⟨b + 1, h⟩) = 0 := by
  simp [e0, bvec, a0, eI, Pi.single_apply]

theorem eI_succ (b : ℕ) (h : b + 1 < 1 + r') : eI k (1 + r') ⟨b + 1, h⟩ = sh (eI k r' ⟨b, by omega⟩) := by
  ext
  simp [eI, sh]

private lemma lev_apply_sh_sh (m : Mat k r') (p q : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' m (sh p) (sh q) = m p q := by
  have hp : 1 ≤ (sh p : Fin (2 * (1 + r') + k + 1)).val ∧
      (sh p : Fin (2 * (1 + r') + k + 1)).val < 2 * r' + k + 1 + 1 := by
    have := p.isLt
    simp only [sh, Fin.val_mk]
    omega
  have hq : 1 ≤ (sh q : Fin (2 * (1 + r') + k + 1)).val ∧
      (sh q : Fin (2 * (1 + r') + k + 1)).val < 2 * r' + k + 1 + 1 := by
    have := q.isLt
    simp only [sh, Fin.val_mk]
    omega
  simp only [ιLev]
  rw [dif_pos hp, dif_pos hq]
  exact congrArg₂ m (Fin.ext (by simp [sh])) (Fin.ext (by simp [sh]))

private lemma lev_mulVec_liftVec_eq_liftVec_mulVec (m : Mat k r') (w : Fin (2 * r' + k + 1) → ℂ) :
    ιLev k 1 r' m *ᵥ liftVec k 1 r' w = liftVec k 1 r' (m *ᵥ w) := by
  funext p
  simp only [Matrix.mulVec, dotProduct]
  refine (sum_eq_sum_sh_of_zero_at_edges _ ?_).trans ?_
  · intro j hj
    have h0 : ¬(1 ≤ j.val ∧ j.val < 2 * r' + k + 1 + 1) := by omega
    simp only [liftVec, dif_neg h0, mul_zero]
  · simp only [liftVec_apply_sh]
    by_cases hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k
    · have h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := by omega
      have hz : ∀ q : Fin (2 * r' + k + 1), ιLev k 1 r' m p (sh q) = 0 := by
        intro q
        have hne : p ≠ sh q := by
          intro he
          rw [he] at hp
          have := q.isLt
          simp only [sh, Fin.val_mk] at hp
          omega
        simp only [ιLev, dif_neg h0, if_neg hne]
      simp only [hz, zero_mul, Finset.sum_const_zero, liftVec, dif_neg h0]
    · have hp' : p = sh ⟨p.val - 1, by have := p.isLt; omega⟩ := by
        ext
        simp only [sh, Fin.val_mk]
        omega
      rw [hp']
      simp only [lev_apply_sh_sh, liftVec_apply_sh, Matrix.mulVec, dotProduct]

theorem hcol (hHA : HeisAct) (m : Mat k r') (X : HPar k r') (w : Fin (2 * r' + k + 1) → ℂ) :
    (heis0 k r' X * ιLev k 1 r' m) *ᵥ liftVec k 1 r' w =
      liftVec k 1 r' (m *ᵥ w) - herm (Hpk k r') (m *ᵥ w) X.1 • e0 k r' := by
  unfold HeisAct at hHA
  rw [← Matrix.mulVec_mulVec, lev_mulVec_liftVec_eq_liftVec_mulVec]
  unfold heis0
  rw [hHA, herm_lv, hermitianForm_liftVec_firstVector, zero_smul, add_zero]

theorem sum_fin_one_add_eq_add_sum {M : Type} [AddCommMonoid M] (F : Fin (1 + r') → M) :
    ∑ a, F a = F ⟨0, by omega⟩ + ∑ a' : Fin r', F ⟨a'.val + 1, by omega⟩ := by
  rw [← Fintype.sum_equiv (finCongr (Nat.add_comm r' 1))
    (fun a : Fin (r' + 1) => F (finCongr (Nat.add_comm r' 1) a)) F (fun _ => rfl), Fin.sum_univ_succ]
  refine congrArg₂ (· + ·) ?_ ?_
  · exact congrArg F (Fin.ext (by simp))
  · exact Finset.sum_congr rfl fun a _ => congrArg F (Fin.ext (by simp))

private lemma liftVec_bvec_eq_bvec_sh (i : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' (bvec i) = bvec (sh i) := by
  funext p
  by_cases hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k
  · have h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := by omega
    have hne : p ≠ sh i := by
      intro he
      rw [he] at hp
      have := i.isLt
      simp only [sh, Fin.val_mk] at hp
      omega
    simp only [liftVec, dif_neg h0, bvec, Pi.single_apply, if_neg hne]
  · have hp' : p = sh ⟨p.val - 1, by have := p.isLt; omega⟩ := by
      ext
      simp only [sh, Fin.val_mk]
      omega
    rw [hp', liftVec_apply_sh]
    simp [bvec, Pi.single_apply, sh, Fin.ext_iff]

theorem fvec_lift (z1 : Fin (2 * r' + k + 1) → ℂ) (a : Fin (1 + r')) :
    fvec k (1 + r') (liftVec k 1 r' z1) ⟨a.val + 1, by omega⟩ = liftVec k 1 r' (fvec k r' z1 ⟨a.val, by omega⟩) := by
  by_cases ha : a.val < r'
  · have h1 : a.val + 1 < 1 + r' := by omega
    simp only [fvec, Fin.val_mk, dif_pos h1, dif_pos ha]
    rw [eI_succ a.val h1]
    exact (liftVec_bvec_eq_bvec_sh _).symm
  · have h1 : ¬ a.val + 1 < 1 + r' := by omega
    simp only [fvec, Fin.val_mk, dif_neg h1, dif_neg ha]

private lemma liftVec_apply_eI_zero_eq_zero (v : Fin (2 * r' + k + 1) → ℂ) (h : 0 < 1 + r') :
    liftVec k 1 r' v (eI k (1 + r') ⟨0, h⟩) = 0 := by
  simp [liftVec, eI]

theorem ell_lev (hHA : HeisAct) (z1 : Fin (2 * r' + k + 1) → ℂ) (m : Mat k r') (X : HPar k r') :
    ell k (1 + r') (liftVec k 1 r' z1) (heis0 k r' X * ιLev k 1 r' m) =
      -herm (Hpk k r') (m *ᵥ fvec k r' z1 ⟨0, by omega⟩) X.1 + ell k r' z1 m := by
  have key : ∀ a : Fin (1 + r'),
      ((heis0 k r' X * ιLev k 1 r' m) *ᵥ fvec k (1 + r') (liftVec k 1 r' z1) ⟨a.val + 1, by omega⟩)
        (eI k (1 + r') a) =
      liftVec k 1 r' (m *ᵥ fvec k r' z1 ⟨a.val, by omega⟩) (eI k (1 + r') a) -
        herm (Hpk k r') (m *ᵥ fvec k r' z1 ⟨a.val, by omega⟩) X.1 * e0 k r' (eI k (1 + r') a) := by
    intro a
    rw [fvec_lift, hcol hHA]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [ell_col, ell_col, sum_fin_one_add_eq_add_sum]
  refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun a' _ => ?_)
  · beta_reduce
    rw [key, firstVector_apply_first, liftVec_apply_eI_zero_eq_zero, mul_one, zero_sub]
  · beta_reduce
    rw [key, firstVector_apply_succ, mul_zero, sub_zero, eI_succ, liftVec_apply_sh]

theorem lam_lev (hHA : HeisAct) (z1 : Fin (2 * r' + k + 1) → ℂ) (m : Mat k r') (X : HPar k r') :
    lam k (1 + r') (liftVec k 1 r' z1) (heis0 k r' X * ιLev k 1 r' m) =
      -2 * (herm (Hpk k r') (m *ᵥ fvec k r' z1 ⟨0, by omega⟩) X.1).im + lam k r' z1 m := by
  simp only [lam, cStd]
  rw [ell_lev hHA]
  simp only [mul_add, mul_neg, Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.neg_im]
  norm_num

theorem z_lift (z : Fin (2 * (1 + r') + k + 1) → ℂ) (hz : inWb k (1 + r') z) :
    z = liftVec k 1 r' (fun q => z (sh q)) := by
  unfold inWb at hz
  funext p
  by_cases hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k
  · have h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := by omega
    rw [hz p (by omega)]
    simp only [liftVec, dif_neg h0]
  · have hp' : p = sh ⟨p.val - 1, by have := p.isLt; omega⟩ := by
      ext
      simp only [sh, Fin.val_mk]
      omega
    rw [hp', liftVec_apply_sh]

theorem shifted_mem_weightSpace (z : Fin (2 * (1 + r') + k + 1) → ℂ) (hz : inWb k (1 + r') z) : inWb k r' (fun q => z (sh q)) := by
  unfold inWb at hz ⊢
  intro i hi
  have := i.isLt
  exact hz (sh i) (by simp only [sh, Fin.val_mk]; omega)

theorem tz_lift (z1 : Fin (2 * r' + k + 1) → ℂ) : Tz k (1 + r') (liftVec k 1 r' z1) = Tz k r' z1 := by
  unfold Tz
  rw [herm_lv]

end Lv2

end BL

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace BL

theorem herm_conj {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (v w : Fin n → ℂ) :
    star (herm H v w) = herm H w v := by
  have h : ∀ i j, star (H i j) = H j i := fun i j => by
    have := congrFun (congrFun hH j) i
    simpa [Matrix.conjTranspose_apply] using this
  unfold herm
  simp only [dotProduct, mulVec, star_sum, star_mul', star_star, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h]; ring

theorem dot_bvec_r {n : ℕ} (i : Fin n) (x : Fin n → ℂ) : x ⬝ᵥ bvec i = x i := by
  simp [bvec]

section ex
variable (k n : ℕ)

def wp (i : Fin (k - 1)) : Fin (2 * n + k + 1) := wI k n ⟨i.val + 1, by omega⟩

def wv (i : Fin (k - 1)) : Fin (2 * n + k + 1) → ℂ := bvec (wp k n i)

theorem wp_val (i : Fin (k - 1)) : (wp k n i).val = n + (i.val + 1) := rfl


private theorem Hpk_apply_wp_eq_ite (i : Fin (k - 1)) (j : Fin (2 * n + k + 1)) :
    Hpk k n (wp k n i) j = if wp k n i = j then 1 else 0 := by
  have hi := i.isLt
  have hv := wp_val k n i
  have hj := j.isLt
  have hij : wp k n i = j ↔ (wp k n i).val = j.val := Fin.ext_iff
  unfold Hpk
  by_cases h : (wp k n i).val = j.val
  · rw [if_pos (hij.2 h), if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, hij.2 h⟩,
      if_neg (by omega)]
  · rw [if_neg (fun he => h (hij.1 he)), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem hpk_mv_w (i : Fin (k - 1)) (y : Fin (2 * n + k + 1) → ℂ) : (Hpk k n *ᵥ y) (wp k n i) = y (wp k n i) := by
  simp only [mulVec, dotProduct, Hpk_apply_wp_eq_ite, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem hpk_bvec_w (i : Fin (k - 1)) : Hpk k n *ᵥ wv k n i = wv k n i := by
  funext p
  have hc : Hpk k n p (wp k n i) = star (Hpk k n (wp k n i) p) := by
    have := congrFun (congrFun (hpk_conjT k n) p) (wp k n i)
    rw [Matrix.conjTranspose_apply] at this
    exact this.symm
  simp only [wv, bvec, mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hc, Hpk_apply_wp_eq_ite]
  by_cases h : wp k n i = p
  · subst h; simp
  · rw [if_neg h, if_neg (fun he => h he.symm), star_zero]

theorem phi_w (a : Fin (n + 1)) (i : Fin (k - 1)) : phiV k n a (wp k n i) = 0 := by
  have hi := i.isLt
  have hv := wp_val k n i
  have ha := a.isLt
  unfold phiV
  split_ifs with h
  · simp only [bvec]
    rw [Pi.single_apply, if_neg]
    intro he
    have := congrArg Fin.val he
    simp only [esI] at this
    omega
  · simp only [epsV, bvec, Pi.smul_apply, Pi.add_apply, Pi.single_apply]
    rw [if_neg, if_neg]
    · simp
    · intro he
      have := congrArg Fin.val he
      simp [wI, Fin.val_last] at this <;> omega
    · intro he
      have := congrArg Fin.val he
      simp [wI] at this <;> omega

theorem phi'_w (a : Fin (n + 1)) (i : Fin (k - 1)) : phiV' k n a (wp k n i) = 0 := by
  show (Hpk k n *ᵥ phiV k n a) (wp k n i) = 0
  rw [hpk_mv_w, phi_w]

theorem herm_w_l (v : Fin (2 * n + k + 1) → ℂ) (i : Fin (k - 1)) : herm (Hpk k n) (wv k n i) v = star (v (wp k n i)) := by
  unfold herm
  rw [hpk_bvec_w]
  simp only [wv]
  rw [dot_bvec_r]
  rfl

theorem herm_w_r (v : Fin (2 * n + k + 1) → ℂ) (i : Fin (k - 1)) : herm (Hpk k n) v (wv k n i) = v (wp k n i) := by
  unfold herm
  have hs : star (wv k n i) = Pi.single (wp k n i) (1 : ℂ) := by
    ext j
    by_cases h : j = wp k n i <;> simp [wv, bvec, h]
  rw [hs, single_dotProduct, one_mul, hpk_mv_w]

def Phv : Fin (n + 1) ⊕ (Fin (n + 1) ⊕ Fin (k - 1)) → Fin (2 * n + k + 1) → ℂ :=
  Sum.elim (phiV' k n) (Sum.elim (phiV k n) (wv k n))

def Psv : Fin (n + 1) ⊕ (Fin (n + 1) ⊕ Fin (k - 1)) → Fin (2 * n + k + 1) → ℂ :=
  Sum.elim (phiV k n) (Sum.elim (phiV' k n) (wv k n))

private theorem herm_Hpk_mulVec_Hpk_mulVec (x y : Fin (2 * n + k + 1) → ℂ) :
    herm (Hpk k n) (Hpk k n *ᵥ x) (Hpk k n *ᵥ y) = herm (Hpk k n) x y := by
  unfold herm
  rw [mulVec_mulVec, hpk_mul, one_mulVec, Matrix.star_mulVec, hpk_conjT, dotProduct_mulVec]

theorem pair_all (hk : 1 ≤ k) (c d : Fin (n + 1) ⊕ (Fin (n + 1) ⊕ Fin (k - 1))) :
    herm (Hpk k n) (Phv k n d) (Psv k n c) = if c = d then 1 else 0 := by
  have hφ' : ∀ a, phiV' k n a = Hpk k n *ᵥ phiV k n a := fun _ => rfl
  rcases c with b | b | i <;> rcases d with a | a | j <;>
    simp only [Phv, Psv, Sum.elim_inl, Sum.elim_inr]
  · rw [← herm_conj (Hpk k n) (hpk_conjT k n) (phiV k n b) (phiV' k n a), phi_pair k n hk]
    by_cases h : b = a
    · subst h; simp
    · simp [h]
  · rw [phi_iso k n hk]; simp
  · rw [herm_w_l, phi_w]; simp
  · rw [hφ', hφ', herm_Hpk_mulVec_Hpk_mulVec, phi_iso k n hk]; simp
  · rw [phi_pair k n hk]
    by_cases h : a = b
    · subst h; simp
    · simp [h, Ne.symm h]
  · rw [herm_w_l, phi'_w]; simp
  · rw [herm_w_r, phi'_w]; simp
  · rw [herm_w_r, phi_w]; simp
  · rw [herm_w_l]
    simp only [wv, bvec, Pi.single_apply]
    by_cases h : i = j
    · subst h; simp
    · have hne : wp k n j ≠ wp k n i := by
        intro he
        apply h
        ext
        have := congrArg Fin.val he
        rw [wp_val, wp_val] at this
        omega
      simp [hne, h]

private theorem herm_sum_smul_left_tail_integrals {ι : Type*} [Fintype ι] (g : ι → ℂ) (v : ι → Fin (2 * n + k + 1) → ℂ)
    (w : Fin (2 * n + k + 1) → ℂ) :
    herm (Hpk k n) (∑ c, g c • v c) w = ∑ c, g c * herm (Hpk k n) (v c) w := by
  unfold herm
  simp only [dotProduct, mulVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem expand (hk : 1 ≤ k) (y : Fin (2 * n + k + 1) → ℂ) :
    y = ∑ c, herm (Hpk k n) y (Psv k n c) • Phv k n c := by
  have hcoef : ∀ (g : Fin (n + 1) ⊕ (Fin (n + 1) ⊕ Fin (k - 1)) → ℂ) c,
      herm (Hpk k n) (∑ d, g d • Phv k n d) (Psv k n c) = g c := by
    intro g c
    rw [herm_sum_smul_left_tail_integrals]
    simp [pair_all k n hk]
  have hli : LinearIndependent ℂ (Phv k n) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg c
    have := hcoef g c
    rw [hg] at this
    simpa [herm] using this.symm
  have hcard : Fintype.card (Fin (n + 1) ⊕ (Fin (n + 1) ⊕ Fin (k - 1))) =
      Module.finrank ℂ (Fin (2 * n + k + 1) → ℂ) := by
    simp only [Fintype.card_sum, Fintype.card_fin, Module.finrank_fin_fun]
    omega
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ∀ c, b c = Phv k n c := fun c => by simp [b]
  have hy := b.sum_repr y
  simp only [hb] at hy
  conv_lhs => rw [← hy]
  refine Finset.sum_congr rfl fun c _ => ?_
  have := hcoef (fun d => b.repr y d) c
  rw [hy] at this
  rw [this]

theorem herm_expand (hk : 1 ≤ k) (y w : Fin (2 * n + k + 1) → ℂ) :
    herm (Hpk k n) y w = ∑ j, (herm (Hpk k n) y (phiV k n j) * herm (Hpk k n) (phiV' k n j) w +
      herm (Hpk k n) y (phiV' k n j) * herm (Hpk k n) (phiV k n j) w) +
      ∑ i, y (wp k n i) * herm (Hpk k n) (wv k n i) w := by
  conv_lhs => rw [expand k n hk y]
  rw [herm_sum_smul_left_tail_integrals, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Psv, Phv, Sum.elim_inl, Sum.elim_inr, herm_w_r]
  rw [Finset.sum_add_distrib]
  exact (add_assoc _ _ _).symm

theorem herm_linF (hk : 1 ≤ k) (y w : Fin (2 * n + k + 1) → ℂ) (s : ℝ) :
    herm (Hpk k n) y w = linF (fun j => herm (Hpk k n) (phiV' k n (Fin.cast (by omega) j)) w)
      (fun j => herm (Hpk k n) (phiV k n (Fin.cast (by omega) j)) w) (fun i => herm (Hpk k n) (wv k n i) w)
      (hcoord k n (y, s)) := by
  rw [herm_expand k n hk y w]
  simp only [linF, hcoord]
  congr 1
  exact ((finCongr (by omega : 1 + n = n + 1)).sum_comp (fun j =>
    herm (Hpk k n) y (phiV k n j) * herm (Hpk k n) (phiV' k n j) w +
      herm (Hpk k n) y (phiV' k n j) * herm (Hpk k n) (phiV k n j) w)).symm

end ex

end BL

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace BL

section cont
variable {p m : ℕ}

theorem cont_ite {β : Type} [TopologicalSpace β] [Zero β] (c : Prop) [Decidable c] {f : Xp p m → β}
    (hf : Continuous f) : Continuous (fun x => if c then f x else 0) := by
  by_cases h : c
  · simp only [h, if_true]; exact hf
  · simp only [h, if_false]; exact continuous_const

theorem cont_Lsq (l : Fin (p + 1)) : Continuous (fun x : Xp p m => Lsq x l) := by
  unfold Lsq
  exact continuous_const.add (continuous_finsetSum _ fun j _ =>
    cont_ite _ (((continuous_apply j).comp continuous_fst).norm.pow 2))

theorem cont_rhoSq (l : Fin (p + 1)) : Continuous (fun x : Xp p m => rhoSq x l) := by
  unfold rhoSq
  refine ((cont_Lsq _).add (continuous_finsetSum _ fun i _ => ?_)).add (continuous_finsetSum _ fun j _ => ?_)
  · exact ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).norm.pow 2
  · exact cont_ite _ (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).norm.pow 2)

theorem cont_bco (l : Fin (p + 1)) : Continuous (fun x : Xp p m => bco x l) := by
  unfold bco
  refine ((Complex.continuous_ofReal.comp ((continuous_finsetSum _ fun i _ => ?_).neg.div_const 2)).add
    ((Complex.continuous_ofReal.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).mul
      continuous_const)).sub (continuous_finsetSum _ fun j _ => ?_)
  · exact ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).norm.pow 2
  · exact cont_ite _ (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).mul
      ((continuous_apply j).comp continuous_fst).star)

theorem cont_de (l : Fin (p + 1)) : Continuous (fun x : Xp p m => de x l) := by
  unfold de
  exact Real.continuous_sqrt.comp (((cont_Lsq l).mul (cont_rhoSq l)).add ((cont_bco l).norm.pow 2))

theorem cont_linF (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) : Continuous (fun x : Xp p m => linF η η' ζ x) := by
  unfold linF
  refine (continuous_finsetSum _ fun j _ => ?_).add (continuous_finsetSum _ fun i _ => ?_)
  · exact (((continuous_apply j).comp continuous_fst).mul continuous_const).add
      (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).mul continuous_const)
  · exact ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).mul continuous_const

def GI (s : Fin (p + 1) → ℝ) (δ : ℝ) (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) (c₀ : ℝ) (x : Xp p m) : ℝ≥0∞ :=
  (∏ l, ENNReal.ofReal (de x l ^ (-s l))) * ENNReal.ofReal ((1 + |2 * (linF η η' ζ x).im + c₀|) ^ (-δ))

theorem meas_GI (s : Fin (p + 1) → ℝ) (δ : ℝ) (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) (c₀ : ℝ) :
    Measurable (GI s δ η η' ζ c₀) := by
  unfold GI
  refine (Finset.measurable_prod _ fun l _ => ?_).mul ?_
  · exact ENNReal.measurable_ofReal.comp ((cont_de l).measurable.pow_const _)
  · exact ENNReal.measurable_ofReal.comp ((continuous_const.add ((continuous_const.mul
      (Complex.continuous_im.comp (cont_linF η η' ζ))).add continuous_const).abs).measurable.pow_const _)

end cont

theorem mp_unitary {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1) :
    MeasurePreserving (fun y : Fin N → ℂ => U *ᵥ y) volume volume := by
  set f : (Fin N → ℂ) →ₗ[ℝ] (Fin N → ℂ) := (Matrix.toLin' U).restrictScalars ℝ with hf
  have hfU : (fun y : Fin N → ℂ => U *ᵥ y) = ⇑f := by funext y; simp [hf, Matrix.toLin'_apply]
  have hn : ((Complex.normSq U.det : ℝ) : ℂ) = 1 := by
    have h := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
    rw [Complex.normSq_eq_conj_mul_self]; exact h
  have hdet : LinearMap.det f = 1 := by
    rw [hf, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]; exact_mod_cast hn
  rw [hfU]
  refine ⟨f.continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; norm_num), hdet]
  simp

theorem mp_hpar {k n : ℕ} (U : Mat k n) (hU : Uᴴ * U = 1) :
    MeasurePreserving (fun X : HPar k n => (U *ᵥ X.1, X.2)) volume volume :=
  (mp_unitary U hU).prod (MeasurePreserving.id volume)

theorem os_q (hOS : OS) (q p m : ℕ) (hq : q = p + 1) (δ γ : ℝ) (e : Fin (q + 1) → ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hγ : 0 < γ) (hγ8 : γ ≤ δ / 8) (he : ∀ l, 0 < e l) (hsum : e 0 + 2 * ∑ i : Fin q, e i.succ < γ / 2) :
    ∃ C : ℝ, ∀ (η η' : Fin q → ℂ) (ζ : Fin m → ℂ) (c₀ : ℝ), η' ⟨0, by omega⟩ ≠ 0 →
      ∫⁻ x, GI (fun l => s0N q m l - e l) δ η η' ζ c₀ x ≤
        ENNReal.ofReal (C * ‖η' ⟨0, by omega⟩‖ ^ (-γ) * (1 + |c₀|) ^ (-δ / 4)) := by
  subst hq
  obtain ⟨C, hC⟩ := hOS p m δ γ e hδ hδ2 hγ hγ8 he hsum
  refine ⟨C, fun η η' ζ c₀ h0 => ?_⟩
  have e0 : (⟨0, by omega⟩ : Fin (p + 1)) = 0 := Fin.ext (by simp)
  rw [e0] at h0 ⊢
  exact hC η η' ζ c₀ h0

end BL

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace BL

theorem cz0 {k : ℕ} (hk : 1 ≤ k) (z : Fin (2 * 0 + k + 1) → ℂ) (hT : 0 < Tz k 0 z) :
    herm (Hpk k 0) (epsV k 0) z ≠ 0 := by
  intro h
  have sgl : ∀ p : Fin (2 * 0 + k + 1), sg k 0 p.val = p.val := fun p => by
    have := p.2; unfold sg; rw [if_neg (by omega)]
  have hmv : ∀ (v : Fin (2 * 0 + k + 1) → ℂ) (p : Fin (2 * 0 + k + 1)),
      (Hpk k 0 *ᵥ v) p = (if p.val = 0 + k then -1 else 1) * v p := by
    intro v p; simp only [mulVec, dotProduct]
    rw [Finset.sum_eq_single p]
    · rw [hpk_apply, sgl, if_pos rfl]
    · intro q _ hq; rw [hpk_apply, sgl, if_neg (fun e => hq (Fin.ext e)), zero_mul]
    · intro hp; exact absurd (Finset.mem_univ _) hp
  have hw0 : (wI k 0 0).val = 0 := by simp [wI]
  have hwk : (wI k 0 (Fin.last k)).val = k := by simp [wI]
  have e1 : Hpk k 0 *ᵥ bvec (wI k 0 0) = bvec (wI k 0 0) := by
    funext p; rw [hmv]; split_ifs with hp
    · rw [bvec_ne _ _ (by omega), mul_zero]
    · rw [one_mul]
  have e2 : Hpk k 0 *ᵥ bvec (wI k 0 (Fin.last k)) = -bvec (wI k 0 (Fin.last k)) := by
    funext p; rw [hmv, Pi.neg_apply]; split_ifs with hp
    · rw [neg_one_mul]
    · rw [bvec_ne _ _ (by omega), mul_zero, neg_zero]
  have hh : herm (Hpk k 0) (epsV k 0) z =
      ((Real.sqrt 2)⁻¹ : ℂ) * (star (z (wI k 0 0)) - star (z (wI k 0 (Fin.last k)))) := by
    unfold epsV herm
    rw [mulVec_smul, mulVec_add, e1, e2, dotProduct_smul, dotProduct_add, dotProduct_neg, dot_bvec_r, dot_bvec_r,
      Pi.star_apply, Pi.star_apply, smul_eq_mul, sub_eq_add_neg]
  have hc : ((Real.sqrt 2)⁻¹ : ℂ) ≠ 0 := by
    have : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) ≠ 0 := by rw [sq2_mul_sq2_eq_half]; norm_num
    exact left_ne_zero_of_mul this
  rw [hh] at h
  have hzz : z (wI k 0 0) = z (wI k 0 (Fin.last k)) :=
    star_injective (sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hc))
  have hre : (herm (Hpk k 0) z z).re = ∑ p, (if p.val = 0 + k then (-1 : ℝ) else 1) * Complex.normSq (z p) := by
    unfold herm
    simp only [dotProduct, hmv, Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Pi.star_apply]
    split_ifs <;> simp [Complex.mul_re, Complex.normSq_apply]
  have hne : wI k 0 0 ≠ wI k 0 (Fin.last k) := fun e => by have := congrArg Fin.val e; omega
  have key : 0 ≤ ∑ p, (if p.val = 0 + k then (-1 : ℝ) else 1) * Complex.normSq (z p) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (wI k 0 (Fin.last k))),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hne, Finset.mem_univ (wI k 0 0)⟩)]
    rw [if_pos (show (wI k 0 (Fin.last k)).val = 0 + k by omega), if_neg (show ¬ (wI k 0 0).val = 0 + k by omega),
      hzz]
    have hrest : 0 ≤ ∑ p ∈ (Finset.univ.erase (wI k 0 (Fin.last k))).erase (wI k 0 0),
        (if p.val = 0 + k then (-1 : ℝ) else 1) * Complex.normSq (z p) := by
      refine Finset.sum_nonneg fun p hp => ?_
      have hpk : p ≠ wI k 0 (Fin.last k) := (Finset.mem_erase.1 (Finset.mem_erase.1 hp).2).1
      rw [if_neg (show ¬ (p.val = 0 + k) from fun e => hpk (Fin.ext (by omega)))]
      exact mul_nonneg zero_le_one (Complex.normSq_nonneg _)
    linarith
  unfold Tz at hT
  rw [hre] at hT
  linarith

theorem cz_ne {k n : ℕ} (hk : 1 ≤ k) (z1 : Fin (2 * n + k + 1) → ℂ) (hT : 0 < Tz k n z1) :
    herm (Hpk k n) (phiV k n ⟨0, by omega⟩) (fvec k n z1 ⟨0, by omega⟩) ≠ 0 := by
  by_cases hn : 0 < n
  · unfold phiV fvec
    rw [dif_pos hn, dif_pos hn, herm_bb, hpk_apply]
    rw [if_pos (show (esI k n ⟨0, hn⟩).val = sg k n (eI k n ⟨0, hn⟩).val by
        show 2 * n + k - 0 = sg k n 0; unfold sg; rw [if_pos (Or.inl hn)]),
      if_neg (show ¬ (eI k n ⟨0, hn⟩).val = n + k by show ¬ 0 = n + k; omega)]
    norm_num
  · have hn0 : n = 0 := by omega
    subst hn0
    unfold phiV fvec
    rw [dif_neg (lt_irrefl 0), dif_neg (lt_irrefl 0)]
    exact cz0 hk z1 hT

def etaF (k n : ℕ) (w : Fin (2 * n + k + 1) → ℂ) : Fin (1 + n) → ℂ :=
  fun j => herm (Hpk k n) (phiV' k n (Fin.cast (by omega) j)) w

def eta'F (k n : ℕ) (w : Fin (2 * n + k + 1) → ℂ) : Fin (1 + n) → ℂ :=
  fun j => herm (Hpk k n) (phiV k n (Fin.cast (by omega) j)) w

def zetaF (k n : ℕ) (w : Fin (2 * n + k + 1) → ℂ) : Fin (k - 1) → ℂ := fun i => herm (Hpk k n) (wv k n i) w

theorem herm_linF' {k n : ℕ} (hk : 1 ≤ k) (y w : Fin (2 * n + k + 1) → ℂ) (s : ℝ) :
    herm (Hpk k n) y w = linF (etaF k n w) (eta'F k n w) (zetaF k n w) (hcoord k n (y, s)) :=
  herm_linF k n hk y w s

section inner
variable {k r' : ℕ}

theorem inner_bound (hIW : IW) (hF : FormulaF) (hHC : HeisConjLev) (hHA : HeisAct) (hk : 1 ≤ k)
    (s : Fin (1 + r' + 1) → ℝ) (δ γ C : ℝ) (z1 : Fin (2 * r' + k + 1) → ℂ)
    (hC : ∀ (η η' : Fin (1 + r') → ℂ) (ζ : Fin (k - 1) → ℂ) (c₀ : ℝ), η' ⟨0, by omega⟩ ≠ 0 →
      ∫⁻ x, GI s δ η η' ζ c₀ x ≤ ENNReal.ofReal (C * ‖η' ⟨0, by omega⟩‖ ^ (-γ) * (1 + |c₀|) ^ (-δ / 4)))
    (hcz : herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩) ≠ 0)
    (m : Mat k r') (hm : m ∈ UH (Hpk k r')) :
    ∫⁻ X : HPar k r', ENNReal.ofReal (xiR k (1 + r') s (heis0 k r' X * ιLev k 1 r' m)) *
        ENNReal.ofReal ((1 + |lam k (1 + r') (liftVec k 1 r' z1) (heis0 k r' X * ιLev k 1 r' m)|) ^ (-δ)) ≤
      ENNReal.ofReal (C * ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ ^ (-γ)) *
        (ENNReal.ofReal (xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) m) *
          ENNReal.ofReal ((1 + |lam k r' z1 m|) ^ (-(δ / 4)))) := by
  obtain ⟨κ, hκG, hκU, t, ht, htn, hD⟩ := lev_data hIW hHC hk m hm
  have hκU' : κ * κᴴ = 1 := mul_eq_one_comm.1 hκU
  have h00 : (0 : Fin (r' + 1)) = ⟨0, by omega⟩ := Fin.ext (by simp)
  have ht' : m *ᵥ phiV k r' ⟨0, by omega⟩ = t • (κ *ᵥ phiV k r' ⟨0, by omega⟩) := by rw [← h00]; exact ht
  obtain ⟨w, hw⟩ : ∃ w, w = κᴴ *ᵥ (m *ᵥ fvec k r' z1 ⟨0, by omega⟩) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = ∏ a : Fin (r' + 1), Del k r' a m ^ (-s (su a)) := ⟨_, rfl⟩
  have hDel : ∀ (n : ℕ) (l : Fin (n + 1)) (x : Mat k n), 0 ≤ Del k n l x := fun n l x => Real.sqrt_nonneg _
  have hA0 : 0 ≤ A := by rw [hA]; exact Finset.prod_nonneg fun a _ => Real.rpow_nonneg (hDel _ _ _) _
  have hpt : ∀ X : HPar k r',
      ENNReal.ofReal (xiR k (1 + r') s (heis0 k r' X * ιLev k 1 r' m)) *
        ENNReal.ofReal ((1 + |lam k (1 + r') (liftVec k 1 r' z1) (heis0 k r' X * ιLev k 1 r' m)|) ^ (-δ)) =
      ENNReal.ofReal A * GI s δ (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (lam k r' z1 m)
        (hcoord k r' (κᴴ *ᵥ X.1, X.2)) := by
    intro X
    obtain ⟨hD0, hDS⟩ := hD X
    have hde : ∀ (x : Xp (1 + r') (k - 1)) (l : Fin (1 + r' + 1)), 0 ≤ de x l := fun x l => Real.sqrt_nonneg _
    have hmr : ∀ a : Fin (r' + 1), (Del k r' a m * de (hcoord k r' (κᴴ *ᵥ X.1, X.2)) (su a)) ^ (-s (su a)) =
        Del k r' a m ^ (-s (su a)) * de (hcoord k r' (κᴴ *ᵥ X.1, X.2)) (su a) ^ (-s (su a)) :=
      fun a => Real.mul_rpow (hDel _ _ _) (hde _ _)
    have hxi : xiR k (1 + r') s (heis0 k r' X * ιLev k 1 r' m) =
        A * ∏ l, de (hcoord k r' (κᴴ *ᵥ X.1, X.2)) l ^ (-s l) := by
      unfold xiR
      rw [prod_su, prod_su (fun l => de (hcoord k r' (κᴴ *ᵥ X.1, X.2)) l ^ (-s l)), hD0]
      simp only [hDS, (hF k r' hk).1, hmr, Finset.prod_mul_distrib]
      rw [hA]; ring
    have hX : X.1 = κ *ᵥ (κᴴ *ᵥ X.1) := by rw [mulVec_mulVec, hκU', one_mulVec]
    have hmf : m *ᵥ fvec k r' z1 ⟨0, by omega⟩ = κ *ᵥ w := by rw [hw, mulVec_mulVec, hκU', one_mulVec]
    have hh : herm (Hpk k r') (κ *ᵥ w) X.1 = star (herm (Hpk k r') (κᴴ *ᵥ X.1) w) := by
      conv_lhs => rw [hX]
      rw [herm_UH _ _ hκG]
      exact (herm_conj _ (hpk_conjT k r') _ _).symm
    have hlam : lam k (1 + r') (liftVec k 1 r' z1) (heis0 k r' X * ιLev k 1 r' m) =
        2 * (linF (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (hcoord k r' (κᴴ *ᵥ X.1, X.2))).im + lam k r' z1 m := by
      rw [lam_lev hHA, hmf, hh, herm_linF' hk _ w X.2, Complex.star_def, Complex.conj_im]
      ring
    rw [hxi, hlam, ENNReal.ofReal_mul hA0, ENNReal.ofReal_prod_of_nonneg (fun l _ => Real.rpow_nonneg (hde _ l) _)]
    unfold GI; rw [mul_assoc]
  have key : t * eta'F k r' w ⟨0, by omega⟩ = herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩) := by
    show t * herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) w = _
    rw [hw, ← herm_UH _ _ hκG (phiV k r' ⟨0, by omega⟩) (κᴴ *ᵥ (m *ᵥ fvec k r' z1 ⟨0, by omega⟩)),
      mulVec_mulVec (m *ᵥ fvec k r' z1 ⟨0, by omega⟩) κ κᴴ, hκU', one_mulVec, ← herm_smul_l, ← ht', herm_UH _ _ hm]
  have ht0 : t ≠ 0 := fun h => hcz (by rw [← key, h, zero_mul])
  have hη0 : eta'F k r' w ⟨0, by omega⟩ ≠ 0 := fun h => hcz (by rw [← key, h, mul_zero])
  have hκH : (κᴴ)ᴴ * κᴴ = 1 := by rw [conjTranspose_conjTranspose]; exact hκU'
  have hg : Measurable (fun x => GI s δ (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (lam k r' z1 m) (hcoord k r' x)) :=
    (meas_GI _ _ _ _ _ _).comp (hF k r' hk).2.measurable
  have hD0pos : 0 < Del k r' 0 m := by rw [← htn]; exact norm_pos_iff.2 ht0
  have hcz0 : 0 < ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ := norm_pos_iff.2 hcz
  have hnorm : ‖eta'F k r' w ⟨0, by omega⟩‖ =
      ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ / Del k r' 0 m := by
    have : eta'F k r' w ⟨0, by omega⟩ = herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩) / t := by
      rw [eq_div_iff ht0, mul_comm]; exact key
    rw [this, norm_div, htn]
  have hQ : xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) m = A * Del k r' 0 m ^ γ := by
    unfold xiR; rw [hA, Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp only [if_true, Fin.succ_ne_zero, if_false, sub_zero]
    rw [show -(s (su 0) - γ) = -s (su 0) + γ by ring, Real.rpow_add hD0pos]; ring
  have hQ0 : 0 ≤ xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) m :=
    Finset.prod_nonneg fun a _ => Real.rpow_nonneg (hDel _ _ _) _
  have hR0 : 0 ≤ (1 + |lam k r' z1 m|) ^ (-(δ / 4)) := Real.rpow_nonneg (by positivity) _
  calc _ = ∫⁻ X : HPar k r', ENNReal.ofReal A * GI s δ (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (lam k r' z1 m)
          (hcoord k r' (κᴴ *ᵥ X.1, X.2)) := lintegral_congr hpt
    _ = ENNReal.ofReal A * ∫⁻ X : HPar k r', GI s δ (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (lam k r' z1 m)
          (hcoord k r' (κᴴ *ᵥ X.1, X.2)) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal A * ∫⁻ X : HPar k r', GI s δ (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (lam k r' z1 m)
          (hcoord k r' X) := by rw [(mp_hpar κᴴ hκH).lintegral_comp hg]
    _ = ENNReal.ofReal A * ∫⁻ x, GI s δ (etaF k r' w) (eta'F k r' w) (zetaF k r' w) (lam k r' z1 m) x := by
          rw [(hF k r' hk).2.lintegral_comp (meas_GI _ _ _ _ _ _)]
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal (C * ‖eta'F k r' w ⟨0, by omega⟩‖ ^ (-γ) * (1 + |lam k r' z1 m|) ^ (-δ / 4)) := by
          gcongr; exact hC _ _ _ _ hη0
    _ = ENNReal.ofReal (A * (C * ‖eta'F k r' w ⟨0, by omega⟩‖ ^ (-γ) * (1 + |lam k r' z1 m|) ^ (-δ / 4))) :=
          (ENNReal.ofReal_mul hA0).symm
    _ = ENNReal.ofReal ((C * ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ ^ (-γ)) *
          (xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) m * (1 + |lam k r' z1 m|) ^ (-(δ / 4)))) := by
          congr 1
          rw [hnorm, Real.div_rpow hcz0.le hD0pos.le, Real.rpow_neg hD0pos.le, div_inv_eq_mul, hQ, neg_div]; ring
    _ = _ := by rw [ENNReal.ofReal_mul' (mul_nonneg hQ0 hR0), ENNReal.ofReal_mul hQ0]

end inner

end BL

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

section
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 BL

theorem bStepBase_of (hB2 : InductiveHeisenbergInputs) : BStepBase := by
  obtain ⟨-, -, -, -, hNB, -⟩ := hB2
  intro k _ δ _
  refine ⟨1, one_pos, fun s _ z _ _ μN hμ => ?_⟩
  set o : Mt k 0 := ((1 : Mat k 0) : Mt k 0) with ho
  have hc : μN ({o}ᶜ : Set (Mt k 0)) = 0 := by
    have h := hμ.conc; rw [hNB k] at h; exact h
  have hr : μN.restrict {o} = μN :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.2 (by simpa [Set.compl_def] using hc))
  unfold IInt
  rw [← hr, lintegral_singleton]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
    (hμ.finite_compact _ isCompact_singleton)

theorem bStepSucc_of (hB2 : InductiveHeisenbergInputs) (hIW : IW) (hF : FormulaF) (hOS : OS) : BStepSucc := by
  obtain ⟨-, -, -, hNR, -, hHC, -, -, -, -, -, hHH, -, -, -, -, hHU, -, -, -, hCN, -, -, -, hHN, -, hHA⟩ := hB2
  intro k r r' hr hk δ hδ hδ2 hB'
  subst hr
  obtain ⟨e', he', hB'⟩ := hB'
  obtain ⟨γ, hγd⟩ : ∃ γ : ℝ, γ = min (δ / 8) (e' / 2) := ⟨_, rfl⟩
  have hγ : 0 < γ := by rw [hγd]; exact lt_min (by positivity) (by positivity)
  have hγ8 : γ ≤ δ / 8 := by rw [hγd]; exact min_le_left _ _
  have hγe : γ ≤ e' / 2 := by rw [hγd]; exact min_le_right _ _
  have hD : (0 : ℝ) < 4 * (1 + r') + 4 := by positivity
  refine ⟨min (e' / 2) (γ / (4 * (1 + r') + 4)), lt_min (by positivity) (div_pos hγ hD), ?_⟩
  intro s hs z hzW hzT μN hμN
  have he0 : ∀ l, 0 < s0 k (1 + r') l - s l := fun l => (hs l).1
  have heS : ∀ l, s0 k (1 + r') l - s l ≤ γ / (4 * (1 + r') + 4) := fun l => le_trans (hs l).2 (min_le_right _ _)
  have heS' : ∀ l, s0 k (1 + r') l - s l ≤ e' / 2 := fun l => le_trans (hs l).2 (min_le_left _ _)
  have hs0 : ∀ l, s0N (1 + r') (k - 1) l = s0 k (1 + r') l := by
    intro l; unfold s0N s0; split_ifs
    · rfl
    · push_cast [Nat.cast_sub hk]; ring
  have hsum : (s0 k (1 + r') 0 - s 0) + 2 * ∑ i : Fin (1 + r'), (s0 k (1 + r') i.succ - s i.succ) < γ / 2 := by
    have h1 : ∑ i : Fin (1 + r'), (s0 k (1 + r') i.succ - s i.succ) ≤ (1 + r') * (γ / (4 * (1 + r') + 4)) := by
      calc _ ≤ ∑ _i : Fin (1 + r'), γ / (4 * (1 + r') + 4) := Finset.sum_le_sum fun i _ => heS _
        _ = _ := by simp [Finset.sum_const, Finset.card_univ]
    have key : (3 + 2 * (r' : ℝ)) * (γ / (4 * (1 + r') + 4)) < γ / 2 := by
      rw [mul_div_assoc', div_lt_div_iff₀ hD (by norm_num)]; nlinarith
    linarith [heS 0]
  obtain ⟨C, hC⟩ := os_q hOS (1 + r') r' (k - 1) (by omega) δ γ (fun l => s0 k (1 + r') l - s l) hδ hδ2 hγ hγ8 he0 hsum
  have hC' : ∀ (η η' : Fin (1 + r') → ℂ) (ζ : Fin (k - 1) → ℂ) (c₀ : ℝ), η' ⟨0, by omega⟩ ≠ 0 →
      ∫⁻ x, GI s δ η η' ζ c₀ x ≤ ENNReal.ofReal (C * ‖η' ⟨0, by omega⟩‖ ^ (-γ) * (1 + |c₀|) ^ (-δ / 4)) := by
    intro η η' ζ c₀ h
    have hse : s = fun l => s0N (1 + r') (k - 1) l - (s0 k (1 + r') l - s l) := by funext l; rw [hs0]; ring
    rw [hse]; exact hC η η' ζ c₀ h
  obtain ⟨z1, hz1W, rfl⟩ : ∃ z1, inWb k r' z1 ∧ z = liftVec k 1 r' z1 := ⟨_, shifted_mem_weightSpace z hzW, z_lift z hzW⟩
  have hz1T : 0 < Tz k r' z1 := by rw [← tz_lift]; exact hzT
  have hcz := cz_ne hk z1 hz1T
  have hsP : ∀ a : Fin (r' + 1), 0 < s0 k r' a - (s (su a) - if a = 0 then γ else 0) ∧
      s0 k r' a - (s (su a) - if a = 0 then γ else 0) ≤ e' := by
    intro a
    have hs0a : s0 k r' a = s0 k (1 + r') (su a) := by
      unfold s0
      by_cases h : a.val < r'
      · rw [if_pos h, if_pos (show (su a).val < 1 + r' by rw [su_val]; omega)]
      · rw [if_neg h, if_neg (show ¬ (su a).val < 1 + r' by rw [su_val]; omega)]
    rw [hs0a]
    have h1 := he0 (su a); have h2 := heS' (su a)
    split_ifs <;> constructor <;> linarith
  obtain ⟨μ', hμ'⟩ := hHN k r'
  have hfin := hB' _ hsP z1 hz1W hz1T μ' hμ'
  obtain ⟨c, hc⟩ := hHU k (1 + r') (Nset k (1 + r')) _ μN (hCN k (1 + r')) (hNR k r' μ' hμ') hμN.conc hμN.left
    hμN.finite_compact
  rw [hc]; unfold IInt; rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
  have : IsFiniteMeasureOnCompacts μ' := ⟨fun ⦃K⦄ hK => hμ'.finite_compact K hK⟩
  have : IsFiniteMeasureOnCompacts (μHeis k r') := ⟨fun ⦃K⦄ hK => (hHH k r').finite_compact K hK⟩
  set F : Mt k (1 + r') → ℝ≥0∞ := fun n => ENNReal.ofReal (xiR k (1 + r') s (Matrix.of n)) *
    ENNReal.ofReal ((1 + |lam k (1 + r') (liftVec k 1 r' z1) (Matrix.of n)|) ^ (-δ)) with hFd
  have hsw : (μHeis k r').prod (μ'.map (levM k r')) = ((μ'.map (levM k r')).prod (μHeis k r')).map Prod.swap :=
    (Measure.prod_swap).symm
  have hae : ∀ᵐ m ∂μ', m ∈ Nset k r' := ae_iff.2 hμ'.conc
  have hpt : ∀ m ∈ Nset k r', ∫⁻ h, F (mulM (h, levM k r' m)) ∂(μHeis k r') ≤
      ENNReal.ofReal (C * ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ ^ (-γ)) *
        (ENNReal.ofReal (xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) (Matrix.of m)) *
          ENNReal.ofReal ((1 + |lam k r' z1 (Matrix.of m)|) ^ (-(δ / 4)))) := by
    intro m hm
    calc _ ≤ ∫⁻ X, F (mulM (heis0 k r' X, levM k r' m)) ∂volume := by unfold μHeis; exact lintegral_map_le _ _
      _ ≤ _ := by rw [hFd]; exact inner_bound hIW hF hHC hHA hk s δ γ C z1 hC' hcz (Matrix.of m) hm.1
  calc ∫⁻ n, F n ∂(((μHeis k r').prod (μ'.map (levM k r'))).map mulM)
      ≤ ∫⁻ q, F (mulM q) ∂((μHeis k r').prod (μ'.map (levM k r'))) := lintegral_map_le _ _
    _ = ∫⁻ q, F (mulM q) ∂(((μ'.map (levM k r')).prod (μHeis k r')).map Prod.swap) := by rw [hsw]
    _ ≤ ∫⁻ q, F (mulM q.swap) ∂((μ'.map (levM k r')).prod (μHeis k r')) := lintegral_map_le _ _
    _ ≤ ∫⁻ n', ∫⁻ h, F (mulM (h, n')) ∂(μHeis k r') ∂(μ'.map (levM k r')) := lintegral_prod_le _
    _ ≤ ∫⁻ m, ∫⁻ h, F (mulM (h, levM k r' m)) ∂(μHeis k r') ∂μ' := lintegral_map_le _ _
    _ ≤ ∫⁻ m, ENNReal.ofReal (C * ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ ^ (-γ)) *
          (ENNReal.ofReal (xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) (Matrix.of m)) *
            ENNReal.ofReal ((1 + |lam k r' z1 (Matrix.of m)|) ^ (-(δ / 4)))) ∂μ' := lintegral_mono_ae (hae.mono hpt)
    _ = ENNReal.ofReal (C * ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ ^ (-γ)) *
          ∫⁻ m, ENNReal.ofReal (xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) (Matrix.of m)) *
            ENNReal.ofReal ((1 + |lam k r' z1 (Matrix.of m)|) ^ (-(δ / 4))) ∂μ' :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end
