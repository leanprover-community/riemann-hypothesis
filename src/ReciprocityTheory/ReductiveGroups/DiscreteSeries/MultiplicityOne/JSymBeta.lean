import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroup
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StReps
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JTransM
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDefs

section
open Matrix

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SymA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

def block (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  (∀ i j : Fin (2 * r + k + 1), (j.val < r ∨ r + k < j.val) → g i j = if i = j then 1 else 0) ∧
  (∀ i j : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → g i j = if i = j then 1 else 0)

def tau (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩

def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

theorem hpk_row (i m : Fin (2 * r + k + 1)) :
    Hpk k r i m = if m = tau k r i then sgn k r i else 0 := by
  unfold Hpk tau sgn
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mul_apply (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) : (Hpk k r * A) i j = sgn k r i * A (tau k r i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (tau k r i)]
  · rw [hpk_row, if_pos rfl]
  · intro m _ hm
    rw [hpk_row, if_neg hm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem tau_tau (i : Fin (2 * r + k + 1)) : tau k r (tau k r i) = i := by
  unfold tau
  apply Fin.ext
  simp only
  split_ifs <;> omega

theorem sgn_tau (i : Fin (2 * r + k + 1)) : sgn k r (tau k r i) = sgn k r i := by
  unfold sgn tau
  simp only
  split_ifs <;> first | rfl | (exfalso; omega)

theorem sgn_mul_self (i : Fin (2 * r + k + 1)) : sgn k r i * sgn k r i = 1 := by
  unfold sgn
  split_ifs <;> norm_num

theorem hpk_sq : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [hpk_mul_apply, hpk_row, tau_tau, sgn_tau, Matrix.one_apply]
  by_cases h : j = i
  · rw [if_pos h, if_pos h.symm, sgn_mul_self]
  · rw [if_neg h, if_neg (Ne.symm h), mul_zero]

theorem isUnit_of_uh {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : IsUnit g.det := by
  apply Matrix.isUnit_det_of_left_inverse (B := Hpk k r * gᴴ * Hpk k r)
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hpk_sq]

theorem uh_mul {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) (hh : h ∈ UH (Hpk k r)) : g * h ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  rw [conjTranspose_mul]
  calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hh']

theorem uh_inv {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : g⁻¹ ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hu := isUnit_of_uh hg
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by
        rw [Matrix.mul_nonsing_inv _ hu, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem col_of_fix {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {c : Fin (2 * r + k + 1)} (hc : h *ᵥ bvec c = bvec c) (p : Fin (2 * r + k + 1)) :
    h p c = if p = c then 1 else 0 := by
  have := congrFun hc p
  simp only [bvec, Matrix.mulVec, dotProduct_single, mul_one, Pi.single_apply] at this
  exact this

theorem row_of_fixed_col {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hU : h ∈ UH (Hpk k r)) (c : Fin (2 * r + k + 1))
    (hc : ∀ p, h p c = if p = c then 1 else 0) (j : Fin (2 * r + k + 1)) :
    h (tau k r c) j = if tau k r c = j then 1 else 0 := by
  have hU' : hᴴ * Hpk k r * h = Hpk k r := hU
  have e := congrFun (congrFun hU' c) j
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single c] at e
  · rw [conjTranspose_apply, hc c, if_pos rfl, star_one, one_mul, hpk_mul_apply, hpk_row] at e
    have hs : sgn k r c ≠ 0 := by
      intro h0
      have := sgn_mul_self (k := k) (r := r) c
      rw [h0, zero_mul] at this
      exact zero_ne_one this
    by_cases hj : j = tau k r c
    · rw [if_pos hj] at e
      rw [if_pos hj.symm]
      exact mul_left_cancel₀ hs (e.trans (mul_one _).symm)
    · rw [if_neg hj] at e
      rw [if_neg (Ne.symm hj)]
      exact (mul_eq_zero.1 e).resolve_left hs
  · intro p _ hp
    rw [conjTranspose_apply, hc p, if_neg hp, star_zero, zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem uw_fixed_col {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (c : Fin (2 * r + k + 1)) (hc : c.val < r ∨ r + k < c.val) (p : Fin (2 * r + k + 1)) :
    h p c = if p = c then 1 else 0 := by
  by_cases hcr : c.val < r
  · have e : eI k r ⟨c.val, hcr⟩ = c := Fin.ext rfl
    have := (hh.2.1 ⟨c.val, hcr⟩).1
    rw [e] at this
    exact col_of_fix this p
  · have ha : 2 * r + k - c.val < r := by omega
    have e : esI k r ⟨2 * r + k - c.val, ha⟩ = c := by
      apply Fin.ext
      simp only [esI]
      omega
    have := (hh.2.1 ⟨2 * r + k - c.val, ha⟩).2
    rw [e] at this
    exact col_of_fix this p

theorem tau_out (i : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) :
    (tau k r i).val < r ∨ r + k < (tau k r i).val := by
  unfold tau
  simp only
  split_ifs
  omega

theorem uw_block {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    block k r h := by
  refine ⟨fun i j hj => uw_fixed_col hh j hj i, fun i j hi => ?_⟩
  have := row_of_fixed_col hh.1 (tau k r i) (uw_fixed_col hh _ (tau_out i hi)) j
  rw [tau_tau] at this
  exact this

theorem uw_inv {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    h⁻¹ ∈ UWset k r z := by
  have hu := isUnit_of_uh hh.1
  have fix : ∀ v : Fin (2 * r + k + 1) → ℂ, h *ᵥ v = v → h⁻¹ *ᵥ v = v := by
    intro v hv
    conv_lhs => rw [← hv]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  exact ⟨uh_inv hh.1, fun a => ⟨fix _ (hh.2.1 a).1, fix _ (hh.2.1 a).2⟩, fix _ hh.2.2⟩

theorem uw_mul {z : Fin (2 * r + k + 1) → ℂ}
    {h h' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (hh' : h' ∈ UWset k r z) : h * h' ∈ UWset k r z := by
  refine ⟨uh_mul hh.1 hh'.1, fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [← Matrix.mulVec_mulVec, (hh'.2.1 a).1, (hh.2.1 a).1]
  · rw [← Matrix.mulVec_mulVec, (hh'.2.1 a).2, (hh.2.1 a).2]
  · rw [← Matrix.mulVec_mulVec, hh'.2.2, hh.2.2]

theorem mul_apply_of_row {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hrow : ∀ p, h i p = if i = p then 1 else 0) : (h * M) i j = M i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hrow, if_pos rfl, one_mul]
  · intro p _ hp
    rw [hrow, if_neg (Ne.symm hp), zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem mul_apply_of_col {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hcol : ∀ q, h q j = if q = j then 1 else 0) : (M * h) i j = M i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [hcol, if_pos rfl, mul_one]
  · intro q _ hq
    rw [hcol, if_neg hq, mul_zero]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem mulVec_apply_of_row {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1))
    (hrow : ∀ p, h i p = if i = p then 1 else 0) : (h *ᵥ v) i = v i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · rw [hrow, if_pos rfl, one_mul]
  · intro p _ hp
    rw [hrow, if_neg (Ne.symm hp), zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem ell_conj (z : Fin (2 * r + k + 1) → ℂ)
    {h h' g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : block k r h) (hh' : block k r h') (hz : h' *ᵥ z = z) :
    ell k r z (h * g * h') = ell k r z g := by
  unfold ell
  apply Finset.sum_congr rfl
  intro a _
  have hrow : ∀ p, h (eI k r a) p = if eI k r a = p then 1 else 0 :=
    fun p => hh.2 _ p (by simp only [eI]; omega)
  by_cases ha : a.val + 1 < r
  · rw [dif_pos ha, dif_pos ha, mul_apply_of_col _ _ _ (fun q => hh'.1 q _ (by simp only [eI]; omega)),
      mul_apply_of_row _ _ _ hrow]
  · rw [dif_neg ha, dif_neg ha, ← Matrix.mulVec_mulVec, hz, ← Matrix.mulVec_mulVec,
      mulVec_apply_of_row _ _ hrow]

abbrev mid (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k

def midx {i : Fin (2 * r + k + 1)} (hi : mid k r i) : Fin (k + 1) := ⟨i.val - r, by have := hi; omega⟩

lemma wI_midx {i : Fin (2 * r + k + 1)} (hi : mid k r i) : wI k r (midx hi) = i := by
  have := hi
  apply Fin.ext
  simp only [wI, midx]
  omega

lemma mid_wI (m : Fin (k + 1)) : mid k r (wI k r m) := by
  have := m.isLt
  constructor <;> simp only [wI] <;> omega

lemma wI_inj {a b : Fin (k + 1)} (h : wI k r a = wI k r b) : a = b := by
  have := congrArg Fin.val h
  simp only [wI] at this
  apply Fin.ext; omega

lemma emb_out_col (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hj : ¬ mid k r j) :
    embWb k r μ q j = if q = j then 1 else 0 := by
  unfold embWb
  rw [dif_neg (fun h => hj h.2)]
  by_cases h : q = j
  · subst h; rw [if_pos ⟨rfl, hj⟩, if_pos rfl]
  · rw [if_neg (fun h' => h h'.1), if_neg h]

lemma emb_out_row (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hq : ¬ mid k r q) :
    embWb k r μ q j = if q = j then 1 else 0 := by
  unfold embWb
  rw [dif_neg (fun h => hq h.1)]
  by_cases h : q = j
  · rw [if_pos ⟨h, hq⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.1), if_neg h]

lemma emb_mid (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hq : mid k r q) (hj : mid k r j) :
    embWb k r μ q j = μ (midx hq) (midx hj) := by
  unfold embWb
  rw [dif_pos ⟨hq, hj⟩]
  rfl

def Em (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (k + 1)) ℂ := fun i m => if i = wI k r m then 1 else 0

lemma Em_mul_mid {X : Type*} (A : Matrix (Fin (k + 1)) X ℂ) (i : Fin (2 * r + k + 1)) (x : X) (hi : mid k r i) :
    (Em k r * A) i x = A (midx hi) x := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (midx hi)]
  · rw [Em, if_pos (wI_midx hi).symm, one_mul]
  · intro b _ hb
    rw [Em, if_neg, zero_mul]
    intro h
    apply hb
    apply wI_inj (r := r)
    rw [wI_midx hi, h]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma Em_mul_out {X : Type*} (A : Matrix (Fin (k + 1)) X ℂ) (i : Fin (2 * r + k + 1)) (x : X) (hi : ¬ mid k r i) :
    (Em k r * A) i x = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [Em, if_neg, zero_mul]
  intro h
  exact hi (h ▸ mid_wI b)

lemma mul_EmT_mid {X : Type*} [Fintype X] (A : Matrix X (Fin (k + 1)) ℂ) (j : Fin (2 * r + k + 1)) (x : X) (hj : mid k r j) :
    (A * (Em k r)ᵀ) x j = A x (midx hj) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (midx hj)]
  · rw [Matrix.transpose_apply, Em, if_pos (wI_midx hj).symm, mul_one]
  · intro b _ hb
    rw [Matrix.transpose_apply, Em, if_neg, mul_zero]
    intro h
    apply hb
    apply wI_inj (r := r)
    rw [wI_midx hj, h]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma mul_EmT_out {X : Type*} [Fintype X] (A : Matrix X (Fin (k + 1)) ℂ) (j : Fin (2 * r + k + 1)) (x : X) (hj : ¬ mid k r j) :
    (A * (Em k r)ᵀ) x j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [Matrix.transpose_apply, Em, if_neg, mul_zero]
  intro h
  exact hj (h ▸ mid_wI b)

lemma EmT_Em : (Em k r)ᵀ * Em k r = 1 := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (wI k r a)]
  · simp only [Matrix.transpose_apply, Em, if_true, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg (fun h => hab (wI_inj h)), if_neg hab, mul_zero]
  · intro i _ hi
    simp only [Matrix.transpose_apply, Em]
    rw [if_neg hi (c := i = wI k r a), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma emb_eq (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    embWb k r μ = Em k r * μ * (Em k r)ᵀ + (1 - Em k r * (Em k r)ᵀ) := by
  ext i j
  rw [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply]
  by_cases hj : mid k r j
  · rw [mul_EmT_mid _ j i hj, mul_EmT_mid _ j i hj]
    by_cases hi : mid k r i
    · rw [Em_mul_mid _ i _ hi, emb_mid μ i j hi hj]
      have : Em k r i (midx hj) = if i = j then 1 else 0 := by rw [Em, wI_midx hj]
      rw [this, sub_self, add_zero]
    · rw [Em_mul_out _ i _ hi, emb_out_row μ i j hi]
      have : Em k r i (midx hj) = if i = j then 1 else 0 := by rw [Em, wI_midx hj]
      rw [this, sub_self, add_zero, if_neg (fun h => hi (by rw [h]; exact hj))]
  · rw [mul_EmT_out _ j i hj, mul_EmT_out _ j i hj, emb_out_col μ i j hj]
    ring

lemma EmT_Q : (Em k r)ᵀ * (1 - Em k r * (Em k r)ᵀ) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, EmT_Em, Matrix.one_mul, sub_self]

lemma Q_Em : (1 - Em k r * (Em k r)ᵀ) * Em k r = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, EmT_Em, Matrix.mul_one, sub_self]

lemma sandwich (a b N : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (M : Mat k r)
    (h1 : M * Em k r = Em k r * N) (h2 : (Em k r)ᵀ * M = N * (Em k r)ᵀ) :
    embWb k r a * M * embWb k r b =
      Em k r * (a * N * b) * (Em k r)ᵀ + (1 - Em k r * (Em k r)ᵀ) * M * (1 - Em k r * (Em k r)ᵀ) := by
  rw [emb_eq, emb_eq]
  set E := Em k r with hE
  set Q := 1 - E * Eᵀ with hQ
  have t1 : E * a * Eᵀ * M * (E * b * Eᵀ) = E * (a * N * b) * Eᵀ := by
    calc E * a * Eᵀ * M * (E * b * Eᵀ) = E * a * (Eᵀ * M) * E * b * Eᵀ := by simp only [Matrix.mul_assoc]
      _ = E * a * N * (Eᵀ * E) * b * Eᵀ := by rw [h2]; simp only [Matrix.mul_assoc]
      _ = E * (a * N * b) * Eᵀ := by rw [EmT_Em]; simp only [Matrix.mul_assoc, Matrix.one_mul]
  have t2 : E * a * Eᵀ * M * Q = 0 := by
    calc E * a * Eᵀ * M * Q = E * a * (Eᵀ * M) * Q := by simp only [Matrix.mul_assoc]
      _ = E * a * N * (Eᵀ * Q) := by rw [h2]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [EmT_Q, Matrix.mul_zero]
  have t3 : Q * M * (E * b * Eᵀ) = 0 := by
    calc Q * M * (E * b * Eᵀ) = Q * (M * E) * b * Eᵀ := by simp only [Matrix.mul_assoc]
      _ = (Q * E) * N * b * Eᵀ := by rw [h1]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [Q_Em]; simp only [Matrix.zero_mul]
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, t1, t2, t3, add_zero, zero_add]

lemma emb_one : embWb k r 1 = 1 := by
  rw [emb_eq, Matrix.mul_one, add_sub_cancel]

lemma emb_mul (a b : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : embWb k r (a * b) = embWb k r a * embWb k r b := by
  have h := sandwich (r := r) a b 1 1 (by rw [Matrix.one_mul, Matrix.mul_one]) (by rw [Matrix.one_mul, Matrix.mul_one])
  rw [Matrix.mul_one] at h
  rw [h, emb_eq, Matrix.mul_one, Matrix.mul_one]
  congr 1
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, Q_Em, Matrix.zero_mul, sub_zero]

end ReciprocityTheory.ChartRestriction.DS.Mult1.SymA
end
end

section
open Matrix MeasureTheory
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SymA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

lemma Hb_mul_self : Hb k * Hb k = 1 := by
  unfold Hb
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  split_ifs <;> norm_num

lemma unit_of_frame {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (h : γᴴ * Hb k * γ = Hb k) : IsUnit γ.det := by
  apply Matrix.isUnit_det_of_left_inverse (B := Hb k * γᴴ * Hb k)
  calc Hb k * γᴴ * Hb k * γ = Hb k * (γᴴ * Hb k * γ) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, Hb_mul_self]

lemma emb_inv {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hγ : IsUnit γ.det) :
    (embWb k r γ)⁻¹ = embWb k r γ⁻¹ :=
  Matrix.inv_eq_right_inv (by rw [← emb_mul, Matrix.mul_nonsing_inv _ hγ, emb_one])

lemma emb_unit {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hγ : IsUnit γ.det) : IsUnit (embWb k r γ).det :=
  Matrix.isUnit_det_of_right_inverse (B := embWb k r γ⁻¹) (by rw [← emb_mul, Matrix.mul_nonsing_inv _ hγ, emb_one])

section gbar

variable (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hE : IsUnit (embWb k r γ).det)
include hE

lemma gbar_mul (g h : Mat k r) : gbar k r γ (g * h) = gbar k r γ g * gbar k r γ h := by
  unfold gbar
  have e : (embWb k r γ)⁻¹ * (g * h) * embWb k r γ =
      ((embWb k r γ)⁻¹ * g * embWb k r γ) * ((embWb k r γ)⁻¹ * h * embWb k r γ) := by
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hE]
  rw [e, Matrix.map_mul]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hE]

lemma gbar_one : gbar k r γ 1 = 1 := by
  unfold gbar
  rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ hE, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
    Matrix.mul_nonsing_inv _ hE]

lemma gbar_gbar (g : Mat k r) : gbar k r γ (gbar k r γ g) = g := by
  unfold gbar
  have h1 : (embWb k r γ)⁻¹ * (embWb k r γ * ((embWb k r γ)⁻¹ * g * embWb k r γ).map (starRingEnd ℂ) *
      (embWb k r γ)⁻¹) * embWb k r γ = ((embWb k r γ)⁻¹ * g * embWb k r γ).map (starRingEnd ℂ) := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hE, Matrix.nonsing_inv_mul _ hE,
      Matrix.mul_one]
  rw [h1]
  have h2 : (((embWb k r γ)⁻¹ * g * embWb k r γ).map (starRingEnd ℂ)).map (starRingEnd ℂ) =
      (embWb k r γ)⁻¹ * g * embWb k r γ := by
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply, Complex.conj_conj]
  rw [h2]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hE, Matrix.mul_nonsing_inv _ hE,
    Matrix.mul_one]

lemma gbar_mul_inv {x : Mat k r} (hx : IsUnit x.det) : gbar k r γ x * gbar k r γ x⁻¹ = 1 := by
  rw [← gbar_mul γ hE, Matrix.mul_nonsing_inv _ hx, gbar_one γ hE]

lemma gbar_inv {x : Mat k r} (hx : IsUnit x.det) : gbar k r γ x⁻¹ = (gbar k r γ x)⁻¹ :=
  (Matrix.inv_eq_right_inv (gbar_mul_inv γ hE hx)).symm

lemma gbar_unit {x : Mat k r} (hx : IsUnit x.det) : IsUnit (gbar k r γ x).det :=
  Matrix.isUnit_det_of_right_inverse (gbar_mul_inv γ hE hx)

lemma th_five {a b g c d : Mat k r} (ha : IsUnit a.det) (hb : IsUnit b.det) (hg : th k r γ g = g) :
    th k r γ (a⁻¹ * b⁻¹ * g * c * d) =
      (gbar k r γ d)⁻¹ * (gbar k r γ c)⁻¹ * g * gbar k r γ b * gbar k r γ a := by
  unfold th at hg ⊢
  rw [gbar_mul γ hE, gbar_mul γ hE, gbar_mul γ hE, gbar_mul γ hE, gbar_inv γ hE ha, gbar_inv γ hE hb]
  simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (gbar_unit γ hE ha),
    Matrix.nonsing_inv_nonsing_inv _ (gbar_unit γ hE hb), hg, Matrix.mul_assoc]

lemma th_mul_inv {h h' : Mat k r} (hh' : IsUnit h'.det) :
    th k r γ (h * h'⁻¹) = gbar k r γ h' * (gbar k r γ h)⁻¹ := by
  unfold th
  rw [gbar_mul γ hE, gbar_inv γ hE hh', Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (gbar_unit γ hE hh')]

end gbar

lemma psi_conj (z : Fin (2 * r + k + 1) → ℂ) {a : Mat k r} (ha : a ∈ UWset k r z) (c : ℂ) (n : Mat k r) :
    psi k r z c (a * n * a⁻¹) = psi k r z c n := by
  unfold psi
  rw [ell_conj z (uw_block ha) (uw_block (uw_inv ha)) (uw_inv ha).2.2]

lemma tau_wI (j : Fin (k + 1)) : tau k r (wI k r j) = wI k r j := by
  have := j.isLt
  unfold tau wI
  apply Fin.ext
  simp only
  split_ifs with h <;> omega

lemma mud_off (d : ℂ) (x y : Fin (k + 1)) (h : (x ≠ 0 ∧ x ≠ Fin.last k) ∨ (y ≠ 0 ∧ y ≠ Fin.last k)) :
    mud k d x y = if x = y then 1 else 0 := by
  unfold mud
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

lemma emb_mud_off (d : ℂ) (i j : Fin (2 * r + k + 1))
    (h : (i ≠ wI k r 0 ∧ i ≠ wI k r (Fin.last k)) ∨ (j ≠ wI k r 0 ∧ j ≠ wI k r (Fin.last k))) :
    embWb k r (mud k d) i j = if i = j then 1 else 0 := by
  by_cases hi : mid k r i
  · by_cases hj : mid k r j
    · rw [emb_mid _ i j hi hj, mud_off]
      · by_cases e : i = j
        · subst e; simp
        · rw [if_neg e, if_neg (fun h' => e (by rw [← wI_midx hi, ← wI_midx hj, h']))]
      · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left
          exact ⟨fun h' => h1 (by rw [← wI_midx hi, h']), fun h' => h2 (by rw [← wI_midx hi, h'])⟩
        · right
          exact ⟨fun h' => h1 (by rw [← wI_midx hj, h']), fun h' => h2 (by rw [← wI_midx hj, h'])⟩
    · exact emb_out_col _ i j hj
  · exact emb_out_row _ i j hi

lemma comm_mud (hk : 1 ≤ k) {R : Mat k r} (hR : R ∈ UH (Hpk k r))
    (h0 : R *ᵥ bvec (wI k r 0) = bvec (wI k r 0)) (hL : R *ᵥ bvec (wI k r (Fin.last k)) = bvec (wI k r (Fin.last k)))
    (d : ℂ) : R * embWb k r (mud k d) = embWb k r (mud k d) * R := by
  set a := wI k r 0
  set b := wI k r (Fin.last k)
  have hne : a ≠ b := fun h => by
    have := congrArg Fin.val (wI_inj h)
    simp at this
    omega
  have c0 := col_of_fix h0
  have cL := col_of_fix hL
  have r0 : ∀ j, R a j = if a = j then 1 else 0 := by
    intro j
    have := row_of_fixed_col hR a c0 j
    rwa [tau_wI] at this
  have rL : ∀ j, R b j = if b = j then 1 else 0 := by
    intro j
    have := row_of_fixed_col hR b cL j
    rwa [tau_wI] at this
  set P : Mat k r := embWb k r (mud k d) - 1 with hPdef
  have hM : embWb k r (mud k d) = 1 + P := by rw [hPdef]; abel
  have hP : ∀ i j, ((i ≠ a ∧ i ≠ b) ∨ (j ≠ a ∧ j ≠ b)) → P i j = 0 := by
    intro i j h
    rw [hPdef, Matrix.sub_apply, emb_mud_off d i j h, Matrix.one_apply, sub_self]
  have RP : R * P = P := by
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_eq_add a b hne (fun l hl => by rw [hP l j (Or.inl hl), mul_zero]),
      c0, cL]
    by_cases ha : i = a
    · subst ha; rw [if_pos rfl, if_neg hne, one_mul, zero_mul, add_zero]
    · by_cases hb : i = b
      · subst hb; rw [if_neg (Ne.symm hne), if_pos rfl, one_mul, zero_mul, zero_add]
      · rw [if_neg ha, if_neg hb, zero_mul, zero_mul, add_zero, hP i j (Or.inl ⟨ha, hb⟩)]
  have PR : P * R = P := by
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_eq_add a b hne (fun l hl => by rw [hP i l (Or.inr hl), zero_mul]),
      r0, rL]
    by_cases ha : j = a
    · subst ha; rw [if_pos rfl, if_neg (Ne.symm hne), mul_one, mul_zero, add_zero]
    · by_cases hb : j = b
      · subst hb; rw [if_neg hne, if_pos rfl, mul_one, mul_zero, zero_add]
      · rw [if_neg (Ne.symm ha), if_neg (Ne.symm hb), mul_zero, mul_zero, add_zero, hP i j (Or.inr ⟨ha, hb⟩)]
  rw [hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, RP, PR]

lemma big_cell_commute_frame_element (hBCF : BigCellFactor) (hUWb : UWbFacts) (hk : 1 ≤ k) {z : Fin (2 * r + k + 1) → ℂ}
    {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hγ : IsZFrame k r z γ) {u : Mat k r} (hu : u ∈ UUset k r z γ)
    (c : Fin r → ℂ) (d : ℂ) : u * g0 k r γ c d = g0 k r γ c d * u := by
  have hγu := unit_of_frame hγ.1
  have hEu : IsUnit (embWb k r γ).det := emb_unit hγu
  have hEW : embWb k r γ ∈ UWb k r := by rw [(hUWb k r).1]; exact ⟨γ, hγ.1, rfl⟩
  have hEG : embWb k r γ ∈ UH (Hpk k r) := hEW.1
  have huW : u ∈ UWb k r := (hUWb k r).2.1 z hu.1
  set E := embWb k r γ with hEdef
  set R := E⁻¹ * u * E with hRdef
  have hR : R ∈ UH (Hpk k r) := uh_mul (uh_mul (uh_inv hEG) hu.1.1) hEG
  have fixR : ∀ v, E *ᵥ v = v → True := fun _ _ => trivial
  have h0 : R *ᵥ bvec (wI k r 0) = bvec (wI k r 0) := by
    rw [hRdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change E⁻¹ *ᵥ (u *ᵥ w1 k r γ) = _
    rw [hu.2, w1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hEu, Matrix.one_mulVec]
  have hL : R *ᵥ bvec (wI k r (Fin.last k)) = bvec (wI k r (Fin.last k)) := by
    rw [hRdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hγ.2, Matrix.mulVec_smul, hu.1.2.2, ← hγ.2,
      Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hEu, Matrix.one_mulVec]
  have hRM := comm_mud hk hR h0 hL d
  have hu' : u = E * R * E⁻¹ := by
    rw [hRdef]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hEu, Matrix.mul_nonsing_inv _ hEu,
      Matrix.mul_one]
  have key : u * (E * embWb k r (mud k d) * E⁻¹) = E * embWb k r (mud k d) * E⁻¹ * u := by
    rw [hu']
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hEu]
    rw [← Matrix.mul_assoc R, hRM, Matrix.mul_assoc]
  unfold g0
  rw [(hBCF k r c _).1, emb_mul, emb_mul, ← emb_inv hγu]
  have hc := (hUWb k r).2.2 c u huW
  calc u * (bigCell k r c 1 * (E * embWb k r (mud k d) * E⁻¹))
      = bigCell k r c 1 * (u * (E * embWb k r (mud k d) * E⁻¹)) := by rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc]
    _ = bigCell k r c 1 * (E * embWb k r (mud k d) * E⁻¹) * u := by rw [key]; simp only [Matrix.mul_assoc]

end ReciprocityTheory.ChartRestriction.DS.Mult1.SymA
end
end

section
open Matrix MeasureTheory
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SymB

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1 ReciprocityTheory.ChartRestriction.DS.Mult1.SymA

variable {k r : ℕ}

lemma cont_lmul (a : Mat k r) : Continuous (lmulM (k := k) (r := r) a) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
  exact continuous_finsetSum _ fun l _ => continuous_const.mul ((continuous_apply j).comp (continuous_apply l))

def sandM (A B : Mat k r) (x : Mt k r) : Mt k r := A * Matrix.of x * B

lemma cont_sand (A B : Mat k r) : Continuous (sandM (k := k) (r := r) A B) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [sandM, Matrix.mul_apply, Matrix.of_apply]
  exact continuous_finsetSum _ fun m _ => (continuous_finsetSum _ fun l _ =>
    continuous_const.mul ((continuous_apply m).comp (continuous_apply l))).mul continuous_const

def gb (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (x : Mt k r) : Mt k r := fun i j => gbar k r γ (Matrix.of x) i j

lemma cont_gb (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Continuous (gb (k := k) (r := r) γ) := by
  have h1 := cont_sand (k := k) (r := r) (embWb k r γ)⁻¹ (embWb k r γ)
  have h2 : Continuous (fun x : Mt k r => (fun i j => starRingEnd ℂ (sandM (embWb k r γ)⁻¹ (embWb k r γ) x i j) :
      Mt k r)) :=
    continuous_pi fun i => continuous_pi fun j =>
      Complex.continuous_conj.comp ((continuous_apply j).comp ((continuous_apply i).comp h1))
  exact (cont_sand (k := k) (r := r) (embWb k r γ) (embWb k r γ)⁻¹).comp h2

def mEquiv {α : Type*} [MeasurableSpace α] (f g : α → α) (hf : Measurable f) (hg : Measurable g)
    (h1 : Function.LeftInverse g f) (h2 : Function.RightInverse g f) : α ≃ᵐ α :=
  { toFun := f, invFun := g, left_inv := h1, right_inv := h2, measurable_toFun := hf, measurable_invFun := hg }

lemma sfin {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

def Sab (a b : Mat k r) (p : SS k r) : SS k r :=
  ((lmulM a p.1.1, conjM a p.1.2), (lmulM b p.2.1, conjM b p.2.2))

lemma meas_Sab (a b : Mat k r) : Measurable (Sab (k := k) (r := r) a b) :=
  (((cont_lmul a).measurable.comp (measurable_fst.comp measurable_fst)).prodMk
    ((cont_sand a a⁻¹).measurable.comp (measurable_snd.comp measurable_fst))).prodMk
    (((cont_lmul b).measurable.comp (measurable_fst.comp measurable_snd)).prodMk
    ((cont_sand b b⁻¹).measurable.comp (measurable_snd.comp measurable_snd)))

lemma Sab_inv {a b : Mat k r} (ha : IsUnit a.det) (hb : IsUnit b.det) (p : SS k r) :
    Sab a⁻¹ b⁻¹ (Sab a b p) = p := by
  have l : ∀ c : Mat k r, IsUnit c.det → ∀ x : Mt k r, lmulM c⁻¹ (lmulM c x) = x := by
    intro c hc x
    exact Matrix.nonsing_inv_mul_cancel_left (A := c) (Matrix.of x) hc
  have m : ∀ c : Mat k r, IsUnit c.det → ∀ x : Mt k r, conjM c⁻¹ (conjM c x) = x := by
    intro c hc x
    show c⁻¹ * (c * Matrix.of x * c⁻¹) * c⁻¹⁻¹ = Matrix.of x
    rw [Matrix.nonsing_inv_nonsing_inv _ hc]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hc, Matrix.nonsing_inv_mul _ hc,
      Matrix.mul_one]
  simp only [Sab, l a ha, l b hb, m a ha, m b hb]

lemma emb_Sab {a b : Mat k r} (ha : IsUnit a.det) (hb : IsUnit b.det) : MeasurableEmbedding (Sab a b) := by
  have ha' : IsUnit a⁻¹.det := Matrix.isUnit_nonsing_inv_det _ ha
  have hb' : IsUnit b⁻¹.det := Matrix.isUnit_nonsing_inv_det _ hb
  refine (mEquiv (Sab a b) (Sab a⁻¹ b⁻¹) (meas_Sab a b) (meas_Sab _ _) (Sab_inv ha hb) ?_).measurableEmbedding
  intro p
  have := Sab_inv ha' hb' p
  rwa [Matrix.nonsing_inv_nonsing_inv _ ha, Matrix.nonsing_inv_nonsing_inv _ hb] at this

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

lemma mp_Sab (D : RealPlaceData k r Wp Wq) (hCI : ConjInv D) {a b : Mat k r} (ha : a ∈ UWset k r D.z)
    (hb : b ∈ UWset k r D.z') : MeasurePreserving (Sab a b) D.μSS D.μSS := by
  have := sfin D.haarW; have := sfin D.haarN; have := sfin D.haarW'
  have m1 : MeasurePreserving (lmulM a) D.μW D.μW := ⟨(cont_lmul a).measurable, D.haarW.left a ha⟩
  have m2 : MeasurePreserving (conjM a) D.μN D.μN := ⟨(cont_sand a a⁻¹).measurable, hCI a (Or.inl ha)⟩
  have m3 : MeasurePreserving (lmulM b) D.μW' D.μW' := ⟨(cont_lmul b).measurable, D.haarW'.left b hb⟩
  have m4 : MeasurePreserving (conjM b) D.μN D.μN := ⟨(cont_sand b b⁻¹).measurable, hCI b (Or.inr hb)⟩
  exact (m1.prod m2).prod (m3.prod m4)

lemma ae_in (D : RealPlaceData k r Wp Wq) : ∀ᵐ p ∂D.μSS, D.inSS p := by
  have := sfin D.haarW; have := sfin D.haarN; have := sfin D.haarW'
  have hW : ∀ᵐ x ∂D.μW, Matrix.of x ∈ UWset k r D.z := ae_iff.2 (measure_mono_null (fun x hx => hx) D.haarW.conc)
  have hN : ∀ᵐ x ∂D.μN, Matrix.of x ∈ Nset k r := ae_iff.2 (measure_mono_null (fun x hx => hx) D.haarN.conc)
  have hW' : ∀ᵐ x ∂D.μW', Matrix.of x ∈ UWset k r D.z' :=
    ae_iff.2 (measure_mono_null (fun x hx => hx) D.haarW'.conc)
  have A1 : ∀ᵐ p ∂D.μSS, Matrix.of p.1.1 ∈ UWset k r D.z :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae hW)
  have A2 : ∀ᵐ p ∂D.μSS, Matrix.of p.1.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae hN)
  have A3 : ∀ᵐ p ∂D.μSS, Matrix.of p.2.1 ∈ UWset k r D.z' :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_fst.ae hW')
  have A4 : ∀ᵐ p ∂D.μSS, Matrix.of p.2.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae hN)
  filter_upwards [A1, A2, A3, A4] with p h1 h2 h3 h4 using ⟨h1, h2, h3, h4⟩

section lie

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def piLIE (z : Fin (2 * r + k + 1) → ℂ) (π : Mat k r → (V →L[ℂ] V)) (hrep : IsCRepOn (UWset k r z) π)
    (hu : ∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) (a : Mat k r) (ha : a ∈ UWset k r z) : V ≃ₗᵢ[ℂ] V where
  toLinearEquiv := LinearEquiv.ofLinear (π a).toLinearMap (π a⁻¹).toLinearMap
    (LinearMap.ext fun v => by
      change ((π a).comp (π a⁻¹)) v = v
      rw [← hrep.2 a ha _ (uw_inv ha), Matrix.mul_nonsing_inv _ (isUnit_of_uh ha.1), hrep.1]
      rfl)
    (LinearMap.ext fun v => by
      change ((π a⁻¹).comp (π a)) v = v
      rw [← hrep.2 _ (uw_inv ha) a ha, Matrix.nonsing_inv_mul _ (isUnit_of_uh ha.1), hrep.1]
      rfl)
  norm_map' := hu a ha

end lie

def ph (D : RealPlaceData k r Wp Wq) (p : SS k r) : ℂ :=
  psi k r D.z cStd (Matrix.of p.1.2) * star (psi k r D.z' cStd (Matrix.of p.2.2))

lemma JF_eq (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    JF D F g = ∫ p, ph D p • rho D p F g ∂D.μSS := rfl

lemma ph_Sab (D : RealPlaceData k r Wp Wq) {a b : Mat k r} (ha : a ∈ UWset k r D.z) (hb : b ∈ UWset k r D.z')
    (p : SS k r) : ph D (Sab a b p) = ph D p := by
  show psi k r D.z cStd (a * Matrix.of p.1.2 * a⁻¹) * star (psi k r D.z' cStd (b * Matrix.of p.2.2 * b⁻¹)) = _
  rw [psi_conj _ ha, psi_conj _ hb]
  rfl

lemma sgs_Sab {a b : Mat k r} (ha : IsUnit a.det) (hb : IsUnit b.det) (p : SS k r) (g : Mat k r) :
    sgs (Sab a b p) g = sgs p (a⁻¹ * g * b) := by
  show (a * Matrix.of p.1.1)⁻¹ * (a * Matrix.of p.1.2 * a⁻¹)⁻¹ * g * (b * Matrix.of p.2.2 * b⁻¹) *
      (b * Matrix.of p.2.1) = (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (a⁻¹ * g * b) * Matrix.of p.2.2 *
      Matrix.of p.2.1
  simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ ha, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul_cancel_left _ _ ha, Matrix.nonsing_inv_mul_cancel_left _ _ hb]

lemma rho_Sab (D : RealPlaceData k r Wp Wq) {a b : Mat k r} (ha : a ∈ UWset k r D.z) (hb : b ∈ UWset k r D.z')
    {p : SS k r} (hp : D.inSS p) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    rho D (Sab a b p) F g = (D.π a).comp ((rho D p F (a⁻¹ * g * b)).comp (D.π' b⁻¹)) := by
  show (D.π (a * Matrix.of p.1.1)).comp ((F (sgs (Sab a b p) g)).comp (D.π' (b * Matrix.of p.2.1)⁻¹)) = _
  rw [sgs_Sab (isUnit_of_uh ha.1) (isUnit_of_uh hb.1), D.π_rep.2 a ha _ hp.1, Matrix.mul_inv_rev,
    D.π'_rep.2 _ (uw_inv hp.2.2.1) _ (uw_inv hb)]
  simp only [rho, ContinuousLinearMap.comp_assoc]

def Lab (D : RealPlaceData k r Wp Wq) {a b : Mat k r} (ha : a ∈ UWset k r D.z) (hb : b ∈ UWset k r D.z') :
    (Wq →L[ℂ] Wp) ≃L[ℂ] (Wq →L[ℂ] Wp) :=
  ContinuousLinearEquiv.arrowCongr (piLIE D.z' D.π' D.π'_rep D.π'_unitary b hb).toContinuousLinearEquiv
    (piLIE D.z D.π D.π_rep D.π_unitary a ha).toContinuousLinearEquiv

lemma Lab_apply (D : RealPlaceData k r Wp Wq) {a b : Mat k r} (ha : a ∈ UWset k r D.z) (hb : b ∈ UWset k r D.z')
    (X : Wq →L[ℂ] Wp) : Lab D ha hb X = (D.π a).comp (X.comp (D.π' b⁻¹)) :=
  ContinuousLinearMap.ext fun _ => rfl

lemma norm_Lab (D : RealPlaceData k r Wp Wq) {a b : Mat k r} (ha : a ∈ UWset k r D.z) (hb : b ∈ UWset k r D.z')
    (X : Wq →L[ℂ] Wp) : ‖Lab D ha hb X‖ = ‖X‖ := by
  have e : Lab D ha hb X = ((piLIE D.z D.π D.π_rep D.π_unitary a ha : Wp ≃ₗᵢ[ℂ] Wp) : Wp →L[ℂ] Wp).comp
      (X.comp ((piLIE D.z' D.π' D.π'_rep D.π'_unitary b hb).symm : Wq →L[ℂ] Wq)) :=
    ContinuousLinearMap.ext fun _ => rfl
  rw [e, ContinuousLinearMap.opNorm_linearIsometryEquiv_comp, ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

lemma J_equiv (D : RealPlaceData k r Wp Wq) (hCI : ConjInv D) {a b : Mat k r} (ha : a ∈ UWset k r D.z)
    (hb : b ∈ UWset k r D.z') (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    JF D F g = Lab D ha hb (JF D F (a⁻¹ * g * b)) := by
  rw [JF_eq, JF_eq, ← (mp_Sab D hCI ha hb).integral_comp (emb_Sab (isUnit_of_uh ha.1) (isUnit_of_uh hb.1)),
    ← ContinuousLinearEquiv.integral_comp_comm]
  refine integral_congr_ae ?_
  filter_upwards [ae_in D] with p hp
  rw [ph_Sab D ha hb, rho_Sab D ha hb hp, map_smul, Lab_apply]

lemma E_equiv (D : RealPlaceData k r Wp Wq) (hCI : ConjInv D) {a b : Mat k r} (ha : a ∈ UWset k r D.z)
    (hb : b ∈ UWset k r D.z') (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    ∫⁻ p, ‖rho D p F g‖ₑ ∂D.μSS = ∫⁻ p, ‖rho D p F (a⁻¹ * g * b)‖ₑ ∂D.μSS := by
  rw [← (mp_Sab D hCI ha hb).lintegral_comp_emb (emb_Sab (isUnit_of_uh ha.1) (isUnit_of_uh hb.1))]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_in D] with p hp
  have h := norm_Lab D ha hb (rho D p F (a⁻¹ * g * b))
  rw [Lab_apply] at h
  rw [rho_Sab D ha hb hp, enorm_eq_nnnorm, enorm_eq_nnnorm,
    show ‖(D.π a).comp ((rho D p F (a⁻¹ * g * b)).comp (D.π' b⁻¹))‖₊ = ‖rho D p F (a⁻¹ * g * b)‖₊ from NNReal.eq h]

end ReciprocityTheory.ChartRestriction.DS.Mult1.SymB
end
end

section
open Matrix MeasureTheory
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SymC

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1 ReciprocityTheory.ChartRestriction.DS.Mult1.SymA
  ReciprocityTheory.ChartRestriction.DS.Mult1.SymB

variable {k r : ℕ}

def Tg (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (p : SS k r) : SS k r :=
  ((gb γ p.2.1, gb γ p.2.2), (gb γ p.1.1, gb γ p.1.2))

lemma Tg_Tg (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hE : IsUnit (embWb k r γ).det) (p : SS k r) :
    Tg γ (Tg γ p) = p := by
  have e : ∀ x : Mt k r, gb γ (gb γ x) = x := fun x => gbar_gbar γ hE (Matrix.of x)
  simp only [Tg, e]

lemma meas_Tg (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Measurable (Tg (k := k) (r := r) γ) :=
  (((cont_gb γ).measurable.comp (measurable_fst.comp measurable_snd)).prodMk
    ((cont_gb γ).measurable.comp (measurable_snd.comp measurable_snd))).prodMk
    (((cont_gb γ).measurable.comp (measurable_fst.comp measurable_fst)).prodMk
    ((cont_gb γ).measurable.comp (measurable_snd.comp measurable_fst)))

lemma emb_Tg (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hE : IsUnit (embWb k r γ).det) :
    MeasurableEmbedding (Tg (k := k) (r := r) γ) :=
  (mEquiv (Tg γ) (Tg γ) (meas_Tg γ) (meas_Tg γ) (Tg_Tg γ hE) (Tg_Tg γ hE)).measurableEmbedding

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

lemma mp_Tg (D : RealPlaceData k r Wp Wp) (hW' : D.μW' = D.μW) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hgW : D.μW.map (gb γ) = D.μW) (hgN : D.μN.map (gb γ) = D.μN) : MeasurePreserving (Tg γ) D.μSS D.μSS := by
  have := sfin D.haarW
  have := sfin D.haarN
  have m1 : MeasurePreserving (gb γ) D.μW D.μW := ⟨(cont_gb γ).measurable, hgW⟩
  have m2 : MeasurePreserving (gb γ) D.μN D.μN := ⟨(cont_gb γ).measurable, hgN⟩
  have m12 := m1.prod m2
  have m := (Measure.measurePreserving_swap (μ := D.μW.prod D.μN) (ν := D.μW.prod D.μN)).comp (m12.prod m12)
  unfold RealPlaceData.μSS
  rw [hW']
  exact m

lemma psi_gbar (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {z : Fin (2 * r + k + 1) → ℂ} {m : Mat k r}
    (hl : lam k r z (gbar k r γ m) = -lam k r z m) :
    psi k r z cStd (gbar k r γ m) = star (psi k r z cStd m) := by
  show Complex.exp (Complex.I * ((lam k r z (gbar k r γ m) : ℝ) : ℂ)) =
    (starRingEnd ℂ) (Complex.exp (Complex.I * ((lam k r z m : ℝ) : ℂ)))
  rw [hl, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  congr 1
  ring

lemma rho_scalF (D : RealPlaceData k r Wp Wp) (p : SS k r) (f : Mat k r → ℂ) (g : Mat k r) :
    rho D p (scalF Wp f) g = f (sgs p g) • (D.π (Matrix.of p.1.1)).comp (D.π' (Matrix.of p.2.1)⁻¹) := by
  ext v
  simp [rho, scalF]

def Phi (D : RealPlaceData k r Wp Wp) (f : Mat k r → ℂ) (g : Mat k r) (p : SS k r) : Wp →L[ℂ] Wp :=
  ph D p • (f (sgs p g) • (D.π (Matrix.of p.1.1)).comp (D.π (Matrix.of p.2.1)⁻¹))

def Psi (D : RealPlaceData k r Wp Wp) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (f : Mat k r → ℂ) (g : Mat k r)
    (p : SS k r) : Wp →L[ℂ] Wp :=
  ph D p • (f (sgs p g) • (D.π (gbar k r γ (Matrix.of p.2.1))).comp (D.π (gbar k r γ (Matrix.of p.1.1))⁻¹))

lemma J_phi (D : RealPlaceData k r Wp Wp) (hD : IsDiag D) (f : Mat k r → ℂ) (g : Mat k r) :
    JF D (scalF Wp f) g = ∫ p, Phi D f g p ∂D.μSS := by
  rw [JF_eq]
  congr 1
  funext p
  rw [rho_scalF, hD.π_eq]
  rfl

lemma J_th (D : RealPlaceData k r Wp Wp) (hD : IsDiag D) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hE : IsUnit (embWb k r γ).det) (hgW : D.μW.map (gb γ) = D.μW) (hgN : D.μN.map (gb γ) = D.μN)
    (hlam : ∀ m ∈ Nset k r, lam k r D.z (gbar k r γ m) = -lam k r D.z m)
    {g0 : Mat k r} (hg0 : th k r γ g0 = g0) (f : Mat k r → ℂ) :
    JF D (scalF Wp (f ∘ th k r γ)) g0 = ∫ p, Psi D γ f g0 p ∂D.μSS := by
  rw [JF_eq, ← (mp_Tg D hD.μW_eq γ hgW hgN).integral_comp (emb_Tg γ hE)]
  refine integral_congr_ae ?_
  filter_upwards [ae_in D] with p hp
  have e3 : th k r γ (sgs (Tg γ p) g0) = sgs p g0 := by
    rw [show sgs (Tg γ p) g0 = (gbar k r γ (Matrix.of p.2.1))⁻¹ * (gbar k r γ (Matrix.of p.2.2))⁻¹ * g0 *
        gbar k r γ (Matrix.of p.1.2) * gbar k r γ (Matrix.of p.1.1) from rfl,
      th_five γ hE (gbar_unit γ hE (isUnit_of_uh hp.2.2.1.1)) (gbar_unit γ hE (isUnit_of_uh hp.2.2.2.1)) hg0,
      gbar_gbar γ hE, gbar_gbar γ hE, gbar_gbar γ hE, gbar_gbar γ hE]
    rfl
  have e4 : ph D (Tg γ p) = ph D p := by
    unfold ph
    rw [hD.z_eq]
    show psi k r D.z cStd (gbar k r γ (Matrix.of p.2.2)) * star (psi k r D.z cStd (gbar k r γ (Matrix.of p.1.2))) = _
    rw [psi_gbar γ (hlam _ hp.2.2.2), psi_gbar γ (hlam _ hp.2.1), star_star, mul_comm]
  have e5 : D.π' = D.π := hD.π_eq
  rw [rho_scalF, Function.comp_apply, e3, e4, e5]
  rfl

section trace

variable [FiniteDimensional ℂ Wp]

def trL (Y : Wp →L[ℂ] Wp) : (Wp →L[ℂ] Wp) →ₗ[ℂ] ℂ where
  toFun X := LinearMap.trace ℂ Wp (((ContinuousLinearMap.adjoint Y).comp X : Wp →L[ℂ] Wp) : Wp →ₗ[ℂ] Wp)
  map_add' X X' := by simp [ContinuousLinearMap.comp_add]
  map_smul' c X := by simp

def trY (Y : Wp →L[ℂ] Wp) : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (trL Y)

lemma trY_apply (Y X : Wp →L[ℂ] Wp) :
    trY Y X = LinearMap.trace ℂ Wp (((ContinuousLinearMap.adjoint Y).comp X : Wp →L[ℂ] Wp) : Wp →ₗ[ℂ] Wp) :=
  rfl

lemma trY_self {Y : Wp →L[ℂ] Wp} (h : trY Y Y = 0) : Y = 0 := by
  set b := stdOrthonormalBasis ℂ Wp
  rw [trY_apply, LinearMap.trace_eq_sum_inner _ b] at h
  have h' : ∀ i, ⟪b i, (((ContinuousLinearMap.adjoint Y).comp Y : Wp →L[ℂ] Wp) : Wp →ₗ[ℂ] Wp) (b i)⟫_ℂ =
      ((‖Y (b i)‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  simp only [h'] at h
  rw [← Complex.ofReal_sum, Complex.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)] at h
  have hb : ∀ i, Y (b i) = 0 := fun i => by
    have := h i (Finset.mem_univ _)
    simpa using this
  apply ContinuousLinearMap.coe_injective
  refine b.toBasis.ext (fun i => ?_)
  simp [hb i]

lemma trY_conj (Y X : Wp →L[ℂ] Wp) (e : Wp ≃ₗᵢ[ℂ] Wp)
    (h2 : Y.comp (e.symm : Wp →L[ℂ] Wp) = (e.symm : Wp →L[ℂ] Wp).comp Y) :
    trY Y ((e : Wp →L[ℂ] Wp).comp (X.comp (e.symm : Wp →L[ℂ] Wp))) = trY Y X := by
  have c : (e : Wp →L[ℂ] Wp).comp (ContinuousLinearMap.adjoint Y) =
      (ContinuousLinearMap.adjoint Y).comp (e : Wp →L[ℂ] Wp) := by
    have := congrArg ContinuousLinearMap.adjoint h2
    rwa [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, e.symm.adjoint_eq_symm,
      LinearIsometryEquiv.symm_symm] at this
  have e1 : (ContinuousLinearMap.adjoint Y).comp ((e : Wp →L[ℂ] Wp).comp (X.comp (e.symm : Wp →L[ℂ] Wp))) =
      (e : Wp →L[ℂ] Wp).comp (((ContinuousLinearMap.adjoint Y).comp X).comp (e.symm : Wp →L[ℂ] Wp)) := by
    rw [← ContinuousLinearMap.comp_assoc, ← c]
    simp only [ContinuousLinearMap.comp_assoc]
  have e2 : ((((ContinuousLinearMap.adjoint Y).comp X).comp (e.symm : Wp →L[ℂ] Wp)).comp (e : Wp →L[ℂ] Wp)) =
      (ContinuousLinearMap.adjoint Y).comp X := by
    ext v
    simp
  have tc : ∀ A B : Wp →L[ℂ] Wp, LinearMap.trace ℂ Wp ((A.comp B : Wp →L[ℂ] Wp) : Wp →ₗ[ℂ] Wp) =
      LinearMap.trace ℂ Wp ((B.comp A : Wp →L[ℂ] Wp) : Wp →ₗ[ℂ] Wp) := fun A B =>
    LinearMap.trace_mul_comm (R := ℂ) (M := Wp) (A : Wp →ₗ[ℂ] Wp) (B : Wp →ₗ[ℂ] Wp)
  rw [trY_apply, trY_apply, e1, tc, e2]

end trace

end ReciprocityTheory.ChartRestriction.DS.Mult1.SymC

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SymD

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1 ReciprocityTheory.ChartRestriction.DS.Mult1.SymA
  ReciprocityTheory.ChartRestriction.DS.Mult1.SymB ReciprocityTheory.ChartRestriction.DS.Mult1.SymC

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

lemma pi_eq (D : RealPlaceData k r Wp Wp) {h : Mat k r} (hh : h ∈ UWset k r D.z) :
    D.π h = ((piLIE D.z D.π D.π_rep D.π_unitary h hh : Wp ≃ₗᵢ[ℂ] Wp) : Wp →L[ℂ] Wp) :=
  ContinuousLinearMap.ext fun _ => rfl

lemma pi_inv_eq (D : RealPlaceData k r Wp Wp) {h : Mat k r} (hh : h ∈ UWset k r D.z) :
    D.π h⁻¹ = (((piLIE D.z D.π D.π_rep D.π_unitary h hh).symm : Wp ≃ₗᵢ[ℂ] Wp) : Wp →L[ℂ] Wp) :=
  ContinuousLinearMap.ext fun _ => rfl

lemma adj_pi (D : RealPlaceData k r Wp Wp) {h : Mat k r} (hh : h ∈ UWset k r D.z) :
    ContinuousLinearMap.adjoint (D.π h) = D.π h⁻¹ := by
  rw [pi_eq D hh, LinearIsometryEquiv.adjoint_eq_symm, ← pi_inv_eq D hh]

lemma norm_pi_le (D : RealPlaceData k r Wp Wp) {h : Mat k r} (hh : h ∈ UWset k r D.z) : ‖D.π h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [D.π_unitary h hh v, one_mul]

lemma pi_inv_apply (D : RealPlaceData k r Wp Wp) {h : Mat k r} (hh : h ∈ UWset k r D.z) (v : Wp) :
    D.π h⁻¹ (D.π h v) = v :=
  (piLIE D.z D.π D.π_rep D.π_unitary h hh).symm_apply_apply v

lemma pi_apply_inv (D : RealPlaceData k r Wp Wp) {h : Mat k r} (hh : h ∈ UWset k r D.z) (v : Wp) :
    D.π h (D.π h⁻¹ v) = v :=
  (piLIE D.z D.π D.π_rep D.π_unitary h hh).apply_symm_apply v

lemma norm_ph (D : RealPlaceData k r Wp Wp) (p : SS k r) : ‖ph D p‖ = 1 := by
  have e : ∀ (z : Fin (2 * r + k + 1) → ℂ) (m : Mat k r), ‖psi k r z cStd m‖ = 1 := fun z m => by
    unfold psi
    rw [Complex.norm_exp]
    simp
  unfold ph
  rw [norm_mul, norm_star, e, e, one_mul]

lemma aesm_comp {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → (Wp →L[ℂ] Wp)}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun a => (f a).comp (g a)) μ :=
  (isBoundedBilinearMap_comp (𝕜 := ℂ) (E := Wp) (F := Wp) (G := Wp)).continuous.comp_aestronglyMeasurable
    (hf.prodMk hg)

lemma aesm_adj {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → (Wp →L[ℂ] Wp)}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun a => ContinuousLinearMap.adjoint (f a)) μ :=
  (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Wp) (F := Wp)).continuous.comp_aestronglyMeasurable hf

def Cf (D : RealPlaceData k r Wp Wp) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (p : SS k r) : Wp →L[ℂ] Wp :=
  (D.π (Matrix.of p.2.1)).comp ((ContinuousLinearMap.adjoint (D.π (Matrix.of p.1.1))).comp
    ((D.π (gbar k r γ (Matrix.of p.2.1))).comp (ContinuousLinearMap.adjoint (D.π (gbar k r γ (Matrix.of p.1.1))))))

def Cb (D : RealPlaceData k r Wp Wp) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (p : SS k r) : Wp →L[ℂ] Wp :=
  (D.π (gbar k r γ (Matrix.of p.1.1))).comp ((ContinuousLinearMap.adjoint (D.π (gbar k r γ (Matrix.of p.2.1)))).comp
    ((D.π (Matrix.of p.1.1)).comp (ContinuousLinearMap.adjoint (D.π (Matrix.of p.2.1)))))

lemma norm_C_le (D : RealPlaceData k r Wp Wp) {a b c d : Mat k r} (ha : a ∈ UWset k r D.z) (hb : b ∈ UWset k r D.z)
    (hc : c ∈ UWset k r D.z) (hd : d ∈ UWset k r D.z) :
    ‖(D.π a).comp ((ContinuousLinearMap.adjoint (D.π b)).comp ((D.π c).comp (ContinuousLinearMap.adjoint (D.π d))))‖
      ≤ 1 := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine mul_le_one₀ (norm_pi_le D ha) (norm_nonneg _) ((ContinuousLinearMap.opNorm_comp_le _ _).trans ?_)
  rw [LinearIsometryEquiv.norm_map]
  refine mul_le_one₀ (norm_pi_le D hb) (norm_nonneg _) ((ContinuousLinearMap.opNorm_comp_le _ _).trans ?_)
  rw [LinearIsometryEquiv.norm_map]
  exact mul_le_one₀ (norm_pi_le D hc) (norm_nonneg _) (norm_pi_le D hd)

lemma aesm_pi (D : RealPlaceData k r Wp Wp) (hclW : IsClosed (UWset k r D.z)) :
    AEStronglyMeasurable (fun x : Mt k r => D.π (Matrix.of x)) D.μW := by
  have hof : Continuous (⇑(Matrix.of : Mt k r ≃ Mat k r)) := by exact continuous_id
  have h : ContinuousOn (fun x : Mt k r => D.π (Matrix.of x)) (Matrix.of ⁻¹' UWset k r D.z) :=
    D.π_cont.comp hof.continuousOn (Set.mapsTo_preimage _ _)
  have h2 := h.aestronglyMeasurable (μ := D.μW) (hclW.preimage hof).measurableSet
  have hae : ∀ᵐ x ∂D.μW, x ∈ (Matrix.of ⁻¹' UWset k r D.z : Set (Mt k r)) :=
    ae_iff.2 (measure_mono_null (fun x hx => hx) D.haarW.conc)
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at h2

variable (D : RealPlaceData k r Wp Wp) (hD : IsDiag D) (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
  (hWbar : ∀ h ∈ UWset k r D.z, gbar k r γ h ∈ UWset k r D.z)
include hD hWbar

lemma psi_eq_C {p : SS k r} (hp : D.inSS p) (f : Mat k r → ℂ) (g : Mat k r) :
    Psi D γ f g p = (Phi D f g p).comp (Cf D γ p) ∧ Phi D f g p = (Psi D γ f g p).comp (Cb D γ p) ∧
      ‖Cf D γ p‖ ≤ 1 ∧ ‖Cb D γ p‖ ≤ 1 := by
  have hh := hp.1
  have hh' : Matrix.of p.2.1 ∈ UWset k r D.z := hD.z_eq ▸ hp.2.2.1
  have g1 := hWbar _ hh
  have g2 := hWbar _ hh'
  refine ⟨?_, ?_, norm_C_le D hh' hh g2 g1, norm_C_le D g1 g2 hh hh'⟩
  · ext v
    simp only [Phi, Psi, Cf, adj_pi D hh, adj_pi D g1, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_comp, _root_.smul_apply, pi_inv_apply D hh', pi_apply_inv D hh]
  · ext v
    simp only [Phi, Psi, Cb, adj_pi D hh', adj_pi D g2, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_comp, _root_.smul_apply, pi_inv_apply D g1, pi_apply_inv D g2]

omit hWbar in
lemma aesm_C (hclW : IsClosed (UWset k r D.z)) (hgW : D.μW.map (gb γ) = D.μW) :
    AEStronglyMeasurable (Cf D γ) D.μSS ∧ AEStronglyMeasurable (Cb D γ) D.μSS := by
  have := sfin D.haarW
  have := sfin D.haarN
  have hb := aesm_pi D hclW
  have hbg : AEStronglyMeasurable (fun x : Mt k r => D.π (gbar k r γ (Matrix.of x))) D.μW :=
    hb.comp_quasiMeasurePreserving (μ := D.μW) (f := gb γ)
      (MeasurePreserving.quasiMeasurePreserving ⟨(cont_gb γ).measurable, hgW⟩)
  have hSS : D.μSS = (D.μW.prod D.μN).prod (D.μW.prod D.μN) := by rw [RealPlaceData.μSS, hD.μW_eq]
  have q1 : Measure.QuasiMeasurePreserving (fun p : SS k r => p.1.1) D.μSS D.μW := by
    rw [hSS]; exact Measure.quasiMeasurePreserving_fst.comp Measure.quasiMeasurePreserving_fst
  have q2 : Measure.QuasiMeasurePreserving (fun p : SS k r => p.2.1) D.μSS D.μW := by
    rw [hSS]; exact Measure.quasiMeasurePreserving_fst.comp Measure.quasiMeasurePreserving_snd
  have a1 := hb.comp_quasiMeasurePreserving q1
  have a2 := hb.comp_quasiMeasurePreserving q2
  have a3 := hbg.comp_quasiMeasurePreserving q1
  have a4 := hbg.comp_quasiMeasurePreserving q2
  exact ⟨aesm_comp a2 (aesm_comp (aesm_adj a1) (aesm_comp a4 (aesm_adj a3))),
    aesm_comp a3 (aesm_comp (aesm_adj a4) (aesm_comp a1 (aesm_adj a2)))⟩

end ReciprocityTheory.ChartRestriction.DS.Mult1.SymD
end
end

section
open Matrix MeasureTheory
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SymE

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1 ReciprocityTheory.ChartRestriction.DS.Mult1.SymA
  ReciprocityTheory.ChartRestriction.DS.Mult1.SymB ReciprocityTheory.ChartRestriction.DS.Mult1.SymC ReciprocityTheory.ChartRestriction.DS.Mult1.SymD

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

private theorem hpk_sq_lemma : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hi := i.isLt
  have hj := j.isLt
  let l : Fin (2 * r + k + 1) :=
    ⟨if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val, by split_ifs <;> omega⟩
  rw [Finset.sum_eq_single l]
  · simp only [Hpk, l, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | (exfalso; omega) | norm_num
  · intro b _ hb
    have hb' : b.val ≠ l.val := fun h => hb (Fin.ext h)
    simp only [l, Fin.val_mk] at hb'
    have hbl := b.isLt
    apply mul_eq_zero_of_left
    simp only [Hpk, Fin.ext_iff]
    split_ifs at hb' ⊢ <;> first | (exfalso; omega) | rfl
  · intro h
    exact absurd (Finset.mem_univ l) h

lemma uu_inv {z : Fin (2 * r + k + 1) → ℂ} {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} {u : Mat k r}
    (hu : u ∈ UUset k r z γ) : u⁻¹ ∈ UUset k r z γ := by
  simp only [UUset, UWset, UH, Set.mem_setOf_eq] at hu ⊢
  obtain ⟨⟨hH, hb, hz⟩, hw⟩ := hu
  have hdH : (Hpk k r).det ≠ 0 := by
    have h := congrArg Matrix.det (hpk_sq_lemma (k := k) (r := r))
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact left_ne_zero_of_mul_eq_one h
  have hdu : IsUnit u.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have h := congrArg Matrix.det hH
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h
    exact hdH h.symm
  have h1 : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul u hdu
  have h3 : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv u hdu
  have h2 : (u⁻¹)ᴴ * uᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h3, Matrix.conjTranspose_one]
  have fix : ∀ v, u *ᵥ v = v → u⁻¹ *ᵥ v = v := fun v hv => by
    conv_lhs => rw [← hv]
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  refine ⟨⟨?_, fun a => ⟨fix _ (hb a).1, fix _ (hb a).2⟩, fix _ hz⟩, fix _ hw⟩
  calc (u⁻¹)ᴴ * Hpk k r * u⁻¹ = (u⁻¹)ᴴ * (uᴴ * Hpk k r * u) * u⁻¹ := by rw [hH]
    _ = ((u⁻¹)ᴴ * uᴴ) * Hpk k r * (u * u⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h2, h3, Matrix.one_mul, Matrix.mul_one]

theorem core (D : RealPlaceData k r Wp Wp) (hD : IsDiag D) (hCI : ConjInv D) (hclW : IsClosed (UWset k r D.z))
    (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hE : IsUnit (embWb k r γ).det)
    (hgW : D.μW.map (gb γ) = D.μW) (hgN : D.μN.map (gb γ) = D.μN)
    (hlam : ∀ m ∈ Nset k r, lam k r D.z (gbar k r γ m) = -lam k r D.z m)
    (hWbar : ∀ h ∈ UWset k r D.z, gbar k r γ h ∈ UWset k r D.z)
    (hT6 : ∀ y ∈ UWset k r D.z, ∃ u₀ ∈ UUset k r D.z γ, th k r γ y = u₀ * y * u₀⁻¹)
    {g0 : Mat k r} (hg0 : th k r γ g0 = g0) (hcomm : ∀ u ∈ UUset k r D.z γ, u * g0 = g0 * u)
    (f : Mat k r → ℂ) (hEf : ∫⁻ p, ‖rho D p (scalF Wp f) g0‖ₑ ∂D.μSS ≠ ∞) :
    JF D (scalF Wp (f ∘ th k r γ)) g0 = JF D (scalF Wp f) g0 := by
  have hz : D.z' = D.z := hD.z_eq
  have hπ : D.π' = D.π := hD.π_eq
  have Bc : ∀ F : Mat k r → (Wp →L[ℂ] Wp), ∀ u ∈ UUset k r D.z γ,
      (JF D F g0).comp (D.π u) = (D.π u).comp (JF D F g0) := by
    intro F u hu
    have hu' : u ∈ UWset k r D.z' := hz ▸ hu.1
    have e := J_equiv D hCI hu.1 hu' F g0
    have eg : u⁻¹ * g0 * u = g0 := by
      rw [Matrix.mul_assoc, ← hcomm u hu, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_of_uh hu.1.1),
        Matrix.one_mul]
    rw [eg, Lab_apply, hπ] at e
    conv_lhs => rw [e]
    ext v
    simp only [ContinuousLinearMap.comp_apply, pi_inv_apply D hu.1]
  have hB : JF D (scalF Wp f) g0 = ∫ p, Phi D f g0 p ∂D.μSS := J_phi D hD f g0
  have hB' : JF D (scalF Wp (f ∘ th k r γ)) g0 = ∫ p, Psi D γ f g0 p ∂D.μSS :=
    J_th D hD γ hE hgW hgN hlam hg0 f
  have hC := aesm_C D hD γ hclW hgW
  have hPC : ∀ᵐ p ∂D.μSS, Psi D γ f g0 p = (Phi D f g0 p).comp (Cf D γ p) ∧
      Phi D f g0 p = (Psi D γ f g0 p).comp (Cb D γ p) ∧ ‖Cf D γ p‖ ≤ 1 ∧ ‖Cb D γ p‖ ≤ 1 := by
    filter_upwards [ae_in D] with p hp using psi_eq_C D hD γ hWbar hp f g0
  by_cases hm : AEStronglyMeasurable (Phi D f g0) D.μSS
  swap
  · have hm' : ¬ AEStronglyMeasurable (Psi D γ f g0) D.μSS := fun h =>
      hm ((aesm_comp h hC.2).congr (hPC.mono fun p hp => hp.2.1.symm))
    rw [hB, hB', integral_non_aestronglyMeasurable hm, integral_non_aestronglyMeasurable hm']
  have hPhiI : Integrable (Phi D f g0) D.μSS := by
    refine ⟨hm, hasFiniteIntegral_iff_enorm.2 ?_⟩
    have e : ∀ p, ‖Phi D f g0 p‖ₑ = ‖rho D p (scalF Wp f) g0‖ₑ := fun p => by
      have h1 : ‖ph D p‖ₑ = 1 := by
        rw [enorm_eq_nnnorm, show ‖ph D p‖₊ = 1 from NNReal.eq (by rw [coe_nnnorm, NNReal.coe_one]; exact norm_ph D p),
          ENNReal.coe_one]
      rw [show Phi D f g0 p = ph D p • rho D p (scalF Wp f) g0 by rw [rho_scalF, hπ]; rfl, enorm_smul, h1, one_mul]
    calc ∫⁻ p, ‖Phi D f g0 p‖ₑ ∂D.μSS = ∫⁻ p, ‖rho D p (scalF Wp f) g0‖ₑ ∂D.μSS := lintegral_congr e
      _ < ∞ := hEf.lt_top
  have hPsiM : AEStronglyMeasurable (Psi D γ f g0) D.μSS :=
    (aesm_comp hm hC.1).congr (hPC.mono fun p hp => hp.1.symm)
  have hPsiI : Integrable (Psi D γ f g0) D.μSS := by
    refine hPhiI.norm.mono' hPsiM (hPC.mono fun p hp => ?_)
    rw [hp.1]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hp.2.2.1)
  obtain ⟨Y, hY⟩ : ∃ Y, Y = JF D (scalF Wp (f ∘ th k r γ)) g0 - JF D (scalF Wp f) g0 := ⟨_, rfl⟩
  have hYc : ∀ u ∈ UUset k r D.z γ, Y.comp (D.π u) = (D.π u).comp Y := fun u hu => by
    rw [hY, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, Bc _ u hu, Bc _ u hu]
  have key : ∀ᵐ p ∂D.μSS, trY Y (Psi D γ f g0 p) = trY Y (Phi D f g0 p) := by
    filter_upwards [ae_in D] with p hp
    have hh := hp.1
    have hh' : Matrix.of p.2.1 ∈ UWset k r D.z := hz ▸ hp.2.2.1
    have hy : Matrix.of p.1.1 * (Matrix.of p.2.1)⁻¹ ∈ UWset k r D.z := uw_mul hh (uw_inv hh')
    obtain ⟨u₀, hu₀, hth⟩ := hT6 _ hy
    have hop : (D.π (gbar k r γ (Matrix.of p.2.1))).comp (D.π (gbar k r γ (Matrix.of p.1.1))⁻¹) =
        ((piLIE D.z D.π D.π_rep D.π_unitary u₀ hu₀.1 : Wp ≃ₗᵢ[ℂ] Wp) : Wp →L[ℂ] Wp).comp
          (((D.π (Matrix.of p.1.1)).comp (D.π (Matrix.of p.2.1)⁻¹)).comp
            (((piLIE D.z D.π D.π_rep D.π_unitary u₀ hu₀.1).symm : Wp ≃ₗᵢ[ℂ] Wp) : Wp →L[ℂ] Wp)) := by
      rw [← D.π_rep.2 _ (hWbar _ hh') _ (uw_inv (hWbar _ hh)), ← th_mul_inv γ hE (isUnit_of_uh hh'.1), hth,
        D.π_rep.2 _ (uw_mul hu₀.1 hy) _ (uw_inv hu₀.1), D.π_rep.2 _ hu₀.1 _ hy, D.π_rep.2 _ hh _ (uw_inv hh')]
      ext v
      rfl
    have h2 : Y.comp (((piLIE D.z D.π D.π_rep D.π_unitary u₀ hu₀.1).symm : Wp ≃ₗᵢ[ℂ] Wp) : Wp →L[ℂ] Wp) =
        (((piLIE D.z D.π D.π_rep D.π_unitary u₀ hu₀.1).symm : Wp ≃ₗᵢ[ℂ] Wp) : Wp →L[ℂ] Wp).comp Y := by
      rw [← pi_inv_eq D hu₀.1]
      exact hYc _ (uu_inv hu₀)
    simp only [Psi, Phi, hop, map_smul, trY_conj Y _ _ h2]
  have hI1 : trY Y (∫ p, Psi D γ f g0 p ∂D.μSS) = trY Y (∫ p, Phi D f g0 p ∂D.μSS) := by
    rw [← ContinuousLinearMap.integral_comp_comm _ hPsiI, ← ContinuousLinearMap.integral_comp_comm _ hPhiI]
    exact integral_congr_ae key
  have hYY : trY Y (JF D (scalF Wp (f ∘ th k r γ)) g0 - JF D (scalF Wp f) g0) = 0 := by
    rw [map_sub, hB, hB', hI1, sub_self]
  rw [← hY] at hYY
  have h0 := trY_self hYY
  rwa [hY, sub_eq_zero] at h0

end ReciprocityTheory.ChartRestriction.DS.Mult1.SymE

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1.SymA ReciprocityTheory.ChartRestriction.DS.Mult1.SymB
  ReciprocityTheory.ChartRestriction.DS.Mult1.SymE

theorem stSym (hIn : UnitaryGroupStructuralFacts) : StSym := by
  intro k r Wp _ _ _ D X hD hX γ hγ f q _ hq hT hEf
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, hCIall, -, -, -, -, -, -, -, -, hClW, -⟩, -, -, hBCF, hUWb, -⟩ := id hIn
  have hCI : ConjInv D := hCIall k r Wp Wp D
  obtain ⟨-, -, hW1, -, -, -, -, hμN, hμW⟩ := stInvGroup hIn k r Wp D X hD hX γ hγ
  have hChar := stInvChar k r Wp D X hD hX γ hγ
  have hL6 := stTransM hIn k r Wp D X hD hX γ hγ
  have hE : IsUnit (embWb k r γ).det := emb_unit (unit_of_frame hγ.1)
  have hTpos : 0 < Tz k r D.z := D.T_pos
  have hc : ∀ a, q.1 a ≠ 0 := by
    intro a ha0
    have hw : 0 < bcWeight k r (Tz k r D.z) (Tz k r D.z') q := hq
    unfold bcWeight at hw
    split_ifs at hw with h1
    · have hM : 0 < 2 * (Mdim k r a - 2) := by
        unfold Mdim
        have := a.isLt
        have := D.k_pos
        omega
      have h0 : (∏ b : Fin r, ‖q.1 b‖ ^ (2 * (Mdim k r b - 2))) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ a) (by rw [ha0, norm_zero, zero_pow hM.ne'])
      rw [h0, zero_mul] at hw
      exact lt_irrefl _ hw
    · exact lt_irrefl _ hw
  have hT0 : ((Tz k r D.z : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hTpos.ne'
  obtain ⟨d, hd_def⟩ : ∃ d : ℂ, d = -(q.2 / ((Tz k r D.z : ℝ) : ℂ)) := ⟨_, rfl⟩
  have hd : 1 < ‖d‖ := by
    have h3 : Tz k r D.z < ‖q.2‖ := by
      rw [Complex.normSq_eq_norm_sq] at hT
      by_contra hcon
      push Not at hcon
      nlinarith [norm_nonneg q.2]
    have hnT : ‖((Tz k r D.z : ℝ) : ℂ)‖ = Tz k r D.z := by
      rw [Complex.norm_real, Real.norm_of_nonneg hTpos.le]
    rw [hd_def, norm_neg, norm_div, hnT, one_lt_div hTpos]
    exact h3
  have hqd : (q.1, -((Tz k r D.z : ℝ) : ℂ) * d) = q := by
    refine Prod.ext rfl ?_
    show -((Tz k r D.z : ℝ) : ℂ) * d = q.2
    rw [hd_def]
    field_simp
  obtain ⟨-, -, -, hg0th, h₀, hh₀, h₀', hh₀', hgq⟩ := stReps hIn k r Wp D X hD hX γ hγ q.1 d hc hd
  rw [hqd] at hgq
  have hh₀'' : h₀' ∈ UWset k r D.z' := hD.z_eq ▸ hh₀'
  have red : ∀ F : Mat k r → (Wp →L[ℂ] Wp),
      JF D F (gq D q) = (Lab D hh₀ hh₀'').symm (JF D F (g0 k r γ q.1 d)) := fun F => by
    rw [J_equiv D hCI hh₀ hh₀'' F (g0 k r γ q.1 d), ← hgq, ContinuousLinearEquiv.symm_apply_apply]
  have hEf0 : ∫⁻ p, ‖rho D p (scalF Wp f) (g0 k r γ q.1 d)‖ₑ ∂D.μSS ≠ ∞ := by
    rw [E_equiv D hCI hh₀ hh₀'', ← hgq]
    exact hEf
  rw [red, red, core D hD hCI (hClW k r D.z).closed γ hE hμW hμN (fun m hm => (hChar m hm).1) hW1 hL6 hg0th
    (fun u hu => big_cell_commute_frame_element hBCF hUWb D.k_pos hγ hu q.1 d) f hEf0]

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section
noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SymBetaA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem deriv_smul_const_any {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (h : ℝ → ℂ) (T : E) :
    deriv (fun t => h t • T) 0 = deriv h 0 • T := by
  by_cases hT : T = 0
  · subst hT
    simp
  by_cases hd : DifferentiableAt ℝ h 0
  · exact deriv_smul_const hd T
  · have hnd : ¬ DifferentiableAt ℝ (fun t => h t • T) 0 := by
      intro hd'
      apply hd
      obtain ⟨φ, -, hφ⟩ := exists_dual_vector ℂ T (norm_ne_zero_iff.mpr hT)
      have hφT : φ T ≠ 0 := by
        rw [hφ]
        exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hT)
      have he : h = fun t => (φ T)⁻¹ * φ (h t • T) := by
        funext t
        rw [map_smul, smul_eq_mul]
        field_simp
      rw [he]
      exact DifferentiableAt.const_mul ((φ.restrictScalars ℝ).differentiableAt.comp (0 : ℝ) hd') _
    rw [deriv_zero_of_not_differentiableAt hnd, deriv_zero_of_not_differentiableAt hd, zero_smul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem LdV_smul (X : Mat k r) (φ : Mat k r → ℂ) (T : E) :
    LdV X (fun g => φ g • T) = fun g => LdV X φ g • T := by
  funext g
  exact deriv_smul_const_any _ T

theorem RdV_smul (X : Mat k r) (φ : Mat k r → ℂ) (T : E) :
    RdV X (fun g => φ g • T) = fun g => RdV X φ g • T := by
  funext g
  exact deriv_smul_const_any _ T

theorem Rw_smul (v : List (Mat k r)) (φ : Mat k r → ℂ) (T : E) :
    Rw v (fun g => φ g • T) = fun g => Rw v φ g • T := by
  induction v with
  | nil => rfl
  | cons X v ih =>
    show RdV X (Rw v (fun g => φ g • T)) = fun g => RdV X (Rw v φ) g • T
    rw [ih]
    exact RdV_smul X (Rw v φ) T

theorem dLR_smul (u v : List (Mat k r)) (φ : Mat k r → ℂ) (T : E) :
    dLR u v (fun g => φ g • T) = fun g => dLR u v φ g • T := by
  induction u with
  | nil => exact Rw_smul v φ T
  | cons X u ih =>
    show LdV X (dLR u v (fun g => φ g • T)) = fun g => LdV X (dLR u v φ) g • T
    rw [ih]
    exact LdV_smul X (dLR u v φ) T

theorem ccle_scalF {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {A : ℝ} {m : ℕ}
    {f : Mat k r → ℂ} {c : ℝ} (hf : CCle A m f c) : CCle A m (scalF Wp f) c := by
  obtain ⟨hck, hb⟩ := hf
  refine ⟨?_, fun u v hu hv hl g hg => ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hcd, heq⟩ := hck g₀ hg₀
    refine ⟨U, fun g => f' g • ContinuousLinearMap.id ℂ Wp, hU, hgU, hcd.smul contDiffOn_const,
      fun g hgU' hgG => ?_⟩
    simp only [scalF, heq g hgU' hgG]
  · have h1 := hb u v hu hv hl g hg
    have hsc : dLR u v (scalF Wp f) g = dLR u v f g • ContinuousLinearMap.id ℂ Wp :=
      congrFun (dLR_smul u v f (ContinuousLinearMap.id ℂ Wp)) g
    rw [hsc, norm_smul]
    have hid : ‖ContinuousLinearMap.id ℂ Wp‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hg0 : 0 ≤ gN g ^ A := Real.rpow_nonneg (Real.sqrt_nonneg _) A
    calc gN g ^ A * (‖dLR u v f g‖ * ‖ContinuousLinearMap.id ℂ Wp‖) ≤ gN g ^ A * ‖dLR u v f g‖ := by
          apply mul_le_mul_of_nonneg_left _ hg0
          exact mul_le_of_le_one_right (norm_nonneg _) hid
      _ ≤ c := h1

theorem inCC_scalF {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {A : ℝ} {m : ℕ}
    {f : Mat k r → ℂ} (hf : InCC A m f) : InCC A m (scalF Wp f) := by
  obtain ⟨c, hc⟩ := hf
  exact ⟨c, ccle_scalF hc⟩

theorem inCC_five_four' {A : ℝ} {f : Mat k r → E} (h : InCC A 5 f) : InCC A 4 f := by
  obtain ⟨c, hck, hb⟩ := h
  refine ⟨c, ?_, fun u v hu hv hl g hg => hb u v hu hv (by omega) g hg⟩
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hcd, heq⟩ := hck g₀ hg₀
  exact ⟨U, f', hU, hgU, hcd.of_le (WithTop.coe_le_coe.mpr (Nat.cast_le.mpr (by norm_num))), heq⟩

theorem continuousOn_of_ckOn {m : ℕ∞} {f : Mat k r → E} (h : CkOn m (GV k r) f) :
    ContinuousOn f (GV k r) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hcd, heq⟩ := h g₀ hg₀
  have hc : ContinuousAt f' g₀ := hcd.continuousOn.continuousAt (hU.mem_nhds hgU)
  refine (hc.continuousWithinAt (s := GV k r)).congr_of_eventuallyEq ?_ (heq g₀ hgU hg₀)
  filter_upwards [inter_mem_nhdsWithin (GV k r) (hU.mem_nhds hgU)] with g hg
  exact heq g hg.2 hg.1

theorem integrable_of_inCC (hInt : GNIntSharp) (hLow : GNLower) (hCl : ClosedG) {Wp Wq : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (D : RealPlaceData k r Wp Wq) {A : ℝ} (hA : AB k r ≤ A) {f : Mat k r → ℂ} (hf : InCC A 5 f) :
    Integrable (fun g : Mt k r => f (Matrix.of g)) D.μG := by
  obtain ⟨c, hCk, hbd⟩ := hf
  have hb0 : ∀ g ∈ GV k r, ‖f g‖ ≤ c * gN g ^ (-A) := by
    intro g hg
    have h1 := hbd [] [] (by simp) (by simp) (by simp) g hg
    have hgN : 0 < gN g := lt_of_lt_of_le one_pos (hLow k r g hg)
    have hpow : 0 < gN g ^ A := Real.rpow_pos_of_pos hgN A
    rw [Real.rpow_neg hgN.le, ← div_eq_mul_inv, le_div_iff₀ hpow]
    have h2 : gN g ^ A * ‖f g‖ ≤ c := h1
    linarith [mul_comm (gN g ^ A) ‖f g‖]
  have hae : ∀ᵐ g ∂D.μG, Matrix.of g ∈ GV k r := ae_iff.mpr D.haarG.conc
  have hGm : MeasurableSet {g : Mt k r | Matrix.of g ∈ GV k r} :=
    (show IsClosed {g : Mt k r | Matrix.of g ∈ GV k r} from (hCl k r).closed).measurableSet
  have hgNc : Continuous fun g : Mt k r => gN (Matrix.of g) := by
    unfold gN
    exact Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))
  have hint : Integrable (fun g : Mt k r => gN (Matrix.of g) ^ (-A)) D.μG := by
    refine ⟨(hgNc.measurable.pow_const (-A)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun g => by
      show (0 : ℝ) ≤ gN (Matrix.of g) ^ (-A)
      unfold gN
      exact Real.rpow_nonneg (Real.sqrt_nonneg _) _)]
    exact hInt k r D.μG A D.haarG hA
  have hcont : ContinuousOn (fun g : Mt k r => f (Matrix.of g)) {g : Mt k r | Matrix.of g ∈ GV k r} :=
    continuousOn_of_ckOn hCk
  have hmeas : AEStronglyMeasurable (fun g : Mt k r => f (Matrix.of g)) D.μG := by
    have := hcont.aestronglyMeasurable (μ := D.μG) hGm
    rwa [Measure.restrict_eq_self_of_ae_mem (s := {g : Mt k r | Matrix.of g ∈ GV k r}) hae] at this
  refine (hint.const_mul c).mono' hmeas (hae.mono fun g hg => ?_)
  exact hb0 _ hg

theorem volume_normSq_eq (c : ℝ) :
    volume {q : (Fin r → ℂ) × ℂ | Complex.normSq q.2 = c} = 0 := by
  have hsub : {q : (Fin r → ℂ) × ℂ | Complex.normSq q.2 = c} ⊆
      Set.univ ×ˢ Metric.sphere (0 : ℂ) (Real.sqrt c) := by
    rintro ⟨a, z⟩ hz
    simp only [Set.mem_setOf_eq] at hz
    refine ⟨Set.mem_univ _, ?_⟩
    rw [mem_sphere_zero_iff_norm, ← hz, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  refine measure_mono_null hsub ?_
  rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.addHaar_sphere, mul_zero]

theorem bcWeight_nonneg (T T' : ℝ) (q : (Fin r → ℂ) × ℂ) : 0 ≤ bcWeight k r T T' q := by
  unfold bcWeight
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun a _ => by positivity) (pow_nonneg (by linarith) _)
  · exact le_rfl

end ReciprocityTheory.ChartRestriction.DS.Mult1.SymBetaA
end
end

section
noncomputable section

open MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stSymBeta (h : UnitaryGroupStructuralFacts) : StSymBeta := by
  have hSym := stSym h
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hGI, hGL, -, -, -, hCl, -⟩, -⟩ := h
  unfold StSymBeta
  intro k r Wp _ _ _ D X hD hX γ hγ A hA hJ f F' hf hF'
  have hfi := SymBetaA.integrable_of_inCC hGI hGL hCl D hA hf
  have hae := (hJ (scalF Wp f) (SymBetaA.inCC_five_four' (SymBetaA.inCC_scalF hf))).1
  have hbd : volume {q : (Fin r → ℂ) × ℂ | Complex.normSq q.2 = Tz k r D.z * Tz k r D.z} = 0 :=
    SymBetaA.volume_normSq_eq _
  unfold beta betaBig
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_imp_of_ae_restrict hae, measure_eq_zero_iff_ae_notMem.1 hbd] with q hq hq2
  by_cases hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0
  · simp [hw]
  have hQ : q ∈ Qset D := lt_of_le_of_ne (SymBetaA.bcWeight_nonneg _ _ q) (Ne.symm hw)
  have hle : Tz k r D.z * Tz k r D.z ≤ Complex.normSq q.2 := by
    by_contra hc
    apply hw
    rw [bcWeight, hD.z_eq, if_neg hc]
  have hlt : Tz k r D.z * Tz k r D.z < Complex.normSq q.2 :=
    lt_of_le_of_ne hle (fun e => hq2 e.symm)
  have hEf : Ef D (scalF Wp f) q ≠ ⊤ := (hq hQ).2.ne
  have e : JF D (scalF Wp (f ∘ th k r γ)) (bigCell k r q.1 (D.μsec q.2)) =
      JF D (scalF Wp f) (bigCell k r q.1 (D.μsec q.2)) :=
    hSym k r Wp D X hD hX γ hγ f q hfi hQ hlt hEf
  simp only [e]

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end
