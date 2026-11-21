import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelDer
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.InhabA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelCext
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HasDerivAtRealOfComplex
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.SingleMulJmComm

section
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def blkMinor (ε : Fin n → Bool) (a : Fin n) (x : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (x.submatrix (fun b : {b : Fin n // ε b = ε a ∧ b ≤ a} => (b : Fin n))
    (fun b : {b : Fin n // ε b = ε a ∧ b ≤ a} => (b : Fin n))).det

open Classical in

def mexp (ε : Fin n → Bool) (m : Fin n → ℤ) (a : Fin n) : ℤ :=
  if h : (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a).Nonempty then
    m a - m ((Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a).min' h)
  else m a

def NonnegDom (ε : Fin n → Bool) (m : Fin n → ℤ) : Prop :=
  (∀ a b, a < b → ε a = ε b → m b ≤ m a) ∧ ∀ a, 0 ≤ m a


def f0 (ε : Fin n → Bool) (m : Fin n → ℤ) (x : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∏ a, blkMinor ε a x ^ (mexp ε m a).toNat

def f0K (ε : Fin n → Bool) (m : Fin n → ℤ) (k : KG ε) : ℂ := f0 ε m (toMK k)

theorem mexp_nonneg (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) (a : Fin n) : 0 ≤ mexp ε m a := by
  unfold mexp
  split_ifs with h
  · have hb := (Finset.mem_filter.1 (Finset.min'_mem _ h)).2
    exact sub_nonneg.2 (hm.1 a _ hb.1 hb.2.symm)
  · exact hm.2 a

lemma hwmf_diff_entry (i j : Fin n) : Differentiable ℂ (fun x : Matrix (Fin n) (Fin n) ℂ => x i j) := by
  first
    | exact ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.proj i) :
        (Fin n → Fin n → ℂ) →L[ℂ] ℂ).differentiable
    | fun_prop
    | exact (differentiable_apply j).comp (differentiable_apply i)

lemma hwmf_diff_prod {ι : Type} (s : Finset ι) (g : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (h : ∀ i, Differentiable ℂ (g i)) : Differentiable ℂ (fun x => ∏ i ∈ s, g i x) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty]
    exact differentiable_const _
  · intro a s ha ih
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih

lemma hwmf_diff_blkMinor (ε : Fin n → Bool) (a : Fin n) : Differentiable ℂ (blkMinor ε a) := by
  show Differentiable ℂ (fun x : Matrix (Fin n) (Fin n) ℂ => blkMinor ε a x)
  simp only [blkMinor, Matrix.det_apply, Matrix.submatrix_apply, Units.smul_def, zsmul_eq_mul]
  first
    | (apply Differentiable.fun_sum
       intro σ _
       exact (differentiable_const _).mul (hwmf_diff_prod _ _ (fun i => hwmf_diff_entry _ _)))
    | fun_prop
    | (apply Differentiable.sum
       intro σ _
       exact (differentiable_const _).mul (hwmf_diff_prod _ _ (fun i => hwmf_diff_entry _ _)))

theorem differentiable_highest_weight_fn (ε : Fin n → Bool) (m : Fin n → ℤ) : Differentiable ℂ (f0 ε m) := by
  show Differentiable ℂ (fun x : Matrix (Fin n) (Fin n) ℂ => f0 ε m x)
  simp only [f0]
  exact hwmf_diff_prod _ _ (fun a => (hwmf_diff_blkMinor ε a).pow _)


theorem highest_weight_fn_K_one (ε : Fin n → Bool) (m : Fin n → ℤ) : f0K ε m 1 = 1 := by
  have h1 : toMK (1 : KG ε) = 1 := by
    first
      | exact toMK_one
      | simp [toMK]
      | rfl
  unfold f0K f0 blkMinor
  rw [h1]
  simp [Matrix.submatrix_one _ Subtype.val_injective]

lemma hwmf_hasDerivAt_A (X Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => Y * NormedSpace.exp ((t : ℂ) • X)) (Y * X) 0 := by
  refine hasDerivAt_pi.2 fun i => ?_
  refine hasDerivAt_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  refine HasDerivAt.fun_sum fun k _ => HasDerivAt.const_mul _ ?_
  have h := InhabA.hasDerivAt_exp_entry X k j
  have e : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) k j) = fun t : ℝ => (NormedSpace.exp (t • X)) k j := by
    funext t; congr 3
  rw [e]; exact h

theorem hasDerivAt_f0K (ε : Fin n → Bool) (m : Fin n → ℤ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (x : KG ε) :
    HasDerivAt (fun t : ℝ => f0K ε m (x * kcurve ε X t)) (fderiv ℂ (f0 ε m) (toMK x) (toMK x * X)) 0 := by
  have hspec := (kcurve_spec ε hX).2.1
  have hmul : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b := by
    intro a b
    first
      | exact toMK_mul a b
      | (simp [toMK, toM]; done)
      | (simp only [toMK]; exact map_mul _ _ _)
      | (simp only [toMK, toM]; rfl)
  have hfun : (fun t : ℝ => f0K ε m (x * kcurve ε X t)) =
      fun t : ℝ => f0 ε m (toMK x * NormedSpace.exp ((t : ℂ) • X)) := by
    funext t
    show f0 ε m (toMK (x * kcurve ε X t)) = _
    rw [hmul, hspec t]
  rw [hfun]
  have hd : HasFDerivAt (f0 ε m) (fderiv ℂ (f0 ε m) (toMK x))
      (toMK x * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one]
    exact (differentiable_highest_weight_fn ε m (toMK x)).hasFDerivAt
  exact (hd.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) (hwmf_hasDerivAt_A X (toMK x))

lemma hwmf_cpart_sum (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε Z + Complex.I • cpart2 ε Z = Z := by
  unfold cpart1 cpart2
  ext i j
  first
    | (simp
       linear_combination (-(1 / 2) * (Z i j + (Jm ε * Zᴴ * Jm ε) i j)) * Complex.I_sq)
    | (simp [Complex.I_sq]; ring)

private theorem inK_cp1_lemma (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inK ε (cpart1 ε (bdPart ε Z)) := by
  unfold inK inG cpart1 Jm bdPart
  constructor <;> ext a b <;>
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, Complex.star_def, map_div₀] <;>
    rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>
    rcases Bool.eq_false_or_eq_true (ε b) with hb | hb <;>
    simp [ha, hb, Complex.conj_ofNat, map_ofNat] <;> ring

private theorem inK_cp2_lemma_2 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inK ε (cpart2 ε (bdPart ε Z)) := by
  unfold inK inG cpart2 Jm bdPart
  constructor <;> ext a b <;>
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Complex.star_def, map_div₀,
      Complex.conj_I] <;>
    rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>
    rcases Bool.eq_false_or_eq_true (ε b) with hb | hb <;>
    simp [ha, hb, Complex.conj_ofNat, map_ofNat] <;> ring

lemma hwmf_rdc (ε : Fin n → Bool) (m : Fin n → ℤ) (Z : Matrix (Fin n) (Fin n) ℂ) (x : KG ε) :
    rdc ε Z (f0K ε m) x = fderiv ℂ (f0 ε m) (toMK x) (toMK x * bdPart ε Z) := by
  have h1 := hasDerivAt_f0K ε m (inK_cp1_lemma ε Z) x
  have h2 := hasDerivAt_f0K ε m (inK_cp2_lemma_2 ε Z) x
  unfold rdc
  rw [h1.deriv, h2.deriv]
  rw [show Complex.I * fderiv ℂ (f0 ε m) (toMK x) (toMK x * cpart2 ε (bdPart ε Z)) =
      fderiv ℂ (f0 ε m) (toMK x) (Complex.I • (toMK x * cpart2 ε (bdPart ε Z))) from
      ((fderiv ℂ (f0 ε m) (toMK x)).map_smul Complex.I _).symm]
  rw [← map_add, ← Matrix.mul_smul, ← Matrix.mul_add, hwmf_cpart_sum]

lemma hwmf_line (ε : Fin n → Bool) (m : Fin n → ℤ) (x W : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun s : ℂ => f0 ε m (x * (1 + s • W))) (fderiv ℂ (f0 ε m) x (x * W)) 0 := by
  have hin : HasDerivAt (fun s : ℂ => x * (1 + s • W)) (x * W) 0 := by
    have hfun : (fun s : ℂ => x * (1 + s • W)) = fun s => x + s • (x * W) := by
      funext s
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
    rw [hfun]
    have h := ((hasDerivAt_id' (0 : ℂ)).smul_const (x * W)).const_add x
    rw [one_smul] at h
    exact h
  have hd : HasFDerivAt (f0 ε m) (fderiv ℂ (f0 ε m) x) (x * (1 + (0 : ℂ) • W)) := by
    rw [zero_smul, add_zero, Matrix.mul_one]
    exact (differentiable_highest_weight_fn ε m x).hasFDerivAt
  exact hd.comp_hasDerivAt (0 : ℂ) hin

lemma hwmf_mul_tv (x : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (s : ℂ) (r q : Fin n) :
    (x * (1 + s • single a b (1 : ℂ))) r q = x r q + (if q = b then s * x r a else 0) := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  congr 1
  by_cases hq : q = b
  · subst hq
    rw [if_pos rfl, Matrix.mul_apply]
    simp [Matrix.single_apply]
  · rw [if_neg hq, Matrix.mul_apply]
    simp [Matrix.single_apply, Ne.symm hq]

lemma hwmf_blk_tv (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b) (c : Fin n)
    (x : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    blkMinor ε c (x * (1 + s • single a b (1 : ℂ))) = blkMinor ε c x := by
  unfold blkMinor
  by_cases hb : ε b = ε c ∧ b ≤ c
  · obtain ⟨B, hB⟩ : ∃ B : {d : Fin n // ε d = ε c ∧ d ≤ c}, (B : Fin n) = b := ⟨⟨b, hb⟩, rfl⟩
    obtain ⟨A, hA⟩ : ∃ A : {d : Fin n // ε d = ε c ∧ d ≤ c}, (A : Fin n) = a :=
      ⟨⟨a, he.trans hb.1, hab.le.trans hb.2⟩, rfl⟩
    have hBA : B ≠ A := fun h => (ne_of_lt hab) (by rw [← hA, ← hB, h])
    have hM : (x * (1 + s • single a b (1 : ℂ))).submatrix
        (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) =
        (x.submatrix (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n))).updateCol B
          (fun k => x.submatrix (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) k B +
            s • x.submatrix (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) k A) := by
      ext i j
      rw [Matrix.submatrix_apply, hwmf_mul_tv, Matrix.updateCol_apply]
      by_cases hj : j = B
      · subst hj
        simp [hB, hA, smul_eq_mul]
      · have hj' : (j : Fin n) ≠ b := fun h => hj (Subtype.ext (h.trans hB.symm))
        simp [hj, hj']
    rw [hM, Matrix.det_updateCol_add_smul_self _ hBA]
  · congr 1
    ext i j
    rw [Matrix.submatrix_apply, Matrix.submatrix_apply, hwmf_mul_tv]
    have hj : (j : Fin n) ≠ b := fun h => hb (h ▸ j.2)
    simp [hj]

lemma hwmf_mul_dg (x : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) (s : ℂ) (r q : Fin n) :
    (x * (1 + s • single a a (1 : ℂ))) r q = x r q * (if q = a then 1 + s else 1) := by
  rw [hwmf_mul_tv]
  by_cases hq : q = a
  · subst hq
    rw [if_pos rfl, if_pos rfl]
    ring
  · rw [if_neg hq, if_neg hq]
    ring

lemma hwmf_blk_dg (ε : Fin n → Bool) (a c : Fin n) (x : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    blkMinor ε c (x * (1 + s • single a a (1 : ℂ))) =
      blkMinor ε c x * (if ε a = ε c ∧ a ≤ c then 1 + s else 1) := by
  unfold blkMinor
  have hx : (x * (1 + s • single a a (1 : ℂ))).submatrix (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n))
      (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) =
      x.submatrix (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n))
        (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) *
      diagonal (fun q : {d : Fin n // ε d = ε c ∧ d ≤ c} => if (q : Fin n) = a then 1 + s else 1) := by
    ext r q
    simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, hwmf_mul_dg]
  rw [hx, det_mul, det_diagonal]
  congr 1
  split_ifs with ha
  · rw [Fintype.prod_eq_single (⟨a, ha⟩ : {d : Fin n // ε d = ε c ∧ d ≤ c})]
    · simp
    · intro q hq
      have : (q : Fin n) ≠ a := fun h => hq (Subtype.ext h)
      simp [this]
  · apply Finset.prod_eq_one
    intro q _
    have : (q : Fin n) ≠ a := fun h => ha (h ▸ q.2)
    simp [this]

lemma hwmf_tele (ε : Fin n → Bool) (m : Fin n → ℤ) : ∀ k : ℕ, ∀ a : Fin n,
    (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a).card = k →
    ∑ c ∈ Finset.univ.filter (fun c : Fin n => ε a = ε c ∧ a ≤ c), mexp ε m c = m a := by
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ih a hk
  have hsplit : Finset.univ.filter (fun c : Fin n => ε a = ε c ∧ a ≤ c) =
      insert a (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      rcases h2.lt_or_eq with h | h
      · exact Or.inr ⟨h, h1.symm⟩
      · exact Or.inl h.symm
    · rintro (h | ⟨h1, h2⟩)
      · subst h
        exact ⟨rfl, le_rfl⟩
      · exact ⟨h2.symm, h1.le⟩
  have hnot : a ∉ Finset.univ.filter (fun b : Fin n => a < b ∧ ε b = ε a) := by simp
  rw [hsplit, Finset.sum_insert hnot]
  by_cases hne : (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a).Nonempty
  · obtain ⟨a', ha'def⟩ : ∃ a', (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a).min' hne = a' :=
      ⟨_, rfl⟩
    have ha'mem : a < a' ∧ ε a' = ε a := by
      have := Finset.min'_mem _ hne
      rw [ha'def] at this
      exact (Finset.mem_filter.1 this).2
    have hset : (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a) =
        Finset.univ.filter (fun c : Fin n => ε a' = ε c ∧ a' ≤ c) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨ha'mem.2.trans h2.symm, ?_⟩
        rw [← ha'def]
        exact Finset.min'_le _ _ (by simp [h1, h2])
      · rintro ⟨h1, h2⟩
        exact ⟨lt_of_lt_of_le ha'mem.1 h2, h1.symm.trans ha'mem.2⟩
    have hcard : (Finset.univ.filter fun b : Fin n => a' < b ∧ ε b = ε a').card < k := by
      rw [← hk]
      have hsub : (Finset.univ.filter fun b : Fin n => a' < b ∧ ε b = ε a') ⊆
          (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a) := by
        intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
        exact ⟨ha'mem.1.trans hc.1, hc.2.trans ha'mem.2⟩
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset hsub]
      exact ⟨a', by simp [ha'mem.1, ha'mem.2], by simp⟩
    rw [hset, ih _ hcard a' rfl]
    unfold mexp
    rw [dif_pos hne, ha'def]
    ring
  · have hemp := Finset.not_nonempty_iff_eq_empty.1 hne
    rw [hemp, Finset.sum_empty, add_zero]
    unfold mexp
    rw [dif_neg hne]

lemma hwmf_bd_single (ε : Fin n → Bool) {a b : Fin n} (he : ε a = ε b) :
    bdPart ε (single a b (1 : ℂ)) = single a b 1 := by
  ext i j
  simp only [bdPart, Matrix.of_apply]
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    rw [if_pos he]
  · rw [Matrix.single_apply, if_neg h, ite_self]

private theorem f0_dg_lemma (ε : Fin n → Bool) (m : Fin n → ℤ) (a : Fin n) (X : Matrix (Fin n) (Fin n) ℂ)
    (s : ℂ) : f0 ε m (X * (1 + s • single a a (1 : ℂ))) =
      f0 ε m X * (1 + s) ^ (∑ c ∈ Finset.univ.filter (fun c : Fin n => ε a = ε c ∧ a ≤ c),
        (mexp ε m c).toNat) := by
  unfold f0
  simp only [hwmf_blk_dg, mul_pow, Finset.prod_mul_distrib, ite_pow, one_pow]
  congr 1
  rw [← Finset.prod_filter, Finset.prod_pow_eq_pow_sum]

theorem rdc_f0K_wt (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) (a : Fin n) (x : KG ε) :
    rdc ε (Matrix.single a a 1) (f0K ε m) x = ((m a : ℤ) : ℂ) * f0K ε m x := by
  rw [hwmf_rdc, hwmf_bd_single ε rfl]
  have h1 := hwmf_line ε m (toMK x) (single a a 1)
  have hc : (fun s : ℂ => f0 ε m (toMK x * (1 + s • single a a (1 : ℂ)))) = fun s =>
      f0 ε m (toMK x) * (1 + s) ^ (∑ c ∈ Finset.univ.filter (fun c : Fin n => ε a = ε c ∧ a ≤ c),
        (mexp ε m c).toNat) := by
    funext s
    exact f0_dg_lemma ε m a (toMK x) s
  rw [hc] at h1
  have h2 := (((hasDerivAt_id' (0 : ℂ)).const_add 1).pow (∑ c ∈ Finset.univ.filter
    (fun c : Fin n => ε a = ε c ∧ a ≤ c), (mexp ε m c).toNat)).const_mul (f0 ε m (toMK x))
  rw [h1.unique h2]
  have hsum : ((∑ c ∈ Finset.univ.filter (fun c : Fin n => ε a = ε c ∧ a ≤ c), (mexp ε m c).toNat : ℕ) : ℤ)
      = m a := by
    rw [Nat.cast_sum, ← hwmf_tele ε m _ a rfl]
    exact Finset.sum_congr rfl fun c _ => Int.toNat_of_nonneg (mexp_nonneg ε hm c)
  have hsumC : ((∑ c ∈ Finset.univ.filter (fun c : Fin n => ε a = ε c ∧ a ≤ c), (mexp ε m c).toNat : ℕ) : ℂ)
      = ((m a : ℤ) : ℂ) := by
    rw [← hsum, Int.cast_natCast]
  simp only [add_zero, one_pow, mul_one]
  rw [hsumC]
  unfold f0K
  ring

theorem rdc_f0K_hw (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) {a b : Fin n} (hab : a < b)
    (he : ε a = ε b) (x : KG ε) : rdc ε (Matrix.single a b 1) (f0K ε m) x = 0 := by
  rw [hwmf_rdc, hwmf_bd_single ε he]
  have h1 := hwmf_line ε m (toMK x) (single a b 1)
  have hc : (fun s : ℂ => f0 ε m (toMK x * (1 + s • single a b (1 : ℂ)))) = fun _ => f0 ε m (toMK x) := by
    funext s
    unfold f0
    simp only [hwmf_blk_tv ε hab he]
  rw [hc] at h1
  exact h1.unique (hasDerivAt_const _ _)

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

section
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def rtr (ε : Fin n → Bool) (k : KG ε) : (KG ε → ℂ) →ₗ[ℂ] (KG ε → ℂ) where
  toFun f := fun x => f (x * k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rtr_mul (ε : Fin n → Bool) (k₁ k₂ : KG ε) (f : KG ε → ℂ) : rtr ε (k₁ * k₂) f = rtr ε k₁ (rtr ε k₂ f) := by
  funext x
  show f (x * (k₁ * k₂)) = f (x * k₁ * k₂)
  rw [mul_assoc]

theorem rtr_one (ε : Fin n → Bool) (f : KG ε → ℂ) : rtr ε 1 f = f := by
  funext x
  show f (x * 1) = f x
  rw [mul_one]

def Vsp (ε : Fin n → Bool) (m : Fin n → ℤ) : Submodule ℂ (KG ε → ℂ) :=
  Submodule.span ℂ (Set.range fun k : KG ε => rtr ε k (f0K ε m))

theorem highest_weight_fn_mem_space (ε : Fin n → Bool) (m : Fin n → ℤ) : f0K ε m ∈ Vsp ε m := by
  have h : rtr ε 1 (f0K ε m) ∈ Vsp ε m := Submodule.subset_span ⟨1, rfl⟩
  rwa [rtr_one] at h

theorem rtr_mem (ε : Fin n → Bool) (m : Fin n → ℤ) (k : KG ε) {f : KG ε → ℂ} (hf : f ∈ Vsp ε m) :
    rtr ε k f ∈ Vsp ε m := by
  have h : Vsp ε m ≤ (Vsp ε m).comap (rtr ε k) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k', rfl⟩
    show rtr ε k (rtr ε k' (f0K ε m)) ∈ Vsp ε m
    rw [← rtr_mul]
    exact Submodule.subset_span ⟨k * k', rfl⟩
  exact h hf

def evalK (ε : Fin n → Bool) : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] (KG ε → ℂ) :=
  MvPolynomial.aeval fun p : Fin n × Fin n => fun k : KG ε => toMK k p.1 p.2

def polyK (ε : Fin n → Bool) (D : ℕ) : Submodule ℂ (KG ε → ℂ) :=
  (MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ D).map (evalK ε).toLinearMap

theorem evalK_apply (ε : Fin n → Bool) (Q : MvPolynomial (Fin n × Fin n) ℂ) (x : KG ε) :
    evalK ε Q x = MvPolynomial.aeval (fun p : Fin n × Fin n => toMK x p.1 p.2) Q := by
  induction Q using MvPolynomial.induction_on
  next a => simp [evalK]
  next p q hp hq => rw [map_add, map_add, Pi.add_apply, hp, hq]
  next p i hp =>
    rw [map_mul, map_mul, Pi.mul_apply, hp]
    simp [evalK]

def rsub (ε : Fin n → Bool) (k : KG ε) : Fin n × Fin n → MvPolynomial (Fin n × Fin n) ℂ :=
  fun p => ∑ l, MvPolynomial.X (p.1, l) * MvPolynomial.C (toMK k l p.2)

theorem toMK_mul' (ε : Fin n → Bool) (x k : KG ε) : toMK (x * k) = toMK x * toMK k := rfl

theorem rtr_evalK (ε : Fin n → Bool) (k : KG ε) (Q : MvPolynomial (Fin n × Fin n) ℂ) :
    rtr ε k (evalK ε Q) = evalK ε (MvPolynomial.bind₁ (rsub ε k) Q) := by
  funext x
  show evalK ε Q (x * k) = evalK ε (MvPolynomial.bind₁ (rsub ε k) Q) x
  rw [evalK_apply, evalK_apply, MvPolynomial.aeval_bind₁]
  refine congrArg (fun g => MvPolynomial.aeval g Q) ?_
  funext p
  simp [rsub, toMK_mul', Matrix.mul_apply]

theorem totalDegree_rsub (ε : Fin n → Bool) (k : KG ε) (p : Fin n × Fin n) :
    (rsub ε k p).totalDegree ≤ 1 := by
  simp only [rsub]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun l _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simp [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]

theorem totalDegree_bind₁_le {σ τ : Type*} (g : σ → MvPolynomial τ ℂ) (hg : ∀ i, (g i).totalDegree ≤ 1)
    (Q : MvPolynomial σ ℂ) : (MvPolynomial.bind₁ g Q).totalDegree ≤ Q.totalDegree := by
  classical
  conv_lhs => rw [Q.as_sum]
  rw [map_sum]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun d hd => ?_)
  rw [MvPolynomial.bind₁_monomial]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_totalDegree hd)
  rw [Finsupp.sum]
  refine Finset.sum_le_sum fun i _ => ?_
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  calc d i * (g i).totalDegree ≤ d i * 1 := Nat.mul_le_mul_left _ (hg i)
    _ = d i := mul_one _

theorem rtr_polyK (ε : Fin n → Bool) (k : KG ε) (Q : MvPolynomial (Fin n × Fin n) ℂ) :
    rtr ε k (evalK ε Q) ∈ polyK ε Q.totalDegree := by
  rw [rtr_evalK]
  exact Submodule.mem_map_of_mem ((MvPolynomial.mem_restrictTotalDegree ..).mpr
    (totalDegree_bind₁_le _ (totalDegree_rsub ε k) Q))

def f0P (ε : Fin n → Bool) (m : Fin n → ℤ) : MvPolynomial (Fin n × Fin n) ℂ :=
  ∏ a, ((Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).submatrix
    (fun b : {b : Fin n // ε b = ε a ∧ b ≤ a} => (b : Fin n))
    (fun b : {b : Fin n // ε b = ε a ∧ b ≤ a} => (b : Fin n))).det ^ (mexp ε m a).toNat

theorem evalK_f0P (ε : Fin n → Bool) (m : Fin n → ℤ) : evalK ε (f0P ε m) = f0K ε m := by
  funext k
  rw [evalK_apply]
  show _ = f0 ε m (toMK k)
  simp only [f0P, f0, blkMinor, map_prod, map_pow]
  refine Finset.prod_congr rfl fun a _ => ?_
  congr 1
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp [Matrix.mvPolynomialX]

theorem Vsp_le_polyK (ε : Fin n → Bool) (m : Fin n → ℤ) : ∃ D : ℕ, Vsp ε m ≤ polyK ε D := by
  refine ⟨(f0P ε m).totalDegree, Submodule.span_le.mpr ?_⟩
  rintro _ ⟨k, rfl⟩
  show rtr ε k (f0K ε m) ∈ polyK ε _
  rw [← evalK_f0P]
  exact rtr_polyK ε k (f0P ε m)

theorem finiteDimensional_Vsp (ε : Fin n → Bool) (m : Fin n → ℤ) : FiniteDimensional ℂ (Vsp ε m) := by
  obtain ⟨D, hD⟩ := Vsp_le_polyK ε m
  haveI : FiniteDimensional ℂ (polyK ε D) := by
    unfold polyK
    infer_instance
  exact Submodule.finiteDimensional_of_le hD

theorem differentiable_aeval_entries (Q : MvPolynomial (Fin n × Fin n) ℂ) :
    Differentiable ℂ (fun M : Matrix (Fin n) (Fin n) ℂ =>
      MvPolynomial.aeval (fun p : Fin n × Fin n => M p.1 p.2) Q) := by
  induction Q using MvPolynomial.induction_on
  next a => simp
  next p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  next p i hp =>
    have hX : Differentiable ℂ (fun M : Matrix (Fin n) (Fin n) ℂ => M i.1 i.2) := by
      fun_prop
    simp only [map_mul, MvPolynomial.aeval_X]
    exact hp.mul hX

theorem Vsp_holo (ε : Fin n → Bool) (m : Fin n → ℤ) {f : KG ε → ℂ} (hf : f ∈ Vsp ε m) :
    ∃ F : Matrix (Fin n) (Fin n) ℂ → ℂ, Differentiable ℂ F ∧ ∀ k, f k = F (toMK k) := by
  obtain ⟨D, hD⟩ := Vsp_le_polyK ε m
  have h' : f ∈ (MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ D).map (evalK ε).toLinearMap := hD hf
  obtain ⟨Q, -, rfl⟩ := Submodule.mem_map.mp h'
  exact ⟨fun M => MvPolynomial.aeval (fun p : Fin n × Fin n => M p.1 p.2) Q,
    differentiable_aeval_entries Q, fun k => evalK_apply ε Q k⟩

theorem continuous_of_mem_Vsp (ε : Fin n → Bool) (m : Fin n → ℤ) {f : KG ε → ℂ} (hf : f ∈ Vsp ε m) :
    Continuous f := by
  obtain ⟨F, hF, hfF⟩ := Vsp_holo ε m hf
  have hfe : f = fun k => F (toMK k) := funext hfF
  rw [hfe]
  refine hF.continuous.comp ?_
  fun_prop

theorem hasDerivAt_of_mem_Vsp (ε : Fin n → Bool) (m : Fin n → ℤ) {f : KG ε → ℂ} (hf : f ∈ Vsp ε m)
    {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : Differentiable ℂ F) (hfF : ∀ k, f k = F (toMK k))
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (x : KG ε) :
    HasDerivAt (fun t : ℝ => f (x * kcurve ε X t)) (fderiv ℂ F (toMK x) (toMK x * X)) 0 := by
  have hc : HasDerivAt (fun t : ℝ => toMK (kcurve ε X t)) X 0 := by
    have hk : ∀ t : ℝ, toMK (kcurve ε X t) = NormedSpace.exp ((t : ℝ) • X) := fun t => by
       unfold kcurve
       rw [dif_pos hX, Classical.choose_spec (exists_curve ε hX) t, Complex.coe_smul]
    simp only [hk]
    letI iR : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℝ ℂ _
    haveI : @CompleteSpace (Matrix (Fin n) (Fin n) ℂ)
        (@PseudoMetricSpace.toUniformSpace _ (@MetricSpace.toPseudoMetricSpace _ (@NormedRing.toMetricSpace _ iR))) := by
      exact FiniteDimensional.complete ℂ _
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ (toMK x))
  have hin : HasDerivAt (fun t : ℝ => L (toMK (kcurve ε X t))) (L X) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 hc
  have h0 : toMK (kcurve ε X 0) = 1 := by
    unfold kcurve
    rw [dif_pos hX, Classical.choose_spec (exists_curve ε hX) 0]
    simp
  have hLx : L (toMK (kcurve ε X 0)) = toMK x := by
    rw [h0]
    exact mul_one _
  have hF' := ((hF (toMK x)).hasFDerivAt.restrictScalars ℝ)
  rw [← hLx] at hF'
  have hcomp := hF'.comp_hasDerivAt (0 : ℝ) hin
  have hfun : (fun t : ℝ => f (x * kcurve ε X t)) = fun t => F (L (toMK (kcurve ε X t))) := by
    funext t
    rw [hfF, toMK_mul']
    rfl
  rw [hfun]
  rw [hLx] at hcomp
  exact hcomp

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

section
noncomputable section

open Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def MV (ε : Fin n → Bool) (m : Fin n → ℤ) : Type := ↥(Vsp ε m)

instance (ε : Fin n → Bool) (m : Fin n → ℤ) : AddCommGroup (MV ε m) := inferInstanceAs (AddCommGroup ↥(Vsp ε m))

instance (ε : Fin n → Bool) (m : Fin n → ℤ) : Module ℂ (MV ε m) := inferInstanceAs (Module ℂ ↥(Vsp ε m))

def MV.fn {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) : KG ε → ℂ := ((show ↥(Vsp ε m) from f) : KG ε → ℂ)

def MV.mk {ε : Fin n → Bool} {m : Fin n → ℤ} (f : KG ε → ℂ) (hf : f ∈ Vsp ε m) : MV ε m :=
  (⟨f, hf⟩ : ↥(Vsp ε m))

theorem MV.mem {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) : f.fn ∈ Vsp ε m := by
  exact (show ↥(Vsp ε m) from f).2

@[simp] theorem MV.fn_mk {ε : Fin n → Bool} {m : Fin n → ℤ} (f : KG ε → ℂ) (hf : f ∈ Vsp ε m) :
    (MV.mk f hf).fn = f := rfl

theorem MV.ext {ε : Fin n → Bool} {m : Fin n → ℤ} {f g : MV ε m} (h : f.fn = g.fn) : f = g := by
  exact Subtype.ext h

@[simp] theorem MV.fn_add {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) : (f + g).fn = f.fn + g.fn := rfl

@[simp] theorem MV.fn_smul {ε : Fin n → Bool} {m : Fin n → ℤ} (c : ℂ) (f : MV ε m) : (c • f).fn = c • f.fn := rfl

@[simp] theorem MV.fn_zero {ε : Fin n → Bool} {m : Fin n → ℤ} : (0 : MV ε m).fn = 0 := rfl

def mvInner {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) : ℂ :=
  ∫ x, starRingEnd ℂ (f.fn x) * g.fn x ∂(muK ε)

theorem MV.continuous_fn {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) : Continuous f.fn := by
  exact continuous_of_mem_Vsp ε m f.mem

theorem integrable_of_continuous_KG {ε : Fin n → Bool} {F : KG ε → ℂ} (hF : Continuous F) :
    MeasureTheory.Integrable F (muK ε) := by

  have := compactSpace_KG ε
  exact hF.integrable_of_hasCompactSupport (isClosed_tsupport F).isCompact

theorem mvInner_integrable {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) :
    MeasureTheory.Integrable (fun x => starRingEnd ℂ (f.fn x) * g.fn x) (muK ε) := by
  exact integrable_of_continuous_KG
    ((Complex.continuous_conj.comp f.continuous_fn).mul g.continuous_fn)

theorem mvInner_self_eq {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) :
    mvInner f f = ((∫ x, Complex.normSq (f.fn x) ∂(muK ε) : ℝ) : ℂ) := by
  unfold mvInner
  simp_rw [← Complex.normSq_eq_conj_mul_self]
  exact integral_ofReal

theorem mvInner_conj {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) :
    starRingEnd ℂ (mvInner g f) = mvInner f g := by
  unfold mvInner
  rw [← integral_conj]
  congr 1
  funext x
  simp only [map_mul, Complex.conj_conj]
  exact mul_comm _ _

theorem mvInner_re_nonneg {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) : 0 ≤ (mvInner f f).re := by
  rw [mvInner_self_eq, Complex.ofReal_re]
  exact integral_nonneg fun x => Complex.normSq_nonneg _

theorem mvInner_add_left {ε : Fin n → Bool} {m : Fin n → ℤ} (f g h : MV ε m) :
    mvInner (f + g) h = mvInner f h + mvInner g h := by
  simp only [mvInner, MV.fn_add, Pi.add_apply, map_add, add_mul]
  exact integral_add (mvInner_integrable f h) (mvInner_integrable g h)

theorem mvInner_smul_left {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) (c : ℂ) :
    mvInner (c • f) g = starRingEnd ℂ c * mvInner f g := by
  simp only [mvInner, MV.fn_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
  exact integral_const_mul _ _

theorem mvInner_definite {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) (h : mvInner f f = 0) : f = 0 := by

  have hc : Continuous fun x => Complex.normSq (f.fn x) :=
    Complex.continuous_normSq.comp f.continuous_fn
  rw [mvInner_self_eq, Complex.ofReal_eq_zero] at h
  have hae : (fun x => Complex.normSq (f.fn x)) =ᵐ[muK ε] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => Complex.normSq_nonneg _)
      (by
        have := compactSpace_KG ε
        exact hc.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact)).mp h
  have hz : (fun x => Complex.normSq (f.fn x)) = 0 :=
    (Continuous.ae_eq_iff_eq (muK ε) hc continuous_const).mp hae
  apply MV.ext
  funext x
  simpa using congrFun hz x

@[instance_reducible]
def mvCore (ε : Fin n → Bool) (m : Fin n → ℤ) : InnerProductSpace.Core ℂ (MV ε m) where
  inner := mvInner
  conj_inner_symm := mvInner_conj
  re_inner_nonneg := mvInner_re_nonneg
  add_left := mvInner_add_left
  smul_left := mvInner_smul_left
  definite := mvInner_definite

instance (ε : Fin n → Bool) (m : Fin n → ℤ) : NormedAddCommGroup (MV ε m) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (MV ε m) _ _ _ (mvCore ε m)

instance (ε : Fin n → Bool) (m : Fin n → ℤ) : InnerProductSpace ℂ (MV ε m) :=
  InnerProductSpace.ofCore (mvCore ε m).toCore

instance (ε : Fin n → Bool) (m : Fin n → ℤ) : FiniteDimensional ℂ (MV ε m) :=
  finiteDimensional_Vsp ε m

instance (ε : Fin n → Bool) (m : Fin n → ℤ) : CompleteSpace (MV ε m) := FiniteDimensional.complete ℂ _

theorem MV.inner_def {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) : inner ℂ f g = mvInner f g := rfl

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

section
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

section PreA

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V] {ε : Fin n → Bool} (τ : KG ε →* unitary (V →L[ℂ] V))
  (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V))

abbrev preOp (k : KG ε) : V →L[ℂ] V := ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V)

theorem preOp_mul (k l : KG ε) : preOp τ (k * l) = preOp τ k * preOp τ l := by
  show ((τ (k * l) : unitary (V →L[ℂ] V)) : V →L[ℂ] V) = _
  rw [map_mul]; rfl

theorem preOp_one : preOp τ (1 : KG ε) = 1 := by
  show ((τ 1 : unitary (V →L[ℂ] V)) : V →L[ℂ] V) = _
  rw [map_one]; rfl

theorem preOp_inv (k : KG ε) : preOp τ k⁻¹ = star (preOp τ k) := by
  show ((τ k⁻¹ : unitary (V →L[ℂ] V)) : V →L[ℂ] V) = _
  rw [map_inv]; rfl

variable (hder : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
    HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (dτ X) 0)

include hder in
theorem pre_op_curve {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) (t : ℝ) :
    preOp τ (γ t) = NormedSpace.exp ((t : ℂ) • dτ X) := by
  set A := dτ X with hAdef
  set F : ℝ → V →L[ℂ] V := fun s => preOp τ (γ s) with hFdef
  have hmul : ∀ s u : ℝ, γ (s + u) = γ s * γ u := by
    intro s u
    apply onep_KG_ext
    show toMK (γ (s + u)) = toMK (γ s) * toMK (γ u)
    rw [hγ, hγ, hγ, show (((s + u : ℝ) : ℂ) • X) = (s : ℂ) • X + (u : ℂ) • X by push_cast; exact add_smul _ _ _]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)
  have h0 : γ 0 = 1 := by
    apply onep_KG_ext
    rw [hγ]
    show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = (1 : Matrix (Fin n) (Fin n) ℂ)
    simp
  have hF : ∀ s u : ℝ, F (s + u) = F s * F u := by
    intro s u
    simp only [hFdef, hmul, preOp_mul]
  have hF0 : F 0 = 1 := by
    simp only [hFdef, h0, preOp_one]
  have hd0 : HasDerivAt F A 0 := hder X hX γ hγ
  have hd : ∀ s, HasDerivAt F (F s * A) s := by
    intro s
    have h1 : HasDerivAt (fun u => F s * F (u - s)) (F s * A) s := by
      have h2 := hd0.const_mul (F s)
      rw [← sub_self s] at h2
      exact HasDerivAt.comp_sub_const (f := fun y => F s * F y) s s h2
    convert h1 using 1
    funext u
    rw [← hF, add_sub_cancel]
  set E : ℝ → V →L[ℂ] V := fun u => NormedSpace.exp (u • (-A)) with hEdef
  have hE : ∀ u, HasDerivAt E (E u * (-A)) u := fun u => hasDerivAt_exp_smul_const (-A) u
  have hcomm : ∀ u, A * E u = E u * A := fun u =>
    (((Commute.refl A).neg_right.smul_right u).exp_right).eq
  have hG : ∀ u, HasDerivAt (F * E) 0 u := by
    intro u
    refine ((hd u).mul (hE u)).congr_deriv ?_
    simp only [mul_neg, mul_assoc, hcomm u, add_neg_cancel]
  have hGc : ∀ u, (F * E) u = (F * E) 0 := fun u =>
    is_const_of_deriv_eq_zero (fun v => (hG v).differentiableAt) (fun v => (hG v).deriv) u 0
  have hG0 : (F * E) 0 = 1 := by
    show F 0 * NormedSpace.exp ((0 : ℝ) • (-A)) = 1
    rw [hF0, zero_smul, NormedSpace.exp_zero, one_mul]
  show F t = _
  have hs : ((t : ℂ) • A) = t • A := by
    exact Complex.coe_smul t A
  rw [hs]
  have hc : Commute (t • (-A)) (t • A) := (((Commute.refl A).neg_left).smul_left t).smul_right t
  calc F t = F t * E t * NormedSpace.exp (t • A) := by
        rw [mul_assoc, hEdef, ← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hc
          ((NormedSpace.expSeries_radius_eq_top ℝ (V →L[ℂ] V)).symm ▸ edist_lt_top _ _)
          ((NormedSpace.expSeries_radius_eq_top ℝ (V →L[ℂ] V)).symm ▸ edist_lt_top _ _), smul_neg, neg_add_cancel,
          NormedSpace.exp_zero, mul_one]
    _ = NormedSpace.exp (t • A) := by
        rw [show F t * E t = (F * E) t from rfl, hGc, hG0, one_mul]

include hder in
theorem pre_op_eq_exp' (k : KG ε) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, inK ε Y ∧ preOp τ k = NormedSpace.exp (dτ Y) := by
  obtain ⟨Y, hY, he⟩ := exists_log ε k
  obtain ⟨γ, hγ⟩ := exists_curve ε hY
  have h1 : γ 1 = k := by
    apply onep_KG_ext
    have := hγ 1
    simp only [Complex.ofReal_one, one_smul] at this
    rw [this, he]
  refine ⟨Y, hY, ?_⟩
  have := pre_op_curve τ dτ hder hY γ hγ 1
  simpa [h1] using this

include hder in
theorem pre_star_dτ {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) : star (dτ X) = -dτ X := by
  obtain ⟨γ, hγ⟩ := exists_curve ε hX
  set A := dτ X
  have key : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • star A) * NormedSpace.exp ((t : ℂ) • A) = 1 := by
    intro t
    have h1 := pre_op_curve τ dτ hder hX γ hγ t
    have h2 : star (preOp τ (γ t)) * preOp τ (γ t) = 1 := Unitary.coe_star_mul_self _
    rw [h1, NormedSpace.star_exp, star_smul, Complex.star_def, Complex.conj_ofReal] at h2
    exact h2
  have hd0 := (hasDerivAt_exp_smul_const (star A) ((0 : ℝ) : ℂ)).mul
    (hasDerivAt_exp_smul_const A ((0 : ℝ) : ℂ))
  have hd2 := hasDerivAt_real_of_complex' hd0
  have hf : (fun y : ℝ => ((fun u : ℂ => NormedSpace.exp (u • star A)) *
      fun u : ℂ => NormedSpace.exp (u • A)) (y : ℂ)) = fun _ => 1 := funext fun t => by
    simpa using key t
  rw [hf] at hd2
  have := hd2.unique (hasDerivAt_const _ _)
  simp at this
  exact eq_neg_of_add_eq_zero_left this

include hder in
theorem pre_conj_dτ (k : KG ε) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) :
    preOp τ k * dτ Y * star (preOp τ k) = dτ (toMK k * Y * star (toMK k)) := by
  obtain ⟨γ, hγ⟩ := exists_curve ε hY
  have hY' := inK_conj' k hY
  set U : (Matrix (Fin n) (Fin n) ℂ)ˣ := ((k : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)
  have hU : ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = star (toMK k) :=
    toMK_inv' k
  have hγ' : ∀ t : ℝ, toMK (k * γ t * k⁻¹) =
      NormedSpace.exp ((t : ℂ) • (toMK k * Y * star (toMK k))) := by
    intro t
    have e1 : toMK (k * γ t * k⁻¹) = toMK k * toMK (γ t) * toMK k⁻¹ := rfl
    rw [e1, toMK_inv', hγ t, ← hU]
    have e2 : (t : ℂ) • ((U : Matrix (Fin n) (Fin n) ℂ) * Y * ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)) = (U : Matrix (Fin n) (Fin n) ℂ) * ((t : ℂ) • Y) *
        ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [e2, Matrix.exp_units_conj]
  set B := dτ Y
  set C := dτ (toMK k * Y * star (toMK k))
  have key : ∀ t : ℝ, preOp τ k * NormedSpace.exp ((t : ℂ) • B) * star (preOp τ k) =
      NormedSpace.exp ((t : ℂ) • C) := by
    intro t
    rw [← pre_op_curve τ dτ hder hY γ hγ t, ← pre_op_curve τ dτ hder hY' _ hγ' t, ← preOp_inv,
      preOp_mul, preOp_mul]
  have h1 := hasDerivAt_real_of_complex' (z := 0)
    (((hasDerivAt_exp_smul_const B ((0 : ℝ) : ℂ)).const_mul (preOp τ k)).mul_const (star (preOp τ k)))
  have h2 := hasDerivAt_real_of_complex' (z := 0) (hasDerivAt_exp_smul_const C ((0 : ℝ) : ℂ))
  have hf : (fun y : ℝ => preOp τ k * NormedSpace.exp ((y : ℂ) • B) * star (preOp τ k)) =
      fun y : ℝ => NormedSpace.exp ((y : ℂ) • C) := funext key
  simp only [hf] at h1
  have := h1.unique h2
  simpa using this

section MatDerivP

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem pre_dτ_conj_hasDerivAt (X Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun y : ℝ => dτ (NormedSpace.exp ((y : ℂ) • X) * Y *
      NormedSpace.exp ((y : ℂ) • (-X)))) (dτ (X * Y - Y * X)) 0 := by
  have h := ((LinearMap.toContinuousLinearMap dτ).hasFDerivAt).comp_hasDerivAt _
    (mat_conj_hasDerivAt X Y)
  exact hasDerivAt_real_of_complex' (z := 0) h

end MatDerivP

include hder in
theorem pre_dτ_bracket {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (hY : inK ε Y) :
    dτ X * dτ Y - dτ Y * dτ X = dτ (X * Y - Y * X) := by
  obtain ⟨γ, hγ⟩ := exists_curve ε hX
  set A := dτ X
  set B := dτ Y
  have hA := pre_star_dτ τ dτ hder hX
  have hXs := ((inK_iff' ε X).1 hX).1
  have key : ∀ s : ℝ, NormedSpace.exp ((s : ℂ) • A) * B * NormedSpace.exp ((s : ℂ) • (-A)) =
      dτ (NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • (-X))) := by
    intro s
    have h := pre_conj_dτ τ dτ hder (γ s) hY
    rw [pre_op_curve τ dτ hder hX γ hγ s, hγ s, NormedSpace.star_exp, star_smul, hA,
      Complex.star_def, Complex.conj_ofReal] at h
    rw [h]
    congr 2
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hXs,
      Complex.star_def, Complex.conj_ofReal]
  have h1 := hasDerivAt_real_of_complex' (z := 0)
    (((hasDerivAt_exp_smul_const A ((0 : ℝ) : ℂ)).mul_const B).mul
      (hasDerivAt_exp_smul_const (-A) ((0 : ℝ) : ℂ)))
  have h2 := pre_dτ_conj_hasDerivAt dτ X Y
  have h1' := h1.congr_of_eventuallyEq
    (f₁ := fun s : ℝ => dτ (NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • (-X))))
    (Filter.Eventually.of_forall fun s => (key s).symm)
  have := h1'.unique h2
  rw [← this]
  simp [sub_eq_add_neg]

include hder in
theorem pre_dτ_bracket_single {a b c d : Fin n} (hab : ε a = ε b) (hcd : ε c = ε d) :
    dτ (Matrix.single a b 1) * dτ (Matrix.single c d 1) -
        dτ (Matrix.single c d 1) * dτ (Matrix.single a b 1) =
      dτ (Matrix.single a b 1 * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1) := by
  rw [single_eq_kp a b, single_eq_kp c d, brk_expand, map_add, map_add, map_smul, map_smul,
    brk_expand, map_add, map_add, map_add, map_smul, map_smul, map_smul,
    pre_dτ_bracket τ dτ hder (inK_hermitian_unit hab) (inK_hermitian_unit hcd), pre_dτ_bracket τ dτ hder (inK_hermitian_unit hab) (inK_skew_hermitian_unit hcd),
    pre_dτ_bracket τ dτ hder (inK_skew_hermitian_unit hab) (inK_hermitian_unit hcd), pre_dτ_bracket τ dτ hder (inK_skew_hermitian_unit hab) (inK_skew_hermitian_unit hcd)]

include hder in
theorem pre_star_dτ_single {a b : Fin n} (hab : ε a = ε b) :
    star (dτ (Matrix.single a b 1)) = dτ (Matrix.single b a 1) := by
  rw [single_eq_kp a b, single_eq_kp' a b, map_add, map_smul, map_add, map_smul, map_neg, star_add,
    star_smul, pre_star_dτ τ dτ hder (inK_hermitian_unit hab), pre_star_dτ τ dτ hder (inK_skew_hermitian_unit hab)]
  simp [Complex.conj_I]

end PreA

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

section
noncomputable section

open Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

section Pre

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

def preUnits (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V)) : Fin n → Fin n → Module.End ℂ V :=
  fun a b => ((dτ (Matrix.single a b 1) : V →L[ℂ] V) : Module.End ℂ V)

variable [FiniteDimensional ℂ V] {ε : Fin n → Bool} (τ : KG ε →* unitary (V →L[ℂ] V)) (hcont : Continuous τ)
  (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V))
  (hder : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
    HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (dτ X) 0)

include hcont hder in
theorem pre_op_eq_exp (k : KG ε) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, inK ε Y ∧
      ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) = NormedSpace.exp (dτ Y) := by
  exact pre_op_eq_exp' τ dτ hder k

include hcont hder in
theorem pre_kRel : Formalism.REAL.KRel ε (preUnits dτ) := by
  intro a b c d hab hcd
  have hbr := pre_dτ_bracket_single τ dτ hder hab hcd
  have hm : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
    by_cases h1 : b = c <;> by_cases h2 : d = a
    · subst h1 h2; simp [Matrix.single_mul_single_same]
    · subst h1; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h2]
    · subst h2; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h1]
    · simp [Matrix.single_mul_single_of_ne, Matrix.single_mul_single_of_ne, h1, h2]
  rw [hm] at hbr
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun F : V →L[ℂ] V => F x) hbr
  have e : ∀ A B : V →L[ℂ] V, (A * B) x = A (B x) := fun _ _ => rfl
  simp only [_root_.sub_apply, e, map_sub] at hx
  simp only [preUnits, LinearMap.sub_apply, Module.End.mul_apply, ContinuousLinearMap.coe_coe]
  rw [hx]
  split_ifs <;> simp

include hcont hder in
theorem pre_kUnit : Formalism.REAL.KUnit ε (preUnits dτ) := by
  intro a b hab x y
  show ⟪dτ (Matrix.single a b 1) x, y⟫_ℂ = ⟪x, dτ (Matrix.single b a 1) y⟫_ℂ
  rw [← pre_star_dτ_single τ dτ hder hab, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

theorem pre_dτ_stable_of_kStable (W : Submodule ℂ V) (hW : Formalism.REAL.KStable ε (preUnits dτ) W) :
    ∀ Y, inK ε Y → ∀ v ∈ W, dτ Y v ∈ W := by
  intro Y hY v hv
  rw [Matrix.matrix_eq_sum_single Y, map_sum, _root_.sum_apply]
  refine W.sum_mem fun a _ => ?_
  rw [map_sum, _root_.sum_apply]
  refine W.sum_mem fun b _ => ?_
  by_cases hab : ε a = ε b
  · have e : Matrix.single a b (Y a b) = Y a b • Matrix.single a b 1 := by
      ext i j; simp [Matrix.single_apply]
    rw [e, map_smul, _root_.smul_apply]
    exact W.smul_mem _ (hW a b hab v hv)
  · have e : Matrix.single a b (Y a b) = 0 := by
      rw [inK_entry_eq_zero hY hab]; ext i j; simp [Matrix.single_apply]
    rw [e, map_zero, _root_.zero_apply]
    exact W.zero_mem

include hcont hder in

theorem pre_kStable_of_stable (W : Submodule ℂ V)
    (hW : ∀ k : KG ε, ∀ v ∈ W, ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) v ∈ W) :
    Formalism.REAL.KStable ε (preUnits dτ) W := by
  have hK : ∀ X, inK ε X → ∀ v ∈ W, dτ X v ∈ W := by
    intro X hX v hv
    obtain ⟨γ, hγ⟩ := exists_curve ε hX
    have hd := hder X hX γ hγ
    have hdv : HasDerivAt (fun t : ℝ => preOp τ (γ t) v) (dτ X v) 0 := by
      have := ((ContinuousLinearMap.apply ℂ V v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
      simpa [Function.comp_def] using this
    rw [hasDerivAt_iff_tendsto_slope] at hdv
    have hcl : IsClosed (W : Set V) := W.closed_of_finiteDimensional
    refine hcl.mem_of_tendsto hdv (Filter.Eventually.of_forall fun t => ?_)
    rw [slope_def_module, SetLike.mem_coe]
    exact Submodule.smul_of_tower_mem W _ (W.sub_mem (hW _ v hv) (hW _ v hv))
  intro a b hab v hv
  show dτ (Matrix.single a b 1) v ∈ W
  set A : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b 1
  set B : Matrix (Fin n) (Fin n) ℂ := Matrix.single b a 1
  have hA : A * Jm ε = Jm ε * A := single_mul_Jm_comm hab 1
  have hB : B * Jm ε = Jm ε * B := single_mul_Jm_comm hab.symm 1
  have hAB : Aᴴ = B := by
    ext i j
    simp only [A, B, Matrix.conjTranspose_apply, Matrix.single_apply]
    by_cases h1 : a = j <;> by_cases h2 : b = i <;> simp [h1, h2]
  have hBA : Bᴴ = A := by rw [← hAB, Matrix.conjTranspose_conjTranspose]
  have h1 : inK ε (A - B) := inK_of_skew_comm (by rw [Matrix.conjTranspose_sub, hAB, hBA, neg_sub])
    (by rw [sub_mul, mul_sub, hA, hB])
  have h2 : inK ε (Complex.I • (A + B)) := inK_of_skew_comm
    (by rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, hAB, hBA, Complex.star_def,
      Complex.conj_I, add_comm, neg_smul])
    (by rw [Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, hA, hB])
  have e : A = (1 / 2 : ℂ) • (A - B) - (Complex.I / 2) • (Complex.I • (A + B)) := by
    rw [smul_smul, show Complex.I / 2 * Complex.I = -(1 / 2 : ℂ) by
      rw [div_mul_eq_mul_div, Complex.I_mul_I]; ring]
    module
  rw [e, map_sub, map_smul, map_smul, _root_.sub_apply, _root_.smul_apply,
    _root_.smul_apply]
  exact W.sub_mem (W.smul_mem _ (hK _ h1 v hv)) (W.smul_mem _ (hK _ h2 v hv))

include hcont hder in

theorem pre_kSpan_stable (x : V) (k : KG ε) :
    ∀ v ∈ Formalism.REAL.kSpan ε (preUnits dτ) x,
      ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) v ∈ Formalism.REAL.kSpan ε (preUnits dτ) x := by
  have hS : Formalism.REAL.KStable ε (preUnits dτ) (Formalism.REAL.kSpan ε (preUnits dτ) x) := by
    intro a b hab y hy
    unfold Formalism.REAL.kSpan at hy ⊢
    rw [Submodule.mem_sInf] at hy ⊢
    intro S hS
    exact hS.2 a b hab y (hy S hS)
  obtain ⟨Y, hY, he⟩ := pre_op_eq_exp' τ dτ hder k
  rw [show ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) = NormedSpace.exp (dτ Y) from he]
  exact exp_mem_of_stable _ _ (pre_dτ_stable_of_kStable dτ _ hS Y hY)

include hcont hder in

theorem irred_of_gen {Λ : Fin n → ℝ} (w : V)
    (hwt : ∀ a, dτ (Matrix.single a a 1) w = ((Λ a : ℝ) : ℂ) • w)
    (hhw : ∀ a b, a < b → ε a = ε b → dτ (Matrix.single a b 1) w = 0)
    (hgen : ∀ W : Submodule ℂ V, (∀ k : KG ε, ∀ v ∈ W, ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) v ∈ W) →
      w ∈ W → W = ⊤) :
    ∀ W : Submodule ℂ V, (∀ k : KG ε, ∀ v ∈ W, ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) v ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
  intro W hW
  have hx : w ∈ Formalism.REAL.kSpan ε (preUnits dτ) w := by
    unfold Formalism.REAL.kSpan
    rw [Submodule.mem_sInf]
    intro S hS
    exact hS.1
  have htop : Formalism.REAL.kSpan ε (preUnits dτ) w = ⊤ :=
    hgen _ (pre_kSpan_stable τ hcont dτ hder w) hx
  have hhi : Formalism.REAL.KHighest ε (preUnits dτ) Λ w :=
    ⟨fun a => hwt a, fun a b hab he => hhw a b hab he⟩
  have := Formalism.REAL.kIrr V n ε (preUnits dτ) Λ w inferInstance (pre_kRel τ hcont dτ hder)
    (pre_kUnit τ hcont dτ hder) hhi W (htop ▸ le_top) (pre_kStable_of_stable τ hcont dτ hder W hW)
  rwa [htop] at this

end Pre

def kTypeOfGen {ε : Fin n → Bool} {Λ : Fin n → ℝ} (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [CompleteSpace V] (τ : KG ε →* unitary (V →L[ℂ] V)) (hcont : Continuous τ)
    (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (V →L[ℂ] V))
    (hder : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      HasDerivAt (fun t => ((τ (γ t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) (dτ X) 0)
    (w : V) (hw : ‖w‖ = 1) (hwt : ∀ a, dτ (Matrix.single a a 1) w = ((Λ a : ℝ) : ℂ) • w)
    (hhw : ∀ a b, a < b → ε a = ε b → dτ (Matrix.single a b 1) w = 0)
    (hgen : ∀ W : Submodule ℂ V, (∀ k : KG ε, ∀ v ∈ W, ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) v ∈ W) →
      w ∈ W → W = ⊤) : KType ε Λ where
  V := V
  τ := τ
  cont := hcont
  irred := irred_of_gen τ hcont dτ hder w hwt hhw hgen
  dτ := dτ
  hasDeriv := hder
  w := w
  w_norm := hw
  w_wt := hwt
  w_hw := hhw

example (ε : Fin n → Bool) : KType ε 0 :=
  kTypeOfGen ℂ 1 continuous_const 0
    (fun _ _ _ _ => by simpa using hasDerivAt_const (0 : ℝ) (1 : ℂ →L[ℂ] ℂ)) 1 (by simp) (fun a => by simp)
    (fun _ _ _ _ => by simp)
    (fun W _ h => eq_top_iff.2 fun x _ => by simpa using W.smul_mem x h)

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

section
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def tauL (ε : Fin n → Bool) (m : Fin n → ℤ) (k : KG ε) : MV ε m →ₗ[ℂ] MV ε m where
  toFun f := MV.mk (rtr ε k f.fn) (rtr_mem ε m k f.mem)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def tauC (ε : Fin n → Bool) (m : Fin n → ℤ) (k : KG ε) : MV ε m →L[ℂ] MV ε m :=
  LinearMap.toContinuousLinearMap (tauL ε m k)

@[simp] theorem tauC_fn (ε : Fin n → Bool) (m : Fin n → ℤ) (k : KG ε) (f : MV ε m) :
    (tauC ε m k f).fn = rtr ε k f.fn := rfl

theorem tauC_one (ε : Fin n → Bool) (m : Fin n → ℤ) : tauC ε m 1 = 1 := by
  refine ContinuousLinearMap.ext fun f => MV.ext ?_
  rw [tauC_fn, rtr_one]
  rfl

theorem tauC_mul (ε : Fin n → Bool) (m : Fin n → ℤ) (k₁ k₂ : KG ε) :
    tauC ε m (k₁ * k₂) = tauC ε m k₁ * tauC ε m k₂ := by
  refine ContinuousLinearMap.ext fun f => MV.ext ?_
  rw [tauC_fn, rtr_mul, ContinuousLinearMap.mul_apply, tauC_fn, tauC_fn]

theorem tauC_inner (ε : Fin n → Bool) (m : Fin n → ℤ) (k : KG ε) (f g : MV ε m) :
    inner ℂ (tauC ε m k f) (tauC ε m k g) = inner ℂ f g := by
  show mvInner _ _ = mvInner _ _
  unfold mvInner
  simp only [tauC_fn]
  haveI := muK_rightInvariant ε
  exact MeasureTheory.integral_mul_right_eq_self (fun x => starRingEnd ℂ (f.fn x) * g.fn x) k

theorem tauC_mem_unitary (ε : Fin n → Bool) (m : Fin n → ℤ) (k : KG ε) : tauC ε m k ∈ unitary (MV ε m →L[ℂ] MV ε m) := by
  have hinv : ∀ f, tauC ε m k (tauC ε m k⁻¹ f) = f := by
    intro f
    rw [← ContinuousLinearMap.mul_apply, ← tauC_mul, mul_inv_cancel, tauC_one]
    rfl
  have hinv' : ∀ f, tauC ε m k⁻¹ (tauC ε m k f) = f := by
    intro f
    rw [← ContinuousLinearMap.mul_apply, ← tauC_mul, inv_mul_cancel, tauC_one]
    rfl
  have hadj : star (tauC ε m k) = tauC ε m k⁻¹ := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    rw [← tauC_inner ε m k (tauC ε m k⁻¹ x) y, hinv]
  first
    | rw [Unitary.mem_iff, hadj]
    | rw [unitary.mem_iff, hadj]
  constructor
  · ext f
    rw [ContinuousLinearMap.mul_apply, hinv', ContinuousLinearMap.one_apply]
  · ext f
    rw [ContinuousLinearMap.mul_apply, hinv, ContinuousLinearMap.one_apply]

def mvFnL (ε : Fin n → Bool) (m : Fin n → ℤ) : MV ε m →ₗ[ℂ] (KG ε → ℂ) where
  toFun f := f.fn
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem mvFnL_injective (ε : Fin n → Bool) (m : Fin n → ℤ) : Function.Injective (mvFnL ε m) := fun _ _ h => MV.ext h

theorem continuous_tauC_apply (ε : Fin n → Bool) (m : Fin n → ℤ) (f : MV ε m) :
    Continuous fun k : KG ε => tauC ε m k f := by
  let e := (LinearEquiv.ofInjective (mvFnL ε m) (mvFnL_injective ε m)).toContinuousLinearEquiv
  have h : Continuous fun k : KG ε => e (tauC ε m k f) := by
    refine continuous_induced_rng.2 ?_
    have hfun : (fun k : KG ε => ((e (tauC ε m k f) : LinearMap.range (mvFnL ε m)) : KG ε → ℂ)) =
        fun k x => f.fn (x * k) := rfl
    rw [Function.comp_def, hfun]
    exact continuous_pi fun x => (continuous_of_mem_Vsp ε m f.mem).comp (continuous_const.mul continuous_id)
  have h2 : (fun k : KG ε => tauC ε m k f) = fun k => e.symm (e (tauC ε m k f)) := by
    funext k; simp
  rw [h2]
  exact e.symm.continuous.comp h

theorem continuous_tauC (ε : Fin n → Bool) (m : Fin n → ℤ) : Continuous (tauC ε m) :=
  continuous_clm_apply.2 (continuous_tauC_apply ε m)

def tauM (ε : Fin n → Bool) (m : Fin n → ℤ) : KG ε →* unitary (MV ε m →L[ℂ] MV ε m) where
  toFun k := ⟨tauC ε m k, tauC_mem_unitary ε m k⟩
  map_one' := Subtype.ext (tauC_one ε m)
  map_mul' k₁ k₂ := Subtype.ext (tauC_mul ε m k₁ k₂)


theorem continuous_tauM (ε : Fin n → Bool) (m : Fin n → ℤ) : Continuous (tauM ε m) := continuous_induced_rng.2 (continuous_tauC ε m)

private theorem derOp_fn_eq_deriv_kcurve (ε : Fin n → Bool) (m : Fin n → ℤ) (X : Matrix (Fin n) (Fin n) ℂ) (f : MV ε m)
    (x : KG ε) : (derOp ε (tauM ε m) X f).fn x = deriv (fun t : ℝ => f.fn (x * kcurve ε X t)) 0 := by
  by_cases hX : inK ε X
  · have h := derOp_hasDeriv ε (tauM ε m) (continuous_tauM ε m) X hX (kcurve ε X) (kcurve_spec ε hX).2.1
    let evx : MV ε m →ₗ[ℂ] ℂ :=
      { toFun := fun g => g.fn x
        map_add' := fun a b => by simp
        map_smul' := fun c a => by simp }
    let E : (MV ε m →L[ℂ] MV ε m) →L[ℂ] ℂ :=
      (LinearMap.toContinuousLinearMap evx).comp (ContinuousLinearMap.apply ℂ (MV ε m) f)
    have h2 := (E.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
    have h3 : HasDerivAt (fun t : ℝ => f.fn (x * kcurve ε X t)) ((derOp ε (tauM ε m) X f).fn x) 0 := h2
    exact h3.deriv.symm
  · have hk : kcurve ε X = fun _ => 1 := by
      unfold kcurve
      rw [dif_neg hX]
    simp [derOp, hk]

theorem derOp_fn (ε : Fin n → Bool) (m : Fin n → ℤ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (f : MV ε m)
    (x : KG ε) : (derOp ε (tauM ε m) X f).fn x = deriv (fun t : ℝ => f.fn (x * kcurve ε X t)) 0 := by
  exact derOp_fn_eq_deriv_kcurve ε m X f x

theorem inK_add' (ε : Fin n → Bool) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (hY : inK ε Y) :
    inK ε (X + Y) := by
  obtain ⟨h1, h2⟩ := hX
  obtain ⟨h3, h4⟩ := hY
  refine ⟨?_, ?_⟩
  · unfold inG at h1 h3 ⊢
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    calc Xᴴ * Jm ε + Yᴴ * Jm ε + (Jm ε * X + Jm ε * Y)
        = (Xᴴ * Jm ε + Jm ε * X) + (Yᴴ * Jm ε + Jm ε * Y) := by abel
      _ = 0 := by rw [h1, h3, add_zero]
  · rw [Matrix.add_mul, Matrix.mul_add, h2, h4]

theorem inK_rsmul' (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (r : ℝ) :
    inK ε ((r : ℂ) • X) := by
  obtain ⟨h1, h2⟩ := hX
  refine ⟨?_, ?_⟩
  · unfold inG at h1 ⊢
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, h1, smul_zero]
  · rw [Matrix.smul_mul, Matrix.mul_smul, h2]

theorem derOp_fn_eq (ε : Fin n → Bool) (m : Fin n → ℤ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (f : MV ε m) (x : KG ε) {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : Differentiable ℂ F)
    (hfF : ∀ k, f.fn k = F (toMK k)) :
    (derOp ε (tauM ε m) X f).fn x = fderiv ℂ F (toMK x) (toMK x * X) := by
  rw [derOp_fn ε m hX f x]
  exact (hasDerivAt_of_mem_Vsp ε m f.mem hF hfF hX x).deriv

theorem rLinOnK_derOp (ε : Fin n → Bool) (m : Fin n → ℤ) : RLinOnK ε (derOp ε (tauM ε m)) := by
  intro X Y r hX hY
  constructor
  · refine ContinuousLinearMap.ext fun f => MV.ext (funext fun x => ?_)
    obtain ⟨F, hF, hfF⟩ := Vsp_holo ε m f.mem
    rw [_root_.add_apply, MV.fn_add, Pi.add_apply, derOp_fn_eq ε m (inK_add' ε hX hY) f x hF hfF,
      derOp_fn_eq ε m hX f x hF hfF, derOp_fn_eq ε m hY f x hF hfF, Matrix.mul_add, map_add]
  · refine ContinuousLinearMap.ext fun f => MV.ext (funext fun x => ?_)
    obtain ⟨F, hF, hfF⟩ := Vsp_holo ε m f.mem
    rw [_root_.smul_apply, MV.fn_smul, Pi.smul_apply, smul_eq_mul,
      derOp_fn_eq ε m (inK_rsmul' ε hX r) f x hF hfF, derOp_fn_eq ε m hX f x hF hfF, Matrix.mul_smul, map_smul,
      smul_eq_mul]

def dTau (ε : Fin n → Bool) (m : Fin n → ℤ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (MV ε m →L[ℂ] MV ε m) :=
  cextL ε (derOp ε (tauM ε m)) (rLinOnK_derOp ε m)

theorem dTau_fn (ε : Fin n → Bool) (m : Fin n → ℤ) (Z : Matrix (Fin n) (Fin n) ℂ) (f : MV ε m) (x : KG ε) :
    (dTau ε m Z f).fn x = rdc ε Z f.fn x := by
  unfold dTau
  rw [cextL_apply]
  unfold cext
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, MV.fn_add, MV.fn_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, derOp_fn_eq_deriv_kcurve]
  rfl

theorem hasDeriv_dTau (ε : Fin n → Bool) (m : Fin n → ℤ) (X : Matrix (Fin n) (Fin n) ℂ) (hX : inK ε X)
    (γ : ℝ → KG ε) (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) :
    HasDerivAt (fun t => ((tauM ε m (γ t) : unitary (MV ε m →L[ℂ] MV ε m)) : MV ε m →L[ℂ] MV ε m))
      (dTau ε m X) 0 := by
  have h := derOp_hasDeriv ε (tauM ε m) (continuous_tauM ε m) X hX γ hγ
  have he : dTau ε m X = derOp ε (tauM ε m) X := by
    unfold dTau
    rw [cextL_apply, cext_of_inK _ (rLinOnK_derOp ε m) hX]
  rw [he]
  exact h

def w0 (ε : Fin n → Bool) (m : Fin n → ℤ) : MV ε m := MV.mk (f0K ε m) (highest_weight_fn_mem_space ε m)

def wN (ε : Fin n → Bool) (m : Fin n → ℤ) : MV ε m := ((‖w0 ε m‖⁻¹ : ℝ) : ℂ) • w0 ε m

theorem highest_weight_vector_ne_zero (ε : Fin n → Bool) (m : Fin n → ℤ) : w0 ε m ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : MV ε m => f.fn 1) h
  simp only [MV.fn_zero, Pi.zero_apply] at h1
  have h2 : (w0 ε m).fn 1 = 1 := highest_weight_fn_K_one ε m
  rw [h2] at h1
  exact one_ne_zero h1

theorem norm_wN (ε : Fin n → Bool) (m : Fin n → ℤ) : ‖wN ε m‖ = 1 := by
  have h0 : ‖w0 ε m‖ ≠ 0 := norm_ne_zero_iff.mpr (highest_weight_vector_ne_zero ε m)
  unfold wN
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ h0]

theorem derived_action_weight_vector (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) (a : Fin n) :
    dTau ε m (Matrix.single a a 1) (w0 ε m) = (((m a : ℝ)) : ℂ) • w0 ε m := by
  apply MV.ext
  funext x
  rw [dTau_fn, MV.fn_smul, Pi.smul_apply, smul_eq_mul]
  have h := rdc_f0K_wt ε hm a x
  rw [show (w0 ε m).fn = f0K ε m from rfl, h]
  push_cast
  ring

theorem derived_action_highest_vector (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) (a b : Fin n) (hab : a < b)
    (he : ε a = ε b) : dTau ε m (Matrix.single a b 1) (w0 ε m) = 0 := by
  apply MV.ext
  funext x
  rw [dTau_fn, MV.fn_zero, Pi.zero_apply]
  exact rdc_f0K_hw ε hm hab he x

theorem dTau_wt (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) (a : Fin n) :
    dTau ε m (Matrix.single a a 1) (wN ε m) = (((m a : ℝ)) : ℂ) • wN ε m := by
  unfold wN
  rw [map_smul, derived_action_weight_vector ε hm a, smul_comm]

theorem dTau_hw (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) (a b : Fin n) (hab : a < b)
    (he : ε a = ε b) : dTau ε m (Matrix.single a b 1) (wN ε m) = 0 := by
  unfold wN
  rw [map_smul, derived_action_highest_vector ε hm a b hab he, smul_zero]

theorem gen_wN (ε : Fin n → Bool) (m : Fin n → ℤ) (W : Submodule ℂ (MV ε m))
    (hW : ∀ k : KG ε, ∀ v ∈ W, ((tauM ε m k : unitary (MV ε m →L[ℂ] MV ε m)) : MV ε m →L[ℂ] MV ε m) v ∈ W)
    (hw : wN ε m ∈ W) : W = ⊤ := by
  have hn : ‖w0 ε m‖ ≠ 0 := norm_ne_zero_iff.mpr (highest_weight_vector_ne_zero ε m)
  have hw0 : w0 ε m ∈ W := by
    have h : w0 ε m = ((‖w0 ε m‖ : ℝ) : ℂ) • wN ε m := by
      unfold wN
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn, Complex.ofReal_one, one_smul]
    rw [h]
    exact W.smul_mem _ hw
  have htr : ∀ k : KG ε, rtr ε k (f0K ε m) ∈ W.map (mvFnL ε m) :=
    fun k => ⟨tauC ε m k (w0 ε m), hW k _ hw0, rfl⟩
  have hle : Vsp ε m ≤ W.map (mvFnL ε m) := by
    rw [Vsp, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact htr k
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := hle x.mem
  rw [← mvFnL_injective ε m hyx]
  exact hy

def modelKType (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) : KType ε (fun a => (m a : ℝ)) :=
  kTypeOfGen (MV ε m) (tauM ε m) (continuous_tauM ε m) (dTau ε m) (hasDeriv_dTau ε m) (wN ε m) (norm_wN ε m)
    (dTau_wt ε hm) (dTau_hw ε hm) (gen_wN ε m)

theorem model_exists (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) :
    Nonempty (KType ε (fun a => (m a : ℝ))) := ⟨modelKType ε hm⟩

end ReciprocityTheory.ChartRestriction.DS.HW
end
end
