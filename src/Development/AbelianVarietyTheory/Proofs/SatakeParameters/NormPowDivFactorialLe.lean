import Mathlib
import Formalism.FormalGroupWitt.FormalGroupWittProofs.SolveV
import Formalism.FormalGroupWitt.FormalGroupWittProofs.EqSingleOfDegreeEqOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Cobdry

noncomputable section

namespace GlobalTheory.BiextInhab

open MvPowerSeries Formalism.FG.SolveVAux

def laK (K : Type) [Field K] (l d : ℕ) (s : ZMod d) : MvPowerSeries (ZMod d) K :=
  fun n => ∑ e ∈ Finset.range ((n.sum fun _ k => k) + 1),
    if n = Finsupp.single (s - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e)) then ((l : K) ^ e)⁻¹ else 0

section Field

variable {K : Type} [Field K] {l d : ℕ}

theorem pow_two_mul_inj (hl : l.Prime) {a b : ℕ} (h : l ^ (2 * a) = l ^ (2 * b)) : a = b := by
  have := Nat.pow_right_injective hl.two_le h
  omega

theorem coeff_laK_single (hl : l.Prime) (j : ZMod d) (e : ℕ) :
    coeff (Finsupp.single (j - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e))) (laK K l d j) = ((l : K) ^ e)⁻¹ := by
  rw [coeff_apply]
  unfold laK
  rw [Finset.sum_eq_single e]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    have h2 := congrArg Finsupp.degree h
    simp only [Finsupp.degree_single] at h2
    exact hb (pow_two_mul_inj hl h2).symm
  · intro h
    exfalso
    apply h
    rw [Finset.mem_range, Finsupp.sum_single_index rfl]
    have := Nat.lt_pow_self (n := 2 * e) hl.one_lt
    omega

theorem coeff_laK_of_ne (j : ZMod d) (n : ZMod d →₀ ℕ)
    (h : ∀ e : ℕ, n ≠ Finsupp.single (j - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e))) :
    coeff n (laK K l d j) = 0 := by
  rw [coeff_apply]
  unfold laK
  exact Finset.sum_eq_zero fun e _ => if_neg (h e)

theorem map_laK {K' : Type} [Field K'] (σ : K →+* K') (j : ZMod d) :
    map σ (laK K l d j) = laK K' l d j := by
  ext n
  rw [coeff_map, coeff_apply, coeff_apply]
  unfold laK
  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp

theorem smul_single_shift (j : ZMod d) (e : ℕ) :
    (l ^ 2) • (Finsupp.single (j - 2 - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e)) : ZMod d →₀ ℕ)
      = Finsupp.single (j - ((2 * (e + 1) : ℕ) : ZMod d)) (l ^ (2 * (e + 1))) := by
  rw [Finsupp.smul_single, smul_eq_mul, ← pow_add]
  congr 1
  · push_cast
    ring
  · congr 1
    ring

open MvPowerSeries in
variable {K : Type} [Field K] {l d : ℕ} in
theorem _root_.GlobalTheory.BiextInhab.laK_idMod2 (hl : l.Prime) :
    _root_.Formalism.FG.IsIdMod2 (_root_.GlobalTheory.BiextInhab.laK K l d) := by
  refine ⟨fun j => ?_, fun j i => ?_⟩
  · show _root_.GlobalTheory.BiextInhab.laK K l d j 0 = 0
    unfold _root_.GlobalTheory.BiextInhab.laK
    refine Finset.sum_eq_zero fun e _ => if_neg fun h => ?_
    exact pow_ne_zero _ hl.ne_zero (Finsupp.single_eq_zero.mp h.symm)
  · show _root_.GlobalTheory.BiextInhab.laK K l d j (Finsupp.single i 1) = _
    unfold _root_.GlobalTheory.BiextInhab.laK
    rw [Finset.sum_eq_single 0]
    · simp [Finsupp.single_left_inj one_ne_zero]
    · intro e _ he
      refine if_neg fun h => he ?_
      have h1 := congrArg (fun f : ZMod d →₀ ℕ => f.sum fun _ k => k) h
      simp only [Finsupp.sum_single_index] at h1
      rcases Nat.pow_eq_one.mp h1.symm with h2 | h2
      · exact absurd h2 hl.ne_one
      · omega
    · intro h
      simp at h

theorem laK_funEq (hl : l.Prime) (j : ZMod d) :
    laK K l d j = X j + (l : K)⁻¹ • expand (l ^ 2) (pow_ne_zero 2 hl.ne_zero) (laK K l d (j - 2)) := by
  classical
  have hq : 1 < l ^ 2 := Nat.one_lt_pow two_ne_zero hl.one_lt
  ext n
  rw [map_add, map_smul, smul_eq_mul, coeff_X]
  by_cases h : ∃ e : ℕ, n = Finsupp.single (j - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e))
  · obtain ⟨e, rfl⟩ := h
    rw [coeff_laK_single hl]
    cases e with
    | zero =>
      rw [coeff_expand_of_not_dvd (i := j)]
      · simp
      · simp only [mul_zero, Nat.cast_zero, sub_zero, pow_zero, Finsupp.single_eq_same, Nat.dvd_one]
        omega
    | succ e =>
      rw [if_neg, ← smul_single_shift, coeff_expand_smul, coeff_laK_single hl, pow_succ', mul_inv, zero_add]
      intro h
      have h2 := congrArg Finsupp.degree h
      simp only [Finsupp.degree_single] at h2
      have := pow_two_mul_inj hl (b := 0) (h2.trans (by simp))
      omega
  · push Not at h
    rw [coeff_laK_of_ne j n h, if_neg (by simpa using h 0)]
    by_cases hd : ∀ i, l ^ 2 ∣ n i
    · have hn : n = (l ^ 2) • n.mapRange (· / l ^ 2) (Nat.zero_div _) := by
        ext i
        simp [Nat.mul_div_cancel' (hd i)]
      rw [hn, coeff_expand_smul, coeff_laK_of_ne]
      · simp
      · intro e he
        apply h (e + 1)
        rw [hn, he, smul_single_shift]
    · push Not at hd
      obtain ⟨i, hi⟩ := hd
      rw [coeff_expand_of_not_dvd _ _ _ hi]
      simp

theorem rescale_laK (hl : l.Prime) (w : ZMod d → K) (hw : ∀ s, w (s - 2) ^ (l ^ 2) = w s) (j : ZMod d) :
    rescale w (laK K l d j) = w j • laK K l d j := by
  have hw' : ∀ (e : ℕ) (s : ZMod d), w (s - ((2 * e : ℕ) : ZMod d)) ^ (l ^ (2 * e)) = w s := by
    intro e
    induction e with
    | zero => simp
    | succ e ih =>
      intro s
      rw [← hw s, ← ih (s - 2), ← pow_mul, ← pow_add]
      congr 2
      push_cast
      ring
  ext n
  rw [coeff_rescale, map_smul, smul_eq_mul]
  by_cases h : ∃ e : ℕ, n = Finsupp.single (j - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e))
  · obtain ⟨e, rfl⟩ := h
    rw [Finsupp.prod_single_index (by simp), hw']
  · push Not at h
    rw [coeff_laK_of_ne j n h, mul_zero, mul_zero]

variable [NeZero d]

def IsInv (l : ℕ) (h : ZMod d → MvPowerSeries (ZMod d) K) : Prop :=
  (∀ i, constantCoeff (h i) = 0) ∧ ∀ j, subst h (laK K l d j) = X j

theorem IsInv.subst_eq (hl : l.Prime) {h : ZMod d → MvPowerSeries (ZMod d) K} (hh : IsInv l h)
    {τ : Type} [Finite τ] {T Z : ZMod d → MvPowerSeries τ K} (hT : ∀ i, constantCoeff (T i) = 0)
    (hTZ : ∀ j, subst T (laK K l d j) = Z j) (j : ZMod d) : subst Z (h j) = T j := by
  have hZ : ∀ j, constantCoeff (Z j) = 0 := fun j => by
    rw [← hTZ]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hT) hT ((laK_idMod2 hl).1 j)
  have hZs := hasSubst_of_constantCoeff_zero hZ
  have hs := hasSubst_of_constantCoeff_zero hh.1
  have := Formalism.FG.subst_injective_vector K (ZMod d) τ (laK K l d) (fun j => subst Z (h j)) T
    (laK_idMod2 hl) (fun i => constantCoeff_subst_eq_zero hZs hZ (hh.1 i)) hT (fun j => by
      rw [← subst_comp_subst_apply hs hZs, hh.2, subst_X hZs, hTZ])
  exact congrFun this j

theorem IsInv.ne_zero (hl : l.Prime) {h : ZMod d → MvPowerSeries (ZMod d) K} (hh : IsInv l h) (j : ZMod d) :
    h j ≠ 0 := by
  intro h0
  have h1 := hh.subst_eq hl (T := X) (Z := laK K l d) (by simp) (fun j => by rw [subst_self]; rfl) j
  rw [h0, ← substAlgHom_apply (hasSubst_of_constantCoeff_zero (laK_idMod2 hl).1), map_zero] at h1
  have := congrArg (coeff (Finsupp.single j 1)) h1
  simp at this

theorem IsInv.rescale_eq (hl : l.Prime) {h : ZMod d → MvPowerSeries (ZMod d) K} (hh : IsInv l h)
    (w : ZMod d → K) (hw : ∀ s, w (s - 2) ^ (l ^ 2) = w s) (j : ZMod d) :
    rescale w (h j) = w j • h j := by
  have hs := hasSubst_of_constantCoeff_zero hh.1
  rw [rescale_eq_subst]
  refine hh.subst_eq hl (T := fun j => w j • h j) (fun i => by simp [hh.1 i]) (fun j => ?_) j
  have e : (fun j => w j • h j) = fun j => subst h ((w • X : ZMod d → MvPowerSeries (ZMod d) K) j) := by
    funext j
    rw [Pi.smul_apply', subst_smul hs, subst_X hs]
  rw [e, ← subst_comp_subst_apply (HasSubst.smul_X w) hs, ← rescale_eq_subst, rescale_laK hl w hw,
    subst_smul hs, hh.2, Pi.smul_apply']

end Field

section Padic

open Formalism.G

variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ} {τ : Type}

theorem exists_lift {F : MvPowerSeries τ ℚ_[l]} (hF : IntegralMv F) :
    ∃ G : MvPowerSeries τ ℤ_[l], map PadicInt.Coe.ringHom G = F :=
  ⟨fun n => ⟨coeff n F, hF n⟩, by ext n; rfl⟩

theorem integral_map (G : MvPowerSeries τ ℤ_[l]) : IntegralMv (map PadicInt.Coe.ringHom G) := fun n => by
  rw [coeff_map]; exact (coeff n G).2

theorem dvd_pow_sub_expand (B : MvPowerSeries τ ℤ_[l]) :
    (l : MvPowerSeries τ ℤ_[l]) ∣ B ^ (l ^ 2) - expand (l ^ 2) (pow_ne_zero 2 hl.out.ne_zero) B := by
  have h0 : map PadicInt.toZMod (B ^ (l ^ 2) - expand (l ^ 2) (pow_ne_zero 2 hl.out.ne_zero) B) = 0 := by
    have hid : iterateFrobenius (ZMod l) l 2 = RingHom.id _ := by
      refine RingHom.ext fun x => ?_
      rw [iterateFrobenius_def, ZMod.pow_card_pow, RingHom.id_apply]
    rw [map_sub, map_pow, map_expand, ← map_iterateFrobenius_expand l hl.out.ne_zero, hid, map_id]
    simp
  have h1 : ∀ n, ∃ c : ℤ_[l],
      coeff n (B ^ (l ^ 2) - expand (l ^ 2) (pow_ne_zero 2 hl.out.ne_zero) B) = l * c := by
    intro n
    have := congrArg (coeff n) h0
    rw [coeff_map, map_zero, ← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton] at this
    exact this
  choose c hc using h1
  refine ⟨c, ?_⟩
  ext n
  rw [hc]
  erw [← nsmul_eq_mul (α := MvPowerSeries τ ℤ_[l]), map_nsmul, nsmul_eq_mul]
  rfl

variable [NeZero d]

theorem norm_subst_sub_le {P Q : ZMod d → MvPowerSeries τ ℤ_[l]} (hP : ∀ i, constantCoeff (P i) = 0)
    (hQ : ∀ i, constantCoeff (Q i) = 0) (h : ∀ i, (l : MvPowerSeries τ ℤ_[l]) ∣ P i - Q i) (j : ZMod d) (n : τ →₀ ℕ) :
    ‖coeff n (subst (fun i => map PadicInt.Coe.ringHom (P i)) (laK ℚ_[l] l d j) -
      subst (fun i => map PadicInt.Coe.ringHom (Q i)) (laK ℚ_[l] l d j))‖ ≤ ‖(l : ℚ_[l])‖ := by
  have hPs : HasSubst (fun i => map PadicInt.Coe.ringHom (P i)) :=
    hasSubst_of_constantCoeff_zero fun i => by simp [hP i]
  have hQs : HasSubst (fun i => map PadicInt.Coe.ringHom (Q i)) :=
    hasSubst_of_constantCoeff_zero fun i => by simp [hQ i]
  rw [map_sub, coeff_subst hPs, coeff_subst hQs,
    ← finsum_sub_distrib (coeff_subst_finite hPs _ _) (coeff_subst_finite hQs _ _)]
  refine finsum_induction (fun x : ℚ_[l] => ‖x‖ ≤ ‖(l : ℚ_[l])‖) (by simp)
    (fun x y hx hy => (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)) fun m => ?_
  by_cases hm : ∃ e : ℕ, m = Finsupp.single (j - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e))
  · obtain ⟨e, rfl⟩ := hm
    obtain ⟨c, hc⟩ := dvd_sub_pow_of_dvd_sub (h (j - ((2 * e : ℕ) : ZMod d))) (2 * e)
    rw [coeff_laK_single hl.out, Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp),
      ← smul_sub, ← map_sub, ← map_pow, ← map_pow, ← map_sub, hc, coeff_map, ← Nat.cast_pow l (2 * e + 1),
      ← nsmul_eq_mul, map_nsmul, map_nsmul, nsmul_eq_mul, smul_eq_mul, Nat.cast_pow]
    have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
    have e1 : ((l : ℚ_[l]) ^ e)⁻¹ * ((l : ℚ_[l]) ^ (2 * e + 1) * PadicInt.Coe.ringHom (coeff n c)) =
        (l : ℚ_[l]) * ((l : ℚ_[l]) ^ e * PadicInt.Coe.ringHom (coeff n c)) := by
      field_simp
      ring
    rw [e1, norm_mul, norm_mul, norm_pow]
    refine mul_le_of_le_one_right (norm_nonneg _) (mul_le_one₀ (pow_le_one₀ (norm_nonneg _) ?_) (norm_nonneg _) (coeff n c).2)
    exact Padic.norm_p_lt_one.le
  · push Not at hm
    simp [coeff_laK_of_ne j m hm]

theorem funEq_subst {P : ZMod d → MvPowerSeries τ ℚ_[l]} (hP0 : ∀ i, constantCoeff (P i) = 0)
    (hP : ∀ i, IntegralMv (P i)) (j : ZMod d) :
    IntegralMv (subst P (laK ℚ_[l] l d j) -
      (l : ℚ_[l])⁻¹ • expand (l ^ 2) (pow_ne_zero 2 hl.out.ne_zero) (subst P (laK ℚ_[l] l d (j - 2)))) := by
  have hq : l ^ 2 ≠ 0 := pow_ne_zero 2 hl.out.ne_zero
  have hs := hasSubst_of_constantCoeff_zero hP0
  choose G hG using fun i => exists_lift (hP i)
  have hG0 : ∀ i, constantCoeff (G i) = 0 := fun i => by
    have := hP0 i
    rw [← hG, constantCoeff_map] at this
    exact Subtype.ext this
  have key := norm_subst_sub_le (P := fun i => G i ^ (l ^ 2)) (Q := fun i => expand (l ^ 2) hq (G i))
    (fun i => by simp [hG0 i, hl.out.ne_zero]) (fun i => by simp [hG0 i]) (fun i => dvd_pow_sub_expand (G i)) (j - 2)
  simp only [map_pow, map_expand, hG] at key
  have e1 : subst P (expand (l ^ 2) hq (laK ℚ_[l] l d (j - 2))) =
      subst (fun i => P i ^ (l ^ 2)) (laK ℚ_[l] l d (j - 2)) := by
    rw [expand, substAlgHom_apply, subst_comp_subst_apply (HasSubst.X_pow hq) hs]
    simp only [subst_pow hs, subst_X hs]
  intro n
  rw [laK_funEq hl.out j, subst_add hs, subst_X hs, subst_smul hs, e1, expand_subst _ _ hs, add_sub_assoc,
    ← smul_sub, map_add, map_smul, smul_eq_mul]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hP j n) ?_)
  have hl0 : 0 < ‖(l : ℚ_[l])‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.out.ne_zero)
  rw [norm_mul, norm_inv, inv_mul_le_iff₀ hl0, mul_one]
  exact key n

theorem integral_of_funEq {T : ZMod d → MvPowerSeries τ ℚ_[l]} (hT0 : ∀ i, constantCoeff (T i) = 0)
    (hT : ∀ j, IntegralMv (subst T (laK ℚ_[l] l d j) -
      (l : ℚ_[l])⁻¹ • expand (l ^ 2) (pow_ne_zero 2 hl.out.ne_zero) (subst T (laK ℚ_[l] l d (j - 2))))) (j : ZMod d) :
    IntegralMv (T j) := by
  classical
  have hq : l ^ 2 ≠ 0 := pow_ne_zero 2 hl.out.ne_zero
  have hq1 : 1 < l ^ 2 := Nat.one_lt_pow two_ne_zero hl.out.one_lt
  have hf := laK_idMod2 (K := ℚ_[l]) (d := d) hl.out
  suffices H : ∀ (k : ℕ) (j : ZMod d) (n : τ →₀ ℕ), n.degree = k → ‖coeff n (T j)‖ ≤ 1 from fun n => H _ j n rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro j n hn
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [(Finsupp.degree_eq_zero_iff n).1 hn, coeff_zero_eq_constantCoeff_apply, hT0]
      simp
    let P : ZMod d → MvPowerSeries τ ℚ_[l] := fun i m => if m.degree < k then coeff m (T i) else 0
    have hPc : ∀ i m, coeff m (P i) = if m.degree < k then coeff m (T i) else 0 := fun _ _ => rfl
    have hP0 : ∀ i, constantCoeff (P i) = 0 := fun i => by
      rw [← coeff_zero_eq_constantCoeff_apply, hPc, coeff_zero_eq_constantCoeff_apply, hT0, ite_self]
    have hP : ∀ i, IntegralMv (P i) := fun i m => by
      rw [hPc]
      split_ifs with h
      · exact ih _ h i m rfl
      · simp
    have hlow : ∀ i, Low k (T i - P i) := fun i m hm => by rw [map_sub, hPc, if_pos hm, sub_self]
    have hTs := hasSubst_of_constantCoeff_zero hT0
    have hPs := hasSubst_of_constantCoeff_zero hP0
    have hg : ∀ i, Low 2 (laK ℚ_[l] l d i - X i) := by
      intro i m hm
      rw [map_sub]
      rcases Nat.eq_zero_or_pos m.degree with h0 | h0
      · rw [(Finsupp.degree_eq_zero_iff m).1 h0, coeff_zero_eq_constantCoeff_apply, hf.1]
        simp
      · obtain ⟨a, rfl⟩ := degree_eq_one m (by omega)
        rw [hf.2, coeff_X]
        simp [Finsupp.single_left_inj]
    have hD : ∀ i, Low (k + 1) (subst T (laK ℚ_[l] l d i) - subst P (laK ℚ_[l] l d i) - (T i - P i)) := by
      intro i
      have := low_subst_sub (fun i => (low_one_iff _).2 (hT0 i)) (fun i => (low_one_iff _).2 (hP0 i)) hlow (hg i)
      rw [subst_sub hTs, subst_sub hPs, subst_X hTs, subst_X hPs] at this
      convert this using 1
      ring
    have hD' : ∀ i, Low k (subst T (laK ℚ_[l] l d i) - subst P (laK ℚ_[l] l d i)) := fun i => by
      simpa using low_add (low_mono (Nat.le_succ k) (hD i)) (hlow i)
    have hE : coeff n (expand (l ^ 2) hq
        (subst T (laK ℚ_[l] l d (j - 2)) - subst P (laK ℚ_[l] l d (j - 2)))) = 0 := by
      by_cases hd : ∀ i, l ^ 2 ∣ n i
      · obtain ⟨m, rfl⟩ : ∃ m : τ →₀ ℕ, (l ^ 2) • m = n := ⟨n.mapRange (fun a => a / l ^ 2) (by simp),
          by ext i; simp [Nat.mul_div_cancel' (hd i)]⟩
        rw [coeff_expand_smul]
        refine hD' _ m ?_
        rw [map_nsmul, smul_eq_mul] at hn
        nlinarith
      · push Not at hd
        obtain ⟨i, hi⟩ := hd
        exact coeff_expand_of_not_dvd _ _ _ hi
    have h1 := hD j n (by omega)
    have h2 := hT j n
    have h3 := funEq_subst hP0 hP j n
    have h4 : coeff n (P j) = 0 := by rw [hPc, if_neg (by omega)]
    simp only [map_sub, map_smul, smul_eq_mul] at h1 h2 h3 hE
    rw [h4] at h1
    have h5 := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 ((norm_neg _).trans_le h3))
    refine le_of_eq_of_le (congrArg norm ?_) h5
    linear_combination (-1 : ℚ_[l]) * h1 + (l : ℚ_[l])⁻¹ * hE

end Padic

section Main

open GlobalTheory.ThStr Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ}

theorem algebraMap_mem_Wp {x : ℚ_[l]} (hx : ‖x‖ ≤ 1) : algebraMap ℚ_[l] ℂ_[l] x ∈ Wp l := by
  have hc : Continuous fun c : ℤ_[l] => algebraMap ℚ_[l] ℂ_[l] (c : ℚ_[l]) :=
    (continuous_algebraMap ℚ_[l] ℂ_[l]).comp continuous_subtype_val
  have hcl : IsClosed {c : ℤ_[l] | algebraMap ℚ_[l] ℂ_[l] (c : ℚ_[l]) ∈ Wp l} :=
    (Subring.isClosed_topologicalClosure _).preimage hc
  have := PadicInt.denseRange_natCast.induction_on (p := fun c : ℤ_[l] => algebraMap ℚ_[l] ℂ_[l] (c : ℚ_[l]) ∈ Wp l)
    ⟨x, hx⟩ hcl (fun n => by simp)
  exact this


def serW (l : ℕ) [Fact l.Prime] (κ : Type) : Subring (MvPowerSeries κ ℂ_[l]) :=
  (MvPowerSeries.map (σ := κ) (Wp l).subtype).range

open MvPowerSeries in
variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ} in
theorem _root_.GlobalTheory.BiextInhab.mem_serW {κ : Type} {F : MvPowerSeries κ ℂ_[l]} :
    F ∈ _root_.GlobalTheory.BiextInhab.serW l κ ↔ _root_.Formalism.MainNotions.GL3Theta.IntegralW F := by
  constructor
  · rintro ⟨G, rfl⟩ n
    exact (coeff n G).2
  · intro h
    exact ⟨fun n => ⟨coeff n F, h n⟩, by ext n; rfl⟩



variable [NeZero d]

theorem exists_integral_point (a b : ZMod d → ℕ) (ha : ∀ s, a (s - 2) = a s) (hb : ∀ s, b (s - 2) = b s) :
    ∃ T : ZMod d → MvPowerSeries (Bool × ZMod d) ℂ_[l], (∀ s, constantCoeff (T s) = 0) ∧ (∀ s, T s ∈ serW l _) ∧
      ∀ s, subst T (laK ℂ_[l] l d s) = a s • laAt (fun r => (false, r)) s + b s • laAt (fun r => (true, r)) s := by
  have hq : l ^ 2 ≠ 0 := pow_ne_zero 2 hl.out.ne_zero
  have hf := laK_idMod2 (K := ℚ_[l]) (d := d) hl.out
  have hX : ∀ c : Bool, ∀ r : ZMod d, constantCoeff (X (c, r) : MvPowerSeries (Bool × ZMod d) ℚ_[l]) = 0 := by simp
  have hXs := fun c => hasSubst_of_constantCoeff_zero (hX c)
  let z : Bool → ZMod d → MvPowerSeries (Bool × ZMod d) ℚ_[l] := fun c s =>
    subst (fun r : ZMod d => (X (c, r) : MvPowerSeries (Bool × ZMod d) ℚ_[l])) (laK ℚ_[l] l d s)
  have hz0 : ∀ c s, constantCoeff (z c s) = 0 := fun c s =>
    constantCoeff_subst_eq_zero (hXs c) (hX c) (hf.1 s)
  have hz : ∀ c s, z c s = X (c, s) + (l : ℚ_[l])⁻¹ • expand (l ^ 2) hq (z c (s - 2)) := by
    intro c s
    simp only [z]
    rw [laK_funEq hl.out s, subst_add (hXs c), subst_X (hXs c), subst_smul (hXs c), expand_subst _ _ (hXs c),
      expand, substAlgHom_apply, subst_comp_subst_apply (HasSubst.X_pow hq) (hXs c)]
    simp only [subst_pow (hXs c), subst_X (hXs c), expand_X]
  obtain ⟨T, hT0, hT⟩ := Formalism.FG.solve_exists_vector ℚ_[l] (ZMod d) (Bool × ZMod d) (laK ℚ_[l] l d)
    (fun s => a s • z false s + b s • z true s) hf (fun s => by simp [hz0])
  have hint := integral_of_funEq hT0 (fun j => by
    have e : subst T (laK ℚ_[l] l d j) - (l : ℚ_[l])⁻¹ • expand (l ^ 2) hq (subst T (laK ℚ_[l] l d (j - 2))) =
        map PadicInt.Coe.ringHom (a j • X (false, j) + b j • X (true, j)) := by
      rw [hT, hT, ha, hb, hz false j, hz true j]
      simp only [map_add, map_nsmul, map_X]
      module
    rw [e]
    exact integral_map _)
  refine ⟨fun s => map (algebraMap ℚ_[l] ℂ_[l]) (T s), fun s => by simp [hT0], fun s => mem_serW.2 fun n => ?_, fun s => ?_⟩
  · rw [coeff_map]
    exact algebraMap_mem_Wp (hint s n)
  · rw [← map_laK (algebraMap ℚ_[l] ℂ_[l]), ← map_subst (hasSubst_of_constantCoeff_zero hT0), hT]
    simp only [map_add, map_nsmul, z, map_subst (hXs _), map_laK, map_X]
    rfl

theorem exists_isInv : ∃ h : ZMod d → MvPowerSeries (ZMod d) ℚ_[l],
    IsInv l fun s => map (algebraMap ℚ_[l] ℂ_[l]) (h s) := by
  obtain ⟨h, h0, hh⟩ := Formalism.FG.solve_exists_vector ℚ_[l] (ZMod d) (ZMod d) (laK ℚ_[l] l d) X
    (laK_idMod2 hl.out) (by simp)
  refine ⟨h, fun s => by simp [h0], fun s => ?_⟩
  rw [← map_laK (algebraMap ℚ_[l] ℂ_[l]), ← map_subst (hasSubst_of_constantCoeff_zero h0), hh, map_X]

omit hl in
theorem val_sub_two_mod (s : ZMod d) : (s - 2).val + 2 ≡ s.val [MOD d] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  simp

omit hl in
theorem even_val_sub_two (hd : Even d) (s : ZMod d) : Even (s - 2).val ↔ Even s.val := by
  have := (val_sub_two_mod s).of_dvd hd.two_dvd
  unfold Nat.ModEq at this
  rw [Nat.even_iff, Nat.even_iff]
  omega


def beOf (M : ℕ) (h : ZMod d → MvPowerSeries (ZMod d) ℂ_[l]) : MvPowerSeries (ZMod d) ℂ_[l] :=
  (l : MvPowerSeries (ZMod d) ℂ_[l]) * (h 0 * h 1) ^ M




omit hl [NeZero d] in
theorem parDeg_add (n : ZMod d →₀ ℕ) : parDeg true n + parDeg false n = n.degree := by
  rw [parDeg, parDeg, Finsupp.sum, Finsupp.sum, ← Finset.sum_add_distrib, Finsupp.degree_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : Even s.val <;> simp [h]


open MvPowerSeries in
variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ} in
variable [NeZero d] in
private theorem coeff_mapDomain_rename_of_injective {σ τ R : Type} [CommSemiring R] (f : σ → τ)
    [Filter.TendstoCofinite f] (hf : Function.Injective f) (p : MvPowerSeries σ R)
    (n : σ →₀ ℕ) : coeff (Finsupp.mapDomain f n) (rename f p) = coeff n p := by
  rw [coeff_rename, Finset.sum_eq_single n]
  · intro y hy hne
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hy
    exact absurd (Finsupp.mapDomain_injective hf hy) hne
  · intro hn
    exact absurd (by simp) hn

open MvPowerSeries in
variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ} in
variable [NeZero d] in

theorem _root_.GlobalTheory.BiextInhab.bridge (l : ℕ) [Fact l.Prime] (d : ℕ) [NeZero d]
    {β : Type} (b : β) (s : ZMod d) :
    _root_.GlobalTheory.ThStr.laAt (l := l) (fun r : ZMod d => (r, b)) s =
      _root_.Formalism.BasicNotions.jetLogG l d (s, b) := by
  have hinj : Function.Injective (fun r : ZMod d => (r, b)) := fun x y h => (Prod.mk.inj h).1
  have hren : _root_.GlobalTheory.ThStr.laAt (l := l) (fun r : ZMod d => (r, b)) s =
      rename (fun r : ZMod d => (r, b)) (_root_.GlobalTheory.ThStr.laS l d s) := by
    rw [rename_eq_subst]
    rfl
  have hsingle : ∀ e : ℕ, (Finsupp.single (s - 2 * (e : ZMod d), b) ((l ^ 2) ^ e) :
      ZMod d × β →₀ ℕ) = Finsupp.mapDomain (fun r : ZMod d => (r, b))
        (Finsupp.single (s - ((2 * e : ℕ) : ZMod d)) (l ^ (2 * e))) := by
    intro e
    rw [Finsupp.mapDomain_single, pow_mul]
    push_cast
    rfl
  rw [hren]
  ext m
  by_cases hm : m ∈ Set.range (Finsupp.mapDomain (fun r : ZMod d => (r, b)))
  · obtain ⟨n, rfl⟩ := hm
    have hdeg : _root_.Formalism.BasicNotions.JetTdeg (Finsupp.mapDomain (fun r : ZMod d => (r, b)) n) =
        n.sum fun _ k => k := by
      unfold _root_.Formalism.BasicNotions.JetTdeg
      exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)
    rw [coeff_mapDomain_rename_of_injective _ hinj]
    show _root_.GlobalTheory.ThStr.laS l d s n =
      _root_.Formalism.BasicNotions.jetLogG l d (s, b) (Finsupp.mapDomain (fun r : ZMod d => (r, b)) n)
    unfold _root_.GlobalTheory.ThStr.laS _root_.Formalism.BasicNotions.jetLogG
    dsimp only
    rw [hdeg]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [hsingle e, (Finsupp.mapDomain_injective hinj).eq_iff]
  · rw [coeff_rename_eq_zero _ _ hm]
    show (0 : ℂ_[l]) = _root_.Formalism.BasicNotions.jetLogG l d (s, b) m
    unfold _root_.Formalism.BasicNotions.jetLogG
    dsimp only
    symm
    refine Finset.sum_eq_zero fun e _ => if_neg ?_
    rintro rfl
    exact hm ⟨_, (hsingle e).symm⟩


end Main

end GlobalTheory.BiextInhab
