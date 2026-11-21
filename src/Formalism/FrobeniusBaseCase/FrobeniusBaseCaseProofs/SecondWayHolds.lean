import Formalism.FrobeniusBaseCase.Statement
import Formalism.FrobeniusBaseCase.FrobeniusBaseCaseProofs.HasUniqueFixedPoint

section
namespace Formalism.BaseCaseIdentities




theorem sqMulIdentity_statement : SqMulIdentity := by
  intro l hl
  have h2 : (2:ℝ) ≤ l := by exact_mod_cast hl
  have hq : ((l:ℝ)^2 - 1) ≠ 0 := by nlinarith
  unfold qnum rho; field_simp; ring

theorem identity_twenty_d : PowMulThreeEighthsIdentity := by
  intro l i hl hi
  obtain ⟨t, rfl⟩ := hi
  have h2 : (2:ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (l:ℝ) ≠ 0 := by linarith
  have hs : Kn (2 * t + 1) = t + 1 := by unfold Kn; omega
  rw [hs]
  unfold qnum sg; field_simp; ring

theorem eNum_eq_sum {l : ℕ} (hl : 2 ≤ l) (s : ℕ) :
    eNum l s = ∑ j ∈ Finset.range s, (l ^ 2) ^ j := by
  have : 2 ≤ l ^ 2 := by nlinarith
  unfold eNum; rw [Nat.geomSum_eq this]

theorem identity_e : IdE := by
  intro l s hl
  have hq : 2 ≤ l ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [eNum_eq_sum hl]; simp
  · rw [eNum_eq_sum hl, eNum_eq_sum hl, Finset.sum_range_succ', Finset.mul_sum]
    simp only [pow_succ, pow_zero]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  · rw [eNum_eq_sum hl]
    have := geom_sum_mul_add (l ^ 2 - 1) s
    rwa [Nat.sub_add_cancel (by omega)] at this

theorem rho_pos {l : ℕ} (hl : 3 ≤ l) : 0 < rho l := by
  have h2 : (3:ℝ) ≤ l := by exact_mod_cast hl
  unfold rho
  have : (0:ℝ) < (l:ℝ)^2 - 1 := by nlinarith
  positivity

theorem rho_mul {l : ℕ} (hl : 3 ≤ l) : ((l:ℝ)^2 - 1) * rho l = 1 := by
  have h2 : (3:ℝ) ≤ l := by exact_mod_cast hl
  have hq : ((l:ℝ)^2 - 1) ≠ 0 := by nlinarith
  unfold rho; field_simp

theorem num_c {l : ℕ} (hl : 3 ≤ l) {j : ℕ} (hj : 3 ≤ j) :
    1 + rho l ≤ -((j:ℝ) - 1) + (l:ℝ)^j * rho l := by
  have h2 : (3:ℝ) ≤ l := by exact_mod_cast hl
  have hr := rho_pos hl
  have hm := rho_mul hl
  induction j, hj using Nat.le_induction with
  | base =>
    have h3 : 0 ≤ ((l:ℝ)^3 - 1 - 3 * ((l:ℝ)^2 - 1)) * rho l := by
      apply mul_nonneg _ hr.le
      nlinarith [mul_nonneg (sq_nonneg (l:ℝ)) (sub_nonneg.2 h2)]
    push_cast
    nlinarith
  | succ j hj ih =>
    have h4 : (l:ℝ)^2 ≤ (l:ℝ)^j := pow_le_pow_right₀ (by linarith) (by omega)
    have h5 : 0 ≤ ((l:ℝ)^j * ((l:ℝ) - 1) - ((l:ℝ)^2 - 1)) * rho l := by
      apply mul_nonneg _ hr.le
      nlinarith
    push_cast
    rw [pow_succ]
    nlinarith

theorem num_d {l : ℕ} (hl : 3 ≤ l) {j : ℕ} (hj : 1 ≤ j) :
    1 + rho l ≤ -(j:ℝ) + (l:ℝ)^j * (1 + rho l) := by
  have h2 : (3:ℝ) ≤ l := by exact_mod_cast hl
  have hr := rho_pos hl
  induction j, hj using Nat.le_induction with
  | base => push_cast; nlinarith
  | succ j hj ih =>
    have h4 : (1:ℝ) ≤ (l:ℝ)^j := one_le_pow₀ (by linarith)
    have h5 : 1 ≤ (l:ℝ)^j * (((l:ℝ) - 1) * (1 + rho l)) := by
      have : 1 ≤ ((l:ℝ) - 1) * (1 + rho l) := by nlinarith
      nlinarith
    push_cast
    rw [pow_succ]
    nlinarith

theorem num_good {l : ℕ} (hl : 3 ≤ l) {j : ℕ} (hj : 2 ≤ j) :
    1 + rho l ≤ -((j:ℝ) - 1) + (l:ℝ)^j * (1 + rho l) := by
  have := num_d hl (j := j) (by omega)
  linarith

end Formalism.BaseCaseIdentities
end

section
open MvPowerSeries

namespace Formalism.BaseCaseIdentities

variable {k : Type*} [Field k] {Z : Type*} {v : AddValuation k (WithTop ℝ)}
  {r w w' w1 w2 wa wb a₀ : ℝ} {f g a b : MvPowerSeries Z k}

theorem le_add_coe_iff (x : WithTop ℝ) (w c : ℝ) :
    (w : WithTop ℝ) ≤ x + (c : WithTop ℝ) ↔ ((w - c : ℝ) : WithTop ℝ) ≤ x := by
  induction x using WithTop.recTopCoe with
  | top => simp
  | coe y => rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe, sub_le_iff_le_add]

theorem hasWt_iff : HasWt v r w f ↔
    ∀ A : Z →₀ ℕ, ((w - ((A.degree : ℕ) : ℝ) * r : ℝ) : WithTop ℝ) ≤ v (coeff A f) := by
  unfold HasWt
  exact forall_congr' fun A => le_add_coe_iff _ _ _

theorem HasWt.mono (h : w' ≤ w) (hf : HasWt v r w f) : HasWt v r w' f := by
  rw [hasWt_iff] at *
  intro A
  refine le_trans ?_ (hf A)
  exact WithTop.coe_le_coe.2 (by linarith)

theorem HasWt.zero : HasWt v r w (0 : MvPowerSeries Z k) := by
  rw [hasWt_iff]; intro A; simp

theorem HasWt.add (hf : HasWt v r w f) (hg : HasWt v r w g) : HasWt v r w (f + g) := by
  rw [hasWt_iff] at *
  intro A
  rw [map_add]
  exact le_trans (le_min (hf A) (hg A)) (v.map_add _ _)

theorem HasWt.neg (hf : HasWt v r w f) : HasWt v r w (-f) := by
  rw [hasWt_iff] at *
  intro A
  rw [map_neg, v.map_neg]
  exact hf A

theorem HasWt.sub (hf : HasWt v r w f) (hg : HasWt v r w g) : HasWt v r w (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem HasWt.sum {ι : Type*} (s : Finset ι) {F : ι → MvPowerSeries Z k}
    (h : ∀ i ∈ s, HasWt v r w (F i)) : HasWt v r w (∑ i ∈ s, F i) := by
  rw [hasWt_iff]
  intro A
  rw [map_sum]
  exact v.map_le_sum fun i hi => (hasWt_iff.1 (h i hi)) A

theorem HasWt.mul (hf : HasWt v r w1 f) (hg : HasWt v r w2 g) : HasWt v r (w1 + w2) (f * g) := by
  classical
  rw [hasWt_iff] at *
  intro A
  rw [coeff_mul]
  refine v.map_le_sum fun p hp => ?_
  rw [v.map_mul]
  have hA : A = p.1 + p.2 := (Finset.HasAntidiagonal.mem_antidiagonal.1 hp).symm
  have hd : ((A.degree : ℕ) : ℝ) = ((p.1.degree : ℕ) : ℝ) + ((p.2.degree : ℕ) : ℝ) := by
    rw [hA, map_add]; push_cast; ring
  have : ((w1 + w2 - ((A.degree : ℕ) : ℝ) * r : ℝ) : WithTop ℝ)
      = ((w1 - ((p.1.degree : ℕ) : ℝ) * r : ℝ) : WithTop ℝ)
        + ((w2 - ((p.2.degree : ℕ) : ℝ) * r : ℝ) : WithTop ℝ) := by
    rw [← WithTop.coe_add, hd]; congr 1; ring
  rw [this]
  exact add_le_add (hf p.1) (hg p.2)

theorem HasWt.C_mul {x : k} (hx : ((a₀ : ℝ) : WithTop ℝ) ≤ v x) (hf : HasWt v r w f) :
    HasWt v r (a₀ + w) (C x * f) := by
  rw [hasWt_iff] at *
  intro A
  rw [coeff_C_mul, v.map_mul]
  have : ((a₀ + w - ((A.degree : ℕ) : ℝ) * r : ℝ) : WithTop ℝ)
      = ((a₀ : ℝ) : WithTop ℝ) + ((w - ((A.degree : ℕ) : ℝ) * r : ℝ) : WithTop ℝ) := by
    rw [← WithTop.coe_add]; congr 1; ring
  rw [this]
  exact add_le_add hx (hf A)

theorem HasWt.mul_C {x : k} (hx : ((a₀ : ℝ) : WithTop ℝ) ≤ v x) (hf : HasWt v r w f) :
    HasWt v r (a₀ + w) (f * C x) := by
  rw [mul_comm]; exact hf.C_mul hx

theorem HasWt.one : HasWt v r 0 (1 : MvPowerSeries Z k) := by
  classical
  rw [hasWt_iff]
  intro A
  rw [coeff_one]
  split_ifs with h
  · subst h; simp
  · simp

theorem HasWt.pow (hf : HasWt v r w f) (n : ℕ) : HasWt v r ((n : ℝ) * w) (f ^ n) := by
  induction n with
  | zero => simpa using (HasWt.one : HasWt v r 0 (1 : MvPowerSeries Z k))
  | succ n ih =>
    rw [pow_succ]
    have := ih.mul hf
    convert this using 1
    push_cast; ring

theorem HasWt.X (d : Z) : HasWt v r r (X d : MvPowerSeries Z k) := by
  classical
  rw [hasWt_iff]
  intro A
  rw [coeff_X]
  split_ifs with h
  · subst h; simp
  · simp

theorem coeff_frob_of_dvd {N : ℕ} {B : Z →₀ ℕ} (h : ∀ d, N ∣ B d) (f : MvPowerSeries Z k) :
    coeff B (frob N f) = (coeff (B.mapRange (· / N) (Nat.zero_div N)) f) ^ N := by
  show frob N f B = _
  unfold frob
  rw [if_pos h]

theorem coeff_frob_of_not_dvd {N : ℕ} {B : Z →₀ ℕ} (h : ¬ ∀ d, N ∣ B d) (f : MvPowerSeries Z k) :
    coeff B (frob N f) = 0 := by
  show frob N f B = _
  unfold frob
  rw [if_neg h]

theorem smul_mapRange_div {N : ℕ} {B : Z →₀ ℕ} (h : ∀ d, N ∣ B d) :
    N • (B.mapRange (· / N) (Nat.zero_div N)) = B := by
  ext d
  simp only [Finsupp.coe_smul, Pi.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
  exact Nat.mul_div_cancel' (h d)

theorem HasWt.frob (hf : HasWt v r w f) (N : ℕ) : HasWt v r ((N : ℝ) * w) (frob N f) := by
  rw [hasWt_iff] at *
  intro B
  by_cases h : ∀ d, N ∣ B d
  · rw [coeff_frob_of_dvd h, v.map_pow]
    set B' := B.mapRange (· / N) (Nat.zero_div N) with hB'
    have hB : B = N • B' := (smul_mapRange_div h).symm
    have hd : ((B.degree : ℕ) : ℝ) = (N : ℝ) * ((B'.degree : ℕ) : ℝ) := by
      rw [hB, map_nsmul]; simp
    have h1 := nsmul_le_nsmul_right (hf B') N
    refine le_trans (le_of_eq ?_) h1
    rw [← WithTop.coe_nsmul, hd]
    congr 1
    rw [nsmul_eq_mul]; ring
  · rw [coeff_frob_of_not_dvd h]; simp

theorem frob_zero {N : ℕ} (hN : 1 ≤ N) : frob N (0 : MvPowerSeries Z k) = 0 := by
  ext B
  by_cases h : ∀ d, N ∣ B d
  · rw [coeff_frob_of_dvd h]; simp; omega
  · rw [coeff_frob_of_not_dvd h]; simp

theorem v_natCast_nonneg (v : AddValuation k (WithTop ℝ)) (n : ℕ) : 0 ≤ v (n : k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    refine le_trans (le_min ih ?_) (v.map_add _ _)
    rw [v.map_one]

theorem HasWt.natCast_mul {l n : ℕ} (hv : v (l : k) = 1) (hd : l ∣ n) (hf : HasWt v r w f) :
    HasWt v r (1 + w) ((n : MvPowerSeries Z k) * f) := by
  have h1 : (n : MvPowerSeries Z k) = C (n : k) := (map_natCast C n).symm
  rw [h1]
  refine hf.C_mul ?_
  obtain ⟨m, rfl⟩ := hd
  push_cast
  rw [v.map_mul, hv]
  have := v_natCast_nonneg v m
  calc (1 : WithTop ℝ) = 1 + 0 := by simp
    _ ≤ 1 + v (m : k) := by gcongr

theorem hasWt_add_pow_sub_pow {l q : ℕ} (hv : v (l : k) = 1) (hq : 1 ≤ q)
    (hdiv : ∀ m, 0 < m → m < q → l ∣ q.choose m) (hw : wa ≤ wb)
    (ha : HasWt v r wa a) (hb : HasWt v r wb b) :
    HasWt v r (1 + ((q : ℝ) - 1) * wa + wb) ((a + b) ^ q - a ^ q - b ^ q) := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  have key : (a + b) ^ (p + 1) - a ^ (p + 1) - b ^ (p + 1)
      = ∑ m ∈ Finset.range p, ((p + 1).choose (m + 1) : MvPowerSeries Z k)
          * (a ^ (m + 1) * b ^ (p + 1 - (m + 1))) := by
    rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_zero,
      one_mul, Nat.choose_zero_right]
    rw [add_sub_cancel_right, add_sub_cancel_right]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [key]
  refine HasWt.sum _ fun m hm => ?_
  have hm' : m < p := Finset.mem_range.1 hm
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hm'
  have h1 := ((ha.pow (m + 1)).mul (hb.pow (m + j + 1 + 1 - (m + 1)))).natCast_mul hv
    (hdiv (m + 1) (by omega) (by omega))
  refine h1.mono ?_
  have h2 : m + j + 1 + 1 - (m + 1) = j + 1 := by omega
  rw [h2]
  push_cast
  have : 0 ≤ (j : ℝ) * (wb - wa) := mul_nonneg (Nat.cast_nonneg j) (by linarith)
  nlinarith

theorem hasWt_add_pow_sub {l e : ℕ} (hl : l.Prime) (hv : v (l : k) = 1) (hw : wa ≤ wb)
    (ha : HasWt v r wa a) (hb : HasWt v r wb b) :
    HasWt v r (1 + (((l ^ e : ℕ) : ℝ) - 1) * wa + wb)
      ((a + b) ^ (l ^ e) - a ^ (l ^ e) - b ^ (l ^ e)) :=
  hasWt_add_pow_sub_pow hv (Nat.one_le_pow _ _ hl.pos)
    (fun m h0 h1 => hl.dvd_choose_pow (by omega) (by omega)) hw ha hb

theorem hasWt_sum_pow_sub {ι : Type*} {l e : ℕ} (hl : l.Prime) (hv : v (l : k) = 1) (_he : 1 ≤ e)
    (s : Finset ι) {F : ι → MvPowerSeries Z k} (h : ∀ i ∈ s, HasWt v r w (F i)) :
    HasWt v r (1 + ((l ^ e : ℕ) : ℝ) * w) ((∑ i ∈ s, F i) ^ (l ^ e) - ∑ i ∈ s, (F i) ^ (l ^ e)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : l ^ e ≠ 0 := pow_ne_zero _ hl.ne_zero
    rw [Finset.sum_empty, Finset.sum_empty, zero_pow this, sub_zero]
    exact HasWt.zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have h1 := hasWt_add_pow_sub (e := e) hl hv le_rfl (h i (Finset.mem_insert_self i s))
      (HasWt.sum s fun j hj => h j (Finset.mem_insert_of_mem hj))
    have h2 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have h3 := (h1.mono (w' := 1 + ((l ^ e : ℕ) : ℝ) * w) (by linarith)).add h2
    convert h3 using 1
    ring

theorem coeff_sum_C_mul_X_pow [Fintype Z] [DecidableEq Z] (y : Z → k) (M : ℕ) (B : Z →₀ ℕ) :
    coeff B (∑ d, C (y d) * X d ^ M : MvPowerSeries Z k)
      = ∑ d, if B = Finsupp.single d M then y d else 0 := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [coeff_C_mul, coeff_X_pow]
  split_ifs <;> simp

theorem frob_sum_X [Fintype Z] {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M) (x : Z → k) :
    frob N (∑ d, C (x d) * X d ^ M) = ∑ d, C (x d ^ N) * X d ^ (N * M) := by
  classical
  ext B
  rw [coeff_sum_C_mul_X_pow]
  by_cases hB : ∃ d0, B = Finsupp.single d0 (N * M)
  · obtain ⟨d0, rfl⟩ := hB
    have h1 : ∀ d, N ∣ (Finsupp.single d0 (N * M)) d := by
      intro d
      by_cases h : d0 = d
      · subst h; simp
      · simp [h]
    have h2 : (Finsupp.single d0 (N * M)).mapRange (· / N) (Nat.zero_div N)
        = Finsupp.single d0 M := by
      rw [Finsupp.mapRange_single]
      congr 1
      exact Nat.mul_div_cancel_left M (by omega)
    rw [coeff_frob_of_dvd h1, h2, coeff_sum_C_mul_X_pow]
    have hNM : N * M ≠ 0 := by positivity
    have hM0 : M ≠ 0 := by omega
    simp only [Finsupp.single_left_inj hNM, Finsupp.single_left_inj hM0]
    rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
    simp
  · have hR : ∀ d, B ≠ Finsupp.single d (N * M) := fun d h => hB ⟨d, h⟩
    rw [Finset.sum_eq_zero (fun d _ => if_neg (hR d))]
    by_cases h : ∀ d, N ∣ B d
    · rw [coeff_frob_of_dvd h, coeff_sum_C_mul_X_pow]
      have hL : ∀ d, B.mapRange (· / N) (Nat.zero_div N) ≠ Finsupp.single d M := by
        intro d hd
        apply hR d
        rw [← smul_mapRange_div h, hd, Finsupp.smul_single, smul_eq_mul]
      rw [Finset.sum_eq_zero (fun d _ => if_neg (hL d))]
      exact zero_pow (by omega)
    · rw [coeff_frob_of_not_dvd h]

end Formalism.BaseCaseIdentities
end

section
open MvPowerSeries

namespace Formalism.BaseCaseIdentities

noncomputable section

open Classical

variable {k : Type*} [Field k] {Z C : Type*}

theorem hasWt_term [Fintype Z] {v : AddValuation k (WithTop ℝ)} {r w : ℝ} {M : ℕ} (hM : 1 ≤ M)
    (x : Z → k) (h : HasWt v r w (∑ d, MvPowerSeries.C (x d) * X d ^ M)) (d : Z) :
    HasWt v r w (MvPowerSeries.C (x d) * X d ^ M) := by
  intro A
  rw [coeff_C_mul, coeff_X_pow]
  split_ifs with hA
  · subst hA
    have h1 := h (Finsupp.single d M)
    rw [coeff_sum_C_mul_X_pow] at h1
    have h2 : (∑ e, if Finsupp.single d M = Finsupp.single e M then x e else 0) = x d := by
      rw [Finset.sum_eq_single d]
      · simp
      · intro e _ hne
        rw [if_neg]
        intro heq
        exact hne ((Finsupp.single_left_inj (by omega)).1 heq).symm
      · simp
    rw [h2] at h1
    simpa using h1
  · simp

theorem hasWt_pow_sub_frob [Fintype Z] {v : AddValuation k (WithTop ℝ)} {r w : ℝ} {l e M : ℕ}
    (hl : l.Prime) (hv : v (l : k) = 1) (he : 1 ≤ e) (hM : 1 ≤ M)
    (x : Z → k) (h : HasWt v r w (∑ d, MvPowerSeries.C (x d) * X d ^ M)) :
    HasWt v r (1 + ((l ^ e : ℕ) : ℝ) * w)
      ((∑ d, MvPowerSeries.C (x d) * X d ^ M) ^ (l ^ e)
        - frob (l ^ e) (∑ d, MvPowerSeries.C (x d) * X d ^ M)) := by
  have h1 := hasWt_sum_pow_sub hl hv he Finset.univ (fun d _ => hasWt_term hM x h d)
  rw [frob_sum_X (Nat.one_le_pow _ _ hl.pos) hM]
  have h2 : ∀ d, (MvPowerSeries.C (x d) * X d ^ M : MvPowerSeries Z k) ^ (l ^ e)
      = MvPowerSeries.C (x d ^ (l ^ e)) * X d ^ (l ^ e * M) := by
    intro d
    rw [mul_pow, ← map_pow, ← pow_mul, mul_comm M]
  simpa only [h2] using h1

namespace Data

variable [Fintype Z] [Fintype C] (D : Data k Z C)

theorem lR : (3 : ℝ) ≤ (D.l : ℝ) := by exact_mod_cast D.l_ge

theorem two_K : 2 * D.K = D.i + 1 := by
  obtain ⟨n, hn⟩ := D.i_odd
  simp only [K, Kn]
  omega

theorem K_pos : 1 ≤ D.K := by
  have := D.two_K
  omega

theorem q_pos : 1 ≤ D.q := Nat.one_le_pow _ _ D.l_prime.pos

theorem q_odd : Odd D.q := by
  have : Odd D.l := D.l_prime.odd_of_ne_two (by have := D.l_ge; omega)
  exact this.pow

theorem l_ne : (D.l : k) ≠ 0 := by
  intro h
  have h1 := D.v_l
  rw [h, AddValuation.map_zero] at h1
  exact WithTop.top_ne_one h1

theorem v_l_inv : D.v (D.l : k)⁻¹ = ((-1 : ℝ) : WithTop ℝ) := by
  have h1 : D.v ((D.l : k) * (D.l : k)⁻¹) = 0 := by
    rw [mul_inv_cancel₀ D.l_ne, AddValuation.map_one]
  rw [AddValuation.map_mul, D.v_l] at h1
  induction h : D.v (D.l : k)⁻¹ using WithTop.recTopCoe with
  | top => rw [h] at h1; simp at h1
  | coe y =>
    rw [h] at h1
    have h2 : ((1 + y : ℝ) : WithTop ℝ) = ((0 : ℝ) : WithTop ℝ) := by
      rw [WithTop.coe_add]; exact h1
    have h3 : 1 + y = 0 := WithTop.coe_injective h2
    have : y = -1 := by linarith
    rw [this]

theorem v_neg_l_inv : D.v (-(D.l : k)⁻¹) = ((-1 : ℝ) : WithTop ℝ) := by
  rw [AddValuation.map_neg, D.v_l_inv]

theorem zvec_eq_zero {c : C} (hc : D.lev c ≠ 0) : D.zvec c = 0 := by
  unfold zvec
  apply Finset.sum_eq_zero
  intro d _
  rw [if_neg]
  rintro rfl
  exact hc (D.ι_lev d)

theorem wt_zvec (c : C) : D.Wt D.rad (D.zvec c) := by
  unfold zvec
  apply HasWt.sum
  intro d _
  split_ifs
  · exact HasWt.X d
  · exact HasWt.zero

theorem m_succ (s : ℕ) (b : C) : D.m (s + 1) b = MvPowerSeries.C (-(D.l : k)⁻¹) *
    ∑ c, frob D.q (D.m s c) * MvPowerSeries.C (D.g c b) := rfl

theorem q_cast : (D.q : ℝ) = qnum D.l := by simp [q, qnum]

theorem q_rho : qnum D.l * rho D.l = 1 + rho D.l := by
  have := sqMulIdentity_statement D.l (by have := D.l_ge; omega)
  linarith

theorem wt_m (s : ℕ) (c : C) : D.Wt (rho D.l + qnum D.l ^ s * sg D.l D.i) (D.m s c) := by
  induction s generalizing c with
  | zero =>
    rw [pow_zero, one_mul]
    exact D.wt_zvec c
  | succ s ih =>
    rw [m_succ]
    have h1 : ∀ c', D.Wt (0 + (D.q : ℝ) * (rho D.l + qnum D.l ^ s * sg D.l D.i))
        (frob D.q (D.m s c') * MvPowerSeries.C (D.g c' c)) := fun c' =>
      HasWt.mul_C (by simpa using D.g_int c' c) (HasWt.frob (ih c') D.q)
    have h2 := HasWt.C_mul (le_of_eq D.v_neg_l_inv.symm)
      (HasWt.sum Finset.univ (fun c' _ => h1 c'))
    refine HasWt.mono ?_ h2
    rw [D.q_cast, pow_succ]
    have := D.q_rho
    nlinarith

theorem sg_pos : 0 < sg D.l D.i := by
  unfold sg
  have := D.lR
  positivity

theorem wt_m_rho (s : ℕ) (c : C) : D.Wt (rho D.l) (D.m s c) := by
  refine HasWt.mono ?_ (D.wt_m s c)
  have h1 := D.sg_pos
  have h2 : 0 < qnum D.l ^ s := by
    unfold qnum
    have := D.lR
    positivity
  nlinarith [mul_pos h2 h1]

theorem m_closed (s : ℕ) (hs : s < D.K) :
    ∃ P : C → Z → k, (∀ c d, 0 ≤ D.v (P c d)) ∧ (∀ c, D.lev c ≠ s → ∀ d, P c d = 0) ∧
    ∀ c, D.m s c = MvPowerSeries.C ((-1) ^ s * ((D.l : k) ^ eNum D.l s)⁻¹) *
      ∑ d, MvPowerSeries.C (P c d) * X d ^ (D.q ^ s) := by
  have hl2 : 2 ≤ D.l := by have := D.l_ge; omega
  induction s with
  | zero =>
    refine ⟨fun c d => if D.ι d = c then 1 else 0, ?_, ?_, ?_⟩
    · intro c d
      show 0 ≤ D.v (if D.ι d = c then 1 else 0)
      split_ifs <;> simp
    · intro c hc d
      show (if D.ι d = c then (1 : k) else 0) = 0
      rw [if_neg]
      rintro rfl
      exact hc (D.ι_lev d)
    · intro c
      have h0 : eNum D.l 0 = 0 := (identity_e D.l 0 hl2).1
      rw [h0]
      show D.zvec c = _
      unfold zvec
      simp only [pow_zero, inv_one, mul_one, map_one, one_mul, pow_one]
      refine Finset.sum_congr rfl fun d _ => ?_
      split_ifs <;> simp
  | succ s ih =>
    obtain ⟨P, hP1, hP2, hP3⟩ := ih (by omega)
    refine ⟨fun b d => ∑ c, P c d ^ D.q * D.g c b, ?_, ?_, ?_⟩
    · intro b d
      apply AddValuation.map_le_sum
      intro c _
      rw [AddValuation.map_mul, AddValuation.map_pow]
      exact add_nonneg (nsmul_nonneg (hP1 c d) _) (D.g_int c b)
    · intro b hb d
      apply Finset.sum_eq_zero
      intro c _
      by_cases hc : D.lev c = s
      · rw [D.g_supp c (by rw [hc]; exact hs) b (by rw [hc]; exact hb), mul_zero]
      · rw [hP2 c hc d, zero_pow (by have := D.q_pos; omega), zero_mul]
    · intro b
      rw [m_succ]
      obtain ⟨κ, hκ⟩ : ∃ κ : k, κ = (-1) ^ s * ((D.l : k) ^ eNum D.l s)⁻¹ := ⟨_, rfl⟩
      rw [← hκ] at hP3
      have hfr : ∀ c, frob D.q (D.m s c) =
          ∑ d, MvPowerSeries.C ((κ * P c d) ^ D.q) * X d ^ (D.q * D.q ^ s) := by
        intro c
        rw [hP3 c, Finset.mul_sum]
        have : ∀ d, (MvPowerSeries.C κ * (MvPowerSeries.C (P c d) * X d ^ (D.q ^ s)) :
            MvPowerSeries Z k) = MvPowerSeries.C (κ * P c d) * X d ^ (D.q ^ s) := by
          intro d
          rw [map_mul, mul_assoc]
        simp only [this]
        exact frob_sum_X D.q_pos (Nat.one_le_pow _ _ D.q_pos) _
      have hκ' : -(D.l : k)⁻¹ * κ ^ D.q = (-1) ^ (s + 1) * ((D.l : k) ^ eNum D.l (s + 1))⁻¹ := by
        have he : eNum D.l (s + 1) = 1 + D.q * eNum D.l s := (identity_e D.l s hl2).2.1
        have hsign : ((-1 : k)) ^ (s * D.q) = (-1) ^ s := by
          rw [mul_comm, pow_mul, D.q_odd.neg_one_pow]
        rw [he, hκ, mul_pow, ← pow_mul, hsign, inv_pow, ← pow_mul, pow_succ, pow_add, pow_one,
          mul_inv, mul_comm (eNum D.l s) D.q]
        ring
      rw [← hκ']
      simp only [hfr, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [map_sum, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← pow_succ', mul_pow]
      simp only [map_mul, map_neg, map_pow]
      ring

theorem chainI_holds : D.ChainI := fun s hs => ⟨D.m_closed s hs, D.wt_m s⟩

theorem m_eq_zero {s : ℕ} (hs : s < D.K) {c : C} (hc : D.lev c ≠ s) : D.m s c = 0 := by
  obtain ⟨P, _, hP2, hP3⟩ := D.m_closed s hs
  rw [hP3 c]
  simp [hP2 c hc]

theorem ord_m {s : ℕ} (hs : s < D.K) (c : C) : OrdGE 1 (D.m s c) := by
  obtain ⟨P, _, _, hP3⟩ := D.m_closed s hs
  rw [hP3 c]
  apply OrdGE.C_mul
  apply OrdGE.sum
  intro d _
  apply OrdGE.C_mul
  exact OrdGE.mono (Nat.one_le_pow _ _ D.q_pos) (OrdGE.pow (OrdGE.X d) _)

theorem wt_m_pow_sub_frob {s : ℕ} (hs : s < D.K) (c : C) :
    D.Wt (1 + qnum D.l * rho D.l) (D.m s c ^ D.q - frob D.q (D.m s c)) := by
  obtain ⟨P, _, _, hP3⟩ := D.m_closed s hs
  have hw := D.wt_m_rho s c
  obtain ⟨κ, hκ⟩ : ∃ κ : k, κ = (-1) ^ s * ((D.l : k) ^ eNum D.l s)⁻¹ := ⟨_, rfl⟩
  rw [← hκ] at hP3
  have h1 : D.m s c = ∑ d, MvPowerSeries.C (κ * P c d) * X d ^ (D.q ^ s) := by
    rw [hP3 c, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_mul, mul_assoc]
  rw [h1] at hw ⊢
  have := hasWt_pow_sub_frob D.l_prime D.v_l (le_refl 2 |>.trans' (by norm_num : 1 ≤ 2))
    (Nat.one_le_pow _ _ D.q_pos) _ hw
  rw [← D.q_cast]
  exact this

end Data

end

end Formalism.BaseCaseIdentities
end

section
open MvPowerSeries

namespace Formalism.BaseCaseIdentities

noncomputable section

open Classical

def ratVal (l : ℕ) [Fact l.Prime] : AddValuation ℚ (WithTop ℝ) :=
  AddValuation.of (fun x => if x = 0 then ⊤ else ((padicValRat l x : ℝ) : WithTop ℝ))
    (by simp) (by simp)
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      by_cases hxy : x + y = 0
      · simp [hxy]
      simp only [hx, hy, hxy, if_false]
      have h := padicValRat.min_le_padicValRat_add (p := l) hxy
      rcases le_total (padicValRat l x) (padicValRat l y) with h1 | h1
      · rw [min_eq_left h1] at h
        refine le_trans (min_le_left _ _) ?_
        exact_mod_cast h
      · rw [min_eq_right h1] at h
        refine le_trans (min_le_right _ _) ?_
        exact_mod_cast h)
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      simp only [hx, hy, mul_eq_zero, or_self, if_false]
      rw [padicValRat.mul hx hy]
      push_cast
      rfl)

theorem ratVal_apply (l : ℕ) [Fact l.Prime] {x : ℚ} (hx : x ≠ 0) :
    ratVal l x = ((padicValRat l x : ℝ) : WithTop ℝ) := by
  simp [ratVal, hx]

theorem ratVal_l (l : ℕ) [hl : Fact l.Prime] : ratVal l (l : ℚ) = 1 := by
  rw [ratVal_apply l (by exact_mod_cast hl.out.ne_zero)]
  simp [padicValRat.self hl.out.one_lt]

theorem ratVal_l_inv (l : ℕ) [hl : Fact l.Prime] : ratVal l (l : ℚ)⁻¹ = ((-1 : ℝ) : WithTop ℝ) := by
  have h0 : (l : ℚ) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  rw [ratVal_apply l (inv_ne_zero h0), padicValRat.inv, padicValRat.self hl.out.one_lt]
  simp

def exData (l i : ℕ) (hl : l.Prime) (hl3 : 3 ≤ l) (hi : Odd i) : Data ℚ Unit (Fin 2) :=
  haveI : Fact l.Prime := ⟨hl⟩
  { v := ratVal l
    l := l
    l_prime := hl
    l_ge := hl3
    v_l := ratVal_l l
    i := i
    i_odd := hi
    good := fun _ => True
    lev := fun c => c.val
    pure_good := fun _ _ => trivial
    ι := fun _ => 0
    ι_inj := fun _ _ _ => rfl
    ι_lev := fun _ => rfl
    al := fun c j b => if c = 0 ∧ j = 2 ∧ b = 1 then (l : ℚ)⁻¹ else 0
    g := fun c b => if c = 0 ∧ b = 1 then 1 else 0
    lam := fun _ _ => 0
    al_all := by
      intro c j b
      split_ifs with h
      · obtain ⟨_, rfl, _⟩ := h
        rw [ratVal_l_inv]
        exact_mod_cast (by norm_num : (-((2 : ℕ) : ℝ)) ≤ -1)
      · simp
    al_good := by
      intro c _ j b _
      split_ifs with h
      · obtain ⟨_, rfl, _⟩ := h
        rw [ratVal_l_inv]
        exact_mod_cast (by norm_num : (-(((2 : ℕ) : ℝ) - 1)) ≤ -1)
      · simp
    al_one := by
      intro c _ b
      simp
    al_two := by
      intro c _ b
      by_cases h : c = 0 ∧ b = 1
      · simp [h]
      · have : ¬ (c = 0 ∧ 2 = 2 ∧ b = 1) := by tauto
        simp [h]
    g_int := by
      intro c b
      split_ifs <;> simp
    lam_int := by
      intro c b
      simp
    g_supp := by
      intro c _ b hb
      by_cases h : c = 0 ∧ b = 1
      · obtain ⟨rfl, rfl⟩ := h
        exact absurd rfl hb
      · simp [h] }

theorem coeff_frob_smul {k : Type*} [Field k] {Z : Type*} (N : ℕ) (hN : 1 ≤ N)
    (f : MvPowerSeries Z k) (A : Z →₀ ℕ) : coeff (N • A) (frob N f) = (coeff A f) ^ N := by
  have h1 : ∀ d, N ∣ (N • A) d := fun d => by simp
  have h2 : (N • A).mapRange (· / N) (Nat.zero_div N) = A := by
    ext d
    simp [Nat.mul_div_cancel_left _ hN]
  show (if ∀ d, N ∣ (N • A) d then
    (coeff ((N • A).mapRange (· / N) (Nat.zero_div N)) f) ^ N else 0) = _
  rw [if_pos h1, h2]


theorem Data.base_case_k_one_holds {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C]
    (D : Data k Z C) : D.FrobeniusBaseCaseIdentity := by
  intro hi
  have hK : D.K = 1 := by simp [Data.K, Kn, hi]
  have hzero : ∀ w : ℝ, D.Wt w (0 : MvPowerSeries Z k) := by
    intro w A
    simp
  refine ⟨?_, ?_⟩
  · intro c hc
    rw [hK] at hc
    have : D.lev c = 0 := by omega
    rw [this]
    show D.Wt D.top (D.zvec c - D.zvec c)
    rw [sub_self]
    exact hzero _
  · intro c hc
    rw [hK] at hc
    have : D.zvec c = 0 := by
      unfold Data.zvec
      apply Finset.sum_eq_zero
      intro d _
      rw [if_neg]
      rintro rfl
      rw [D.ι_lev] at hc
      omega
    rw [this]
    exact hzero _

end

end Formalism.BaseCaseIdentities
end

section
open MvPowerSeries

namespace Formalism.BaseCaseIdentities

noncomputable section

open Classical

namespace Data

variable {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C] (D : Data k Z C)

def mu (J : ℕ) (c : C) : MvPowerSeries Z k := if D.lev c < J then D.m (D.lev c) c else 0

theorem inWTo_iff (J : ℕ) (t : C → MvPowerSeries Z k) :
    D.InWTo J t ↔ ∀ c, D.Wt D.top (t c - D.mu J c) := by
  constructor
  · intro h c
    unfold mu
    split_ifs with hc
    · exact h.1 c hc
    · rw [sub_zero]; exact h.2 c (not_lt.1 hc)
  · intro h
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · have := h c
      rwa [mu, if_pos hc] at this
    · have := h c
      rwa [mu, if_neg (not_lt.2 hc), sub_zero] at this

def main (J : ℕ) (c b : C) : MvPowerSeries Z k :=
  if D.lev c < J ∧ D.lev c + 1 < D.K then
    MvPowerSeries.C (-(D.l : k)⁻¹ * D.g c b) * frob D.q (D.m (D.lev c) c) else 0

theorem main_eq_zero (J : ℕ) (c b : C) (h : D.lev b ≠ D.lev c + 1) : D.main J c b = 0 := by
  unfold main
  split_ifs with h1
  · rw [D.g_supp c h1.2 b h, mul_zero, map_zero, zero_mul]
  · rfl

theorem mu_succ (J : ℕ) (hJ1 : 1 ≤ J) (hJK : J ≤ D.K) (b : C) :
    D.mu (min (J + 1) D.K) b = D.zvec b + ∑ c, D.main J c b := by
  have hK := D.K_pos
  by_cases hb0 : D.lev b = 0
  · have h1 : D.mu (min (J + 1) D.K) b = D.zvec b := by
      rw [mu, if_pos (by rw [hb0]; omega), hb0]
      rfl
    rw [h1, Finset.sum_eq_zero, add_zero]
    intro c _
    exact D.main_eq_zero J c b (by omega)
  · rw [D.zvec_eq_zero hb0, zero_add]
    by_cases hb : D.lev b < min (J + 1) D.K
    · obtain ⟨s, hs⟩ : ∃ s, D.lev b = s + 1 := ⟨D.lev b - 1, by omega⟩
      rw [mu, if_pos hb, hs, m_succ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hc : D.lev c = s
      · rw [main, if_pos ⟨by omega, by omega⟩, hc, map_mul]
        ring
      · rw [D.m_eq_zero (by omega) hc, frob_zero D.q_pos, zero_mul, mul_zero,
          D.main_eq_zero J c b (by omega)]
    · rw [mu, if_neg hb]
      symm
      apply Finset.sum_eq_zero
      intro c _
      unfold main
      split_ifs with h
      · rw [D.g_supp c h.2 b (by omega), mul_zero, map_zero, zero_mul]
      · rfl

theorem rho_le_top : rho D.l ≤ D.top := by
  unfold top
  linarith

theorem v_al_two (c : C) (hg : D.good c) (b : C) : ((-1 : ℝ) : WithTop ℝ) ≤ D.v (D.al c 2 b) := by
  have h := D.al_good c hg 2 b (by norm_num)
  have h1 : (-(((2 : ℕ) : ℝ) - 1)) = (-1 : ℝ) := by norm_num
  rwa [h1] at h

theorem wt_two (J : ℕ) (hJK : J ≤ D.K) (c b : C) (hcJ : D.lev c < J) (τ : MvPowerSeries Z k)
    (hν : D.Wt D.top (τ - D.m (D.lev c) c)) :
    D.Wt D.top (MvPowerSeries.C (D.al c 2 b) * τ ^ (D.l ^ 2) + D.main J c b) := by
  have hl := D.l_ge
  have hcK : D.lev c < D.K := by omega
  have hgood := D.pure_good c hcK
  have hal := D.v_al_two c hgood b
  have hρ := rho_pos hl
  obtain ⟨μ, hμdef⟩ : ∃ μ, μ = D.m (D.lev c) c := ⟨_, rfl⟩
  obtain ⟨ν, hνdef⟩ : ∃ ν, ν = τ - μ := ⟨_, rfl⟩
  have hτ : τ = μ + ν := by rw [hνdef]; ring
  have hμ : D.Wt (rho D.l) μ := by rw [hμdef]; exact D.wt_m_rho _ _
  have hν' : D.Wt D.top ν := by rw [hνdef, hμdef]; exact hν
  have hdec : MvPowerSeries.C (D.al c 2 b) * τ ^ (D.l ^ 2) + D.main J c b =
      MvPowerSeries.C (D.al c 2 b) * (μ ^ (D.l ^ 2) - frob D.q μ)
      + MvPowerSeries.C (D.al c 2 b) * ((μ + ν) ^ (D.l ^ 2) - μ ^ (D.l ^ 2) - ν ^ (D.l ^ 2))
      + MvPowerSeries.C (D.al c 2 b) * ν ^ (D.l ^ 2)
      + (MvPowerSeries.C (D.al c 2 b) * frob D.q μ + D.main J c b) := by
    rw [hτ]; ring
  rw [hdec]
  have hqρ := D.q_rho
  refine HasWt.add (HasWt.add (HasWt.add ?_ ?_) ?_) ?_
  · have h1 : D.Wt (1 + qnum D.l * rho D.l) (μ ^ (D.l ^ 2) - frob D.q μ) := by
      rw [hμdef]; exact D.wt_m_pow_sub_frob hcK c
    refine HasWt.mono ?_ (HasWt.C_mul hal h1)
    unfold top
    linarith
  · have h1 := hasWt_add_pow_sub (e := 2) D.l_prime D.v_l D.rho_le_top hμ hν'
    refine HasWt.mono ?_ (HasWt.C_mul hal h1)
    have := rho_mul hl
    push_cast
    linarith
  · have h1 := HasWt.pow hν' (D.l ^ 2)
    refine HasWt.mono ?_ (HasWt.C_mul hal h1)
    have := num_good hl (j := 2) le_rfl
    unfold top
    push_cast at this ⊢
    linarith
  · by_cases hK1 : D.lev c + 1 < D.K
    · rw [main, if_pos ⟨hcJ, hK1⟩, ← hμdef, ← add_mul, ← map_add]
      have h1 : D.al c 2 b + -(D.l : k)⁻¹ * D.g c b = D.lam c b := by
        rw [D.al_two c hcK b]
        have := D.l_ne
        field_simp
        ring
      rw [h1]
      have h2 : ((0 : ℝ) : WithTop ℝ) ≤ D.v (D.lam c b) := by simpa using D.lam_int c b
      refine HasWt.mono ?_ (HasWt.C_mul h2 (HasWt.frob hμ D.q))
      rw [D.q_cast]
      unfold top
      linarith
    · rw [main, if_neg (fun h => hK1 h.2), add_zero]
      have h1 : D.Wt (rho D.l + qnum D.l ^ (D.lev c) * sg D.l D.i) μ := by
        rw [hμdef]; exact D.wt_m _ _
      refine HasWt.mono ?_ (HasWt.C_mul hal (HasWt.frob h1 D.q))
      rw [D.q_cast]
      have hlev : D.lev c + 1 = Kn D.i := by
        have : D.K = Kn D.i := rfl
        omega
      have h2 := identity_twenty_d D.l D.i (by omega) D.i_odd
      rw [← hlev, pow_succ'] at h2
      have := D.lR
      unfold top
      nlinarith

theorem wt_contrib (J : ℕ) (hJK : J ≤ D.K) (t : C → MvPowerSeries Z k)
    (ht : ∀ c, D.Wt D.top (t c - D.mu J c)) (N : ℕ) (hN : 2 ≤ N) (c b : C) :
    D.Wt D.top
      (∑ j ∈ Finset.Icc 1 N, MvPowerSeries.C (D.al c j b) * t c ^ (D.l ^ j) + D.main J c b) := by
  have hl := D.l_ge
  by_cases hcJ : D.lev c < J
  · have hcK : D.lev c < D.K := by omega
    have hgood := D.pure_good c hcK
    have hν : D.Wt D.top (t c - D.m (D.lev c) c) := by
      have := ht c
      rwa [mu, if_pos hcJ] at this
    have ht' : D.Wt (rho D.l) (t c) := by
      have h1 := HasWt.add (D.wt_m_rho (D.lev c) c) (HasWt.mono D.rho_le_top hν)
      rwa [add_sub_cancel] at h1
    have h2mem : 2 ∈ Finset.Icc 1 N := Finset.mem_Icc.2 ⟨by norm_num, hN⟩
    rw [← Finset.add_sum_erase _ _ h2mem, add_right_comm]
    refine HasWt.add (D.wt_two J hJK c b hcJ (t c) hν) ?_
    apply HasWt.sum
    intro j hj
    have hj' : j ≠ 2 ∧ 1 ≤ j ∧ j ≤ N := by
      simpa [Finset.mem_erase, Finset.mem_Icc] using hj
    by_cases hj1 : j = 1
    · subst hj1
      rw [D.al_one c hgood b, map_zero, zero_mul]
      exact HasWt.zero
    · have hj3 : 3 ≤ j := by omega
      refine HasWt.mono ?_ (HasWt.C_mul (D.al_good c hgood j b (by omega))
        (HasWt.pow ht' (D.l ^ j)))
      have := num_c hl hj3
      unfold top
      push_cast
      exact this
  · have ht' : D.Wt D.top (t c) := by
      have := ht c
      rwa [mu, if_neg hcJ, sub_zero] at this
    rw [main, if_neg (fun h => hcJ h.1), add_zero]
    apply HasWt.sum
    intro j hj
    have hj' : 1 ≤ j ∧ j ≤ N := by simpa [Finset.mem_Icc] using hj
    by_cases hg : D.good c
    · by_cases hj1 : j = 1
      · subst hj1
        rw [D.al_one c hg b, map_zero, zero_mul]
        exact HasWt.zero
      · refine HasWt.mono ?_ (HasWt.C_mul (D.al_good c hg j b (by omega))
          (HasWt.pow ht' (D.l ^ j)))
        have := num_good hl (j := j) (by omega)
        unfold top
        push_cast
        exact this
    · refine HasWt.mono ?_ (HasWt.C_mul (D.al_all c j b) (HasWt.pow ht' (D.l ^ j)))
      have := num_d hl (j := j) hj'.1
      unfold top
      push_cast
      exact this

theorem step (J : ℕ) (hJ1 : 1 ≤ J) (hJK : J ≤ D.K) (t : C → MvPowerSeries Z k)
    (hnc : NoConst t) (ht : D.InWTo J t) : D.InWTo (min (J + 1) D.K) (D.Psi t) := by
  rw [inWTo_iff] at ht ⊢
  intro b A
  have h1 : coeff A (D.Psi t b - D.mu (min (J + 1) D.K) b) =
      coeff A (D.PsiPartial (max A.degree 2) t b - D.mu (min (J + 1) D.K) b) := by
    rw [map_sub, map_sub, D.opIsLimit t hnc b A _ (le_max_left _ _)]
  rw [h1]
  have h2 : D.PsiPartial (max A.degree 2) t b - D.mu (min (J + 1) D.K) b =
      -∑ c, (∑ j ∈ Finset.Icc 1 (max A.degree 2),
        MvPowerSeries.C (D.al c j b) * t c ^ (D.l ^ j) + D.main J c b) := by
    rw [D.mu_succ J hJ1 hJK b, PsiPartial, Finset.sum_add_distrib]
    ring
  rw [h2]
  exact (HasWt.neg (HasWt.sum _ fun c _ =>
    D.wt_contrib J hJK t ht _ (le_max_right _ _) c b)) A

theorem start_in_W_holds : D.StartInW := by
  refine ⟨?_, ?_, ?_⟩
  · intro c
    unfold start
    split_ifs with h
    · exact D.ord_m h c
    · exact OrdGE.zero
  · intro c hc
    unfold start
    rw [if_pos hc, sub_self]
    exact HasWt.zero
  · intro c hc
    unfold start
    rw [if_neg (not_lt.2 hc)]
    exact HasWt.zero

theorem psi_in_W_holds : D.PsiW := by
  intro t hnc hW
  refine ⟨D.noConst_Psi t, ?_⟩
  have h := D.step D.K D.K_pos le_rfl t hnc hW
  rwa [min_eq_right (by omega)] at h

theorem chainII_holds : D.ChainII := by
  intro t hnc hfix
  have hit : ∀ n, NoConst ((D.Psi)^[n] D.start) ∧ D.InW ((D.Psi)^[n] D.start) := by
    intro n
    induction n with
    | zero => exact D.start_in_W_holds
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact D.psi_in_W_holds _ ih.1 ih.2
  unfold InW
  rw [inWTo_iff]
  intro c A
  have h := (D.inWTo_iff _ _).1 (hit A.degree).2 c A
  have hc := D.hasUniqueFixedPoint.2 D.start t D.start_in_W_holds.1 hnc hfix A.degree A le_rfl c
  rw [map_sub] at h ⊢
  rw [← hc]
  exact h

theorem second_way_holds : D.SecondWay := by
  have h1 : D.InWTo 1 D.zvec := by
    refine ⟨?_, ?_⟩
    · intro c hc
      have : D.lev c = 0 := by omega
      rw [this]
      show D.Wt D.top (D.zvec c - D.zvec c)
      rw [sub_self]
      exact HasWt.zero
    · intro c hc
      rw [D.zvec_eq_zero (by omega)]
      exact HasWt.zero
  refine ⟨h1, fun J t hJ1 hJK hnc ht => D.step J hJ1 hJK t hnc ht, ?_⟩
  have hK := D.K_pos
  have hit : ∀ n, D.InWTo (min (n + 1) D.K) ((D.Psi)^[n] D.zvec) := by
    intro n
    induction n with
    | zero =>
      rw [min_eq_left (by omega)]
      exact h1
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have h2 := D.step _ (by omega) (min_le_right _ _) _ (D.noConst_iterate D.noConst_zvec n) ih
      have h3 : min (min (n + 1) D.K + 1) D.K = min (n + 1 + 1) D.K := by omega
      rwa [h3] at h2
  intro n hn
  have h2 := hit n
  rwa [min_eq_right (by omega)] at h2

end Data

end

end Formalism.BaseCaseIdentities
end
