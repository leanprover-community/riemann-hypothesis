import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsEqSubOfMemCob
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexStabilizer
import Development.AbelianVarietyTheory.Definitions.Foundations.HTLawAt
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolynomialInPrimitiveRootOfInertiaFixedStatement
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ExistsApplyEqOfMemDec

section
namespace GlobalTheory.AxSen

variable {K : Type} [Field K]

def Ge (A : ValuationSubring K) (ϖ w : K) (q : ℚ) : Prop :=
  ∀ (a : ℤ) (b : ℕ), 0 < b → (a : ℚ) ≤ q * b → A.valuation w ^ b ≤ A.valuation ϖ ^ a

variable {A : ValuationSubring K} {ϖ : K}

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.ge_zero (q : ℚ) : _root_.GlobalTheory.AxSen.Ge A ϖ 0 q := by
  intro a b hb _
  rw [map_zero, zero_pow hb.ne']
  exact zero_le'

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.mono {w : K} {q q' : ℚ}
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ w q) (hq : q' ≤ q) :
    _root_.GlobalTheory.AxSen.Ge A ϖ w q' :=
  fun a b hb hab => h a b hb (hab.trans (mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg b)))

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.of_le {w w' : K} {q : ℚ}
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ w q) (hw : A.valuation w' ≤ A.valuation w) :
    _root_.GlobalTheory.AxSen.Ge A ϖ w' q :=
  fun a b hb hab => (pow_le_pow_left' hw b).trans (h a b hb hab)

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.add {w w' : K} {q : ℚ}
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ w q) (h' : _root_.GlobalTheory.AxSen.Ge A ϖ w' q) :
    _root_.GlobalTheory.AxSen.Ge A ϖ (w + w') q := by
  rcases le_total (A.valuation w) (A.valuation w') with hle | hle
  · exact h'.of_le ((Valuation.map_add _ _ _).trans (max_le hle le_rfl))
  · exact h.of_le ((Valuation.map_add _ _ _).trans (max_le le_rfl hle))

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.symm {x y : K} {q : ℚ}
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ (x - y) q) : _root_.GlobalTheory.AxSen.Ge A ϖ (y - x) q :=
  h.of_le (by rw [Valuation.map_sub_swap])

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.trans {x y z : K} {q : ℚ}
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ (x - y) q) (h' : _root_.GlobalTheory.AxSen.Ge A ϖ (y - z) q) :
    _root_.GlobalTheory.AxSen.Ge A ϖ (x - z) q := by
  have := h.add h'
  rwa [sub_add_sub_cancel] at this

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.mul (h0 : ϖ ≠ 0) (h1 : A.valuation ϖ ≤ 1)
    {w w' : K} {q q' : ℚ} (h : _root_.GlobalTheory.AxSen.Ge A ϖ w q)
    (h' : _root_.GlobalTheory.AxSen.Ge A ϖ w' q') :
    _root_.GlobalTheory.AxSen.Ge A ϖ (w * w') (q + q') := by
  intro a b hb hab
  have hv : A.valuation ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have hd : 0 < q.den := q.den_pos
  have hd' : 0 < q'.den := q'.den_pos
  have h₁ := h (q.num * q'.den * b) (q.den * q'.den * b) (by positivity)
    (le_of_eq (by push_cast; rw [← Rat.mul_den_eq_num q]; ring))
  have h₂ := h' (q'.num * q.den * b) (q.den * q'.den * b) (by positivity)
    (le_of_eq (by push_cast; rw [← Rat.mul_den_eq_num q']; ring))
  have hexp : a * ((q.den * q'.den : ℕ) : ℤ) ≤ (q.num * q'.den * b + q'.num * q.den * b) := by
    have hq : ((a * ((q.den * q'.den : ℕ) : ℤ) : ℤ) : ℚ)
        ≤ ((q.num * q'.den * b + q'.num * q.den * b : ℤ) : ℚ) := by
      push_cast
      rw [← Rat.mul_den_eq_num q, ← Rat.mul_den_eq_num q']
      have hdd : (0 : ℚ) ≤ q.den * q'.den := by positivity
      calc (a : ℚ) * (q.den * q'.den) ≤ ((q + q') * b) * (q.den * q'.den) :=
            mul_le_mul_of_nonneg_right hab hdd
        _ = _ := by ring
    exact_mod_cast hq
  have key : (A.valuation (w * w') ^ b) ^ (q.den * q'.den)
      ≤ (A.valuation ϖ ^ a) ^ (q.den * q'.den) := by
    calc (A.valuation (w * w') ^ b) ^ (q.den * q'.den)
        = A.valuation w ^ (q.den * q'.den * b) * A.valuation w' ^ (q.den * q'.den * b) := by
          rw [map_mul, mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm b]
      _ ≤ A.valuation ϖ ^ (q.num * q'.den * b) * A.valuation ϖ ^ (q'.num * q.den * b) :=
          mul_le_mul' h₁ h₂
      _ = A.valuation ϖ ^ (q.num * q'.den * b + q'.num * q.den * b) := by
          rw [← zpow_add₀ hv]
      _ ≤ A.valuation ϖ ^ (a * ((q.den * q'.den : ℕ) : ℤ)) :=
          zpow_le_zpow_right_of_le_one₀ (zero_lt_iff.2 hv) h1 hexp
      _ = (A.valuation ϖ ^ a) ^ (q.den * q'.den) := by rw [zpow_mul, zpow_natCast]
  exact (pow_le_pow_iff_left₀ zero_le' zero_le' (by positivity)).1 key

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.root {w : K} {q : ℚ} {N : ℕ} (hN : 0 < N)
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ (w ^ N) (q * N)) : _root_.GlobalTheory.AxSen.Ge A ϖ w q := by
  intro a b hb hab
  have h₁ := h (a * N) b hb (by
    push_cast
    calc (a : ℚ) * N ≤ q * b * N := mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg N)
      _ = q * N * b := by ring)
  refine (pow_le_pow_iff_left₀ zero_le' zero_le' hN.ne').1 ?_
  calc (A.valuation w ^ b) ^ N = A.valuation (w ^ N) ^ b := by
        rw [map_pow, ← pow_mul, ← pow_mul, mul_comm]
    _ ≤ A.valuation ϖ ^ (a * (N : ℤ)) := h₁
    _ = (A.valuation ϖ ^ a) ^ N := by rw [zpow_mul, zpow_natCast]

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.div (h0 : ϖ ≠ 0) (h1 : A.valuation ϖ ≤ 1)
    {c w : K} {q : ℚ} {e : ℕ} (hc : A.valuation ϖ ^ e ≤ A.valuation c)
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ (c * w) q) :
    _root_.GlobalTheory.AxSen.Ge A ϖ w (q - e) := by
  intro a b hb hab
  have hv : A.valuation ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have hc0 : A.valuation c ≠ 0 := by
    intro hc0
    rw [hc0] at hc
    exact pow_ne_zero e hv (le_zero_iff.1 hc)
  have h₁ := h (a + e * b) b hb (by push_cast; linarith [hab, sub_mul q (e : ℚ) b])
  rw [map_mul, mul_pow, zpow_add₀ hv] at h₁
  have h₂ : A.valuation ϖ ^ ((e : ℤ) * (b : ℤ)) ≤ A.valuation c ^ b := by
    rw [zpow_mul, zpow_natCast, zpow_natCast]
    exact pow_le_pow_left' hc b
  refine (mul_le_mul_iff_of_pos_right (zero_lt_iff.2 (pow_ne_zero b hc0))).1 ?_
  calc A.valuation w ^ b * A.valuation c ^ b = A.valuation c ^ b * A.valuation w ^ b := mul_comm _ _
    _ ≤ A.valuation ϖ ^ a * A.valuation ϖ ^ ((e : ℤ) * (b : ℤ)) := h₁
    _ ≤ A.valuation ϖ ^ a * A.valuation c ^ b := mul_le_mul' le_rfl h₂

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.ge_natCast_iff (h0 : ϖ ≠ 0) (h1 : A.valuation ϖ ≤ 1) {w : K}
    {m : ℕ} : _root_.GlobalTheory.AxSen.Ge A ϖ w m ↔ ∃ z ∈ A, w = ϖ ^ m * z := by
  have hv : A.valuation ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  constructor
  · intro h
    have h₁ := h m 1 one_pos (by simp)
    rw [pow_one, zpow_natCast, ← map_pow] at h₁
    refine ⟨w / ϖ ^ m, ?_, by field_simp⟩
    rw [← ValuationSubring.valuation_le_one_iff, map_div₀]
    exact (div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (pow_ne_zero m h0)))).2 h₁
  · rintro ⟨z, hz, rfl⟩ a b hb hab
    have hz' : A.valuation z ≤ 1 := (ValuationSubring.valuation_le_one_iff A z).2 hz
    have hab' : a ≤ ((m * b : ℕ) : ℤ) := by
      have : (a : ℚ) ≤ ((m * b : ℕ) : ℚ) := by push_cast; exact hab
      exact_mod_cast this
    rw [map_mul, mul_pow, map_pow]
    calc (A.valuation ϖ ^ m) ^ b * A.valuation z ^ b ≤ (A.valuation ϖ ^ m) ^ b * 1 :=
          mul_le_mul' le_rfl (pow_le_one' hz' b)
      _ = A.valuation ϖ ^ ((m * b : ℕ) : ℤ) := by rw [mul_one, ← pow_mul, zpow_natCast]
      _ ≤ A.valuation ϖ ^ a := zpow_le_zpow_right_of_le_one₀ (zero_lt_iff.2 hv) h1 hab'

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in

theorem _root_.GlobalTheory.AxSen.Ge.map (h0 : ϖ ≠ 0) (f : K →+* K)
    (hf : ∀ x ∈ A, f x ∈ A) (hϖ : f ϖ = ϖ) {w : K} {q : ℚ}
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ w q) : _root_.GlobalTheory.AxSen.Ge A ϖ (f w) q := by
  intro a b hb hab
  have hv : A.valuation ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have h₁ := h a b hb hab
  have hpos : 0 < A.valuation ϖ ^ a := zero_lt_iff.2 (zpow_ne_zero a hv)
  rw [← div_le_one₀ hpos, ← map_pow, ← map_zpow₀, ← map_div₀,
    ValuationSubring.valuation_le_one_iff] at h₁ ⊢
  have := hf _ h₁
  rwa [map_div₀, map_pow, map_zpow₀, hϖ] at this

end GlobalTheory.AxSen
end

section
namespace GlobalTheory

private lemma not_dvd_choose_prime_pow_of_between {p : ℕ} (hp : p.Prime) :
    ∀ (k N : ℕ), p ^ k ≤ N → N < p ^ (k + 1) → ¬ p ∣ N.choose (p ^ k) := by
  haveI := Fact.mk hp
  intro k
  induction k with
  | zero =>
    intro N h1 h2 hdvd
    simp only [pow_zero, zero_add, pow_one, Nat.choose_one_right] at h1 h2 hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  | succ k ih =>
    intro N h1 h2 hdvd
    have hmod := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := N) (k := p ^ (k + 1))
      (p := p)
    rw [pow_succ, Nat.mul_mod_left, Nat.choose_zero_right, one_mul,
      Nat.mul_div_cancel _ hp.pos, ← pow_succ] at hmod
    refine ih (N / p) ?_ ?_ ((hmod.dvd_iff (dvd_refl p)).1 hdvd)
    · exact (Nat.le_div_iff_mul_le hp.pos).2 (by rw [← pow_succ]; exact h1)
    · exact (Nat.div_lt_iff_lt_mul hp.pos).2 (by rw [← pow_succ]; exact h2)

theorem _root_.GlobalTheory.exists_choose_small_valuation_ax : ∀ (p : ℕ), p.Prime → ∀ N : ℕ, 2 ≤ N →
    ∃ j e : ℕ, 0 < j ∧ j < N ∧ ¬ p ^ (e + 1) ∣ N.choose j ∧
  (e : ℚ) / ((N - j : ℕ) : ℚ) + (p : ℚ) / ((p : ℚ) - 1) ^ 2 * (1 - 1 / (p : ℚ) ^ Nat.log p (N - j)) ≤ (p : ℚ) / ((p : ℚ) - 1) ^ 2 * (1 - 1 / (p : ℚ) ^ Nat.log p N) := by
  intro p hp N hN
  have hp1 : 1 < p := hp.one_lt
  obtain ⟨k, hk⟩ : ∃ k, Nat.log p N = k := ⟨_, rfl⟩
  have hkle : p ^ k ≤ N := hk ▸ Nat.pow_log_le_self p (by omega)
  have hlt : N < p ^ (k + 1) := hk ▸ Nat.lt_pow_succ_log_self hp1 N
  have hpk : 0 < p ^ k := pow_pos hp.pos k
  rcases hkle.lt_or_eq with hlt' | heq
  · refine ⟨N - p ^ k, 0, by omega, by omega, ?_, ?_⟩
    · rw [Nat.choose_symm_of_eq_add (b := p ^ k) (by omega), zero_add, pow_one]
      exact not_dvd_choose_prime_pow_of_between hp k N hkle hlt
    · have hm : N - (N - p ^ k) = p ^ k := by omega
      rw [hm, Nat.log_pow hp1, hk]
      simp
  · subst heq
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp at hN
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hpk' : 0 < p ^ k' := pow_pos hp.pos k'
    have hsucc : p ^ (k' + 1) = p ^ k' * p := pow_succ p k'
    have h2 : 2 * p ^ k' ≤ p ^ (k' + 1) := by
      rw [hsucc, mul_comm]; exact Nat.mul_le_mul le_rfl hp.two_le
    refine ⟨p ^ k', 1, hpk', by omega, ?_, ?_⟩
    · have hmult := hp.emultiplicity_choose_prime_pow (n := k' + 1) (k := p ^ k')
        (by omega) (pow_ne_zero _ hp.ne_zero)
      rw [multiplicity_pow_self_of_prime hp.prime k'] at hmult
      rw [pow_dvd_iff_le_emultiplicity, hmult]
      norm_num
    · have hlogm : Nat.log p (p ^ (k' + 1) - p ^ k') = k' :=
        Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)
      have hcast : ((p ^ (k' + 1) - p ^ k' : ℕ) : ℚ) = (p : ℚ) ^ k' * ((p : ℚ) - 1) := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hp1' : (p : ℚ) - 1 ≠ 0 := by
        have : (1 : ℚ) < p := by exact_mod_cast hp1
        linarith
      rw [hlogm, Nat.log_pow hp1, hcast]
      apply le_of_eq
      field_simp
      ring

end GlobalTheory
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_choose_small_padicVal_ax_induction : ∀ (p : ℕ), p.Prime → ∀ N : ℕ, 2 ≤ N → ∃ j e : ℕ, 0 < j ∧ j < N ∧ ¬ p ^ (e + 1) ∣ N.choose j ∧
  (e : ℚ) / ((N - j : ℕ) : ℚ) + (p : ℚ) / ((p : ℚ) - 1) ^ 2 * (1 - 1 / (p : ℚ) ^ Nat.log p (N - j)) ≤ (p : ℚ) / ((p : ℚ) - 1) ^ 2 * (1 - 1 / (p : ℚ) ^ Nat.log p N) := by
  first | exact @GlobalTheory.exists_choose_small_valuation_ax | exact GlobalTheory.exists_choose_small_valuation_ax | (intros; apply GlobalTheory.exists_choose_small_valuation_ax; all_goals assumption)
end

section
section
open Polynomial

namespace GlobalTheory.AxSen

section Step

variable {K : Type} [Field K] {A : ValuationSubring K} {ϖ : K}

theorem ge_coeff_prod (h0 : ϖ ≠ 0) (h1 : A.valuation ϖ ≤ 1) {q : ℚ} (s : Multiset K) (hs : ∀ d ∈ s, Ge A ϖ d q) (k : ℕ) :
    Ge A ϖ ((s.map fun d => X + C d).prod.coeff k) (((s.card : ℚ) - k) * q) := by
  induction s using Multiset.induction_on generalizing k with
  | empty =>
    rcases k with _ | k
    · have := (ge_natCast_iff (A := A) h0 h1 (w := 1) (m := 0)).mpr ⟨1, A.one_mem, by simp⟩
      simpa using this
    · simpa [coeff_one] using ge_zero _
  | cons d s ih =>
    have hd := hs d (Multiset.mem_cons_self _ _)
    have ih' := ih fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, coeff_add, coeff_C_mul, Multiset.card_cons]
    refine Ge.add ?_ ((hd.mul h0 h1 (ih' k)).mono (le_of_eq (by push_cast; ring)))
    rcases k with _ | k
    · rw [coeff_X_mul_zero]; exact ge_zero _
    · rw [coeff_X_mul]; exact (ih' k).mono (le_of_eq (by push_cast; ring))

theorem exists_ge_of_prod (s : Multiset K) (hs : s ≠ 0) {q : ℚ} (h : Ge A ϖ s.prod (q * s.card)) :
    ∃ d ∈ s, Ge A ϖ d q := by
  classical
  obtain ⟨d, hd, hmin⟩ := Finset.exists_min_image s.toFinset A.valuation (Multiset.toFinset_nonempty.mpr hs)
  refine ⟨d, Multiset.mem_toFinset.mp hd, Ge.root (Multiset.card_pos.mpr hs) (h.of_le ?_)⟩
  rw [map_pow, map_multiset_prod, ← Multiset.card_map A.valuation s]
  refine Multiset.pow_card_le_prod fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
  exact hmin y (Multiset.mem_toFinset.mpr hy)

theorem exists_root_hasseDeriv [IsAlgClosed K] [CharZero K] (h0 : ϖ ≠ 0) (h1 : A.valuation ϖ ≤ 1) (T : Finset K) (α : K) {a : ℚ}
    (hT : ∀ t ∈ T, Ge A ϖ (α - t) a) {j e : ℕ} (hj : j < T.card)
    (hc : A.valuation ϖ ^ e ≤ A.valuation ((T.card.choose j : ℕ) : K)) :
    ∃ β ∈ (hasseDeriv j (∏ t ∈ T, (X - C t))).roots, Ge A ϖ (α - β) (a - e / ((T.card - j : ℕ) : ℚ)) := by
  set P : K[X] := ∏ t ∈ T, (X - C t) with hP
  have hPm : P.Monic := monic_prod_of_monic _ _ fun t _ => monic_X_sub_C t
  have hPd : P.natDegree = T.card := by simp [hP]
  set Q := hasseDeriv j P with hQ
  have hQd : Q.natDegree = T.card - j := by rw [hQ, natDegree_hasseDeriv, hPd]
  have hlc : Q.leadingCoeff = ((T.card.choose j : ℕ) : K) := by
    rw [leadingCoeff, hQd, hQ, hasseDeriv_coeff, Nat.sub_add_cancel hj.le, ← hPd, hPm.coeff_natDegree, mul_one]
  have hcard : Q.roots.card = Q.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have hev : Q.eval α = ((T.val.map fun t => α - t).map fun d => X + C d).prod.coeff j := by
    rw [hQ, ← taylor_coeff, taylor_apply, hP, prod_comp, Multiset.map_map]
    congr 1
    refine Finset.prod_congr rfl fun t _ => ?_
    simp [add_sub_assoc]
  have hge := ge_coeff_prod h0 h1 (T.val.map fun t => α - t) (q := a) (by
    intro d hd
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hd
    exact hT t ht) j
  rw [← hev, ← hfac, eval_mul, eval_C, hlc, eval_multiset_prod, Multiset.map_map] at hge
  have hdiv := hge.div h0 h1 hc
  have hpos : 0 < T.card - j := Nat.sub_pos_of_lt hj
  obtain ⟨d, hd, hd'⟩ := exists_ge_of_prod (A := A) (ϖ := ϖ) (q := a - e / ((T.card - j : ℕ) : ℚ))
    (Q.roots.map ((fun p => eval α p) ∘ fun a => X - C a)) (by
      rw [← Multiset.card_pos, Multiset.card_map, hcard, hQd]; exact hpos)
    (hdiv.mono (le_of_eq (by
      rw [Multiset.card_map, Multiset.card_map, hcard, hQd, Finset.card_val]
      have : ((T.card - j : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
      rw [← Nat.cast_sub hj.le]
      field_simp)))
  obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.mp hd
  exact ⟨β, hβ, by simpa using hd'⟩

end Step

section Orbit

variable {K : Type} [Field K] [Algebra ℚ K] {A : ValuationSubring K}

def loss (p n : ℕ) : ℚ := (p : ℚ) / ((p : ℚ) - 1) ^ 2 * (1 - 1 / (p : ℚ) ^ Nat.log p n)

theorem loss_mono {p n n' : ℕ} (hp : p.Prime) (h : n ≤ n') : loss p n ≤ loss p n' := by
  have h1 : (1 : ℚ) ≤ p := by exact_mod_cast hp.one_le
  unfold loss
  gcongr

theorem loss_nonneg {p : ℕ} (hp : p.Prime) (n : ℕ) : 0 ≤ loss p n := by
  have := loss_mono hp (Nat.zero_le n)
  simpa [loss] using this

theorem loss_le_one {p : ℕ} (hp : 3 ≤ p) (n : ℕ) : loss p n ≤ 1 := by
  have h1 : (3 : ℚ) ≤ p := by exact_mod_cast hp
  have h2 : (p : ℚ) / ((p : ℚ) - 1) ^ 2 ≤ 1 := by
    rw [div_le_one (by nlinarith)]; nlinarith
  have h3 : (0 : ℚ) ≤ 1 / (p : ℚ) ^ Nat.log p n := by positivity
  have h4 : (0 : ℚ) ≤ (p : ℚ) / ((p : ℚ) - 1) ^ 2 := by positivity
  unfold loss
  nlinarith [mul_nonneg h3 h4]

theorem valuation_natCast_ge {p : ℕ} (hp : p.Prime) (h1 : A.valuation (p : K) < 1) {c e : ℕ} (hc : ¬ p ^ (e + 1) ∣ c) :
    A.valuation (p : K) ^ e ≤ A.valuation (c : K) := by
  have hc0 : c ≠ 0 := by rintro rfl; exact hc (dvd_zero _)
  obtain ⟨k, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hc0 p hp.one_lt.ne'
  have hk : k ≤ e := by
    by_contra hk
    exact hc ((pow_dvd_pow p (by omega)).mul_right u)
  have hint : ∀ z : ℤ, A.valuation (z : K) ≤ 1 := fun z => (A.valuation_le_one_iff _).mpr (intCast_mem A z)
  have hu1 : 1 ≤ A.valuation (u : K) := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨s, t, hst⟩ : IsCoprime (p : ℤ) (u : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hu)
    have e1 : (s : K) * p + t * u = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) hst
    have : A.valuation ((s : K) * p + t * u) < 1 := by
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint s)) h1
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint t)) hlt
    rw [e1, map_one] at this
    exact lt_irrefl _ this
  rw [Nat.cast_mul, Nat.cast_pow, map_mul, map_pow]
  exact (pow_le_pow_right_of_le_one' h1.le hk).trans (le_mul_of_one_le_right' hu1)

theorem exists_fixed [IsAlgClosed K] {p : ℕ} (hp : p.Prime) (h1 : A.valuation (p : K) < 1) (H : Subgroup (K ≃ₐ[ℚ] K))
    (hH : ∀ h ∈ H, ∀ x ∈ A, h x ∈ A) (n : ℕ) :
    ∀ (α : K) (a : ℚ) (S : Finset K), S.card ≤ n → (∀ h ∈ H, h α ∈ S) → (∀ h ∈ H, Ge A (p : K) (h α - α) a) →
      ∃ y, (∀ h ∈ H, h y = y) ∧ Ge A (p : K) (α - y) (a - loss p n) := by
  classical
  haveI : CharZero K := algebraRat.charZero K
  have h0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro α a S hS hαS hα
  set T := S.filter fun t => ∃ h ∈ H, h α = t with hT
  have hmem : ∀ t, t ∈ T ↔ ∃ h ∈ H, h α = t := fun t => by
    rw [hT, Finset.mem_filter]
    exact ⟨fun h => h.2, fun ⟨h, hh, e⟩ => ⟨e ▸ hαS h hh, h, hh, e⟩⟩
  have hTn : T.card ≤ n := (Finset.card_filter_le _ _).trans hS
  by_cases h2 : 2 ≤ T.card
  swap
  · refine ⟨α, fun h hh => ?_, by simpa using ge_zero _⟩
    exact Finset.card_le_one.mp (by omega : T.card ≤ 1) _ ((hmem _).mpr ⟨h, hh, rfl⟩) _ ((hmem _).mpr ⟨1, H.one_mem, rfl⟩)
  obtain ⟨j, e, hj0, hj, hdvd, hloss⟩ := GlobalTheory.T.exists_choose_small_padicVal_ax_induction p hp T.card h2
  change _ + loss p _ ≤ loss p _ at hloss
  obtain ⟨β, hβ, hαβ⟩ := exists_root_hasseDeriv h0 h1.le T α (a := a) (fun t ht => by
    obtain ⟨h, hh, rfl⟩ := (hmem t).mp ht
    exact (hα h hh).symm) hj (valuation_natCast_ge hp h1 hdvd)
  set P : K[X] := ∏ t ∈ T, (X - C t) with hP
  have hPd : P.natDegree = T.card := by simp [hP]
  have hQd : (hasseDeriv j P).natDegree = T.card - j := by rw [natDegree_hasseDeriv, hPd]
  have hPmap : ∀ h ∈ H, P.map (h : K →+* K) = P := by
    intro h hh
    rw [hP, Polynomial.map_prod]
    refine Finset.prod_bij (fun t _ => h t) (fun t ht => ?_) (fun t _ t' _ e => h.injective e) (fun t ht => ?_) (fun t _ => by simp)
    · obtain ⟨g, hg, rfl⟩ := (hmem t).mp ht
      exact (hmem _).mpr ⟨h * g, H.mul_mem hh hg, rfl⟩
    · obtain ⟨g, hg, rfl⟩ := (hmem t).mp ht
      exact ⟨(h⁻¹ * g) α, (hmem _).mpr ⟨_, H.mul_mem (H.inv_mem hh) hg, rfl⟩, by
        rw [← AlgEquiv.mul_apply, mul_inv_cancel_left]⟩
  have hQmap : ∀ h ∈ H, (hasseDeriv j P).map (h : K →+* K) = hasseDeriv j P := by
    intro h hh
    ext k
    rw [coeff_map, hasseDeriv_coeff, map_mul, map_natCast, ← coeff_map, hPmap h hh]
  have he : (0 : ℚ) ≤ e / ((T.card - j : ℕ) : ℚ) := by positivity
  obtain ⟨y, hy, hβy⟩ := ih (T.card - j) (by omega) β (a - e / ((T.card - j : ℕ) : ℚ)) (hasseDeriv j P).roots.toFinset
    ((Multiset.toFinset_card_le _).trans ((card_roots' _).trans hQd.le)) (fun h hh => by
      rw [Multiset.mem_toFinset, mem_roots'] at *
      refine ⟨hβ.1, ?_⟩
      rw [← hQmap h hh]
      exact hβ.2.map) (fun h hh => by
      have k1 := hαβ.symm.map h0 (h : K →+* K) (hH h hh) (map_natCast _ p)
      rw [map_sub] at k1
      exact Ge.trans k1 (((hα h hh).mono (by linarith)).trans hαβ))
  have hm := loss_mono hp hTn
  have hnn := loss_nonneg hp (T.card - j)
  exact ⟨y, hy, (hαβ.mono (by linarith)).trans (hβy.mono (by linarith))⟩

end Orbit

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Ord2 in

theorem exists_fixed_congr (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω) (hA : OverL l A) (H : Subgroup (G ℚ Ω)) (hH : H ≤ Dec (F := ℚ) A) (m : ℕ) (x : Ω) (hx : x ∈ A)
    (hcg : ∀ h ∈ H, GlobalTheory.Glue.CgA A l (m + 1) (h x) x) :
    ∃ y ∈ A, (∀ h ∈ H, h y = y) ∧ GlobalTheory.Glue.CgA A l m x y := by
  classical
  have hp : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  have h0 : (l : Ω) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨v, hv, hlv⟩ := hA
  have h1 : A.valuation (l : Ω) < 1 := by simpa using (hv _).mpr hlv
  have hint : IsIntegral ℚ x := (IsAlgClosure.isAlgebraic.isAlgebraic x).isIntegral
  have h3 : 3 ≤ l := by have := hp.two_le; omega
  obtain ⟨y, hy, hxy⟩ := exists_fixed hp h1 H (fun h hh z hz => (apply_mem_iff_of_mem_Dec (hH hh) z).mpr hz) _ x ((m + 1 : ℕ) : ℚ)
    ((minpoly ℚ x).aroots Ω).toFinset le_rfl (fun h _ => by
      rw [Multiset.mem_toFinset, mem_aroots]
      refine ⟨minpoly.ne_zero hint, ?_⟩
      rw [aeval_algHom_apply, minpoly.aeval, map_zero])
    (fun h hh => (ge_natCast_iff h0 h1.le).mpr (hcg h hh))
  have hm : Ge A (l : Ω) (x - y) (m : ℚ) := hxy.mono (by
    have := loss_le_one h3 ((minpoly ℚ x).aroots Ω).toFinset.card
    push_cast; linarith)
  obtain ⟨z, hz, e⟩ := (ge_natCast_iff h0 h1.le).mp hm
  refine ⟨y, ?_, hy, z, hz, e⟩
  have : y = x - (l : Ω) ^ m * z := by rw [← e]; ring
  rw [this]
  exact A.sub_mem hx (A.mul_mem _ _ (A.pow_mem (natCast_mem A l) m) hz)

end GlobalTheory.AxSen
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fixed_congr_axLemma_oddPrime : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A →
  ∀ (H : Subgroup (G ℚ Ω)), H ≤ Dec (F := ℚ) A → ∀ (m : ℕ) (x : Ω), x ∈ A →
  (∀ h ∈ H, GlobalTheory.Glue.CgA A l (m + 1) (h x) x) → ∃ y ∈ A, (∀ h ∈ H, h y = y) ∧ GlobalTheory.Glue.CgA A l m x y := by
  atlas_forward_decl GlobalTheory.AxSen.exists_fixed_congr
end

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix

namespace GlobalTheory.HTTrace

theorem apply_pow (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (σ : G ℚ Ω)
    {ζ : Ω} (hζ : ζ ^ (l ^ r) = 1) :
    σ ζ = ζ ^ ((cycMod ℚ Ω l r σ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  exact cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) ζ hζ

theorem cycMod_eq_one (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) (hm : 1 ≤ m)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ (l ^ m)) (s : G ℚ Ω) (hsζ : s ζ = ζ) : cycMod ℚ Ω l m s = 1 := by
  have hlm : 1 < l ^ m := Nat.one_lt_pow (by omega) (Fact.out : l.Prime).one_lt
  haveI : Fact (1 < l ^ m) := ⟨hlm⟩
  have h1 := apply_pow Ω l m s hζ.pow_eq_one
  rw [hsζ] at h1
  have hv1 : ((cycMod ℚ Ω l m s : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)).val = 1 := by
    have := hζ.pow_inj (i := 1) (j := ((cycMod ℚ Ω l m s : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)).val) hlm (ZMod.val_lt _)
      (by rw [pow_one]; exact h1)
    exact this.symm
  ext
  rw [Units.val_one]
  apply ZMod.val_injective
  rw [hv1, ZMod.val_one]

theorem exists_gen (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω) (hA : OverL l A) (m : ℕ) (hm : 1 ≤ m) (ζ ζ' : Ω) (hζ : IsPrimitiveRoot ζ (l ^ m))
    (hζ' : ζ' ^ (l ^ m) = ζ) :
    ∃ s ∈ Ine (F := ℚ) A, s ζ' = ζ * ζ' := by
  obtain ⟨v, hv, hlv⟩ := hA
  have hAl : A.valuation (l : Ω) < 1 := by simpa using (hv (l : 𝓞 ℚ)).2 hlv
  have hl1 : 1 < l := (Fact.out : l.Prime).one_lt
  have hlm : 1 < l ^ m := Nat.one_lt_pow (by omega) hl1
  have hlt : 1 + l ^ m < l ^ (2 * m) := by
    rw [two_mul, pow_add]; nlinarith
  have hu : IsUnit ((1 + l ^ m : ℕ) : ZMod (l ^ (2 * m))) := by
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out)]
    intro h
    have h2 : l ∣ l ^ m := dvd_pow_self l (by omega)
    have h3 : l ∣ 1 := (Nat.dvd_add_left h2).mp h
    have := Nat.le_of_dvd one_pos h3
    omega
  obtain ⟨⟨s, hs⟩, hsu⟩ := GlobalTheory.InertiaPowers.cycMod_Ine_surjective l Ω A hAl (2 * m) hu.unit
  have hsu' : ((cycMod ℚ Ω l (2 * m) s : (ZMod (l ^ (2 * m)))ˣ) : ZMod (l ^ (2 * m)))
      = ((1 + l ^ m : ℕ) : ZMod (l ^ (2 * m))) := by
    have := congrArg Units.val hsu
    simpa using this
  have hpow2 : ζ' ^ (l ^ (2 * m)) = 1 := by
    rw [two_mul, pow_add, pow_mul, hζ', hζ.pow_eq_one]
  refine ⟨s, hs, ?_⟩
  rw [apply_pow Ω l (2 * m) s hpow2, hsu', ZMod.val_natCast, Nat.mod_eq_of_lt hlt, pow_add, pow_one, hζ', mul_comm]

theorem isPrimitiveRoot_root {Ω : Type} [Field Ω] (l : ℕ) [Fact l.Prime] (m : ℕ) (hm : 1 ≤ m) (ζ ζ' : Ω)
    (hζ : IsPrimitiveRoot ζ (l ^ m)) (hζ' : ζ' ^ (l ^ m) = ζ) : IsPrimitiveRoot ζ' (l ^ (2 * m)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [IsPrimitiveRoot.iff_orderOf, show 2 * (n + 1) = (n + 1 + n) + 1 by ring]
  apply orderOf_eq_prime_pow
  · rw [pow_add, pow_mul, hζ']
    exact hζ.pow_ne_one_of_pos_of_lt (pow_pos (Fact.out : l.Prime).pos n).ne'
      (Nat.pow_lt_pow_right (Fact.out : l.Prime).one_lt (by omega))
  · rw [show (n + 1 + n) + 1 = (n + 1) + (n + 1) by ring, pow_add l (n + 1) (n + 1), pow_mul, hζ', hζ.pow_eq_one]

theorem geom_sum_root {Ω : Type} [Field Ω] (N : ℕ) (u : Ω) (hu : u ^ N = 1) :
    ∃ e : ℕ, ∑ j ∈ Finset.range N, u ^ j = (N : Ω) * e := by
  by_cases h : u = 1
  · exact ⟨1, by simp [h]⟩
  · refine ⟨0, ?_⟩
    have h1 := geom_sum_mul u N
    rw [hu, sub_self] at h1
    simpa using (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 h)

theorem trace_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (N : ℕ) (ζ ζ' : Ω) (hζ : ζ ^ N = 1)
    (hζ'A : ζ' ∈ A) (γ : G ℚ Ω) (h1 : γ ζ = ζ) (h2 : γ ζ' = ζ * ζ') (Q : Polynomial Ω)
    (hQ : ∀ d, Q.coeff d ∈ A ∧ γ (Q.coeff d) = Q.coeff d) :
    ∃ v ∈ A, ∑ j ∈ Finset.range N, (γ ^ j) (Q.eval ζ') = (N : Ω) * v := by
  have hfix : ∀ a : Ω, γ a = a → ∀ j : ℕ, (γ ^ j) a = a := by
    intro a ha j
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, ha, ih]
  have hj : ∀ j : ℕ, (γ ^ j) ζ' = ζ ^ j * ζ' := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, h2, map_mul, hfix ζ h1, ih]; ring
  choose e he using fun d : ℕ => geom_sum_root N (ζ ^ d) (by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow])
  refine ⟨∑ d ∈ Finset.range (Q.natDegree + 1), Q.coeff d * ζ' ^ d * e d,
    sum_mem fun d _ => mul_mem (mul_mem (hQ d).1 (pow_mem hζ'A d)) (natCast_mem A _), ?_⟩
  simp only [Polynomial.eval_eq_sum_range, map_sum, map_mul, map_pow, hj, hfix _ (hQ _).2]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have : ∀ j : ℕ, Q.coeff d * (ζ ^ j * ζ') ^ d = Q.coeff d * ζ' ^ d * (ζ ^ d) ^ j := fun j => by ring
  simp only [this]
  rw [← Finset.mul_sum, he d]; ring

theorem main : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A →
  ∀ (m k : ℕ), k ≤ m → ∀ (ζ ζ' : Ω), IsPrimitiveRoot ζ (l ^ m) → ζ' ^ (l ^ m) = ζ → ∀ o x : Ω, o ∈ A → x ∈ A →
  (∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → s o = o) →
  (∀ s, s ∈ Ine (F := ℚ) A → cycMod ℚ Ω l m s = 1 → ∀ t : ZMod (l ^ m), s ζ' = ζ ^ t.val * ζ' →
    GlobalTheory.Glue.CgA A l k ((t.val : Ω) * o) (s x - x)) →
  GlobalTheory.Glue.CgA A l k ((l : Ω) ^ c * o) 0 := by
  intro l _ hl2
  refine ⟨1, ?_⟩
  intro Ω _ _ _ A hA m k hkm ζ ζ' hζ hζ' o x ho hx hofix hyp
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hlA : (l : Ω) ∈ A := natCast_mem A l
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  rcases k with _ | k
  · exact ⟨(l : Ω) ^ 1 * o, mul_mem (pow_mem hlA 1) ho, by simp⟩
  have hm : 1 ≤ m := by omega
  have hlm : 1 < l ^ m := Nat.one_lt_pow (by omega) (Fact.out : l.Prime).one_lt
  haveI : Fact (1 < l ^ m) := ⟨hlm⟩
  have hprim := isPrimitiveRoot_root l m hm ζ ζ' hζ hζ'
  have hζ'A : ζ' ∈ A := by
    rw [← A.valuation_le_one_iff]
    have h1 := congrArg A.valuation hprim.pow_eq_one
    rw [map_pow, map_one] at h1
    exact (pow_le_one_iff (pow_pos (Fact.out : l.Prime).pos _).ne').1 h1.le
  let H : Subgroup (G ℚ Ω) := Ine (F := ℚ) A ⊓ MulAction.stabilizer (G ℚ Ω) ζ'
  have hHmem : ∀ s : G ℚ Ω, s ∈ H ↔ s ∈ Ine (F := ℚ) A ∧ s ζ' = ζ' := fun s => Iff.rfl
  have hHζ : ∀ s : G ℚ Ω, s ζ' = ζ' → s ζ = ζ := fun s hs => by rw [← hζ', map_pow, hs]
  have hHc : ∀ s : G ℚ Ω, s ζ' = ζ' → cycMod ℚ Ω l m s = 1 := fun s hs =>
    cycMod_eq_one l Ω m hm ζ hζ s (hHζ s hs)
  obtain ⟨y, hyA, hyfix, e, heA, he⟩ := GlobalTheory.T.exists_fixed_congr_axLemma_oddPrime l hl2 Ω A hA H (inf_le_left.trans (Ine_le_Dec A)) k x hx (by
    intro h hh
    obtain ⟨hh1, hh2⟩ := (hHmem h).1 hh
    obtain ⟨z, hz, hze⟩ := hyp h hh1 (hHc h hh2) 0 (by simpa using hh2)
    refine ⟨-z, neg_mem hz, ?_⟩
    simp only [ZMod.val_zero, Nat.cast_zero, zero_mul] at hze
    linear_combination -hze)
  obtain ⟨γ, hγI, hγ⟩ := exists_gen l Ω A hA m hm ζ ζ' hζ hζ'
  have hγζ : γ ζ = ζ := by
    conv_lhs => rw [← hζ']
    rw [map_pow, hγ, mul_pow, hζ.pow_eq_one, one_mul, hζ']
  have hγc := cycMod_eq_one l Ω m hm ζ hζ γ hγζ
  obtain ⟨z, hzA, hz⟩ := hyp γ hγI hγc 1 (by rw [ZMod.val_one, pow_one]; exact hγ)
  rw [ZMod.val_one, Nat.cast_one, one_mul] at hz
  have hγD := Ine_le_Dec A hγI
  set w : Ω := γ e - e + l * z with hw
  have hwA : w ∈ A :=
    add_mem (sub_mem ((apply_mem_iff_of_mem_Dec hγD e).2 heA) heA) (mul_mem hlA hzA)
  have hweq : (l : Ω) ^ k * w = o - (γ y - y) := by
    have h1 := congrArg γ he
    rw [map_sub, map_mul, map_pow, map_natCast] at h1
    rw [hw]
    linear_combination -hz - h1 + he
  have hwfix : ∀ s ∈ Ine (F := ℚ) A, s ζ' = ζ' → s w = w := by
    intro s hs hsζ
    have h1 : γ⁻¹ * s * γ⁻¹⁻¹ ∈ H := by
      refine (hHmem _).2 ⟨conj_mem_Ine ((Dec (F := ℚ) A).inv_mem hγD) hs, ?_⟩
      rw [inv_inv, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hγ, map_mul, hHζ s hsζ, hsζ, ← hγ]
      exact γ.symm_apply_apply ζ'
    have h2 : s (γ y) = γ y := by
      have h3 := congrArg γ (hyfix _ h1)
      rw [inv_inv, AlgEquiv.mul_apply, AlgEquiv.mul_apply, mul_inv_apply] at h3
      exact h3
    have h4 := congrArg s hweq
    rw [map_mul, map_pow, map_natCast, map_sub, map_sub, h2, hyfix s ((hHmem s).2 ⟨hs, hsζ⟩),
      hofix s hs (hHc s hsζ), ← hweq] at h4
    exact mul_left_cancel₀ (pow_ne_zero k hl0) h4
  obtain ⟨Q, hQ, hQw⟩ := GlobalTheory.T.exists_polynomial_in_primitiveRoot_of_inertia_fixed l Ω A hA (2 * m) ζ' hprim w hwA hwfix
  obtain ⟨v, hvA, hv⟩ := trace_mem A (l ^ m) ζ ζ' hζ.pow_eq_one hζ'A γ hγζ hγ Q fun d => ⟨(hQ d).1, (hQ d).2 γ hγI⟩
  rw [hQw] at hv
  have hfix : ∀ a : Ω, γ a = a → ∀ j : ℕ, (γ ^ j) a = a := by
    intro a ha j
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, ha, ih]
  have hj : ∀ j : ℕ, (γ ^ j) ζ' = ζ ^ j * ζ' := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, hγ, map_mul, hfix ζ hγζ, ih]; ring
  have htop : (γ ^ (l ^ m)) y = y :=
    hyfix _ ((hHmem _).2 ⟨pow_mem hγI _, by rw [hj, hζ.pow_eq_one, one_mul]⟩)
  have hsum : ∑ j ∈ Finset.range (l ^ m), (γ ^ j) ((l : Ω) ^ k * w) = ((l ^ m : ℕ) : Ω) * o := by
    have h5 : ∀ j : ℕ, (γ ^ j) ((l : Ω) ^ k * w) = o - ((γ ^ (j + 1)) y - (γ ^ j) y) := fun j => by
      rw [hweq, map_sub, map_sub, hfix o (hofix γ hγI hγc), pow_succ, AlgEquiv.mul_apply]
    simp only [h5]
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun j => (γ ^ j) y), htop]
    simp
  simp only [map_mul, map_pow, map_natCast] at hsum
  rw [← Finset.mul_sum, hv] at hsum
  have hN : ((l ^ m : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have ho' : o = (l : Ω) ^ k * v := mul_left_cancel₀ hN (by linear_combination -hsum)
  exact ⟨v, hvA, by rw [ho']; ring⟩

end GlobalTheory.HTTrace
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_discrete_inertia_kummer_coboundary_bound : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A →
  ∀ (m k : ℕ), k ≤ m → ∀ (ζ ζ' : Ω), IsPrimitiveRoot ζ (l ^ m) → ζ' ^ (l ^ m) = ζ → ∀ o x : Ω, o ∈ A → x ∈ A →
  (∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → s o = o) →
  (∀ s, s ∈ Ine (F := ℚ) A → cycMod ℚ Ω l m s = 1 → ∀ t : ZMod (l ^ m), s ζ' = ζ ^ t.val * ζ' →
    GlobalTheory.Glue.CgA A l k ((t.val : Ω) * o) (s x - x)) →
  GlobalTheory.Glue.CgA A l k ((l : Ω) ^ c * o) 0 := by
  atlas_forward_decl GlobalTheory.HTTrace.main
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2

noncomputable section

namespace GlobalTheory.LambdaValuationPowers.HTCoUniq

section Abstract

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def ball (π : K) : AddSubgroup K where
  carrier := {z | ‖z‖ ≤ ‖π‖}
  zero_mem' := by simp
  add_mem' := fun ha hb => (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  neg_mem' := fun ha => by simpa using ha

theorem mem_ball {π z : K} : z ∈ ball π ↔ ‖z‖ ≤ ‖π‖ := Iff.rfl

theorem mul_mem_ball {π a z : K} (ha : ‖a‖ ≤ 1) (hz : z ∈ ball π) : a * z ∈ ball π := by
  rw [mem_ball, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans hz

theorem ball_pow_mono {p : K} (hp : ‖p‖ < 1) {i k : ℕ} (h : i ≤ k) {z : K} (hz : z ∈ ball (p ^ k)) : z ∈ ball (p ^ i) := by
  refine (mem_ball.1 hz).trans ?_
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) hp.le h

theorem mem_ball_of_mul {p : K} (hp0 : p ≠ 0) {a k : ℕ} (h : a ≤ k) {u z : K} (hu : ‖p ^ a‖ ≤ ‖u‖)
    (hz : u * z ∈ ball (p ^ k)) : z ∈ ball (p ^ (k - a)) := by
  rw [mem_ball] at hz ⊢
  have h1 : 0 < ‖p ^ a‖ := norm_pos_iff.2 (pow_ne_zero _ hp0)
  have e : p ^ k = p ^ a * p ^ (k - a) := by rw [← pow_add, Nat.add_sub_cancel' h]
  rw [e, norm_mul, norm_mul] at hz
  exact le_of_mul_le_mul_left ((mul_le_mul_of_nonneg_right hu (norm_nonneg _)).trans hz) h1

omit [IsUltrametricDist K] in
theorem exists_pow_le {p : K} (hp : ‖p‖ < 1) {u : K} (hu : u ≠ 0) : ∃ a : ℕ, ‖p ^ a‖ ≤ ‖u‖ := by
  obtain ⟨a, ha⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hu) hp
  exact ⟨a, by rw [norm_pow]; exact ha.le⟩

variable {Γ : Type} [Group Γ] [MulSemiringAction Γ K]

theorem smul_mem_ball (hn : ∀ (g : Γ) (x : K), ‖g • x‖ = ‖x‖) (g : Γ) {π z : K} (hz : z ∈ ball π) : g • z ∈ ball π := by
  rw [mem_ball, hn]; exact hz

theorem inv_mul (hn : ∀ (g : Γ) (x : K), ‖g • x‖ = ‖x‖) {lam : Γ → K} {π d x : K} (hd : ‖d‖ ≤ 1) {h t : Γ}
    (hfix : h • lam t = lam t) (hadd : lam (h * t) - lam h - lam t ∈ ball π)
    (h1 : d * lam h - (h • x - x) ∈ ball π) (h2 : d * lam t - (t • x - x) ∈ ball π)
    (h3 : d * lam (h * t) - ((h * t) • x - x) ∈ ball π) : lam t * (h • d - d) ∈ ball π := by
  have e : lam t * (h • d - d) = h • (d * lam t - (t • x - x)) - (d * lam (h * t) - ((h * t) • x - x)) +
      (d * lam h - (h • x - x)) + d * (lam (h * t) - lam h - lam t) := by
    simp only [smul_sub, smul_mul', hfix, mul_smul]; ring
  rw [e]
  exact add_mem (add_mem (sub_mem (smul_mem_ball hn h h2) h3) h1) (mul_mem_ball hd hadd)

theorem pow_sub_mem {lam : Γ → K} {π : K} (hadd : ∀ s t, lam (s * t) - lam s - lam t ∈ ball π) (s : Γ) (n : ℕ) :
    lam (s ^ n) - n * lam s ∈ ball π := by
  induction n with
  | zero => simpa using neg_mem (hadd 1 1)
  | succ n ih =>
    have e : lam (s ^ (n + 1)) - ((n + 1 : ℕ) : K) * lam s =
        (lam (s ^ n * s) - lam (s ^ n) - lam s) + (lam (s ^ n) - n * lam s) := by
      rw [pow_succ]; push_cast; ring
    rw [e]; exact add_mem (hadd _ _) ih

theorem transfer (hn : ∀ (g : Γ) (x : K), ‖g • x‖ = ‖x‖) (H : Subgroup Γ) [Fintype (Γ ⧸ H)] {lam : Γ → K} {π d y : K}
    (hd : ‖d‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hl : ∀ s, ‖lam s‖ ≤ 1) (hfix : ∀ g s : Γ, g • lam s = lam s)
    (hadd : ∀ s t, lam (s * t) - lam s - lam t ∈ ball π)
    (h1 : ∀ h ∈ H, d * lam h - (h • y - y) ∈ ball π) (h2 : ∀ h ∈ H, h • d - d ∈ ball π) :
    ∃ X : K, ‖X‖ ≤ 1 ∧ ∀ s : Γ, (∑ q : Γ ⧸ H, q.out • d) * lam s - (s • X - X) ∈ ball π := by
  refine ⟨∑ q : Γ ⧸ H, (q.out • y - lam q.out * q.out • d), ?_, fun s => ?_⟩
  · have : (∑ q : Γ ⧸ H, (q.out • y - lam q.out * q.out • d)) ∈ ball (1 : K) :=
      sum_mem fun q _ => sub_mem (smul_mem_ball hn _ (by simpa [mem_ball] using hy))
        (mul_mem_ball (hl _) (smul_mem_ball hn _ (by simpa [mem_ball] using hd)))
    simpa [mem_ball] using this
  · rw [← Equiv.sum_comp (MulAction.toPerm s) (fun q : Γ ⧸ H => q.out • d)]
    conv => enter [2, 2, 2]; rw [← Equiv.sum_comp (MulAction.toPerm s)]
    rw [Finset.smul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine sum_mem fun q _ => ?_
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (s * q.out)
    have hq : (MulAction.toPerm s q : Γ ⧸ H).out = s * q.out * h := by
      rw [← hh, MulAction.toPerm_apply, ← MulAction.Quotient.mk_smul_out, smul_eq_mul]
    rw [hq]
    set r := q.out
    have e : (s * r * h) • d * lam s - (s • (r • y - lam r * r • d) - ((s * r * h) • y - lam (s * r * h) * (s * r * h) • d)) =
        - ((s * r) • (d * lam h - ((h : Γ) • y - y))) - (lam r + lam h) * (s * r) • ((h : Γ) • d - d) -
          (s * r * h) • d * (lam (s * r * h) - lam (s * r) - lam h) - (s * r * h) • d * (lam (s * r) - lam s - lam r) := by
      simp only [smul_sub, smul_mul', hfix, mul_smul]; ring
    rw [e]
    have hd' : ‖(s * r * h) • d‖ ≤ 1 := by rw [hn]; exact hd
    refine sub_mem (sub_mem (sub_mem (neg_mem (smul_mem_ball hn _ (h1 h h.2))) (mul_mem_ball ?_ (smul_mem_ball hn _ (h2 h h.2))))
      (mul_mem_ball hd' (hadd _ _))) (mul_mem_ball hd' (hadd _ _))
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hl _) (hl _))

theorem core [CharZero K] {R : Type} [CommRing R] [Algebra R K] (O : Subalgebra R K) [Finite (O →ₐ[R] K)]
    (hO : ∀ a ∈ O, ‖a‖ ≤ 1) (hφ : ∀ (φ : O →ₐ[R] K) a, ‖φ a‖ ≤ 1) {p : K} (hp0 : p ≠ 0) (hp : ‖p‖ < 1) (c : ℕ) :
    ∃ c₁ : ℕ, ∀ (Γ : Type) [Group Γ] [MulSemiringAction Γ K] (_ : ∀ (g : Γ) (x : K), ‖g • x‖ = ‖x‖)
      (_ : ∀ (g : Γ) (a : R), g • algebraMap R K a = algebraMap R K a) (lam : Γ → K) (m k : ℕ) (_ : k ≤ m)
      (_ : ∀ s, ‖lam s‖ ≤ 1) (_ : ∀ g s : Γ, g • lam s = lam s)
      (_ : ∀ s t, lam (s * t) - lam s - lam t ∈ ball (p ^ m)) (s₀ : Γ) (_ : ‖lam s₀‖ = 1)
      (_ : ∀ k' ≤ m, ∀ T X : K, ‖T‖ ≤ 1 → ‖X‖ ≤ 1 → (∀ s : Γ, T * lam s - (s • X - X) ∈ ball (p ^ k')) →
        p ^ c * T ∈ ball (p ^ k')) (d y : K) (_ : ‖d‖ ≤ 1) (_ : ‖y‖ ≤ 1)
      (_ : ∀ h : Γ, (∀ a ∈ O, h • a = a) → d * lam h - (h • y - y) ∈ ball (p ^ k)), d ∈ ball (p ^ (k - c₁)) := by
  classical
  haveI := Fintype.ofFinite (O →ₐ[R] K)
  have hsep : ∀ φ : O →ₐ[R] K, ∃ a : O, φ ≠ O.val → (a : K) - φ a ≠ 0 := by
    intro φ
    by_cases h : φ = O.val
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 h
      exact ⟨a, fun _ => sub_ne_zero.2 (Ne.symm ha)⟩
  choose α hα using hsep
  set S : Finset (O →ₐ[R] K) := Finset.univ.erase O.val with hS
  have hD : (∏ φ ∈ S, ((α φ : K) - φ (α φ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun φ h => hα φ (Finset.ne_of_mem_erase h)
  obtain ⟨b, hb⟩ := exists_pow_le hp hD
  have hN : (((Nat.card (O →ₐ[R] K)).factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  obtain ⟨a, ha⟩ := exists_pow_le hp hN
  refine ⟨a + c + b + 1, ?_⟩
  intro Γ _ _ hn hR lam m k hkm hl hfix hadd s₀ hs₀ U d y hd hy hyp
  by_cases hk : k ≤ a + c + b + 1
  · rw [Nat.sub_eq_zero_of_le hk, mem_ball]; simpa using hd
  let H : Subgroup Γ :=
    { carrier := {h | ∀ a ∈ O, h • a = a}
      one_mem' := fun a _ => one_smul _ _
      mul_mem' := fun {g h} hg hh a ha => by rw [mul_smul, hh a ha, hg a ha]
      inv_mem' := fun {g} hg a ha => by rw [inv_smul_eq_iff, hg a ha] }
  let e : Γ → (O →ₐ[R] K) := fun g =>
    { toRingHom := (MulSemiringAction.toRingHom Γ K g).comp (O.val : O →+* K)
      commutes' := fun r => hR g r }
  have he : ∀ g (a : O), e g a = g • (a : K) := fun _ _ => rfl
  have hinj : Function.Injective fun q : Γ ⧸ H => e q.out := by
    intro q q' hq
    rw [← q.out_eq', ← q'.out_eq', QuotientGroup.eq]
    intro a ha
    rw [mul_smul, inv_smul_eq_iff]
    exact (DFunLike.congr_fun hq ⟨a, ha⟩).symm
  haveI : Finite (Γ ⧸ H) := Finite.of_injective _ hinj
  haveI := Fintype.ofFinite (Γ ⧸ H)
  have hidx : H.index ≤ Nat.card (O →ₐ[R] K) := Nat.card_le_card_of_injective _ hinj
  have ht : s₀ ^ (Nat.card (O →ₐ[R] K)).factorial ∈ H :=
    Subgroup.pow_mem_of_index_ne_zero_of_dvd (Nat.card_pos (α := Γ ⧸ H)).ne' s₀
      fun n h0 hn => Nat.dvd_factorial h0 (hn.trans hidx)
  set t := s₀ ^ (Nat.card (O →ₐ[R] K)).factorial
  have hlt : ‖p ^ a‖ ≤ ‖lam t‖ := by
    by_contra hlt
    push Not at hlt
    have h1 := pow_sub_mem hadd s₀ (Nat.card (O →ₐ[R] K)).factorial
    have h2 : ‖p ^ m‖ < ‖p ^ a‖ := by
      rw [norm_pow, norm_pow]
      exact pow_lt_pow_right_of_lt_one₀ (norm_pos_iff.2 hp0) hp (by omega)
    have h3 := IsUltrametricDist.norm_add_le_max (lam t) (-(lam t - ((Nat.card (O →ₐ[R] K)).factorial : ℕ) * lam s₀))
    rw [norm_neg, neg_sub, add_sub_cancel, norm_mul, hs₀, mul_one] at h3
    exact absurd (ha.trans h3) (not_le.2 (max_lt hlt (lt_of_le_of_lt h1 h2)))
  have hinv : ∀ h ∈ H, h • d - d ∈ ball (p ^ (k - a)) := fun h hh =>
    mem_ball_of_mul hp0 (by omega) hlt (inv_mul hn hd (hfix _ _) (ball_pow_mono hp hkm (hadd _ _))
      (hyp h hh) (hyp t ht) (hyp _ (H.mul_mem hh ht)))
  have hT : ∀ β ∈ O, p ^ c * ∑ q : Γ ⧸ H, q.out • (β * d) ∈ ball (p ^ (k - a)) := by
    intro β hβ
    have hβd : ‖β * d‖ ≤ 1 := by rw [norm_mul]; exact mul_le_one₀ (hO β hβ) (norm_nonneg _) hd
    have hβy : ‖β * y‖ ≤ 1 := by rw [norm_mul]; exact mul_le_one₀ (hO β hβ) (norm_nonneg _) hy
    obtain ⟨X, hX, hXs⟩ := transfer hn H (π := p ^ (k - a)) hβd hβy hl hfix
      (fun s t => ball_pow_mono hp (by omega) (hadd s t))
      (fun h hh => by
        have := mul_mem_ball (hO β hβ) (ball_pow_mono hp (Nat.sub_le k a) (hyp h hh))
        rw [smul_mul', hh β hβ]
        convert this using 1; ring)
      (fun h hh => by
        have := mul_mem_ball (hO β hβ) (hinv h hh)
        rw [smul_mul', hh β hβ]
        convert this using 1; ring)
    refine U _ (by omega) _ X ?_ hX hXs
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun q _ => by rw [hn]; exact hβd
  have hsep : ∀ S' : Finset (O →ₐ[R] K), ∀ β ∈ O,
      p ^ c * ∑ q : Γ ⧸ H, (∏ φ ∈ S', (q.out • (α φ : K) - φ (α φ))) * q.out • (β * d) ∈ ball (p ^ (k - a)) := by
    intro S'
    induction S' using Finset.induction_on with
    | empty => simpa using hT
    | insert φ S' hφS ih =>
      intro β hβ
      have h1 := sub_mem (ih (α φ * β) (O.mul_mem (α φ).2 hβ)) (mul_mem_ball (hφ φ (α φ)) (ih β hβ))
      convert h1 using 1
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.prod_insert hφS]
      simp only [smul_mul']
      ring
  have h1 := hsep S 1 O.one_mem
  have hout : ((1 : Γ) : Γ ⧸ H).out ∈ H := by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (1 : Γ)
    rw [hh, one_mul]; exact h.2
  rw [Finset.sum_eq_single ((1 : Γ) : Γ ⧸ H) (fun q _ hq => ?_) (by simp)] at h1
  · have h2 : (p ^ c * ∏ φ ∈ S, ((α φ : K) - φ (α φ))) * d ∈ ball (p ^ (k - a)) := by
      rw [Finset.prod_congr rfl (fun φ _ => by rw [hout _ (α φ).2])] at h1
      rw [mem_ball] at h1 ⊢
      simpa only [norm_mul, hn, one_mul, mul_assoc] using h1
    have h3 := mem_ball_of_mul hp0 (a := c + b) (by omega)
      (by rw [pow_add, norm_mul, norm_mul]; exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)) h2
    exact ball_pow_mono hp (by omega) h3
  · have hne : e q.out ≠ O.val := by
      intro h
      apply hq
      apply hinj
      show e q.out = e _
      rw [h]
      ext a
      exact (hout _ a.2).symm
    rw [Finset.prod_eq_zero (i := e q.out) (Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩) (by rw [he, sub_self]), zero_mul]

end Abstract

open ReciprocityTheory.Neutral.Cmp

variable {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_isIntegral {a : Qbar l} (hi : IsIntegral ℤ_[l] a) : ‖a‖ ≤ 1 := by
  have hq : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  change spectralValue (minpoly ℚ_[l] a) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hq)]
  intro k
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

theorem norm_algebraMap_padicInt (a : ℤ_[l]) : ‖algebraMap ℤ_[l] (Qbar l) a‖ = ‖a‖ := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l), norm_algebraMap']
  rfl

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {A : ValuationSubring Ω} {j : Ω →+* Qbar l}

omit [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] in

theorem cgA_iff (hj : Compat l A j) (n : ℕ) (x y : Ω) :
    GlobalTheory.Glue.CgA A l n x y ↔ j x - j y ∈ ball ((l : Qbar l) ^ n) := by
  have h0 : ((l : Qbar l) ^ n) ≠ 0 := pow_ne_zero _ natCast_ne_zero
  constructor
  · rintro ⟨z, hz, e⟩
    rw [← map_sub, e, map_mul, map_pow, map_natCast, mul_comm]
    exact mul_mem_ball ((hj z).1 hz) (mem_ball.2 le_rfl)
  · intro h
    have h1 : ((l : Ω) ^ n) ≠ 0 := by
      intro h'
      apply h0
      simpa using congrArg j h'
    refine ⟨(x - y) / (l : Ω) ^ n, (hj _).2 ?_, by field_simp⟩
    rw [map_div₀, map_sub, map_pow, map_natCast, norm_div]
    exact div_le_one_of_le₀ h (norm_nonneg _)

theorem exists_approx (hj : Compat l A j) (n : ℕ) {T : Qbar l} (hT : ‖T‖ ≤ 1) :
    ∃ o ∈ A, T - j o ∈ ball ((l : Qbar l) ^ n) := by
  obtain ⟨o, ho⟩ := Metric.denseRange_iff.1 (denseRange ℚ j) T _
    (norm_pos_iff.2 (pow_ne_zero n (natCast_ne_zero (l := l))))
  rw [dist_eq_norm] at ho
  refine ⟨o, (hj o).2 ?_, ho.le⟩
  have h1 : T - j o ∈ ball ((l : Qbar l) ^ 0) := ball_pow_mono norm_natCast_lt_one (Nat.zero_le n) ho.le
  have h2 : T ∈ ball ((l : Qbar l) ^ 0) := by simpa [mem_ball] using hT
  simpa [mem_ball] using sub_mem h2 h1

omit [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] in
theorem valuation_lt_one (hj : Compat l A j) : A.valuation (l : Ω) < 1 := by
  rw [hj.valuation_lt_one_iff, map_natCast]; exact norm_natCast_lt_one

theorem overL (hj : Compat l A j) : OverL l A := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have h := lies_over_ratPrime A (valuation_lt_one hj)
  refine ⟨ratPrime l, fun x => by simpa using h x, (h (l : 𝓞 ℚ)).1 ?_⟩
  simpa using valuation_lt_one hj

theorem exists_norm_lamv_eq_one (hl2 : l ≠ 2) (hA : A.valuation (l : Ω) < 1) (m : ℕ) :
    ∃ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 ∧ ‖lamv l m s‖ = 1 := by
  have hl := (Fact.out : l.Prime)
  have hu : IsUnit ((1 + l ^ m : ℕ) : ZMod (l ^ (m + 1))) := by
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl]
    intro h
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (by simpa using h))
    · exact hl.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_left (dvd_pow_self l hm.ne')).mp h))
  obtain ⟨⟨s, hs⟩, hsu⟩ := GlobalTheory.InertiaPowers.cycMod_Ine_surjective l Ω A hA (m + 1) hu.unit
  have h1 : PadicInt.toZModPow (m + 1) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = ((1 + l ^ m : ℕ) : ZMod (l ^ (m + 1))) := by
    simpa [cycMod] using congrArg Units.val hsu
  have h2 : ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) - ((1 + l ^ m : ℕ) : ℤ_[l]) ∈
      RingHom.ker (PadicInt.toZModPow (m + 1) : ℤ_[l] →+* ZMod (l ^ (m + 1))) := by
    rw [RingHom.mem_ker, map_sub, h1, map_natCast, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h2
  obtain ⟨b, hb⟩ := h2
  have h3 : ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ m * (1 + l * b) := by
    push_cast at hb
    linear_combination hb
  have hm : cycMod ℚ Ω l m s = 1 := by
    ext
    show PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1
    rw [h3, map_add, map_one, map_mul, map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul, add_zero]
  refine ⟨s, hs, hm, ?_⟩
  obtain ⟨a, ha, ha'⟩ := exists_lamv_eq hm
  have h4 : a = 1 + l * b :=
    mul_left_cancel₀ (pow_ne_zero m (Nat.cast_ne_zero.2 hl.ne_zero)) (add_left_cancel (ha.symm.trans h3))
  rw [ha', norm_algebraMap_padicInt, h4]
  have h5 : ‖(l : ℤ_[l]) * b‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one b))
      (PadicInt.norm_natCast_lt_one_iff.2 dvd_rfl)
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact h5.ne'), norm_one, max_eq_left h5.le]

theorem kummer_sub_lamv {m : ℕ} {ζ' : Ω} (hζ : IsPrimitiveRoot ζ' (l ^ (m + m))) {s : G ℚ Ω} (hs : cycMod ℚ Ω l m s = 1)
    {t : ℕ} (ht : s ζ' = (ζ' ^ l ^ m) ^ t * ζ') : (t : Qbar l) - lamv l m s ∈ ball ((l : Qbar l) ^ m) := by
  have hl := (Fact.out : l.Prime)
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  have h1 : s ζ' = ζ' ^ (PadicInt.toZModPow (m + m) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])).val :=
    cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ' hζ.pow_eq_one
  rw [ht, ← pow_mul, ← pow_succ, pow_eq_pow_mod _ hζ.pow_eq_one] at h1
  have : NeZero (l ^ (m + m)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  replace h1 := congrArg (Nat.cast : ℕ → ZMod (l ^ (m + m)))
    (hζ.pow_inj (Nat.mod_lt _ (pow_pos hl.pos _)) (ZMod.val_lt _) h1)
  rw [ZMod.natCast_mod, ZMod.natCast_zmod_val] at h1
  obtain ⟨a, ha, ha'⟩ := exists_lamv_eq hs
  have h2 : ((l ^ m * t + 1 : ℕ) : ℤ_[l]) - ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) ∈
      RingHom.ker (PadicInt.toZModPow (m + m) : ℤ_[l] →+* ZMod (l ^ (m + m))) := by
    rw [RingHom.mem_ker, map_sub, ← h1, map_natCast, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h2
  obtain ⟨b, hb⟩ := h2
  have h4 : (t : ℤ_[l]) - a = b * (l : ℤ_[l]) ^ m := by
    apply mul_left_cancel₀ (pow_ne_zero m (Nat.cast_ne_zero.2 hl.ne_zero : (l : ℤ_[l]) ≠ 0))
    rw [ha] at hb
    push_cast at hb
    linear_combination hb
  have h5 := congrArg (algebraMap ℤ_[l] (Qbar l)) h4
  rw [map_sub, map_natCast, map_mul, map_pow, map_natCast] at h5
  rw [ha', h5]
  exact mul_mem_ball (by rw [norm_algebraMap_padicInt]; exact PadicInt.norm_le_one b) (mem_ball.2 le_rfl)

def grp (A : ValuationSubring Ω) (j : Ω →+* Qbar l) (m : ℕ) : Subgroup (GK ℚ j) :=
  (Ine (F := ℚ) A ⊓ (cycMod ℚ Ω l m).ker).comap (res j)

theorem exists_grp (hj : Compat l A j) {m : ℕ} {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) A) (hm : cycMod ℚ Ω l m s = 1) :
    ∃ σ : grp A j m, res j σ.1 = s := by
  obtain ⟨σ, rfl⟩ := exists_res_eq hj (Ine_le_Dec A hs)
  exact ⟨⟨σ, ⟨hs, hm⟩⟩, rfl⟩

theorem smul_algebraMap (σ : GK ℚ j) (a : ℤ_[l]) : σ (algebraMap ℤ_[l] (Qbar l) a) = algebraMap ℤ_[l] (Qbar l) a := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]
  exact σ.commutes ⟨_, (Kloc ℚ j).algebraMap_mem _⟩

theorem lamv_add_mem {m : ℕ} {s t : G ℚ Ω} (hs : cycMod ℚ Ω l m s = 1) (ht : cycMod ℚ Ω l m t = 1) :
    lamv l m (s * t) - lamv l m s - lamv l m t ∈ ball ((l : Qbar l) ^ m) := by
  have e : lamv l m (s * t) - lamv l m s - lamv l m t = lamv l m s * (lamv l m t * (l : Qbar l) ^ m) := by
    rw [lamv_mul]; ring
  rw [e]
  exact mul_mem_ball (norm_lamv_le_one hs) (mul_mem_ball (norm_lamv_le_one ht) (mem_ball.2 le_rfl))

theorem smul_lamv {m : ℕ} (σ : GK ℚ j) {s : G ℚ Ω} (hs : cycMod ℚ Ω l m s = 1) : σ (lamv l m s) = lamv l m s := by
  obtain ⟨a, -, ha⟩ := exists_lamv_eq hs
  rw [ha, smul_algebraMap]

theorem uniq_true (hl2 : l ≠ 2) : ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω)
    (j : Ω →+* Qbar l), Compat l A j → ∀ m k : ℕ, k ≤ m → ∀ T X : Qbar l, ‖T‖ ≤ 1 → ‖X‖ ≤ 1 →
    (∀ σ : grp A j m, T * lamv l m (res j σ.1) - (σ • X - X) ∈ ball ((l : Qbar l) ^ k)) →
    (l : Qbar l) ^ c * T ∈ ball ((l : Qbar l) ^ k) := by
  obtain ⟨c, hc⟩ := GlobalTheory.T.tate_discrete_inertia_kummer_coboundary_bound l hl2
  refine ⟨c + 1, ?_⟩
  intro Ω _ _ _ A j hj m k hkm T X hT hX hyp
  have hl := (Fact.out : l.Prime)
  have hp1 := norm_natCast_lt_one (l := l)
  have hpc : ‖(l : Qbar l) ^ c‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hp1.le
  rcases k with _ | n
  · have : T ∈ ball ((l : Qbar l) ^ 0) := by simpa [mem_ball] using hT
    exact mul_mem_ball (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hp1.le) this
  have hn : ∀ (g : grp A j m) (x : Qbar l), ‖g • x‖ = ‖x‖ := fun g x => norm_map_GK j g.1 x
  obtain ⟨s₀, hs₀, hm₀, hu₀⟩ := exists_norm_lamv_eq_one hl2 (valuation_lt_one hj) m
  obtain ⟨t, rfl⟩ := exists_grp hj hs₀ hm₀
  have hinv : ∀ h : grp A j m, h • T - T ∈ ball ((l : Qbar l) ^ (n + 1)) := by
    intro h
    have := inv_mul hn (lam := fun σ : grp A j m => lamv l m (res j σ.1)) hT (h := h) (t := t) (smul_lamv h.1 hm₀)
      (by simpa using ball_pow_mono hp1 hkm (lamv_add_mem h.2.2 hm₀)) (hyp _) (hyp _) (hyp _)
    rwa [mem_ball, norm_mul, hu₀, one_mul] at this
  obtain ⟨o, ho, hTo⟩ := exists_approx hj (n + 1) hT
  obtain ⟨x, hx, hXx⟩ := exists_approx hj (n + 1) hX
  obtain ⟨y, hy, hyfix, hoy⟩ := GlobalTheory.T.exists_fixed_congr_axLemma_oddPrime l hl2 Ω A (overL hj) (Ine (F := ℚ) A ⊓ (cycMod ℚ Ω l m).ker)
    (fun h hh => Ine_le_Dec A hh.1) n o ho (fun h hh => by
      obtain ⟨σ, rfl⟩ := exists_grp hj hh.1 hh.2
      rw [cgA_iff hj, res_spec]
      have := add_mem (sub_mem (hinv σ) (smul_mem_ball hn σ hTo)) hTo
      convert this using 1
      rw [smul_sub]
      show σ.1 (j o) - j o = σ.1 T - T - (σ.1 T - σ.1 (j o)) + (T - j o)
      ring)
  rw [cgA_iff hj] at hoy
  have hTy : T - j y ∈ ball ((l : Qbar l) ^ n) := by
    simpa using add_mem (ball_pow_mono hp1 (Nat.le_succ n) hTo) hoy
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : NeZero ((l ^ (m + m) : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (pow_ne_zero _ hl.ne_zero)⟩
  obtain ⟨ζ', hζ'⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ (m + m))
  have hζ : IsPrimitiveRoot (ζ' ^ l ^ m) (l ^ m) := hζ'.pow (pow_pos hl.pos _) (pow_add l m m)
  have key := hc Ω A (overL hj) m n (by omega) _ ζ' hζ rfl y x hy hx (fun s hs hm => hyfix s ⟨hs, hm⟩)
    (fun s hs hm τ hτ => by
      have h1 := kummer_sub_lamv hζ' hm hτ
      obtain ⟨σ, rfl⟩ := exists_grp hj hs hm
      rw [cgA_iff hj, map_mul, map_natCast, map_sub, res_spec]
      have h2 := ball_pow_mono hp1 (Nat.le_succ n) hXx
      have := sub_mem (add_mem (sub_mem (add_mem (ball_pow_mono hp1 (Nat.le_succ n) (hyp σ))
        (mul_mem_ball hT (ball_pow_mono hp1 (by omega : n ≤ m) h1)))
        (mul_mem_ball (IsUltrametricDist.norm_natCast_le_one (Qbar l) τ.val) hTy)) (smul_mem_ball hn σ h2)) h2
      convert this using 1
      rw [smul_sub]
      show _ = T * _ - (σ.1 X - X) + _ - _ + (σ.1 X - σ.1 (j x)) - _
      ring)
  rw [cgA_iff hj, map_zero, sub_zero, map_mul, map_pow, map_natCast] at key
  have h3 := add_mem key (mul_mem_ball hpc hTy)
  rw [mem_ball] at h3 ⊢
  have e : (l : Qbar l) ^ (c + 1) * T = l * ((l : Qbar l) ^ c * j y + (l : Qbar l) ^ c * (T - j y)) := by ring
  rw [e, pow_succ' _ n, norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left h3 (norm_nonneg _)

theorem main : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ c : Coef l, ∃ c₁ : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω) (j : Ω →+* Qbar l)
    (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (m c₀ : ℕ) (y : (ZMod (l ^ m))ˣ) (h h' : Qbar l),
    GlobalTheory.LambdaValuationPowers.HTCoIn c A j Z m c₀ y h → GlobalTheory.LambdaValuationPowers.HTCoIn c A j Z m c₀ y h' → Cg (m - c₀ - c₁) h h' := by
  intro l _ hl2 c
  have hp1 := norm_natCast_lt_one (l := l)
  obtain ⟨c', hc'⟩ := uniq_true hl2
  obtain ⟨c₁, hc₁⟩ := core (K := Qbar l) c.O (fun a ha => norm_le_one_of_mem ha)
    (fun φ a => norm_le_one_of_isIntegral ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map φ))
    natCast_ne_zero hp1 c'
  refine ⟨c₁, ?_⟩
  intro Ω _ _ _ A j Z m c₀ y h h' H H'
  obtain ⟨hj, f, hf, hyp⟩ := H.sub H'
  obtain ⟨x, hx, hfx⟩ := exists_eq_sub_of_mem_cob hj (neg_mem hf)
  have hyp' : ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 →
      (h - h') * lamv l m s + f s ∈ ball ((l : Qbar l) ^ (m - c₀)) := fun s hs hm => by
    have := hyp s hs hm
    simp only [Cg, sub_self, zero_sub, norm_neg] at this
    exact this
  obtain ⟨s₀, hs₀, hm₀, hu₀⟩ := exists_norm_lamv_eq_one hl2 (valuation_lt_one hj) m
  have hd : ‖h - h'‖ ≤ 1 := by
    have h1 : f s₀ ∈ ball ((l : Qbar l) ^ 0) := by
      obtain ⟨q, o, w, how, e⟩ := mem_cob_iff.1 hf
      rw [e]
      refine sum_mem fun i _ => mul_mem_ball (norm_le_one_of_mem (how i).1) (sub_mem ?_ ?_)
      · simpa [mem_ball] using (hj _).1 ((apply_mem_iff_of_mem_Dec (Ine_le_Dec A hs₀) _).2 (how i).2)
      · simpa [mem_ball] using (hj _).1 (how i).2
    have h2 := sub_mem (ball_pow_mono hp1 (Nat.zero_le _) (hyp' s₀ hs₀ hm₀)) h1
    simpa [mem_ball, hu₀] using h2
  obtain ⟨t, rfl⟩ := exists_grp hj hs₀ hm₀
  refine hc₁ (grp A j m) (fun g x => norm_map_GK j g.1 x) (fun g a => smul_algebraMap g.1 a)
    (fun σ => lamv l m (res j σ.1)) m (m - c₀) (Nat.sub_le _ _) (fun σ => norm_lamv_le_one σ.2.2)
    (fun g σ => smul_lamv g.1 σ.2.2) (fun s t => by simpa using lamv_add_mem s.2.2 t.2.2) t hu₀
    (fun k hk T X hT hX hh => hc' Ω A j hj m k hk T X hT hX hh) (h - h') x hd hx fun σ hσ => ?_
  have h1 := hfx σ.1.toRingEquiv (res j σ.1) (fun w => res_spec j σ.1 w) hσ
  have h2 := hyp' _ σ.2.1 σ.2.2
  convert h2 using 1
  rw [Pi.neg_apply] at h1
  show _ - (σ.1.toRingEquiv x - x) = _
  rw [← h1]; ring

end GlobalTheory.LambdaValuationPowers.HTCoUniq
end
end
