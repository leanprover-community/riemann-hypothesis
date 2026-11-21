import Mathlib
import GroundTheory.FunctionField.PlaceBasic

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.FunctionField

namespace Place

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsFunctionField k K]

theorem valuation_le_exp_iff (v : Place k K) {x : K} (hx : x ≠ 0) (n : ℤ) :
    v.valuation x ≤ WithZero.exp n ↔ -n ≤ v.ord x := by
  rw [v.valuation_eq_exp_neg_ord hx, WithZero.exp_le_exp]
  omega

theorem ord_neg (v : Place k K) (x : K) : v.ord (-x) = v.ord x := by
  simp only [ord, Valuation.map_neg]

theorem ord_add_of_lt (v : Place k K) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : v.ord a < v.ord b) : a + b ≠ 0 ∧ v.ord (a + b) = v.ord a := by
  have hlt : v.valuation b < v.valuation a := by
    rw [v.valuation_eq_exp_neg_ord ha, v.valuation_eq_exp_neg_ord hb, WithZero.exp_lt_exp]
    omega
  have heq : v.valuation (a + b) = v.valuation a := Valuation.map_add_eq_of_lt_left _ hlt
  refine ⟨fun h0 => ?_, by simp only [ord, heq]⟩
  rw [h0, map_zero] at heq
  exact ha ((Valuation.zero_iff _).1 heq.symm)

theorem ne_zero_of_ord_ne_zero (v : Place k K) {x : K} (h : v.ord x ≠ 0) : x ≠ 0 := by
  rintro rfl
  exact h v.ord_zero

theorem exists_ord_pos_forall_ord_neg (v : Place k K) (S : Finset (Place k K)) (hv : v ∉ S) :
    ∃ u : K, u ≠ 0 ∧ 0 < v.ord u ∧ ∀ w ∈ S, w.ord u < 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    obtain ⟨π, hπ⟩ := v.exists_ord_eq_one
    exact ⟨π, v.ne_zero_of_ord_ne_zero (by omega), by omega, by simp⟩
  | insert w S hwS ih =>
    rw [Finset.mem_insert, not_or] at hv
    obtain ⟨y, hy0, hyv, hyS⟩ := ih hv.2

    obtain ⟨y₁, hy₁v, hy₁w⟩ := SetLike.not_le_iff_exists.1 fun h => hv.1 (eq_of_le h)
    obtain ⟨y₂, hy₂w, hy₂v⟩ := SetLike.not_le_iff_exists.1 fun h => hv.1 (eq_of_le h).symm
    have hy₁0 : y₁ ≠ 0 := fun h => hy₁w (h ▸ w.ring.zero_mem)
    have hy₂0 : y₂ ≠ 0 := fun h => hy₂v (h ▸ v.ring.zero_mem)
    have h1 := (v.ord_nonneg_iff hy₁0).2 hy₁v
    have h2 : v.ord y₂ < 0 := not_le.1 fun h => hy₂v ((v.ord_nonneg_iff hy₂0).1 h)
    have h3 : w.ord y₁ < 0 := not_le.1 fun h => hy₁w ((w.ord_nonneg_iff hy₁0).1 h)
    have h4 := (w.ord_nonneg_iff hy₂0).2 hy₂w
    set z := y₁ / y₂ with hz
    have hz0 : z ≠ 0 := div_ne_zero hy₁0 hy₂0
    have hzv : 0 < v.ord z := by rw [hz, v.ord_div hy₁0 hy₂0]; omega
    have hzw : w.ord z < 0 := by rw [hz, w.ord_div hy₁0 hy₂0]; omega
    by_cases hyw : w.ord y < 0
    · refine ⟨y, hy0, hyv, ?_⟩
      intro w' hw'
      rw [Finset.mem_insert] at hw'
      rcases hw' with rfl | hw'
      · exact hyw
      · exact hyS w' hw'
    push Not at hyw
    set r : ℕ := 1 + ∑ w' ∈ S, (w'.ord y).natAbs with hr
    have hzr0 : z ^ r ≠ 0 := pow_ne_zero _ hz0
    have hordr : ∀ w' : Place k K, w'.ord (z ^ r) = r * w'.ord z := fun w' => w'.ord_pow z r
    have hr1 : (1 : ℤ) ≤ r := by exact_mod_cast Nat.le_add_right 1 _
    have hw := w.ord_add_of_lt hzr0 hy0 (by
      rw [hordr]
      have := mul_neg_of_pos_of_neg (show (0 : ℤ) < r by omega) hzw
      omega)
    refine ⟨z ^ r + y, hw.1, ?_, ?_⟩
    · refine lt_of_lt_of_le (lt_min ?_ hyv) (v.min_le_ord_add hzr0 hy0 hw.1)
      rw [hordr]; exact mul_pos (by omega) hzv
    · intro w' hw'
      rw [Finset.mem_insert] at hw'
      rcases hw' with rfl | hw'
      · rw [hw.2, hordr]; exact mul_neg_of_pos_of_neg (by omega) hzw
      · have hyw' := hyS w' hw'
        have habs : ((w'.ord y).natAbs : ℤ) < r := by
          have h' := Finset.single_le_sum (f := fun w'' : Place k K => (w''.ord y).natAbs)
            (fun _ _ => Nat.zero_le _) hw'
          have h'' : (w'.ord y).natAbs < r := by rw [hr]; omega
          exact_mod_cast h''
        rcases le_or_gt 0 (w'.ord z) with hzw' | hzw'
        · have h := w'.ord_add_of_lt hy0 hzr0 (by
            rw [hordr]
            have := mul_nonneg (show (0 : ℤ) ≤ r by omega) hzw'
            omega)
          rw [add_comm, h.2]; exact hyw'
        · have h := w'.ord_add_of_lt hzr0 hy0 (by
            rw [hordr]
            have := mul_le_mul_of_nonneg_left (show w'.ord z ≤ -1 by omega)
              (show (0 : ℤ) ≤ r by omega)
            omega)
          rw [h.2, hordr]; exact mul_neg_of_pos_of_neg (by omega) hzw'

theorem exists_near_one (v : Place k K) (S : Finset (Place k K)) (hv : v ∉ S) (n : ℤ) :
    ∃ e : K, v.valuation (e - 1) ≤ WithZero.exp (-n) ∧
      ∀ w ∈ S, w.valuation e ≤ WithZero.exp (-n) := by
  obtain ⟨u, hu0, huv, huS⟩ := v.exists_ord_pos_forall_ord_neg S hv
  set s : ℕ := n.toNat + 1 with hs
  have hsn : n ≤ (s : ℤ) := by rw [hs]; push_cast; omega
  have hs1 : (1 : ℤ) ≤ s := by rw [hs]; push_cast; omega
  have ha0 : u ^ s ≠ 0 := pow_ne_zero _ hu0
  have hord : ∀ w : Place k K, w.ord (u ^ s) = s * w.ord u := fun w => w.ord_pow u s
  have hv1 := v.ord_add_of_lt one_ne_zero ha0 (by rw [hord, ord_one]; exact mul_pos (by omega) huv)
  refine ⟨(1 + u ^ s)⁻¹, ?_, ?_⟩
  · have heq : (1 + u ^ s)⁻¹ - 1 = -(u ^ s) / (1 + u ^ s) := by
      field_simp [hv1.1]
      ring
    have hne : -(u ^ s) / (1 + u ^ s) ≠ 0 := div_ne_zero (neg_ne_zero.2 ha0) hv1.1
    rw [heq, v.valuation_le_exp_iff hne, v.ord_div (neg_ne_zero.2 ha0) hv1.1, ord_neg, hv1.2,
      ord_one, hord]
    have := mul_le_mul_of_nonneg_left (show 1 ≤ v.ord u by omega) (show (0 : ℤ) ≤ s by omega)
    omega
  · intro w hw
    have hw1 := w.ord_add_of_lt ha0 one_ne_zero (by
      rw [hord, ord_one]; exact mul_neg_of_pos_of_neg (by omega) (huS w hw))
    rw [add_comm] at hw1
    rw [w.valuation_le_exp_iff (inv_ne_zero hw1.1), ord_inv, hw1.2, hord]
    have := mul_le_mul_of_nonneg_left (show w.ord u ≤ -1 by have := huS w hw; omega)
      (show (0 : ℤ) ≤ s by omega)
    omega

theorem exists_approx_const (S : Finset (Place k K)) (y : Place k K → K) (n : ℤ) :
    ∃ z : K, ∀ v ∈ S, v.valuation (z - y v) ≤ WithZero.exp (-n) := by
  classical
  set B : ℤ := ∑ w ∈ S, ∑ v ∈ S, ((w.ord (y v)).natAbs : ℤ) with hB
  have hyB : ∀ v ∈ S, ∀ w ∈ S, w.valuation (y v) ≤ WithZero.exp B := by
    intro v hv w hw
    by_cases h0 : y v = 0
    · rw [h0, map_zero]; exact zero_le
    rw [w.valuation_le_exp_iff h0]
    have h1 : ((w.ord (y v)).natAbs : ℤ) ≤ ∑ v' ∈ S, ((w.ord (y v')).natAbs : ℤ) :=
      Finset.single_le_sum (f := fun v' => ((w.ord (y v')).natAbs : ℤ))
        (fun _ _ => Int.natCast_nonneg _) hv
    have h2 : ∑ v' ∈ S, ((w.ord (y v')).natAbs : ℤ) ≤ B :=
      Finset.single_le_sum (f := fun w' : Place k K => ∑ v' ∈ S, ((w'.ord (y v')).natAbs : ℤ))
        (fun _ _ => Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _) hw
    omega
  choose e he using fun v : Place k K => v.exists_near_one (S.erase v) (S.notMem_erase v) (n + B)
  refine ⟨∑ v ∈ S, y v * e v, fun w hw => ?_⟩
  have hsplit : ∑ v ∈ S, y v * e v - y w =
      y w * (e w - 1) + ∑ v ∈ S.erase w, y v * e v := by
    rw [← Finset.add_sum_erase S _ hw]
    ring
  have hbound : WithZero.exp B * WithZero.exp (-(n + B)) = WithZero.exp (-n) := by
    rw [← WithZero.exp_add]
    congr 1
    ring
  rw [hsplit]
  refine Valuation.map_add_le _ ?_ (Valuation.map_sum_le _ fun v hv => ?_)
  · rw [map_mul, ← hbound]
    exact mul_le_mul' (hyB w hw w hw) (he w).1
  · rw [map_mul, ← hbound]
    exact mul_le_mul' (hyB v (Finset.mem_of_mem_erase hv) w hw)
      ((he v).2 w (Finset.mem_erase.2 ⟨fun h => (Finset.ne_of_mem_erase hv) h.symm, hw⟩))

theorem exists_approx (S : Finset (Place k K)) (y : Place k K → K) (n : Place k K → ℤ) :
    ∃ z : K, ∀ v ∈ S, v.valuation (z - y v) ≤ WithZero.exp (-n v) := by
  set N : ℤ := ∑ v ∈ S, ((n v).natAbs : ℤ) with hN
  obtain ⟨z, hz⟩ := exists_approx_const S y N
  refine ⟨z, fun v hv => (hz v hv).trans ?_⟩
  rw [WithZero.exp_le_exp, neg_le_neg_iff]
  have := Finset.single_le_sum (f := fun v : Place k K => ((n v).natAbs : ℤ))
    (fun _ _ => Int.natCast_nonneg _) hv
  omega

end Place

end GroundTheory.FunctionField
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.FunctionField

open Polynomial

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

theorem exists_eq_zpow_mul_of_mem_adjoin {x : K} (hx : Transcendental k x) {h : K}
    (hh : h ∈ IntermediateField.adjoin k {x}) :
    ∃ m : ℤ, ∃ c : k, ∃ r s : k[X], s.coeff 0 ≠ 0 ∧ (h ≠ 0 → c ≠ 0) ∧
      h = x ^ m * (algebraMap k K c + x * (aeval x r / aeval x s)) := by
  have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ isAlgebraic_zero)
  have hne : ∀ p : k[X], p ≠ 0 → aeval x p ≠ 0 := fun p hp h0 => hx ⟨p, hp, h0⟩
  by_cases h0 : h = 0
  · exact ⟨0, 0, 0, 1, by simp, fun h' => absurd h0 h', by simp [h0]⟩
  obtain ⟨r₀, s₀, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff k _).1 hh
  have hr₀ : r₀ ≠ 0 := by rintro rfl; simp at h0
  have hs₀ : s₀ ≠ 0 := by rintro rfl; simp at h0
  obtain ⟨r₁, hr₁, hr₁'⟩ := r₀.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hr₀ 0
  obtain ⟨s₁, hs₁, hs₁'⟩ := s₀.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hs₀ 0
  simp only [map_zero, sub_zero] at hr₁ hs₁ hr₁' hs₁'
  rw [Polynomial.X_dvd_iff] at hr₁' hs₁'
  generalize r₀.rootMultiplicity 0 = a at hr₁
  generalize s₀.rootMultiplicity 0 = b at hs₁
  subst hr₁ hs₁
  obtain ⟨r, hr⟩ : X ∣ r₁ * C (s₁.coeff 0) - C (r₁.coeff 0) * s₁ := by
    rw [Polynomial.X_dvd_iff, coeff_sub, coeff_mul_C, coeff_C_mul]
    ring
  refine ⟨(a : ℤ) - b, r₁.coeff 0 / s₁.coeff 0, r, s₁ * C (s₁.coeff 0), ?_,
    fun _ => div_ne_zero hr₁' hs₁', ?_⟩
  · rw [coeff_mul_C]; exact mul_ne_zero hs₁' hs₁'
  · have hxr : x * aeval x r = aeval x r₁ * algebraMap k K (s₁.coeff 0) -
        algebraMap k K (r₁.coeff 0) * aeval x s₁ := by
      have := congrArg (aeval x) hr
      simp only [map_sub, map_mul, aeval_C, aeval_X] at this
      rw [← this]
    have hs₁0 : s₁ ≠ 0 := fun h => hs₁' (by rw [h, coeff_zero])
    have hB : aeval x s₁ ≠ 0 := hne s₁ hs₁0
    have hc₀ : algebraMap k K (s₁.coeff 0) ≠ 0 := (_root_.map_ne_zero _).2 hs₁'
    simp only [map_mul, map_pow, aeval_X, aeval_C]
    rw [← mul_div_assoc x, hxr, map_div₀, zpow_sub₀ hx0, zpow_natCast, zpow_natCast]
    field_simp
    ring

namespace Place

variable [IsFunctionField k K]

theorem valuation_aeval_le_one' (v : Place k K) {x : K} (hx : v.valuation x ≤ 1) (p : k[X]) :
    v.valuation (aeval x p) ≤ 1 := by
  rw [v.valuation_le_one_iff] at hx ⊢
  exact (v.ring.valuation_le_one_iff _).1 (v.valuation_aeval_le_one hx p)

theorem valuation_aeval_sub_coeff_zero_le (v : Place k K) {x : K} (hx : v.valuation x ≤ 1)
    (p : k[X]) : v.valuation (aeval x p - algebraMap k K (p.coeff 0)) ≤ v.valuation x := by
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := p)
  have h : aeval x p - algebraMap k K (p.coeff 0) = x * aeval x q := by
    have := congrArg (aeval x) hq
    simpa only [map_sub, map_mul, aeval_C, aeval_X] using this
  rw [h, map_mul]
  exact mul_le_of_le_one_right' (v.valuation_aeval_le_one' hx q)

theorem valuation_aeval_eq_one (v : Place k K) {x : K} (hx : v.valuation x < 1) {s : k[X]}
    (hs : s.coeff 0 ≠ 0) : v.valuation (aeval x s) = 1 := by
  have h1 := v.valuation_algebraMap' hs
  have hlt : v.valuation (aeval x s - algebraMap k K (s.coeff 0)) <
      v.valuation (algebraMap k K (s.coeff 0)) := by
    rw [h1]; exact lt_of_le_of_lt (v.valuation_aeval_sub_coeff_zero_le hx.le s) hx
  have : aeval x s = algebraMap k K (s.coeff 0) + (aeval x s - algebraMap k K (s.coeff 0)) := by
    ring
  rw [this, Valuation.map_add_eq_of_lt_left _ hlt, h1]

theorem valuation_mul_aeval_div_le (v : Place k K) {x : K} (hx : v.valuation x < 1)
    (r : k[X]) {s : k[X]} (hs : s.coeff 0 ≠ 0) :
    v.valuation (x * (aeval x r / aeval x s)) ≤ v.valuation x := by
  rw [map_mul, map_div₀, v.valuation_aeval_eq_one hx hs, div_one]
  exact mul_le_of_le_one_right' (v.valuation_aeval_le_one' hx.le r)

theorem eq_zero_of_valuation_sum_le (v : Place k K) {f : ℕ} {s : Fin f → K}
    (hs1 : ∀ α, v.valuation (s α) ≤ 1)
    (hs : ∀ d : Fin f → k, v.valuation (∑ α, algebraMap k K (d α) * s α) < 1 → d = 0)
    {π : K} (hπ0 : π ≠ 0) (hπ : v.valuation π < 1) :
    ∀ (e : ℕ) (d : Fin e → Fin f → k),
      v.valuation (∑ a, ∑ α, algebraMap k K (d a α) * (π ^ (a : ℕ) * s α)) ≤
        v.valuation π ^ e → d = 0 := by
  intro e
  induction e with
  | zero => intro d _; funext a; exact a.elim0
  | succ e ih =>
    intro d hd
    rw [Fin.sum_univ_succ] at hd
    set T := ∑ a : Fin e, ∑ α, algebraMap k K (d a.succ α) * (π ^ (a : ℕ) * s α) with hT
    have hsplit : ∑ a : Fin e, ∑ α, algebraMap k K (d a.succ α) * (π ^ ((a.succ : Fin (e + 1)) : ℕ) * s α)
        = π * T := by
      rw [hT, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Fin.val_succ, pow_succ]
      ring
    rw [hsplit] at hd
    have hT1 : v.valuation T ≤ 1 := by
      refine Valuation.map_sum_le _ fun a _ => Valuation.map_sum_le _ fun α _ => ?_
      rw [map_mul, map_mul, map_pow]
      refine mul_le_one' ?_ (mul_le_one' (pow_le_one' hπ.le _) (hs1 α))
      by_cases hd0 : d a.succ α = 0
      · rw [hd0, map_zero, map_zero]; exact zero_le
      · rw [v.valuation_algebraMap' hd0]
    have hπT : v.valuation (π * T) ≤ v.valuation π := by
      rw [map_mul]; exact mul_le_of_le_one_right' hT1
    have h0 : d 0 = 0 := by
      apply hs
      have hsum0 : (∑ α, algebraMap k K (d 0 α) * s α) =
          (∑ α, algebraMap k K (d 0 α) * (π ^ ((0 : Fin (e + 1)) : ℕ) * s α) + π * T) - π * T := by
        simp
      rw [hsum0]
      refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ (lt_of_le_of_lt hπT hπ))
      refine lt_of_le_of_lt hd ?_
      rw [pow_succ]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (pow_le_one' hπ.le _)) hπ
    have hTle : v.valuation T ≤ v.valuation π ^ e := by
      have hd' : v.valuation (π * T) ≤ v.valuation π ^ e * v.valuation π := by
        rw [← pow_succ]
        simpa [h0] using hd
      rw [map_mul, mul_comm] at hd'
      exact le_of_mul_le_mul_right hd' (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hπ0))
    have hrest := ih (fun a => d a.succ) hTle
    funext a
    refine Fin.cases h0 (fun b => ?_) a
    exact congrFun hrest b

theorem exists_lift_basis (v : Place k K) :
    ∃ s : Fin v.deg → K, (∀ α, v.valuation (s α) ≤ 1) ∧
      ∀ d : Fin v.deg → k, v.valuation (∑ α, algebraMap k K (d α) * s α) < 1 → d = 0 := by
  let b : Module.Basis (Fin v.deg) k v.ResidueField := Module.finBasisOfFinrankEq k v.ResidueField
    (rfl : Module.finrank k v.ResidueField = v.deg)
  choose s' hs' using fun α : Fin v.deg => IsLocalRing.residue_surjective (b α)
  refine ⟨fun α => (s' α : K), fun α => (v.valuation_le_one_iff _).2 (s' α).2, fun d hd => ?_⟩
  have hmem : (∑ α, algebraMap k K (d α) * (s' α : K)) =
      ((∑ α, algebraMap k v.ring (d α) * s' α : v.ring) : K) := by
    simp
  rw [hmem, v.valuation_lt_one_iff, ← ValuationSubring.valuation_lt_one_iff,
    ← IsLocalRing.residue_eq_zero_iff, map_sum] at hd
  have h : ∑ α, d α • b α = 0 := by
    rw [← hd]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [map_mul, hs', Algebra.smul_def, IsScalarTower.algebraMap_apply k v.ring v.ResidueField,
      IsLocalRing.ResidueField.algebraMap_eq]
  exact funext fun α => Fintype.linearIndependent_iff.1 b.linearIndependent d h α

theorem sum_ord_mul_deg_le {x : K} (hx : Transcendental k x) (S : Finset (Place k K))
    (hS : ∀ v ∈ S, 0 < v.ord x) :
    ∑ v ∈ S, (v.ord x).toNat * v.deg ≤ Module.finrank (IntermediateField.adjoin k {x}) K := by
  classical
  have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ isAlgebraic_zero)
  have := finiteDimensional_adjoin hx
  choose s hs1 hs using fun v : Place k K => v.exists_lift_basis
  choose π hπ using fun v : Place k K => v.exists_ord_eq_one
  have hπ0 : ∀ v : Place k K, π v ≠ 0 := fun v => v.ne_zero_of_ord_ne_zero (by rw [hπ]; norm_num)
  have hπv : ∀ v : Place k K, v.valuation (π v) = WithZero.exp (-1) := fun v => by
    rw [v.valuation_eq_exp_neg_ord (hπ0 v), hπ]
  have hxv : ∀ v : Place k K, v.valuation x = WithZero.exp (-v.ord x) :=
    fun v => v.valuation_eq_exp_neg_ord hx0
  have hx1 : ∀ v ∈ S, v.valuation x < 1 := fun v hv => by
    rw [hxv, ← WithZero.exp_zero, WithZero.exp_lt_exp]; have := hS v hv; omega
  choose y hy using fun (v : Place k K) (a : ℕ) (α : Fin v.deg) =>
    exists_approx S (fun w => if w = v then π v ^ a * s v α else 0) (fun w => w.ord x)
  let ι := Σ v : S, Fin (v.1.ord x).toNat × Fin v.1.deg
  let Y : ι → K := fun i => y i.1.1 i.2.1 i.2.2
  have hP1 : ∀ i : ι, ∀ w ∈ S, w ≠ i.1.1 → w.valuation (Y i) ≤ w.valuation x := by
    intro i w hw hne
    have := hy i.1.1 i.2.1 i.2.2 w hw
    rw [if_neg hne, sub_zero] at this
    rw [hxv]; exact this
  have hP2 : ∀ i : ι, i.1.1.valuation (Y i - π i.1.1 ^ (i.2.1 : ℕ) * s i.1.1 i.2.2) ≤
      i.1.1.valuation x := by
    intro i
    have := hy i.1.1 i.2.1 i.2.2 i.1.1 i.1.2
    rw [if_pos rfl] at this
    rw [hxv]; exact this
  have hP3 : ∀ i : ι, ∀ w ∈ S, w.valuation (Y i) ≤ 1 := by
    intro i w hw
    by_cases hwi : w = i.1.1
    · subst hwi
      have h2 : Y i = (Y i - π i.1.1 ^ (i.2.1 : ℕ) * s i.1.1 i.2.2) +
          π i.1.1 ^ (i.2.1 : ℕ) * s i.1.1 i.2.2 := by ring
      rw [h2]
      refine Valuation.map_add_le _ ((hP2 i).trans (hx1 _ hw).le) ?_
      rw [map_mul, map_pow, hπv]
      exact mul_le_one' (pow_le_one' (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega) _)
        (hs1 _ _)
    · exact (hP1 i w hw hwi).trans (hx1 w hw).le
  have hli : LinearIndependent (IntermediateField.adjoin k {x}) Y := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    by_contra hne
    push Not at hne
    obtain ⟨i₀, hi₀⟩ := hne
    choose m c r t ht hc hgeq using fun i => exists_eq_zpow_mul_of_mem_adjoin hx (g i).2
    have hsum : ∑ i, (g i : K) * Y i = 0 := by simpa [Algebra.smul_def] using hg
    let T := Finset.univ.filter fun i => (g i : K) ≠ 0
    have hT : T.Nonempty := ⟨i₀, by
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun h => hi₀ (Subtype.ext h)⟩
    obtain ⟨j, hjT, hjmin⟩ := T.exists_min_image m hT
    have hgj : (g j : K) ≠ 0 := by simpa [T] using hjT
    let d : ι → k := fun i => if (g i : K) ≠ 0 ∧ m i = m j then c i else 0
    have hA : ∀ w ∈ S, w.valuation (∑ i, algebraMap k K (d i) * Y i) ≤ w.valuation x := by
      intro w hw
      have heq : ∑ i, algebraMap k K (d i) * Y i =
          ∑ i, (algebraMap k K (d i) - x ^ (-m j) * g i) * Y i := by
        simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hsum, mul_zero,
          sub_zero]
      rw [heq]
      refine Valuation.map_sum_le _ fun i _ => ?_
      rw [map_mul]
      refine le_trans (mul_le_mul' ?_ (hP3 i w hw)) (le_of_eq (mul_one _))
      by_cases hgi : (g i : K) = 0
      · have hgi' : g i = 0 := Subtype.ext hgi
        have hdi : d i = 0 := by simp [d, hgi']
        rw [hdi, hgi, map_zero, mul_zero, sub_zero, map_zero]; exact zero_le
      · have hmij : m j ≤ m i := hjmin i (by
          simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]; exact hgi)
        set W := algebraMap k K (c i) + x * (aeval x (r i) / aeval x (t i)) with hW
        have hW1 : w.valuation W ≤ 1 := by
          refine Valuation.map_add_le _ ?_ ((w.valuation_mul_aeval_div_le (hx1 w hw) _ (ht i)).trans
            (hx1 w hw).le)
          by_cases hci : c i = 0
          · rw [hci, map_zero, map_zero]; exact zero_le
          · rw [w.valuation_algebraMap' hci]
        rw [hgeq i]
        rcases hmij.lt_or_eq with hlt | heq'
        · have hdi : d i = 0 := by
            simp only [d, ne_eq, hgi, not_false_eq_true, true_and]
            rw [if_neg (by omega)]
          obtain ⟨n, hn⟩ : ∃ n : ℕ, m i - m j = n + 1 := ⟨(m i - m j - 1).toNat, by omega⟩
          have hpow : x ^ (-m j) * (x ^ m i * W) = x ^ (n + 1) * W := by
            rw [← mul_assoc, ← zpow_add₀ hx0, show -m j + m i = ((n + 1 : ℕ) : ℤ) by push_cast; omega,
              zpow_natCast]
          rw [hdi, map_zero, zero_sub, hpow, Valuation.map_neg, map_mul, map_pow, pow_succ]
          refine le_trans (mul_le_of_le_one_right' hW1) ?_
          exact mul_le_of_le_one_left' (pow_le_one' (hx1 w hw).le _)
        · have hdi : d i = c i := by
            simp only [d, ne_eq, hgi, not_false_eq_true, true_and]
            rw [if_pos heq'.symm]
          have hpow : x ^ (-m j) * (x ^ m i * W) = W := by
            rw [← mul_assoc, ← zpow_add₀ hx0, ← heq', neg_add_cancel, zpow_zero, one_mul]
          rw [hdi, hpow, hW, sub_add_cancel_left, Valuation.map_neg]
          exact w.valuation_mul_aeval_div_le (hx1 w hw) _ (ht i)
    obtain ⟨⟨v, hvS⟩, a₀, α₀⟩ := j
    have hcj : d ⟨⟨v, hvS⟩, a₀, α₀⟩ ≠ 0 := by
      simp only [d, ne_eq, hgj, not_false_eq_true, and_self, if_true]
      exact hc _ hgj
    let v₀ : S := ⟨v, hvS⟩
    let B : ι → K := fun i => if i.1 = v₀ then π i.1.1 ^ (i.2.1 : ℕ) * s i.1.1 i.2.2 else 0
    have hBsum : ∑ i, algebraMap k K (d i) * B i =
        ∑ a : Fin (v.ord x).toNat, ∑ α : Fin v.deg,
          algebraMap k K (d ⟨v₀, a, α⟩) * (π v ^ (a : ℕ) * s v α) := by
      rw [Fintype.sum_sigma, Finset.sum_eq_single v₀]
      · rw [Fintype.sum_prod_type]
        simp [B, v₀]
      · intro b _ hb
        refine Finset.sum_eq_zero fun p _ => ?_
        simp [B, hb]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hrest : v.valuation (∑ i, algebraMap k K (d i) * (Y i - B i)) ≤ v.valuation x := by
      refine Valuation.map_sum_le _ fun i _ => ?_
      rw [map_mul]
      refine le_trans (mul_le_of_le_one_left' ?_) ?_
      · by_cases hdi : d i = 0
        · rw [hdi, map_zero, map_zero]; exact zero_le
        · rw [v.valuation_algebraMap' hdi]
      · obtain ⟨⟨w, hw⟩, a, α⟩ := i
        by_cases hwv : w = v
        · subst hwv
          have hB : B ⟨⟨w, hw⟩, a, α⟩ = π w ^ (a : ℕ) * s w α := if_pos rfl
          rw [hB]; exact hP2 ⟨⟨w, hw⟩, a, α⟩
        · have hB : B ⟨⟨w, hw⟩, a, α⟩ = 0 := if_neg (fun h => hwv (congrArg Subtype.val h))
          rw [hB, sub_zero]
          exact hP1 _ v hvS (fun h => hwv h.symm)
    have hmain : v.valuation (∑ a : Fin (v.ord x).toNat, ∑ α : Fin v.deg,
        algebraMap k K (d ⟨v₀, a, α⟩) * (π v ^ (a : ℕ) * s v α)) ≤
        v.valuation (π v) ^ (v.ord x).toNat := by
      have hpe : v.valuation (π v) ^ (v.ord x).toNat = v.valuation x := by
        rw [hπv, ← WithZero.exp_nsmul, hxv, nsmul_eq_mul, Int.toNat_of_nonneg (hS v hvS).le]
        congr 1; ring
      rw [hpe, ← hBsum]
      have h3 : ∑ i, algebraMap k K (d i) * B i =
          ∑ i, algebraMap k K (d i) * Y i - ∑ i, algebraMap k K (d i) * (Y i - B i) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [h3]
      exact le_trans (Valuation.map_sub _ _ _) (max_le (hA v hvS) hrest)
    have hzero := v.eq_zero_of_valuation_sum_le (hs1 v) (hs v) (hπ0 v)
      (by rw [hπv, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega) _ _ hmain
    exact hcj (congrFun (congrFun hzero a₀) α₀)
  have hcard := hli.fintype_card_le_finrank
  have hι : Fintype.card ι = ∑ v ∈ S, (v.ord x).toNat * v.deg := by
    simp only [ι, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
    exact Finset.sum_coe_sort S (fun v => (v.ord x).toNat * v.deg)
  rw [← hι]
  exact hcard

theorem finite_ord_pos (x : K) : {v : Place k K | 0 < v.ord x}.Finite := by
  classical
  by_cases hx0 : x = 0
  · convert Set.finite_empty
    ext v
    simp [hx0]
  by_cases halg : IsAlgebraic k x
  · convert Set.finite_empty
    ext v
    simp [v.ord_eq_zero_of_isAlgebraic halg hx0]
  by_contra hinf
  obtain ⟨S, hSsub, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf
    (Module.finrank (IntermediateField.adjoin k {x}) K + 1)
  have h := sum_ord_mul_deg_le halg S fun v hv => hSsub hv
  have h2 : S.card ≤ ∑ v ∈ S, (v.ord x).toNat * v.deg := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun v hv => ?_
    have h1 : 1 ≤ (v.ord x).toNat := by have := hSsub hv; simp only [Set.mem_ofPred_eq] at this; omega
    have h2 := v.deg_pos
    nlinarith
  omega

theorem finite_ord_ne_zero (x : K) : {v : Place k K | v.ord x ≠ 0}.Finite := by
  refine ((finite_ord_pos x).union (finite_ord_pos x⁻¹)).subset fun v hv => ?_
  simp only [Set.mem_ofPred_eq, Set.mem_union, ord_inv] at hv ⊢
  omega

end Place

end GroundTheory.FunctionField
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.FunctionField

open Module

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

abbrev Divisor := Place k K →₀ ℤ

variable {k K}

namespace Divisor

noncomputable def deg : Divisor k K →+ ℤ :=
  Finsupp.liftAddHom fun v => AddMonoidHom.mulRight (v.deg : ℤ)

theorem deg_apply (D : Divisor k K) : deg D = D.sum fun v n => n * v.deg := by
  simp [deg, Finsupp.liftAddHom_apply]

@[simp]
theorem deg_single (v : Place k K) (n : ℤ) : deg (Finsupp.single v n) = n * v.deg := by
  simp [deg]

theorem deg_eq_sum (D : Divisor k K) : deg D = ∑ v ∈ D.support, D v * v.deg := by
  rw [deg_apply, Finsupp.sum]

theorem deg_nonneg {D : Divisor k K} (hD : 0 ≤ D) : 0 ≤ deg D := by
  rw [deg_eq_sum]
  exact Finset.sum_nonneg fun v _ => mul_nonneg (by simpa using Finsupp.le_def.1 hD v)
    (Int.natCast_nonneg _)

variable [IsFunctionField k K]

theorem eq_zero_of_deg_eq_zero {D : Divisor k K} (hD : 0 ≤ D) (h : deg D = 0) : D = 0 := by
  rw [deg_eq_sum] at h
  have hnn : ∀ v ∈ D.support, 0 ≤ D v * v.deg := fun v _ =>
    mul_nonneg (by simpa using Finsupp.le_def.1 hD v) (Int.natCast_nonneg _)
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h
  ext v
  by_cases hv : v ∈ D.support
  · have := h0 v hv
    have hdeg : (0 : ℤ) < v.deg := by exact_mod_cast v.deg_pos
    rcases mul_eq_zero.1 this with h' | h'
    · simpa using h'
    · omega
  · simpa using hv

end Divisor

variable [IsFunctionField k K]

noncomputable def divisor (x : K) : Divisor k K :=
  Finsupp.ofSupportFinite (fun v : Place k K => v.ord x) (Place.finite_ord_ne_zero x)

@[simp]
theorem divisor_apply (x : K) (v : Place k K) : divisor x v = v.ord x := rfl

@[simp]
theorem divisor_zero : divisor (0 : K) = (0 : Divisor k K) := by
  ext v; simp

@[simp]
theorem divisor_one : divisor (1 : K) = (0 : Divisor k K) := by
  ext v; simp

theorem divisor_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    divisor (x * y) = (divisor x + divisor y : Divisor k K) := by
  ext v; simp [v.ord_mul hx hy]

@[simp]
theorem divisor_inv (x : K) : divisor x⁻¹ = -(divisor x : Divisor k K) := by
  ext v; simp [Place.ord_inv]


theorem divisor_eq_zero_of_isAlgebraic {x : K} (hx : IsAlgebraic k x) (hx0 : x ≠ 0) :
    divisor x = (0 : Divisor k K) := by
  ext v; simp [v.ord_eq_zero_of_isAlgebraic hx hx0]

noncomputable def divisorHom : Additive Kˣ →+ Divisor k K where
  toFun x := divisor ((x.toMul : Kˣ) : K)
  map_zero' := by simp
  map_add' x y := by
    simp only [toMul_add, Units.val_mul]
    exact divisor_mul (Additive.toMul x).ne_zero (Additive.toMul y).ne_zero


variable (k K) in

noncomputable def principalDivisors : AddSubgroup (Divisor k K) := (divisorHom (k := k)).range

theorem mem_principalDivisors {D : Divisor k K} :
    D ∈ principalDivisors k K ↔ ∃ x : K, x ≠ 0 ∧ divisor x = D := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, (Additive.toMul x).ne_zero, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Additive.ofMul (Units.mk0 x hx), rfl⟩

noncomputable def zeroDivisor (x : K) : Divisor k K := divisor x ⊔ 0

noncomputable def poleDivisor (x : K) : Divisor k K := divisor x⁻¹ ⊔ 0

@[simp]
theorem zeroDivisor_apply (x : K) (v : Place k K) :
    zeroDivisor x v = max (v.ord x) 0 := rfl

@[simp]
theorem poleDivisor_apply (x : K) (v : Place k K) :
    poleDivisor x v = max (-v.ord x) 0 := by
  simp [poleDivisor, Finsupp.sup_apply]


theorem poleDivisor_nonneg (x : K) : (0 : Divisor k K) ≤ poleDivisor x :=
  Finsupp.le_def.2 fun v => by simp

@[simp]
theorem poleDivisor_inv (x : K) : poleDivisor x⁻¹ = (zeroDivisor x : Divisor k K) := by
  simp [poleDivisor, zeroDivisor]

@[simp]
theorem zeroDivisor_inv (x : K) : zeroDivisor x⁻¹ = (poleDivisor x : Divisor k K) := rfl

theorem zeroDivisor_sub_poleDivisor (x : K) :
    zeroDivisor x - poleDivisor x = (divisor x : Divisor k K) := by
  ext v
  simp only [Finsupp.coe_sub, Pi.sub_apply, zeroDivisor_apply, poleDivisor_apply, divisor_apply]
  rcases le_total 0 (v.ord x) with h | h
  · rw [max_eq_left h, max_eq_right (by omega)]; ring
  · rw [max_eq_right h, max_eq_left (by omega)]; ring

namespace Divisor

def L (D : Divisor k K) : Submodule k K where
  carrier := {z | ∀ v : Place k K, v.valuation z ≤ WithZero.exp (D v)}
  add_mem' {a b} ha hb v := Valuation.map_add_le _ (ha v) (hb v)
  zero_mem' v := by rw [map_zero]; exact zero_le
  smul_mem' c z hz v := by
    rw [Algebra.smul_def, map_mul]
    by_cases hc : c = 0
    · rw [hc, map_zero, map_zero, zero_mul]; exact zero_le
    · rw [v.valuation_algebraMap' hc, one_mul]; exact hz v

theorem mem_L {D : Divisor k K} {z : K} :
    z ∈ L D ↔ ∀ v : Place k K, v.valuation z ≤ WithZero.exp (D v) := Iff.rfl

theorem mem_L_iff_le {D : Divisor k K} {z : K} (hz : z ≠ 0) :
    z ∈ L D ↔ 0 ≤ divisor z + D := by
  rw [mem_L, Finsupp.le_def]
  refine forall_congr' fun v => ?_
  rw [v.valuation_le_exp_iff hz]
  simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Pi.add_apply, divisor_apply]
  omega

theorem L_mono {D E : Divisor k K} (h : D ≤ E) : L D ≤ L E := fun _z hz v =>
  (hz v).trans (WithZero.exp_le_exp.2 (Finsupp.le_def.1 h v))

theorem mem_L_zero {z : K} : z ∈ L (0 : Divisor k K) ↔ IsAlgebraic k z := by
  rw [Place.isAlgebraic_iff_forall_mem, mem_L]
  refine forall_congr' fun v => ?_
  rw [Finsupp.coe_zero, Pi.zero_apply, WithZero.exp_zero, v.valuation_le_one_iff]

theorem L_eq_bot_of_nonpos {D : Divisor k K} (hD : D ≤ 0) {v : Place k K} (hv : D v < 0) :
    L D = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Submodule.mem_bot]
  by_contra hz0
  have hall : ∀ w : Place k K, z ∈ w.ring := fun w =>
    (w.valuation_le_one_iff z).1 ((hz w).trans (by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]; simpa using Finsupp.le_def.1 hD w))
  have h0 := v.ord_eq_zero_of_isAlgebraic (Place.isAlgebraic_iff_forall_mem.2 hall) hz0
  have := hz v
  rw [v.valuation_le_exp_iff hz0, h0] at this
  omega

theorem finiteDimensional_L_add_single (D : Divisor k K) (v : Place k K)
    [FiniteDimensional k (L D)] :
    FiniteDimensional k (L (D + Finsupp.single v 1)) ∧
      finrank k (L (D + Finsupp.single v 1)) ≤ finrank k (L D) + v.deg := by
  classical
  set E := D + Finsupp.single v 1 with hE
  have hEv : E v = D v + 1 := by simp [E]
  have hEw : ∀ w, w ≠ v → E w = D w := fun w hw => by
    simp [E, Ne.symm hw]
  obtain ⟨t, ht⟩ := v.valuation_surjective (WithZero.exp (-(D v + 1)))
  have hmem : ∀ z : L E, t * (z : K) ∈ v.ring := fun z => by
    rw [← v.valuation_le_one_iff, map_mul, ht]
    calc WithZero.exp (-(D v + 1)) * v.valuation (z : K)
        ≤ WithZero.exp (-(D v + 1)) * WithZero.exp (E v) := mul_le_mul' le_rfl (z.2 v)
      _ = 1 := by rw [hEv, ← WithZero.exp_add]; simp
  let φ : L E →ₗ[k] v.ResidueField :=
    { toFun := fun z => IsLocalRing.residue v.ring ⟨t * z, hmem z⟩
      map_add' := fun a b => by
        rw [← map_add]
        congr 1
        ext
        simp [mul_add]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, Algebra.smul_def,
          IsScalarTower.algebraMap_apply k v.ring v.ResidueField,
          IsLocalRing.ResidueField.algebraMap_eq, ← map_mul]
        congr 1
        ext
        change t * ((c • a : L E) : K) = (algebraMap k v.ring c : K) * (t * a)
        rw [Submodule.coe_smul, Algebra.smul_def, Place.coe_algebraMap_apply]
        ring }
  have hker : ∀ z : L E, φ z = 0 ↔ (z : K) ∈ L D := by
    intro z
    change IsLocalRing.residue v.ring ⟨t * z, hmem z⟩ = 0 ↔ _
    rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    change v.ring.valuation (t * z) < 1 ↔ _
    rw [← v.valuation_lt_one_iff, map_mul, ht]
    constructor
    · intro h w
      by_cases hw : w = v
      · rw [hw]
        by_cases hz : (z : K) = 0
        · rw [hz, map_zero]; exact zero_le
        · rw [v.valuation_eq_exp_neg_ord hz, ← WithZero.exp_add, ← WithZero.exp_zero,
            WithZero.exp_lt_exp] at h
          rw [v.valuation_eq_exp_neg_ord hz, WithZero.exp_le_exp]
          omega
      · rw [← hEw w hw]; exact z.2 w
    · intro h
      calc WithZero.exp (-(D v + 1)) * v.valuation (z : K)
          ≤ WithZero.exp (-(D v + 1)) * WithZero.exp (D v) := mul_le_mul' le_rfl (h v)
        _ < 1 := by rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  let ψ : LinearMap.ker φ →ₗ[k] L D :=
    ((L E).subtype.comp (LinearMap.ker φ).subtype).codRestrict (L D)
      fun z => (hker z.1).1 (LinearMap.mem_ker.1 z.2)
  have hψ : Function.Injective ψ := fun a b h => by
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  have : FiniteDimensional k (LinearMap.ker φ) := Module.Finite.of_injective ψ hψ
  have hrank := LinearMap.rank_range_add_rank_ker φ
  have hfin : FiniteDimensional k (L E) := by
    apply Module.rank_lt_aleph0_iff.1
    rw [← hrank]
    exact Cardinal.add_lt_aleph0 (Module.rank_lt_aleph0 k _) (Module.rank_lt_aleph0 k _)
  refine ⟨hfin, ?_⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 : finrank k (LinearMap.range φ) ≤ v.deg := Submodule.finrank_le _
  have h3 : finrank k (LinearMap.ker φ) ≤ finrank k (L D) :=
    LinearMap.finrank_le_finrank_of_injective hψ
  omega

theorem finiteDimensional_L_of_le_of_deg_lt (n : ℕ) :
    ∀ {D E : Divisor k K}, D ≤ E → deg (E - D) < n → FiniteDimensional k (L D) →
      FiniteDimensional k (L E) ∧
        (finrank k (L E) : ℤ) ≤ finrank k (L D) + deg E - deg D := by
  classical
  induction n with
  | zero =>
    intro D E hDE hn _
    have := deg_nonneg (sub_nonneg.2 hDE)
    omega
  | succ n ih =>
    intro D E hDE hn hD
    by_cases hED : E = D
    · subst hED
      exact ⟨hD, by omega⟩
    obtain ⟨v, hv⟩ : ∃ v, D v < E v := by
      by_contra h
      push Not at h
      exact hED (le_antisymm (Finsupp.le_def.2 h) hDE)
    set E' := E - Finsupp.single v 1 with hE'
    have hDE' : D ≤ E' := Finsupp.le_def.2 fun w => by
      rw [hE', Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]
      split_ifs with h
      · subst h; omega
      · have := Finsupp.le_def.1 hDE w; omega
    have hn' : deg (E' - D) < n := by
      have h1 : deg (E' - D) = deg (E - D) - v.deg := by
        rw [hE', map_sub, map_sub, map_sub, deg_single]; ring
      have := v.deg_pos
      omega
    obtain ⟨hfin', hle'⟩ := ih hDE' hn' hD
    have hE : E = E' + Finsupp.single v 1 := by rw [hE']; abel
    have := hfin'
    obtain ⟨hfin, hle⟩ := finiteDimensional_L_add_single E' v
    rw [← hE] at hfin hle
    refine ⟨hfin, ?_⟩
    have hdeg : deg E = deg E' + v.deg := by rw [hE, map_add, deg_single, one_mul]
    have : (finrank k (L E) : ℤ) ≤ finrank k (L E') + v.deg := by exact_mod_cast hle
    omega

theorem finiteDimensional_L_of_le {D E : Divisor k K} (hDE : D ≤ E)
    [FiniteDimensional k (L D)] :
    FiniteDimensional k (L E) ∧
      (finrank k (L E) : ℤ) ≤ finrank k (L D) + deg E - deg D :=
  finiteDimensional_L_of_le_of_deg_lt ((deg (E - D)).toNat + 1) hDE (by omega) inferInstance

instance (D : Divisor k K) : FiniteDimensional k (L D) := by
  classical
  obtain ⟨v⟩ := Place.nonempty (k := k) (K := K)
  have hbot : L (-Finsupp.single v 1 : Divisor k K) = ⊥ :=
    L_eq_bot_of_nonpos (v := v) (Finsupp.le_def.2 fun w => by
      have h := Finsupp.single_apply (a := v) (a' := w) (b := (1 : ℤ))
      simp only [Finsupp.coe_neg, Pi.neg_apply, Finsupp.coe_zero, Pi.zero_apply]
      split_ifs at h <;> omega) (by simp)
  have : FiniteDimensional k (L (-Finsupp.single v 1 : Divisor k K)) := by
    rw [hbot]; infer_instance
  have := (finiteDimensional_L_of_le
    (le_sup_right : (-Finsupp.single v 1 : Divisor k K) ≤ D ⊔ -Finsupp.single v 1)).1
  exact Module.Finite.of_injective
    (Submodule.inclusion (L_mono (le_sup_left : D ≤ D ⊔ -Finsupp.single v 1)))
    (Submodule.inclusion_injective _)

theorem finrank_L_le_of_le {D E : Divisor k K} (hDE : D ≤ E) :
    (finrank k (L E) : ℤ) ≤ finrank k (L D) + deg E - deg D :=
  (finiteDimensional_L_of_le hDE).2

theorem L_zero :
    L (0 : Divisor k K) = Subalgebra.toSubmodule (algebraicClosure k K).toSubalgebra := by
  ext z
  rw [mem_L_zero]
  simp [mem_algebraicClosure_iff]

theorem finrank_L_zero : finrank k (L (0 : Divisor k K)) = finrank k (algebraicClosure k K) := by
  rw [L_zero]
  rfl

theorem finrank_L_le_deg_add {D : Divisor k K} (hD : 0 ≤ D) :
    (finrank k (L D) : ℤ) ≤ deg D + finrank k (algebraicClosure k K) := by
  have := finrank_L_le_of_le hD
  rw [finrank_L_zero, map_zero] at this
  omega


end Divisor

end GroundTheory.FunctionField
end
