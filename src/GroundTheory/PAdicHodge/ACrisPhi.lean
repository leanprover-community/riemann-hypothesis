import Mathlib
import GroundTheory.PAdicHodge.ACrisLog

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open PowerSeries

theorem X_dvd_one_add_X_pow_sub_one {R : Type*} [CommRing R] (q : ℕ) :
    (Polynomial.X : Polynomial R) ∣ (1 + Polynomial.X) ^ q - 1 := by
  have h := sub_dvd_pow_sub_pow (1 + Polynomial.X : Polynomial R) 1 q
  rwa [one_pow, add_sub_cancel_left] at h

theorem coeff_one_add_X_pow_sub_one_pow_of_lt {R : Type*} [CommRing R] (q : ℕ) {m n : ℕ}
    (h : m < n) : (((1 + Polynomial.X : Polynomial R) ^ q - 1) ^ n).coeff m = 0 := by
  obtain ⟨g, hg⟩ := pow_dvd_pow_of_dvd (X_dvd_one_add_X_pow_sub_one (R := R) q) n
  rw [hg, Polynomial.coeff_X_pow_mul', if_neg (not_le.2 h)]

theorem one_add_X_mul_mk_neg_one_pow :
    (1 + X : ℚ⟦X⟧) * mk (fun n => algebraMap ℚ ℚ ((-1 : ℚ) ^ n)) = 1 := by
  ext n
  rw [add_mul, one_mul, map_add]
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_mk, coeff_mk, coeff_one, if_neg n.succ_ne_zero]
    simp [pow_succ]

theorem hasSubst_one_add_X_pow_sub_one (q : ℕ) : HasSubst ((1 + X : ℚ⟦X⟧) ^ q - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp)

theorem PowerSeries.log_subst_one_add_X_pow_sub_one (q : ℕ) :
    (log ℚ).subst ((1 + X : ℚ⟦X⟧) ^ q - 1) = (q : ℚ⟦X⟧) * log ℚ := by
  set U : ℚ⟦X⟧ := (1 + X) ^ q - 1 with hU
  have hs : HasSubst U := hasSubst_one_add_X_pow_sub_one q
  set G : ℚ⟦X⟧ := mk fun n => algebraMap ℚ ℚ ((-1 : ℚ) ^ n)
  have hG : (1 + U) * G.subst U = 1 := by
    have h := congrArg (substAlgHom (R := ℚ) hs) one_add_X_mul_mk_neg_one_pow
    rw [map_mul, map_add, map_one] at h
    simp only [coe_substAlgHom] at h
    rwa [subst_X hs] at h
  have h1U : 1 + U = (1 + X) ^ q := by rw [hU]; ring
  apply derivative.ext
  · have hd : d⁄dX ℚ ((log ℚ).subst U) = d⁄dX ℚ ((q : ℚ⟦X⟧) * log ℚ) := by
      have hunit : IsUnit (1 + X : ℚ⟦X⟧) := by
        rw [isUnit_iff_constantCoeff]; simp
      apply hunit.mul_left_cancel
      rw [derivative_subst hs, deriv_log, Derivation.leibniz, deriv_log]
      rcases q with _ | q
      · simp [hU]
      · have hdU : d⁄dX ℚ U = ((q + 1 : ℕ) : ℚ⟦X⟧) * (1 + X) ^ q := by
          rw [hU, map_sub, derivative_pow, Derivation.map_one_eq_zero, sub_zero, map_add,
            Derivation.map_one_eq_zero, derivative_X, zero_add, mul_one, Nat.add_sub_cancel]
        rw [hdU]
        have hc : d⁄dX ℚ ((q + 1 : ℕ) : ℚ⟦X⟧) = 0 := by
          rw [← map_natCast (C (R := ℚ)), derivative_C]
        rw [hc, smul_zero, add_zero, smul_eq_mul]
        calc (1 + X) * (G.subst U * (((q + 1 : ℕ) : ℚ⟦X⟧) * (1 + X) ^ q))
            = ((q + 1 : ℕ) : ℚ⟦X⟧) * ((1 + X) ^ (q + 1) * G.subst U) := by ring
          _ = ((q + 1 : ℕ) : ℚ⟦X⟧) := by rw [← h1U, hG, mul_one]
          _ = (1 + X) * (((q + 1 : ℕ) : ℚ⟦X⟧) * G) := by
            rw [mul_left_comm, one_add_X_mul_mk_neg_one_pow, mul_one]
    exact hd
  · have h0 : constantCoeff U = 0 := by simp [hU]
    have h1 : constantCoeff ((log ℚ).subst U) = 0 :=
      constantCoeff_subst_eq_zero h0 _ constantCoeff_log
    rw [h1]
    simp

theorem one_add_X_pow_sub_one_eq_coe (q : ℕ) :
    ((1 + X : ℚ⟦X⟧) ^ q - 1) =
      (((1 + Polynomial.X : Polynomial ℚ) ^ q - 1 : Polynomial ℚ) : ℚ⟦X⟧) := by
  simp

theorem sum_coeff_one_add_X_pow_sub_one_pow (q : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    ∑ n ∈ Finset.Icc 1 m, (-1 : ℚ) ^ (n - 1) / n *
      (((1 + Polynomial.X : Polynomial ℚ) ^ q - 1) ^ n).coeff m = (-1) ^ (m - 1) * q / m := by
  have h := congrArg (coeff m) (PowerSeries.log_subst_one_add_X_pow_sub_one q)
  rw [coeff_subst' (hasSubst_one_add_X_pow_sub_one q), one_add_X_pow_sub_one_eq_coe] at h
  simp only [← Polynomial.coe_pow, Polynomial.coeff_coe, smul_eq_mul] at h
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc 1 m) ?_] at h
  · have hr : coeff m ((q : ℚ⟦X⟧) * log ℚ) = q * ((-1) ^ (m - 1) / m) := by
      rw [show (q : ℚ⟦X⟧) = C (q : ℚ) from (map_natCast C q).symm, coeff_C_mul, coeff_log,
        if_neg (by omega), Algebra.algebraMap_self, RingHom.id_apply]
      congr 2
      rw [show m + 1 = (m - 1) + 2 by omega, pow_add]; simp
    rw [hr] at h
    rw [show (-1 : ℚ) ^ (m - 1) * q / m = q * ((-1) ^ (m - 1) / m) by ring, ← h]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : n ≠ 0 := by have := (Finset.mem_Icc.1 hn).1; omega
    rw [coeff_log, if_neg hn1, Algebra.algebraMap_self, RingHom.id_apply,
      show n + 1 = (n - 1) + 2 by omega, pow_add]
    simp
  · intro n hn
    rw [Function.mem_support] at hn
    rw [Finset.coe_Icc, Set.mem_Icc]
    by_contra hc
    rcases Nat.lt_or_ge n 1 with h1 | h1
    · obtain rfl : n = 0 := by omega
      simp at hn
    · have hlt : m < n := by omega
      rw [coeff_one_add_X_pow_sub_one_pow_of_lt q hlt, mul_zero] at hn
      exact hn rfl

theorem log_pow_coeff_int (q m : ℕ) (hm : 1 ≤ m) :
    ∑ n ∈ Finset.Icc 1 m, (-1 : ℤ) ^ (n - 1) *
      ((((1 : Polynomial ℤ) + Polynomial.X) ^ q - 1) ^ n).coeff m * ((m.factorial / n : ℕ) : ℤ) =
      (-1) ^ (m - 1) * q * (m - 1).factorial := by
  apply Int.cast_injective (α := ℚ)
  have hcoe : ∀ n : ℕ, (((((1 : Polynomial ℤ) + Polynomial.X) ^ q - 1) ^ n).coeff m : ℚ) =
      (((1 + Polynomial.X : Polynomial ℚ) ^ q - 1) ^ n).coeff m := fun n => by
    rw [← eq_intCast (Int.castRingHom ℚ), ← Polynomial.coeff_map]
    simp [Polynomial.map_pow]
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast, hcoe]
  have hdiv : ∀ n ∈ Finset.Icc 1 m, (((m.factorial / n : ℕ) : ℚ)) = m.factorial / n := fun n hn => by
    have h1 := (Finset.mem_Icc.1 hn)
    rw [Nat.cast_div (Nat.dvd_factorial (by omega) h1.2) (by exact_mod_cast (show n ≠ 0 by omega))]
  rw [Finset.sum_congr rfl fun n hn => by rw [hdiv n hn]]
  have hfac : (m.factorial : ℚ) = m * (m - 1).factorial := by
    rw [← Nat.cast_mul, ← Nat.mul_factorial_pred (by omega)]
  calc ∑ n ∈ Finset.Icc 1 m, (-1 : ℚ) ^ (n - 1) *
        ((((1 + Polynomial.X : Polynomial ℚ) ^ q - 1) ^ n).coeff m) * (m.factorial / n)
      = m.factorial * ∑ n ∈ Finset.Icc 1 m, (-1 : ℚ) ^ (n - 1) / n *
        (((1 + Polynomial.X : Polynomial ℚ) ^ q - 1) ^ n).coeff m := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => by ring
    _ = (-1) ^ (m - 1) * q * (m - 1).factorial := by
        rw [sum_coeff_one_add_X_pow_sub_one_pow q hm, hfac]
        field_simp

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open _root_.WittVector Polynomial

namespace ACris

section Coefficients

variable (q : ℕ)

def powCoeff (N m : ℕ) : ℤ := ((((1 : ℤ[X]) + X) ^ q - 1) ^ N).coeff m

theorem natDegree_one_add_X_pow_sub_one_pow_le (N : ℕ) :
    ((((1 : ℤ[X]) + X) ^ q - 1) ^ N).natDegree ≤ q * N := by
  refine (natDegree_pow_le).trans ?_
  rw [mul_comm q N]
  refine Nat.mul_le_mul_left N ?_
  refine (natDegree_sub_le _ _).trans (max_le ?_ (by simp))
  refine (natDegree_pow_le).trans ?_
  have : ((1 : ℤ[X]) + X).natDegree ≤ 1 := (natDegree_add_le _ _).trans (by simp)
  nlinarith

theorem powCoeff_of_lt {N m : ℕ} (h : m < N) : powCoeff q N m = 0 :=
  coeff_one_add_X_pow_sub_one_pow_of_lt q h

theorem powCoeff_of_gt {N m : ℕ} (h : q * N < m) : powCoeff q N m = 0 :=
  coeff_eq_zero_of_natDegree_lt ((natDegree_one_add_X_pow_sub_one_pow_le q N).trans_lt h)

theorem sum_powCoeff (j : ℕ) :
    ∑ n ∈ Finset.range (j + 1), (-1 : ℤ) ^ n * powCoeff q (n + 1) (j + 1) *
      (((j + 1).factorial / (n + 1) : ℕ) : ℤ) = (-1) ^ j * q * j.factorial := by
  have h := log_pow_coeff_int q (j + 1) (Nat.succ_pos j)
  have hI : Finset.Icc 1 (j + 1) = Finset.Ico 1 (j + 2) := by ext; simp; omega
  rw [hI, Finset.sum_Ico_eq_sum_range] at h
  simp only [Nat.add_sub_cancel, show j + 2 - 1 = j + 1 by omega] at h
  rw [← h]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [add_comm 1 n, Nat.add_sub_cancel, powCoeff]

theorem factorial_div_succ_eq {n j : ℕ} (h : n ≤ j) :
    (j + 1).factorial / (n + 1) = n.factorial * ((j + 1).factorial / (n + 1).factorial) := by
  obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial (Nat.succ_le_succ h)
  rw [hc, Nat.factorial_succ, mul_assoc, Nat.mul_div_cancel_left _ n.succ_pos,
    ← mul_assoc, Nat.mul_div_cancel_left _ (Nat.mul_pos n.succ_pos n.factorial_pos)]

end Coefficients

end ACris

namespace ACris

section Expansion

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)

variable (p) in

def logCoeff (n j : ℕ) : ℤ :=
  (-1) ^ n * powCoeff p (n + 1) (j + 1) * (((j + 1).factorial / (n + 1) : ℕ) : ℤ)

omit hp in
theorem logCoeff_of_lt {n j : ℕ} (h : j < n) : logCoeff p n j = 0 := by
  simp [logCoeff, powCoeff_of_lt p (show j + 1 < n + 1 by omega)]

omit hp in
theorem logCoeff_of_gt {n j : ℕ} (h : p * (n + 1) < j + 1) : logCoeff p n j = 0 := by
  simp [logCoeff, powCoeff_of_gt p h]

omit hp in
theorem factorial_dvd_logCoeff (n j : ℕ) : (n.factorial : ℤ) ∣ logCoeff p n j := by
  by_cases h : n ≤ j
  · rw [logCoeff, factorial_div_succ_eq h, Nat.cast_mul]
    exact Dvd.dvd.mul_left (Dvd.intro _ rfl) _
  · rw [logCoeff_of_lt (by omega)]
    exact dvd_zero _

omit hp in
theorem sum_logCoeff (j : ℕ) :
    ∑ n ∈ Finset.range (j + 1), logCoeff p n j = (-1) ^ j * p * j.factorial :=
  sum_powCoeff p j

theorem one_add_pow_sub_one_pow_eq_sum (x : AInf K p) (N L : ℕ) (hL : p * N ≤ L) :
    ((1 + x) ^ p - 1) ^ N =
      ∑ m ∈ Finset.range (L + 1), (powCoeff p N m : AInf K p) * x ^ m := by
  have hdeg : ((((1 : ℤ[X]) + X) ^ p - 1) ^ N).natDegree < L + 1 :=
    Nat.lt_succ_of_le ((natDegree_one_add_X_pow_sub_one_pow_le p N).trans hL)
  have h := aeval_eq_sum_range' (R := ℤ) hdeg x
  simp only [map_pow, map_sub, map_add, map_one, aeval_X] at h
  rw [h]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [zsmul_eq_mul, powCoeff]

theorem factorial_mul_dpow_eq_sum (x : AInf K p) (n L : ℕ) (hL : p * (n + 1) ≤ L) :
    (n.factorial : 𝔸) * dpow (n + 1) ((1 + x) ^ p - 1) =
      ∑ j ∈ Finset.range L, ((powCoeff p (n + 1) (j + 1) *
        (((j + 1).factorial / (n + 1) : ℕ) : ℤ) : ℤ) : 𝔸) * dpow (j + 1) x := by
  have h1 := isUnit_natCast (K := K) (p := p) (Nat.succ_ne_zero n)
  apply h1.mul_left_cancel
  rw [← mul_assoc, ← Nat.cast_mul, ← Nat.factorial_succ, factorial_mul_dpow, ← map_pow,
    one_add_pow_sub_one_pow_eq_sum x (n + 1) L hL, map_sum, Finset.sum_range_succ', Finset.mul_sum]
  simp only [map_mul, map_intCast, map_pow, pow_zero, mul_one, powCoeff_of_lt p n.succ_pos,
    Int.cast_zero, zero_mul, map_zero, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : n ≤ j
  · have hdvd : n + 1 ∣ (j + 1).factorial := Nat.dvd_factorial n.succ_pos (Nat.succ_le_succ h)
    rw [← factorial_mul_dpow (j + 1) x]
    obtain ⟨d, hd⟩ : ∃ d, (j + 1).factorial / (n + 1) = d := ⟨_, rfl⟩
    have hd' : (n + 1) * d = (j + 1).factorial := by rw [← hd, Nat.mul_div_cancel' hdvd]
    rw [hd, ← hd']
    push_cast
    ring
  · rw [powCoeff_of_lt p (show j + 1 < n + 1 by omega)]
    simp

variable {x : AInf K p}

theorem one_add_pow_sub_one_mem (hx : x ∈ RingHom.ker θ) : (1 + x) ^ p - 1 ∈ RingHom.ker θ := by
  rw [RingHom.mem_ker] at hx ⊢
  rw [map_sub, map_pow, map_add, map_one, hx, add_zero, one_pow, sub_self]

theorem logTermZero_one_add_pow (hx : x ∈ RingHom.ker θ) (n L : ℕ) (hL : p * (n + 1) ≤ L) :
    logTermZero (one_add_pow_sub_one_mem hx) n =
      ∑ j ∈ Finset.range L, (logCoeff p n j : ACrisZero K p) * dpowZero hx (j + 1) := by
  apply Subtype.ext
  simp only [logTermZero, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_neg,
    Subalgebra.coe_one, SubringClass.coe_natCast, coe_dpowZero, AddSubmonoidClass.coe_finsetSum,
    SubringClass.coe_intCast]
  rw [mul_assoc, factorial_mul_dpow_eq_sum x n L hL, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [logCoeff]
  push_cast
  ring

theorem p_mul_logTermZero (hx : x ∈ RingHom.ker θ) (j : ℕ) :
    (p : ACrisZero K p) * logTermZero hx j =
      ∑ n ∈ Finset.range (j + 1), (logCoeff p n j : ACrisZero K p) * dpowZero hx (j + 1) := by
  rw [← Finset.sum_mul, ← Int.cast_sum, sum_logCoeff, logTermZero]
  push_cast
  ring

end Expansion

end ACris

namespace ACris

section PhiT

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}
local notation "𝔭₀" => Ideal.span {(p : ACrisZero K p)}

variable {x : AInf K p}

theorem sum_p_mul_logTermZero_sub_mem (hx : x ∈ RingHom.ker θ) {k M : ℕ} (hM : p * (p * k + 1) ≤ M) :
    ∑ j ∈ Finset.range M, (p : ACrisZero K p) * logTermZero hx j -
      ∑ n ∈ Finset.range M, logTermZero (one_add_pow_sub_one_mem hx) n ∈ 𝔭₀ ^ k := by
  have hpM : M ≤ p * M := Nat.le_mul_of_pos_left M hp.out.pos
  rw [Finset.sum_congr rfl fun n hn => logTermZero_one_add_pow hx n (p * M)
      (Nat.mul_le_mul_left p (Finset.mem_range.1 hn)),
    Finset.sum_congr rfl fun j _ => p_mul_logTermZero hx j]
  have h1 : ∀ j ∈ Finset.range M,
      ∑ n ∈ Finset.range (j + 1), (logCoeff p n j : ACrisZero K p) * dpowZero hx (j + 1) =
        ∑ n ∈ Finset.range M, (logCoeff p n j : ACrisZero K p) * dpowZero hx (j + 1) := by
    intro j hj
    apply Finset.sum_subset (Finset.range_subset_range.2 (Finset.mem_range.1 hj))
    intro n _ hn
    rw [Finset.mem_range, not_lt] at hn
    rw [logCoeff_of_lt (by omega), Int.cast_zero, zero_mul]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm (s := Finset.range M) (t := Finset.range (p * M)),
    ← Finset.sum_range_add_sum_Ico _ hpM, sub_add_cancel_left]
  refine neg_mem (Ideal.sum_mem _ fun j hj => Ideal.sum_mem _ fun n _ => ?_)
  have hj := (Finset.mem_Ico.1 hj).1
  by_cases hc : p * (n + 1) < j + 1
  · rw [logCoeff_of_gt hc, Int.cast_zero, zero_mul]
    exact zero_mem _
  · have hn : p * k ≤ n := by
      by_contra hlt
      have : p * (n + 1) ≤ p * (p * k) := Nat.mul_le_mul_left p (by omega)
      nlinarith
    obtain ⟨z, hz⟩ := factorial_dvd_logCoeff (p := p) n j
    rw [hz, Int.cast_mul, Int.cast_natCast]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (natCast_mem_pow (pow_dvd_factorial hn)))

theorem log_one_add_pow (hx : x ∈ RingHom.ker θ) :
    log (one_add_pow_sub_one_mem hx) =
      algebraMap (ACrisZero K p) (ACris K p) (p : ACrisZero K p) * log hx := by
  have hs := (isAdicSum_log hx).mul_left (algebraMap (ACrisZero K p) (ACris K p) (p : ACrisZero K p))
  apply log_eq_of_isAdicSum
  intro k
  obtain ⟨N, hN⟩ := hs k
  refine ⟨max N (p * (p * k + 1)), fun M hM => ?_⟩
  have h1 := hN M (le_of_max_le_left hM)
  have h2 : ∑ n ∈ Finset.range M, algebraMap (ACrisZero K p) (ACris K p) (p : ACrisZero K p) *
      logTerm hx n - ∑ n ∈ Finset.range M, logTerm (one_add_pow_sub_one_mem hx) n ∈ 𝔭 ^ k := by
    have h := algebraMap_mem_pow (sum_p_mul_logTermZero_sub_mem hx (le_of_max_le_right hM))
    rw [map_sub, map_sum, map_sum] at h
    simpa only [map_mul, logTerm] using h
  have := add_mem h1 h2
  simp only at this
  rwa [sub_add_sub_cancel] at this

theorem log_congr {x y : AInf K p} (h : x = y) (hx : x ∈ RingHom.ker θ) (hy : y ∈ RingHom.ker θ) :
    log hx = log hy := by
  subst h; rfl

theorem span_p_le_comap_phi : 𝔭 ≤ Ideal.comap (phi K p) 𝔭 := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
  exact Ideal.mem_span_singleton_self _

theorem coe_logTermZero {y : AInf K p} (hy : y ∈ RingHom.ker θ) (n : ℕ) :
    (logTermZero hy n : 𝔸) = (-1) ^ n * (n.factorial : 𝔸) * dpow (n + 1) y := by
  simp only [logTermZero, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_neg,
    Subalgebra.coe_one, SubringClass.coe_natCast, coe_dpowZero]

theorem phiZero_logTermZero (hx : x ∈ RingHom.ker θ) (hφ : φ x ∈ RingHom.ker θ) (n : ℕ) :
    phiZero K p (logTermZero hx n) = logTermZero hφ n := by
  apply Subtype.ext
  rw [coe_phiZero, coe_logTermZero, coe_logTermZero, map_mul, map_mul, map_pow, map_neg, map_one,
    map_natCast, phiAway_dpow]

theorem phi_algebraMap_zero (y : ACrisZero K p) :
    phi K p (algebraMap (ACrisZero K p) (ACris K p) y) =
      algebraMap (ACrisZero K p) (ACris K p) (phiZero K p y) :=
  phi_of y

theorem phi_logTerm (hx : x ∈ RingHom.ker θ) (hφ : φ x ∈ RingHom.ker θ) (n : ℕ) :
    phi K p (logTerm hx n) = logTerm hφ n := by
  rw [logTerm, logTerm, phi_algebraMap_zero, phiZero_logTermZero hx hφ]

theorem phi_log (hx : x ∈ RingHom.ker θ) (hφ : φ x ∈ RingHom.ker θ) :
    phi K p (log hx) = log hφ :=
  (log_eq_of_isAdicSum (((isAdicSum_log hx).map (phi K p) span_p_le_comap_phi).congr
    (phi_logTerm hx hφ))).symm

theorem frobenius_mu (ε : 𝒪♭) : φ (AInf.mu (K := K) ε) = (1 + AInf.mu ε) ^ p - 1 := by
  rw [AInf.mu, map_sub, map_one, WittVector.frobeniusEquiv_teichmuller, map_pow, add_sub_cancel]

theorem phi_periodT {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) :
    phi K p (periodT hε) =
      algebraMap (ACrisZero K p) (ACris K p) (p : ACrisZero K p) * periodT hε := by
  have hφ : φ (AInf.mu (K := K) ε) ∈ RingHom.ker θ := by
    rw [frobenius_mu]; exact one_add_pow_sub_one_mem (mu_mem_ker hε)
  rw [periodT, phi_log _ hφ, log_congr (frobenius_mu ε) hφ (one_add_pow_sub_one_mem (mu_mem_ker hε)),
    log_one_add_pow]

theorem phi_periodT_eq_mul {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) :
    phi K p (periodT hε) = (p : ACris K p) * periodT hε := by
  rw [phi_periodT, map_natCast]

theorem periodT_pow_mem' {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) : periodT hε ^ (p - 1) ∈ 𝔭 := by
  by_cases hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) = 1
  · set ε' := (_root_.frobeniusEquiv 𝒪♭ p).symm ε
    have hε' : ε = ε' ^ p := by
      have h := (_root_.frobeniusEquiv 𝒪♭ p).apply_symm_apply ε
      rw [_root_.frobeniusEquiv_apply, frobenius_def] at h
      exact h.symm
    have hμ : AInf.mu (K := K) ε = φ (AInf.mu ε') := by
      rw [frobenius_mu, AInf.mu, AInf.mu, hε', map_pow, add_sub_cancel]
    have hφ : φ (AInf.mu (K := K) ε') ∈ RingHom.ker θ := hμ ▸ mu_mem_ker hε
    have ht : periodT hε = algebraMap (ACrisZero K p) (ACris K p) (p : ACrisZero K p) *
        periodT (ε := ε') hζ := by
      rw [periodT, log_congr hμ _ hφ, ← phi_log (mu_mem_ker hζ) hφ, ← periodT, phi_periodT]
    have hmem : periodT hε ∈ 𝔭 := by
      rw [ht]
      exact Ideal.mul_mem_right _ _ (by simpa using algebraMap_p_mem (K := K) (p := p))
    exact Ideal.pow_mem_of_mem _ hmem _ (Nat.sub_pos_of_lt hp.out.one_lt)
  · exact periodT_pow_mem hε hζ

end PhiT

end ACris

end GroundTheory.PAdicHodge
end
end
