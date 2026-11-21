import Mathlib
import GroundTheory.PAdicHodge.ACrisPhi
import GroundTheory.PAdicHodge.GalSmulAlgebraMapPadicPlus

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open _root_.WittVector

namespace ACris

section PD

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}
local notation "𝔭₀" => Ideal.span {(p : ACrisZero K p)}

theorem dpow_zero_right {n : ℕ} (hn : n ≠ 0) : dpow n (0 : AInf K p) = 0 := by
  rw [dpow, map_zero, zero_pow hn, mul_zero]

variable (K p) in

def pdIdeal : Ideal (AInf K p) where
  carrier := {x | ∀ n : ℕ, dpow n x ∈ ACrisZero K p}
  add_mem' {x y} hx hy n := by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [dpow_add]
    exact Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (hx k) (hy (n - k))
  zero_mem' n := by
    rcases n with _ | n
    · rw [dpow_zero]; exact Subalgebra.one_mem _
    · rw [dpow_zero_right n.succ_ne_zero]; exact Subalgebra.zero_mem _
  smul_mem' c x hx n := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [smul_eq_mul, mul_comm, dpow_mul]
    exact Subalgebra.mul_mem _ (hx n) (Subalgebra.pow_mem _ (Subalgebra.algebraMap_mem _ c) n)


theorem ker_le_pdIdeal : RingHom.ker θ ≤ pdIdeal K p := fun _ hx n => dpow_mem hx n

theorem natCast_p_mem_pdIdeal : (p : AInf K p) ∈ pdIdeal K p := fun n => by
  obtain ⟨w, hw⟩ := exists_dpow_p_mul (K := K) (p := p) n 1
  rw [mul_one] at hw
  rw [hw]
  exact Subalgebra.algebraMap_mem _ w

theorem mem_pdIdeal_of_theta_mem {z : AInf K p} (hz : θ z ∈ Ideal.span {(p : 𝒪)}) :
    z ∈ pdIdeal K p := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hz
  obtain ⟨b, hb⟩ := IsPerfectoidField.surjective_fontaineTheta (K := K) p c
  have hk : z - (p : AInf K p) * b ∈ RingHom.ker θ := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_natCast, hb, ← hc, mul_comm, sub_self]
  have h := add_mem (ker_le_pdIdeal hk) (Ideal.mul_mem_right b _ natCast_p_mem_pdIdeal)
  rwa [sub_add_cancel] at h

theorem one_add_pow_sub_one_mem_pdIdeal {z : AInf K p} (hz : z ∈ pdIdeal K p) :
    (1 + z) ^ p - 1 ∈ pdIdeal K p := by
  have h := geom_sum_mul (1 + z) p
  rw [add_sub_cancel_left] at h
  rw [← h]
  exact Ideal.mul_mem_left _ _ hz

def dpowJ {x : AInf K p} (hx : x ∈ pdIdeal K p) (n : ℕ) : ACrisZero K p :=
  ⟨dpow n x, hx n⟩

theorem coe_dpowJ {x : AInf K p} (hx : x ∈ pdIdeal K p) (n : ℕ) : (dpowJ hx n : 𝔸) = dpow n x :=
  rfl

def logTermJ {x : AInf K p} (hx : x ∈ pdIdeal K p) (n : ℕ) : ACrisZero K p :=
  (-1) ^ n * (n.factorial : ACrisZero K p) * dpowJ hx (n + 1)

theorem coe_logTermJ {x : AInf K p} (hx : x ∈ pdIdeal K p) (n : ℕ) :
    (logTermJ hx n : 𝔸) = (-1) ^ n * (n.factorial : 𝔸) * dpow (n + 1) x := by
  simp only [logTermJ, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_neg,
    Subalgebra.coe_one, SubringClass.coe_natCast, coe_dpowJ]

theorem logTermJ_mem {x : AInf K p} (hx : x ∈ pdIdeal K p) {k n : ℕ} (h : p * k ≤ n) :
    logTermJ hx n ∈ 𝔭₀ ^ k :=
  Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (natCast_mem_pow (pow_dvd_factorial h)))

def logTermJA {x : AInf K p} (hx : x ∈ pdIdeal K p) (n : ℕ) : ACris K p :=
  algebraMap (ACrisZero K p) (ACris K p) (logTermJ hx n)

theorem exists_isAdicSum_logTermJA {x : AInf K p} (hx : x ∈ pdIdeal K p) :
    ∃ s, IsAdicSum 𝔭 (logTermJA hx) s :=
  exists_isAdicSum fun k => ⟨p * k, fun _ hn => algebraMap_mem_pow (logTermJ_mem hx hn)⟩

def logJ {x : AInf K p} (hx : x ∈ pdIdeal K p) : ACris K p :=
  (exists_isAdicSum_logTermJA hx).choose

theorem isAdicSum_logJ {x : AInf K p} (hx : x ∈ pdIdeal K p) :
    IsAdicSum 𝔭 (logTermJA hx) (logJ hx) :=
  (exists_isAdicSum_logTermJA hx).choose_spec

theorem logJ_eq_of_isAdicSum {x : AInf K p} {hx : x ∈ pdIdeal K p} {s : ACris K p}
    (hs : IsAdicSum 𝔭 (logTermJA hx) s) : logJ hx = s :=
  (isAdicSum_logJ hx).unique hs

theorem logJ_congr {x y : AInf K p} (h : x = y) (hx : x ∈ pdIdeal K p) (hy : y ∈ pdIdeal K p) :
    logJ hx = logJ hy := by
  subst h; rfl

theorem logTermJ_one_add_pow {x : AInf K p} (hx : x ∈ pdIdeal K p) (n L : ℕ) (hL : p * (n + 1) ≤ L) :
    logTermJ (one_add_pow_sub_one_mem_pdIdeal hx) n =
      ∑ j ∈ Finset.range L, (logCoeff p n j : ACrisZero K p) * dpowJ hx (j + 1) := by
  apply Subtype.ext
  simp only [logTermJ, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_neg,
    Subalgebra.coe_one, SubringClass.coe_natCast, coe_dpowJ, AddSubmonoidClass.coe_finsetSum,
    SubringClass.coe_intCast]
  rw [mul_assoc, factorial_mul_dpow_eq_sum x n L hL, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [logCoeff]
  push_cast
  ring

theorem p_mul_logTermJ {x : AInf K p} (hx : x ∈ pdIdeal K p) (j : ℕ) :
    (p : ACrisZero K p) * logTermJ hx j =
      ∑ n ∈ Finset.range (j + 1), (logCoeff p n j : ACrisZero K p) * dpowJ hx (j + 1) := by
  rw [← Finset.sum_mul, ← Int.cast_sum, sum_logCoeff, logTermJ]
  push_cast
  ring

theorem sum_p_mul_logTermJ_sub_mem {x : AInf K p} (hx : x ∈ pdIdeal K p) {k M : ℕ}
    (hM : p * (p * k + 1) ≤ M) :
    ∑ j ∈ Finset.range M, (p : ACrisZero K p) * logTermJ hx j -
      ∑ n ∈ Finset.range M, logTermJ (one_add_pow_sub_one_mem_pdIdeal hx) n ∈ 𝔭₀ ^ k := by
  have hpM : M ≤ p * M := Nat.le_mul_of_pos_left M hp.out.pos
  rw [Finset.sum_congr rfl fun n hn => logTermJ_one_add_pow hx n (p * M)
      (Nat.mul_le_mul_left p (Finset.mem_range.1 hn)),
    Finset.sum_congr rfl fun j _ => p_mul_logTermJ hx j]
  have h1 : ∀ j ∈ Finset.range M,
      ∑ n ∈ Finset.range (j + 1), (logCoeff p n j : ACrisZero K p) * dpowJ hx (j + 1) =
        ∑ n ∈ Finset.range M, (logCoeff p n j : ACrisZero K p) * dpowJ hx (j + 1) := by
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

theorem logJ_one_add_pow {x : AInf K p} (hx : x ∈ pdIdeal K p) :
    logJ (one_add_pow_sub_one_mem_pdIdeal hx) = (p : ACris K p) * logJ hx := by
  have hs := (isAdicSum_logJ hx).mul_left (p : ACris K p)
  apply logJ_eq_of_isAdicSum
  intro k
  obtain ⟨N, hN⟩ := hs k
  refine ⟨max N (p * (p * k + 1)), fun M hM => ?_⟩
  have h1 := hN M (le_of_max_le_left hM)
  have h2 : ∑ n ∈ Finset.range M, (p : ACris K p) * logTermJA hx n -
      ∑ n ∈ Finset.range M, logTermJA (one_add_pow_sub_one_mem_pdIdeal hx) n ∈ 𝔭 ^ k := by
    have h := algebraMap_mem_pow (sum_p_mul_logTermJ_sub_mem hx (le_of_max_le_right hM))
    rw [map_sub, map_sum, map_sum] at h
    simpa only [map_mul, map_natCast, logTermJA] using h
  have := add_mem h1 h2
  simp only at this
  rwa [sub_add_sub_cancel] at this

theorem phiZero_logTermJ {x : AInf K p} (hx : x ∈ pdIdeal K p) (hφ : φ x ∈ pdIdeal K p) (n : ℕ) :
    phiZero K p (logTermJ hx n) = logTermJ hφ n := by
  apply Subtype.ext
  rw [coe_phiZero, coe_logTermJ, coe_logTermJ, map_mul, map_mul, map_pow, map_neg, map_one,
    map_natCast, phiAway_dpow]

theorem phi_logTermJA {x : AInf K p} (hx : x ∈ pdIdeal K p) (hφ : φ x ∈ pdIdeal K p) (n : ℕ) :
    phi K p (logTermJA hx n) = logTermJA hφ n := by
  rw [logTermJA, logTermJA, phi_algebraMap_zero, phiZero_logTermJ hx hφ]

theorem phi_logJ {x : AInf K p} (hx : x ∈ pdIdeal K p) (hφ : φ x ∈ pdIdeal K p) :
    phi K p (logJ hx) = logJ hφ :=
  (logJ_eq_of_isAdicSum (((isAdicSum_logJ hx).map (phi K p) span_p_le_comap_phi).congr
    (phi_logTermJA hx hφ))).symm

theorem mu_mem_pdIdeal {x : 𝒪♭} (hx : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)}) :
    AInf.mu (K := K) x ∈ pdIdeal K p :=
  mem_pdIdeal_of_theta_mem (by rwa [AInf.mu, map_sub, fontaineTheta_teichmuller, map_one])

def logTeich {x : 𝒪♭} (hx : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)}) : ACris K p :=
  logJ (mu_mem_pdIdeal hx)

theorem phi_logTeich {x : 𝒪♭} (hx : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)}) :
    phi K p (logTeich hx) = (p : ACris K p) * logTeich hx := by
  have h1 := one_add_pow_sub_one_mem_pdIdeal (mu_mem_pdIdeal hx)
  have hφ : φ (AInf.mu (K := K) x) ∈ pdIdeal K p := by rw [frobenius_mu]; exact h1
  rw [logTeich, phi_logJ _ hφ, logJ_congr (frobenius_mu x) hφ h1, logJ_one_add_pow]

end PD

section Theta

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]

local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}

theorem thetaZero_logTermJ_zero {x : AInf K p} (hx : x ∈ pdIdeal K p) :
    thetaZero K p (logTermJ hx 0) = θ x := by
  apply Subtype.ext
  rw [coe_thetaZero, coe_logTermJ, pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, one_mul,
    zero_add, dpow_one, thetaAway_algebraMap]

theorem thetaZero_logTermJ_mem {x : AInf K p} (hx : x ∈ pdIdeal K p) {c : 𝒪}
    (hc : θ x = (p : 𝒪) ^ 2 * c) (m : ℕ) :
    thetaZero K p (logTermJ hx (m + 1)) ∈ Ideal.span {(p : 𝒪) ^ 3} := by
  obtain ⟨w, hw⟩ := exists_natCast_mul_eq_pow (K := K) (p := p) (n := m + 2) (k := 2 * m + 1)
    (by omega) (by have := Nat.factorization_lt p (show m + 2 ≠ 0 by omega); omega)
  rw [Ideal.mem_span_singleton']
  refine ⟨(-1) ^ (m + 1) * (θ w * c ^ (m + 2)), Subtype.ext ?_⟩
  have hn1 : ((m + 2 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hf : (m + 2).factorial = (m + 2) * (m + 1).factorial := Nat.factorial_succ (m + 1)
  have e : ((m + 2 : ℕ) : 𝔸) * (((m + 1).factorial : 𝔸) * dpow (m + 2) x) =
      algebraMap (AInf K p) 𝔸 x ^ (m + 2) := by
    rw [← mul_assoc, ← Nat.cast_mul, ← hf, factorial_mul_dpow]
  have e2 := congrArg (thetaAway K p) e
  rw [map_mul, map_natCast, map_pow, thetaAway_algebraMap] at e2
  have hw2 : ((m + 2 : ℕ) : K) * (θ w : K) = (p : K) ^ (2 * m + 1) := by
    have := congrArg (fun a => ((θ a : 𝒪) : K)) hw
    simpa only [map_mul, map_natCast, map_pow, MulMemClass.coe_mul, SubringClass.coe_natCast,
      SubmonoidClass.coe_pow] using this
  have hc2 : (θ x : K) = (p : K) ^ 2 * (c : K) := by
    have := congrArg (fun a : 𝒪 => (a : K)) hc
    simpa only [MulMemClass.coe_mul, SubringClass.coe_natCast, SubmonoidClass.coe_pow] using this
  rw [hc2] at e2
  have e3 : thetaAway K p ((-1) ^ (m + 1) * ((m + 1).factorial : 𝔸) * dpow (m + 1 + 1) x) =
      (-1 : K) ^ (m + 1) * thetaAway K p (((m + 1).factorial : 𝔸) * dpow (m + 2) x) := by
    rw [mul_assoc, map_mul, map_pow, map_neg, map_one]
  rw [coe_thetaZero, coe_logTermJ, e3]
  apply mul_left_cancel₀ hn1
  push_cast at hw2 e2 ⊢
  linear_combination ((-1 : K) ^ (m + 1) * (c : K) ^ (m + 2) * (p : K) ^ 3) * hw2 -
    (-1 : K) ^ (m + 1) * e2

theorem theta_logJ_sub_mem {x : AInf K p} (hx : x ∈ pdIdeal K p) {c : 𝒪}
    (hc : θ x = (p : 𝒪) ^ 2 * c) : theta K p (logJ hx) - θ x ∈ Ideal.span {(p : 𝒪) ^ 3} := by
  have hle : 𝔭 ≤ (Ideal.span {(p : 𝒪)}).comap (theta K p) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨N, hN⟩ := (isAdicSum_logJ hx).map (theta K p) hle 3
  have h := hN (N + 1) (Nat.le_succ N)
  have ht : ∀ n, theta K p (logTermJA hx n) = thetaZero K p (logTermJ hx n) := fun n => by
    rw [logTermJA, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      theta_of]
  simp only [ht] at h
  rw [Finset.sum_range_succ', thetaZero_logTermJ_zero, Ideal.span_singleton_pow] at h
  have hs : ∑ n ∈ Finset.range N, thetaZero K p (logTermJ hx (n + 1)) ∈
      Ideal.span {(p : 𝒪) ^ 3} :=
    Ideal.sum_mem _ fun n _ => thetaZero_logTermJ_mem hx hc n
  have := add_mem h hs
  convert this using 1
  ring

theorem theta_logTeich_sub_mem {x : 𝒪♭} (hx : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)})
    {c : 𝒪} (hc : PreTilt.untilt x - 1 = (p : 𝒪) ^ 2 * c) :
    theta K p (logTeich hx) - (p : 𝒪) ^ 2 * c ∈ Ideal.span {(p : 𝒪) ^ 3} := by
  have hθ : θ (AInf.mu (K := K) x) = PreTilt.untilt x - 1 := by
    rw [AInf.mu, map_sub, fontaineTheta_teichmuller, map_one]
  have h := theta_logJ_sub_mem (mu_mem_pdIdeal hx) (c := c) (by rw [hθ, hc])
  rwa [hθ, hc] at h

end Theta

end ACris

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open _root_.WittVector

namespace ACris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝒪" => normInteger ℂ_[p]
local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔭" => Ideal.span {(p : ACris ℂ_[p] p)}
local notation "θdR" => IsPerfectoidField.thetaBDeRhamPlusField (K := ℂ_[p]) p

theorem exists_untilt_eq_of_cp (π : 𝒪) : ∃ x : 𝒪♭, PreTilt.untilt x = π := by
  have hp0 : 0 < p := hp.out.pos
  let root : 𝒪 → 𝒪 := fun z =>
    ⟨Classical.choose (IsAlgClosed.exists_pow_nat_eq (z : ℂ_[p]) hp0), mem_normInteger.2 (by
      have h := Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (z : ℂ_[p]) hp0)
      have h2 : ‖Classical.choose (IsAlgClosed.exists_pow_nat_eq (z : ℂ_[p]) hp0)‖ ^ p ≤ 1 := by
        rw [← norm_pow, h]; exact mem_normInteger.1 z.2
      exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hp0.ne').1 h2)⟩
  have hroot : ∀ z, root z ^ p = z := fun z => Subtype.ext (by
    simp only [root, SubmonoidClass.coe_pow]
    exact Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (z : ℂ_[p]) hp0))
  let y : ℕ → 𝒪 := fun n => root^[n] π
  have hy : ∀ n, y (n + 1) ^ p = y n := fun n => by
    simp only [y, Function.iterate_succ_apply', hroot]
  exact ⟨IsPerfectoidField.ofCompatible p y hy, by rw [IsPerfectoidField.untilt_ofCompatible]; rfl⟩

theorem exists_phi_eq_p_mul_theta_sub_mem (c : 𝒪) :
    ∃ u : ACris ℂ_[p] p, phi ℂ_[p] p u = (p : ACris ℂ_[p] p) * u ∧
      theta ℂ_[p] p u - (p : 𝒪) ^ 2 * c ∈ Ideal.span {(p : 𝒪) ^ 3} := by
  obtain ⟨x, hx⟩ := exists_untilt_eq_of_cp (1 + (p : 𝒪) ^ 2 * c)
  have h1 : PreTilt.untilt x - 1 = (p : 𝒪) ^ 2 * c := by rw [hx]; ring
  have hmem : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)} := by
    rw [h1, Ideal.mem_span_singleton']
    exact ⟨p * c, by ring⟩
  exact ⟨logTeich hmem, phi_logTeich hmem, theta_logTeich_sub_mem hmem h1⟩

theorem exists_phi_eq_p_mul_theta_eq (c : 𝒪) :
    ∃ u : ACris ℂ_[p] p, phi ℂ_[p] p u = (p : ACris ℂ_[p] p) * u ∧
      theta ℂ_[p] p u = (p : 𝒪) ^ 2 * c := by
  choose g hgφ hgθ using exists_phi_eq_p_mul_theta_sub_mem (p := p)
  have he : ∀ c, ∃ e : 𝒪, theta ℂ_[p] p (g c) = (p : 𝒪) ^ 2 * c - (p : 𝒪) ^ 3 * e := fun c => by
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (hgθ c)
    exact ⟨-e, by linear_combination -he⟩
  choose e he using he
  set cs : ℕ → 𝒪 := fun j => e^[j] c with hcs
  have hcs1 : ∀ j, e (cs j) = cs (j + 1) := fun j => by
    simp only [hcs, Function.iterate_succ_apply']
  set a : ℕ → ACris ℂ_[p] p := fun j => (p : ACris ℂ_[p] p) ^ j * g (cs j) with ha_def
  have ha : ∀ k, ∃ N, ∀ n, N ≤ n → a n ∈ 𝔭 ^ k := fun k => ⟨k, fun n hn => by
    rw [Ideal.span_singleton_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton.2 (pow_dvd_pow _ hn))⟩
  obtain ⟨s, hs⟩ := exists_isAdicSum ha
  refine ⟨s, ?_, ?_⟩
  · have h1 := (hs.map (phi ℂ_[p] p) span_p_le_comap_phi).congr
      (b := fun n => (p : ACris ℂ_[p] p) * a n) (fun n => by
        simp only [ha_def]
        rw [map_mul, map_pow, map_natCast, hgφ]
        ring)
    exact h1.unique (hs.mul_left _)
  · have hle : 𝔭 ≤ (Ideal.span {(p : 𝒪)}).comap (theta ℂ_[p] p) := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
      exact Ideal.mem_span_singleton_self _
    have h1 := hs.map (theta ℂ_[p] p) hle
    have htel : ∀ M, ∑ j ∈ Finset.range M, theta ℂ_[p] p (a j) =
        (p : 𝒪) ^ 2 * c - (p : 𝒪) ^ (M + 2) * cs M := by
      intro M
      induction M with
      | zero => simp [hcs]
      | succ M ih =>
        rw [Finset.sum_range_succ, ih]
        simp only [ha_def]
        rw [map_mul, map_pow, map_natCast, he, hcs1]
        ring
    have h2 : IsAdicSum (Ideal.span {(p : 𝒪)}) (fun n => theta ℂ_[p] p (a n))
        ((p : 𝒪) ^ 2 * c) := fun k => ⟨k, fun M hM => by
      rw [htel, sub_sub_cancel, Ideal.span_singleton_pow]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton.2 (pow_dvd_pow _ (by omega)))⟩
    exact h1.unique h2

section Plus

set_option maxHeartbeats 1600000 in

theorem phiPlus_eq_of_mul_eq {y : (BCrisPlus ℂ_[p] p)} {a : ACris ℂ_[p] p} {k m : ℕ}
    (hy : y * (p : (BCrisPlus ℂ_[p] p)) ^ k = algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) a)
    (ha : phi ℂ_[p] p a = (p : ACris ℂ_[p] p) ^ m * a) :
    phiPlus ℂ_[p] p y = (p : (BCrisPlus ℂ_[p] p)) ^ m * y := by
  have h := congrArg (phiPlus ℂ_[p] p) hy
  rw [map_mul, map_pow, map_natCast, phiPlus_algebraMap, ha, map_mul, map_pow, map_natCast,
    ← hy] at h
  exact (isUnit_p_bCrisPlus.pow k).mul_right_cancel (by rw [h]; ring)

set_option maxHeartbeats 1600000 in

theorem exists_phiPlus_eq_theta_eq (c : ℂ_[p]) :
    ∃ y : (BCrisPlus ℂ_[p] p), phiPlus ℂ_[p] p y = (p : (BCrisPlus ℂ_[p] p)) * y ∧ θdR (iotaPlus ℂ_[p] p y) = c := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖(p : ℂ_[p]) ^ N * c‖ ≤ 1 := by
    rcases eq_or_ne c 0 with rfl | hc
    · exact ⟨0, by simp⟩
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (norm_pos_iff.2 hc))
      (norm_natCast_p_lt_one (p := p))
    refine ⟨N, ?_⟩
    rw [norm_mul, norm_pow]
    calc ‖(p : ℂ_[p])‖ ^ N * ‖c‖ ≤ ‖c‖⁻¹ * ‖c‖ := by gcongr
      _ = 1 := inv_mul_cancel₀ (norm_ne_zero_iff.2 hc)
  set c' : 𝒪 := ⟨(p : ℂ_[p]) ^ N * c, mem_normInteger.2 hN⟩ with hc'
  have hc'' : (c' : ℂ_[p]) = (p : ℂ_[p]) ^ N * c := rfl
  obtain ⟨u, hφ, hθ⟩ := exists_phi_eq_p_mul_theta_eq c'
  obtain ⟨y, hy⟩ : ∃ y : (BCrisPlus ℂ_[p] p), y * (p : (BCrisPlus ℂ_[p] p)) ^ (N + 2) = algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) u :=
    ⟨algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) u * Ring.inverse (p : (BCrisPlus ℂ_[p] p)) ^ (N + 2), by
      rw [mul_assoc, ← mul_pow, Ring.inverse_mul_cancel _ isUnit_p_bCrisPlus, one_pow, mul_one]⟩
  refine ⟨y, by simpa using phiPlus_eq_of_mul_eq hy (m := 1) (by rw [hφ, pow_one]), ?_⟩
  have h := congrArg (fun z => θdR (iotaPlus ℂ_[p] p z)) hy
  simp only [map_mul, map_pow, map_natCast, thetaField_iotaPlus_algebraMap, hθ] at h
  have hp0 : (p : ℂ_[p]) ^ (N + 2) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  apply mul_right_cancel₀ hp0
  rw [h]
  push_cast
  rw [hc'']
  ring

set_option maxHeartbeats 1600000 in

theorem exists_phiPlus_eq_pow_theta_eq {m : ℕ} (hm : 1 ≤ m) (c : ℂ_[p]) :
    ∃ y : (BCrisPlus ℂ_[p] p), phiPlus ℂ_[p] p y = (p : (BCrisPlus ℂ_[p] p)) ^ m * y ∧ θdR (iotaPlus ℂ_[p] p y) = c := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨y1, h1, h1'⟩ := exists_phiPlus_eq_theta_eq c
  obtain ⟨y0, h0, h0'⟩ := exists_phiPlus_eq_theta_eq (p := p) 1
  refine ⟨y1 * y0 ^ k, ?_, ?_⟩
  · rw [map_mul, map_pow, h1, h0]
    ring
  · rw [map_mul, map_mul, map_pow, map_pow, h1', h0', one_pow, mul_one]

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

abbrev periodTPlus : (BCrisPlus ℂ_[p] p) := algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (periodT hε)

set_option maxHeartbeats 1600000 in
theorem phiPlus_periodTPlus : phiPlus ℂ_[p] p (periodTPlus hε) = (p : (BCrisPlus ℂ_[p] p)) * periodTPlus hε := by
  rw [periodTPlus, phiPlus_algebraMap, phi_periodT_eq_mul, map_mul, map_natCast]

set_option maxHeartbeats 1600000 in
theorem iotaPlus_periodTPlus : iotaPlus ℂ_[p] p (periodTPlus hε) = fontaineT ε hε := by
  rw [periodTPlus, iotaPlus_algebraMap, iota_periodT]

include hζ in

theorem mem_span_fontaineT_of_theta_eq_zero {r : 𝔹} (hr : θdR r = 0) :
    r ∈ Ideal.span {fontaineT ε hε} := by
  rw [← maximalIdeal_eq_span_fontaineT hε hζ, IsPerfectoidField.maximalIdeal_bDeRhamPlus]
  exact hr

set_option maxHeartbeats 1600000 in
include hζ in

theorem exists_phiPlus_eq_pow_iotaPlus_sub_mem {m n : ℕ} (hnm : n ≤ m) (w : 𝔹) :
    ∃ y : (BCrisPlus ℂ_[p] p), phiPlus ℂ_[p] p y = (p : (BCrisPlus ℂ_[p] p)) ^ m * y ∧
      iotaPlus ℂ_[p] p y - w ∈ Ideal.span {fontaineT ε hε ^ n} := by
  induction n with
  | zero =>
    refine ⟨0, by simp, ?_⟩
    rw [pow_zero, Ideal.span_singleton_one]
    exact Submodule.mem_top
  | succ n ih =>
    obtain ⟨y, hy, hyw⟩ := ih (by omega)
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hyw
    obtain ⟨z, hz, hz'⟩ := exists_phiPlus_eq_pow_theta_eq (p := p) (m := m - n) (by omega) (-θdR d)
    refine ⟨y + periodTPlus hε ^ n * z, ?_, ?_⟩
    · have hpm : (p : (BCrisPlus ℂ_[p] p)) ^ m = (p : (BCrisPlus ℂ_[p] p)) ^ n * (p : (BCrisPlus ℂ_[p] p)) ^ (m - n) := by
        rw [← pow_add, Nat.add_sub_cancel' (by omega)]
      rw [map_add, map_mul, map_pow, hy, hz, phiPlus_periodTPlus, mul_pow, hpm]
      ring
    · have h0 : θdR (d + iotaPlus ℂ_[p] p z) = 0 := by rw [map_add, hz', add_neg_cancel]
      obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (mem_span_fontaineT_of_theta_eq_zero hε hζ h0)
      rw [Ideal.mem_span_singleton']
      refine ⟨e, ?_⟩
      rw [map_add, map_mul, map_pow, iotaPlus_periodTPlus, add_sub_right_comm, ← hd, pow_succ]
      linear_combination (fontaineT ε hε ^ n) * he

end Plus

end ACris

end GroundTheory.PAdicHodge
end
end
