import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinIntegralityComputation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmulMemMMOfEqLphiUAdd
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSmulPhiMemMM
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

section
section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries Matrix

theorem PhiMod.mem_MM_of_series (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι) :
    ∀ (w : Vec K a ι) (t : ℕ → Vec K a ι), (∀ n, ∃ v ∈ P.MM, t n = (l : K) ^ n • v) →
      (∀ m, w - ∑ n ∈ Finset.range m, t n ∈ uPow K a ι m) → w ∈ P.MM := by
  intro w t ht hw
  choose v hv htv using ht
  have h2 (k : ℕ) : ∃ s ∈ P.MM, ∀ m, ∃ g ∈ P.MM,
      w - (s + (l : K) ^ k • g) ∈ uPow K a ι m := by
    refine ⟨∑ n ∈ Finset.range k, t n,
      sum_mem fun n _ => (htv n) ▸ P.l_pow_smul_mem_MM n (hv n), fun m => ?_⟩
    refine ⟨∑ n ∈ Finset.range m, (l : K) ^ n • v (k + n),
      sum_mem fun n _ => P.l_pow_smul_mem_MM n (hv _), uPow_anti (Nat.le_add_left m k) ?_⟩
    have := hw (k + m)
    rw [Finset.sum_range_add] at this
    simpa only [Finset.smul_sum, smul_smul, ← pow_add, ← htv] using this
  refine mem_tot.2 fun τ => P.mem_extc_iff.2 fun i => mem_S_of_approx (l := l) fun k => ?_
  obtain ⟨s, hs, H⟩ := h2 k
  refine ⟨_, P.mem_extc_iff.1 (mem_tot.1 hs τ) i, fun m => ?_⟩
  obtain ⟨g, hg, H'⟩ := H m
  refine ⟨_, P.mem_extc_iff.1 (mem_tot.1 hg τ) i, ?_⟩
  have := dvd_mulVec (P.mxInv τ) (H' τ) i
  simpa only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Matrix.mulVec_sub, Matrix.mulVec_add,
    Matrix.mulVec_smul] using this

end GlobalTheory.BK
end
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_phiModuleLattice_of_adic_series_prime_pow_terms : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι), ∀ (w : Vec K a ι) (t : ℕ → Vec K a ι), (∀ n, ∃ v ∈ P.MM, t n = (l : K) ^ n • v) → (∀ m, w - ∑ n ∈ Finset.range m, t n ∈ uPow K a ι m) → w ∈ P.MM := by
  atlas_forward_decl GlobalTheory.BK.PhiMod.mem_MM_of_series
end

section
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.BK

theorem lphi_pow_conn_X_pow_smul_mem : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ (y₀ : Vec K a ι), 1 ≤ η → E K l e ^ η • y₀ ∈ D.M → ∀ n : ℕ, ∃ w ∈ D.MM, (l : K) ^ (H + 2 * η + n * (η - 1)) • (D.lphi ^ (n + 1)) (D.conn ((X : K⟦X⟧) ^ e • y₀)) = (X : K⟦X⟧) ^ (e * l ^ (n + 1)) • w := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D y₀ hη hy n
  have key (w : Vec K a ι) (hw : w ∈ D.MM) : (l : K) ^ η • D.phi w ∈ D.MM :=
    PhiMod.pow_smul_phi_mem_MM O K l e a ι D.toPhiMod η D.upper w hw
  induction n with
  | zero =>
    have hE : E K l e ∈ S O K e := E_mem l e _
    have hNE : N K (E K l e) ∈ S O K e := by
      rw [N_apply]; exact mul_mem HasU.X_mem (derivative_mem_S hE)

    have h0 : (l : K) ^ η • D.phi y₀ ∈ D.MM :=
      D.l_pow_smul_phi_mem_MM (D.Mext_mono (A_le_S l e) hy)
    have hA : (l : K) ^ (H + 2 * η + 1) • D.phi y₀ ∈ D.MM := by
      have := D.l_pow_smul_mem_MM (H + η + 1) h0
      rwa [smul_smul, ← pow_add, show H + η + 1 + η = H + 2 * η + 1 by ring] at this

    have hk : E K l e ^ (H + η) • y₀ ∈ D.MM := by
      rw [pow_add, mul_smul]
      exact D.ext_mono (A_le_S l e) (D.lower _ hy)
    have h1 : E K l e ^ (H + η + 1) • D.conn y₀ ∈ D.MM := by
      have h2 := sub_mem (D.smul_mem_MM hE (D.conn_mem_MM hk))
        (D.smul_mem_MM (mul_mem (natCast_mem _ (H + η)) hNE) hk)
      convert h2 using 1
      rw [PhiMod.conn_smul, N_apply, derivative_pow]
      generalize H + η = k
      ext τ i : 2
      simp only [smul_eq_mul, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, N_apply]
      cases k with
      | zero => simp
      | succ k => simp only [Nat.add_sub_cancel]; ring
    have h3 := D.smul_mem_Mext (A_le_S l e) h1
    rw [smul_smul, ← pow_add] at h3
    have hB := D.l_pow_smul_phi_mem_MM h3
    rw [show η + (H + η + 1) = H + 2 * η + 1 by ring] at hB
    refine ⟨(e : K⟦X⟧) • ((l : K) ^ (H + 2 * η + 1) • D.phi y₀) +
      (l : K) ^ (H + 2 * η + 1) • D.phi (D.conn y₀),
      add_mem (D.smul_mem_MM (natCast_mem _ e) hA) hB, ?_⟩
    have hc : D.conn ((X : K⟦X⟧) ^ e • y₀) = (X : K⟦X⟧) ^ e • ((e : K⟦X⟧) • y₀ + D.conn y₀) := by
      rw [PhiMod.conn_smul, smul_add, smul_smul]
      congr 2
      ext n
      rw [coeff_N, ← map_natCast (C : K →+* K⟦X⟧), coeff_mul_C, coeff_X_pow]
      split_ifs with h <;> simp [h]
    rw [zero_mul, add_zero, zero_add, pow_one, pow_one, hc, PhiMod.lphi_apply, PhiMod.phi_smul, map_add,
      PhiMod.phi_smul, map_pow, frob_X, ← pow_mul, map_natCast, mul_comm l e]
    simp only [smul_add, smul_smul, pow_succ]
    congr 1 <;> exact smul_comm _ _ _
  | succ n ih =>
    obtain ⟨w, hw, h⟩ := ih
    refine ⟨_, key w hw, ?_⟩
    rw [show H + 2 * η + (n + 1) * (η - 1) = (η - 1) + (H + 2 * η + n * (η - 1)) by ring, pow_add,
      mul_smul, pow_succ', Module.End.mul_apply, ← map_smul, h, PhiMod.lphi_apply, PhiMod.phi_smul,
      map_pow, frob_X, ← pow_mul, smul_smul, ← pow_succ, Nat.sub_add_cancel hη, smul_comm]
    congr 2
    ring

end GlobalTheory.BK
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_pow_smul_connection_series_term_mem_lattice : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ (y₀ : Vec K a ι), 1 ≤ η → E K l e ^ η • y₀ ∈ D.M → ∀ n : ℕ, ∃ w ∈ D.MM, (l : K) ^ (H + 2 * η + n * (η - 1)) • (D.lphi ^ (n + 1)) (D.conn ((X : K⟦X⟧) ^ e • y₀)) = (X : K⟦X⟧) ^ (e * l ^ (n + 1)) • w := by
  atlas_forward_decl GlobalTheory.BK.lphi_pow_conn_X_pow_smul_mem
end

section
section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries

theorem PhiMod.exists_X_pow_smul_eq_l_pow_smul (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι)
    (n : ℕ) : ∀ w ∈ P.MM, ∃ w' ∈ P.MM,
      (X : K⟦X⟧) ^ (e * l ^ (n + 1)) • w = (l : K) ^ (l ^ n) • w' := by
  intro w hw
  have hl0 := l_ne_zero (K := K) l
  have hlp := (Fact.out : l.Prime).pos
  have hm : monomial (e * l ^ (n + 1)) (((l : K) ^ (l ^ n))⁻¹) ∈ S O K e := by
    refine monomial_mem_S ?_
    rw [norm_inv, norm_pow, inv_mul_le_one₀ (pow_pos (norm_pos_iff.2 hl0) _), wS,
      Nat.mul_div_cancel_left _ (NeZero.pos e)]
    refine (norm_factorial_le l _).trans (le_of_eq ?_)
    rw [pow_succ, Nat.mul_div_cancel _ hlp]
  refine ⟨_, P.MM.smul_mem ⟨_, hm⟩ hw, ?_⟩
  change _ = (l : K) ^ (l ^ n) • ((monomial (e * l ^ (n + 1)) (((l : K) ^ (l ^ n))⁻¹)) • w)
  rw [← smul_assoc, monomial_eq_C_mul_X_pow, smul_eq_C_mul, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (pow_ne_zero _ hl0), map_one, one_mul]
end GlobalTheory.BK
end
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_X_pow_smul_eq_prime_pow_smul_phiModule : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι), ∀ (n : ℕ), ∀ w ∈ P.MM, ∃ w' ∈ P.MM, (X : K⟦X⟧) ^ (e * l ^ (n + 1)) • w = (l : K) ^ (l ^ n) • w' := by
  atlas_forward_decl GlobalTheory.BK.PhiMod.exists_X_pow_smul_eq_l_pow_smul
end

section
section
noncomputable section

namespace GlobalTheory

open PowerSeries GlobalTheory.BK

theorem nat_mul_add_le_pow {l : ℕ} (hl : 2 ≤ l) (n : ℕ) : n * l + l ≤ l ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have h1 := Nat.mul_le_mul_right l ih
    have h2 := Nat.mul_le_mul_left (n * l + l) hl
    nlinarith

theorem zeta_add_lphi_conn_mem : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ (y₀ : Vec K a ι), 1 ≤ η → η < H → 14 * H < l → E K l e ^ η • y₀ ∈ D.M → ∃ r ∈ D.MM, D.zeta ((X : K⟦X⟧) ^ e • y₀) + D.lphi (D.conn ((X : K⟦X⟧) ^ e • y₀)) = (l : K) ^ (l - 14 * H) • r := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D y₀ hη hηH hHl hy₀
  set y : Vec K a ι := (X : K⟦X⟧) ^ e • y₀ with hy
  set A := l - 14 * H with hA
  have hl0 : (l : K) ≠ 0 := l_ne_zero (K := K) l
  have hlA : (l : K) ^ A ≠ 0 := pow_ne_zero _ hl0
  set c : K := ((l : K) ^ A)⁻¹ with hc
  set w : Vec K a ι := c • (D.zeta y + D.lphi (D.conn y)) with hw
  let t : ℕ → Vec K a ι := fun n => -(c • (D.lphi ^ (n + 2)) (D.conn y))
  have hterm : ∀ n, ∃ v ∈ D.MM, t n = (l : K) ^ n • v := by
    intro n
    obtain ⟨w₁, hw₁, h₁⟩ := GlobalTheory.T.prime_pow_smul_connection_series_term_mem_lattice O K l e a ι η H D y₀ hη hy₀ (n + 1)
    obtain ⟨w', hw', h₂⟩ := GlobalTheory.T.exists_X_pow_smul_eq_prime_pow_smul_phiModule O K l e a ι D.toPhiMod (n + 1) w₁ hw₁
    set B := H + 2 * η + (n + 1) * (η - 1) with hB
    have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
    have hineq : B + A + n ≤ l ^ (n + 1) := by
      have h1 := nat_mul_add_le_pow hl2 n
      have h2 : (n + 1) * (η - 1) ≤ (n + 1) * H := Nat.mul_le_mul_left _ (by omega)
      have h3 : n * (H + 1) ≤ n * l := Nat.mul_le_mul_left _ (by omega)
      have h4 : (n + 1) * H = n * H + H := by ring
      have h5 : n * (H + 1) = n * H + n := by ring
      omega
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hineq
    rw [h₂, hd, show B + A + n + d = B + (A + (n + d)) by ring, pow_add (l : K) B, mul_smul] at h₁
    have h₃ := congrArg (fun v => ((l : K) ^ B)⁻¹ • v) h₁
    simp only [inv_smul_smul₀ (pow_ne_zero B hl0)] at h₃
    refine ⟨-((l : K) ^ d • w'), neg_mem (PhiMod.l_pow_smul_mem_MM _ d hw'), ?_⟩
    change -(c • (D.lphi ^ (n + 1 + 1)) (D.conn y)) = _
    rw [h₃, pow_add, mul_smul, hc, inv_smul_smul₀ hlA, pow_add, mul_smul, smul_neg]
  have hpart : ∀ m, w - ∑ n ∈ Finset.range m, t n ∈ uPow K a ι m := by
    intro m
    have key := D.zeta_add_sum_mem y (m + 1)
    rw [Finset.sum_range_succ'] at key
    have heq : w - ∑ n ∈ Finset.range m, t n = c • (D.zeta y + (∑ n ∈ Finset.range m,
        (D.lphi ^ (n + 1 + 1)) (D.conn y) + (D.lphi ^ (0 + 1)) (D.conn y))) := by
      simp only [t, hw, Finset.sum_neg_distrib, sub_neg_eq_add, zero_add, pow_one, smul_add,
        Finset.smul_sum]
      abel
    rw [heq]
    exact Submodule.smul_of_tower_mem _ c (uPow_anti (by omega) key)
  refine ⟨w, GlobalTheory.T.mem_phiModuleLattice_of_adic_series_prime_pow_terms O K l e a ι D.toPhiMod w t hterm hpart, ?_⟩
  rw [hw, hc, smul_inv_smul₀ hlA]

end GlobalTheory
end
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeta_series_higher_terms_mem_lPow_breuilKisin : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ (y₀ : Vec K a ι), 1 ≤ η → η < H → 14 * H < l → E K l e ^ η • y₀ ∈ D.M → ∃ r ∈ D.MM, D.zeta ((X : K⟦X⟧) ^ e • y₀) + D.lphi (D.conn ((X : K⟦X⟧) ^ e • y₀)) = (l : K) ^ (l - 14 * H) • r := by
  atlas_forward_decl GlobalTheory.zeta_add_lphi_conn_mem
end

section
section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]

theorem EIn_pow_eq_factorial_mul_Ediv (i : ℕ) :
    EIn l e (S O K e) ^ i = (i.factorial : S O K e) * ⟨Ediv K l e i, Ediv_mem_S l e i⟩ := by
  apply Subtype.ext
  have hf : (i.factorial : K) ≠ 0 := natCast_ne_zero' l i.factorial_ne_zero
  have hc : ((i.factorial : S O K e) : K⟦X⟧) = C (i.factorial : K) := by
    rw [map_natCast]; rfl
  simp only [SubmonoidClass.coe_pow, coe_EIn, Subalgebra.coe_mul, Ediv, hc]
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hf, map_one, one_mul]

theorem exists_uIn_pow_eq (j : ℕ) (hj : j ≤ l) : ∃ σ : S O K e, ∃ φ ∈ Fil O K l e j,
    uIn (S O K e) ^ (e * l) = (l : S O K e) ^ (l - j) * σ + φ := by
  have hu : uIn (S O K e) ^ e = EIn l e (S O K e) + -(l : S O K e) := by
    apply Subtype.ext
    simp [E]
  refine ⟨∑ i ∈ Finset.range j, EIn l e (S O K e) ^ i * (-1) ^ (l - i) * (l : S O K e) ^ (j - i) *
      (l.choose i : S O K e),
    ∑ i ∈ Finset.Ico j (l + 1), EIn l e (S O K e) ^ i * (-(l : S O K e)) ^ (l - i) *
      (l.choose i : S O K e), ?_, ?_⟩
  · refine Ideal.sum_mem _ fun i hi => ?_
    have hi' : j ≤ i := (Finset.mem_Ico.1 hi).1
    rw [EIn_pow_eq_factorial_mul_Ediv]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ediv_mem_Fil l e hi')))
  · rw [pow_mul, hu, add_pow, ← Finset.sum_range_add_sum_Ico _ (by omega : j ≤ l + 1),
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < j := Finset.mem_range.1 hi
    have h1 : l - i = (l - j) + (j - i) := by omega
    rw [neg_pow, h1, pow_add, pow_add]
    ring

theorem X_pow_smul_mem_l_pow_MM_add_FilMM (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι) (j : ℕ) (hj : j ≤ l)
    (w : Vec K a ι) (hw : w ∈ P.MM) : ∃ s ∈ P.MM, ∃ f ∈ P.FilMM j,
      (X : K⟦X⟧) ^ (e * l) • w = (l : K) ^ (l - j) • s + f := by
  obtain ⟨σ, φ, hφ, h⟩ := exists_uIn_pow_eq (O := O) (K := K) (l := l) (e := e) j hj
  refine ⟨σ • w, P.MM.smul_mem σ hw, φ • w, Submodule.smul_mem_smul hφ hw, ?_⟩
  have h2 : (X : K⟦X⟧) ^ (e * l) • w = (uIn (S O K e) ^ (e * l)) • w := by
    rw [Subalgebra.smul_def]
    simp
  have h3 : ((l : S O K e) ^ (l - j)) • (σ • w) = (l : K) ^ (l - j) • (σ • w) := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [h2, h, add_smul, mul_smul, h3]

end GlobalTheory.BK
end
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.X_pow_smul_mem_prime_pow_add_filtration_phiModule : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι), ∀ (j : ℕ), j ≤ l → ∀ w ∈ P.MM, ∃ s ∈ P.MM, ∃ f ∈ P.FilMM j, (X : K⟦X⟧) ^ (e * l) • w = (l : K) ^ (l - j) • s + f := by
  atlas_forward_decl GlobalTheory.BK.X_pow_smul_mem_l_pow_MM_add_FilMM
end

section
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.BK

theorem zeta_Y'_fine_bound : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), 1 ≤ η → η < H → 14 * H < l → ∀ y ∈ D.Y', ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), D.zeta y = (l : K) ^ (l - 14 * H) • p + ((l : K) ^ (3 * H))⁻¹ • f := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D hη hηH hl y hy
  obtain ⟨y₀, ⟨hy₀, -⟩, rfl⟩ := hy
  have hy₀' : E K l e ^ η • y₀ ∈ D.M := hy₀
  show ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), D.zeta ((X : K⟦X⟧) ^ e • y₀) = _
  obtain ⟨r, hr, hT⟩ := GlobalTheory.T.zeta_series_higher_terms_mem_lPow_breuilKisin O K l e a ι η H D y₀ hη hηH hl hy₀'
  obtain ⟨w₁, hw₁, hB⟩ := GlobalTheory.T.prime_pow_smul_connection_series_term_mem_lattice O K l e a ι η H D y₀ hη hy₀' 0
  obtain ⟨s, hs, f, hf, hD⟩ := GlobalTheory.T.X_pow_smul_mem_prime_pow_add_filtration_phiModule O K l e a ι D.toPhiMod (10 * H) (by omega) w₁ hw₁
  have hIC := GlobalTheory.T.breuilKisin_integrality_computation O K l e a ι η H D hηH (by omega)
  obtain ⟨p₁, hp₁, f₁, hf₁, rfl⟩ := hIC.1 s hs
  obtain ⟨p₂, hp₂, f₂, hf₂, rfl⟩ := hIC.1 r hr
  have hsm : ∀ {R : Type} [Semiring R] [Module R (Vec K a ι)] (W : Submodule R (Vec K a ι)) (k : ℕ)
      {v : Vec K a ι}, v ∈ W → (l : K) ^ k • v ∈ W := fun W k v hv => by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]; exact nsmul_mem hv _
  refine ⟨p₂ - (l : K) ^ (3 * H - 2 * η) • p₁, sub_mem hp₂ (hsm _ _ hp₁),
    (l : K) ^ (l - 11 * H) • f₂ - (l : K) ^ (2 * H - 2 * η) • ((l : K) ^ (l - 10 * H) • f₁ + f),
    sub_mem (hsm _ _ hf₂) (hsm _ _ (add_mem (hsm _ _ hf₁) hf)), ?_⟩
  simp only [zero_add, pow_one, zero_mul, add_zero, one_mul] at hB
  rw [hD] at hB
  have hl0 : (l : K) ≠ 0 := l_ne_zero l
  have e1 : l - 10 * H = (l - 14 * H) + (3 * H - 2 * η) + (H + 2 * η) := by omega
  have e2 : l - 11 * H = (l - 14 * H) + (2 * H - 2 * η) + (H + 2 * η) := by omega
  have e3 : (l : K) ^ (3 * H) = (l : K) ^ (2 * H - 2 * η) * (l : K) ^ (H + 2 * η) := by
    rw [← pow_add]; congr 1; omega
  rw [e1] at hB
  rw [e1, e2, e3]
  have hz := eq_sub_of_add_eq hT
  rw [hz]
  generalize l - 14 * H = A at *
  generalize 3 * H - 2 * η = B at *
  generalize 2 * H - 2 * η = Dd at *
  generalize H + 2 * η = Cc at *
  generalize (l : K) = x at *
  have hL : D.lphi (D.conn ((X : K⟦X⟧) ^ e • y₀)) = (x ^ Cc)⁻¹ • (x ^ (A + B + Cc) • (p₁ + f₁) + f) := by
    rw [← hB, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hl0), one_smul]
  rw [hL]
  match_scalars <;> field_simp <;> ring

end GlobalTheory.BK
end

open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_zeta_fine_bound_second_basis : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), 1 ≤ η → η < H → 14 * H < l → ∀ y ∈ D.Y', ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), D.zeta y = (l : K) ^ (l - 14 * H) • p + ((l : K) ^ (3 * H))⁻¹ • f := by
  atlas_forward_decl GlobalTheory.BK.zeta_Y'_fine_bound
end
