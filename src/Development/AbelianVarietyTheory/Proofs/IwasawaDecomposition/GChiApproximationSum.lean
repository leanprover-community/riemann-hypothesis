import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplZeta
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplChi
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ZeroCount
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TailAndSumBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogFactorialEqSumVonMangoldtMulDiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogDerivSeriesOfExplicitStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZerosInWindowFiniteAndPosOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZeroSymmetry
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumIndicatorLeZsumR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Psi0TruncatedExplicitFormula
import BuildAid.ForwardExisting

section
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An.GoodBound

theorem inv_eq_self_of_real {q : ℕ} (χ : DirichletCharacter ℂ q) [NeZero q] (h : GlobalTheoryTheory.IsRealChar χ) :
    χ⁻¹ = χ := by
  rw [← MulChar.star_eq_inv]
  ext a
  rw [MulChar.star_apply]
  exact Complex.conj_eq_iff_im.2 (h _)

theorem re_bounds {Q T : ℝ} {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hg : GlobalTheoryTheory.GoodFor Q χ)
    (hT : T ≤ Q) {ρ : ℂ} (hρ : ρ ∈ zerosIn χ 0 T) : 1 / 400 ≤ ρ.re ∧ ρ.re ≤ 1 - 1 / 400 := by
  obtain ⟨hp, hr, -, hz⟩ := hg
  obtain ⟨h0, h1, h2, h3⟩ := hρ
  rw [sub_zero] at h2
  refine ⟨?_, not_lt.1 fun h => hz ρ h (h2.trans hT) h3⟩
  by_contra hlt
  have h4 := (zeros_symm_one_sub q χ hp ρ h0 h1).1.1 h3
  rw [inv_eq_self_of_real χ hr] at h4
  refine hz (1 - ρ) ?_ ?_ h4
  · simp only [Complex.sub_re, Complex.one_re]
    linarith [not_le.1 hlt]
  · simpa using h2.trans hT

theorem recip_le {Q T : ℝ} {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hg : GlobalTheoryTheory.GoodFor Q χ)
    (hT : T ≤ Q) {ρ : ℂ} (hρ : ρ ∈ zerosIn χ 0 T) : 1 / ‖ρ‖ ≤ 400 := by
  have h1 := (re_bounds hg hT hρ).1
  have h2 : ρ.re ≤ ‖ρ‖ := Complex.re_le_norm ρ
  rw [div_le_iff₀ (by linarith)]
  linarith

theorem low_le {Q : ℝ} {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hg : GlobalTheoryTheory.GoodFor Q χ)
    (hQ : 1 ≤ Q) : zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) ≤ 400 * zsumR χ 0 1 (fun _ => 1) := by
  have hf := (ZeroWindow.finite_and_one_le_zmult q χ 0 1).1
  rw [zsumR_eq_sum_toFinset χ _ _ _ hf, zsumR_eq_sum_toFinset χ _ _ _ hf, Finset.mul_sum]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  have := recip_le hg hQ (by simpa using hρ : ρ ∈ zerosIn χ 0 1)
  have h0 : (0 : ℝ) ≤ zmult χ ρ := Nat.cast_nonneg _
  nlinarith

theorem low_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    0 ≤ zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) := by
  have hf := (ZeroWindow.finite_and_one_le_zmult q χ 0 1).1
  rw [zsumR_eq_sum_toFinset χ _ _ _ hf]
  exact Finset.sum_nonneg fun ρ _ => by positivity

theorem norm_zsum_le {Q T u : ℝ} {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hg : GlobalTheoryTheory.GoodFor Q χ)
    (hT : T ≤ Q) (hu : 1 ≤ u) :
    ‖zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤ u ^ (1 - (1 : ℝ) / 400) *
      (zsumR χ 0 T (fun ρ => if 1 < |ρ.im| then 1 / ‖ρ‖ else 0) + 400 * zsumR χ 0 1 (fun _ => 1)) := by
  classical
  have hf := (ZeroWindow.finite_and_one_le_zmult q χ 0 T).1
  have hf1 := (ZeroWindow.finite_and_one_le_zmult q χ 0 1).1
  have hA : 0 ≤ u ^ (1 - (1 : ℝ) / 400) := by positivity
  have hI := sum_indicator_le_zsumR χ 0 1 hf.toFinset hf1
  refine le_trans ?_ (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hI (by norm_num))) hA)
  rw [zsumR_eq_sum_toFinset χ _ _ _ hf, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  unfold zsum
  rw [finsum_mem_eq_finite_toFinset_sum _ hf]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
  have hρ' : ρ ∈ zerosIn χ 0 T := by simpa using hρ
  have h2 : ‖(u : ℂ) ^ ρ / ρ‖ ≤ u ^ (1 - (1 : ℝ) / 400) * (1 / ‖ρ‖) := by
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hu (re_bounds hg hT hρ').2) (by positivity)
  have h3 : 1 / ‖ρ‖ ≤ (if 1 < |ρ.im| then 1 / ‖ρ‖ else 0) +
      400 * (if ρ ∈ zerosIn χ 0 1 then (1 : ℝ) else 0) := by
    by_cases h : 1 < |ρ.im|
    · rw [if_pos h]
      split_ifs <;> simp
    · have : ρ ∈ zerosIn χ 0 1 := ⟨hρ'.1, hρ'.2.1, by simpa using h, hρ'.2.2.2⟩
      rw [if_neg h, if_pos this]
      linarith [recip_le hg hT hρ']
  have h0 : (0 : ℝ) ≤ zmult χ ρ := Nat.cast_nonneg _
  rw [norm_mul, Complex.norm_natCast]
  calc _ ≤ (zmult χ ρ : ℝ) * (u ^ (1 - (1 : ℝ) / 400) * ((if 1 < |ρ.im| then 1 / ‖ρ‖ else 0) +
      400 * (if ρ ∈ zerosIn χ 0 1 then (1 : ℝ) else 0))) :=
        mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 hA)) h0
    _ = _ := by ring

set_option maxHeartbeats 1000000 in

theorem psiChi_bound_of_goodFor : GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.ExplZeta → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (Q : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 3 ≤ Q → χ ≠ 1 → GlobalTheoryTheory.GoodFor Q χ → ∀ u : ℝ, 2 ≤ u → ‖psiChi χ u‖ ≤ C₁ * (u ^ (1 - (1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + u / Q * Real.log (u * Q) ^ 2) := by
  intro hE hL hZ _ hE0
  obtain ⟨C, hC⟩ := ExplUsed.explicit_formula_used hE0 hE hL
  obtain ⟨D, hD⟩ := zsumR_recip_le hZ
  refine ⟨|C| * (5 + 800 * |D|) + 801 * |D| + 1, by positivity, ?_⟩
  intro Q q _ χ hQ hχ hg u hu
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hqQ : (q : ℝ) ≤ Q := hg.2.2.1
  obtain ⟨T, hT2, hTu, hTQ, huT⟩ : ∃ T : ℝ, 2 ≤ T ∧ T ≤ u ∧ T ≤ Q ∧ u / T ≤ 1 + u / Q := by
    have : 0 ≤ u / Q := by positivity
    rcases le_total u Q with h | h
    · exact ⟨u, hu, le_rfl, h, by rw [div_self (by linarith)]; linarith⟩
    · exact ⟨Q, by linarith, h, le_rfl, by linarith⟩
  have h1 := hC q χ hg.1 u T hT2 hTu
  obtain ⟨h2, h3⟩ := hD q χ hg.1 T hT2
  have h4 := norm_zsum_le hg hTQ (by linarith : (1 : ℝ) ≤ u)
  have h5 := low_le hg (by linarith : (1 : ℝ) ≤ Q)
  have h6 := low_nonneg χ
  have hpsi : GlobalTheoryTheory.psi0 χ u = psiChi χ u := by
    simp [GlobalTheoryTheory.psi0, psiChi, hχ]
  rw [hpsi] at h1
  set S := zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)
  set A := u ^ (1 - (1 : ℝ) / 400)
  set L := Real.log (u * Q) with hLdef
  set N := zsumR χ 0 1 (fun _ => (1 : ℝ))
  set R := zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖)
  set H := zsumR χ 0 T (fun ρ => if 1 < |ρ.im| then 1 / ‖ρ‖ else 0)
  have hA1 : 1 ≤ A := Real.one_le_rpow (by linarith) (by norm_num)
  have hP : 6 ≤ u * Q := by nlinarith
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hLL : L ≤ L ^ 2 := by nlinarith
  have h2L : Real.log ((u * Q) ^ 2) = 2 * L := by rw [Real.log_pow, hLdef]; norm_num
  have l1 : Real.log (q * T) ^ 2 ≤ L ^ 2 :=
    pow_le_pow_left₀ (Real.log_nonneg (by nlinarith))
      (Real.log_le_log (by nlinarith) (by nlinarith)) 2
  have hqu : (q : ℝ) * u ≤ u * Q := by nlinarith
  have hqu1 : (1 : ℝ) ≤ q * u := by nlinarith
  have l2 : Real.log (3 * q) ≤ 2 * L := by
    rw [← h2L]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have l2' : 0 ≤ Real.log (3 * q) := Real.log_nonneg (by linarith)
  have l3 : Real.log (q * u) ≤ L := Real.log_le_log (by linarith) hqu
  have l3' : 0 ≤ Real.log (q * u) := Real.log_nonneg hqu1
  have l4 : Real.log (q * u * T) ^ 2 ≤ (2 * L) ^ 2 := by
    refine pow_le_pow_left₀ (Real.log_nonneg (by nlinarith)) ?_ 2
    rw [← h2L, sq]
    exact Real.log_le_log (by positivity)
      (mul_le_mul hqu (by nlinarith) (by linarith) (by linarith))
  have hB : 0 ≤ u / Q := by positivity
  set B := u / Q
  have hD0 := abs_nonneg D
  have hC0 := abs_nonneg C
  have hM : 0 ≤ L ^ 2 := sq_nonneg _
  have hN : N ≤ 2 * (|D| * L ^ 2) := by
    have := h3.trans ((mul_le_mul_of_nonneg_right (le_abs_self D) l2').trans
      (mul_le_mul_of_nonneg_left (l2.trans (by linarith : 2 * L ≤ 2 * L ^ 2)) hD0))
    linarith
  have hH : H ≤ |D| * L ^ 2 :=
    h2.trans ((mul_le_mul_of_nonneg_right (le_abs_self D) (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left l1 hD0))
  have hS : ‖S‖ ≤ A * (801 * (|D| * L ^ 2)) :=
    h4.trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
  have e1 : u * Real.log (q * u * T) ^ 2 / T ≤ (1 + B) * (2 * L) ^ 2 := by
    rw [mul_div_right_comm]
    exact mul_le_mul huT l4 (sq_nonneg _) (by linarith)
  have e0 : 0 ≤ u * Real.log (q * u * T) ^ 2 / T := by positivity
  set M := L ^ 2
  have hAM : M ≤ A * M := le_mul_of_one_le_left hM hA1
  have hBM : 0 ≤ B * M := mul_nonneg hB hM
  have hDM : |D| * M ≤ |D| * (A * M + B * M) := mul_le_mul_of_nonneg_left (by linarith) hD0
  have hDM' : |D| * (A * M) ≤ |D| * (A * M + B * M) := mul_le_mul_of_nonneg_left (by linarith) hD0
  have e2 : u * Real.log (q * u * T) ^ 2 / T + Real.log (q * u) + R ≤
      (5 + 800 * |D|) * (A * M + B * M) := by
    have : (1 + B) * (2 * L) ^ 2 = 4 * M + 4 * (B * M) := by simp only [M]; ring
    have h7 : (5 + 800 * |D|) * (A * M + B * M) = 5 * (A * M) + 5 * (B * M) + 800 * (|D| * (A * M + B * M)) := by
      ring
    linarith
  have e3 := h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)).trans
    (mul_le_mul_of_nonneg_left e2 hC0))
  have htri : ‖psiChi χ u‖ ≤ ‖psiChi χ u + S‖ + ‖S‖ := by
    simpa using norm_sub_le (psiChi χ u + S) S
  have h8 : A * (801 * (|D| * M)) = 801 * (|D| * (A * M)) := by ring
  have h9 : (|C| * (5 + 800 * |D|) + 801 * |D| + 1) * (A * M + B * M) =
      |C| * ((5 + 800 * |D|) * (A * M + B * M)) + 801 * (|D| * (A * M + B * M)) + (A * M + B * M) := by ring
  linarith

end GlobalTheory.Mem.An.GoodBound
end

open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_chi_power_saving_bound : GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.ExplZeta → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (Q : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 3 ≤ Q → χ ≠ 1 → GlobalTheoryTheory.GoodFor Q χ → ∀ u : ℝ, 2 ≤ u → ‖psiChi χ u‖ ≤ C₁ * (u ^ (1 - (1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + u / Q * Real.log (u * Q) ^ 2) := by
  atlas_forward_decl GlobalTheory.Mem.An.GoodBound.psiChi_bound_of_goodFor
end

section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_psi0_add_zsum_le_of_isPrimitive : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ u T : ℝ, 2 ≤ T → T ≤ u → ‖GlobalTheoryTheory.psi0 χ u + zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤ C * (u * Real.log (q * u * T) ^ 2 / T + Real.log (q * u) + zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖)) := by
  first | exact @GlobalTheory.Mem.An.ExplUsed.explicit_formula_used | exact GlobalTheory.Mem.An.ExplUsed.explicit_formula_used | (intros; apply GlobalTheory.Mem.An.ExplUsed.explicit_formula_used <;> assumption)
end

section
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An.GoodLarge

theorem inv_eq_self {q : ℕ} (χ : DirichletCharacter ℂ q) (h : GlobalTheoryTheory.IsRealChar χ) : χ⁻¹ = χ := by
  rw [← MulChar.star_eq_inv]
  ext a
  rw [MulChar.star_apply]
  exact Complex.conj_eq_iff_im.2 (h _)

theorem inv_norm_le {Q : ℝ} {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hQ : 1 ≤ Q)
    (hg : GlobalTheoryTheory.GoodFor Q χ) {ρ : ℂ} (hρ : ρ ∈ zerosIn χ 0 1) : 1 / ‖ρ‖ ≤ 400 := by
  obtain ⟨h0, h1, hT, hL⟩ := hρ
  have h2 := ((zeros_symm_one_sub q χ hg.1 ρ h0 h1).1).1 hL
  rw [inv_eq_self χ hg.2.1] at h2
  have h3 : 1 / 400 ≤ ρ.re := by
    by_contra hc
    refine hg.2.2.2 (1 - ρ) ?_ ?_ h2
    · simp only [Complex.sub_re, Complex.one_re]; linarith
    · simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
      rw [sub_zero] at hT; linarith
  have h4 : 1 / 400 ≤ ‖ρ‖ := h3.trans (Complex.re_le_norm ρ)
  rw [div_le_iff₀ (by linarith)]
  linarith

theorem zsumR_inv_norm_one_le {Q : ℝ} {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hQ : 1 ≤ Q)
    (hg : GlobalTheoryTheory.GoodFor Q χ) :
    zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) ≤ 400 * zsumR χ 0 1 (fun _ => 1) := by
  have hf := (ZeroWindow.finite_and_one_le_zmult q χ 0 1).1
  rw [zsumR_eq_sum_toFinset χ 0 1 _ hf, zsumR_eq_sum_toFinset χ 0 1 _ hf, Finset.mul_sum]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  have := mul_le_mul_of_nonneg_left (inv_norm_le hQ hg (by simpa using hρ))
    (Nat.cast_nonneg (α := ℝ) (zmult χ ρ))
  linarith

theorem zsumR_inv_norm_le {Q : ℝ} {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hQ : 1 ≤ Q)
    (hg : GlobalTheoryTheory.GoodFor Q χ) (T : ℝ) :
    zsumR χ 0 T (fun ρ => 1 / ‖ρ‖) ≤ 400 * zsumR χ 0 1 (fun _ => 1) +
      zsumR χ 0 T (fun ρ => if 1 < |ρ.im| then 1 / ‖ρ‖ else 0) := by
  classical
  have hf := (ZeroWindow.finite_and_one_le_zmult q χ 0 T).1
  have hf1 := (ZeroWindow.finite_and_one_le_zmult q χ 0 1).1
  have h1 := sum_indicator_le_zsumR χ 0 1 hf.toFinset hf1
  rw [zsumR_eq_sum_toFinset χ 0 T _ hf, zsumR_eq_sum_toFinset χ 0 T _ hf]
  refine le_trans ?_ (add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num)) le_rfl)
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  have hρ' : ρ ∈ zerosIn χ 0 T := by simpa using hρ
  have hm : (0 : ℝ) ≤ zmult χ ρ := Nat.cast_nonneg _
  by_cases h : 1 < |ρ.im|
  · rw [if_pos h]
    split_ifs <;> linarith
  · have h2 : ρ ∈ zerosIn χ 0 1 := ⟨hρ'.1, hρ'.2.1, by rw [sub_zero]; linarith, hρ'.2.2.2⟩
    rw [if_neg h, if_pos h2]
    have := mul_le_mul_of_nonneg_left (inv_norm_le hQ hg h2) hm
    linarith

theorem norm_zsum_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (u T M : ℝ)
    (h : ∀ ρ ∈ zerosIn χ 0 T, ‖(u : ℂ) ^ ρ‖ ≤ M) :
    ‖zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤ M * zsumR χ 0 T (fun ρ => 1 / ‖ρ‖) := by
  have hf := (ZeroWindow.finite_and_one_le_zmult q χ 0 T).1
  rw [zsumR_eq_sum_toFinset χ 0 T _ hf, zsum, finsum_mem_eq_finite_toFinset_sum _ hf, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
  rw [norm_mul, norm_div, Complex.norm_natCast, mul_left_comm, mul_one_div]
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (h ρ (by simpa using hρ)) (norm_nonneg _)) (Nat.cast_nonneg _)

theorem re_le (hZ : Formalism.ZeroFreeDirichlet.ZFRDirichlet) : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
    ∀ (Q : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 0 < Q → χ ≠ 1 → GlobalTheoryTheory.GoodFor Q χ →
      ∀ s : ℝ, 1 ≤ s → Real.log q ≤ s → ∀ ρ ∈ zerosIn χ 0 (Real.exp s), ρ.re ≤ 1 - c / s := by
  obtain ⟨c, hc, H⟩ := hZ
  refine ⟨min (c / 4) (1 / 400), by positivity, (min_le_right _ _).trans (by norm_num), ?_⟩
  intro Q q _ χ hQ hχ hg s hs hqs ρ ⟨h0, h1, hT, hL⟩
  rw [sub_zero] at hT
  have hs0 : 0 < s := by linarith
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  by_cases hR : Formalism.ZeroFreeDirichlet.InRegion c q ρ
  · have him := (H q χ ρ hR ⟨Or.inl hχ, hL⟩).2.2.1
    have h2 : ρ.re ≤ 1 - 1 / 400 := by
      by_contra hn
      exact hg.2.2.2 ρ (not_le.1 hn) (by rw [him, abs_zero]; exact hQ.le) hL
    have h3 : min (c / 4) (1 / 400) / s ≤ 1 / 400 :=
      (div_le_self (by positivity) hs).trans (min_le_right _ _)
    linarith
  · unfold Formalism.ZeroFreeDirichlet.InRegion at hR
    have ha : 0 ≤ |ρ.im| := abs_nonneg _
    have hLpos : 0 < Real.log (q * (|ρ.im| + 2)) := Real.log_pos (by nlinarith)
    have hL4 : Real.log (q * (|ρ.im| + 2)) ≤ 4 * s := by
      rw [Real.log_mul (by positivity) (by positivity)]
      have h1 : Real.log (|ρ.im| + 2) ≤ s + 2 := by
        rw [Real.log_le_iff_le_exp (by positivity), Real.exp_add]
        have e1 : 1 ≤ Real.exp s := Real.one_le_exp hs0.le
        have e2 : 3 ≤ Real.exp 2 := by
          have := Real.add_one_le_exp 2
          linarith
        nlinarith
      linarith
    have h2 : c / (4 * s) ≤ c / Real.log (q * (|ρ.im| + 2)) :=
      div_le_div_of_nonneg_left hc.le hLpos hL4
    have h3 : min (c / 4) (1 / 400) / s ≤ c / (4 * s) := by
      rw [← div_div]
      exact div_le_div_of_nonneg_right (min_le_left _ _) hs0.le
    linarith [not_le.1 hR]

theorem psi_le_of_large : GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.ExplZeta → ∃ C₁ c₁ : ℝ, 0 < C₁ ∧ 0 < c₁ ∧ ∀ (Q : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 3 ≤ Q → χ ≠ 1 → GlobalTheoryTheory.GoodFor Q χ → ∀ u : ℝ, Real.exp (Real.log Q ^ 2) ≤ u → ‖psiChi χ u‖ ≤ C₁ * u * Real.exp (-c₁ * Real.sqrt (Real.log u)) := by
  intro h1 h2 h3 h4 h5
  obtain ⟨A₀, hA₀⟩ := GlobalTheory.T.norm_psi0_add_zsum_le_of_isPrimitive h5 h1 h2
  obtain ⟨B₀, hB₀⟩ := zsumR_recip_le h3
  obtain ⟨c, hc, hc1, hre⟩ := re_le h4
  set A := max A₀ 0 with hA
  set B := max B₀ 0 with hB
  have hA0 : 0 ≤ A := le_max_right _ _
  have hB0 : 0 ≤ B := le_max_right _ _
  refine ⟨(1 + 1204 * B + A * (11 + 1200 * B)) * (24 / (c / 2) ^ 4), c / 2, by positivity, by positivity, ?_⟩
  intro Q q _ χ hQ hχ hg u hu
  have hQ0 : 0 < Q := by linarith
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hlQ : 1 ≤ Real.log Q := by
    rw [Real.le_log_iff_exp_le hQ0]
    have := Real.exp_one_lt_d9
    linarith
  have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos _) hu
  have hlu : Real.log Q ^ 2 ≤ Real.log u := (Real.le_log_iff_exp_le hu0).2 hu
  have hlu0 : 0 ≤ Real.log u := le_trans (sq_nonneg _) hlu
  set s := Real.sqrt (Real.log u) with hs
  have hss : s ^ 2 = Real.log u := Real.sq_sqrt hlu0
  have hQs : Real.log Q ≤ s := Real.le_sqrt_of_sq_le hlu
  have hs1 : 1 ≤ s := hlQ.trans hQs
  have hs0 : 0 < s := by linarith
  have hqs : Real.log q ≤ s := (Real.log_le_log (by linarith) hg.2.2.1).trans hQs
  have hq0 : 0 ≤ Real.log q := Real.log_nonneg hq
  have hT2 : 2 ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
  have hs2 : s ≤ s ^ 2 := by nlinarith
  have hs4 : s ^ 2 ≤ s ^ 4 := pow_le_pow_right₀ hs1 (by norm_num)
  have hTu : Real.exp s ≤ u := by
    rw [← Real.le_log_iff_exp_le hu0, ← hss]; exact hs2
  set M := u * Real.exp (-c * s) with hM
  have hM' : u / Real.exp s ≤ M := by
    rw [div_eq_mul_inv, ← Real.exp_neg]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hu0.le
  have hM1 : 1 ≤ M := le_trans ((one_le_div (Real.exp_pos _)).2 hTu) hM'
  have hMz : ∀ ρ ∈ zerosIn χ 0 (Real.exp s), ‖(u : ℂ) ^ ρ‖ ≤ M := by
    intro ρ hρ
    have hre' := hre Q q χ hQ0 hχ hg s hs1 hqs ρ hρ
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0, Real.rpow_def_of_pos hu0]
    have e : M = Real.exp (Real.log u * (1 - c / s)) := by
      rw [hM]
      conv_lhs => rw [← Real.exp_log hu0]
      rw [← Real.exp_add, ← hss]
      congr 1
      field_simp
      ring
    rw [e]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hre' hlu0)
  obtain ⟨hb1, hb2⟩ := hB₀ q χ hg.1 (Real.exp s) hT2
  have hl1 : Real.log (q * Real.exp s) ^ 2 ≤ 4 * s ^ 4 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
    nlinarith
  have hl2 : Real.log (3 * q) ≤ 3 * s ^ 4 := by
    rw [Real.log_mul (by positivity) (by positivity)]
    have := Real.log_le_sub_one_of_pos (x := 3) (by norm_num)
    linarith
  have hl2' : 0 ≤ Real.log (3 * q) := Real.log_nonneg (by linarith)
  have hc1' : zsumR χ 0 (Real.exp s) (fun ρ => if 1 < |ρ.im| then 1 / ‖ρ‖ else 0) ≤ B * (4 * s ^ 4) :=
    hb1.trans (mul_le_mul (le_max_left _ _) hl1 (sq_nonneg _) hB0)
  have hc2 : zsumR χ 0 1 (fun _ => 1) ≤ B * (3 * s ^ 4) :=
    hb2.trans (mul_le_mul (le_max_left _ _) hl2 hl2' hB0)
  have hS1 : zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) ≤ 1200 * B * s ^ 4 := by
    have := zsumR_inv_norm_one_le (by linarith) hg
    linarith
  have hS0 : 0 ≤ zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) := by
    rw [zsumR_eq_sum_toFinset χ 0 1 _ (ZeroWindow.finite_and_one_le_zmult q χ 0 1).1]
    exact Finset.sum_nonneg fun ρ _ => by positivity
  have hST : zsumR χ 0 (Real.exp s) (fun ρ => 1 / ‖ρ‖) ≤ 1204 * B * s ^ 4 := by
    have := zsumR_inv_norm_le (by linarith) hg (Real.exp s)
    linarith
  have hZ : ‖zsum χ 0 (Real.exp s) (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤ M * (1204 * B * s ^ 4) :=
    (norm_zsum_le χ u _ M hMz).trans (mul_le_mul_of_nonneg_left hST (by linarith))
  have hE := hA₀ q χ hg.1 u (Real.exp s) hT2 hTu
  have hp : GlobalTheoryTheory.psi0 χ u = psiChi χ u := by
    rw [GlobalTheoryTheory.psi0, if_neg hχ, sub_zero, psiChi]
  rw [hp] at hE
  have hl3 : Real.log (q * u * Real.exp s) ^ 2 ≤ 9 * s ^ 4 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_exp, ← hss]
    calc _ ≤ (3 * s ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
      _ = _ := by ring
  have hl4 : Real.log (q * u) ≤ 2 * s ^ 4 := by
    rw [Real.log_mul (by positivity) (by positivity), ← hss]
    linarith
  have hl4' : 0 ≤ Real.log (q * u) := by
    rw [Real.log_mul (by positivity) (by positivity)]
    linarith
  have he1 : u * Real.log (q * u * Real.exp s) ^ 2 / Real.exp s ≤ M * (9 * s ^ 4) := by
    rw [mul_div_right_comm]
    exact mul_le_mul hM' hl3 (sq_nonneg _) (by linarith)
  have he2 : 2 * s ^ 4 + 1200 * B * s ^ 4 ≤ M * (2 * s ^ 4 + 1200 * B * s ^ 4) :=
    le_mul_of_one_le_left (by positivity) hM1
  have hE' : ‖psiChi χ u + zsum χ 0 (Real.exp s) (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤
      A * (M * (9 * s ^ 4) + M * (2 * s ^ 4 + 1200 * B * s ^ 4)) :=
    hE.trans (mul_le_mul (le_max_left _ _) (by linarith)
      (add_nonneg (add_nonneg (by positivity) hl4') hS0) hA0)
  have hfin : ‖psiChi χ u‖ ≤ (1 + 1204 * B + A * (11 + 1200 * B)) * (M * s ^ 4) := by
    have h := norm_sub_le (psiChi χ u + zsum χ 0 (Real.exp s) (fun ρ => (u : ℂ) ^ ρ / ρ))
      (zsum χ 0 (Real.exp s) (fun ρ => (u : ℂ) ^ ρ / ρ))
    rw [add_sub_cancel_right] at h
    have : 0 ≤ M * s ^ 4 := by positivity
    linarith
  have hsq : s ^ 4 ≤ 24 / (c / 2) ^ 4 * Real.exp (c / 2 * s) := by
    have h := Real.pow_div_factorial_le_exp (c / 2 * s) (by positivity) 4
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    rw [mul_pow] at h
    norm_num [Nat.factorial] at h
    linarith
  refine hfin.trans ?_
  have e : Real.exp (-(c / 2) * s) = Real.exp (-c * s) * Real.exp (c / 2 * s) := by
    rw [← Real.exp_add]; congr 1; ring
  calc _ ≤ (1 + 1204 * B + A * (11 + 1200 * B)) * (M * (24 / (c / 2) ^ 4 * Real.exp (c / 2 * s))) := by
        gcongr
    _ = _ := by rw [e, hM]; ring

end GlobalTheory.Mem.An.GoodLarge
end

open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_chi_sqrt_log_bound : GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.ExplZeta → ∃ C₁ c₁ : ℝ, 0 < C₁ ∧ 0 < c₁ ∧ ∀ (Q : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 3 ≤ Q → χ ≠ 1 → GlobalTheoryTheory.GoodFor Q χ → ∀ u : ℝ, Real.exp (Real.log Q ^ 2) ≤ u → ‖psiChi χ u‖ ≤ C₁ * u * Real.exp (-c₁ * Real.sqrt (Real.log u)) := by
  atlas_forward_decl GlobalTheory.Mem.An.GoodLarge.psi_le_of_large
end

section
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.GoodCharacterSum

theorem gChi_add_sum_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (x z : ℝ)
    (hx : 0 ≤ x) (hz : x ≤ z) :
    GlobalTheoryTheory.gChi χ x + ∑ n ∈ Icc 1 ⌊z⌋₊, (GlobalTheoryTheory.cn x n : ℂ) * χ (n : ZMod q) =
      -((x : ℂ) * (-GlobalTheoryTheory.logDerivativeAtOne χ -
        ∑ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) / (n : ℂ))) := by
  have h1 : GlobalTheoryTheory.sumLamChi χ x = ∑ n ∈ Icc 1 ⌊z⌋₊,
      ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((max (x / n - 1) 0 : ℝ) : ℂ) := by
    unfold GlobalTheoryTheory.sumLamChi
    apply Finset.sum_subset (Finset.Icc_subset_Icc_right (Nat.floor_le_floor hz))
    intro n hn hn'
    have h1n : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have hlt : ⌊x⌋₊ < n := by
      by_contra h
      exact hn' (Finset.mem_Icc.2 ⟨h1n, not_lt.1 h⟩)
    have hxn : x < n := (Nat.floor_lt hx).1 hlt
    have hn0 : (0 : ℝ) < n := by exact_mod_cast h1n
    have : x / n - 1 ≤ 0 := by
      have := (div_le_one hn0).2 hxn.le
      linarith
    rw [max_eq_right this]
    simp
  have h2 : ∀ n ∈ Icc 1 ⌊z⌋₊,
      ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((max (x / n - 1) 0 : ℝ) : ℂ) +
        (GlobalTheoryTheory.cn x n : ℂ) * χ (n : ZMod q) =
      (x : ℂ) * (((Λ n : ℝ) : ℂ) * χ (n : ZMod q) / (n : ℂ)) := by
    intro n _
    have hm : max (x / n - 1) 0 + min 1 (x / n) = x / n := by
      rcases le_total 1 (x / n) with h | h
      · rw [max_eq_left (by linarith), min_eq_left h]; ring
      · rw [max_eq_right (by linarith), min_eq_right h]; ring
    have hm' : ((max (x / n - 1) 0 : ℝ) : ℂ) + ((min 1 (x / n) : ℝ) : ℂ) = (x : ℂ) / (n : ℂ) := by
      rw [← Complex.ofReal_add, hm]; push_cast; rfl
    unfold GlobalTheoryTheory.cn
    rw [Complex.ofReal_mul]
    linear_combination (((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) * hm'
  unfold GlobalTheoryTheory.gChi
  rw [if_neg hχ, h1, mul_sub, Finset.mul_sum, ← Finset.sum_congr rfl h2, Finset.sum_add_distrib]
  ring

theorem gChi_add_sum_bound : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x → ∀ (Q : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 0 < Q → x ^ (eps / 6) ≤ Real.log Q → Real.log Q ≤ x ^ (eps / 4) → χ ≠ 1 → GlobalTheoryTheory.GoodFor Q χ → ‖GlobalTheoryTheory.gChi χ x + ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, (GlobalTheoryTheory.cn x n : ℂ) * χ (n : ZMod q)‖ ≤ x ^ eps ∧ ‖GlobalTheoryTheory.logDerivativeAtOne χ‖ ≤ C * Real.log x := by
  intro hZ hC hL hN hF eps h0 h1
  obtain ⟨C₁, hC₁, H1⟩ := GlobalTheory.T.psi_chi_power_saving_bound hC hL hN hF hZ
  obtain ⟨C₂, c₂, hC₂, hc₂, H2⟩ := GlobalTheory.T.psi_chi_sqrt_log_bound hC hL hN hF hZ
  obtain ⟨CM, hCM, HM⟩ : ∃ CM : ℝ, 0 ≤ CM ∧ ∀ y : ℝ, 1 ≤ y →
      |∑ n ∈ Icc 1 ⌊y⌋₊, Λ n / (n : ℝ) - Real.log y| ≤ CM := GlobalTheory.mertens_first_vonMangoldt
  have HS := GlobalTheory.T.log_deriv_series_of_explicit hZ hC hL hN hF
  obtain ⟨x₀, C, HT⟩ := GlobalTheory.GoodCharacterTail.tail_and_sum_bound eps h0 (by linarith)
    (max C₁ C₂) c₂ CM (lt_max_of_lt_left hC₁) hc₂ hCM
  refine ⟨max x₀ (max 1 ((2 : ℝ) ^ (6 / eps))), max C 1, lt_max_of_lt_right one_pos, ?_⟩
  intro x hx Q q _ χ hQ hl hu hχ hg
  have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx2 : (2 : ℝ) ^ (6 / eps) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have h2 : (2 : ℝ) ≤ x ^ (eps / 6) := by
    have := Real.rpow_le_rpow (by positivity) hx2 (by positivity : 0 ≤ eps / 6)
    rw [← Real.rpow_mul (by norm_num), show 6 / eps * (eps / 6) = 1 by field_simp, Real.rpow_one] at this
    exact this
  have hQ3 : 3 ≤ Q := by
    have := Real.log_le_sub_one_of_pos hQ
    linarith
  have key := HT x hx0 Q hQ hl hu (fun n => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) (-GlobalTheoryTheory.logDerivativeAtOne χ)
    (HS q χ hχ) ?_ ?_ ?_
  · refine ⟨?_, ?_⟩
    · have hz : x ≤ x ^ (400 : ℝ) := by
        have := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 : ℝ) ≤ 400)
        rwa [Real.rpow_one] at this
      rw [gChi_add_sum_eq χ hχ x _ (by linarith) hz, norm_neg]
      exact key.1
    · have := key.2
      rw [norm_neg] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg hx1))
  · intro y hy
    have := (abs_le.1 (HM y hy)).2
    refine le_trans (Finset.sum_le_sum fun n _ => ?_) (by linarith : ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n / (n : ℝ) ≤ _)
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
    exact mul_le_of_le_one_right vonMangoldt_nonneg (χ.norm_le_one _)
  · intro u hu2
    refine le_trans (H1 Q q χ hQ3 hχ hg u hu2) (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    have : 0 < u := by linarith
    positivity
  · intro u hu2
    have : 0 < u := lt_of_lt_of_le (Real.exp_pos _) hu2
    refine le_trans (H2 Q q χ hQ3 hχ hg u hu2) ?_
    gcongr
    exact le_max_right _ _

end GlobalTheory.GoodCharacterSum
end

open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.g_chi_approximation_sum : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x → ∀ (Q : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 0 < Q → x ^ (eps / 6) ≤ Real.log Q → Real.log Q ≤ x ^ (eps / 4) → χ ≠ 1 → GlobalTheoryTheory.GoodFor Q χ → ‖GlobalTheoryTheory.gChi χ x + ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, (GlobalTheoryTheory.cn x n : ℂ) * χ (n : ZMod q)‖ ≤ x ^ eps ∧ ‖GlobalTheoryTheory.logDerivativeAtOne χ‖ ≤ C * Real.log x := by
  atlas_forward_decl GlobalTheory.GoodCharacterSum.gChi_add_sum_bound
end
