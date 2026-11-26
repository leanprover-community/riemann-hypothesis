module

import TauCeti.NumberTheory.ArithmeticFunction.Zeta
import TauCeti.NumberTheory.DirichletCharacter.PolyaVinogradov
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Lib.Speed
import Lib.Analytic.ZeroSymmetry

/-!
# The Pólya–Vinogradov bound for initial intervals

For a non-principal character mod `q`, every partial sum of its values is at most
`2 √q (1 + log q)` in absolute value.

* `New.polya_vinogradov`: the Pólya–Vinogradov inequality.

## Relation to the literature

Known result: the Pólya–Vinogradov inequality for sums of a non-principal Dirichlet character. It is
proved here for initial intervals only, with the explicit bound `2 √q (1 + log q)`. The case of a
general character is reduced to the primitive character that induces it, using Tau Ceti's
inequality for the characters induced from a primitive one, and a divisor-count bound. Source:
Pólya 1918, Vinogradov 1918; Davenport, Multiplicative Number Theory; Montgomery–Vaughan Thm 9.18.
-/

@[expose] public section

open Complex Finset DirichletCharacter Real ZMod ArithmeticFunction Moebius NeZero Nat

namespace New

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- A natural number `r` has at most `2 √r` divisors. -/
lemma card_divisors_le_two_mul_sqrt (r : ℕ) : (#r.divisors : ℝ) ≤ 2 * √r := by
  -- Of two complementary divisors one is at most `√r`.
  have h_sub : r.divisors ⊆ Ioc 0 r.sqrt ∪ (Ioc 0 r.sqrt).image fun d : ℕ ↦ r / d := by
    intro d hd
    obtain ⟨⟨e, rfl⟩, hr⟩ : d ∣ r ∧ r ≠ 0 := mem_divisors.mp hd
    obtain ⟨hd_pos, he_pos⟩ : 0 < d ∧ 0 < e := by simpa [Nat.pos_iff_ne_zero] using hr
    rcases le_sqrt_of_eq_mul (rfl : d * e = d * e) with hd_le | he_le
    · simp [hd_pos, hd_le]
    · exact mem_union_right _
        (mem_image.mpr ⟨e, mem_Ioc.mpr ⟨he_pos, he_le⟩, Nat.mul_div_cancel d he_pos⟩)
  grw [card_le_card h_sub, card_union_le, Finset.card_image_le, ← nat_sqrt_le_real_sqrt]
  simp [two_mul]

open scoped ArithmeticFunction.omega in
/-- The **Pólya–Vinogradov inequality** for initial intervals: for a non-principal Dirichlet
character `χ` mod `q` one has `|∑_{1 ≤ v ≤ X} χ v| ≤ 2 √q (1 + log q)` for all `X`. -/
theorem polya_vinogradov (hχ : χ ≠ 1) (X : ℕ) :
    ‖∑ v ∈ Ioc 0 X, χ v‖ ≤ 2 * √q * (1 + Real.log q) := by
  -- Apply Tau Ceti's bound for the primitive `ψ` mod `M` that induces `χ`.
  obtain ⟨M, hMq, ψ, _, hψ, h_ind⟩ := exists_isPrimitive_changeLevel_eq χ
  obtain ⟨r, hr⟩ := exists_eq_mul_right_of_dvd hMq
  have hψ₀ : ψ ≠ 1 := fun h ↦ hχ (by rw [← h_ind, h, changeLevel_one])
  have hM_pos : (0 : ℝ) < M := Nat.cast_pos.mpr (NeZero.pos M)
  have hM_le : (M : ℝ) ≤ q := mod_cast le_of_dvd (NeZero.pos q) hMq
  have hr0 : r ≠ 0 := right_ne_zero_of_mul (hr.symm.trans_ne (NeZero.ne q))
  -- `2 ^ ω r` is at most the number of divisors of `r`
  have h_two_pow : (2 : ℝ) ^ ω r ≤ 2 * √r := by
    refine le_trans ?_ (card_divisors_le_two_mul_sqrt r)
    exact_mod_cast (pow_cardDistinctFactors_le_zeta_pow 2 hr0).trans
      (by simpa using zeta_pow_succ_apply_le_card_divisors_pow 1 r)
  have hqM : q / M = r := by rw [hr, Nat.mul_div_cancel_left _ (NeZero.pos M)]
  have hsq : √(q : ℝ) = √M * √r := by rw [hr, Nat.cast_mul, Real.sqrt_mul hM_pos.le]
  have h := norm_sum_Icc_changeLevel_le ψ hψ hψ₀ hMq X
  rw [hqM] at h
  have hM_one : 1 ≤ M := NeZero.pos M
  have hlog : Real.log M ≤ Real.log q := Real.log_le_log hM_pos hM_le
  have hlog₀ : 0 ≤ Real.log M := Real.log_nonneg (mod_cast hM_one)
  calc ‖∑ v ∈ Ioc 0 X, χ v‖
      = ‖∑ n ∈ Icc 1 X, changeLevel hMq ψ n‖ := by
        have h_Icc : Ioc 0 X = Icc 1 X := by ext; simp; omega
        simp [h_Icc, ← h_ind]
    _ ≤ 2 ^ ω r * (√M * (1 + Real.log M)) := h
    _ ≤ 2 * √r * (√M * (1 + Real.log q)) :=
        mul_le_mul h_two_pow (mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _))
          (mul_nonneg (Real.sqrt_nonneg _) (by linarith)) (by positivity)
    _ = 2 * √q * (1 + Real.log q) := by rw [hsq]; ring

end New
