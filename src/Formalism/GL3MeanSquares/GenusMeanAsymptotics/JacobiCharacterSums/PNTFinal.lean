import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTEOf
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PrimeCountOfPsi
import Mathlib
import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTZSum
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDens
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplMain
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHBSt
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHB

section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem rangeA_card_char_le (M : ℕ) [NeZero M] :
    ((Finset.univ : Finset (DirichletCharacter ℂ M)).card : ℝ) ≤ M := by
  have h : (Finset.univ : Finset (DirichletCharacter ℂ M)).card = M.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ M]
  rw [h]
  exact_mod_cast Nat.totient_le M

theorem rangeA_far_term (M : ℕ) (hM : 8 ≤ M) (y cA β : ℝ) (hy : 2 ≤ y) (hcA : cA ≤ cZ)
    (hl : Real.log M ≤ cA * Real.sqrt (Real.log y)) (hβ : 1 / 2 ≤ β)
    (hr : ¬ InRegion cZ M (β : ℂ)) :
    ‖(y : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ 2 * y * Real.exp (-(Real.sqrt (Real.log y) / 2)) := by
  have hy0 : 0 < y := by linarith
  have hL : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  set s := Real.sqrt (Real.log y) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s * s = Real.log y := Real.mul_self_sqrt hL
  have hMr : (8 : ℝ) ≤ M := by exact_mod_cast hM
  have hZ := cZ_pos
  unfold InRegion at hr
  simp only [Complex.ofReal_im, abs_zero, zero_add, Complex.ofReal_re, not_le] at hr
  set l := Real.log ((M : ℝ) * 2) with hl'
  have hl0 : 0 < l := Real.log_pos (by linarith)
  have hl2 : l ≤ 2 * Real.log M := by
    rw [hl', Real.log_mul (by linarith) (by norm_num)]
    have : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hl3 : l ≤ 2 * cZ * s := by nlinarith
  have h1 : cZ < (1 - β) * l := by
    have : cZ / l < 1 - β := by linarith
    rwa [div_lt_iff₀ hl0] at this
  have hb1 : 0 < 1 - β := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  have h2 : s / 2 ≤ (1 - β) * Real.log y := by
    have h3 : cZ * s ≤ (1 - β) * (2 * cZ * s) * s := by
      have : (1 - β) * l ≤ (1 - β) * (2 * cZ * s) := mul_le_mul_of_nonneg_left hl3 hb1.le
      nlinarith
    have h4 : cZ * (s / 2) ≤ cZ * ((1 - β) * (s * s)) := by nlinarith
    rw [← hss]
    exact le_of_mul_le_mul_left h4 hZ
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.ofReal_re, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < β)]
  have h5 : y ^ β = y * Real.exp (-((1 - β) * Real.log y)) := by
    rw [Real.rpow_def_of_pos hy0]
    nth_rewrite 2 [← Real.exp_log hy0]
    rw [← Real.exp_add]
    congr 1
    ring
  have h6 : Real.exp (-((1 - β) * Real.log y)) ≤ Real.exp (-(s / 2)) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [div_le_iff₀ (by linarith), h5]
  have h7 : 0 < Real.exp (-(s / 2)) := Real.exp_pos _
  have : y * Real.exp (-((1 - β) * Real.log y)) ≤ y * Real.exp (-(s / 2)) :=
    mul_le_mul_of_nonneg_left h6 hy0.le
  have h8 : 0 ≤ y * Real.exp (-(s / 2)) := by positivity
  nlinarith

theorem rangeA_excZeros_empty (M : ℕ) [NeZero M] (hM : 2 ≤ M) (χ : DirichletCharacter ℂ M)
    (h : ∀ β : ℝ, eOf M = some (χ, β) → ¬ InRegion cZ M (β : ℂ)) : ExcZeros cZ χ ∅ := by
  refine ⟨by simp, by simp, ?_⟩
  intro s hs hz
  obtain ⟨β₁, h1, h2, -⟩ := zero_in_region M hM χ s hs hz
  exact absurd (h2 ▸ hs) (h β₁ h1)

theorem rangeA_excZeros_single (M : ℕ) [NeZero M] (hM : 2 ≤ M) (χ : DirichletCharacter ℂ M) (β : ℝ)
    (h : eOf M = some (χ, β)) (hr : InRegion cZ M (β : ℂ)) : ExcZeros cZ χ {β} := by
  have he := eOf_exc M _ h
  have hz : IsLZero χ (β : ℂ) := ⟨Or.inl he.2.1, he.2.2.1⟩
  obtain ⟨-, -, -, hd⟩ := zero_in_region M hM χ _ hr hz
  refine ⟨by simp, ?_, ?_⟩
  · intro b hb
    rw [Finset.mem_singleton] at hb
    subst hb
    exact ⟨he.2.1, hr, he.2.2.1, hd⟩
  · intro s hs hz'
    obtain ⟨β₁, h1, h2, -⟩ := zero_in_region M hM χ s hs hz'
    rw [h] at h1
    have : β = β₁ := by simpa using h1
    exact ⟨β, by simp, by rw [h2, this]⟩

theorem rangeA_one_char (c C cA : ℝ)
    (H : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (B : Finset ℝ) (x : ℝ), ExcZeros cZ χ B → 2 ≤ x →
      (q : ℝ) ≤ Real.exp (c * Real.sqrt (Real.log x)) →
      ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0) + ∑ β ∈ B, (x : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)))
    (hcA : cA ≤ cZ) (hcA' : cA ≤ c) (M : ℕ) [NeZero M] (hM : 8 ≤ M) (y : ℝ) (hy : 2 ≤ y)
    (hl : Real.log M ≤ cA * Real.sqrt (Real.log y)) (χ : DirichletCharacter ℂ M) :
    ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      C * y * Real.exp (-c * Real.sqrt (Real.log y)) + 2 * y * Real.exp (-(Real.sqrt (Real.log y) / 2)) := by
  have hM2 : 2 ≤ M := by omega
  have hMr : (8 : ℝ) ≤ M := by exact_mod_cast hM
  have hs0 : 0 ≤ Real.sqrt (Real.log y) := Real.sqrt_nonneg _
  have hq : (M : ℝ) ≤ Real.exp (c * Real.sqrt (Real.log y)) := by
    rw [← Real.exp_log (by linarith : (0 : ℝ) < M)]
    exact Real.exp_le_exp.mpr (hl.trans (mul_le_mul_of_nonneg_right hcA' hs0))
  have hE : 0 ≤ 2 * y * Real.exp (-(Real.sqrt (Real.log y) / 2)) := by positivity
  have H' : ∀ B : Finset ℝ, ExcZeros cZ χ B →
      ‖psiChi χ y - mainPsi none χ y + ∑ β ∈ B, (y : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤
        C * y * Real.exp (-c * Real.sqrt (Real.log y)) := by
    intro B hB
    have h0 := H M χ B y hB hy hq
    simp only [mainPsi, sub_zero]
    convert h0
  have hsome : ∀ (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ), mainPsi (some (χ₁, β₁)) χ y =
      mainPsi none χ y - (if χ = χ₁ then (y : ℂ) ^ (β₁ : ℂ) / (β₁ : ℂ) else 0) := by
    intro χ₁ β₁
    simp only [mainPsi, sub_zero]
    congr
  rcases he : eOf M with _ | ⟨χ₁, β₁⟩
  · have h0 := H' ∅ (rangeA_excZeros_empty M hM2 χ (by intro β hβ; rw [he] at hβ; simp at hβ))
    simp only [Finset.sum_empty, add_zero] at h0
    linarith
  · rw [hsome]
    by_cases hχ : χ = χ₁
    · subst hχ
      rw [if_pos rfl, ← sub_add]
      by_cases hr : InRegion cZ M (β₁ : ℂ)
      · have h0 := H' {β₁} (rangeA_excZeros_single M hM2 χ β₁ he hr)
        simp only [Finset.sum_singleton] at h0
        linarith
      · have h0 := H' ∅ (rangeA_excZeros_empty M hM2 χ (by
          intro β hβ; rw [he] at hβ
          have : β₁ = β := by simpa using hβ
          rw [← this]; exact hr))
        simp only [Finset.sum_empty, add_zero] at h0
        have hex := eOf_exc M _ he
        have hβ : 1 / 2 ≤ β₁ := by
          have h1 := hex.2.2.2.1
          have hlog : 1 ≤ Real.log M := by
            rw [Real.le_log_iff_exp_le (by linarith)]
            have := Real.exp_one_lt_d9
            linarith
          have : 1 / (8 * Real.log M) ≤ 1 / 8 := by
            apply one_div_le_one_div_of_le (by norm_num) (by linarith)
          simp only at h1
          linarith
        have h1 := rangeA_far_term M hM y cA β₁ hy hcA hl hβ hr
        exact (norm_add_le _ _).trans (add_le_add h0 h1)
    · have h0 := H' ∅ (rangeA_excZeros_empty M hM2 χ (by
          intro β hβ; rw [he] at hβ
          have : χ₁ = χ := by
            have := Option.some.inj hβ
            exact (Prod.mk.inj this).1
          exact absurd this.symm hχ))
      simp only [Finset.sum_empty, add_zero] at h0
      rw [if_neg hχ, sub_zero]
      linarith

theorem psi_relative_near_range : PsiRelA := by
  obtain ⟨c, C, hc, H⟩ := psiChiBound cZ cZ_pos cZ_le
  obtain ⟨c₁, hc₁, H₁⟩ := etaOf_lower 1 one_pos
  have hZ := cZ_pos
  have hZ' := cZ_le
  refine ⟨min (c / 4) cZ, min (c / 2) (2 / 5), (|C| + 2) / c₁, lt_min (by linarith) hZ,
    lt_min (by linarith) (by norm_num), ?_⟩
  intro M _ h8 y hy hl
  have hM : 8 ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h8
  have hMr : (8 : ℝ) ≤ M := by exact_mod_cast hM
  have hy0 : 0 < y := by linarith
  set cA := min (c / 4) cZ with hcA
  set c' := min (c / 2) (2 / 5 : ℝ) with hc'
  set s := Real.sqrt (Real.log y) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hA1 : cA ≤ c / 4 := min_le_left _ _
  have hA2 : cA ≤ cZ := min_le_right _ _
  have hc1 : c' ≤ c / 2 := min_le_left _ _
  have hc2 : c' ≤ 2 / 5 := min_le_right _ _
  have hsum : ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      (M : ℝ) * (|C| * y * Real.exp (-c * s) + 2 * y * Real.exp (-(s / 2))) := by
    have hb : 0 ≤ |C| * y * Real.exp (-c * s) + 2 * y * Real.exp (-(s / 2)) := by positivity
    calc ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖
        ≤ ∑ _χ : DirichletCharacter ℂ M, (|C| * y * Real.exp (-c * s) + 2 * y * Real.exp (-(s / 2))) := by
          apply Finset.sum_le_sum
          intro χ _
          have h0 := rangeA_one_char c C cA H hA2 (by linarith) M hM y hy hl χ
          have h1 : C * y * Real.exp (-c * s) ≤ |C| * y * Real.exp (-c * s) := by
            have : 0 ≤ y * Real.exp (-c * s) := by positivity
            have h2 := mul_le_mul_of_nonneg_right (le_abs_self C) this
            linarith
          linarith
      _ = ((Finset.univ : Finset (DirichletCharacter ℂ M)).card : ℝ) *
            (|C| * y * Real.exp (-c * s) + 2 * y * Real.exp (-(s / 2))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (rangeA_card_char_le M) hb
  have heta : c₁ ≤ etaOf M * M := by
    have h0 := H₁ M (by omega)
    rw [Real.rpow_neg_one] at h0
    have h1 := mul_le_mul_of_nonneg_right h0 (by linarith : (0 : ℝ) ≤ M)
    rwa [mul_assoc, inv_mul_cancel₀ (by linarith), mul_one] at h1
  have hMe : (M : ℝ) ≤ Real.exp (cA * s) := by
    rw [← Real.exp_log (by linarith : (0 : ℝ) < M)]
    exact Real.exp_le_exp.mpr hl
  have hMM : (M : ℝ) * M ≤ Real.exp (2 * cA * s) := by
    have : Real.exp (2 * cA * s) = Real.exp (cA * s) * Real.exp (cA * s) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]
    exact mul_le_mul hMe hMe (by linarith) (Real.exp_pos _).le
  have e1 : (M : ℝ) * M * Real.exp (-c * s) ≤ Real.exp (-(c' * s)) := by
    calc (M : ℝ) * M * Real.exp (-c * s) ≤ Real.exp (2 * cA * s) * Real.exp (-c * s) :=
          mul_le_mul_of_nonneg_right hMM (Real.exp_pos _).le
      _ = Real.exp (2 * cA * s + -c * s) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have e2 : (M : ℝ) * M * Real.exp (-(s / 2)) ≤ Real.exp (-(c' * s)) := by
    calc (M : ℝ) * M * Real.exp (-(s / 2)) ≤ Real.exp (2 * cA * s) * Real.exp (-(s / 2)) :=
          mul_le_mul_of_nonneg_right hMM (Real.exp_pos _).le
      _ = Real.exp (2 * cA * s + -(s / 2)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  refine hsum.trans ?_
  set X := Real.exp (-(c' * s)) with hX
  have hX0 : 0 < X := Real.exp_pos _
  have hM0 : (0 : ℝ) < M := by linarith

  have key : (M : ℝ) * ((M : ℝ) * (|C| * y * Real.exp (-c * s) + 2 * y * Real.exp (-(s / 2)))) ≤
      (|C| + 2) * y * X := by
    have a1 : |C| * y * ((M : ℝ) * M * Real.exp (-c * s)) ≤ |C| * y * X :=
      mul_le_mul_of_nonneg_left e1 (by positivity)
    have a2 : 2 * y * ((M : ℝ) * M * Real.exp (-(s / 2))) ≤ 2 * y * X :=
      mul_le_mul_of_nonneg_left e2 (by positivity)
    nlinarith
  have key2 : (|C| + 2) * y * X ≤ (M : ℝ) * ((|C| + 2) / c₁ * y * etaOf M * X) := by
    have : (M : ℝ) * ((|C| + 2) / c₁ * y * etaOf M * X) = (|C| + 2) * y * X * ((etaOf M * M) / c₁) := by
      field_simp
    rw [this]
    have h1 : 1 ≤ (etaOf M * M) / c₁ := by rwa [le_div_iff₀ hc₁, one_mul]
    have h2 : 0 ≤ (|C| + 2) * y * X := by positivity
    nlinarith
  exact le_of_mul_le_mul_left (key.trans key2) hM0

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem glue_aux {S A B y η E E' F : ℝ} (h : S ≤ A * y * η * E) (hy : 0 ≤ y) (hη : 0 ≤ η)
    (hE : 0 ≤ E) (hEE : E ≤ E') (hF : 0 ≤ F) (hAB : A ≤ B) (hB : 0 ≤ B) :
    S ≤ B * y * η * (E' + F) := by
  have h1 : A * y * η * E ≤ B * y * η * E := by
    have : 0 ≤ y * η * E := by positivity
    nlinarith
  have h2 : B * y * η * E ≤ B * y * η * (E' + F) := by
    have : 0 ≤ B * y * η := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) this
  linarith

theorem glue_ranges : GlueOf := by
  rintro ⟨cA, c, A, hcA, hc, hA⟩ hB
  obtain ⟨c', A', C₀, hc', hB'⟩ := hB cA hcA
  refine ⟨min c c', max A 0 + max A' 0, C₀, lt_min hc hc', ?_⟩
  intro M _ h8 y hy hC
  have hM : 2 ≤ M := by
    have : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
    have := Nat.le_of_dvd this h8
    omega
  have hη : 0 ≤ etaOf M := (etaOf_pos M hM).le
  have hy0 : 0 ≤ y := by linarith
  have hL : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hlM : 0 < Real.log M := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hA0 : 0 ≤ max A 0 := le_max_right _ _
  have hA0' : 0 ≤ max A' 0 := le_max_right _ _
  by_cases hr : Real.log M ≤ cA * Real.sqrt (Real.log y)
  · have h := hA M h8 y hy hr
    rw [add_comm (Real.exp _)]
    refine glue_aux h hy0 hη (Real.exp_pos _).le ?_ (Real.exp_pos _).le ?_ (by positivity)
    · apply Real.exp_le_exp.mpr
      have : min c c' * Real.sqrt (Real.log y) ≤ c * Real.sqrt (Real.log y) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)
      linarith
    · have := le_max_left A 0
      linarith
  · have h := hB' M h8 y hy hC (not_le.mp hr)
    refine glue_aux h hy0 hη (Real.exp_pos _).le ?_ (Real.exp_pos _).le ?_ (by positivity)
    · apply Real.exp_le_exp.mpr
      have h1 : min c c' * Real.log y ≤ c' * Real.log y :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hL
      have h2 : min c c' * Real.log y / Real.log M ≤ c' * Real.log y / Real.log M :=
        div_le_div_of_nonneg_right h1 hlM.le
      linarith
    · have := le_max_left A' 0
      linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section
open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

lemma sharp_cpow_sub_one {ρ : ℂ} (hρ0 : ρ ≠ 0) (hre : ρ.re ≤ 1) {t : ℝ} (ht : 1 ≤ t) :
    ‖(t : ℂ) ^ ρ - 1‖ ≤ ‖ρ‖ * (t - 1) := by
  have hd : ∀ x ∈ Set.Icc (1 : ℝ) t,
      HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ ρ) (ρ * (x : ℂ) ^ (ρ - 1)) (Set.Icc 1 t) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by linarith [hx.1]
    exact ((Complex.hasStrictDerivAt_cpow_const (Complex.ofReal_mem_slitPlane.2 hx0)).hasDerivAt.comp_ofReal).hasDerivWithinAt
  have hb : ∀ x ∈ Set.Ico (1 : ℝ) t, ‖ρ * (x : ℂ) ^ (ρ - 1)‖ ≤ ‖ρ‖ := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by linarith [hx.1]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have h1 : x ^ (ρ - 1).re ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.1 (by simp; linarith)
    calc ‖ρ‖ * x ^ (ρ - 1).re ≤ ‖ρ‖ * 1 := by gcongr
      _ = ‖ρ‖ := mul_one _
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb t ⟨ht, le_rfl⟩
  simpa using h

lemma differenced_kernel_bound {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) (hre : ρ.re ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    ‖(((1 + δ : ℝ) : ℂ) ^ (ρ - 1) - 1) / (ρ - 1) + (((1 + δ)⁻¹ - 1 : ℝ) : ℂ)‖ ≤ ‖ρ‖ * δ * δ := by
  have hρ1' : ρ - 1 ≠ 0 := sub_ne_zero.2 hρ1
  let f : ℝ → ℂ := fun u => (((u : ℂ) ^ (ρ - 1) - 1) / (ρ - 1)) + (((u⁻¹ - 1 : ℝ)) : ℂ)
  let f' : ℝ → ℂ := fun u => ((u : ℂ) ^ ρ - 1) / (u : ℂ) ^ 2
  have hd : ∀ x ∈ Set.Icc (1 : ℝ) (1 + δ), HasDerivWithinAt f (f' x) (Set.Icc 1 (1 + δ)) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by linarith [hx.1]
    have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx0.ne'
    have h1 := (((Complex.hasStrictDerivAt_cpow_const (c := ρ - 1)
      (Complex.ofReal_mem_slitPlane.2 hx0)).hasDerivAt.comp_ofReal).sub_const 1).div_const (ρ - 1)
    have h2 := ((hasDerivAt_inv hx0.ne').sub_const 1).ofReal_comp
    refine (h1.add h2).hasDerivWithinAt.congr_deriv ?_
    simp only [f']
    have e1 : (x : ℂ) ^ (ρ - 1 - 1) = (x : ℂ) ^ ρ / (x : ℂ) ^ 2 := by
      rw [show ρ - 1 - 1 = ρ - 2 by ring, Complex.cpow_sub _ _ hxc,
        show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
    rw [e1]
    push_cast
    field_simp
    ring
  have hb : ∀ x ∈ Set.Ico (1 : ℝ) (1 + δ), ‖f' x‖ ≤ ‖ρ‖ * δ := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by linarith [hx.1]
    have hk := sharp_cpow_sub_one hρ0 hre hx.1
    simp only [f']
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx0.le]
    have hx1 : 1 ≤ x ^ 2 := one_le_pow₀ hx.1
    calc ‖(x : ℂ) ^ ρ - 1‖ / x ^ 2 ≤ ‖(x : ℂ) ^ ρ - 1‖ := div_le_self (norm_nonneg _) hx1
      _ ≤ ‖ρ‖ * (x - 1) := hk
      _ ≤ ‖ρ‖ * δ := by gcongr; linarith [hx.2]
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb (1 + δ) ⟨by linarith, le_rfl⟩
  have hf1 : f 1 = 0 := by simp [f]
  rw [hf1, sub_zero, show 1 + δ - 1 = δ by ring] at h
  exact h

lemma sharp_kernel {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) (hre : ρ.re ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) :
    ‖(((1 + δ) / δ : ℝ) : ℂ) * ((((1 + δ : ℝ) : ℂ) ^ (ρ - 1) - 1) / (ρ - 1)) - 1‖ ≤ 2 * δ * ‖ρ‖ := by
  set g : ℂ := (((1 + δ : ℝ) : ℂ) ^ (ρ - 1) - 1) / (ρ - 1) with hg
  set e : ℂ := g + (((1 + δ)⁻¹ - 1 : ℝ) : ℂ) with he
  have hae := differenced_kernel_bound hρ0 hρ1 hre hδ
  rw [← hg, ← he] at hae
  have hr : (1 + δ) / δ * ((1 + δ)⁻¹ - 1) = -1 := by
    field_simp
    ring
  have hid : (((1 + δ) / δ : ℝ) : ℂ) * g - 1 = (((1 + δ) / δ : ℝ) : ℂ) * e := by
    rw [he, mul_add, ← Complex.ofReal_mul, hr]
    push_cast
    ring
  have hq : 0 < (1 + δ) / δ := by positivity
  rw [hid, norm_mul, Complex.norm_real, Real.norm_of_nonneg hq.le]
  calc (1 + δ) / δ * ‖e‖ ≤ (1 + δ) / δ * (‖ρ‖ * δ * δ) := by gcongr
    _ = (1 + δ) * (δ * ‖ρ‖) := by field_simp
    _ ≤ 2 * (δ * ‖ρ‖) := by gcongr; linarith
    _ = 2 * δ * ‖ρ‖ := by ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section
open Finset Complex ArithmeticFunction

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

lemma sharp_split (g : ℕ → ℂ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Icc 1 b, g n = ∑ n ∈ Icc 1 a, g n + ∑ n ∈ Ioc a b, g n := by
  have hd : Disjoint (Icc 1 a) (Ioc a b) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hx hx'
    omega
  have hu : Icc 1 b = Icc 1 a ∪ Ioc a b := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]
    omega
  rw [hu, Finset.sum_union hd]

lemma sharp_schi_div {N : ℕ} (χ : DirichletCharacter ℂ N) {v : ℝ} (hv : 0 < v) :
    Formalism.ZeroFreeDirichlet.Schi χ v / (v : ℂ) =
      ∑ n ∈ Icc 1 ⌊v⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * ((1 / n - 1 / v : ℝ) : ℂ) := by
  rw [Formalism.ZeroFreeDirichlet.Schi.eq_1, Finset.sum_div]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hv0 : v ≠ 0 := hv.ne'
  rw [mul_div_assoc]
  congr 1
  rw [← Complex.ofReal_div]
  congr 1
  field_simp

lemma sharp_identity {N : ℕ} (χ : DirichletCharacter ℂ N) {y u : ℝ} (hy : 1 ≤ y) (hu : y < u) :
    ((y * u / (u - y) : ℝ) : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ u / (u : ℂ) - Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ)) - psiChi χ y =
      ∑ n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) *
        ((y * u / (u - y) * (1 / n - 1 / u) : ℝ) : ℂ) := by
  have hy0 : 0 < y := by linarith
  have hu0 : 0 < u := by linarith
  have huy : u - y ≠ 0 := (sub_pos.mpr hu).ne'
  have hfl : ⌊y⌋₊ ≤ ⌊u⌋₊ := Nat.floor_mono hu.le
  rw [sharp_schi_div χ hu0, sharp_schi_div χ hy0, sharp_split _ hfl, Formalism.ZeroFreeDirichlet.psiChi.eq_1]
  have hc1 : y * u / (u - y) * (1 / y - 1 / u) = 1 := by
    field_simp
  have hAC : (∑ n ∈ Icc 1 ⌊y⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * ((1 / n - 1 / u : ℝ) : ℂ)) -
      ∑ n ∈ Icc 1 ⌊y⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * ((1 / n - 1 / y : ℝ) : ℂ) =
      ((1 / y - 1 / u : ℝ) : ℂ) * ∑ n ∈ Icc 1 ⌊y⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    push_cast
    ring
  have hE : ∑ n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) *
        ((y * u / (u - y) * (1 / n - 1 / u) : ℝ) : ℂ) =
      ((y * u / (u - y) : ℝ) : ℂ) *
        ∑ n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * ((1 / n - 1 / u : ℝ) : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    push_cast
    ring
  have hc1' : ((y * u / (u - y) : ℝ) : ℂ) * ((1 / y - 1 / u : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hc1, Complex.ofReal_one]
  rw [hE]
  linear_combination ((y * u / (u - y) : ℝ) : ℂ) * hAC +
    (∑ n ∈ Icc 1 ⌊y⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N)) * hc1'

lemma sharp_term {N : ℕ} (χ : DirichletCharacter ℂ N) {y u : ℝ} (hy : 1 ≤ y) (hu : y < u)
    {n : ℕ} (hn : n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊) :
    ‖((Λ n : ℝ) : ℂ) * χ (n : ZMod N) * ((y * u / (u - y) * (1 / n - 1 / u) : ℝ) : ℂ)‖ ≤
      Real.log u := by
  have hy0 : 0 < y := by linarith
  have hu0 : 0 < u := by linarith
  obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
  have hyn : y < n := (Nat.floor_lt hy0.le).mp hn1
  have hnu : (n : ℝ) ≤ u := (Nat.le_floor_iff hu0.le).mp hn2
  have hnpos : (0:ℝ) < n := by linarith
  have huy : 0 < u - y := by linarith
  have hf0 : 0 ≤ y * u / (u - y) * (1 / n - 1 / u) := by
    apply mul_nonneg (div_nonneg (by positivity) huy.le)
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le hnpos hnu
  have hf1 : y * u / (u - y) * (1 / n - 1 / u) ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one huy]
    have h1 : y * u * (1 / n - 1 / u) = y * u / n - y := by
      rw [mul_sub, mul_one_div, mul_one_div, mul_div_cancel_right₀ y hu0.ne']
    rw [h1]
    have h2 : y * u / n ≤ u := by
      rw [div_le_iff₀ hnpos]
      nlinarith
    linarith
  have hΛ0 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have hΛ : Λ n ≤ Real.log u :=
    ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hnpos hnu)
  have hχ : ‖χ (n : ZMod N)‖ ≤ 1 := DirichletCharacter.norm_le_one χ (n : ZMod N)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg hΛ0, ← abs_mul, abs_of_nonneg hf0]
  calc Λ n * ‖χ (n : ZMod N)‖ * (y * u / (u - y) * (1 / n - 1 / u)) ≤ Λ n * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hχ hΛ0) hf1 hf0 (mul_nonneg hΛ0 zero_le_one)
    _ = Λ n := by ring
    _ ≤ Real.log u := hΛ

theorem sharp_arith {N : ℕ} (χ : DirichletCharacter ℂ N) {y u : ℝ} (hy : 1 ≤ y) (hu : y < u) :
    ‖((y * u / (u - y) : ℝ) : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ u / (u : ℂ) - Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ)) - psiChi χ y‖ ≤
      (u - y + 1) * Real.log u := by
  rw [sharp_identity χ hy hu]
  have hu1 : 1 ≤ u := by linarith
  have hlog : 0 ≤ Real.log u := Real.log_nonneg hu1
  calc _ ≤ ∑ n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊, ‖((Λ n : ℝ) : ℂ) * χ (n : ZMod N) *
          ((y * u / (u - y) * (1 / n - 1 / u) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊, Real.log u := Finset.sum_le_sum (fun n hn => sharp_term χ hy hu hn)
    _ = ((⌊u⌋₊ - ⌊y⌋₊ : ℕ) : ℝ) * Real.log u := by
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
    _ ≤ (u - y + 1) * Real.log u := by
        apply mul_le_mul_of_nonneg_right _ hlog
        have h1 : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le (by linarith)
        have h2 : y < ⌊y⌋₊ + 1 := Nat.lt_floor_add_one y
        have h3 : ⌊y⌋₊ ≤ ⌊u⌋₊ := Nat.floor_mono hu.le
        rw [Nat.cast_sub h3]
        linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

lemma sharp_zero_term {ρ : ℂ} (h1 : 1 / 2 ≤ ρ.re) (h2 : ρ.re < 1) {y δ : ℝ} (hy : 0 < y) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) :
    ‖((y * ((1 + δ) / δ) : ℝ) : ℂ) * ((((1 + δ) * y : ℝ) : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)) -
        (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))) - (y : ℂ) ^ ρ / ρ‖ ≤ 2 * δ * y * y ^ (ρ.re - 1) := by
  have hρ0 : ρ ≠ 0 := by
    intro h; rw [h] at h1; norm_num at h1
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at h2; norm_num at h2
  have hs : ρ - 1 ≠ 0 := sub_ne_zero.2 hρ1
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hpow : (y : ℂ) ^ ρ = (y : ℂ) * (y : ℂ) ^ (ρ - 1) := by
    rw [Complex.cpow_sub _ _ hyc, Complex.cpow_one]; field_simp
  have e : ((y * ((1 + δ) / δ) : ℝ) : ℂ) * ((((1 + δ) * y : ℝ) : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)) -
        (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))) - (y : ℂ) ^ ρ / ρ =
      (y : ℂ) ^ ρ / ρ *
        ((((1 + δ) / δ : ℝ) : ℂ) * ((((1 + δ : ℝ) : ℂ) ^ (ρ - 1) - 1) / (ρ - 1)) - 1) := by
    rw [Complex.ofReal_mul (1 + δ) y, Complex.mul_cpow_ofReal_nonneg (by linarith) hy.le, hpow]
    generalize ((1 + δ : ℝ) : ℂ) ^ (ρ - 1) = a
    generalize (y : ℂ) ^ (ρ - 1) = b
    push_cast
    field_simp
  rw [e, norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have hk := sharp_kernel hρ0 hρ1 h2.le hδ hδ2
  have hn : 0 < ‖ρ‖ := norm_pos_iff.2 hρ0
  have hr : y ^ ρ.re = y * y ^ (ρ.re - 1) := by
    rw [Real.rpow_sub_one hy.ne']; field_simp
  calc y ^ ρ.re / ‖ρ‖ * _ ≤ y ^ ρ.re / ‖ρ‖ * (2 * δ * ‖ρ‖) :=
        mul_le_mul_of_nonneg_left hk (by positivity)
    _ = 2 * δ * y * y ^ (ρ.re - 1) := by rw [hr]; field_simp

lemma sharp_log_term {y δ : ℝ} (hy : 0 < y) (hδ : 0 < δ) :
    |y * ((1 + δ) / δ) * ((Real.log ((1 + δ) * y) - 1) - (Real.log y - 1)) - y| ≤ δ * y := by
  have h1 : (0 : ℝ) < 1 + δ := by linarith
  rw [Real.log_mul h1.ne' hy.ne']
  have hup : Real.log (1 + δ) ≤ δ := by
    have := Real.log_le_sub_one_of_pos h1; linarith
  have hlo : δ / (1 + δ) ≤ Real.log (1 + δ) := by
    have := Real.one_sub_inv_le_log_of_pos h1
    have e : 1 - (1 + δ)⁻¹ = δ / (1 + δ) := by field_simp; ring
    linarith
  have e : y * ((1 + δ) / δ) * ((Real.log (1 + δ) + Real.log y - 1) - (Real.log y - 1)) - y =
      y * ((1 + δ) / δ * Real.log (1 + δ) - 1) := by ring
  rw [e, abs_mul, abs_of_pos hy, mul_comm δ y]
  refine mul_le_mul_of_nonneg_left ?_ hy.le
  have hc : 0 < (1 + δ) / δ := by positivity
  rw [abs_le]
  constructor
  · have : (1 + δ) / δ * (δ / (1 + δ)) ≤ (1 + δ) / δ * Real.log (1 + δ) :=
      mul_le_mul_of_nonneg_left hlo hc.le
    have e2 : (1 + δ) / δ * (δ / (1 + δ)) = 1 := by field_simp
    linarith
  · have : (1 + δ) / δ * Real.log (1 + δ) ≤ (1 + δ) / δ * δ := mul_le_mul_of_nonneg_left hup hc.le
    have e2 : (1 + δ) / δ * δ = 1 + δ := by field_simp
    linarith

theorem differenced_explicit_formula : SharpenS := by
  intro M _ χ Z m K E y δ hZ hy hδ hδ2 hE
  have hy0 : 0 < y := by linarith
  have hEu := hE ((1 + δ) * y) (Or.inr rfl)
  have hEy := hE y (Or.inl rfl)
  have hE0 : 0 ≤ E := (norm_nonneg _).trans hEy
  have huy : y < (1 + δ) * y := by nlinarith
  have hR := sharp_arith χ (by linarith : (1 : ℝ) ≤ y) huy
  have hc : y * ((1 + δ) * y) / ((1 + δ) * y - y) = y * ((1 + δ) / δ) := by
    have : (1 + δ) * y - y = δ * y := by ring
    rw [this]; field_simp
  rw [hc] at hR
  set c : ℝ := y * ((1 + δ) / δ) with hcdef
  have hc0 : 0 < c := by positivity
  have hcle : c ≤ 3 / 2 * y / δ := by
    rw [hcdef, show y * ((1 + δ) / δ) = (1 + δ) * y / δ by ring]
    exact div_le_div_of_nonneg_right (by nlinarith) hδ.le
  set T : ℂ → ℂ := fun ρ => (c : ℂ) * ((((1 + δ) * y : ℝ) : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)) -
        (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))) - (y : ℂ) ^ ρ / ρ with hT
  have hsum : ∑ ρ ∈ Z, (m ρ : ℂ) * T ρ =
      (c : ℂ) * (∑ ρ ∈ Z, (m ρ : ℂ) * (((1 + δ) * y : ℝ) : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)) -
        ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))) -
        ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    simp only [hT]; ring
  have hTb : ‖∑ ρ ∈ Z, (m ρ : ℂ) * T ρ‖ ≤ 2 * δ * y * ∑ ρ ∈ Z, (m ρ : ℝ) * y ^ (ρ.re - 1) := by
    rw [Finset.mul_sum]
    refine norm_sum_le_of_le _ fun ρ hρ => ?_
    rw [norm_mul, Complex.norm_natCast]
    have := sharp_zero_term (hZ ρ hρ).1 (hZ ρ hρ).2 hy0 hδ hδ2
    calc (m ρ : ℝ) * ‖T ρ‖ ≤ (m ρ : ℝ) * (2 * δ * y * y ^ (ρ.re - 1)) :=
          mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
      _ = 2 * δ * y * ((m ρ : ℝ) * y ^ (ρ.re - 1)) := by ring
  have hS0 : 0 ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * y ^ (ρ.re - 1) :=
    Finset.sum_nonneg fun ρ _ => by positivity
  have hP : ‖(c : ℂ) * ((if χ = 1 then ((Real.log ((1 + δ) * y) - 1 : ℝ) : ℂ) else 0) -
      (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0)) - (if χ = 1 then (y : ℂ) else 0)‖ ≤ δ * y := by
    by_cases hχ : χ = 1
    · simp only [hχ, if_true]
      rw [← Complex.ofReal_sub, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]
      exact sharp_log_term hy0 hδ
    · simp only [hχ, if_false]
      simp; positivity
  have hlog1 : 1 ≤ Real.log (2 * y) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlogu : Real.log ((1 + δ) * y) ≤ Real.log (2 * y) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hD : ‖(c : ℂ) * ((Formalism.ZeroFreeDirichlet.Schi χ ((1 + δ) * y) / (((1 + δ) * y : ℝ) : ℂ) - K -
        (if χ = 1 then ((Real.log ((1 + δ) * y) - 1 : ℝ) : ℂ) else 0) +
          ∑ ρ ∈ Z, (m ρ : ℂ) * (((1 + δ) * y : ℝ) : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))) -
      (Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ) - K - (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0) +
                ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))))‖ ≤ c * (2 * E) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
    refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) hc0.le
    linarith
  have key : psiChi χ y - (if χ = 1 then (y : ℂ) else 0) + ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ =
      (c : ℂ) * ((Formalism.ZeroFreeDirichlet.Schi χ ((1 + δ) * y) / (((1 + δ) * y : ℝ) : ℂ) - K -
        (if χ = 1 then ((Real.log ((1 + δ) * y) - 1 : ℝ) : ℂ) else 0) +
          ∑ ρ ∈ Z, (m ρ : ℂ) * (((1 + δ) * y : ℝ) : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))) -
      (Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ) - K - (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0) +
                ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))))
      - ((c : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ ((1 + δ) * y) / (((1 + δ) * y : ℝ) : ℂ) - Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ)) - psiChi χ y)
      + ((c : ℂ) * ((if χ = 1 then ((Real.log ((1 + δ) * y) - 1 : ℝ) : ℂ) else 0) -
      (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0)) - (if χ = 1 then (y : ℂ) else 0))
      - ∑ ρ ∈ Z, (m ρ : ℂ) * T ρ := by
    rw [hsum]; ring
  rw [key]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
    (add_le_add hD hR)) hP)) hTb).trans ?_
  have b1 : c * (2 * E) ≤ 4 * y * E / δ := by
    calc c * (2 * E) ≤ 3 / 2 * y / δ * (2 * E) := mul_le_mul_of_nonneg_right hcle (by positivity)
      _ = 3 * y * E / δ := by ring
      _ ≤ 4 * y * E / δ := div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hy0.le hE0]) hδ.le
  have hdy : 0 < δ * y := by positivity
  have b2 : ((1 + δ) * y - y + 1) * Real.log ((1 + δ) * y) ≤ (δ * y + 1) * Real.log (2 * y) := by
    rw [show (1 + δ) * y - y + 1 = δ * y + 1 by ring]
    exact mul_le_mul_of_nonneg_left hlogu (by positivity)
  have b3 : δ * y ≤ (δ * y + 1) * Real.log (2 * y) := by nlinarith
  have b4 : 2 * δ * y * ∑ ρ ∈ Z, (m ρ : ℝ) * y ^ (ρ.re - 1) ≤
      20 * δ * y * ∑ ρ ∈ Z, (m ρ : ℝ) * y ^ (ρ.re - 1) :=
    mul_le_mul_of_nonneg_right (by nlinarith) hS0
  have b5 : 0 ≤ (δ * y + 1) * Real.log (2 * y) := by positivity
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section
noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem num_alg (M y C D Pt t lg lm : ℝ) (hM : 1 ≤ M) (hy : M ^ 5 ≤ y) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hPt : Pt ≤ (M ^ 8)⁻¹) (ht : t ≤ (M ^ 2)⁻¹) (hlg : lg ≤ D * M ^ 2)
    (hlm0 : 0 ≤ lm) (hlm : lm ≤ 13 * M) :
    M * (4 * y * (C * (Pt + lg * lm ^ 2 / M ^ 12)) / (M ^ 5)⁻¹ + 4 * ((M ^ 5)⁻¹ * y + 1) * lg)
        + 20 * (M ^ 5)⁻¹ * y + 2 * y * t ≤ (4 * C + 676 * C * D + 8 * D + 22) * y * (M ^ 2)⁻¹ := by
  have hM0 : 0 < M := by linarith
  have hy0 : 0 ≤ y := le_trans (by positivity) hy
  have hA : M ^ 6 * Pt ≤ (M ^ 2)⁻¹ := by
    calc M ^ 6 * Pt ≤ M ^ 6 * (M ^ 8)⁻¹ := mul_le_mul_of_nonneg_left hPt (by positivity)
      _ = (M ^ 2)⁻¹ := by field_simp
  have hB : lg * lm ^ 2 / M ^ 6 ≤ 169 * D * (M ^ 2)⁻¹ := by
    have hlm2 : lm ^ 2 ≤ 169 * M ^ 2 := by nlinarith
    have h2 : lg * lm ^ 2 ≤ D * M ^ 2 * (169 * M ^ 2) :=
      calc lg * lm ^ 2 ≤ D * M ^ 2 * lm ^ 2 := mul_le_mul_of_nonneg_right hlg (sq_nonneg _)
        _ ≤ D * M ^ 2 * (169 * M ^ 2) := mul_le_mul_of_nonneg_left hlm2 (by positivity)
    calc lg * lm ^ 2 / M ^ 6 ≤ D * M ^ 2 * (169 * M ^ 2) / M ^ 6 :=
          div_le_div_of_nonneg_right h2 (by positivity)
      _ = 169 * D * (M ^ 2)⁻¹ := by field_simp <;> ring
  have e1 : M * (4 * y * (C * (Pt + lg * lm ^ 2 / M ^ 12)) / (M ^ 5)⁻¹)
      = 4 * C * y * (M ^ 6 * Pt + lg * lm ^ 2 / M ^ 6) := by
    field_simp <;> ring
  have h1 : M * (4 * y * (C * (Pt + lg * lm ^ 2 / M ^ 12)) / (M ^ 5)⁻¹)
      ≤ 4 * C * y * ((M ^ 2)⁻¹ + 169 * D * (M ^ 2)⁻¹) := by
    rw [e1]; exact mul_le_mul_of_nonneg_left (add_le_add hA hB) (by positivity)
  have hM3 : M ^ 3 ≤ y * (M ^ 2)⁻¹ := by
    rw [le_mul_inv_iff₀ (by positivity)]; calc M ^ 3 * M ^ 2 = M ^ 5 := by ring
      _ ≤ y := hy
  have h2 : M * (4 * ((M ^ 5)⁻¹ * y + 1) * lg) ≤ 8 * D * y * (M ^ 2)⁻¹ := by
    have hc : 0 ≤ 4 * M * ((M ^ 5)⁻¹ * y + 1) := by positivity
    calc M * (4 * ((M ^ 5)⁻¹ * y + 1) * lg) = 4 * M * ((M ^ 5)⁻¹ * y + 1) * lg := by ring
      _ ≤ 4 * M * ((M ^ 5)⁻¹ * y + 1) * (D * M ^ 2) := mul_le_mul_of_nonneg_left hlg hc
      _ = 4 * D * (y * (M ^ 2)⁻¹ + M ^ 3) := by field_simp <;> ring
      _ ≤ 4 * D * (y * (M ^ 2)⁻¹ + y * (M ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 8 * D * y * (M ^ 2)⁻¹ := by ring
  have h5 : (M ^ 5)⁻¹ ≤ (M ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hM (by norm_num))
  have h3 : 20 * (M ^ 5)⁻¹ * y ≤ 20 * (M ^ 2)⁻¹ * y := by
    have := mul_le_mul_of_nonneg_right h5 hy0; linarith
  have h4 : 2 * y * t ≤ 2 * y * (M ^ 2)⁻¹ := mul_le_mul_of_nonneg_left ht (by positivity)
  have e2 : M * (4 * y * (C * (Pt + lg * lm ^ 2 / M ^ 12)) / (M ^ 5)⁻¹ + 4 * ((M ^ 5)⁻¹ * y + 1) * lg)
      = M * (4 * y * (C * (Pt + lg * lm ^ 2 / M ^ 12)) / (M ^ 5)⁻¹)
        + M * (4 * ((M ^ 5)⁻¹ * y + 1) * lg) := by ring
  rw [e2]
  have e3 : (4 * C + 676 * C * D + 8 * D + 22) * y * (M ^ 2)⁻¹
      = 4 * C * y * ((M ^ 2)⁻¹ + 169 * D * (M ^ 2)⁻¹) + 8 * D * y * (M ^ 2)⁻¹
        + 20 * (M ^ 2)⁻¹ * y + 2 * y * (M ^ 2)⁻¹ := by ring
  rw [e3]
  linarith

theorem one_le_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  have h3 : Real.exp 1 ≤ x := by linarith [Real.exp_one_lt_d9]
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 1) h3

theorem inv_pow_eq_exp {M : ℝ} (hM : 0 < M) (n : ℕ) : (M ^ n)⁻¹ = Real.exp (-(n * Real.log M)) := by
  rw [Real.exp_neg, ← Real.log_pow, Real.exp_log (pow_pos hM n)]

theorem logy_lt {cA M y : ℝ} (hcA : 0 < cA) (hy : 2 ≤ y)
    (h : cA * Real.sqrt (Real.log y) < Real.log M) : cA ^ 2 * Real.log y < Real.log M ^ 2 := by
  have hl : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hs := Real.sq_sqrt hl
  have h0 : 0 ≤ cA * Real.sqrt (Real.log y) := by positivity
  have h2 : (cA * Real.sqrt (Real.log y)) ^ 2 < Real.log M ^ 2 := by nlinarith
  calc cA ^ 2 * Real.log y = (cA * Real.sqrt (Real.log y)) ^ 2 := by rw [mul_pow, hs]
    _ < Real.log M ^ 2 := h2

theorem inv_le_exp {cA c M y : ℝ} (hcA : 0 < cA) (hc : 0 < c) (hc' : c ≤ cA ^ 2) (hM : 8 ≤ M) (hy : 2 ≤ y)
    (h : cA * Real.sqrt (Real.log y) < Real.log M) :
    M⁻¹ ≤ Real.exp (-(c * Real.log y / Real.log M)) := by
  have hM0 : 0 < M := by linarith
  have hlM : 0 < Real.log M := Real.log_pos (by linarith)
  have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have h2 := logy_lt hcA hy h
  have h3 : c * Real.log y ≤ Real.log M ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hc' hly]
  have h4 : c * Real.log y / Real.log M ≤ Real.log M := by
    rw [div_le_iff₀ hlM]; nlinarith
  calc M⁻¹ = Real.exp (-Real.log M) := by rw [Real.exp_neg, Real.exp_log hM0]
    _ ≤ Real.exp (-(c * Real.log y / Real.log M)) := Real.exp_le_exp.mpr (by linarith)

theorem num_main (cA κ C : ℝ) (hcA : 0 < cA) (hκ : 0 < κ) (hC : 0 < C) :
    ∃ C₀ B : ℝ, 0 ≤ C₀ ∧ 0 ≤ B ∧ ∀ M y : ℝ, 8 ≤ M → 2 ≤ y →
      C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y →
      cA * Real.sqrt (Real.log y) < Real.log M →
      M * (4 * y * (C * ((M * M ^ (12 : ℝ)) ^ C * y ^ (-(κ / 2))
          + Real.log (2 * y) * Real.log (M * M ^ (12 : ℝ)) ^ 2 / M ^ (12 : ℝ))) / (M ^ 5)⁻¹
          + 4 * ((M ^ 5)⁻¹ * y + 1) * Real.log (2 * y))
        + 20 * (M ^ 5)⁻¹ * y + 2 * y * y ^ (-(κ / 2)) ≤ B * y * (M⁻¹ * M⁻¹) := by
  set D : ℝ := 1 + (cA ^ 2)⁻¹ with hDdef
  have hD : 0 ≤ D := by positivity
  refine ⟨5 + (26 * C + 20) / κ, 4 * C + 676 * C * D + 8 * D + 22, by positivity, by positivity, ?_⟩
  intro M y hM hy hlog hsq
  have hM0 : 0 < M := by linarith
  have hy0 : 0 < y := by linarith
  have hL1 : 1 ≤ Real.log M := one_le_log_of_three_le (by linarith)
  have hl1 : 1 ≤ Real.log (Real.log M + 2) := one_le_log_of_three_le (by linarith)
  have hLM : Real.log M ≤ M := by linarith [Real.log_le_sub_one_of_pos hM0]
  have hC0 : 0 ≤ 5 + (26 * C + 20) / κ := by positivity
  have hlog' : (5 + (26 * C + 20) / κ) * Real.log M ≤ Real.log y := by
    have : (5 + (26 * C + 20) / κ) * Real.log M * 1
        ≤ (5 + (26 * C + 20) / κ) * Real.log M * Real.log (Real.log M + 2) :=
      mul_le_mul_of_nonneg_left hl1 (by positivity)
    linarith
  have hkC : κ * (5 + (26 * C + 20) / κ) = 5 * κ + (26 * C + 20) := by field_simp
  have hK : (26 * C + 20) * Real.log M ≤ κ * Real.log y := by
    have := mul_le_mul_of_nonneg_left hlog' hκ.le
    have h5 : 0 ≤ 5 * κ * Real.log M := by positivity
    nlinarith
  have hy5 : M ^ 5 ≤ y := by
    rw [← Real.log_le_log_iff (by positivity) hy0, Real.log_pow]
    have : 5 * Real.log M ≤ (5 + (26 * C + 20) / κ) * Real.log M := by
      have : 0 ≤ (26 * C + 20) / κ * Real.log M := by positivity
      nlinarith
    push_cast; linarith
  have h12 : M ^ (12 : ℝ) = M ^ 12 := by
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h12]
  have hlm : Real.log (M * M ^ 12) = 13 * Real.log M := by
    rw [show M * M ^ 12 = M ^ 13 by ring, Real.log_pow]; push_cast; ring
  have hpow : (M * M ^ 12) ^ C = Real.exp (13 * C * Real.log M) := by
    rw [Real.rpow_def_of_pos (by positivity), hlm]; ring_nf
  have hyk : y ^ (-(κ / 2)) = Real.exp (-(κ / 2 * Real.log y)) := by
    rw [Real.rpow_def_of_pos hy0]; ring_nf
  have hPt : (M * M ^ 12) ^ C * y ^ (-(κ / 2)) ≤ (M ^ 8)⁻¹ := by
    rw [hpow, hyk, ← Real.exp_add, inv_pow_eq_exp hM0]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  have ht : y ^ (-(κ / 2)) ≤ (M ^ 2)⁻¹ := by
    rw [hyk, inv_pow_eq_exp hM0]
    apply Real.exp_le_exp.mpr
    push_cast
    have : 0 ≤ 26 * C * Real.log M := by positivity
    nlinarith
  have hlg : Real.log (2 * y) ≤ D * M ^ 2 := by
    have hq := logy_lt hcA hy hsq
    have hq' : Real.log y ≤ Real.log M ^ 2 * (cA ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ (by positivity)]; linarith
    have hLM2 : Real.log M ^ 2 ≤ M ^ 2 := by nlinarith
    have hq'' : Real.log M ^ 2 * (cA ^ 2)⁻¹ ≤ M ^ 2 * (cA ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right hLM2 (by positivity)
    have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
    have hM1 : 1 ≤ M ^ 2 := by nlinarith
    rw [Real.log_mul (by norm_num) hy0.ne', hDdef]
    nlinarith
  have hlm0 : 0 ≤ Real.log (M * M ^ 12) := by rw [hlm]; linarith
  have hlm13 : Real.log (M * M ^ 12) ≤ 13 * M := by rw [hlm]; linarith
  have key := num_alg M y C D ((M * M ^ 12) ^ C * y ^ (-(κ / 2))) (y ^ (-(κ / 2)))
    (Real.log (2 * y)) (Real.log (M * M ^ 12)) (by linarith) hy5 hC.le hD hPt ht hlg hlm0 hlm13
  refine key.trans (le_of_eq ?_)
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

def excI {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M) : ℝ :=
  match e with
  | none => 0
  | some (χ₁, _) => if χ = χ₁ then 1 else 0

def excT {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M) (y : ℝ) : ℂ :=
  match e with
  | none => 0
  | some (χ₁, β₁) => if χ = χ₁ then (y : ℂ) ^ (β₁ : ℂ) / (β₁ : ℂ) else 0

theorem mainPsi_eq {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M) (y : ℝ) :
    mainPsi e χ y = (if χ = 1 then (y : ℂ) else 0) - excT e χ y := rfl


theorem sum_excI_le {M : ℕ} [NeZero M] (e : Option (DirichletCharacter ℂ M × ℝ)) :
    ∑ χ : DirichletCharacter ℂ M, excI e χ ≤ 1 := by
  rcases e with _ | ⟨χ₁, β₁⟩
  · simp [excI]
  · have h : (∑ χ : DirichletCharacter ℂ M, excI (some (χ₁, β₁)) χ) = excI (some (χ₁, β₁)) χ₁ :=
      Finset.sum_eq_single χ₁ (fun b _ hb => if_neg hb) (fun h => absurd (Finset.mem_univ _) h)
    rw [h]
    exact (if_pos rfl).le

theorem excW_le_one {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M) (ρ : ℂ) :
    excW e χ ρ ≤ 1 := by
  rcases e with _ | ⟨χ₁, β₁⟩
  · simp [excW]
  · simp only [excW]; split_ifs <;> norm_num

theorem card_char_le (M : ℕ) [NeZero M] :
    ((Finset.univ : Finset (DirichletCharacter ℂ M)).card : ℝ) ≤ M := by
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ M]
  exact_mod_cast Nat.totient_le M

theorem sum_excW_le {M : ℕ} (e : Option (DirichletCharacter ℂ M × ℝ)) (χ : DirichletCharacter ℂ M)
    (Z : Finset ℂ) (y : ℝ) (hy : 1 ≤ y) (hZ : ∀ ρ ∈ Z, ρ.re < 1) :
    ∑ ρ ∈ Z, (excW e χ ρ : ℝ) * y ^ (ρ.re - 1) ≤ excI e χ := by
  rcases e with _ | ⟨χ₁, β₁⟩
  · simp [excW, excI]
  · simp only [excW, excI]
    by_cases h : χ = χ₁
    · simp only [h, true_and, if_true]
      have : ∀ ρ ∈ Z, (((if ρ = (β₁ : ℂ) then 1 else 0 : ℕ) : ℝ)) * y ^ (ρ.re - 1)
          = if ρ = (β₁ : ℂ) then y ^ (ρ.re - 1) else 0 := by
        intro ρ _; split_ifs <;> simp
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
      split_ifs with hm
      · exact Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith [hZ _ hm])
      · norm_num
    · simp [h]

theorem excT_sub_le {M : ℕ} [NeZero M] (hM : 3 ≤ M) (e : Option (DirichletCharacter ℂ M × ℝ))
    (he : ∀ p, e = some p → IsExcPair p.1 p.2) (χ : DirichletCharacter ℂ M)
    (Z : Finset ℂ) (y κ T : ℝ) (hy : 1 ≤ y) (hT : 0 ≤ T)
    (hZ : ∀ ρ : ℂ, IsLZero χ ρ → 1 - κ / 2 ≤ ρ.re → |ρ.im| ≤ T → ρ ∈ Z) :
    ‖excT e χ y - ∑ ρ ∈ Z, (excW e χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖ ≤ excI e χ * (2 * y * y ^ (-(κ / 2))) := by
  rcases e with _ | ⟨χ₁, β₁⟩
  · simp [excW, excI, excT]
  · obtain ⟨-, hne, hz, hlo, hhi⟩ := he _ rfl
    simp only at hne hz hlo hhi
    simp only [excW, excI, excT]
    by_cases h : χ = χ₁
    · subst h
      simp only [true_and, if_true]
      have : ∀ ρ ∈ Z, (((if ρ = (β₁ : ℂ) then 1 else 0 : ℕ) : ℂ)) * (y : ℂ) ^ ρ / ρ
          = if ρ = (β₁ : ℂ) then (y : ℂ) ^ ρ / ρ else 0 := by
        intro ρ _; split_ifs <;> simp
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
      have hy0 : 0 < y := by linarith
      split_ifs with hm
      · simp only [sub_self, norm_zero, one_mul]; positivity
      · have hb : β₁ < 1 - κ / 2 := by
          by_contra hcon
          push Not at hcon
          exact hm (hZ _ ⟨Or.inl hne, hz⟩ (by simpa using hcon) (by simpa using hT))
        have hl : 1 ≤ Real.log M := by
          rw [Real.le_log_iff_exp_le (by positivity)]
          have : (3 : ℝ) ≤ M := by exact_mod_cast hM
          linarith [Real.exp_one_lt_d9]
        have hb2 : 1 / 2 ≤ β₁ := by
          have : 1 / (8 * Real.log M) ≤ 1 / 8 := by
            apply one_div_le_one_div_of_le (by norm_num); linarith
          linarith
        rw [sub_zero, one_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.ofReal_re,
          Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        have h1 : y ^ β₁ ≤ y ^ (1 - κ / 2) := Real.rpow_le_rpow_of_exponent_le hy hb.le
        have h2 : y ^ (1 - κ / 2) = y * y ^ (-(κ / 2)) := by
          rw [sub_eq_add_neg, Real.rpow_add hy0, Real.rpow_one]
        rw [div_le_iff₀ (by linarith)]
        have h3 : 0 ≤ y * y ^ (-(κ / 2)) := by positivity
        nlinarith
    · simp [h]

theorem one_char {M : ℕ} [NeZero M] (hM : 3 ≤ M) (e : Option (DirichletCharacter ℂ M × ℝ))
    (he : ∀ p, e = some p → IsExcPair p.1 p.2) (χ : DirichletCharacter ℂ M)
    (Z : Finset ℂ) (m : ℂ → ℕ) (y κ T R : ℝ) (hy : 1 ≤ y) (hT : 0 ≤ T)
    (hZ : ∀ ρ : ℂ, IsLZero χ ρ → 1 - κ / 2 ≤ ρ.re → |ρ.im| ≤ T → ρ ∈ Z)
    (hre : ∀ ρ ∈ Z, 1 / 2 ≤ ρ.re) (hm : ∀ ρ ∈ Z, 1 ≤ m ρ)
    (hR : ‖psiChi χ y - (if χ = 1 then (y : ℂ) else 0) + ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖ ≤ R) :
    ‖psiChi χ y - mainPsi e χ y‖ ≤
      R + 2 * y * ∑ ρ ∈ Z, ((m ρ : ℝ) - (excW e χ ρ : ℝ)) * y ^ (ρ.re - 1)
        + excI e χ * (2 * y * y ^ (-(κ / 2))) := by
  have hy0 : 0 < y := by linarith
  have e1 : psiChi χ y - mainPsi e χ y
      = (psiChi χ y - (if χ = 1 then (y : ℂ) else 0) + ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ)
        - ∑ ρ ∈ Z, ((m ρ : ℂ) - (excW e χ ρ : ℂ)) * (y : ℂ) ^ ρ / ρ
        + (excT e χ y - ∑ ρ ∈ Z, (excW e χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ) := by
    rw [mainPsi_eq]
    have : ∑ ρ ∈ Z, ((m ρ : ℂ) - (excW e χ ρ : ℂ)) * (y : ℂ) ^ ρ / ρ
        = ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ ρ / ρ - ∑ ρ ∈ Z, (excW e χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun ρ _ => by ring)
    rw [this]
    by_cases hχ : χ = 1
    · simp only [if_pos hχ]; ring
    · simp only [if_neg hχ]; ring
  have h2 : ‖∑ ρ ∈ Z, ((m ρ : ℂ) - (excW e χ ρ : ℂ)) * (y : ℂ) ^ ρ / ρ‖
      ≤ 2 * y * ∑ ρ ∈ Z, ((m ρ : ℝ) - (excW e χ ρ : ℝ)) * y ^ (ρ.re - 1) := by
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro ρ hρ
    have hw : (0 : ℝ) ≤ (m ρ : ℝ) - (excW e χ ρ : ℝ) := by
      have : ((excW e χ ρ : ℕ) : ℝ) ≤ (m ρ : ℝ) := by exact_mod_cast (excW_le_one e χ ρ).trans (hm ρ hρ)
      linarith
    have hn : ‖(m ρ : ℂ) - (excW e χ ρ : ℂ)‖ = (m ρ : ℝ) - (excW e χ ρ : ℝ) := by
      have : (m ρ : ℂ) - (excW e χ ρ : ℂ) = (((m ρ : ℝ) - (excW e χ ρ : ℝ) : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.norm_real, Real.norm_of_nonneg hw]
    have hρn : 1 / 2 ≤ ‖ρ‖ := (hre ρ hρ).trans ((le_abs_self _).trans (Complex.abs_re_le_norm ρ))
    rw [norm_div, norm_mul, hn, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    have h3 : y ^ ρ.re = y * y ^ (ρ.re - 1) := by
      rw [Real.rpow_sub hy0, Real.rpow_one]; field_simp
    rw [div_le_iff₀ (by linarith), h3]
    have h4 : 0 ≤ ((m ρ : ℝ) - (excW e χ ρ : ℝ)) * (y * y ^ (ρ.re - 1)) := by positivity
    nlinarith
  rw [e1]
  refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add hR h2)) ?_)
  exact excT_sub_le hM e he χ Z y κ T hy hT hZ

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

set_option maxHeartbeats 400000 in

theorem psi_relative_far_range : PsiRelBOf := by
  intro hE hS hZS cA hcA
  obtain ⟨κ, hκ, hκ', hZ⟩ := hZS
  obtain ⟨C, hC, hEx⟩ := hE κ hκ hκ'
  obtain ⟨cz, Az, Cz, hcz, hZ⟩ := hZ C 12 (by norm_num)
  obtain ⟨C₀, B, hC₀, hB, hnum⟩ := num_main cA κ C hcA hκ hC
  obtain ⟨c₁, hc₁, heta⟩ := etaOf_lower 1 one_pos
  refine ⟨min cz (cA ^ 2), 22 * |Az| + B / c₁, max Cz C₀, lt_min hcz (by positivity), ?_⟩
  intro M _ h8 y hy hr1 hr2
  have hM8 : 8 ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h8
  have hM8r : (8 : ℝ) ≤ M := by exact_mod_cast hM8
  have hM3 : 3 ≤ M := by omega
  have hM0 : (0 : ℝ) < M := by linarith
  have hy0 : 0 < y := by linarith
  have hT8 : (8 : ℝ) ≤ (M : ℝ) ^ (12 : ℝ) := by
    calc (8 : ℝ) ≤ (M : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]; exact hM8r
      _ ≤ (M : ℝ) ^ (12 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hδ0 : 0 < ((M : ℝ) ^ 5)⁻¹ := by positivity
  have hδ : ((M : ℝ) ^ 5)⁻¹ ≤ 1 / 2 := by
    rw [one_div]
    apply inv_anti₀ (by norm_num)
    calc (2 : ℝ) ≤ (M : ℝ) ^ 1 := by rw [pow_one]; linarith
      _ ≤ (M : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
  choose Z m K h1 h2 h3 h4 h5 h6 using fun χ => hEx M χ ((M : ℝ) ^ (12 : ℝ)) hM3 (by linarith)
  have hl : 1 ≤ Real.log M := one_le_log_of_three_le (by linarith)
  have hll : 1 ≤ Real.log (Real.log M + 2) := one_le_log_of_three_le (by linarith)
  have hL : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hrz : Cz * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y := by
    refine le_trans ?_ hr1
    have : Cz ≤ max Cz C₀ := le_max_left _ _
    gcongr
  have hrn : C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y := by
    refine le_trans ?_ hr1
    have : C₀ ≤ max Cz C₀ := le_max_right _ _
    gcongr
  have hZS := hZ M Z m h8 h1 h3 h4 h5 y hy hrz
  have hN := hnum M y hM8r hy hrn hr2
  generalize hTdef : (M : ℝ) ^ (12 : ℝ) = T at *
  generalize hδdef : ((M : ℝ) ^ 5)⁻¹ = δ at *
  generalize htdef : y ^ (-(κ / 2)) = t at *
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = C * (((M : ℝ) * T) ^ C * t
      + Real.log (2 * y) * Real.log ((M : ℝ) * T) ^ 2 / T) := ⟨_, rfl⟩
  rw [← hEdef] at hN
  have hT0 : 0 < T := by linarith
  have ht0 : 0 ≤ t := by rw [← htdef]; positivity
  have hlg : 0 ≤ Real.log (2 * y) := Real.log_nonneg (by linarith)
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hre : ∀ χ, ∀ ρ ∈ Z χ, 1 / 2 ≤ ρ.re ∧ ρ.re < 1 := by
    intro χ ρ hρ
    obtain ⟨hz, hlo, -⟩ := h1 χ ρ hρ
    refine ⟨by linarith, ?_⟩
    by_contra hcon
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hz.1 (not_lt.1 hcon) hz.2
  have hEu : ∀ u : ℝ, y ≤ u → u ≤ 2 * y →
      C * (((M : ℝ) * T) ^ C * u ^ (-(κ / 2)) + Real.log u * Real.log ((M : ℝ) * T) ^ 2 / T) ≤ E := by
    intro u hu1 hu2
    rw [hEdef]
    have a1 : u ^ (-(κ / 2)) ≤ t := by
      rw [← htdef]; exact Real.rpow_le_rpow_of_nonpos hy0 hu1 (by linarith)
    have a2 : Real.log u ≤ Real.log (2 * y) := Real.log_le_log (by linarith) hu2
    gcongr
  have hsharp : ∀ χ : DirichletCharacter ℂ M,
      ‖psiChi χ y - (if χ = 1 then (y : ℂ) else 0) + ∑ ρ ∈ Z χ, (m χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖ ≤
      4 * y * E / δ + 20 * δ * y * ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1)
        + 4 * (δ * y + 1) * Real.log (2 * y) := by
    intro χ
    refine hS M χ (Z χ) (m χ) (K χ) E y δ (hre χ) hy hδ0 hδ ?_
    intro u hu
    have hu1 : y ≤ u := by
      rcases hu with rfl | rfl
      · exact le_rfl
      · nlinarith
    have hu2 : u ≤ 2 * y := by
      rcases hu with rfl | rfl
      · linarith
      · nlinarith
    exact (h6 χ u (by linarith)).trans (hEu u hu1 hu2)
  obtain ⟨W, hW⟩ : ∃ W : DirichletCharacter ℂ M → ℝ, W = fun χ =>
      ∑ ρ ∈ Z χ, ((m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ)) * y ^ (ρ.re - 1) := ⟨_, rfl⟩
  have hW0 : ∀ χ, 0 ≤ W χ := by
    intro χ
    rw [hW]
    apply Finset.sum_nonneg
    intro ρ hρ
    have : ((excW (eOf M) χ ρ : ℕ) : ℝ) ≤ (m χ ρ : ℝ) := by
      exact_mod_cast (excW_le_one (eOf M) χ ρ).trans (h3 χ ρ hρ)
    have h0 : (0 : ℝ) ≤ (m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ) := by linarith
    positivity
  have hmW : ∀ χ, ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1) ≤ W χ + excI (eOf M) χ := by
    intro χ
    have := sum_excW_le (eOf M) χ (Z χ) y (by linarith) (fun ρ hρ => (hre χ ρ hρ).2)
    have e : ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1)
        = W χ + ∑ ρ ∈ Z χ, (excW (eOf M) χ ρ : ℝ) * y ^ (ρ.re - 1) := by
      rw [hW, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun ρ _ => by ring)
    linarith
  have hper : ∀ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      (4 * y * E / δ + 4 * (δ * y + 1) * Real.log (2 * y)) + 22 * y * W χ
        + excI (eOf M) χ * (20 * δ * y + 2 * y * t) := by
    intro χ
    have a := one_char hM3 (eOf M) (fun p hp => eOf_exc M p hp) χ (Z χ) (m χ) y κ T _ (by linarith)
      hT0.le (h2 χ) (fun ρ hρ => (hre χ ρ hρ).1) (h3 χ) (hsharp χ)
    rw [htdef] at a
    have a' : ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
        4 * y * E / δ + 20 * δ * y * ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1)
        + 4 * (δ * y + 1) * Real.log (2 * y) + 2 * y * W χ + excI (eOf M) χ * (2 * y * t) := by
      rw [hW]; exact a
    have b : 20 * δ * y * ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1)
        ≤ 20 * δ * y * (W χ + excI (eOf M) χ) := mul_le_mul_of_nonneg_left (hmW χ) (by positivity)
    have c : 20 * δ * y * W χ ≤ 20 * y * W χ := by
      have : 0 ≤ y * W χ := mul_nonneg hy0.le (hW0 χ)
      nlinarith
    linarith
  have hsum : ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      (M : ℝ) * (4 * y * E / δ + 4 * (δ * y + 1) * Real.log (2 * y)) + 22 * y * ∑ χ, W χ
        + (20 * δ * y + 2 * y * t) := by
    refine (Finset.sum_le_sum (fun χ _ => hper χ)).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.sum_mul]
    have q0 : 0 ≤ 4 * y * E / δ + 4 * (δ * y + 1) * Real.log (2 * y) := by positivity
    have q1 : 0 ≤ 20 * δ * y + 2 * y * t := by positivity
    have r1 := mul_le_mul_of_nonneg_right (card_char_le M) q0
    have r2 := mul_le_mul_of_nonneg_right (sum_excI_le (eOf M)) q1
    linarith
  have hη0 : 0 < etaOf M := etaOf_pos M (by omega)
  have hex := inv_le_exp hcA (lt_min hcz (by positivity : 0 < cA ^ 2)) (min_le_right _ _) hM8r hy hr2
  have hηM : (M : ℝ)⁻¹ ≤ etaOf M / c₁ := by
    have := heta M hM3
    rw [Real.rpow_neg_one] at this
    rw [le_div_iff₀ hc₁]; linarith
  have hMi : 0 < (M : ℝ)⁻¹ := by positivity
  have hWs : ∑ χ, W χ ≤ |Az| * etaOf M * Real.exp (-(min cz (cA ^ 2) * Real.log y / Real.log M)) := by
    rw [hW]
    refine hZS.trans ?_
    have e1 : Real.exp (-(cz * Real.log y / Real.log M))
        ≤ Real.exp (-(min cz (cA ^ 2) * Real.log y / Real.log M)) := by
      apply Real.exp_le_exp.2
      apply neg_le_neg
      have : min cz (cA ^ 2) ≤ cz := min_le_left _ _
      gcongr
    have e2 : Az ≤ |Az| := le_abs_self _
    gcongr
  have hfin : B * y * ((M : ℝ)⁻¹ * (M : ℝ)⁻¹)
      ≤ B * y * (etaOf M / c₁ * Real.exp (-(min cz (cA ^ 2) * Real.log y / Real.log M))) := by
    gcongr
  generalize Real.exp (-(min cz (cA ^ 2) * Real.log y / Real.log M)) = ex at *
  have f1 : 22 * y * ∑ χ, W χ ≤ 22 * y * (|Az| * etaOf M * ex) :=
    mul_le_mul_of_nonneg_left hWs (by positivity)
  have f2 : (22 * |Az| + B / c₁) * y * etaOf M * ex
      = 22 * y * (|Az| * etaOf M * ex) + B * y * (etaOf M / c₁ * ex) := by ring
  rw [f2]
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem pow_absorb (N : ℕ) (c l large₂ : ℝ) (hc : 0 < c) (hl : 2 ≤ l)
    (hL : 2 * N / c * l * Real.log (l + 2) ≤ large₂) :
    l ^ N * Real.exp (-(c / 2 * large₂ / l)) ≤ 1 := by
  have hl0 : 0 < l := by linarith
  have hpow : Real.exp (N * Real.log l) = l ^ N := by
    rw [← Real.log_pow, Real.exp_log (pow_pos hl0 N)]
  have key : (N : ℝ) * Real.log l ≤ c / 2 * large₂ / l := by
    rw [le_div_iff₀ hl0]
    have hlog : Real.log l ≤ Real.log (l + 2) := Real.log_le_log hl0 (by linarith)
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    calc (N : ℝ) * Real.log l * l ≤ N * Real.log (l + 2) * l := by gcongr
      _ = c / 2 * (2 * N / c * l * Real.log (l + 2)) := by field_simp
      _ ≤ c / 2 * large₂ := by gcongr
  calc l ^ N * Real.exp (-(c / 2 * large₂ / l))
      = Real.exp (N * Real.log l + -(c / 2 * large₂ / l)) := by rw [Real.exp_add, hpow]
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

theorem zero_sum_bound_lossy : ZeroSumOfB := by
  intro hLD hDH
  obtain ⟨a, B, C, ha, hB, hC, hdens⟩ := density_norm hLD
  obtain ⟨c₀, c₁, c₂, N, hc₀, hc₁, hc₂, hdh⟩ := hDH
  refine ⟨min c₀ (1 / 20), lt_min hc₀ (by norm_num), min_le_right _ _, ?_⟩
  intro C₁ A₁ hA₁
  have hk : 0 < A₁ + 2 := by linarith
  have hcZ := cZ_pos
  have hcZ' := cZ_le
  set η0 : ℝ := min (cZ / 2) (c₁ / (A₁ + 2)) with hη0
  have hη0pos : 0 < η0 := lt_min (by linarith) (by positivity)
  have hη0a : η0 ≤ cZ / 2 := min_le_left _ _
  have hη0b : η0 ≤ c₁ / (A₁ + 2) := min_le_right _ _
  have hη0c : η0 ≤ c₁ := hη0b.trans (div_le_self hc₁.le (by linarith))
  have hη01 : η0 ≤ 1 := by linarith
  set A' : ℝ := 4 * |C₁| * C * Real.exp (a + a * cZ / 2) * (A₁ + 2) ^ (B + 1) with hA'
  have hA'0 : 0 ≤ A' := by
    have h1 : 0 ≤ (A₁ + 2) ^ (B + 1) := Real.rpow_nonneg hk.le _
    have h2 : 0 ≤ C := by linarith
    positivity
  set c : ℝ := cZ / (4 * (A₁ + 2)) with hc
  have hc0 : 0 < c := by positivity
  set K0 : ℝ := (A₁ + 2) * (a + 1 + 2 / c₂) + (B + 1) / c with hK0
  have hK00 : 0 ≤ K0 := by
    have h1 : 0 ≤ a + 1 + 2 / c₂ := by positivity
    have h2 : 0 ≤ (B + 1) / c := by positivity
    positivity
  refine ⟨c / 2, A' * (A₁ + 2) ^ N / η0, K0 + 2 * N / c, by positivity, ?_⟩
  intro M _ Z m h8 hZ _ hms hwin y hy hL
  have hM8 : 8 ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h8
  have hM8' : (8 : ℝ) ≤ M := by exact_mod_cast hM8
  have hM0 : (0 : ℝ) < M := by linarith
  have hpw : 0 < (M : ℝ) ^ A₁ := Real.rpow_pos_of_pos hM0 _
  obtain ⟨hl2, hlℓ, hℓk⟩ := ell_bounds M hM8 A₁ hA₁
  set ℓ : ℝ := Real.log ((M : ℝ) * ((M : ℝ) ^ A₁ + 3)) with hℓ
  have hℓ0 : 0 < ℓ := by linarith
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hℓN : 1 ≤ ℓ ^ N := one_le_pow₀ hℓ1
  have hll : 0 ≤ Real.log M * Real.log (Real.log M + 2) :=
    mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
  have hL1 : K0 * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y := by
    have : 0 ≤ 2 * N / c * (Real.log M * Real.log (Real.log M + 2)) :=
      mul_nonneg (by positivity) hll
    nlinarith
  have hL2 : 2 * N / c * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y := by
    have : 0 ≤ K0 * (Real.log M * Real.log (Real.log M + 2)) := mul_nonneg hK00 hll
    nlinarith
  have habs := pow_absorb N c (Real.log M) (Real.log y) hc0 hl2 hL2
  suffices h : ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ η0 * θ ≤ etaOf M * ℓ ^ N ∧
      (∀ χ, ∀ ρ ∈ Z χ, ¬ InRegion cZ M ρ → c₂ * Real.log (1 / θ) ≤ ℓ * (1 - ρ.re)) by
    obtain ⟨θ, h0, h1, hη, hθ⟩ := h
    have key := zeroSum_core a B C ha hB hC hdens (min c₀ (1 / 20)) c₂ C₁ A₁ (min_le_right _ _) hc₂ hA₁
      M Z m h8 hZ hms hwin y hy hL1 θ h0 h1 hθ
    refine key.trans ?_
    have hηpos : 0 < etaOf M := etaOf_pos M (by omega)
    set E : ℝ := Real.exp (-(c / 2 * Real.log y / Real.log M)) with hE
    have hE0 : 0 < E := Real.exp_pos _
    have hEE : Real.exp (-(c * Real.log y / Real.log M)) = E * E := by
      rw [hE, ← Real.exp_add]
      congr 1
      ring
    rw [hEE]
    have hpow : ℓ ^ N ≤ (A₁ + 2) ^ N * Real.log M ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hℓ0.le hℓk N
    have hθle : θ ≤ etaOf M * ((A₁ + 2) ^ N * Real.log M ^ N) / η0 := by
      rw [le_div_iff₀ hη0pos]
      calc θ * η0 = η0 * θ := by ring
        _ ≤ etaOf M * ℓ ^ N := hη
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow hηpos.le
    have hkN : 0 ≤ (A₁ + 2) ^ N := by positivity
    calc A' * θ * (E * E)
        ≤ A' * (etaOf M * ((A₁ + 2) ^ N * Real.log M ^ N) / η0) * (E * E) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hθle hA'0
      _ = (A' * (A₁ + 2) ^ N / η0 * etaOf M * E) * (Real.log M ^ N * E) := by ring
      _ ≤ (A' * (A₁ + 2) ^ N / η0 * etaOf M * E) * 1 := by
          apply mul_le_mul_of_nonneg_left habs
          positivity
      _ = _ := by ring
  have hone' : η0 ≤ etaOf M * ℓ ^ N → ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ η0 * θ ≤ etaOf M * ℓ ^ N ∧
      (∀ χ, ∀ ρ ∈ Z χ, ¬ InRegion cZ M ρ → c₂ * Real.log (1 / θ) ≤ ℓ * (1 - ρ.re)) := by
    intro hη
    refine ⟨1, one_pos, le_refl _, by linarith, ?_⟩
    intro χ ρ _ hr
    unfold InRegion at hr
    replace hr := not_le.mp hr
    have habs := abs_nonneg ρ.im
    have h1 : (1 : ℝ) ≤ (M : ℝ) * (|ρ.im| + 2) := by nlinarith
    have h2 : 0 ≤ cZ / Real.log ((M : ℝ) * (|ρ.im| + 2)) := div_nonneg hcZ.le (Real.log_nonneg h1)
    have h3 : 0 ≤ ℓ * (1 - ρ.re) := mul_nonneg hℓ0.le (by linarith)
    simpa using h3
  have hone : η0 ≤ etaOf M → ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ η0 * θ ≤ etaOf M * ℓ ^ N ∧
      (∀ χ, ∀ ρ ∈ Z χ, ¬ InRegion cZ M ρ → c₂ * Real.log (1 / θ) ≤ ℓ * (1 - ρ.re)) := by
    intro hη
    apply hone'
    calc η0 ≤ etaOf M := hη
      _ = etaOf M * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hℓN (hη0pos.le.trans hη)
  rcases he : eOf M with _ | ⟨χ₁, β₁⟩
  · apply hone
    rw [etaOf_none M he]
    exact hη01
  · obtain ⟨hsq, hne, hL0, _, hβ1⟩ := eOf_exc M (χ₁, β₁) he
    simp only at hsq hne hL0 hβ1
    have hβ : 0 < 1 - β₁ := by linarith
    have hlow : (1 - β₁) * ℓ / (A₁ + 2) ≤ (1 - β₁) * Real.log M := by
      rw [div_le_iff₀ hk]
      calc (1 - β₁) * ℓ ≤ (1 - β₁) * ((A₁ + 2) * Real.log M) := mul_le_mul_of_nonneg_left hℓk hβ.le
        _ = _ := by ring
    have hup : (1 - β₁) * ℓ ^ N ≤ (1 - β₁) * Real.log M * ℓ ^ N := by
      have h0 : 0 ≤ (1 - β₁) * ℓ ^ N := by positivity
      calc (1 - β₁) * ℓ ^ N = (1 - β₁) * ℓ ^ N * 1 := (mul_one _).symm
        _ ≤ (1 - β₁) * ℓ ^ N * Real.log M := mul_le_mul_of_nonneg_left (by linarith) h0
        _ = _ := by ring
    by_cases hr : InRegion cZ M (β₁ : ℂ)
    · by_cases hcc : c₁ ≤ (1 - β₁) * ℓ
      · apply hone
        rw [etaOf_some M χ₁ β₁ he]
        apply le_min hη01
        have : c₁ / (A₁ + 2) ≤ (1 - β₁) * ℓ / (A₁ + 2) := div_le_div_of_nonneg_right hcc hk.le
        linarith
      · replace hcc := not_le.mp hcc
        by_cases hu : c₁ ≤ (1 - β₁) * ℓ ^ N
        · apply hone'
          rw [etaOf_some M χ₁ β₁ he, min_mul_of_nonneg (1 : ℝ) ((1 - β₁) * Real.log M) (by positivity : (0 : ℝ) ≤ ℓ ^ N)]
          apply le_min
          · linarith
          · linarith
        · replace hu := not_le.mp hu
          have hθ0 : 0 < (1 - β₁) * ℓ ^ N / c₁ := by positivity
          have hθ1 : (1 - β₁) * ℓ ^ N / c₁ ≤ 1 := by
            rw [div_le_one hc₁]; exact hu.le
          refine ⟨(1 - β₁) * ℓ ^ N / c₁, hθ0, hθ1, ?_, ?_⟩
          · rw [etaOf_some M χ₁ β₁ he, min_mul_of_nonneg (1 : ℝ) ((1 - β₁) * Real.log M) (by positivity : (0 : ℝ) ≤ ℓ ^ N)]
            apply le_min
            · calc η0 * ((1 - β₁) * ℓ ^ N / c₁) ≤ 1 * 1 := mul_le_mul hη01 hθ1 hθ0.le zero_le_one
                _ ≤ 1 * ℓ ^ N := by linarith
            · calc η0 * ((1 - β₁) * ℓ ^ N / c₁) ≤ c₁ * ((1 - β₁) * ℓ ^ N / c₁) :=
                    mul_le_mul_of_nonneg_right hη0c hθ0.le
                _ = (1 - β₁) * ℓ ^ N := by field_simp
                _ ≤ _ := hup
          · intro χ ρ hρ hnr
            obtain ⟨hz, hre, him⟩ := hZ χ ρ hρ
            have hd := hdh M χ₁ χ β₁ ((M : ℝ) ^ A₁ + 3) ρ (by omega) (by linarith) hsq hne hL0
              (by
                have : 1 - β₁ < c₁ / ℓ := by rw [lt_div_iff₀ hℓ0]; exact hcc
                linarith)
              hβ1 hz
              (by
                have := min_le_left c₀ (1 / 20 : ℝ)
                linarith)
              (by linarith)
              (by
                intro heq
                have h2 : ρ = (β₁ : ℂ) := (Prod.mk.inj heq).2
                rw [h2] at hnr
                exact hnr hr)
            rw [one_div_div]
            rw [div_le_iff₀ hℓ0] at hd
            linarith
    · apply hone
      have := etaOf_far M (by omega) χ₁ β₁ he hr
      linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section
noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem explicitS_proof' : ExplicitS := smoothed_explicit_formula

theorem logDensityM_proof' : LogDensityM := Dens.log_density_bound

theorem deuringHeilbronnMB_proof' : DeuringHeilbronnMB := deuring_heilbronn_lossy

theorem pnt_progressions_relative_weak_holds : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.PNTAPRelW :=
  prime_count_of_psi (glue_ranges psi_relative_near_range
    (psi_relative_far_range explicitS_proof' differenced_explicit_formula (zero_sum_bound_lossy logDensityM_proof' deuringHeilbronnMB_proof')))

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
