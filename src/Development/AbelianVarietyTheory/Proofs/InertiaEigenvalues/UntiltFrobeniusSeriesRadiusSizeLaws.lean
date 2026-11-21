import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import BuildAid.ForwardExisting

section
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory

theorem psers_norm_natCast_self (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  have h := PadicComplex.norm_extends' l (l : ℚ_[l])
  rw [Padic.norm_p] at h
  simpa using h

theorem psers_terms_tendsto_zero : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ), 1 ≤ h → 0 ≤ r → r < 1 → Filter.Tendsto (fun n : ℤ => ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ))) Filter.cofinite (nhds 0) := by
  intro l _ h j r h1 hr0 hr1
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hlR : (1 : ℝ) < l := by exact_mod_cast hl
  have ha := psers_norm_natCast_self l
  set a := ‖(l : ℂ_[l])‖ with ha_def
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have ha1 : a < 1 := by rw [ha]; exact inv_lt_one_of_one_lt₀ hlR
  rw [Int.cofinite_eq, Filter.tendsto_sup]
  constructor
  · rw [← Filter.map_neg_atTop, Filter.tendsto_map'_iff, ← Nat.map_cast_int_atTop,
      Filter.tendsto_map'_iff]
    refine squeeze_zero (fun k => ?_) (fun k => ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1)
    · simp only [Function.comp_apply, neg_neg, zpow_natCast]
      exact mul_nonneg (pow_nonneg ha0 _) (Real.rpow_nonneg hr0 _)
    · simp only [Function.comp_apply, neg_neg, zpow_natCast]
      have : r ^ ((l : ℝ) ^ (-(k : ℤ) * h + j : ℤ)) ≤ 1 :=
        Real.rpow_le_one hr0 hr1.le (zpow_nonneg (by positivity) _)
      calc a ^ k * r ^ ((l : ℝ) ^ (-(k : ℤ) * h + j : ℤ)) ≤ a ^ k * 1 :=
            mul_le_mul_of_nonneg_left this (pow_nonneg ha0 _)
        _ = a ^ k := mul_one _
  · rw [← Nat.map_cast_int_atTop, Filter.tendsto_map'_iff]
    have hN : Filter.Tendsto (fun k : ℕ => l ^ (k * h + j)) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop_mono (fun k => ?_) Filter.tendsto_id
      calc k ≤ l ^ k := (Nat.lt_pow_self hl).le
        _ ≤ l ^ (k * h + j) := Nat.pow_le_pow_right (by omega) (by nlinarith)
    refine squeeze_zero (fun k => ?_) (fun k => ?_)
      ((tendsto_self_mul_const_pow_of_lt_one hr0 hr1).comp hN)
    · exact mul_nonneg (zpow_nonneg ha0 _) (Real.rpow_nonneg hr0 _)
    · have e1 : a ^ (-((k : ℕ) : ℤ)) = (l : ℝ) ^ k := by
        rw [zpow_neg, zpow_natCast, ha, inv_pow, inv_inv]
      have e2 : (l : ℝ) ^ (((k : ℕ) : ℤ) * h + j : ℤ) = ((l ^ (k * h + j) : ℕ) : ℝ) := by
        rw [show (((k : ℕ) : ℤ) * h + j : ℤ) = ((k * h + j : ℕ) : ℤ) by push_cast; ring,
          zpow_natCast]
        push_cast; ring
      simp only [Function.comp_apply]
      rw [e1, e2, Real.rpow_natCast]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr0 _)
      have : l ^ k ≤ l ^ (k * h + j) := Nat.pow_le_pow_right (by omega) (by nlinarith)
      exact_mod_cast this

end GlobalTheory
end

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_untiltFrobeniusSeries_term_norms_zero : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ), 1 ≤ h → 0 ≤ r → r < 1 → Filter.Tendsto (fun n : ℤ => ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ))) Filter.cofinite (nhds 0) := by
  atlas_forward_decl GlobalTheory.psers_terms_tendsto_zero
end

section
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory

theorem gam_norm_natCast_eq (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  have h := PadicComplex.norm_extends' l (l : ℚ_[l])
  rw [Padic.norm_p] at h
  simpa using h

theorem gam_exists_max_of_tendsto (f : ℤ → ℝ) (hf0 : ∀ n, 0 ≤ f n)
    (hf : Filter.Tendsto f Filter.cofinite (nhds 0)) : ∃ n₀, ∀ n, f n ≤ f n₀ := by
  by_cases hall : ∀ n, f n = 0
  · exact ⟨0, fun n => by rw [hall n, hall 0]⟩
  push_neg at hall
  obtain ⟨m, hm⟩ := hall
  have hmpos : 0 < f m := lt_of_le_of_ne (hf0 m) (Ne.symm hm)
  have hev : ∀ᶠ n in Filter.cofinite, f n < f m := hf (Iio_mem_nhds hmpos)
  have hfin : {n | ¬ f n < f m}.Finite := Filter.eventually_cofinite.mp hev
  have hmem : m ∈ hfin.toFinset := by simp
  obtain ⟨n₀, hn₀, hmax⟩ := hfin.toFinset.exists_max_image f ⟨m, hmem⟩
  refine ⟨n₀, fun n => ?_⟩
  by_cases hn : f n < f m
  · exact hn.le.trans (hmax m hmem)
  · exact hmax n (by simpa using hn)

theorem gam_laws : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ), 1 ≤ h → 0 ≤ r → r < 1 → (∀ n : ℤ, ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ)) ≤ gam l h j r) ∧ (∃ n : ℤ, gam l h j r = ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ))) ∧ 0 ≤ gam l h j r ∧ (0 < r → 0 < gam l h j r) ∧ gam l h j (r ^ l ^ h) = ‖(l : ℂ_[l])‖ * gam l h j r ∧ ∀ s : ℝ, r < s → s < 1 → gam l h j r < gam l h j s := by
  intro l _ h j r h1 hr0 hr1
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hlR : (1 : ℝ) < l := by exact_mod_cast hl
  have ha := gam_norm_natCast_eq l
  set a := ‖(l : ℂ_[l])‖ with ha_def
  have ha0 : 0 < a := by rw [ha]; positivity

  have key : ∀ t : ℝ, 0 ≤ t → t < 1 →
      (∀ n : ℤ, a ^ (-n) * t ^ ((l : ℝ) ^ (n * h + j : ℤ)) ≤ gam l h j t) ∧
      (∃ n : ℤ, gam l h j t = a ^ (-n) * t ^ ((l : ℝ) ^ (n * h + j : ℤ))) := by
    intro t ht0 ht1
    set f : ℤ → ℝ := fun n => a ^ (-n) * t ^ ((l : ℝ) ^ (n * h + j : ℤ)) with hf_def
    have hf0 : ∀ n, 0 ≤ f n := fun n => mul_nonneg (zpow_nonneg ha0.le _) (Real.rpow_nonneg ht0 _)
    obtain ⟨n₀, hn₀⟩ := gam_exists_max_of_tendsto f hf0 (GlobalTheory.T.tendsto_untiltFrobeniusSeries_term_norms_zero l h j t h1 ht0 ht1)
    have hbdd : BddAbove (Set.range f) := ⟨f n₀, by rintro _ ⟨n, rfl⟩; exact hn₀ n⟩
    have hg : gam l h j t = ⨆ n, f n := rfl
    refine ⟨fun n => ?_, n₀, ?_⟩
    · rw [hg]; exact le_ciSup hbdd n
    · rw [hg]; exact le_antisymm (ciSup_le hn₀) (le_ciSup hbdd n₀)
  obtain ⟨hle, n₀, hn₀⟩ := key r hr0 hr1
  refine ⟨hle, ⟨n₀, hn₀⟩, ?_, ?_, ?_, ?_⟩
  · rw [hn₀]; exact mul_nonneg (zpow_nonneg ha0.le _) (Real.rpow_nonneg hr0 _)
  · intro hr
    exact lt_of_lt_of_le (mul_pos (zpow_pos ha0 _) (Real.rpow_pos_of_pos hr _)) (hle 0)
  ·
    have hq0 : 0 ≤ r ^ l ^ h := pow_nonneg hr0 _
    have hq1 : r ^ l ^ h < 1 := pow_lt_one₀ hr0 hr1 (by positivity)
    obtain ⟨hle', m₀, hm₀⟩ := key (r ^ l ^ h) hq0 hq1
    have shift : ∀ n : ℤ, a ^ (-n) * (r ^ l ^ h) ^ ((l : ℝ) ^ (n * h + j : ℤ)) =
        a * (a ^ (-(n + 1)) * r ^ ((l : ℝ) ^ ((n + 1) * h + j : ℤ))) := by
      intro n
      have e1 : (r ^ l ^ h) ^ ((l : ℝ) ^ (n * h + j : ℤ)) = r ^ ((l : ℝ) ^ ((n + 1) * h + j : ℤ)) := by
        rw [← Real.rpow_natCast r (l ^ h), ← Real.rpow_mul hr0]
        congr 1
        have hl0 : (l : ℝ) ≠ 0 := by positivity
        rw [show ((n + 1) * h + j : ℤ) = (h : ℤ) + (n * h + j) by ring, zpow_add₀ hl0 (h : ℤ) (n * h + j), zpow_natCast, Nat.cast_pow]
      have e2 : a ^ (-n) = a * a ^ (-(n + 1)) := by
        rw [show -n = 1 + (-(n + 1)) by ring, zpow_add₀ ha0.ne', zpow_one]
      rw [e1, e2]; ring
    apply le_antisymm
    · rw [hm₀, shift]
      exact mul_le_mul_of_nonneg_left (hle (m₀ + 1)) ha0.le
    · rw [hn₀]
      have := hle' (n₀ - 1)
      rw [shift, show n₀ - 1 + 1 = n₀ by ring] at this
      exact this
  · intro s hrs hs1
    have hs0 : 0 < s := lt_of_le_of_lt hr0 hrs
    obtain ⟨hles, -⟩ := key s hs0.le hs1
    rw [hn₀]
    refine lt_of_lt_of_le ?_ (hles n₀)
    apply mul_lt_mul_of_pos_left _ (zpow_pos ha0 _)
    exact Real.rpow_lt_rpow hr0 hrs (zpow_pos (by positivity) _)

end GlobalTheory
end

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.untiltFrobeniusSeriesRadiusSize_laws : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ), 1 ≤ h → 0 ≤ r → r < 1 → (∀ n : ℤ, ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ)) ≤ gam l h j r) ∧ (∃ n : ℤ, gam l h j r = ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ))) ∧ 0 ≤ gam l h j r ∧ (0 < r → 0 < gam l h j r) ∧ gam l h j (r ^ l ^ h) = ‖(l : ℂ_[l])‖ * gam l h j r ∧ ∀ s : ℝ, r < s → s < 1 → gam l h j r < gam l h j s := by
  atlas_forward_decl GlobalTheory.gam_laws
end
