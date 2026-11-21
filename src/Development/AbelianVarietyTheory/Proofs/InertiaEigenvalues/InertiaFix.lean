import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis

section
universe u_1

namespace GlobalTheory.PowerEqOneClose

theorem norm_pow_sub_one_le {K : Type u_1} [NormedField K] [IsUltrametricDist K] (u : K)
    (hu : ‖u‖ ≤ 1) (n : ℕ) : ‖u ^ n - 1‖ ≤ ‖u - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : u ^ (n + 1) - 1 = (u ^ n - 1) * u + (u - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hu).trans ih

theorem norm_geom_sum_sub_le {K : Type u_1} [NormedField K] [IsUltrametricDist K] (u : K)
    (hu : ‖u‖ ≤ 1) (n : ℕ) : ‖(∑ i ∈ Finset.range n, u ^ i) - (n : K)‖ ≤ ‖u - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (∑ i ∈ Finset.range (n + 1), u ^ i) - ((n + 1 : ℕ) : K)
        = ((∑ i ∈ Finset.range n, u ^ i) - (n : K)) + (u ^ n - 1) := by
      rw [Finset.sum_range_succ]; push_cast; ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ih (norm_pow_sub_one_le u hu n))

theorem eq_one_of_pow_eq_one {K : Type u_1} [NormedField K] [IsUltrametricDist K] (m : ℕ)
    (hm : ‖(m : K)‖ = (1 : ℝ)) (u : K) (hu : u ^ m = (1 : K)) (h : ‖u - (1 : K)‖ < (1 : ℝ)) :
    u = (1 : K) := by
  have hu1 : ‖u‖ ≤ 1 := by
    have e : u = (u - 1) + 1 := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h.le norm_one.le)
  have hs := norm_geom_sum_sub_le u hu1 m
  have hg : (∑ i ∈ Finset.range m, u ^ i) * (u - 1) = 0 := by
    rw [geom_sum_mul, hu, sub_self]
  rcases mul_eq_zero.mp hg with h0 | h0
  · rw [h0, zero_sub, norm_neg, hm] at hs
    exact absurd h (not_lt.mpr hs)
  · exact sub_eq_zero.mp h0

end GlobalTheory.PowerEqOneClose
end

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.InertFix

theorem eq_one_of_pow_eq_one {K : Type*} [NormedField K] [IsUltrametricDist K] (m : ℕ)
    (hm : ‖(m : K)‖ = 1) (u : K) (hu : u ^ m = 1) (h1 : ‖u - 1‖ < 1) : u = 1 := by
  first
  | exact @_root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one
  | exact _root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one
  | (apply _root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerEqOneClose.eq_one_of_pow_eq_one ..)

theorem inertia_fix : ∀ (l : ℕ) [Fact l.Prime] (n : ℕ), 0 < n → ∀ σ : GQ l,
    (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → ∀ x : Om l, x ^ l ^ n = x → σ x = x := by
  intro l hl n hn σ hσ x hx
  by_cases hx0 : x = 0
  · rw [hx0, map_zero]
  have hlp : 1 < l ^ n := Nat.one_lt_pow hn.ne' hl.out.one_lt
  obtain ⟨m, hm⟩ : ∃ m, l ^ n = m + 1 := ⟨l ^ n - 1, by omega⟩
  have hm0 : m ≠ 0 := by omega
  have hxm : x ^ m = 1 := by
    rw [hm, pow_succ] at hx
    exact mul_right_cancel₀ hx0 (by rw [hx, one_mul])
  have hnx : ‖x‖ = 1 := by
    have : ‖x‖ ^ m = 1 := by rw [← norm_pow, hxm, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0).1 this
  have hcop : l.Coprime m := by
    have h : (l ^ n).Coprime m := by rw [hm]; simp
    exact Nat.Coprime.of_dvd_left (dvd_pow_self l hn.ne') h
  have hmn : ‖(m : Om l)‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
    exact Padic.norm_natCast_eq_one_iff.2 hcop
  have hu : σ x / x = 1 := by
    refine eq_one_of_pow_eq_one m hmn _ ?_ ?_
    · rw [div_pow, ← map_pow, hxm, map_one, div_one]
    · have e : σ x / x - 1 = (σ x - x) / x := by field_simp
      rw [e, norm_div, hnx, div_one]
      exact hσ x hnx.le
  exact (div_eq_one_iff_eq hx0).1 hu

end GlobalTheory.InertFix
end
