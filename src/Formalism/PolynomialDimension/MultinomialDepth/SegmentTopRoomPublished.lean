import Formalism.PolynomialDimension.DigitSumValuationBound

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

lemma window_parameter_bounds {p N N₁ r : ℕ} {Y a b' Q La : ℝ} (h : HypSeg p N N₁ (r + 1) Y a b' Q La) :
    1 ≤ Y ∧ ((r : ℝ) + 1) ^ 2 * Y ^ 2 ≤ p ∧ ((r : ℝ) + 1) * Y ^ 2 * Real.log a ≤ a / b' ∧
    (N : ℝ) ≤ (r : ℝ) + 1 ∧ (N₁ : ℝ) ^ 4 ≤ (r : ℝ) + 1 ∧ Real.log a ≤ (r : ℝ) + 1 ∧ 0 ≤ La ∧
    La ≤ (r : ℝ) + 1 ∧ ((r : ℝ) + 1) ^ 3 * Q * Y ≤ b' ∧ b' ≤ a ∧ (p : ℝ) < a / b' ∧
    (3 : ℝ) ≤ (r : ℝ) + 1 ∧ (1 : ℝ) ≤ N ∧ (1 : ℝ) ≤ N₁ ∧ 1 ≤ Q ∧ 0 < b' := by
  obtain ⟨hY, hp, h2, hN, hN1, hlog, hLa0, hLa, h4, hba, h6, hk, hN', hN1', hQ, hb0⟩ := h
  push_cast at hp h2 hlog hLa h4
  exact ⟨hY, hp, h2, by exact_mod_cast hN, by exact_mod_cast hN1, hlog, hLa0, hLa, h4, hba, h6,
    by exact_mod_cast hk, by exact_mod_cast hN', by exact_mod_cast hN1', hQ, hb0⟩

lemma derived_parameter_bounds {K Y a b' Q pp : ℝ} (hY : 1 ≤ Y) (hp : K ^ 2 * Y ^ 2 ≤ pp) (h4 : K ^ 3 * Q * Y ≤ b')
    (hba : b' ≤ a) (h6 : pp < a / b') (hK : 3 ≤ K) (hQ : 1 ≤ Q) (hb0 : 0 < b') :
    9 ≤ pp ∧ 27 ≤ b' ∧ pp * b' < a ∧ 243 < a ∧ pp < a ∧ 9 * (K * Q) ≤ a ∧ K ≤ a ∧
      9 * (K * Q * Y) ≤ a ∧ 3 * (K ^ 2 * Q * Y) ≤ a := by
  have hK2 : (9 : ℝ) ≤ K ^ 2 := by
    calc (9 : ℝ) = 3 ^ 2 := by norm_num
      _ ≤ K ^ 2 := by gcongr
  have hK3 : (27 : ℝ) ≤ K ^ 3 := by
    calc (27 : ℝ) = 3 ^ 3 := by norm_num
      _ ≤ K ^ 3 := by gcongr
  have hK0 : 0 < K := by linarith
  have hY2 : 1 ≤ Y ^ 2 := one_le_pow₀ hY
  have hp9 : 9 ≤ pp := by
    calc (9 : ℝ) = 9 * 1 := by norm_num
      _ ≤ K ^ 2 * Y ^ 2 := by gcongr
      _ ≤ pp := hp
  have hb27 : 27 ≤ b' := by
    calc (27 : ℝ) = 27 * 1 * 1 := by norm_num
      _ ≤ K ^ 3 * Q * Y := by gcongr
      _ ≤ b' := h4
  have hpb : pp * b' < a := (lt_div_iff₀ hb0).mp h6
  have h243 : (243 : ℝ) ≤ pp * b' := by
    calc (243 : ℝ) = 9 * 27 := by norm_num
      _ ≤ pp * b' := by gcongr
  have hppa : pp ≤ pp * b' := le_mul_of_one_le_right (by linarith) (by linarith)
  have hKQY : 9 * (K * Q * Y) ≤ a := by
    calc 9 * (K * Q * Y) ≤ K ^ 2 * (K * Q * Y) := by gcongr
      _ = K ^ 3 * Q * Y := by ring
      _ ≤ a := by linarith
  have hKQ : K * Q ≤ K * Q * Y := le_mul_of_one_le_right (by positivity) hY
  have hKK : K ≤ K * Q := le_mul_of_one_le_right hK0.le hQ
  have hK2QY : 3 * (K ^ 2 * Q * Y) ≤ a := by
    calc 3 * (K ^ 2 * Q * Y) ≤ K * (K ^ 2 * Q * Y) := by gcongr
      _ = K ^ 3 * Q * Y := by ring
      _ ≤ a := by linarith
  have hKQ0 : 0 < K * Q := by positivity
  exact ⟨hp9, hb27, hpb, by linarith, by linarith, by linarith, by linarith, hKQY, hK2QY⟩







theorem segment_top_room : SegSTopRoom := by
  intro p N N₁ r Y a b' Q La P Qj A0 sg C h hP hPQ hpP hA0 hsg hC
  obtain ⟨hY, hp, h2, hN, hN1, hlog, hLa0, hLa, h4, hba, h6, hK, hN', hN1', hQ, hb0⟩ := window_parameter_bounds h
  obtain ⟨hp9, hb27, hpb, h243, hpa, hKQ, hKa, hKQY, hK2QY⟩ := derived_parameter_bounds hY hp h4 hba h6 hK hQ hb0
  generalize (r : ℝ) + 1 = K at *
  have hK0 : 0 < K := by linarith
  have ha0 : 0 < a := by linarith
  have h9P : 9 * P ≤ Qj := le_trans (by gcongr) hpP
  have hQj : 0 < Qj := by linarith
  have haP : 0 < a / P := by positivity
  have h1 : a / Qj ≤ a / P / 9 := by
    rw [div_div, mul_comm P 9]
    gcongr
  have h2' : La * A0 ≤ K * (a / P / 9) := by
    calc La * A0 ≤ La * (a / P / 9) := by gcongr; linarith
      _ ≤ K * (a / P / 9) := by gcongr
  have h3 : sg ≤ 2 / 9 * (a / P) := by
    calc sg ≤ 2 * La * A0 / K := hsg
      _ = 2 * (La * A0) / K := by ring
      _ ≤ 2 * (K * (a / P / 9)) / K := by gcongr
      _ = 2 / 9 * (a / P) := by field_simp
  have h4' : K ≤ 1 / 9 * (a / P) := by
    have h9 : 9 * (K * P) ≤ a := le_trans (by gcongr) hKQ
    rw [← mul_div_assoc, le_div_iff₀ hP]
    linarith
  exact ⟨h3, by linarith, by linarith⟩

theorem segment_top_room₂ : SegmentTopRoom := by
  intro p N N₁ r Y a b' Q La P A c o h hP hA0 hA hc ho
  obtain ⟨hY, hp, h2, hN, hN1, hlog, hLa0, hLa, h4, hba, h6, hK, hN', hN1', hQ, hb0⟩ := window_parameter_bounds h
  obtain ⟨hp9, hb27, hpb, h243, hpa, hKQ, hKa, hKQY, hK2QY⟩ := derived_parameter_bounds hY hp h4 hba h6 hK hQ hb0
  generalize (r : ℝ) + 1 = K at *
  generalize (p : ℝ) = pp at *
  have hK0 : 0 < K := by linarith
  have ha0 : 0 < a := by linarith
  have haP : 0 < a / P := by positivity
  have hb9 : b' ≤ a / 9 := by
    have : 9 * b' ≤ pp * b' := by gcongr
    linarith
  have hbP : b' / P ≤ a / P / 9 := by
    calc b' / P ≤ a / 9 / P := by gcongr
      _ = a / P / 9 := by ring
  have hp2 : (81 : ℝ) ≤ pp ^ 2 := by
    calc (81 : ℝ) = 9 ^ 2 := by norm_num
      _ ≤ pp ^ 2 := by gcongr
  have h4p : 4 / pp ^ 2 ≤ 4 / 81 := by gcongr
  have c1 : A * (1 + 4 / pp ^ 2) ≤ 0.25 * (a / P) := by
    calc A * (1 + 4 / pp ^ 2) ≤ (3 * b' / (2 * P)) * (1 + 4 / 81) := by gcongr
      _ = 85 / 54 * (b' / P) := by field_simp; ring
      _ ≤ 85 / 54 * (a / P / 9) := by gcongr
      _ ≤ 0.25 * (a / P) := by norm_num; linarith
  have c2 : a / (pp * P) + (3 * b' / 2) / ((pp ^ 2 - 1) * P) ≤ 0.12 * (a / P) := by
    have d1 : a / (pp * P) ≤ a / (9 * P) := by gcongr
    have d2 : (3 * b' / 2) / ((pp ^ 2 - 1) * P) ≤ (3 * b' / 2) / (80 * P) := by
      gcongr; linarith
    have d3 : a / (9 * P) = a / P / 9 := by field_simp
    have d4 : (3 * b' / 2) / (80 * P) = 3 / 160 * (b' / P) := by field_simp; ring
    have d5 : 3 / 160 * (b' / P) ≤ 3 / 160 * (a / P / 9) := by gcongr
    norm_num
    linarith
  refine ⟨c1, c2, ?_⟩
  have c3 : La * c / K ≤ 0.12 * (a / P) := by
    rw [div_le_iff₀ hK0]
    calc La * c ≤ La * (0.12 * (a / P)) := by gcongr; linarith
      _ ≤ K * (0.12 * (a / P)) := by gcongr
      _ = 0.12 * (a / P) * K := by ring
  norm_num at c1 c3 ⊢
  linarith













end Formalism.CountingSumsFrames
