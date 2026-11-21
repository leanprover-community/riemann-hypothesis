import Formalism.HermitianCurvature.HermitianCurvatureProofs.Interlace
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.QwBound
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.InterlacingGrids.PstMul

namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Finset

theorem interlaces_of_OK (P : M.Par) (hOK : P.OK) : I.Interlaces P.k P.u P.u' P.lo := by
  intro i hi
  have hg := hOK.gap i hi
  unfold M.Par.lo M.Par.hi at *
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := min_le_left (P.u i) (P.u' i); linarith
  · have := min_le_right (P.u i) (P.u' i); linarith
  · have := le_max_left (P.u (i + 1)) (P.u' (i + 1)); linarith
  · have := le_max_right (P.u (i + 1)) (P.u' (i + 1)); linarith

theorem den_core (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : I.Interlaces k u u' ρ) (hA : u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) :
    ∀ i, 1 ≤ i → i ≤ k → 1 ≤ |Y + 1 / 2 + u i| ∧ 1 ≤ |Y + 1 / 2 + u' i| := by
  have hu := Formalism.FourierDecayAlt.P.Interlace.antitone_on (Formalism.FourierDecayAlt.P.Interlace.u_step h)
  have hu' := Formalism.FourierDecayAlt.P.Interlace.antitone_on
    (Formalism.FourierDecayAlt.P.Interlace.u_step (Formalism.FourierDecayAlt.P.Interlace.interlaces_swap h))
  intro i hi1 hik
  rcases lt_trichotomy i l with hil | rfl | hil
  · obtain ⟨a, b, c, d⟩ := h i (mem_Icc.2 ⟨hi1, by omega⟩)
    have h1 := hu' (i + 1) l (by omega) (by omega) hlk
    exact ⟨le_abs.2 (Or.inl (by linarith)), le_abs.2 (Or.inl (by linarith))⟩
  · exact ⟨le_abs.2 (Or.inr (by linarith)), le_abs.2 (Or.inl (by linarith))⟩
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    obtain ⟨a, b, c, d⟩ := h j (mem_Icc.2 ⟨by omega, by omega⟩)
    have h1 := hu l j hl1 (by omega) (by omega)
    exact ⟨le_abs.2 (Or.inr (by linarith)), le_abs.2 (Or.inr (by linarith))⟩

theorem den_onCut (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : I.Interlaces k u u' ρ) (hc : I.OnCut u u' l Y) :
    ∀ i, 1 ≤ i → i ≤ k → 1 ≤ |Y + 1 / 2 + u i| ∧ 1 ≤ |Y + 1 / 2 + u' i| := by
  rcases hc with hA | hB
  · exact den_core k u u' ρ l Y hl1 hlk h hA
  · intro i hi1 hik
    exact (den_core k u' u ρ l Y hl1 hlk (Formalism.FourierDecayAlt.P.Interlace.interlaces_swap h) hB i hi1 hik).symm

theorem abs_le_of_onCut (u u' : ℕ → ℝ) (l : ℕ) (Y b : ℝ) (hc : I.OnCut u u' l Y) (hu : |u l| ≤ b)
    (hu' : |u' l| ≤ b) : |Y| ≤ b := by
  rw [abs_le] at hu hu' ⊢
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith

theorem qpoly_eq_of_pos (k : ℕ) (T T' : ℝ) (u u' : ℕ → ℝ) (Y : ℝ) (hT : 0 < T) (hT' : 0 < T')
    (hq : 0 < I.qpoly k T T' u u' Y) :
    I.qpoly k T T' u u' Y = T * T' * ∏ i ∈ Icc 1 k, (|Y + 1 / 2 + u i| * |Y + 1 / 2 + u' i|) := by
  rw [← abs_of_pos hq]
  unfold I.qpoly
  rw [abs_mul, abs_neg, abs_of_pos (mul_pos hT hT'), Finset.abs_prod]
  simp only [abs_mul]

structure LamData (P : M.Par) (lam : ℕ → ℝ) (c g b : ℝ) : Prop where
  c_pos : 0 < c
  g_ge : 1 + c ≤ g
  b_ge_three : 3 ≤ b
  b_ge_k : (P.k : ℝ) ≤ b
  b_ge_c : c + 2 ≤ b
  lam_le : ∀ s, 1 ≤ s → s ≤ P.k + 2 * P.r + 1 → |lam s| ≤ b
  gap : ∀ s, 1 ≤ s → s + 1 ≤ P.k - 1 → lam (s + 1) + g ≤ lam s
  inter : ∀ s, 1 ≤ s → s ≤ P.k - 1 →
    (lam s + 1 / 2 ≤ P.u s ∧ P.u (s + 1) ≤ lam s - 1 / 2) ∧ (lam s + 1 / 2 ≤ P.u' s ∧ P.u' (s + 1) ≤ lam s - 1 / 2)
  u_le : ∀ i, 1 ≤ i → i ≤ P.k → |P.u i| ≤ b ∧ |P.u' i| ≤ b

noncomputable def P₀ : M.Par where
  k := 2
  r := 0
  T := 1
  T' := 1
  u := fun i => if i = 1 then 20 else 0
  u' := fun i => if i = 1 then 40 else 0

noncomputable def lam₀ : ℕ → ℝ := fun s => if s = 1 then 10 else 0

theorem P₀_OK : P₀.OK where
  k_pos := by show 1 ≤ 2; norm_num
  T_pos := by show (0 : ℝ) < 1; norm_num
  T'_pos := by show (0 : ℝ) < 1; norm_num
  int_u := by
    intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi
    have h2' : i ≤ 2 := h2
    interval_cases i
    · exact ⟨0, by simp [P₀]⟩
    · exact ⟨-20, by simp [P₀]⟩
  int_u' := by
    intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi
    have h2' : i ≤ 2 := h2
    interval_cases i
    · exact ⟨20, by simp [P₀]; norm_num⟩
    · exact ⟨-20, by simp [P₀]⟩
  gap := by
    intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi
    have h2' : i ≤ 1 := h2
    interval_cases i
    simp only [M.Par.lo, M.Par.hi, P₀]
    norm_num

theorem lamData₀ : LamData P₀ lam₀ 1 2 40 where
  c_pos := by norm_num
  g_ge := by norm_num
  b_ge_three := by norm_num
  b_ge_k := by show ((2 : ℕ) : ℝ) ≤ 40; norm_num
  b_ge_c := by norm_num
  lam_le := by
    intro s _ _
    unfold lam₀
    split_ifs <;> norm_num
  gap := by
    intro s h1 h2
    have : P₀.k = 2 := rfl
    omega
  inter := by
    intro s h1 h2
    have h2' : s ≤ 1 := h2
    interval_cases s
    simp only [lam₀, P₀]
    norm_num
  u_le := by
    intro i h1 h2
    have h2' : i ≤ 2 := h2
    interval_cases i <;> simp [P₀] <;> norm_num



end CompanionTheory.WaveGrid
