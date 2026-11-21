import Formalism.HermitianCurvature.HermitianCurvatureProofs.Interlace
import Formalism.HermitianCurvature.StatementD
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.InterlacingGrids.PstMul

section
namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt

noncomputable def fac (l : C.Letter) (y : ℝ) : ℝ :=
  if l.1 then (y - l.2 + 1) / (y - l.2) else (l.2 - y) / (l.2 - y - 1)

noncomputable def facW {S : Type} (l : Wd.Letter ℂ S) (Y : ℂ) : ℂ :=
  if l.plus then (Y - l.pt + 1) / (Y - l.pt) else (l.pt - Y) / (l.pt - Y - 1)




theorem qC_ofReal (P : M.Par) (y : ℝ) :
    M.qC P (y : ℂ) = ((I.qpoly P.k P.T P.T' P.u P.u' y : ℝ) : ℂ) := by
  simp [M.qC, I.qpoly]






end CompanionTheory.WaveGrid
end

section
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
end

section
namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Finset GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

structure PairData (P : M.Par) (l : ℕ) (lam : ℕ → ℝ) (c g b : ℝ) : Prop where
  c_pos : 0 < c
  g_ge : 1 + c ≤ g
  b_ge_three : 3 ≤ b
  b_ge_k : (P.k : ℝ) ≤ b
  b_ge_c : c + 2 ≤ b
  lam_le : ∀ s, 1 ≤ s → s ≤ P.k + 2 * P.r + 1 → |lam s| ≤ b
  gap : ∀ s, 1 ≤ s → s + 1 ≤ P.k - 1 → lam (s + 1) + g ≤ lam s
  ul_le : |P.u l| ≤ b ∧ |P.u' l| ≤ b
  pair : ∀ Y, I.OnCut P.u P.u' l Y → (∃ e, PairOK P.k lam P.u e (-Y)) ∧ ∃ e', PairOK P.k lam P.u' e' (-Y)

theorem LamData.toPair {P : M.Par} {lam : ℕ → ℝ} {c g b : ℝ} (hL : LamData P lam c g b) {l : ℕ} (hl1 : 1 ≤ l)
    (hlk : l ≤ P.k) : PairData P l lam c g b where
  c_pos := hL.c_pos
  g_ge := hL.g_ge
  b_ge_three := hL.b_ge_three
  b_ge_k := hL.b_ge_k
  b_ge_c := hL.b_ge_c
  lam_le := hL.lam_le
  gap := hL.gap
  ul_le := hL.u_le l hl1 hlk
  pair := fun Y _ =>
    ⟨⟨0, pairOK_of_interlace P.k lam P.u 0 (-Y) fun s h1 h2 => (hL.inter s h1 h2).1⟩,
      ⟨0, pairOK_of_interlace P.k lam P.u' 0 (-Y) fun s h1 h2 => (hL.inter s h1 h2).2⟩⟩

theorem pairOK_of_moved (k l : ℕ) (lam u v : ℕ → ℝ) (x : ℝ)
    (h : ∀ s, 1 ≤ s → s ≤ k - 1 → lam s + 1 / 2 ≤ u s ∧ u (s + 1) ≤ lam s - 1 / 2)
    (hv : ∀ i, i ≠ l → v i = u i) (hx : (u l < x ∧ x < v l) ∨ (v l < x ∧ x < u l)) :
    ∃ e, PairOK k lam v e x := by
  rcases hx with ⟨h1, -⟩ | ⟨-, h2⟩
  · refine ⟨l - 1, fun s hs1 hsk hse => ⟨fun hlt => ?_, fun _ => ?_⟩⟩
    · have hsl : s ≠ l := by
        rintro rfl
        have := (h s hs1 hsk).1
        linarith
      rw [hv s hsl]
      exact (h s hs1 hsk).1
    · rw [hv (s + 1) (by omega)]
      exact (h s hs1 hsk).2
  · refine ⟨l, fun s hs1 hsk hse => ⟨fun _ => ?_, fun hle => ?_⟩⟩
    · rw [hv s hse]
      exact (h s hs1 hsk).1
    · have hsl : s + 1 ≠ l := by
        rintro rfl
        have := (h s hs1 hsk).2
        linarith
      rw [hv (s + 1) hsl]
      exact (h s hs1 hsk).2

structure MovedData (P : M.Par) (l : ℕ) (lam : ℕ → ℝ) (c g b : ℝ) : Prop where
  c_pos : 0 < c
  g_ge : 1 + c ≤ g
  b_ge_three : 3 ≤ b
  b_ge_k : (P.k : ℝ) ≤ b
  b_ge_c : c + 2 ≤ b
  lam_le : ∀ s, 1 ≤ s → s ≤ P.k + 2 * P.r + 1 → |lam s| ≤ b
  gap : ∀ s, 1 ≤ s → s + 1 ≤ P.k - 1 → lam (s + 1) + g ≤ lam s
  inter : ∀ s, 1 ≤ s → s ≤ P.k - 1 → lam s + 1 / 2 ≤ P.u s ∧ P.u (s + 1) ≤ lam s - 1 / 2
  moved : ∀ i, i ≠ l → P.u' i = P.u i
  ul_le : |P.u l| ≤ b ∧ |P.u' l| ≤ b

theorem MovedData.toPair {P : M.Par} {l : ℕ} {lam : ℕ → ℝ} {c g b : ℝ} (hM : MovedData P l lam c g b) :
    PairData P l lam c g b where
  c_pos := hM.c_pos
  g_ge := hM.g_ge
  b_ge_three := hM.b_ge_three
  b_ge_k := hM.b_ge_k
  b_ge_c := hM.b_ge_c
  lam_le := hM.lam_le
  gap := hM.gap
  ul_le := hM.ul_le
  pair := fun Y hY =>
    ⟨⟨0, pairOK_of_interlace P.k lam P.u 0 (-Y) hM.inter⟩,
      pairOK_of_moved P.k l lam P.u P.u' (-Y) hM.inter hM.moved (by
        rcases hY with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨by linarith, by linarith⟩
        · exact Or.inr ⟨by linarith, by linarith⟩)⟩

theorem nq_onCut_pair (P : M.Par) (hOK : P.OK) (l : ℕ) (hl1 : 1 ≤ l) (hlk : l ≤ P.k) (hk : 2 ≤ P.k)
    (lam : ℕ → ℝ) (c g b : ℝ) (hL : PairData P l lam c g b) (Y : ℝ) (hY : I.OnCut P.u P.u' l Y) :
    0 < (M.qC P (Y : ℂ)).re ∧
      Pst P.k P.r lam c Y * Pst P.k P.r lam c (Y + 1) ≤
        b ^ (8 * P.r + 20) / (P.T * P.T') * (M.qC P (Y : ℂ)).re := by
  have hρ := interlaces_of_OK P hOK
  have hq := Formalism.FourierDecayAlt.P.q_positive_interlacing P.k P.u P.u' P.lo l Y P.T P.T' hl1 hlk hρ hY hOK.T_pos hOK.T'_pos
  have hTT : 0 < P.T * P.T' := mul_pos hOK.T_pos hOK.T'_pos
  rw [qC_ofReal, Complex.ofReal_re]
  refine ⟨hq, ?_⟩
  have hden := den_onCut P.k P.u P.u' P.lo l Y hl1 hlk hρ hY
  have hYb : |Y| ≤ b := abs_le_of_onCut P.u P.u' l Y b hY hL.ul_le.1 hL.ul_le.2
  obtain ⟨⟨e, he⟩, e', he'⟩ := hL.pair Y hY
  have hmain := pst_mul_le P.k P.r lam P.u P.u' e e' c g b Y hk hL.c_pos.le
    hL.g_ge hL.b_ge_three hL.b_ge_k hL.b_ge_c hYb hL.lam_le hL.gap he he'
    (fun i h1 h2 => (hden i h1 h2).1) (fun i h1 h2 => (hden i h1 h2).2)
  rw [qpoly_eq_of_pos P.k P.T P.T' P.u P.u' Y hOK.T_pos hOK.T'_pos hq]
  calc _ ≤ b ^ (8 * P.r + 20) * ∏ i ∈ Icc 1 P.k, (|Y + 1 / 2 + P.u i| * |Y + 1 / 2 + P.u' i|) := hmain
    _ = b ^ (8 * P.r + 20) / (P.T * P.T') *
        (P.T * P.T' * ∏ i ∈ Icc 1 P.k, (|Y + 1 / 2 + P.u i| * |Y + 1 / 2 + P.u' i|)) := by
      rw [div_mul_eq_mul_div, eq_div_iff hTT.ne']
      ring

noncomputable def P₁ : M.Par where
  k := 2
  r := 0
  T := 1
  T' := 1
  u := fun i => if i = 1 then 40 else 0
  u' := fun i => if i = 1 then 40 else if i = 2 then 36 else 0

theorem P₁_OK : P₁.OK where
  k_pos := by show 1 ≤ 2; norm_num
  T_pos := by show (0 : ℝ) < 1; norm_num
  T'_pos := by show (0 : ℝ) < 1; norm_num
  int_u := by
    intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi
    have h2' : i ≤ 2 := h2
    interval_cases i
    · exact ⟨0, by simp [P₁]⟩
    · exact ⟨-40, by simp [P₁]⟩
  int_u' := by
    intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi
    have h2' : i ≤ 2 := h2
    interval_cases i
    · exact ⟨0, by simp [P₁]⟩
    · exact ⟨-4, by simp [P₁]; norm_num⟩
  gap := by
    intro i hi
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi
    have h2' : i ≤ 1 := h2
    interval_cases i
    simp only [M.Par.lo, M.Par.hi, P₁]
    norm_num

theorem movedData₁ : MovedData P₁ 2 lam₀ 1 2 40 where
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
    have : P₁.k = 2 := rfl
    omega
  inter := by
    intro s h1 h2
    have h2' : s ≤ 1 := h2
    interval_cases s
    simp only [lam₀, P₁]
    norm_num
  moved := by
    intro i hi
    simp only [P₁]
    split_ifs <;> simp_all
  ul_le := by
    simp only [P₁]
    norm_num


end CompanionTheory.WaveGrid
end
