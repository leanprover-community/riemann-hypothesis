import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaFiveOneOfTheoremTwo

section
noncomputable section
namespace Formalism.MainNotions.StandardLattice
open NumberField Formalism.BasicNotions Finset

theorem b_ge_one_section_B (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (ρ : D.what₂.Tau) (j : ℕ) (hj : j < D.R.m) : 1 ≤ bN D ρ j := by
  unfold DataB at hB
  obtain ⟨hpi, hlogv, hf, hmk, hk, hg, hΔ, hv1, hv2, hu1, hu2, hu3, hw, hinc, hb0, hgap⟩ := hB
  have hL := scale_one_le_L sc
  have hkpos : (0 : ℝ) < D.R.k := by
    have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
    nlinarith
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have : 0 < D.R.k := by exact_mod_cast hkpos
    exact_mod_cast Nat.one_le_of_lt this
  have hx := sc.one_lt_alt
  have hpos : ∀ i, i < D.R.m → 1 ≤ bN D ρ i := by
    intro i
    induction i with
    | zero =>
      intro _
      have h0 := (hb0 ρ).1
      have h4 : 1 ≤ bN D ρ 0 / sc.x := le_trans (by nlinarith) h0
      have h5 := (le_div_iff₀ (by linarith)).mp h4
      nlinarith
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := (hw ρ i (by omega)).2.1
      have h3 := hinc ρ i hi
      linarith
  exact hpos j hj

theorem weights_le_two_b (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (ρ : D.what₂.Tau) (j : ℕ) (hj : j < D.R.m) : w j ρ ≤ 2 * sc.b := by
  unfold DataB at hB
  obtain ⟨hpi, hlogv, hf, hmk, hk, hg, hΔ, hv1, hv2, hu1, hu2, hu3, hw, hinc, hb0, hgap⟩ := hB
  have hstep : ∀ i, i + 1 < D.R.m → w i ρ ≤ w (i + 1) ρ := fun i hi =>
    le_of_lt (lt_trans (hinc ρ i hi) (hw ρ (i + 1) hi).2.1)
  have hmono : ∀ d, ∀ i, i + d = D.R.m - 1 → w i ρ ≤ w (D.R.m - 1) ρ := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have h : i = D.R.m - 1 := by omega
      simp only [h, le_refl]
    | succ d ih =>
      intro i hi
      exact le_trans (hstep i (by omega)) (ih (i + 1) (by omega))
  exact le_trans (hmono (D.R.m - 1 - j) j (by omega)) (hb0 ρ).2

theorem log_weight_minus_log_b_bound (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (ρ : D.what₂.Tau) (j : ℕ) (hj : j < D.R.m) :
    (D.R.k : ℝ) * Real.log (w j ρ) - ((D.R.k : ℝ) - 1) * Real.log (bN D ρ j) ≤ (D.R.k : ℝ) / sc.x + 2 * sc.L := by
  have hb1 := b_ge_one_section_B D sc C0 Δ w hB ρ j hj
  have hwl := weights_le_two_b D sc C0 Δ w hB ρ j hj
  unfold DataB at hB
  obtain ⟨hpi, hlogv, hf, hmk, hk, hg, hΔ, hv1, hv2, hu1, hu2, hu3, hw, hinc, hb0, hgap⟩ := hB
  obtain ⟨hw0, hbw, habs⟩ := hw ρ j hj
  have hL := scale_one_le_L sc
  have hx := sc.one_lt_alt
  have hkpos : (0 : ℝ) < D.R.k := by
    have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
    nlinarith
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have : 0 < D.R.k := by exact_mod_cast hkpos
    exact_mod_cast Nat.one_le_of_lt this
  have hBpos : 0 < bN D ρ j := by linarith
  have hratio : Real.log (w j ρ) - Real.log (bN D ρ j) ≤ 1 / sc.x := by
    rw [← Real.log_div hw0.ne' hBpos.ne']
    have h1 := Real.log_le_sub_one_of_pos (div_pos hw0 hBpos)
    have h2 : w j ρ / bN D ρ j - 1 ≤ 1 / sc.x := by
      rw [div_sub_one hBpos.ne', div_le_div_iff₀ hBpos (by linarith)]
      have h4 := (abs_le.mp habs).2
      have h3 : (w j ρ - bN D ρ j) * sc.x ≤ bN D ρ j := by rwa [le_div_iff₀ (by linarith)] at h4
      linarith
    linarith
  have hlogW : Real.log (w j ρ) ≤ 2 * sc.L := by
    have h1 : Real.log (w j ρ) ≤ Real.log (2 * sc.b) := Real.log_le_log hw0 hwl
    have h2 : Real.log (2 * sc.b) = Real.log 2 + sc.L := by
      unfold Scale.b
      rw [Real.log_mul two_ne_zero (Real.exp_pos _).ne', Real.log_exp]
    have h3 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9
      linarith
    linarith
  have hx1 : 0 < 1 / sc.x := one_div_pos.mpr (by linarith)
  have hkx : ((D.R.k : ℝ) - 1) * (1 / sc.x) ≤ (D.R.k : ℝ) / sc.x := by
    have e : ((D.R.k : ℝ) - 1) * (1 / sc.x) = (D.R.k : ℝ) / sc.x - 1 / sc.x := by ring
    linarith
  have hmul : ((D.R.k : ℝ) - 1) * (Real.log (w j ρ) - Real.log (bN D ρ j)) ≤
      ((D.R.k : ℝ) - 1) * (1 / sc.x) :=
    mul_le_mul_of_nonneg_left hratio (by linarith)
  nlinarith

theorem place_dimension_lower_bound (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (h2k : Real.log (2 * (D.R.k : ℝ)) ≤ sc.L)
    (hx : 2 * (Real.log 8 + 1 + Real.log sc.x) ≤ sc.L) (u : D.what₂.Word) (ρ : D.what₂.Tau)
    (h3 : (2 / 3 : ℝ) * dimV (rowLam D ρ) ≤ D.dsig ρ) :
    Real.log (2 / 3) + ((D.R.k : ℝ) - 1) * ∑ j ∈ range D.R.m, Real.log (bN D ρ j) - 5 * D.R.k * sc.L ≤
      Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) := by
  have hP := place_data_under_section_B D sc C0 Δ w hB u ρ
  have hm2 := D.R.two_le_m
  have hk5 := D.R.m_add_three_le_k
  have hΔ : 1 ≤ Δ := by
    unfold DataB at hB
    exact hB.2.2.2.2.2.2.1
  have hx1 : (1 : ℝ) ≤ sc.x := sc.one_lt_alt.le
  obtain ⟨hvu, hvr, hVV⟩ := Formalism.LogVandermondeBounds.StandardLattice.VandPlace_holds sc.eps sc.x sc.eps_pos hx1 D.R.k D.R.m Δ
    (uN D u ρ) (vN D ρ) (bN D ρ) (fun j => w j ρ) (by omega) (by omega) hΔ hP
  have hfac : 0 < facProd D.R.r := Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  have hvandu : vand (uColR D u ρ) = Formalism.LogVandermondeBounds.StandardLattice.vandN (uN D u ρ) D.R.k := by
    rw [column_param_eq_fun, vandermonde_fin_eq_nat]
  have hdimrow : dimV (rowLam D ρ) =
      Formalism.LogVandermondeBounds.StandardLattice.vandN (Formalism.LogVandermondeBounds.StandardLattice.rowPar D.R.k (vN D ρ) (bN D ρ)) (D.R.k - 1 + D.R.m) /
        facProd D.R.r := by
    rw [dim_weyl_line_eq, rank_eq_sum]
    rfl
  set A := Formalism.LogVandermondeBounds.StandardLattice.vandN (Formalism.LogVandermondeBounds.StandardLattice.rowPar D.R.k (vN D ρ) (bN D ρ)) (D.R.k - 1 + D.R.m) with hAdef
  set U := Formalism.LogVandermondeBounds.StandardLattice.vandN (uN D u ρ) D.R.k with hUdef
  have hdsig : (2 / 3 : ℝ) * (A / facProd D.R.r) ≤ D.dsig ρ := by
    rw [← hdimrow]
    exact h3
  have hA' : (2 / 3 : ℝ) * A ≤ D.dsig ρ * facProd D.R.r := by
    have := mul_le_mul_of_nonneg_right hdsig hfac.le
    rwa [mul_assoc, div_mul_cancel₀ _ hfac.ne'] at this
  have hdivle : (2 / 3 : ℝ) * A / U ≤ D.dsig ρ * facProd D.R.r / U := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hA' (inv_nonneg.mpr hvu.le)
  have hlog1 := Real.log_le_log (div_pos (mul_pos (by norm_num) hvr) hvu) hdivle
  rw [Real.log_div (mul_pos (by norm_num) hvr).ne' hvu.ne', Real.log_mul (by norm_num) hvr.ne'] at hlog1
  have hLd : sc.L = sc.x ^ sc.eps := rfl
  have h8 : Real.log (8 * (sc.x * Real.exp (sc.x ^ sc.eps))) = Real.log 8 + Real.log sc.x + sc.L := by
    rw [Real.log_mul (by norm_num) (mul_pos (by linarith) (Real.exp_pos _)).ne',
      Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp, hLd]
    ring
  rw [h8] at hVV
  have hkpos : (0 : ℝ) < D.R.k := by exact_mod_cast (by omega : 0 < D.R.k)
  have hlogk : Real.log D.R.k ≤ sc.L := le_trans (Real.log_le_log hkpos (by linarith)) h2k
  have hm1 := mul_le_mul_of_nonneg_left hx hkpos.le
  have hm2' := mul_le_mul_of_nonneg_left hlogk hkpos.le
  rw [hvandu]
  linarith

theorem log_X_lower_arithmetic (F K Mm Lr lv l2v G SL SG SP SW X lo : ℝ)
    (hF : 1 ≤ F) (hM : 44 ≤ Mm) (hMK : Mm ≤ K) (hL : 1 ≤ Lr) (hlv0 : 0 ≤ lv) (hlv : lv ≤ Lr) (hl2v : l2v ≤ Lr)
    (hG : 0 ≤ G) (hSL : -(F * (Mm - 1)) ≤ SL) (hSG : -2 ≤ SG)
    (hSPW : F * (-1 - 5 * K * Lr - (K + 2 * K * Lr)) ≤ SP - K * SW)
    (hid : F * K * X = F * ((Mm - 1) * K + Mm * (Mm - 1) / 2) * lv - F * ((Mm - 1) / 2) * l2v + SL +
      F * (Mm * (2 * K + Mm - 1) / 2) * G + F * SG + SP)
    (hlo : F * K * lo = K * SW + F * K * Mm * lv + F * K * Mm * G - 11 * F * K * Lr) : lo ≤ X := by
  have hK : 0 < K := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hFK : 0 < F * K := mul_pos (by linarith) hK
  have hMM : 0 ≤ Mm * (Mm - 1) / 2 := by nlinarith
  have key : F * K * (X - lo) = F * (Mm * (Mm - 1) / 2) * lv - F * K * lv - F * ((Mm - 1) / 2) * l2v +
      SL + F * (Mm * (Mm - 1) / 2) * G + F * SG + (SP - K * SW) + 11 * F * K * Lr := by
    linear_combination hid - hlo
  have hQ : 0 ≤ 3 * K * Lr - (Mm - 1) / 2 * Lr - Mm - 2 - K := by
    nlinarith [mul_le_mul_of_nonneg_right hMK (by linarith : (0 : ℝ) ≤ Lr),
      mul_le_mul_of_nonneg_left hL (by linarith : (0 : ℝ) ≤ K),
      mul_le_mul_of_nonneg_left hL (by linarith : (0 : ℝ) ≤ Mm)]
  have h1 : 0 ≤ F * (Mm * (Mm - 1) / 2) * lv := mul_nonneg (mul_nonneg hF0 hMM) hlv0
  have h2 : F * K * lv ≤ F * K * Lr := mul_le_mul_of_nonneg_left hlv hFK.le
  have h3 : F * ((Mm - 1) / 2) * l2v ≤ F * ((Mm - 1) / 2) * Lr :=
    mul_le_mul_of_nonneg_left hl2v (mul_nonneg hF0 (by linarith))
  have h4 : 0 ≤ F * (Mm * (Mm - 1) / 2) * G := mul_nonneg (mul_nonneg hF0 hMM) hG
  have h5 : F * (-2) ≤ F * SG := mul_le_mul_of_nonneg_left hSG hF0
  have h6 : 0 ≤ F * (3 * K * Lr - (Mm - 1) / 2 * Lr - Mm - 2 - K) := mul_nonneg hF0 hQ
  have hpos : 0 ≤ F * K * (X - lo) := by
    rw [key]
    nlinarith
  by_contra hlt
  push_neg at hlt
  have : F * K * (X - lo) < 0 := mul_neg_of_pos_of_neg hFK (by linarith)
  linarith



end Formalism.MainNotions.StandardLattice
end
end

section
noncomputable section
namespace Formalism.MainNotions.StandardLattice
open NumberField Formalism.BasicNotions Finset

theorem exp_neg_r_le_third (D : D7) : Real.exp (-(D.R.r : ℝ)) ≤ 1 / 3 := by
  have hr : 2 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    first
      | (show 2 ≤ D.R.k + D.R.m - 1; omega)
      | omega
  have hr' : (2 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  calc Real.exp (-(D.R.r : ℝ)) ≤ Real.exp (-2) := Real.exp_le_exp.2 (by linarith)
    _ = 1 / Real.exp 2 := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) h3

theorem place_dimension_upper_bound (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (h3 : SigmaDegreeTwoSidedBoundOfGap D) (hgap : ∀ ρ, GapAtLeast (rowSgn D) (rowLam D ρ) (gap3 D 8192 (1 / 3)))
    (u : D.what₂.Word) (ρ : D.what₂.Tau) :
    Real.log (D.dsig ρ) - Real.log (dimV (uColR D u ρ)) ≤
      (D.R.k : ℝ) * D.R.m * (Real.log 3 + 5 * Real.log (2 * D.R.k) + 5 * sc.L + 10) := by
  have hk := D.R.k_ge
  have hm := D.R.two_le_m
  have hpl := place_data_under_section_B D sc C0 Δ w hB u ρ
  have b7 : 1 ≤ Δ := hB.2.2.2.2.2.2.1
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by
    exact_mod_cast (by have := D.R.m_add_three_le_k; omega : D.R.m ≤ D.R.k)
  have h := (h3 (1 / 3) (exp_neg_r_le_third D) (by norm_num) ρ
    (fun a b hab => le_trans (explicit_gap_le_general_gap D 8192 (1 / 3) le_rfl) (hgap ρ a b hab))).2
  rw [formal_degree_line_eq, count_plus_eq, count_minus_eq] at h
  obtain ⟨hd, hT, hlog⟩ := Formalism.LogVandermondeBounds.StandardLattice.UpperPlace_holds sc.eps sc.x sc.eps_pos sc.one_lt_alt.le D.R.k D.R.m Δ 3
      (uN D u ρ) (vN D ρ) (bN D ρ) (fun j => w j ρ) hm D.R.m_even (by omega) hmk b7 (by norm_num) hpl
      (fun i j hij hj => one_le_column_sub_of_lt D u ρ i j hij hj)
  have a1 := abs_param_sup_nonneg (rowLam D ρ)
  have a2 := abs_param_sup_le D ρ
  have hr1 : (1 : ℝ) ≤ ((D.R.k - 1 + D.R.m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ D.R.k - 1 + D.R.m)
  have h' : D.dsig ρ ≤ 4 * Formalism.LogVandermondeBounds.StandardLattice.dTau D.R.k D.R.m (Formalism.LogVandermondeBounds.StandardLattice.rowPar D.R.k (vN D ρ) (bN D ρ)) *
      (3 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ) * ((D.R.k - 1 + D.R.m : ℕ) : ℝ) *
        (vN D ρ 0 + bN D ρ (D.R.m - 1))) ^ ((D.R.k - 1 + D.R.m / 2) * (D.R.m / 2)) := by
    refine le_trans h ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have c0 : 0 ≤ 3 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ) := by positivity
    calc 3 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ) * lamAbs (rowLam D ρ)
        ≤ 3 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ) * (vN D ρ 0 + bN D ρ (D.R.m - 1)) :=
          mul_le_mul_of_nonneg_left a2 c0
      _ = 3 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ) * 1 * (vN D ρ 0 + bN D ρ (D.R.m - 1)) := by ring
      _ ≤ 3 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ) * ((D.R.k - 1 + D.R.m : ℕ) : ℝ) *
          (vN D ρ 0 + bN D ρ (D.R.m - 1)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr1 c0) (le_trans a1 a2)
  rw [dim_weyl_column_eq]
  have h4 := Real.log_le_log (D.dsig_pos ρ) h'
  have eL : sc.L = sc.x ^ sc.eps := rfl
  rw [eL]
  linarith

theorem facProd_pos' (N : ℕ) : 0 < facProd N :=
  Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i

theorem log_factorial_product_difference (k r : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r) :
    Real.log (facProd r) - Real.log (facProd k) ≤ ((r - k : ℕ) : ℝ) * ((r : ℝ) * Real.log r) := by
  have hsplit : facProd r = facProd k * ∏ i ∈ Finset.Ico k r, ((i.factorial : ℕ) : ℝ) := by
    unfold facProd
    rw [Finset.prod_range_mul_prod_Ico _ hkr]
  have hk0 : 0 < facProd k := facProd_pos' k
  have hP0 : 0 < ∏ i ∈ Finset.Ico k r, ((i.factorial : ℕ) : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  rw [hsplit, Real.log_mul hk0.ne' hP0.ne', add_sub_cancel_left,
    Real.log_prod (fun i _ => by exact_mod_cast (Nat.factorial_pos i).ne')]
  calc ∑ i ∈ Finset.Ico k r, Real.log ((i.factorial : ℕ) : ℝ)
      ≤ ∑ i ∈ Finset.Ico k r, ((r : ℝ) * Real.log r) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hir : i ≤ r := (Finset.mem_Ico.mp hi).2.le
        have h1 : ((i.factorial : ℕ) : ℝ) ≤ (r : ℝ) ^ r := by
          exact_mod_cast (Nat.factorial_le_pow i).trans
            ((Nat.pow_le_pow_left hir i).trans (Nat.pow_le_pow_right (by omega) hir))
        calc Real.log ((i.factorial : ℕ) : ℝ) ≤ Real.log ((r : ℝ) ^ r) :=
              Real.log_le_log (by exact_mod_cast Nat.factorial_pos i) h1
          _ = (r : ℝ) * Real.log r := by rw [Real.log_pow]
    _ = ((r - k : ℕ) : ℝ) * ((r : ℝ) * Real.log r) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]

theorem log_X_upper_arithmetic (f k m L CY lv l2v SL lg S5 S6 X : ℝ) (hf : 0 < f) (hk : 5 ≤ k) (hm : 44 ≤ m) (hmk : m ≤ k)
    (hL : 9 ≤ L) (hlv0 : 0 ≤ lv) (hlv : lv ≤ L) (h2v : 0 ≤ l2v) (hSL : SL ≤ f * m) (hlg0 : 0 ≤ lg)
    (hlg : lg ≤ 2 * CY * L) (hS5 : S5 ≤ 0)
    (hS6 : S6 ≤ f * (k * m * (2 + 5 * L + 5 * L + 10) + m * (2 * k * L)))
    (id : f * k * X = f * ((m - 1) * k + m * (m - 1) / 2) * lv - f * ((m - 1) / 2) * l2v + SL +
      f * (m * (2 * k + m - 1) / 2) * lg + f * S5 + S6) :
    X ≤ (15 + 3 * CY) * m * L := by
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  have hL0 : 0 < L := by linarith
  have hCY : 0 ≤ CY := by
    by_contra h
    push_neg at h
    have : 2 * CY * L < 0 := by nlinarith
    linarith
  have ht1 : f * ((m - 1) * k + m * (m - 1) / 2) * lv ≤ f * ((m - 1) * k + m * (m - 1) / 2) * L :=
    mul_le_mul_of_nonneg_left hlv (by have : 0 ≤ (m - 1) * k := by nlinarith
                                      have : 0 ≤ m * (m - 1) / 2 := by nlinarith
                                      positivity)
  have ht2 : 0 ≤ f * ((m - 1) / 2) * l2v := by
    have : 0 ≤ (m - 1) / 2 := by linarith
    positivity
  have ht4 : f * (m * (2 * k + m - 1) / 2) * lg ≤ f * (m * (2 * k + m - 1) / 2) * (2 * CY * L) :=
    mul_le_mul_of_nonneg_left hlg (by have : 0 ≤ m * (2 * k + m - 1) / 2 := by nlinarith
                                      positivity)
  have ht5 : f * S5 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hf.le hS5
  have hsum : f * k * X ≤ f * (((m - 1) * k + m * (m - 1) / 2) * L + m +
      m * (2 * k + m - 1) * CY * L + k * m * (12 + 12 * L)) := by
    rw [id]
    nlinarith
  have hpoly : ((m - 1) * k + m * (m - 1) / 2) * L + m + m * (2 * k + m - 1) * CY * L +
      k * m * (12 + 12 * L) ≤ k * ((15 + 3 * CY) * m * L) := by
    have a1 : 0 ≤ CY * L * m * (k - m + 1) := by
      have : 0 ≤ k - m + 1 := by linarith
      positivity
    have a2 : 0 ≤ k * m * (L - 9) := by
      have : 0 ≤ L - 9 := by linarith
      positivity
    have a3 : 0 ≤ m * (k - m) * L := by
      have : 0 ≤ k - m := by linarith
      positivity
    have a4 : 0 ≤ k * L := by positivity
    have a5 : m ≤ k * m * L := by nlinarith
    nlinarith
  have hfk : 0 < f * k := mul_pos hf hk0
  have : f * k * X ≤ f * k * ((15 + 3 * CY) * m * L) := by
    calc f * k * X ≤ f * (((m - 1) * k + m * (m - 1) / 2) * L + m +
          m * (2 * k + m - 1) * CY * L + k * m * (12 + 12 * L)) := hsum
      _ ≤ f * (k * ((15 + 3 * CY) * m * L)) := mul_le_mul_of_nonneg_left hpoly hf.le
      _ = f * k * ((15 + 3 * CY) * m * L) := by ring
  exact le_of_mul_le_mul_left this hfk


end Formalism.MainNotions.StandardLattice
end
end

section
noncomputable section
namespace Formalism.MainNotions.StandardLattice
open NumberField Formalism.BasicNotions Finset

theorem abs_log_sub_le_div (X X' e c : ℝ) (hc : 0 < c) (hX : c ≤ X) (hX' : c ≤ X') (he : |X - X'| ≤ e) :
    |Real.log X - Real.log X'| ≤ e / c := by
  have he0 : 0 ≤ e := le_trans (abs_nonneg _) he
  have key : ∀ A B : ℝ, c ≤ A → c ≤ B → A - B ≤ e → Real.log A - Real.log B ≤ e / c := by
    intro A B hA hB hAB
    have hA0 : 0 < A := lt_of_lt_of_le hc hA
    have hB0 : 0 < B := lt_of_lt_of_le hc hB
    rw [← Real.log_div hA0.ne' hB0.ne']
    have h1 := Real.log_le_sub_one_of_pos (div_pos hA0 hB0)
    rw [div_sub_one hB0.ne'] at h1
    rcases le_total (A - B) 0 with hn | hn
    · have h2 : (A - B) / B ≤ 0 := div_nonpos_of_nonpos_of_nonneg hn hB0.le
      have h3 : 0 ≤ e / c := div_nonneg he0 hc.le
      linarith
    · have h2 : (A - B) / B ≤ (A - B) / c := div_le_div_of_nonneg_left hn hc hB
      have h3 : (A - B) / c ≤ e / c := div_le_div_of_nonneg_right hAB hc.le
      linarith
  have h := abs_le.mp he
  rw [abs_le]
  constructor
  · have := key X' X hX' hX (by linarith [h.1])
    linarith
  · exact key X X' hX hX' (by linarith [h.2])

theorem harmonic_gap_sum_le (k : ℕ) (a : Fin k) :
    ∑ b ∈ univ.filter (fun b : Fin k => a < b), (1 : ℝ) / ((b.val : ℝ) - (a.val : ℝ)) ≤ 1 + Real.log k := by
  have e : (∑ b ∈ univ.filter (fun b : Fin k => a < b), (1 : ℝ) / ((b.val : ℝ) - (a.val : ℝ))) =
      ∑ i ∈ range k, (if a.val < i then (1 : ℝ) / ((i : ℝ) - (a.val : ℝ)) else 0) := by
    rw [Finset.sum_filter, ← Fin.sum_univ_eq_sum_range
      (fun i => if a.val < i then (1 : ℝ) / ((i : ℝ) - (a.val : ℝ)) else 0) k]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    try dsimp only
    by_cases h : a < b
    · rw [if_pos h, if_pos (show a.val < b.val from h)]
    · rw [if_neg h, if_neg (show ¬ a.val < b.val from h)]
  obtain ⟨m, hm⟩ : ∃ m, k = (a.val + 1) + m := ⟨k - (a.val + 1), by have := a.isLt; omega⟩
  have hr : range k = range ((a.val + 1) + m) := congrArg range hm
  rw [e, hr, Finset.sum_range_add]
  have h1 : ∑ i ∈ range (a.val + 1), (if a.val < i then (1 : ℝ) / ((i : ℝ) - (a.val : ℝ)) else 0) = 0 :=
    Finset.sum_eq_zero (fun i hi => if_neg (by have := Finset.mem_range.mp hi; omega))
  have h2 : ∑ x ∈ range m, (if a.val < a.val + 1 + x then
      (1 : ℝ) / (((a.val + 1 + x : ℕ) : ℝ) - (a.val : ℝ)) else 0) =
      ∑ x ∈ range m, (1 : ℝ) / ((x : ℝ) + 1) :=
    Finset.sum_congr rfl (fun x _ => by
      rw [if_pos (show a.val < a.val + 1 + x by omega)]
      push_cast
      congr 1
      ring)
  rw [h1, zero_add, h2]
  have h3 : ∑ x ∈ range m, (1 : ℝ) / ((x : ℝ) + 1) ≤ ∑ x ∈ range k, (1 : ℝ) / ((x : ℝ) + 1) :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega))
      (fun i _ _ => by positivity)
  have h4 : ∑ x ∈ range k, (1 : ℝ) / ((x : ℝ) + 1) = (harmonic k : ℝ) := by
    simp [harmonic]
  have h5 := harmonic_le_one_add_log k
  linarith

theorem log_vandermonde_variation_of_separated (k : ℕ) (Δ : ℝ) (u u' : Fin k → ℝ) (h0 : 0 < Δ)
    (G0 : ∀ a b : Fin k, a.val = 0 → a < b → (k : ℝ) * (4 * Δ) ≤ u a - u b ∧ (k : ℝ) * (4 * Δ) ≤ u' a - u' b ∧
      |(u a - u b) - (u' a - u' b)| ≤ Δ)
    (G1 : ∀ a b : Fin k, 1 ≤ a.val → a < b → 3 * ((b.val : ℝ) - (a.val : ℝ)) * Δ ≤ u a - u b ∧
      3 * ((b.val : ℝ) - (a.val : ℝ)) * Δ ≤ u' a - u' b ∧ |(u a - u b) - (u' a - u' b)| ≤ 2 * Δ) :
    |Real.log (vand u) - Real.log (vand u')| ≤ 1 / 4 + 2 / 3 * k * (1 + Real.log k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · norm_num [vand]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := hkR.ne'
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_natCast_nonneg k
  have hpair : ∀ a b : Fin k, a < b →
      0 < u a - u b ∧ 0 < u' a - u' b ∧
      |Real.log (u a - u b) - Real.log (u' a - u' b)| ≤
        (if a.val = 0 then 1 / (4 * (k : ℝ)) else 2 / 3 * (1 / ((b.val : ℝ) - (a.val : ℝ)))) := by
    intro a b hab
    by_cases ha : a.val = 0
    · obtain ⟨h1, h2, h3⟩ := G0 a b ha hab
      have hc : 0 < (k : ℝ) * (4 * Δ) := mul_pos hkR (by linarith)
      refine ⟨by linarith, by linarith, ?_⟩
      rw [if_pos ha]
      have h4 := abs_log_sub_le_div (u a - u b) (u' a - u' b) Δ ((k : ℝ) * (4 * Δ)) hc h1 h2 h3
      have h5 : Δ / ((k : ℝ) * (4 * Δ)) = 1 / (4 * (k : ℝ)) := by
        rw [div_eq_div_iff hc.ne' (mul_ne_zero (by norm_num) hk0)]
        ring
      linarith
    · have ha1 : 1 ≤ a.val := Nat.one_le_iff_ne_zero.mpr ha
      obtain ⟨h1, h2, h3⟩ := G1 a b ha1 hab
      have hab' : a.val < b.val := hab
      have hab'' : (a.val : ℝ) < (b.val : ℝ) := by exact_mod_cast hab'
      have hba : (0 : ℝ) < (b.val : ℝ) - (a.val : ℝ) := by linarith
      have hc : 0 < 3 * ((b.val : ℝ) - (a.val : ℝ)) * Δ := mul_pos (mul_pos (by norm_num) hba) h0
      refine ⟨by linarith, by linarith, ?_⟩
      rw [if_neg ha]
      have h4 := abs_log_sub_le_div (u a - u b) (u' a - u' b) (2 * Δ) (3 * ((b.val : ℝ) - (a.val : ℝ)) * Δ)
        hc h1 h2 h3
      have h5 : 2 * Δ / (3 * ((b.val : ℝ) - (a.val : ℝ)) * Δ) =
          2 / 3 * (1 / ((b.val : ℝ) - (a.val : ℝ))) := by
        have hx : (1 / ((b.val : ℝ) - (a.val : ℝ))) * ((b.val : ℝ) - (a.val : ℝ)) = 1 :=
          one_div_mul_cancel hba.ne'
        rw [div_eq_iff hc.ne']
        linear_combination (-2 * Δ) * hx
      linarith
  have hlog : ∀ v : Fin k → ℝ, (∀ a b : Fin k, a < b → 0 < v a - v b) →
      Real.log (vand v) = ∑ a : Fin k, ∑ b ∈ univ.filter (fun b => a < b), Real.log (v a - v b) := by
    intro v hv
    simp only [vand]
    rw [Real.log_prod (fun a _ =>
      (Finset.prod_pos (fun b hb => hv a b (Finset.mem_filter.mp hb).2)).ne')]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact Real.log_prod (fun b hb => (hv a b (Finset.mem_filter.mp hb).2).ne')
  have hrow : ∀ a : Fin k, ∑ b ∈ univ.filter (fun b => a < b),
      (if a.val = 0 then 1 / (4 * (k : ℝ)) else 2 / 3 * (1 / ((b.val : ℝ) - (a.val : ℝ)))) ≤
      (if a.val = 0 then (1 : ℝ) / 4 else 0) + 2 / 3 * (1 + Real.log k) := by
    intro a
    by_cases ha : a.val = 0
    · simp only [if_pos ha]
      rw [Finset.sum_const, nsmul_eq_mul]
      have hc : ((univ.filter (fun b : Fin k => a < b)).card : ℝ) ≤ k := by
        have := Finset.card_filter_le (univ : Finset (Fin k)) (fun b => a < b)
        rw [Finset.card_univ, Fintype.card_fin] at this
        exact_mod_cast this
      have h4 : (k : ℝ) * (1 / (4 * (k : ℝ))) = 1 / 4 := by
        rw [mul_one_div, div_eq_iff (mul_ne_zero (by norm_num) hk0)]
        ring
      have h5 : 0 ≤ 1 / (4 * (k : ℝ)) := by positivity
      have h6 := mul_le_mul_of_nonneg_right hc h5
      linarith
    · simp only [if_neg ha]
      rw [← Finset.mul_sum, zero_add]
      exact mul_le_mul_of_nonneg_left (harmonic_gap_sum_le k a) (by norm_num)
  have hS : ∑ a : Fin k, ((if a.val = 0 then (1 : ℝ) / 4 else 0) + 2 / 3 * (1 + Real.log k)) ≤
      1 / 4 + 2 / 3 * k * (1 + Real.log k) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hc1 : ((univ.filter (fun a : Fin k => a.val = 0)).card : ℝ) ≤ 1 := by
      have : (univ.filter (fun a : Fin k => a.val = 0)).card ≤ 1 :=
        Finset.card_le_one.mpr (fun x hx y hy =>
          Fin.ext ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm))
      exact_mod_cast this
    linarith
  rw [hlog u (fun a b h => (hpair a b h).1), hlog u' (fun a b h => (hpair a b h).2.1)]
  simp only [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _)) ?_
  refine le_trans (Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b hb =>
    (hpair a b (Finset.mem_filter.mp hb).2).2.2))) ?_
  refine le_trans (Finset.sum_le_sum (fun a _ => hrow a)) ?_
  exact hS

theorem vandermonde_variation_at_place (D : D7) (sc : Scale) (C0 CY Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hA : DataA D sc C0 CY Δ w)
    (u u' : D.what₂.Word) (ρ : D.what₂.Tau) :
    |Real.log (vand (uColR D u ρ)) - Real.log (vand (uColR D u' ρ))| ≤
      1 / 4 + 2 / 3 * D.R.k * (1 + Real.log D.R.k) := by
  obtain ⟨⟨-, -, -, -, -, -, hΔ1, hv, hvstep, hmid, -, hnt, -⟩, ⟨-, -, hm44, hmk, -, -, -, htop⟩⟩ := hA
  have hk44 : 44 ≤ D.R.k := le_trans hm44 hmk
  have hkpos : 0 < D.R.k := by omega
  have h0 : 0 < Δ := by linarith
  have hK : (44 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast hk44
  have hu : ∀ w (i : Fin D.R.k), uColR D w ρ i = uN D w ρ i.val := by
    intro w i
    simp [uColR, uN]
  have hfirst : uN D u ρ 0 = uN D u' ρ 0 := by
    have h := (D.hcW_first u ρ hkpos).trans (D.hcW_first u' ρ hkpos).symm
    simp only [uN, dif_pos hkpos]
    exact congrArg (fun q : ℚ => (q : ℝ)) h
  have hlast : uN D u ρ (D.R.k - 1) = uN D u' ρ (D.R.k - 1) := by
    have h1 : D.R.k - 1 < D.R.k := by omega
    have h := (D.hcW_last u ρ hkpos).trans (D.hcW_last u' ρ hkpos).symm
    simp only [uN, dif_pos h1]
    exact congrArg (fun q : ℚ => (q : ℝ)) h
  have hchain : ∀ i j : ℕ, i ≤ j → j < D.R.k - 1 →
      vN D ρ i - vN D ρ j = 4 * Δ * ((j : ℝ) - (i : ℝ)) := by
    intro i j
    induction j with
    | zero =>
      intro hij _
      have : i = 0 := by omega
      subst this
      simp
    | succ n ih =>
      intro hij hj
      rcases Nat.eq_or_lt_of_le hij with h | h
      · subst h
        simp
      · have h1 := ih (by omega) (by omega)
        have h2 := hvstep ρ n (by omega)
        push_cast
        linarith
  have hV0 : 0 ≤ vN D ρ 0 := (hv ρ 0 (by omega)).1
  have hmidR : ∀ w l, 1 ≤ l → l ≤ D.R.k - 2 →
      vN D ρ 0 - 4 * Δ * ((l : ℝ) - 1) - 1 / 2 - Δ ≤ uN D w ρ l ∧
      uN D w ρ l ≤ vN D ρ 0 - 4 * Δ * ((l : ℝ) - 1) - 1 / 2 := by
    intro w l h1 h2
    have hc := hchain 0 (l - 1) (by omega) (by omega)
    rw [Nat.cast_sub h1, Nat.cast_one, Nat.cast_zero] at hc
    rcases hmid w ρ l h1 h2 with h | h <;> exact ⟨by linarith, by linarith⟩
  have hVl : ∀ l, 1 ≤ l → l ≤ D.R.k - 2 → 4 * Δ * ((l : ℝ) - 1) ≤ vN D ρ 0 := by
    intro l h1 h2
    have hc := hchain 0 (l - 1) (by omega) (by omega)
    rw [Nat.cast_sub h1, Nat.cast_one, Nat.cast_zero] at hc
    have := (hv ρ (l - 1) (by omega)).1
    linarith
  have hK2 : ((D.R.k - 2 : ℕ) : ℝ) = (D.R.k : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hK1 : ((D.R.k - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hlastR : ∀ w, ¬ IsTop D ρ →
      uN D w ρ (D.R.k - 1) = vN D ρ 0 - 4 * Δ * ((D.R.k : ℝ) - 2) - 1 / 2 := by
    intro w hT
    have hc := hchain 0 (D.R.k - 2) (by omega) (by omega)
    rw [hK2, Nat.cast_zero] at hc
    rw [(hnt w ρ hT).2.2]
    linarith
  have hu0 : ∀ w, (D.R.k : ℝ) * (4 * Δ) ≤ uN D w ρ 0 - vN D ρ 0 := by
    intro w
    by_cases hT : IsTop D ρ
    · exact (htop w ρ hT).1
    · exact (hnt w ρ hT).1
  have hKΔ : 0 ≤ (D.R.k : ℝ) * (4 * Δ) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  refine log_vandermonde_variation_of_separated D.R.k Δ _ _ h0 ?_ ?_
  · intro a b ha hab
    simp only [hu]
    rw [ha]
    have hab' : a.val < b.val := hab
    have hb := b.isLt
    have hb1 : (1 : ℝ) ≤ (b.val : ℝ) := by exact_mod_cast (show 1 ≤ b.val by omega)
    have hub : ∀ w, uN D w ρ b.val ≤ vN D ρ 0 := by
      intro w
      rcases Nat.lt_or_ge b.val (D.R.k - 1) with hj | hj
      · have h1 := (hmidR w b.val (by omega) (by omega)).2
        have hp : 0 ≤ Δ * ((b.val : ℝ) - 1) := mul_nonneg h0.le (by linarith)
        linarith
      · have hbe : b.val = D.R.k - 1 := by omega
        rw [hbe]
        by_cases hT : IsTop D ρ
        · have := (htop w ρ hT).2
          linarith
        · rw [hlastR w hT]
          have hp : 0 ≤ Δ * ((D.R.k : ℝ) - 2) := mul_nonneg h0.le (by linarith)
          linarith
    have hdiff : |uN D u' ρ b.val - uN D u ρ b.val| ≤ Δ := by
      rcases Nat.lt_or_ge b.val (D.R.k - 1) with hj | hj
      · have h1 := hmidR u b.val (by omega) (by omega)
        have h2 := hmidR u' b.val (by omega) (by omega)
        rw [abs_le]
        constructor <;> linarith
      · have hbe : b.val = D.R.k - 1 := by omega
        rw [hbe, hlast, sub_self, abs_zero]
        linarith
    refine ⟨by linarith [hu0 u, hub u], by linarith [hu0 u', hub u'], ?_⟩
    have e3 : (uN D u ρ 0 - uN D u ρ b.val) - (uN D u' ρ 0 - uN D u' ρ b.val) =
        uN D u' ρ b.val - uN D u ρ b.val := by
      rw [hfirst]
      ring
    rw [e3]
    exact hdiff
  · intro a b ha hab
    simp only [hu]
    have hab' : a.val < b.val := hab
    have hb := b.isLt
    have hai : (1 : ℝ) ≤ (a.val : ℝ) := by exact_mod_cast ha
    have hji : (a.val : ℝ) + 1 ≤ (b.val : ℝ) := by
      have := Nat.succ_le_of_lt hab'
      exact_mod_cast this
    have hA1 := hmidR u a.val ha (by omega)
    have hA2 := hmidR u' a.val ha (by omega)
    have hVa := hVl a.val ha (by omega)
    rcases Nat.lt_or_ge b.val (D.R.k - 1) with hj | hj
    · have hB1 := hmidR u b.val (by omega) (by omega)
      have hB2 := hmidR u' b.val (by omega) (by omega)
      have hp : 0 ≤ Δ * ((b.val : ℝ) - (a.val : ℝ) - 1) := mul_nonneg h0.le (by linarith)
      refine ⟨by linarith, by linarith, ?_⟩
      rw [abs_le]
      constructor <;> linarith
    · have hbe : b.val = D.R.k - 1 := by omega
      rw [hbe] at hji ⊢
      rw [hK1] at hji ⊢
      have hd : |uN D u ρ a.val - uN D u' ρ a.val| ≤ Δ := by
        rw [abs_le]
        constructor <;> linarith
      have e3 : (uN D u ρ a.val - uN D u ρ (D.R.k - 1)) - (uN D u' ρ a.val - uN D u' ρ (D.R.k - 1)) =
          uN D u ρ a.val - uN D u' ρ a.val := by
        rw [hlast]
        ring
      by_cases hT : IsTop D ρ
      · have hL1 := (htop u ρ hT).2
        have hL2 := (htop u' ρ hT).2
        have hp2 : ((D.R.k : ℝ) - 1) * 1 ≤ ((D.R.k : ℝ) - 1) * Δ :=
          mul_le_mul_of_nonneg_left hΔ1 (by linarith)
        have hp3 : 0 ≤ Δ * ((a.val : ℝ) - 1) := mul_nonneg h0.le (by linarith)
        refine ⟨by linarith, by linarith, ?_⟩
        rw [e3]
        linarith
      · have hL1 := hlastR u hT
        have hL2 := hlastR u' hT
        have hp : 0 ≤ Δ * ((D.R.k : ℝ) - 2 - (a.val : ℝ)) := mul_nonneg h0.le (by linarith)
        refine ⟨by linarith, by linarith, ?_⟩
        rw [e3]
        linarith

theorem vandermonde_variation_holds (D : D7) (sc : Scale) (C0 CY : ℝ) : VandermondeVariationExplicitBound D sc C0 CY := by
  unfold VandermondeVariationExplicitBound
  intro Δ w hA
  have hlogk : 0 ≤ Real.log (D.R.k : ℝ) := Real.log_natCast_nonneg _
  have hkpos : 0 < D.R.k := by
    have := D.R.m_add_three_le_k
    omega
  have hkR : (0 : ℝ) < D.R.k := by exact_mod_cast hkpos
  have hkk : 0 ≤ (D.R.k : ℝ) * (1 + Real.log D.R.k) := mul_nonneg hkR.le (by linarith)
  have hplace := fun u u' ρ => vandermonde_variation_at_place D sc C0 CY Δ w hA u u' ρ
  refine ⟨fun u u' ρ => le_trans (hplace u u' ρ) (by linarith), ?_⟩
  intro u u'
  have hdec : ∀ (x : D.what₂.Word) (ρ : D.what₂.Tau) (i j : ℕ) (hi : i < D.R.k) (hj : j < D.R.k), i < j →
      (((D.hcW x ρ).u ⟨j, hj⟩ : ℚ) : ℝ) < (((D.hcW x ρ).u ⟨i, hi⟩ : ℚ) : ℝ) := by
    intro x ρ i j
    induction j with
    | zero =>
      intro _ _ h
      omega
    | succ n ih =>
      intro hi hj h
      have h1 := (D.hcW x ρ).v_gt_u ⟨n, by omega⟩
      have h2 := (D.hcW x ρ).u_gt_v ⟨n, by omega⟩
      have h3 := h1.trans h2
      have step : (((D.hcW x ρ).u ⟨n + 1, hj⟩ : ℚ) : ℝ) < (((D.hcW x ρ).u ⟨n, by omega⟩ : ℚ) : ℝ) := by
        exact_mod_cast h3
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
      · exact step.trans (ih hi (by omega) h')
      · subst h'
        exact step
  have hvpos : ∀ (x : D.what₂.Word) (ρ : D.what₂.Tau), 0 < vand (uColR D x ρ) := by
    intro x ρ
    simp only [vand]
    refine Finset.prod_pos (fun a _ => Finset.prod_pos (fun b hb => ?_))
    have hab : a < b := (Finset.mem_filter.mp hb).2
    simp only [uColR]
    exact sub_pos.mpr (hdec x ρ a.val b.val a.isLt b.isLt hab)
  have hdu : ∀ x, duStarU D x = (massI D D.R.k * idxPi D (D.host.g 0) (D.host.g 1) /
      ∏ ρ : D.what₂.Tau, facProd D.R.k) * ∏ ρ, vand (uColR D x ρ) := by
    intro x
    simp only [duStarU, duStarP, dimV]
    rw [Finset.prod_div_distrib]
    ring
  have hsum : |Real.log (∏ ρ, vand (uColR D u ρ)) - Real.log (∏ ρ, vand (uColR D u' ρ))| ≤
      (D.R.f : ℝ) * (1 / 4 + 2 / 3 * D.R.k * (1 + Real.log D.R.k)) := by
    rw [Real.log_prod (fun ρ _ => (hvpos u ρ).ne'), Real.log_prod (fun ρ _ => (hvpos u' ρ).ne'),
      ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun ρ _ => hplace u u' ρ)) ?_
    rw [Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]
  have hkey : ∀ (Ds K P P' : ℝ), 0 < P → 0 < P' →
      |Real.log (Ds / (K * P)) - Real.log (Ds / (K * P'))| ≤ |Real.log P - Real.log P'| := by
    intro Ds K P P' hP hP'
    by_cases hD : Ds = 0
    · simp [hD]
    by_cases hK : K = 0
    · simp [hK]
    rw [Real.log_div hD (mul_ne_zero hK hP.ne'), Real.log_div hD (mul_ne_zero hK hP'.ne'),
      Real.log_mul hK hP.ne', Real.log_mul hK hP'.ne', abs_sub_comm (Real.log P)]
    apply le_of_eq
    congr 1
    ring
  simp only [logXuD, logXu]
  rw [hdu u, hdu u', ← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((D.R.f : ℝ) * D.R.k))]
  refine le_trans (mul_le_mul_of_nonneg_left (le_trans (hkey _ _ _ _
    (Finset.prod_pos (fun ρ _ => hvpos u ρ)) (Finset.prod_pos (fun ρ _ => hvpos u' ρ))) hsum)
    (by positivity)) ?_
  rcases Nat.eq_zero_or_pos D.R.f with hf0 | hf0
  · rw [hf0]
    simp only [Nat.cast_zero, zero_mul, div_zero]
    have : 0 ≤ 2 / (D.R.k : ℝ) := by positivity
    linarith
  · have hfR : (0 : ℝ) < D.R.f := by exact_mod_cast hf0
    rw [div_mul_eq_mul_div, one_mul, mul_div_mul_left _ _ hfR.ne', div_le_iff₀ hkR]
    have h2 : 2 / (D.R.k : ℝ) * D.R.k = 2 := div_mul_cancel₀ 2 hkR.ne'
    have h3 := mul_nonneg hkR.le hlogk
    nlinarith

end Formalism.MainNotions.StandardLattice
end
end

section
noncomputable section
namespace Formalism.MainNotions.StandardLattice
open NumberField Formalism.BasicNotions Finset



end Formalism.MainNotions.StandardLattice
end
end
