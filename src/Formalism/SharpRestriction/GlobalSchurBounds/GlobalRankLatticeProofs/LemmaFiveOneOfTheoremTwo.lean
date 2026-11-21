import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeOfExplicitAndCompact
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate

section
noncomputable section
namespace Formalism.MainNotions.StandardLattice
open NumberField Formalism.BasicNotions Finset


section P3
open Formalism.MainNotions.S MeasureTheory
open scoped InnerProductSpace

theorem signature_counts_ge_one (D : D7) : 1 ≤ pY D ∧ 1 ≤ qY D := by
  unfold pY qY
  simp only [Formalism.BasicNotions.Ranks.sigY0]
  have := D.R.m_add_three_le_k
  constructor <;> omega

theorem theorem_three_sigma_holds (D : D7) : SigmaDegreeBoundOfDiscreteSeriesBounds D := by
  intro hAll hT hEx ep0 he1 he2 ρ hgap
  obtain ⟨H, i1, i2, σ, hDS, hF⟩ := hEx ρ
  have hcs : CompleteSpace H := hDS.1
  have hnt : Nontrivial H := hDS.2.1
  obtain ⟨w, hw⟩ := exists_ne (0 : H)
  have hHC := line_param_harish_chandra D ρ
  have hdt := (hT _ (epsSH D.R) (lamSH D.R (D.hc ρ)) hHC H σ hDS).2
  have hp : ((Finset.univ.filter (fun a => epsSH D.R a = true)).card : ℝ) = (pY D : ℝ) := by
    have : (Finset.univ.filter (fun a => epsSH D.R a = true)).card = nPlus (epsSH D.R) := rfl
    rw [this, sign_vector_eq_line_sign, count_plus_finCast, count_plus_line_sign]
  have hq : ((Finset.univ.filter (fun a => epsSH D.R a = false)).card : ℝ) = (qY D : ℝ) := by
    have : (Finset.univ.filter (fun a => epsSH D.R a = false)).card = nMinus (epsSH D.R) := rfl
    rw [this, sign_vector_eq_line_sign, count_minus_finCast, count_minus_line_sign]
  have hN : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = (D.R.r : ℝ) := by rw [dimS_eq]
  have hg' : Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamSH D.R (D.hc ρ)) (spectralGapLowerBound D ep0) := by
    rw [sign_vector_eq_line_sign, param_vector_eq_line_param]; exact gapAtLeast_finCast _ _ _ _ hgap
  have key := hAll _ (epsSH D.R) (lamSH D.R (D.hc ρ)) ep0 (spectralGapLowerBound D ep0) H σ w
    (by rw [hp]; exact_mod_cast (signature_counts_ge_one D).1) (by rw [hq]; exact_mod_cast (signature_counts_ge_one D).2) hHC hg'
    (by rw [hN]; exact he1) he2
    (by rw [hp, hq, hN]; unfold spectralGapLowerBound; rw [Nat.cast_min]) hDS hw
  rw [formal_degree_of_eq _ σ _ hF w hw, hp, hq, hdt] at key
  rw [← dimV_eq_fdegHC _ hHC.1] at key
  rw [sign_vector_eq_line_sign, param_vector_eq_line_param, dim_weyl_finCast, formal_degree_finCast, abs_param_sup_finCast] at key
  refine ⟨key.1, ?_⟩
  have e : ((pY D : ℝ) * (qY D : ℝ)) = ((pY D * qY D : ℕ) : ℝ) := by push_cast; rfl
  rw [e, Real.rpow_natCast] at key
  exact key.2


end P3

theorem explicit_gap_le_general_gap (D : D7) (C ep0 : ℝ) (hC : 8192 ≤ C) : spectralGapLowerBound D ep0 ≤ gap3 D C ep0 := by
  unfold spectralGapLowerBound gap3
  have hr1 : (1 : ℝ) ≤ D.R.r := by
    have : 1 ≤ D.R.r := by
      simp only [Formalism.BasicNotions.Ranks.r]
      have := D.R.m_add_three_le_k
      omega
    exact_mod_cast this
  have hlog : 0 ≤ Real.log D.R.r := Real.log_nonneg hr1
  have hX : 0 ≤ (↑(min (pY D) (qY D)) : ℝ) * (↑(pY D) * ↑(qY D)) ^ 3 := by positivity
  apply div_le_div_of_nonneg_right ?_ (sq_nonneg ep0)
  have h1 : (8192 : ℝ) ≤ C * D.R.r := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (mul_nonneg hX hlog)]

theorem theorem_three_sigma_of_explicit (D : D7) (C : ℝ) (hC : 8192 ≤ C) (h : SigmaDegreeTwoSidedBoundOfGap D) : PointsLemma D C := by
  intro ep0 h1 h2 ρ hg
  obtain ⟨hA, hB⟩ := h ep0 h1 h2 ρ (fun a b hab => (explicit_gap_le_general_gap D C ep0 hC).trans (hg a b hab))
  refine ⟨hA, hB.trans ?_⟩
  have hr1 : (1 : ℝ) ≤ D.R.r := by
    have : 1 ≤ D.R.r := by
      simp only [Formalism.BasicNotions.Ranks.r]
      have := D.R.m_add_three_le_k
      omega
    exact_mod_cast this
  have hd := (formalDegreeFactor_pos_of_strictAnti (rowSgn D) (rowLam D ρ) (line_param_strictAnti D ρ)).le
  have hl := lamAbs_nonneg (rowLam D ρ)
  have hpq : (0 : ℝ) ≤ (pY D : ℝ) * (qY D : ℝ) := by positivity
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  apply pow_le_pow_left₀ (by positivity)
  have h3 : (3 : ℝ) ≤ C * D.R.r := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 h3) (mul_nonneg hpq hl)]

theorem weighted_log_sum_lower_bound (D : D7) (w : ℕ → D.what₂.Tau → ℝ) (w0 : ℝ) (hw0 : 0 < w0) (hpi : Real.pi ≤ D.host.v)
    (hw : ∀ ρ j, j < D.R.m → w0 ≤ w j ρ) :
    (D.R.m : ℝ) * Real.log w0 ≤
      ∑ j ∈ range D.R.m, (1 / (D.R.f : ℝ)) * ∑ ρ, Real.log (w j ρ * D.host.v / Real.pi) := by
  have hf : (0 : ℝ) < D.R.f := by exact_mod_cast degree_pos_alt D
  have hv : 1 ≤ D.host.v / Real.pi := (one_le_div Real.pi_pos).2 hpi
  have hterm : ∀ j, j < D.R.m → (Fintype.card D.what₂.Tau : ℝ) * Real.log w0 ≤
      ∑ ρ, Real.log (w j ρ * D.host.v / Real.pi) := by
    intro j hj
    rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro ρ _
    apply Real.log_le_log hw0
    rw [mul_div_assoc]
    calc w0 = w0 * 1 := (mul_one _).symm
      _ ≤ w j ρ * (D.host.v / Real.pi) :=
        mul_le_mul (hw ρ j hj) hv zero_le_one (by linarith [hw ρ j hj])
  rw [D.what₂.card_Tau] at hterm
  calc (D.R.m : ℝ) * Real.log w0 =
        ∑ j ∈ range D.R.m, (1 / (D.R.f : ℝ)) * ((D.R.f : ℝ) * Real.log w0) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, one_div, inv_mul_cancel_left₀ hf.ne']
    _ ≤ _ := Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_left (hterm j (Finset.mem_range.1 hj)) (by positivity)

theorem weights_ge_one_section_B (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (ρ : D.what₂.Tau) (j : ℕ) (hj : j < D.R.m) : 1 ≤ w j ρ := by
  obtain ⟨-, -, -, -, -, -, hΔ, -, -, -, -, -, hw, hwb, hb0, -⟩ := hB
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hx := sc.one_lt_alt
  have hbase : 1 ≤ bN D ρ 0 := by
    have h := (hb0 ρ).1
    rw [le_div_iff₀ (by linarith)] at h
    have h4 : (1 : ℝ) ≤ D.R.k * (4 * Δ) := by nlinarith
    have h5 : (D.R.k : ℝ) * (4 * Δ) ≤ D.R.k * (4 * Δ) * sc.x :=
      le_mul_of_one_le_right (by positivity) hx.le
    linarith
  have hmono : ∀ i, i < D.R.m → bN D ρ 0 ≤ bN D ρ i := by
    intro i
    induction i with
    | zero => intro _; exact le_rfl
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := (hw ρ i (by omega)).2.1
      have h3 := hwb ρ i hi
      linarith
  linarith [(hw ρ j hj).2.1, hmono j hj]

theorem eight_L_le_log_g (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w) (i : Fin 2) :
    8 * sc.L ≤ Real.log (D.host.g i : ℝ) := by
  obtain ⟨-, -, -, -, -, hg, -⟩ := hB
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hb : 0 < sc.b := Real.exp_pos _
  have h1 := (hg i).1
  have hpos : 0 < ((D.R.k : ℝ) * sc.b) ^ 8 := by positivity
  calc 8 * sc.L = Real.log (sc.b ^ 8) := by
        rw [Real.log_pow, Formalism.BasicNotions.Scale.b, Real.log_exp]
        norm_num
    _ ≤ Real.log (((D.R.k : ℝ) * sc.b) ^ 8) :=
        Real.log_le_log (by positivity) (pow_le_pow_left₀ hb.le (by nlinarith) 8)
    _ ≤ Real.log (D.host.g i : ℝ) := Real.log_le_log hpos h1

theorem corollary_five_four_of_explicit (D : D7) (sc : Scale) (C0 CY : ℝ) (h5 : Conclusion5Sharp D sc C0 CY) : VandermondeCountExplicit D sc C0 CY := by
  intro Δ w hA Γ hΓ u hT2 hf2 hT1 hT3
  have hB := hA.1
  have hg := three_le_level_of_section_B D sc C0 Δ w hB
  have hD := dual_degree_pos D hg
  have hd := dual_degree_word_pos D hg (massI_pos D D.R.k) u
  have hk := D.R.k_ge
  have hf : 1 ≤ D.R.f := le_trans one_le_two (le_trans D.R.two_le_m D.R.m_le_f)
  have hfk : 2 * D.R.f ≤ 2 ^ D.R.k := by
    have h3 : 2 ^ D.R.k = 2 * 2 ^ (D.R.k - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  have hX : Real.exp (logXuD D u) ^ (D.R.f * D.R.k) = DstarD D / duStarU D u := by
    have hfR : (0 : ℝ) < D.R.f := by exact_mod_cast hf
    have hkR : (0 : ℝ) < D.R.k := by exact_mod_cast (by omega : 0 < D.R.k)
    rw [← Real.exp_nat_mul]
    unfold logXuD logXu
    push_cast
    rw [show (D.R.f : ℝ) * D.R.k * (1 / ((D.R.f : ℝ) * D.R.k) * Real.log (DstarD D / duStarU D u)) =
      Real.log (DstarD D / duStarU D u) by field_simp]
    exact Real.exp_log (div_pos hD hd)
  have hT : (2 : ℝ) ≤ ((D.mem u).A.T : ℝ) := by exact_mod_cast hT2
  obtain ⟨c1, c2, c3, c4⟩ := Formalism.HermitianLattices.GenusMassVolumes.mass_corollary D.R.f D.R.k ((D.mem u).A.T : ℝ) (Real.exp (logXuD D u)) Γ
    (DstarD D) (duStarU D u) _ (logXuD D u) (logXuD D u) hf (by omega) hfk hT (Real.exp_pos _) hΓ hD hd hX
    hT1 hT3 rfl (by rw [Real.log_exp]) (by rw [Real.log_exp])
  have hL := scale_one_le_L sc
  have hlog2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hΓ0 : 0 < Γ := by linarith
  have eΓ : Γ ^ (-(2 : ℝ)) = (Γ⁻¹) ^ 2 := by
    rw [Real.rpow_neg hΓ0.le, Real.rpow_two, inv_pow]
  have l1 := (h5 Δ w hA u).1
  refine ⟨⟨by rw [eΓ]; exact c1, by rw [eΓ]; exact c2⟩, by linarith, by linarith, fun hG => ⟨c4, by linarith, ?_⟩⟩
  have hm : (44 : ℝ) ≤ D.R.m := by exact_mod_cast hA.2.2.2.1
  have s1 := weighted_log_sum_lower_bound D w 1 one_pos hB.1 (fun ρ j hj => weights_ge_one_section_B D sc C0 Δ w hB ρ j hj)
  rw [Real.log_one, mul_zero] at s1
  have s2 : 16 * sc.L ≤ ∑ i : Fin 2, Real.log (D.host.g i : ℝ) := by
    rw [Fin.sum_univ_two]
    have := eight_L_le_log_g D sc C0 Δ w hB 0
    have := eight_L_le_log_g D sc C0 Δ w hB 1
    linarith
  unfold lowS at l1
  have s3 : (D.R.m : ℝ) * (16 * sc.L) ≤ (D.R.m : ℝ) * ∑ i : Fin 2, Real.log (D.host.g i : ℝ) :=
    mul_le_mul_of_nonneg_left s2 (by linarith)
  nlinarith

theorem part_five_explicit_of_propositions (D : D7) (sc : Scale) (C0 CY : ℝ) (h5 : Conclusion5Sharp D sc C0 CY) (hv : VandermondeVariationExplicitBound D sc C0 CY) :
    VandermondeCountBound D sc C0 CY := ⟨h5, corollary_five_six_of_explicit D sc C0 CY h5, corollary_five_four_of_explicit D sc C0 CY h5, hv⟩

end Formalism.MainNotions.StandardLattice
end
end

section
noncomputable section
namespace Formalism.MainNotions.StandardLattice
open NumberField Formalism.BasicNotions Finset

theorem Ico_succ_eq_Ioc (a b : ℕ) : Ico (a + 1) (b + 1) = Ioc a b := by
  ext x
  simp only [Finset.mem_Ico, Finset.mem_Ioc]
  omega

theorem log_mass_ratio_formula (D : D7) (M : ℕ) (hM : 2 ≤ M) :
    letI := D.host.cmStar
    Real.log (ratioH D M) = (D.R.f : ℝ) * (Real.log (((M - 1).factorial : ℕ) : ℝ) +
      M * Real.log (D.host.v / Real.pi)) - (D.R.f : ℝ) / 2 * Real.log (2 * D.host.v) +
      Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M) := by
  have hv := host_v_pos D
  have hL := lVal_pos D M hM
  unfold ratioH
  have hfac : (0 : ℝ) < (((M - 1).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hvp : 0 < D.host.v / Real.pi := div_pos hv Real.pi_pos
  have h2v : (0 : ℝ) < 2 * D.host.v := by linarith
  have hA : 0 < (((M - 1).factorial : ℕ) : ℝ) * (D.host.v / Real.pi) ^ M := mul_pos hfac (pow_pos hvp M)
  have hS : 0 < Real.sqrt ((2 * D.host.v) ^ D.R.f) := Real.sqrt_pos.mpr (pow_pos h2v _)
  rw [Real.log_mul (div_pos (pow_pos hA _) hS).ne' hL.ne', Real.log_div (pow_pos hA _).ne' hS.ne',
    Real.log_pow, Real.log_mul hfac.ne' (pow_pos hvp M).ne', Real.log_pow,
    Real.log_sqrt (pow_pos h2v _).le, Real.log_pow]
  ring

theorem log_mass_ratio_telescoping (D : D7) (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    letI := D.host.cmStar
    ∑ M ∈ Ico (k + 1) (k + n + 1), Real.log (ratioH D M) =
      (D.R.f : ℝ) * (Real.log (facProd (k + n)) - Real.log (facProd k)) +
      (D.R.f : ℝ) * ((n : ℝ) * k + (n : ℝ) * ((n : ℝ) + 1) / 2) * Real.log (D.host.v / Real.pi) -
      (D.R.f : ℝ) * ((n : ℝ) / 2) * Real.log (2 * D.host.v) +
      ∑ M ∈ Ico (k + 1) (k + n + 1), Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e1 : k + (n + 1) + 1 = (k + n + 1) + 1 := by ring
    have e2 : k + (n + 1) = (k + n) + 1 := by ring
    rw [e1, Finset.sum_Ico_succ_top (show k + 1 ≤ k + n + 1 by omega),
      Finset.sum_Ico_succ_top (show k + 1 ≤ k + n + 1 by omega), ih,
      log_mass_ratio_formula D (k + n + 1) (by omega), e2]
    have hf : facProd (k + n + 1) = facProd (k + n) * (((k + n).factorial : ℕ) : ℝ) := by
      unfold facProd
      rw [Finset.prod_range_succ]
    have hpos : 0 < facProd (k + n) := by
      unfold facProd
      exact Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
    have hfpos : (0 : ℝ) < (((k + n).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [hf, Real.log_mul hpos.ne' hfpos.ne']
    simp only [Nat.add_sub_cancel]
    push_cast
    ring


theorem piN_succ (n g : ℕ) : piN (n + 1) g = piN n g * (1 - ((g : ℝ) ^ (n + 1))⁻¹) := by
  unfold piN
  rw [Finset.prod_Icc_succ_top (by omega)]

theorem piN_eq_range (n g : ℕ) : piN n g = ∏ i ∈ range n, (1 - ((g : ℝ)⁻¹) ^ (i + 1)) := by
  induction n with
  | zero => simp [piN]
  | succ n ih =>
    rw [piN_succ, ih, Finset.prod_range_succ]
    congr 1
    rw [inv_pow]

theorem piN_split (k n g : ℕ) : piN (k + n) g = piN k g * ∏ j ∈ Ioc k (k + n), (1 - ((g : ℝ) ^ j)⁻¹) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, piN_succ, ih, Finset.prod_Ioc_succ_top (show k ≤ k + n by omega), mul_assoc]

theorem one_sub_inv_pow_pos (g : ℕ) (hg : 2 ≤ g) (j : ℕ) (hj : 1 ≤ j) : 0 < 1 - ((g : ℝ) ^ j)⁻¹ := by
  have hg1 : (1 : ℝ) < (g : ℝ) := by exact_mod_cast (show 1 < g by omega)
  have h1 : (1 : ℝ) < (g : ℝ) ^ j := one_lt_pow₀ hg1 (by omega)
  have h2 : ((g : ℝ) ^ j)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  linarith

theorem piN_pos (n g : ℕ) (hg : 2 ≤ g) : 0 < piN n g := by
  unfold piN
  exact Finset.prod_pos fun i hi => one_sub_inv_pow_pos g hg i (Finset.mem_Icc.mp hi).1

theorem partial_product_bounds (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) (k n : ℕ) :
    1 - 2 * y ^ (k + 1) + 2 * y ^ (k + n + 1) ≤ ∏ j ∈ Ioc k (k + n), (1 - y ^ j) ∧
      ∏ j ∈ Ioc k (k + n), (1 - y ^ j) ≤ 1 ∧ 0 ≤ ∏ j ∈ Ioc k (k + n), (1 - y ^ j) := by
  have hfac : ∀ j : ℕ, 0 ≤ 1 - y ^ j ∧ 1 - y ^ j ≤ 1 := fun j =>
    ⟨by have := pow_le_one₀ (n := j) hy0 (by linarith); linarith,
     by have := pow_nonneg hy0 j; linarith⟩
  have low : ∀ n : ℕ, 1 - 2 * y ^ (k + 1) + 2 * y ^ (k + n + 1) ≤ ∏ j ∈ Ioc k (k + n), (1 - y ^ j) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← add_assoc, Finset.prod_Ioc_succ_top (show k ≤ k + n by omega)]
      have ht0 : 0 ≤ y ^ (k + n + 1) := pow_nonneg hy0 _
      have hmono : y ^ (k + n + 1) ≤ y ^ (k + 1) := pow_le_pow_of_le_one hy0 (by linarith) (by omega)
      have e : y ^ (k + n + 1 + 1) = y * y ^ (k + n + 1) := by ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_right ih (hfac (k + n + 1)).1,
        mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ 1 - 2 * y), mul_nonneg ht0 (sub_nonneg.mpr hmono)]
  exact ⟨low n, Finset.prod_le_one (fun j _ => (hfac j).1) (fun j _ => (hfac j).2),
    Finset.prod_nonneg fun j _ => (hfac j).1⟩

theorem triangular_number_identities (k : ℕ) : ∃ A, k * (k - 1) / 2 = A ∧ k * (k + 1) / 2 = A + k ∧ k * k = 2 * A + k := by
  refine ⟨k * (k - 1) / 2, rfl, ?_, ?_⟩
  · have h : k * (k + 1) = k * (k - 1) + k * 2 := by
      cases k with
      | zero => simp
      | succ m =>
        simp only [Nat.add_sub_cancel]
        ring
    rw [h, Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)]
  · have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self k)
    cases k with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel] at h2 ⊢
      rw [h2]
      ring

theorem add_two_mul_add_one_sq_expand (k s : ℕ) :
    (k + 2 * s + 1) ^ 2 = k * k + 4 * (s * k) + 4 * (s * s) + 2 * k + 4 * s + 1 := by
  ring

theorem index_exponent_identities (k s A : ℕ) (hA : k * k = 2 * A + k) :
    ((k + 2 * s + 1) ^ 2 - (k + 1) ^ 2 - 2 * s) / 2 = 2 * (s * k) + s + 2 * (s * s) ∧
    ((k + 2 * s + 1) ^ 2 + 3 * k + 1 + 2 * s) / 2 = A + 3 * k + 1 + 2 * (s * k) + 3 * s + 2 * (s * s) := by
  have hs := add_two_mul_add_one_sq_expand k s
  have hk1 : (k + 1) ^ 2 = k * k + 2 * k + 1 := by ring
  constructor
  · omega
  · omega

theorem card_GL_eq_pow_mul_prod' (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) :
    (Fintype.card (GL (Fin n) F) : ℝ) =
      (Fintype.card F : ℝ) ^ (n * n) * ∏ i ∈ range n, (1 - ((Fintype.card F : ℝ)⁻¹) ^ (i + 1)) := by
  rw [← Nat.card_eq_fintype_card, Matrix.card_GL_field, Nat.cast_prod,
    Fin.prod_univ_eq_prod_range (fun i => (((Fintype.card F) ^ n - (Fintype.card F) ^ i : ℕ) : ℝ)) n]
  have hq1 : 1 ≤ Fintype.card F := Fintype.card_pos
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq1
  have hq0 : (Fintype.card F : ℝ) ≠ 0 := hq.ne'
  have key : ∀ i ∈ range n, (((Fintype.card F) ^ n - (Fintype.card F) ^ i : ℕ) : ℝ) =
      (Fintype.card F : ℝ) ^ n * (1 - ((Fintype.card F : ℝ)⁻¹) ^ (n - 1 - i + 1)) := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hle : (Fintype.card F) ^ i ≤ (Fintype.card F) ^ n := Nat.pow_le_pow_right hq1 hin.le
    have e1 : n - 1 - i + 1 = n - i := by omega
    have e2 : (Fintype.card F : ℝ) ^ n = (Fintype.card F : ℝ) ^ (n - i) * (Fintype.card F : ℝ) ^ i := by
      rw [← pow_add, Nat.sub_add_cancel hin.le]
    rw [Nat.cast_sub hle, e1]
    push_cast
    rw [e2, inv_pow]
    field_simp
  rw [Finset.prod_congr rfl key, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
  congr 1
  exact Finset.prod_range_reflect (fun j => 1 - ((Fintype.card F : ℝ)⁻¹) ^ (j + 1)) n

theorem local_index_at_place (F : Type) [Field F] [Fintype F] [DecidableEq F] (k m : ℕ) (hm : 2 ≤ m) (hev : Even m) :
    (Fintype.card (GL (Fin k) F) : ℝ) / (Fintype.card F : ℝ) ^ (k * (k - 1) / 2) =
      (Fintype.card F : ℝ) ^ (k * (k + 1) / 2) * ∏ i ∈ range k, (1 - ((Fintype.card F : ℝ)⁻¹) ^ (i + 1)) ∧
    (Fintype.card (GL (Fin (k + m - 1)) F) : ℝ) /
        ((Fintype.card F : ℝ) ^ (((k + m - 1) ^ 2 - (k + 1) ^ 2 - 2 * (m / 2 - 1)) / 2) *
          (Fintype.card F : ℝ) ^ (k * (k - 1) / 2)) =
      (Fintype.card F : ℝ) ^ (((k + m - 1) ^ 2 + 3 * k + 1 + 2 * (m / 2 - 1)) / 2) *
        ∏ i ∈ range (k + m - 1), (1 - ((Fintype.card F : ℝ)⁻¹) ^ (i + 1)) := by
  obtain ⟨A, hA1, hA2, hA3⟩ := triangular_number_identities k
  obtain ⟨t, rfl⟩ := hev
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have hr : k + (s + 1 + (s + 1)) - 1 = k + 2 * s + 1 := by omega
  have hm2 : (s + 1 + (s + 1)) / 2 - 1 = s := by omega
  obtain ⟨h1, h2⟩ := index_exponent_identities k s A hA3
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsq : (k + 2 * s + 1) * (k + 2 * s + 1) =
      (2 * (s * k) + s + 2 * (s * s)) + A + (A + 3 * k + 1 + 2 * (s * k) + 3 * s + 2 * (s * s)) := by
    have hs := add_two_mul_add_one_sq_expand k s
    rw [sq] at hs
    omega
  rw [hr, hm2, h1, h2, hA1, hA2, card_GL_eq_pow_mul_prod', card_GL_eq_pow_mul_prod', hA3, hsq]
  constructor
  · rw [div_eq_iff (pow_pos hq _).ne']
    ring
  · rw [div_eq_iff (mul_pos (pow_pos hq _) (pow_pos hq _)).ne']
    ring

theorem local_index_formulas_and_bounds (D : D7) : LocalIndexFormulasAndBounds D := by
  refine ⟨fun i => ?_, fun n g hg => ?_⟩
  · have : Fact (D.host.g i).Prime := ⟨D.host.g_prime i⟩
    have hc : Fintype.card (ZMod (D.host.g i)) = D.host.g i := ZMod.card _
    have hg2 : 2 ≤ D.host.g i := (D.host.g_prime i).two_le
    obtain ⟨h1, h2⟩ := local_index_at_place (ZMod (D.host.g i)) D.R.k D.R.m D.R.two_le_m D.R.m_even
    rw [hc] at h1 h2
    have e1 : idxColLoc (D.host.g i) D.R.k =
        (D.host.g i : ℝ) ^ (D.R.k * (D.R.k + 1) / 2) * piN D.R.k (D.host.g i) := by
      rw [piN_eq_range, ← h1]
      unfold idxColLoc idxLoc
      rw [card_GL_subtype_eq_card_matrix _ det_eq_one_of_unitriangular]
      have := Formalism.LogVandermondeBounds.StandardLattice.cardUnitriangular (ZMod (D.host.g i)) D.R.k
      rw [hc] at this
      have h3 : Nat.card {A : Matrix (Fin D.R.k) (Fin D.R.k) (ZMod (D.host.g i)) // IsUnitri A} =
          D.host.g i ^ (D.R.k * (D.R.k - 1) / 2) := this
      rw [h3, Nat.card_eq_fintype_card]
      push_cast
      rfl
    have e2 : idxRowLoc (D.host.g i) D.R.k D.R.m =
        (D.host.g i : ℝ) ^ ((D.R.r ^ 2 + 3 * D.R.k + 1 + 2 * D.R.rS) / 2) * piN D.R.r (D.host.g i) := by
      have h2' : _ = (D.host.g i : ℝ) ^ ((D.R.r ^ 2 + 3 * D.R.k + 1 + 2 * D.R.rS) / 2) *
          ∏ j ∈ range D.R.r, (1 - ((D.host.g i : ℝ)⁻¹) ^ (j + 1)) := h2
      rw [piN_eq_range, ← h2']
      unfold idxRowLoc idxLoc
      rw [rowLevCard_holds _ _ _ (D.host.g_prime i) D.R.two_le_m D.R.m_even, Nat.card_eq_fintype_card]
      push_cast
      rfl
    have hr : D.R.r = D.R.k + (D.R.m - 1) := by
      have er : D.R.r = D.R.k + D.R.m - 1 := rfl
      have := D.R.two_le_m
      omega
    have hq : piN D.R.r (D.host.g i) / piN D.R.k (D.host.g i) =
        ∏ j ∈ Ioc D.R.k (D.R.k + (D.R.m - 1)), (1 - ((D.host.g i : ℝ)⁻¹) ^ j) := by
      rw [hr, piN_split, mul_div_cancel_left₀ _ (piN_pos _ _ hg2).ne']
      exact Finset.prod_congr rfl fun j _ => by rw [inv_pow]
    have hy0 : (0 : ℝ) ≤ (D.host.g i : ℝ)⁻¹ := by positivity
    have hy : (D.host.g i : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast hg2)
    obtain ⟨t1, t2, -⟩ := partial_product_bounds _ hy0 hy D.R.k (D.R.m - 1)
    refine ⟨e1, e2, ?_, by rw [hq]; exact t2⟩
    rw [hq, ← inv_pow]
    have : 0 ≤ 2 * ((D.host.g i : ℝ)⁻¹) ^ (D.R.k + (D.R.m - 1) + 1) := by positivity
    linarith
  · rw [piN_eq_range]
    exact Formalism.LogVandermondeBounds.StandardLattice.eulerProductBounds (g : ℝ) (by exact_mod_cast hg) n

theorem indices_four_three_of_indices_four_two (D : D7) (h : LocalIndexFormulasAndBounds D) : IndexProductFormulasAndRatio D := by
  obtain ⟨hloc, -⟩ := h
  have hPi : idxPi D (D.host.g 0) (D.host.g 1) =
      ∏ i : Fin 2, ((D.host.g i : ℝ) ^ (D.R.k * (D.R.k + 1) / 2) * piN D.R.k (D.host.g i)) ^ D.R.f := by
    unfold idxPi
    rw [Fin.prod_univ_two, (hloc 0).1, (hloc 1).1]
  have hSig : idxSig D (D.host.g 0) (D.host.g 1) =
      ∏ i : Fin 2, ((D.host.g i : ℝ) ^ ((D.R.r ^ 2 + 3 * D.R.k + 1 + 2 * D.R.rS) / 2) *
        piN D.R.r (D.host.g i)) ^ D.R.f := by
    unfold idxSig
    rw [Fin.prod_univ_two, (hloc 0).2.1, (hloc 1).2.1]
  refine ⟨hPi, hSig, ?_⟩
  obtain ⟨t, ht⟩ := D.R.m_even
  have hm2 := D.R.two_le_m
  obtain ⟨A, hA1, hA2, hA3⟩ := triangular_number_identities D.R.k
  have hE : (D.R.r ^ 2 + 3 * D.R.k + 1 + 2 * D.R.rS) / 2 =
      D.R.k * (D.R.k + 1) / 2 + D.R.m * (2 * D.R.k + D.R.m - 1) / 2 := by
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have e1 : D.R.r = D.R.k + 2 * s + 1 := by
      show D.R.k + D.R.m - 1 = _
      omega
    have e2 : D.R.rS = s := by
      show D.R.m / 2 - 1 = _
      omega
    have e3 : D.R.m * (2 * D.R.k + D.R.m - 1) / 2 =
        2 * (s * D.R.k) + 2 * (s * s) + 3 * s + 2 * D.R.k + 1 := by
      rw [ht]
      have h4 : (s + 1 + (s + 1)) * (2 * D.R.k + (s + 1 + (s + 1)) - 1) =
          2 * (2 * (s * D.R.k) + 2 * (s * s) + 3 * s + 2 * D.R.k + 1) := by
        have h5 : 2 * D.R.k + (s + 1 + (s + 1)) - 1 = 2 * D.R.k + 2 * s + 1 := by omega
        rw [h5]
        ring
      rw [h4]
      omega
    rw [e1, e2, (index_exponent_identities D.R.k s A hA3).2, e3, hA2]
    omega
  have hg : ∀ i, 2 ≤ D.host.g i := fun i => (D.host.g_prime i).two_le
  have hgR : ∀ i, (0 : ℝ) < (D.host.g i : ℝ) := fun i => by
    have := hg i
    exact_mod_cast (show 0 < D.host.g i by omega)
  have hN : ∀ i, 0 < piN D.R.k (D.host.g i) := fun i => piN_pos _ _ (hg i)
  have hr' : D.R.r = D.R.k + (D.R.m - 1) := by
    show D.R.k + D.R.m - 1 = _
    omega
  rw [hPi, hSig, hE, hr']
  simp only [Fin.prod_univ_two]
  rw [piN_split, piN_split, Finset.prod_pow, Finset.prod_pow,
    div_eq_iff (mul_pos (pow_pos (mul_pos (pow_pos (hgR 0) _) (hN 0)) _)
      (pow_pos (mul_pos (pow_pos (hgR 1) _) (hN 1)) _)).ne']
  ring

theorem index_product_formulas_and_ratio (D : D7) : IndexProductFormulasAndRatio D := indices_four_three_of_indices_four_two D (local_index_formulas_and_bounds D)


end Formalism.MainNotions.StandardLattice
end
end
