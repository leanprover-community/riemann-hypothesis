import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.GeoRatio
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.SgBasics
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SumField
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpqMinor
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QhtBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.VolOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.ContinuousLeviUnipotentPath
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.UnipMemIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.CtZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.BlkCont
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.PolyBdAll

section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K]

private theorem sd_ent {n : ℕ} (h : AdelicGLn.AdelicGL K n) (i j : Fin n) (y : GroundTheory.Global.IdeleGroup K)
    (hy : (y : 𝔸[K]) = (h : Matrix (Fin n) (Fin n) 𝔸[K]) i j) :
    (GroundTheory.Global.IdeleGroup.ideleModule K y : ℝ) ≤ AutomorphicForm.height h := by
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq, AutomorphicForm.height]
  refine mul_le_mul (Finset.prod_le_prod (fun w _ => by positivity) fun w _ => ?_)
    (finprod_le_finprod_of_nonneg (GroundTheory.Global.IdeleGroup.finite_mulSupport_norm y) (finite_mulSupport_locHeight_finAt h)
      (fun v => norm_nonneg _) fun v => ?_) (finprod_nonneg fun v => norm_nonneg _)
    (Finset.prod_nonneg fun w _ => pow_nonneg (locHeight_pos _).le _)
  · refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    rw [hy]
    exact norm_apply_le_locHeight (infAt w h) i j
  · rw [hy]
    exact norm_apply_le_locHeight (finAt v h) i j

private theorem mul_upper_triangular_first_col {R : Type} [CommRing R] (S T : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (hT : T.IsUpperTriangular)
    (i : Fin (2 + 2)) : (S * T) i 0 = S i 0 * T 0 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single 0 (fun l _ hl => ?_) (fun h => absurd (Finset.mem_univ _) h)
  rw [hT (show (id 0 : Fin (2 + 2)) < id l from Fin.pos_iff_ne_zero.2 hl), mul_zero]

private theorem upper_triangular_mul_last_row {R : Type} [CommRing R] (S T : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (hT : T.IsUpperTriangular)
    (j : Fin (2 + 2)) : (T * S) 3 j = T 3 3 * S 3 j := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single 3 (fun l _ hl => ?_) (fun h => absurd (Finset.mem_univ _) h)
  rw [hT (show (id l : Fin (2 + 2)) < id 3 from Fin.lt_last_iff_ne_last.2 hl), zero_mul]

private theorem sd_col (δ : GL (Fin (2 + 2)) K) (T : AdelicGLn.AdelicGL K (2 + 2)) (hT : T ∈ adelicBorel)
    (u : GroundTheory.Global.IdeleGroup K) (hu : (u : 𝔸[K]) = (T : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) 0 0) :
    (GroundTheory.Global.IdeleGroup.ideleModule K u : ℝ) ≤ AutomorphicForm.height (AdelicGLn.diagonal K (2 + 2) δ * T) := by
  obtain ⟨i, hi⟩ : ∃ i, (δ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) i 0 ≠ 0 := by
    by_contra h
    push Not at h
    have := congrArg (fun M => M 0 0) (Units.inv_mul δ)
    simp only [Matrix.mul_apply, h, mul_zero, Finset.sum_const_zero, Matrix.one_apply_eq] at this
    exact zero_ne_one this
  have h := sd_ent (AdelicGLn.diagonal K (2 + 2) δ * T) i 0 (GroundTheory.Global.IdeleGroup.diagonal K (Units.mk0 _ hi) * u) (by
    rw [Units.val_mul, Units.val_mul, mul_upper_triangular_first_col _ _ hT, hu, GroundTheory.Global.IdeleGroup.coe_diagonal, AdelicGLn.diagonal_apply,
      Units.val_mk0])
  rwa [map_mul, GroundTheory.Global.IdeleGroup.ideleModule_diagonal, one_mul] at h

private theorem sd_row (δ : GL (Fin (2 + 2)) K) (T : AdelicGLn.AdelicGL K (2 + 2)) (hT : T ∈ adelicBorel)
    (u : GroundTheory.Global.IdeleGroup K) (hu : (u : 𝔸[K]) = (T : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) 3 3) :
    (GroundTheory.Global.IdeleGroup.ideleModule K u : ℝ) ≤ AutomorphicForm.height (T * AdelicGLn.diagonal K (2 + 2) δ) := by
  obtain ⟨j, hj⟩ : ∃ j, (δ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) 3 j ≠ 0 := by
    by_contra h
    push Not at h
    have := congrArg (fun M => M 3 3) (Units.mul_inv δ)
    simp only [Matrix.mul_apply, h, zero_mul, Finset.sum_const_zero, Matrix.one_apply_eq] at this
    exact zero_ne_one this
  have h := sd_ent (T * AdelicGLn.diagonal K (2 + 2) δ) 3 j (u * GroundTheory.Global.IdeleGroup.diagonal K (Units.mk0 _ hj)) (by
    rw [Units.val_mul, Units.val_mul, upper_triangular_mul_last_row _ _ hT, hu, GroundTheory.Global.IdeleGroup.coe_diagonal, AdelicGLn.diagonal_apply,
      Units.val_mk0])
  rwa [map_mul, GroundTheory.Global.IdeleGroup.ideleModule_diagonal, mul_one] at h

private theorem sd_zt (s : ℝ) : ∃ a : GroundTheory.Global.IdeleGroup K, zt K s = diagUnits 2 (fun _ => a) ∧
    (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) = Real.exp (s / 2) := by
  obtain ⟨a, ha⟩ : ∃ a : GroundTheory.Global.IdeleGroup K, zt K s = diagUnits 2 (fun _ => a) := ⟨_, rfl⟩
  refine ⟨a, ha, ?_⟩
  have h : (detModule K 2 (zt K s) : ℝ) = Real.exp s := by rw [zt, detModule_centralSection two_pos]
  change (GroundTheory.Global.IdeleGroup.ideleModule K (AdelicGLn.det K 2 (zt K s)) : ℝ) = _ at h
  rw [ha, det_diagUnits, Fin.prod_univ_two, map_mul, Positive.val_mul] at h
  refine (pow_left_inj₀ (GroundTheory.Global.IdeleGroup.ideleModule K a).2.le (Real.exp_pos _).le two_ne_zero).1 ?_
  rw [sq, h, sq, ← Real.exp_add, add_halves]

private theorem sd_lv (s : ℝ) : ∃ a : Fin (2 + 2) → GroundTheory.Global.IdeleGroup K,
    ((lv 1 1 s : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = diagUnits (2 + 2) a ∧
    (GroundTheory.Global.IdeleGroup.ideleModule K (a 0) : ℝ) = Real.exp (s / 2) ∧
    (GroundTheory.Global.IdeleGroup.ideleModule K (a 3) : ℝ) = Real.exp (-s / 2) := by
  obtain ⟨a, ha, ha'⟩ := sd_zt (K := K) s
  obtain ⟨c, hc, hc'⟩ := sd_zt (K := K) (-s)
  refine ⟨fun i => Sum.elim (fun _ => a) (fun _ => c) (finSumFinEquiv.symm i), ?_, ha', hc'⟩
  rw [blkLaws.1, Subgroup.coe_one, one_mul, one_mul, ha, hc]
  refine Units.ext ?_
  change Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Matrix.diagonal _) 0 0 (Matrix.diagonal _)) = _
  rw [Matrix.fromBlocks_diagonal, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv, coe_diagUnits]
  congr 1
  funext i
  simp only [Function.comp_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rfl

private theorem sd_key (δ : GL (Fin (2 + 2)) K) (b : AdelicGLn.AdelicGL K (2 + 2)) (hb : b ∈ adelicBorel)
    (a r : Fin (2 + 2) → GroundTheory.Global.IdeleGroup K) :
    (GroundTheory.Global.IdeleGroup.ideleModule K (a 0) : ℝ) * GroundTheory.Global.IdeleGroup.ideleModule K (r 0) ≤ AutomorphicForm.height b *
      AutomorphicForm.height (AdelicGLn.diagonal K (2 + 2) δ * (diagUnits (2 + 2) a * b * diagUnits (2 + 2) r)) ∧
    ((GroundTheory.Global.IdeleGroup.ideleModule K (a 3) : ℝ) * GroundTheory.Global.IdeleGroup.ideleModule K (r 3))⁻¹ ≤ AutomorphicForm.height b *
      AutomorphicForm.height (AdelicGLn.diagonal K (2 + 2) δ * (diagUnits (2 + 2) a * b * diagUnits (2 + 2) r)) := by
  have hT : diagUnits (2 + 2) a * b * diagUnits (2 + 2) r ∈ adelicBorel :=
    mul_mem (mul_mem (diagUnits_mem_adelicBorel _ a) hb) (diagUnits_mem_adelicBorel _ r)
  constructor
  · obtain ⟨β, hβ⟩ := isUnit_apply_self_of_mem_adelicBorel hb 0
    have h1 := sd_col δ _ hT (a 0 * β * r 0) (by
      simp only [Units.val_mul, coe_diagUnits, Matrix.mul_diagonal, Matrix.diagonal_mul, hβ])
    have h2 := sd_ent b⁻¹ 0 0 β⁻¹ (by
      have := mul_upper_triangular_first_col (b⁻¹ : AdelicGLn.AdelicGL K (2 + 2)).val b.val hb 0
      rw [Units.inv_mul, Matrix.one_apply_eq, ← hβ] at this
      exact Units.inv_eq_of_mul_eq_one_left this.symm)
    rw [height_inv, map_inv, Positive.coe_inv] at h2
    rw [map_mul, map_mul, Positive.val_mul, Positive.val_mul] at h1
    have hp := (GroundTheory.Global.IdeleGroup.ideleModule K β).2
    refine le_trans (le_of_eq ?_) (mul_le_mul h2 h1 (le_of_lt (mul_pos (mul_pos (Subtype.prop _) hp) (Subtype.prop _))) (height_pos _).le)
    field_simp
  · obtain ⟨β, hβ⟩ := isUnit_apply_self_of_mem_adelicBorel (inv_mem hb) 3
    have h1 := sd_row δ⁻¹ _ (inv_mem hT) ((r 3)⁻¹ * (β * (a 3)⁻¹)) (by
      rw [mul_inv_rev, mul_inv_rev, ← map_inv, ← map_inv]
      simp only [Units.val_mul, coe_diagUnits, Matrix.mul_diagonal, Matrix.diagonal_mul, hβ, Pi.inv_apply])
    have h2 := sd_ent b 3 3 β⁻¹ (by
      have := upper_triangular_mul_last_row b.val (b⁻¹ : AdelicGLn.AdelicGL K (2 + 2)).val (inv_mem hb : b⁻¹ ∈ adelicBorel) 3
      rw [Units.inv_mul, Matrix.one_apply_eq, ← hβ] at this
      exact Units.inv_eq_of_mul_eq_one_right this.symm)
    rw [map_inv, Positive.coe_inv] at h2
    rw [map_inv (AdelicGLn.diagonal K (2 + 2)), ← mul_inv_rev, height_inv, map_mul, map_mul, map_inv, map_inv, Positive.val_mul,
      Positive.val_mul, Positive.coe_inv, Positive.coe_inv] at h1
    have hp := (GroundTheory.Global.IdeleGroup.ideleModule K β).2
    have hp1 := (GroundTheory.Global.IdeleGroup.ideleModule K (a 3)).2
    have hp2 := (GroundTheory.Global.IdeleGroup.ideleModule K (r 3)).2
    refine le_trans (le_of_eq ?_) (mul_le_mul h2 h1 (by positivity) (height_pos _).le)
    field_simp

private theorem sd_real {d : ℕ} (hd : 0 < d) {ρ : Fin (2 + 2) → ℝ} (hρ : ∀ i, 0 < ρ i) {h C X : ℝ} (hX : 1 ≤ X) (hC : 0 ≤ C)
    (h1 : |h - (d : ℝ) * Real.log (ρ 0 * ρ 1)| ≤ C) (h2 : |Real.log (ρ 0 * ρ 1 * (ρ 2 * ρ 3))| ≤ C)
    (h3 : Real.exp (-h / 2) * ρ 0 ^ d ≤ X) (h4 : (Real.exp (- -h / 2) * ρ 3 ^ d)⁻¹ ≤ X) :
    inR ρ ≤ Real.exp (3 * C) * X ^ 4 := by
  have p0 := hρ 0
  have p1 := hρ 1
  have p2 := hρ 2
  have p3 := hρ 3
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL := Real.log_nonneg hX
  have h3' := Real.log_le_log (by positivity) h3
  have h4' := Real.log_le_log (by positivity) h4
  rw [Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow] at h3'
  rw [Real.log_inv, Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow] at h4'
  rw [Real.log_mul (by positivity) (by positivity)] at h1
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)] at h2
  rw [← Real.log_le_log_iff (by unfold inR; positivity) (by positivity), inR, Real.log_mul (by positivity) (by positivity),
    Real.log_div p0.ne' p1.ne', Real.log_div p2.ne' p3.ne', Real.log_mul (by positivity) (by positivity), Real.log_exp,
    Real.log_pow]
  have h5 := (abs_le.1 h1).2
  have h6 := (abs_le.1 h2).2
  have h7 : (d : ℝ) * -(Real.log (ρ 1) + Real.log (ρ 3)) ≤ C + 2 * Real.log X := by linarith
  have h8 : -(Real.log (ρ 1) + Real.log (ρ 3)) ≤ C + 2 * Real.log X := by
    rcases le_total (-(Real.log (ρ 1) + Real.log (ρ 3))) 0 with h | h
    · linarith
    · exact (le_mul_of_one_le_left h hd1).trans h7
  push_cast
  linarith

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.secDec :
    ∀ {K : Type} [Field K] [NumberField K] (ω : Set (AdelicGLn.AdelicGL K (2 + 2))) (t : ℝ), Bor ω → 0 < t → ∀ f : G1 K (2 + 2) → ℂ, SFun f → ∀ N : ℕ, ∃ C : ℝ, ∀ (ρ : Fin (2 + 2) → ℝ) (z : G1 K (2 + 2)), Sg ω ρ z → Rel t ρ →
      ‖f z‖ * inR ρ ^ N ≤ C := by
  intro K _ _ ω t hω _ f hf N
  obtain ⟨C, c, hC, hS⟩ := sgBasics ω hω
  obtain ⟨M, hM⟩ := exists_height_le_of_isCompact hω.1
  obtain ⟨C', hC'⟩ := hf.dec (4 * N) 0
  have hc1 := one_le_heightConst (K := K) (n := 2 + 2)
  refine ⟨(Real.exp (3 * C) * (M * heightConst K (2 + 2)) ^ 4) ^ N * C', fun ρ z hz _ => ?_⟩
  obtain ⟨h1, h2, -⟩ := hS ρ z hz
  obtain ⟨hρ, b, hb, k, hk, e⟩ := hz
  have hy : HH (lv 1 1 (-HH z) * z) = 0 := by
    have := (hpSpec (K := K)).1 0 1 1 (-HH z) z
    rw [show nn (K := K) 0 = 1 from unipOne_zero _, one_mul] at this
    rw [this, neg_add_cancel]
  obtain ⟨γ, hγ, hd⟩ := hC' _ (by rw [hy, abs_zero])
  rw [hf.ray] at hd
  obtain ⟨δ, hδ⟩ : ∃ δ : GL (Fin (2 + 2)) K, AdelicGLn.diagonal K (2 + 2) δ = (γ : AdelicGLn.AdelicGL K (2 + 2)) := by
    obtain ⟨γ', -, rfl⟩ := hγ
    exact γ'.2
  obtain ⟨a, ha, ha0, ha3⟩ := sd_lv (K := K) (-HH z)
  set H := AutomorphicForm.height ((γ * (lv 1 1 (-HH z) * z) : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) with hH
  have hH1 : 1 ≤ H := one_le_height _
  have hbM : AutomorphicForm.height b ≤ M := hM b hb
  have hM1 : 1 ≤ M := (one_le_height b).trans hbM
  obtain ⟨h3, h4⟩ := sd_key δ b (hω.2 hb) a fun i => posIdele (K := K) (ρ i) (hρ i)
  have h5 : AutomorphicForm.height b * AutomorphicForm.height (AdelicGLn.diagonal K (2 + 2) δ *
      (diagUnits (2 + 2) a * b * diagUnits (2 + 2) fun i => posIdele (K := K) (ρ i) (hρ i))) ≤ M * heightConst K (2 + 2) * H := by
    have h6 := height_mul_le ((γ * (lv 1 1 (-HH z) * z) : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) k⁻¹
    rw [height_inv, height_eq_one_of_mem_maxCompact hk, mul_one, ← hH, Subgroup.coe_mul, Subgroup.coe_mul, ha, ← hδ, e] at h6
    simp only [mul_assoc, mul_inv_cancel, mul_one] at h6 ⊢
    exact mul_le_mul hbM h6 (height_pos _).le (by linarith)
  rw [ha0, ideleModule_posIdele] at h3
  rw [ha3, ideleModule_posIdele] at h4
  have h7 := sd_real Module.finrank_pos hρ (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hM1 hc1) hH1)
    (by linarith) h1 h2 (h3.trans h5) (h4.trans h5)
  have h8 : 0 ≤ inR ρ := by
    have := hρ 0
    have := hρ 1
    have := hρ 2
    have := hρ 3
    unfold inR
    positivity
  calc ‖f z‖ * inR ρ ^ N ≤ ‖f z‖ * (Real.exp (3 * C) * (M * heightConst K (2 + 2) * H) ^ 4) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h8 h7 N) (norm_nonneg _)
    _ = (Real.exp (3 * C) * (M * heightConst K (2 + 2)) ^ 4) ^ N * (‖f z‖ * H ^ (4 * N)) := by
        rw [mul_pow _ H, ← mul_assoc (Real.exp _), mul_pow _ (H ^ 4), ← pow_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)
end

section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

private theorem fs_ratio (ρ : Fin (2 + 2) → ℝ) (hρ : ∀ i, 0 < ρ i) (t C H d : ℝ) (ht : 0 < t) (hd : 1 ≤ d) (hH : 0 ≤ H)
    (hr : Rel t ρ) (h1 : |H - d * Real.log (ρ 0 * ρ 1)| ≤ C) (h2 : |Real.log (ρ 0 * ρ 1 * (ρ 2 * ρ 3))| ≤ C) (i j : Fin (2 + 2)) :
    ρ i / ρ j ≤ Real.exp (2 * C + |Real.log t|) * Real.exp H * max 1 (inR ρ) := by
  have p0 := hρ 0
  have p1 := hρ 1
  have p2 := hρ 2
  have p3 := hρ 3
  have hm : 0 < max 1 (inR ρ) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hM0 : 0 ≤ Real.log (max 1 (inR ρ)) := Real.log_nonneg (le_max_left _ _)
  have hL : Real.log (ρ 0) - Real.log (ρ 1) + (Real.log (ρ 2) - Real.log (ρ 3)) ≤ Real.log (max 1 (inR ρ)) := by
    rw [← Real.log_div p0.ne' p1.ne', ← Real.log_div p2.ne' p3.ne', ← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by positivity) (le_max_right _ _)
  have r1 := Real.log_le_log (by positivity) hr.1
  have r2 := Real.log_le_log (by positivity) hr.2
  rw [Real.log_mul ht.ne' p1.ne'] at r1
  rw [Real.log_mul ht.ne' p3.ne'] at r2
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul p0.ne' p1.ne', Real.log_mul p2.ne' p3.ne', abs_le] at h2
  rw [Real.log_mul p0.ne' p1.ne', abs_le] at h1
  have hτ := neg_abs_le (Real.log t)
  have hτ0 := abs_nonneg (Real.log t)
  have hs : -C ≤ Real.log (ρ 0) + Real.log (ρ 1) ∧ Real.log (ρ 0) + Real.log (ρ 1) ≤ H + C := by
    rcases le_total 0 (Real.log (ρ 0) + Real.log (ρ 1)) with h | h
    · have := mul_le_mul_of_nonneg_right hd h
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · have := mul_le_mul_of_nonpos_right hd h
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hb : ∀ k : Fin (2 + 2), |Real.log (ρ k)| ≤ (2 * C + |Real.log t| + H + Real.log (max 1 (inR ρ))) / 2 := by
    have hk : ∀ k : Fin (2 + 2), k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by decide
    intro k
    rw [abs_le]
    rcases hk k with rfl | rfl | rfl | rfl <;> constructor <;> linarith [hs.1, hs.2, h2.1, h2.2]
  have e : ρ i / ρ j = Real.exp (Real.log (ρ i) - Real.log (ρ j)) := by
    rw [Real.exp_sub, Real.exp_log (hρ i), Real.exp_log (hρ j)]
  rw [e, ← Real.exp_log hm, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  linarith [(abs_le.1 (hb i)).2, (abs_le.1 (hb j)).1]

private theorem fs_point {K : Type} [Field K] [NumberField K] (ω : Set (AdelicGLn.AdelicGL K (2 + 2))) (t : ℝ) (hω : Bor ω)
    (ht : 0 < t) (f : G1 K (2 + 2) → ℂ) (hf : SFun f) (N₀ : ℕ) :
    ∃ N₁ : ℕ, ∀ M : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ (ρ : Fin (2 + 2) → ℝ) (z : G1 K (2 + 2)), Sg ω ρ z → Rel t ρ → 0 ≤ HH z →
      Real.exp (2 * HH z) * ‖f z‖ * AutomorphicForm.height (z : AdelicGLn.AdelicGL K (2 + 2)) ^ N₀ * max 1 (inR ρ) ^ M ≤
        D * qht z ^ N₁ := by
  obtain ⟨C, c, hC, hs⟩ := sgBasics ω hω
  obtain ⟨c₀, C₀, hc₀, hq⟩ := hpQht (K := K)
  refine ⟨⌈c₀⌉₊ * (2 + c * N₀), fun M => ?_⟩
  obtain ⟨D₀, hD₀⟩ := secDec ω t hω ht f hf 0
  obtain ⟨D₁, hD₁⟩ := secDec ω t hω ht f hf (c * N₀ + M)
  set A := Real.exp (2 * C + |Real.log t|) with hA
  have hA1 : 1 ≤ A := Real.one_le_exp (by have := abs_nonneg (Real.log t); linarith)
  refine ⟨(C * A ^ c) ^ N₀ * max 0 (max D₀ D₁) * Real.exp C₀ ^ (2 + c * N₀), by positivity, fun ρ z hz hr hH => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hs ρ z hz
  have hd : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  set m := max 1 (inR ρ) with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  set E := Real.exp (HH z) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp hH
  have h4 := h3 (A * E * m) (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hA1 hE1) hm1)
    (fs_ratio ρ hz.1 t C (HH z) _ ht hd hH hr h1 h2)
  have hQ : 1 ≤ qht z := (qhtBasic K (2 + 2)).1 z
  have h5 : E ≤ Real.exp C₀ * qht z ^ ⌈c₀⌉₊ := by
    rw [← Real.exp_log (lt_of_lt_of_le one_pos hQ), ← Real.exp_nat_mul, ← Real.exp_add, hE, Real.exp_le_exp]
    have := mul_le_mul_of_nonneg_right (Nat.le_ceil c₀) (Real.log_nonneg hQ)
    linarith [hq z]
  have h6 : ‖f z‖ * m ^ (c * N₀ + M) ≤ max 0 (max D₀ D₁) := by
    refine le_trans ?_ (le_max_right _ _)
    rcases le_total 1 (inR ρ) with h | h
    · rw [hm, max_eq_right h]
      exact (hD₁ ρ z hz hr).trans (le_max_right _ _)
    · rw [hm, max_eq_left h, one_pow, ← pow_zero (inR ρ)]
      exact (hD₀ ρ z hz hr).trans (le_max_left _ _)
  have e2 : Real.exp (2 * HH z) = E ^ 2 := by rw [hE, ← Real.exp_nat_mul]; norm_num
  have hh0 := (height_pos (z : AdelicGLn.AdelicGL K (2 + 2))).le
  calc Real.exp (2 * HH z) * ‖f z‖ * AutomorphicForm.height (z : AdelicGLn.AdelicGL K (2 + 2)) ^ N₀ * m ^ M
      ≤ E ^ 2 * ‖f z‖ * (C * (A * E * m) ^ c) ^ N₀ * m ^ M := by rw [e2]; gcongr
    _ = (C * A ^ c) ^ N₀ * (‖f z‖ * m ^ (c * N₀ + M)) * E ^ (2 + c * N₀) := by ring
    _ ≤ (C * A ^ c) ^ N₀ * max 0 (max D₀ D₁) * (Real.exp C₀ * qht z ^ ⌈c₀⌉₊) ^ (2 + c * N₀) := by gcongr
    _ = _ := by rw [mul_pow (Real.exp C₀), ← pow_mul, mul_assoc _ _ (qht z ^ _)]

private theorem fs_sum {K : Type} [Field K] [NumberField K] : ∃ (N₀ : ℕ) (C : ℝ), ∀ (x : G1 K (2 + 2)) (S : Finset (Cos K))
    (g : Cos K → ℝ) (B : ℝ), 0 ≤ B →
    (∀ q ∈ S, ∃ δ ∈ PK K, g q * AutomorphicForm.height ((δ * qx q x : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ^ N₀ ≤ B) →
    ∑ q ∈ S, g q ≤ C * B := by
  classical
  obtain ⟨N, C, hC, hs⟩ := sumHt (K := K) (2 + 2)
  refine ⟨N, C.toReal, fun x S g B hB h => ?_⟩
  set φ : Gam K (2 + 2) → ℝ := fun γ =>
    (AutomorphicForm.height (((γ : G1 K (2 + 2)) * x : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ^ N)⁻¹ with hφ
  have hφ0 : ∀ γ, 0 ≤ φ γ := fun γ => inv_nonneg.2 (pow_nonneg (height_pos _).le _)
  have h' : ∀ q : Cos K, ∃ γ : Gam K (2 + 2), (Quotient.mk _ γ : Cos K) = q ∧ (q ∈ S → g q ≤ φ γ * B) := by
    intro q
    by_cases hq : q ∈ S
    · obtain ⟨_, ⟨δ, hδ, rfl⟩, hb⟩ := h q hq
      refine ⟨δ * q.out, ?_, fun _ => ?_⟩
      · refine Eq.trans (Quotient.sound ?_) (Quotient.out_eq q)
        change QuotientGroup.rightRel _ _ _
        rw [QuotientGroup.rightRel_apply]
        simpa using hδ
      · rw [hφ]
        beta_reduce
        rw [le_inv_mul_iff₀ (pow_pos (height_pos _) _), mul_comm, Subgroup.coe_mul (Gam K (2 + 2)), mul_assoc]
        exact hb
    · exact ⟨q.out, Quotient.out_eq q, fun h => absurd h hq⟩
  choose γ hγ hg using h'
  have hinj : Function.Injective γ := fun a b e => by rw [← hγ a, ← hγ b, e]
  have h1 : ∑ q ∈ S, φ (γ q) ≤ C.toReal := by
    rw [← ENNReal.ofReal_le_iff_le_toReal hC, ENNReal.ofReal_sum_of_nonneg fun q _ => hφ0 _,
      ← Finset.sum_image (f := fun a => ENNReal.ofReal (φ a)) fun a _ b _ e => hinj e]
    exact (ENNReal.sum_le_tsum _).trans (hs x)
  calc ∑ q ∈ S, g q ≤ ∑ q ∈ S, φ (γ q) * B := Finset.sum_le_sum fun q hq => hg q hq
    _ = (∑ q ∈ S, φ (γ q)) * B := (Finset.sum_mul _ _ _).symm
    _ ≤ C.toReal * B := mul_le_mul_of_nonneg_right h1 hB

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.farSum :
    ∀ {K : Type} [Field K] [NumberField K] (ω : Set (AdelicGLn.AdelicGL K (2 + 2))) (t : ℝ), Red ω t → ∀ f : G1 K (2 + 2) → ℂ, SFun f →
      (∃ (C : ℝ) (N : ℕ), ∀ (x : G1 K (2 + 2)) (S : Finset (Cos K)), (∀ q ∈ S, 0 ≤ HH (qx q x)) →
        ∑ q ∈ S, Real.exp (2 * HH (qx q x)) * ‖f (qx q x)‖ ≤ C * qht x ^ N) ∧
      ∀ (ε : ℝ) (N' : ℕ), 0 < ε → ∃ C : ℝ, ∀ (x : G1 K (2 + 2)) (S : Finset (Cos K)), (∀ q ∈ S, 0 ≤ HH (qx q x) ∧ Far ω t ε (qx q x)) →
        ∑ q ∈ S, Real.exp (2 * HH (qx q x)) * ‖f (qx q x)‖ ≤ C * (qht x ^ N')⁻¹ := by
  intro K _ _ ω t hred f hf
  obtain ⟨N₀, C, hsum⟩ := fs_sum (K := K)
  obtain ⟨N₁, hp⟩ := fs_point ω t hred.bor hred.pos f hf N₀
  obtain ⟨hq1, hq2, -⟩ := qhtBasic K (2 + 2)
  have hqx : ∀ (q : Cos K) (x : G1 K (2 + 2)), qht (qx q x) = qht x := fun q x => hq2 _ q.out.2 x
  have hqδ : ∀ δ ∈ PK K, ∀ z : G1 K (2 + 2), qht (δ * z) = qht z := by
    rintro _ ⟨δ, -, rfl⟩ z
    exact hq2 _ δ.2 z
  have hH := (hpSpec (K := K)).2.2.1
  refine ⟨?_, fun ε N' hε => ?_⟩
  · obtain ⟨D, hD, h⟩ := hp 0
    refine ⟨C * D, N₁, fun x S hS => ?_⟩
    rw [mul_assoc]
    refine hsum x S _ _ (mul_nonneg hD (pow_nonneg (zero_le_one.trans (hq1 x)) _)) fun q hq => ?_
    obtain ⟨δ, hδ, ρ, h1, h2⟩ := hred.rel (qx q x)
    have h3 := h ρ _ h1 h2 (by rw [hH δ hδ]; exact hS q hq)
    rw [pow_zero, mul_one, hH δ hδ, hf.rat δ hδ, hqδ δ hδ, hqx] at h3
    exact ⟨δ, hδ, h3⟩
  · obtain ⟨D, hD, h⟩ := hp ⌈((N₁ + N' : ℕ) : ℝ) / ε⌉₊
    refine ⟨C * D, fun x S hS => ?_⟩
    rw [mul_assoc]
    have hx0 : 0 < qht x := one_pos.trans_le (hq1 x)
    refine hsum x S _ _ (by positivity) fun q hq => ?_
    obtain ⟨h0, δ, hδ, ρ, h1, h2, h4⟩ := hS q hq
    have h3 := h ρ _ h1 h2 (by rw [hH δ hδ]; exact h0)
    rw [hH δ hδ, hf.rat δ hδ, hqδ δ hδ, hqx] at h3
    rw [hqx] at h4
    refine ⟨δ, hδ, ?_⟩
    have h5 : qht x ^ (N₁ + N') ≤ max 1 (inR ρ) ^ ⌈((N₁ + N' : ℕ) : ℝ) / ε⌉₊ := by
      refine le_trans ?_ (pow_le_pow_left₀ (Real.rpow_nonneg hx0.le ε) (h4.trans (le_max_right _ _)) _)
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      refine Real.rpow_le_rpow_of_exponent_le (hq1 x) ?_
      rw [mul_comm, ← div_le_iff₀ hε]
      exact Nat.le_ceil _
    have hh0 := (height_pos ((δ * qx q x : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2))).le
    have h6 := (mul_le_mul_of_nonneg_left h5 (by positivity)).trans h3
    rw [pow_add, mul_comm (qht x ^ N₁), ← mul_assoc, mul_le_mul_iff_left₀ (pow_pos hx0 _)] at h6
    rwa [← div_eq_mul_inv, le_div_iff₀ (pow_pos hx0 _)]
end

section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate Pointwise Manifold ContDiff

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_bump {K : Type} [Field K] [NumberField K] {n : ℕ} {L : Set (ArchMatrix K n)}
    (hL : IsCompact L) (hLu : L ⊆ {x | IsUnit x}) :
    ∃ χ : ArchMatrix K n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧ (∀ x ∈ L, χ x = 1) ∧
      tsupport χ ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n) := by
  obtain ⟨M, hM, hLM, hMu⟩ := exists_compact_between hL Units.isOpen hLu
  obtain ⟨f, h1, h0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior (n := ⊤)
    𝓘(ℝ, ArchMatrix K n) hL.isClosed hLM
  have hsub : tsupport f ⊆ M :=
    closure_minimal (fun x hx => by_contra fun h => hx (h0 x h)) hM.isClosed
  refine ⟨f, f.contMDiff.contDiff, hM.of_isClosed_subset (isClosed_tsupport _) hsub,
    fun x hx => (h1.filter_mono (nhds_le_nhdsSet hx)).self_of_nhds, fun x hx => ?_⟩
  obtain ⟨u, rfl⟩ := hMu (hsub hx)
  exact ⟨u, rfl⟩

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_test {K : Type} [Field K] [NumberField K] {n : ℕ} {f : archGroup K n → ℂ}
    (hf : (isExpLieAlgebra K n).IsSmoothFun f) {χ : ArchMatrix K n → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχu : tsupport χ ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n)) :
    (isExpLieAlgebra K n).IsTestFunction
      (fun a : archGroup K n => (χ ((a : ArchUnits K n) : ArchMatrix K n) : ℂ) * f a) := by
  refine ⟨((isExpLieAlgebra K n).isSmoothFun_iff).2 fun g => ?_, ?_⟩
  · refine ContDiff.mul ?_ (((isExpLieAlgebra K n).isSmoothFun_iff).1 hf g)
    have e : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun Y : archLie K n =>
        (((g * (isExpLieAlgebra K n).expG Y : archGroup K n) : ArchUnits K n) : ArchMatrix K n) := by
      have : (fun Y : archLie K n =>
          (((g * (isExpLieAlgebra K n).expG Y : archGroup K n) : ArchUnits K n) : ArchMatrix K n)) =
          fun Y : archLie K n => ((g : ArchUnits K n) : ArchMatrix K n) * NormedSpace.exp (Y : ArchMatrix K n) := by
        funext Y
        simp only [Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG]
      rw [this]
      exact contDiff_const.mul ((contDiff_exp ℝ (ArchMatrix K n)).comp (archLie K n).subtypeL.contDiff)
    exact Complex.ofRealCLM.contDiff.comp (hχ.comp e)
  · refine HasCompactSupport.intro
      ((isCompact_unitsSupport hχc hχu).image (archGroupEquiv K n).symm.continuous) fun a ha => ?_
    have : ((a : ArchUnits K n) : ArchMatrix K n) ∉ tsupport χ := fun h =>
      ha ⟨(a : ArchUnits K n), h, (archGroupEquiv K n).symm_apply_apply a⟩
    rw [image_eq_zero_of_notMem_tsupport this, Complex.ofReal_zero, zero_mul]

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_local {K : Type} [Field K] [NumberField K] {n : ℕ} {f : archGroup K n → ℂ}
    (hf : (isExpLieAlgebra K n).IsSmoothFun f) {T : Set (archGroup K n)} (hT : IsCompact T) (k : ℕ) (R : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (Y : Fin k → ArchMatrix K n), (∀ i j, Y i * Y j = 0) → (∀ i, ‖Y i‖ ≤ R) →
      ∀ C : (Fin k → Bool) → ArchUnits K n, (∀ ε, ((C ε : ArchUnits K n) : ArchMatrix K n) = 1 + altPoint Y ε) →
      ∀ A ∈ T, ‖∑ ε, (altSign ε : ℂ) * f ⟨(C ε)⁻¹ * (A : ArchUnits K n), Subgroup.mem_top _⟩‖ ≤ c * ∏ i, ‖Y i‖ := by
  set T₀ : Set (ArchUnits K n) := (fun a : archGroup K n => (a : ArchUnits K n)) '' T with hT₀
  have hT₀c : IsCompact T₀ := hT.image continuous_subtype_val
  set T₁ : Set (ArchUnits K n) := (unipBall (K := K) (n := n) (k * R))⁻¹ * T₀ with hT₁
  have hT₁c : IsCompact T₁ := (isCompact_unipBall _).inv.mul hT₀c
  set L : Set (ArchMatrix K n) := (Units.val : ArchUnits K n → ArchMatrix K n) '' T₁ with hLdef
  have hLc : IsCompact L := hT₁c.image Units.continuous_val
  have hLu : L ⊆ {x | IsUnit x} := by
    rintro _ ⟨u, -, rfl⟩
    exact u.isUnit
  obtain ⟨χ, hχ, hχc, hχ1, hχu⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_bump hLc hLu
  have hκ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_test hf hχ hχc hχu
  obtain ⟨B, hB⟩ := exists_norm_altSum_le (contDiff_matExt hκ) (hasCompactSupport_matExt hκ.2) k
  obtain ⟨Rt, hRt⟩ := hT₀c.exists_bound_of_continuousOn
    (Units.continuous_val (M := ArchMatrix K n)).continuousOn
  refine ⟨max B 0 * max Rt 0 ^ k, mul_nonneg (le_max_right _ _) (pow_nonneg (le_max_right _ _) _),
    fun Y hY hR C hC A hA => ?_⟩
  have hAT₀ : (A : ArchUnits K n) ∈ T₀ := ⟨A, hA, rfl⟩
  set v : Fin k → ArchMatrix K n := fun i => -(Y i * ((A : ArchUnits K n) : ArchMatrix K n)) with hv
  have hsum : ∑ ε, (altSign ε : ℂ) * f ⟨(C ε)⁻¹ * (A : ArchUnits K n), Subgroup.mem_top _⟩ =
      altSum k (matExt K n fun a : archGroup K n => (χ ((a : ArchUnits K n) : ArchMatrix K n) : ℂ) * f a) v
        ((A : ArchUnits K n) : ArchMatrix K n) := by
    rw [altSum_eq_sum]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [← val_inv_mul_eq hY (hC ε) (A : ArchUnits K n), zsmul_eq_mul]
    have hm := matExt_val (K := K) (n := n)
      (fun a : archGroup K n => (χ ((a : ArchUnits K n) : ArchMatrix K n) : ℂ) * f a)
      ⟨(C ε)⁻¹ * (A : ArchUnits K n), Subgroup.mem_top _⟩
    have hin : (((C ε)⁻¹ * (A : ArchUnits K n) : ArchUnits K n) : ArchMatrix K n) ∈ L :=
      ⟨_, ⟨(C ε)⁻¹, Set.inv_mem_inv.2 (mem_unipBall_of_val_eq hY hR (hC ε)), _, hAT₀, rfl⟩, rfl⟩
    simp only at hm
    rw [hm, hχ1 _ hin, Complex.ofReal_one, one_mul]
  rw [hsum]
  refine (hB v _).trans ?_
  have hA' : ‖((A : ArchUnits K n) : ArchMatrix K n)‖ ≤ max Rt 0 := (hRt _ hAT₀).trans (le_max_left _ _)
  have hprod : ∏ i, ‖v i‖ ≤ (∏ i, ‖Y i‖) * max Rt 0 ^ k := by
    rw [← Fin.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
    rw [hv, norm_neg]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hA' (norm_nonneg _))
  calc B * ∏ i, ‖v i‖ ≤ max B 0 * ∏ i, ‖v i‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
    _ ≤ max B 0 * ((∏ i, ‖Y i‖) * max Rt 0 ^ k) := mul_le_mul_of_nonneg_left hprod (le_max_right _ _)
    _ = max B 0 * max Rt 0 ^ k * ∏ i, ‖Y i‖ := by ring

private def UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.DiffBdOn {K : Type} [Field K] [NumberField K] {n : ℕ} (a : CC K n) (k : ℕ) (R : ℝ)
    (s : Set (G1 K n)) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ ∀ (Y : Fin k → ArchMatrix K n), (∀ i j, Y i * Y j = 0) → (∀ i, ‖Y i‖ ≤ R) →
    ∀ C : (Fin k → Bool) → ArchUnits K n, (∀ ε, ((C ε : ArchUnits K n) : ArchMatrix K n) = 1 + altPoint Y ε) →
    ∀ w ∈ s, ‖∑ ε, (altSign ε : ℂ) * a ((archProj K n (C ε))⁻¹ * w)‖ ≤ c * ∏ i, ‖Y i‖

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_split {K : Type} [Field K] [NumberField K] {n : ℕ} {g : G1 K n}
    {u : AdelicGLn.integralFiniteGL K n} (hu : finPart K n (g : AdelicGLn.AdelicGL K n) = u) :
    g = finOne K n u * archP K n (infPart K n (g : AdelicGLn.AdelicGL K n)) := by
  have hd : detA K n (infPart K n (g : AdelicGLn.AdelicGL K n)) = 1 :=
    detA_infPart (hu ▸ u.2)
  have hp : (archP K n (infPart K n (g : AdelicGLn.AdelicGL K n)) : AdelicGLn.AdelicGL K n) =
      infEmb K n (infPart K n (g : AdelicGLn.AdelicGL K n)) := by
    rw [← retract_infEmb, coe_retractOne]
    have : detModule K n (infEmb K n (infPart K n (g : AdelicGLn.AdelicGL K n))) = 1 := hd
    rw [this, map_one, inv_one, mul_one]
  rw [← archimedeanProjection_mul_finiteEmbedding_comm]
  ext1
  rw [Subgroup.coe_mul, hp, coe_finOne, ← hu, infEmb_infPart_mul_finEmb_finPart]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (a : CC K n), IsLeftSmooth a → ∀ (k : ℕ) (R : ℝ), ∃ c : ℝ, ∀ (Y : Fin k → ArchMatrix K n), (∀ i j, Y i * Y j = 0) → (∀ i, ‖Y i‖ ≤ R) →
      ∀ C : (Fin k → Bool) → ArchUnits K n, (∀ ε, ((C ε : ArchUnits K n) : ArchMatrix K n) = 1 + altPoint Y ε) → ∀ w : G1 K n,
        ‖∑ ε, (altSign ε : ℂ) * a ((archProj K n (C ε))⁻¹ * w)‖ ≤ c * ∏ i, ‖Y i‖ := by
  intro K _ _ n a ha k R
  obtain ⟨hsm, U, hUo, hU⟩ := ha
  set Ω : Set (G1 K n) := (archProj K n '' unipBall (K := K) (n := n) (k * R)) * tsupport a with hΩdef
  have hΩ : IsCompact Ω :=
    ((isCompact_unipBall _).image continuous_archProj).mul a.hasCompactSupport
  have key : UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.DiffBdOn a k R Ω := by
    refine hΩ.induction_on ?_ ?_ ?_ ?_
    · exact ⟨0, le_rfl, fun _ _ _ _ _ w hw => absurd hw (Set.notMem_empty w)⟩
    · rintro s t hst ⟨c, hc, h⟩
      exact ⟨c, hc, fun Y hY hR C hC w hw => h Y hY hR C hC w (hst hw)⟩
    · rintro s t ⟨c, hc, h⟩ ⟨d, hd, h'⟩
      refine ⟨max c d, le_max_of_le_left hc, fun Y hY hR C hC w hw => ?_⟩
      have hp : 0 ≤ ∏ i, ‖Y i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
      rcases hw with hw | hw
      · exact (h Y hY hR C hC w hw).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)
      · exact (h' Y hY hR C hC w hw).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp)
    · intro x _
      have hcm : Continuous fun w : G1 K n => w * x⁻¹ := continuous_id.mul continuous_const
      set V : Set (G1 K n) := (fun w : G1 K n => w * x⁻¹) ⁻¹' finUSet U hUo with hV
      have hVc : IsClopen V := (isClopen_finUSet U hUo).preimage hcm
      have hxV : x ∈ V := by
        show x * x⁻¹ ∈ finUSet U hUo
        rw [mul_inv_cancel]
        show finPart K n ((1 : G1 K n) : AdelicGLn.AdelicGL K n) ∈ (finOpenSubgroup U hUo : Set _)
        rw [Subgroup.coe_one, map_one]
        exact one_mem (finOpenSubgroup U hUo)
      refine ⟨Ω ∩ V, inter_mem_nhdsWithin _ (hVc.isOpen.mem_nhds hxV), ?_⟩
      have hTc : IsCompact ((fun w : G1 K n => infPart K n ((w * x⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n)) '' (Ω ∩ V)) :=
        (hΩ.inter_right hVc.isClosed).image
          (continuous_infPart.comp (continuous_subtype_val.comp hcm))
      obtain ⟨c, hc, h⟩ := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_local (hsm x) hTc k R
      refine ⟨c, hc, fun Y hY hR C hC w hw => ?_⟩
      have hwV : finPart K n ((w * x⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n) ∈
          (finOpenSubgroup U hUo : Set (AdelicGLn.FiniteAdelicGL K n)) := hw.2
      rw [coe_openSubgroupOf] at hwV
      obtain ⟨u, huU, hu⟩ := hwV
      have hg := UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.diffBd_split hu.symm
      obtain ⟨b, hbdef⟩ : ∃ b, b = infPart K n ((w * x⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n) := ⟨_, rfl⟩
      rw [← hbdef] at hg
      have hb := h Y hY hR C hC b ⟨w, hw, hbdef.symm⟩
      have hw' : w = finOne K n u * archP K n b * x := by
        rw [← hg, inv_mul_cancel_right]
      have hterm : ∀ ε, a ((archProj K n (C ε))⁻¹ * w) =
          a (archP K n ⟨(C ε)⁻¹ * (b : ArchUnits K n), Subgroup.mem_top _⟩ * x) := by
        intro ε
        have hpb : archP K n ⟨(C ε)⁻¹ * (b : ArchUnits K n), Subgroup.mem_top _⟩ =
            (archProj K n (C ε))⁻¹ * archP K n b := by
          rw [archimedeanProjection_apply, map_mul, map_inv, archimedeanProjection_apply]
        have e : (archProj K n (C ε))⁻¹ * w =
            finOne K n u * (archP K n ⟨(C ε)⁻¹ * (b : ArchUnits K n), Subgroup.mem_top _⟩ * x) := by
          rw [hpb, hw', ← mul_assoc, ← mul_assoc, ← mul_assoc, archProj_inv_mul_finOne]
          simp only [mul_assoc]
        rw [e, hU u huU]
      have hs : ∑ ε, (altSign ε : ℂ) * a ((archProj K n (C ε))⁻¹ * w) =
          ∑ ε, (altSign ε : ℂ) * a (archP K n ⟨(C ε)⁻¹ * (b : ArchUnits K n), Subgroup.mem_top _⟩ * x) :=
        Finset.sum_congr rfl fun ε _ => by rw [hterm ε]
      rw [hs]
      exact hb
  obtain ⟨c, hc, h⟩ := key
  refine ⟨c, fun Y hY hR C hC w => ?_⟩
  by_cases hw : w ∈ Ω
  · exact h Y hY hR C hC w hw
  · have hz : ∑ ε, (altSign ε : ℂ) * a ((archProj K n (C ε))⁻¹ * w) = 0 := by
      refine Finset.sum_eq_zero fun ε _ => ?_
      have : (archProj K n (C ε))⁻¹ * w ∉ tsupport a := fun hs =>
        hw ⟨archProj K n (C ε), ⟨C ε, mem_unipBall_of_val_eq hY hR (hC ε), rfl⟩, _, hs, mul_inv_cancel_left _ _⟩
      rw [image_eq_zero_of_notMem_tsupport this, mul_zero]
    rw [hz, norm_zero]
    exact mul_nonneg hc (Finset.prod_nonneg fun i _ => norm_nonneg _)
end

section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

open scoped Pointwise

private theorem sub_ct_le_of_altSum {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] (f : CC K n) (φ : L2 μ) {r M : ℕ} (hM : 0 < M) (x : G1 K n) (k : ℕ) {B : ℝ}
    (hB : ∀ y : Fin (k + 1) → UPos n r → 𝔸[K], (∀ i, y i ∈ scaledUnipFD K n r M) →
      ‖altSum (k + 1) (fun s => rc μ f φ (unipOne K n r s * x)) y 0‖ ≤ B) :
    ‖rc μ f φ x - ct r (rc μ f φ) x‖ ≤ B := by
  set H : (UPos n r → 𝔸[K]) → ℂ := fun s => rc μ f φ (unipOne K n r s * x) with hH
  set c : ℂ := ct r (rc μ f φ) x with hc
  have hHc : Continuous H :=
    (continuous_rconv (Gam K n) μ f φ).comp ((continuous_unipOne r).mul continuous_const)
  have hper : ∀ ξ ∈ unipLattice K n r, ∀ s, H (ξ + s) = H s := by
    intro ξ hξ s
    simp only [H, rc]
    rw [unipOne_add, mul_assoc,
      rconv_mul_left (Gam K n) μ f φ (unipOne_mem_rationalGLOne r ⟨ξ, hξ⟩)]
  have hD := isAddFundamentalDomain_scaledUnipFD (K := K) (n := n) (r := r) hM
  have hD1 := unipMeasure_scaledUnipFD (K := K) (n := n) (r := r) hM
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_scaledUnipFD (K := K) (n := n) r hM
  have hint : ∀ t, IntegrableOn (fun y => H (t + y)) (scaledUnipFD K n r M) (unipMeasure K n r) :=
    fun t => ((hHc.comp (continuous_const.add continuous_id)).continuousOn.integrableOn_compact
      hC).mono_set hDC
  have hcint : IntegrableOn (fun _ : UPos n r → 𝔸[K] => c) (scaledUnipFD K n r M) (unipMeasure K n r) :=
    integrableOn_const (by rw [hD1]; exact ENNReal.one_ne_top)
  have hmean0 : ∫ y in scaledUnipFD K n r M, H y ∂unipMeasure K n r = c := by
    rw [hD.setIntegral_eq isAddFundamentalDomain_unipFundamentalDomain fun ξ s => hper ξ ξ.2 s]
    rfl
  have hi0 : IntegrableOn H (scaledUnipFD K n r M) (unipMeasure K n r) := by simpa using hint 0
  have hmean : ∫ y in scaledUnipFD K n r M, (H y - c) ∂unipMeasure K n r = 0 := by
    rw [integral_sub hi0 hcint, hmean0, setIntegral_const, measureReal_def, hD1]
    simp
  have h0 := norm_le_of_forall_altSum_le hD hD1 (k + 1) (fun s => H s - c)
    (fun ξ hξ s => by simp only [hper ξ hξ s]) (fun t => (hint t).sub hcint) hmean B (fun y hy => by
      have := hB y hy
      rw [altSum_succ] at this ⊢
      simpa only [sub_sub_sub_cancel_right] using this)
  simpa [H, unipOne_zero] using h0

private theorem sub_ct_le_of_altSum_inf {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] (f : CC K n) (φ : L2 μ) {r M : ℕ} (hM : 0 < M) (x : G1 K n)
    (hfin : ∀ z : UPos n r → 𝔸[K], (∀ p, (z p).1 = 0) →
      (∀ p, ∃ a ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K,
        (z p).2 = (M : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) * a) →
      ∀ w, f ((x⁻¹ * unipOne K n r z * x)⁻¹ * w) = f w)
    (k : ℕ) {B : ℝ}
    (hB : ∀ y : Fin (k + 1) → UPos n r → 𝔸[K], (∀ i, y i ∈ scaledUnipFD K n r M) →
      ‖altSum (k + 1) (fun s => rc μ f φ (unipOne K n r (truncInf s) * x)) y 0‖ ≤ B) :
    ‖rc μ f φ x - ct r (rc μ f φ) x‖ ≤ B := by
  refine sub_ct_le_of_altSum (r := r) μ f φ hM x k fun y hy => ?_
  have key : ∀ ε : Fin (k + 1) → Bool,
      rc μ f φ (unipOne K n r (0 + altPoint y ε) * x) =
        rc μ f φ (unipOne K n r (truncInf (0 + altPoint y ε)) * x) := by
    intro ε
    rw [zero_add]
    have hfinP := hfin (truncFin (altPoint y ε)) (fun p => rfl) fun p => by
      obtain ⟨a, ha, hPa⟩ := exists_finite_altPoint_eq_natCast_mul hM y hy ε p
      exact ⟨a, ha, hPa⟩
    have hP : unipOne K n r (altPoint y ε) * x = unipOne K n r (truncInf (altPoint y ε)) * x *
        (x⁻¹ * unipOne K n r (truncFin (altPoint y ε)) * x) := by
      simp only [mul_assoc, mul_inv_cancel_left]
      rw [← mul_assoc, ← unipOne_add, truncInf_add_truncFin]
    rw [hP]
    exact rconv_mul_right μ f φ hfinP _
  have heq : altSum (k + 1) (fun s => rc μ f φ (unipOne K n r s * x)) y 0 =
      altSum (k + 1) (fun s => rc μ f φ (unipOne K n r (truncInf s) * x)) y 0 := by
    rw [altSum_eq_sum, altSum_eq_sum]
    exact Finset.sum_congr rfl fun ε _ => congrArg (altSign ε • ·) (key ε)
  rw [heq]
  exact hB y hy

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.rootDecay :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (a : CC K n), IsLeftSmooth a → ∀ (ω : Set (AdelicGLn.AdelicGL K n)) (t : ℝ), Bor ω → 0 < t →
      ∀ (r : ℕ) (hr : 0 < r) (hrn : r < n), ∃ N : ℕ, ∀ k : ℕ, ∃ C : ℝ, ∀ (φ : L2 μ) (ρ : Fin n → ℝ) (x : G1 K n) (R : ℝ), Sg ω ρ x → Full t ρ → 1 ≤ R → Rat R ρ →
        ‖rc μ a φ x - ct r (rc μ a φ) x‖ ≤ C * (ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩) ^ k * R ^ N * ‖φ‖ := by
  intro K _ _ n μ _ f hf ω t hBor ht r hr hrn
  obtain ⟨hω, hωB⟩ := hBor
  obtain ⟨U, hU, hUf⟩ := hf.2
  obtain ⟨V₀, hV₀c, hV₀⟩ := exists_compact_mem_nhds (1 : normOneGL K n)
  obtain ⟨Cc, N, hCc⟩ := exists_encard_le_siegel hω ht hV₀c
  refine ⟨N, fun k => ?_⟩
  obtain ⟨M, hM, hMconj⟩ := exists_natCast_conj_unipGL_mem U hU hω r
  obtain ⟨C₁, hC₁⟩ := exists_norm_archMat_conj_le hω hωB ht hr hrn
    (isCompact_scaledInfSet (K := K) M)
  set C₁' := max C₁ 0
  set R₁ := C₁' * t⁻¹
  obtain ⟨c, hc⟩ := diffBd f hf (k + 1) R₁
  set c' := max c 0
  have h𝒞 := isCompact_unipBall (K := K) (n := n) (((k + 1 : ℕ) : ℝ) * R₁)
  set Q := archProj K n '' unipBall (K := K) (n := n) (((k + 1 : ℕ) : ℝ) * R₁) *
    tsupport (f : normOneGL K n → ℂ)
  have hQ : IsCompact Q := (h𝒞.image continuous_archProj).mul f.hasCompactSupport
  obtain ⟨s, -, hs⟩ := hQ.elim_nhds_subcover (fun g => (fun y => y * g) '' V₀) fun g _ => by
    have := (Homeomorph.mulRight g).isOpenMap.image_mem_nhds hV₀
    rw [Homeomorph.coe_mulRight] at this
    simpa only [one_mul] using this
  refine ⟨c' * C₁' ^ k * R₁ * √(μ.real Q * (s.card * max Cc 0)), ?_⟩
  rintro φ ρ x R ⟨hρ, b, hb, kk, hkk, hx⟩ hsieg hR1 hR
  obtain ⟨m₀, hmC₀, hm₀⟩ := hCc b hb ρ hρ hsieg kk hkk x hx R hR1 hR
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = s.card * m₀ := ⟨_, rfl⟩
  have hm : ∀ z : normOneGL K n,
      {γ : rationalGLOne K n | γ • z ∈ (fun y => x * y) '' Q}.encard ≤ m := by
    intro z
    have := encard_le_of_subset_mul s hs hm₀ z
    rw [hmdef]
    exact_mod_cast this
  have hmC : (m : ℝ) ≤ s.card * Cc * R ^ N := by
    rw [hmdef, Nat.cast_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hmC₀ (Nat.cast_nonneg _)
  set gain := ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩
  have hgain0 : 0 ≤ gain := div_nonneg (hρ _).le (hρ _).le
  have hgain : gain ≤ t⁻¹ := by
    have h1 := hsieg ⟨r - 1, by omega⟩ ⟨r, hrn⟩ (by simp; omega)
    rw [div_le_iff₀ (hρ _), ← div_eq_inv_mul, le_div_iff₀ ht, mul_comm]
    exact h1
  have hc'0 : 0 ≤ c' := le_max_right _ _
  have hC₁'0 : 0 ≤ C₁' := le_max_right _ _
  have hgR : C₁' * gain ≤ R₁ := mul_le_mul_of_nonneg_left hgain hC₁'0
  have hg0 : 0 ≤ C₁' * gain := mul_nonneg hC₁'0 hgain0
  set b₀ := c' * ((C₁' * gain) ^ k * R₁)
  have hb₀ : 0 ≤ b₀ := mul_nonneg hc'0 (mul_nonneg (pow_nonneg hg0 _) (hg0.trans hgR))
  have hfinal : ‖rc μ f φ x - ct r (rc μ f φ) x‖ ≤ b₀ * √(μ.real Q * m) * ‖φ‖ := by
    refine sub_ct_le_of_altSum_inf (r := r) μ f φ hM x ?_ k ?_
    · intro z hz1 hz2 w
      obtain ⟨u, hu⟩ := hMconj b hb ρ hρ kk hkk z hz1 hz2
      have hxu : x⁻¹ * unipOne K n r z * x = finOne K n (u : AdelicGLn.integralFiniteGL K n) := by
        refine Subtype.ext ?_
        change (x : AdelicGLn.AdelicGL K n)⁻¹ * unipGL z * (x : AdelicGLn.AdelicGL K n) =
          finEmb K n _
        rw [hx]
        exact hu
      rw [hxu, ← map_inv]
      exact hUf _ (U.inv_mem u.2) w
    · intro y hy
      set Y : Fin (k + 1) → ArchMatrix K n :=
        fun i => conjArch K n (x : AdelicGLn.AdelicGL K n) (truncInf (y i))
      have hYY : ∀ i j, Y i * Y j = 0 := fun i j => conjArch_mul_conjArch _ _ _
      have hYn : ∀ i, ‖Y i‖ ≤ C₁' * gain := by
        intro i
        have h1 := hC₁ b hb ρ hρ hsieg kk hkk (truncInf (y i)) (fun p => rfl)
          (fun p => infinite_mem_scaledInfSet hM (hy i) p)
        have h2 : Y i = archMat K n ((((b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) *
            kk)⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) *
            blockEntry (truncInf (y i)) * ((b * diagUnits n (fun i => posIdele (K := K) (ρ i)
              (hρ i)) * kk : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])) := by
          simp only [Y, conjArch, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hx]
        rw [h2]
        exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hgain0)
      have hYR : ∀ i, ‖Y i‖ ≤ R₁ := fun i => (hYn i).trans hgR
      have hex : ∀ ε : Fin (k + 1) → Bool, ∃ C : ArchUnits K n,
          archProj K n C = x⁻¹ * unipOne K n r (truncInf (altPoint y ε)) * x ∧
            (C : ArchMatrix K n) = 1 + altPoint Y ε := by
        intro ε
        obtain ⟨C, hC1, hC2⟩ := exists_archProj_eq_conj x (truncInf (altPoint y ε)) fun p => rfl
        refine ⟨C, hC1, ?_⟩
        rw [hC2, ← truncInfHom_apply, map_altPoint (truncInfHom n r),
          map_altPoint (conjArch K n (x : AdelicGLn.AdelicGL K n))]
        rfl
      choose Cε hCε1 hCε2 using hex
      have hsum : altSum (k + 1) (fun s => rc μ f φ (unipOne K n r (truncInf s) * x)) y 0 =
          ∑ ε, (altSign ε : ℂ) * rconv (rationalGLOne K n) μ f φ (x * archProj K n (Cε ε)) := by
        rw [altSum_eq_sum]
        refine Finset.sum_congr rfl fun ε _ => ?_
        rw [zero_add, hCε1 ε, zsmul_eq_mul]
        have : x * (x⁻¹ * unipOne K n r (truncInf (altPoint y ε)) * x) =
            unipOne K n r (truncInf (altPoint y ε)) * x := by group
        rw [this]
      rw [hsum]
      have hb' : ∀ w, ‖∑ ε, (altSign ε : ℂ) * f ((archProj K n (Cε ε))⁻¹ * w)‖ ≤ b₀ := by
        intro w
        refine (hc Y hYY hYR Cε hCε2 w).trans ?_
        have hprod : ∏ i, ‖Y i‖ ≤ (C₁' * gain) ^ (k + 1) := by
          rw [← Fin.prod_const]
          exact Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hYn i
        have hprod' : ∏ i, ‖Y i‖ ≤ (C₁' * gain) ^ k * R₁ := by
          refine hprod.trans ?_
          rw [pow_succ]
          exact mul_le_mul_of_nonneg_left hgR (pow_nonneg hg0 _)
        calc c * ∏ i, ‖Y i‖ ≤ c' * ∏ i, ‖Y i‖ :=
              mul_le_mul_of_nonneg_right (le_max_left _ _)
                (Finset.prod_nonneg fun i _ => norm_nonneg _)
          _ ≤ b₀ := mul_le_mul_of_nonneg_left hprod' hc'0
      have hmem : ∀ ε, Cε ε ∈ unipBall (K := K) (n := n) (((k + 1 : ℕ) : ℝ) * R₁) := fun ε =>
        mem_unipBall_of_val_eq hYY hYR (hCε2 ε)
      have hsq := enorm_sum_altSign_rconv_sq_le μ f φ x h𝒞 Cε hmem hb' hm
      have hA : ENNReal.ofReal b₀ ^ 2 * μ Q * (m : ℝ≥0∞) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hQ.measure_lt_top.ne) (by simp)
      have hle := norm_le_of_enorm_sq_le hA (by rw [mul_assoc]; exact hsq)
      refine hle.trans (le_of_eq ?_)
      congr 1
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hb₀,
        ENNReal.toReal_natCast, Real.sqrt_mul (by positivity), Real.sqrt_mul' _ (by positivity),
        Real.sqrt_sq hb₀, measureReal_def, mul_assoc, Real.sqrt_mul ENNReal.toReal_nonneg]
  refine hfinal.trans ?_
  have hμQ : 0 ≤ μ.real Q := measureReal_nonneg
  have hRN : 1 ≤ R ^ N := one_le_pow₀ hR1
  have hm' : (m : ℝ) ≤ s.card * max Cc 0 * R ^ N :=
    hmC.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_left _ _)
      (Nat.cast_nonneg _)) (pow_nonneg (by linarith) _))
  have hsqrt : √(μ.real Q * m) ≤ √(μ.real Q * (s.card * max Cc 0)) * √(R ^ N) := by
    rw [← Real.sqrt_mul (mul_nonneg hμQ (mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)))]
    refine Real.sqrt_le_sqrt ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hm' hμQ
  have hsR : √(R ^ N) ≤ R ^ N := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hsqrt' : √(μ.real Q * m) ≤ √(μ.real Q * (s.card * max Cc 0)) * R ^ N :=
    hsqrt.trans (mul_le_mul_of_nonneg_left hsR (Real.sqrt_nonneg _))
  calc b₀ * √(μ.real Q * m) * ‖φ‖
      ≤ b₀ * (√(μ.real Q * (s.card * max Cc 0)) * R ^ N) * ‖φ‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt' hb₀) (norm_nonneg _)
    _ = c' * C₁' ^ k * R₁ * √(μ.real Q * (s.card * max Cc 0)) * gain ^ k * R ^ N * ‖φ‖ := by
        simp only [b₀, mul_pow]
        ring
end

section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

private theorem p0_mem {H V W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {J : L V →ₗᵢ[ℂ] H} {J' : L W →ₗᵢ[ℂ] H} {P : H →L[ℂ] H} (hP : IsOrthogonalProjectionTwoLines J J' P) (S : Submodule ℂ H)
    (hS : IsClosed (S : Set H)) (h₁ : ∀ u, J u ∈ S) (h₂ : ∀ v, J' v ∈ S) (φ : H) : P φ ∈ S := by
  haveI : CompleteSpace S := hS.completeSpace_coe
  rw [← S.orthogonal_orthogonal, Submodule.mem_orthogonal]
  intro w hw
  have h0 : P w = 0 := (hP.2.2 w).2
    ⟨fun u => Submodule.inner_right_of_mem_orthogonal (h₁ u) hw, fun v => Submodule.inner_right_of_mem_orthogonal (h₂ v) hw⟩
  have h := hP.1.isSymmetric w φ
  simp only [ContinuousLinearMap.coe_coe] at h
  rw [← h, h0, inner_zero_left]

private theorem ct_rc_zero {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    (f : CC K n) (φ : L2 μ) (r : ℕ) (hφ : constantTermL2 μ r φ =ᵐ[μ] 0) (x : G1 K n) : ct r (rc μ f φ) x = 0 := by
  change ∫ X in unipFundamentalDomain K n r, rconv (rationalGLOne K n) μ f φ (unipOne K n r X * x)
      ∂unipMeasure K n r = 0
  haveI : SigmaCompactSpace (normOneGL K n) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite μ
  haveI : SFinite μ := instSFiniteOfSigmaFinite
  set S := (x * ·) '' tsupport (f : normOneGL K n → ℂ)
  have hS : IsCompact S := f.hasCompactSupport.isCompact.image (continuous_const_mul x)
  obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  have hfS : ∀ z ∉ S, f (x⁻¹ * z) = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz ⟨x⁻¹ * z, h, by simp⟩
  set F : (UPos n r → 𝔸[K]) → normOneGL K n → ℂ :=
    fun X z => f (x⁻¹ * z) * φ (mk (rationalGLOne K n) (unipOne K n r X * z))
  have hFm : StronglyMeasurable (Function.uncurry F) :=
    (f.continuous.comp (continuous_const_mul x⁻¹ |>.comp continuous_snd)).stronglyMeasurable.mul
      ((Lp.stronglyMeasurable φ).comp_measurable ((measurable_mk (rationalGLOne K n)).comp
        (continuous_unipOne_mul r).measurable))
  have hint : Integrable (Function.uncurry F)
      (((unipMeasure K n r).restrict (unipFundamentalDomain K n r)).prod μ) := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    obtain ⟨C, hC, hCφ⟩ := exists_lintegral_unip_sq_le μ r hS
    have hfin : ∫⁻ z in S, ∫⁻ X in unipFundamentalDomain K n r,
        ‖φ (mk (rationalGLOne K n) (unipOne K n r X * z))‖ₑ ∂unipMeasure K n r ∂μ < ⊤ :=
      L2Kernel.lt_top_of_sq_lt_top ((hCφ φ).trans_lt
        (ENNReal.mul_lt_top hC.lt_top (ENNReal.pow_lt_top enorm_lt_top)))
    have hmeas : Measurable fun p : (UPos n r → 𝔸[K]) × normOneGL K n =>
        ‖φ (mk (rationalGLOne K n) (unipOne K n r p.1 * p.2))‖ₑ :=
      ((Lp.stronglyMeasurable φ).measurable.comp ((measurable_mk (rationalGLOne K n)).comp
        (continuous_unipOne_mul r).measurable)).enorm
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hFm.aestronglyMeasurable.enorm]
    calc ∫⁻ X in unipFundamentalDomain K n r, ∫⁻ z, ‖Function.uncurry F (X, z)‖ₑ ∂μ ∂unipMeasure K n r
        ≤ ∫⁻ X in unipFundamentalDomain K n r, ∫⁻ z in S,
            ENNReal.ofReal M * ‖φ (mk (rationalGLOne K n) (unipOne K n r X * z))‖ₑ ∂μ ∂unipMeasure K n r := by
          refine lintegral_mono fun X => ?_
          rw [← lintegral_indicator hS.measurableSet]
          refine lintegral_mono fun z => ?_
          by_cases hz : z ∈ S
          · rw [indicator_of_mem hz]
            simp only [F, Function.uncurry_apply_pair, enorm_mul]
            gcongr
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hM _)
          · rw [indicator_of_notMem hz]
            simp [F, hfS z hz]
      _ = ENNReal.ofReal M * ∫⁻ z in S, ∫⁻ X in unipFundamentalDomain K n r,
            ‖φ (mk (rationalGLOne K n) (unipOne K n r X * z))‖ₑ ∂unipMeasure K n r ∂μ := by
          simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          exact lintegral_lintegral_swap hmeas.aemeasurable
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  have hinner : ∀ X, rconv (rationalGLOne K n) μ f φ (unipOne K n r X * x) = ∫ z, F X z ∂μ := by
    intro X
    rw [rconv, ← integral_mul_left_eq_self _ (unipOne K n r X)]
    congr 1
    ext z
    simp only [F, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  have hCT : ∀ z, ∫ X in unipFundamentalDomain K n r, F X z ∂unipMeasure K n r =
      f (x⁻¹ * z) * constantTermL2 μ r φ z := by
    intro z
    simp only [F, constantTermL2, ctFun]
    exact integral_const_mul _ _
  simp_rw [hinner]
  rw [integral_integral_swap hint]
  simp_rw [hCT]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hφ] with z hz
  rw [hz, Pi.zero_apply, mul_zero]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.ctVanish :
    ForAllC fun K _ _ μ _ _ _ _ _ _ _ _ A A' => ∀ (a : CC K (2 + 2)) (P : L2 μ →L[ℂ] L2 μ), IsOrthogonalProjectionTwoLines A.J A'.J P → (∀ φ, P φ = φ → ∀ z, ct 1 (rc μ a φ) z = 0 ∧ ct 3 (rc μ a φ) z = 0) ∧
      Pc μ ∘L P = 0 ∧ P ∘L Pc μ = 0 := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' a P hP
  have hp' : Pair μ₂ τ₂ τ₁ := ⟨hp.irr₂, hp.irr₁, hp.orth.symm⟩
  have h₁ := ctZero K μ μ₂ τ₁ τ₂ hp D d d' A A'
  have h₂ := ctZero K μ μ₂ τ₂ τ₁ hp' D d' d A' A
  refine ⟨fun φ hφ z => ⟨?_, ?_⟩, ?_, ?_⟩
  · obtain ⟨S, hS, hm⟩ := ctClosed μ 1
    refine ct_rc_zero μ a φ 1 ((hm φ).1 ?_) z
    rw [← hφ]
    exact p0_mem hP S hS (fun u => (hm _).2 (h₁ u).2.2.1) (fun u => (hm _).2 (h₂ u).2.2.1) φ
  · obtain ⟨S, hS, hm⟩ := ctClosed μ 3
    refine ct_rc_zero μ a φ 3 ((hm φ).1 ?_) z
    rw [← hφ]
    exact p0_mem hP S hS (fun u => (hm _).2 (h₁ u).2.2.2) (fun u => (hm _).2 (h₂ u).2.2.2) φ
  · refine ContinuousLinearMap.ext fun φ => ?_
    exact p0_mem hP (Pc μ).ker (Pc μ).isClosed_ker (fun u => (h₁ u).1) (fun u => (h₂ u).1) φ
  · refine ContinuousLinearMap.ext fun φ => ?_
    have hs : ∀ w, ⟪w, Pc μ φ⟫_ℂ = ⟪Pc μ w, φ⟫_ℂ := fun w => by
      unfold Pc
      exact (Submodule.inner_starProjection_left_eq_right _ w φ).symm
    refine (hP.2.2 (Pc μ φ)).2 ⟨fun u => ?_, fun v => ?_⟩
    · rw [hs, (h₁ u).1, inner_zero_left]
    · rw [hs, (h₂ v).1, inner_zero_left]
end

section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

private theorem pow_arith (c : ℝ) (hc : 0 < c) (A B : ℕ) :
    ∃ k : ℕ, ∀ y u : ℝ, 1 ≤ y → 0 ≤ u → u ≤ (y ^ c)⁻¹ → u ^ k * y ^ A ≤ (y ^ B)⁻¹ := by
  obtain ⟨k, hk⟩ := exists_nat_ge (((A : ℝ) + B) / c)
  refine ⟨k, fun y u hy hu huy => ?_⟩
  have hy0 : 0 < y := by linarith
  have hk' : (A : ℝ) + B ≤ c * k := by
    rw [div_le_iff₀ hc] at hk
    linarith
  have h1 : u ^ k ≤ ((y ^ c)⁻¹) ^ k := pow_le_pow_left₀ hu huy k
  have h2 : ((y ^ c)⁻¹) ^ k = (y ^ (c * k))⁻¹ := by
    rw [inv_pow, ← Real.rpow_natCast (y ^ c), ← Real.rpow_mul hy0.le]
  have h3 : y ^ ((A : ℝ) + B) ≤ y ^ (c * k) := Real.rpow_le_rpow_of_exponent_le hy hk'
  have h4 : y ^ ((A : ℝ) + B) = y ^ A * y ^ B := by
    rw [Real.rpow_add hy0, Real.rpow_natCast, Real.rpow_natCast]
  have hyA : 0 < y ^ A := pow_pos hy0 A
  have hyB : 0 < y ^ B := pow_pos hy0 B
  have h5 : (y ^ (c * k))⁻¹ ≤ (y ^ A * y ^ B)⁻¹ := by
    rw [← h4]
    exact inv_anti₀ (Real.rpow_pos_of_pos hy0 _) h3
  calc u ^ k * y ^ A ≤ (y ^ A * y ^ B)⁻¹ * y ^ A :=
        mul_le_mul_of_nonneg_right ((h2 ▸ h1).trans h5) hyA.le
    _ = (y ^ B)⁻¹ := by field_simp

private theorem pow_arith2 (c : ℝ) (hc : 0 < c) (N N' : ℕ) :
    ∃ k : ℕ, ∀ y R u : ℝ, 1 ≤ y → 1 ≤ R → y ^ c ≤ R → 0 ≤ u → u ≤ (R ^ c)⁻¹ →
      u ^ k * R ^ N ≤ (y ^ N')⁻¹ := by
  obtain ⟨B, hB⟩ := exists_nat_ge ((N' : ℝ) / c)
  obtain ⟨k, hk⟩ := pow_arith c hc N B
  refine ⟨k, fun y R u hy hR hyR hu huR => (hk R u hR hu huR).trans ?_⟩
  have hy0 : 0 < y := by linarith
  have hB' : (N' : ℝ) ≤ c * B := by
    rw [div_le_iff₀ hc] at hB
    linarith
  have h1 : y ^ N' ≤ (y ^ c) ^ B := by
    rw [← Real.rpow_natCast y N', ← Real.rpow_natCast (y ^ c) B, ← Real.rpow_mul hy0.le]
    exact Real.rpow_le_rpow_of_exponent_le hy hB'
  have h2 : (y ^ c) ^ B ≤ R ^ B := pow_le_pow_left₀ (Real.rpow_nonneg hy0.le _) hyR B
  exact inv_anti₀ (pow_pos hy0 _) (h1.trans h2)

section

variable {K : Type} [Field K] [NumberField K]

private theorem sec_norm_le {d : ℕ} (sec : Eu d →ₗ[ℂ] (G1 K (2 + 2) → ℂ)) (U : ℝ → Eu d) (B : ℝ)
    (hU : ∀ s, ‖U s‖ ≤ B) (z : G1 K (2 + 2)) :
    ‖secF sec U z‖ ≤ B * ∑ i, Real.exp (2 * HH z) * ‖sec (EuclideanSpace.basisFun (Fin d) ℂ i) z‖ := by
  set b := EuclideanSpace.basisFun (Fin d) ℂ with hb
  set v := U (HH z) with hv
  have hsum : sec v z = ∑ i, b.repr v i * sec (b i) z := by
    conv_lhs => rw [← b.sum_repr v]
    simp [map_sum, Finset.sum_apply]
  have hc : ∀ i, ‖b.repr v i‖ ≤ B := fun i =>
    (PiLp.norm_apply_le (b.repr v) i).trans ((b.repr.norm_map v).le.trans (hU _))
  have hexp : ‖Complex.exp (2 * (HH z : ℂ))‖ = Real.exp (2 * HH z) := by
    rw [Complex.norm_exp]
    simp
  unfold secF
  rw [norm_mul, hexp, hsum]
  have h : ‖∑ i, b.repr v i * sec (b i) z‖ ≤ ∑ i, B * ‖sec (b i) z‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _))
  calc Real.exp (2 * HH z) * ‖∑ i, b.repr v i * sec (b i) z‖
      ≤ Real.exp (2 * HH z) * ∑ i, B * ‖sec (b i) z‖ :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = B * ∑ i, Real.exp (2 * HH z) * ‖sec (b i) z‖ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring

private theorem far_fam {ι : Type} [Fintype ι] (ω : Set (AdelicGLn.AdelicGL K (2 + 2))) (t : ℝ) (hR : Red ω t)
    (f : ι → G1 K (2 + 2) → ℂ) (hf : ∀ i, SFun (f i)) :
    (∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (x : G1 K (2 + 2)) (S : Finset (Cos K)), (∀ q ∈ S, 0 ≤ HH (qx q x)) →
        ∑ q ∈ S, ∑ i, Real.exp (2 * HH (qx q x)) * ‖f i (qx q x)‖ ≤ C * qht x ^ N) ∧
      ∀ (ε : ℝ) (N' : ℕ), 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : G1 K (2 + 2)) (S : Finset (Cos K)),
        (∀ q ∈ S, 0 ≤ HH (qx q x) ∧ Far ω t ε (qx q x)) →
        ∑ q ∈ S, ∑ i, Real.exp (2 * HH (qx q x)) * ‖f i (qx q x)‖ ≤ C * (qht x ^ N')⁻¹ := by
  have hq1 : ∀ x : G1 K (2 + 2), 1 ≤ qht x := (qhtBasic K (2 + 2)).1
  constructor
  · choose C N hC using fun i => (farSum ω t hR (f i) (hf i)).1
    refine ⟨∑ i, |C i|, ∑ i, N i, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun x S hS => ?_⟩
    rw [Finset.sum_comm, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => (hC i x S hS).trans ?_
    have h0 : (0 : ℝ) < qht x ^ N i := pow_pos (by linarith [hq1 x]) _
    have h1 : qht x ^ N i ≤ qht x ^ ∑ i, N i :=
      pow_le_pow_right₀ (hq1 x) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
    exact (mul_le_mul_of_nonneg_right (le_abs_self _) h0.le).trans
      (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
  · intro ε N' hε
    choose C hC using fun i => (farSum ω t hR (f i) (hf i)).2 ε N' hε
    refine ⟨∑ i, |C i|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun x S hS => ?_⟩
    rw [Finset.sum_comm, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => (hC i x S hS).trans ?_
    have h0 : (0 : ℝ) ≤ (qht x ^ N')⁻¹ := inv_nonneg.2 (pow_nonneg (by linarith [hq1 x]) _)
    exact mul_le_mul_of_nonneg_right (le_abs_self _) h0

private theorem th_hi_eq (T : ℝ) (F : G1 K (2 + 2) → ℂ) (x : G1 K (2 + 2)) :
    ∃ S : Finset (Cos K), (∀ q, q ∈ S ↔ T < HH (qx q x)) ∧ th (hi T F) x = ∑ q ∈ S, F (qx q x) := by
  have hfin : {q : Cos K | T < HH (qx q x)}.Finite :=
    (locFin {x} T isCompact_singleton).subset fun q hq => ⟨x, rfl, le_of_lt hq⟩
  refine ⟨hfin.toFinset, fun q => by simp, ?_⟩
  unfold th
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
  · refine Finset.sum_congr rfl fun q hq => ?_
    have : T < HH (qx q x) := by simpa using hq
    exact Set.indicator_of_mem (s := {z : G1 K (2 + 2) | T < HH z}) this F
  · intro q hq
    by_contra hn
    have hn' : ¬ T < HH (qx q x) := by simpa using hn
    exact hq (Set.indicator_of_notMem (s := {z : G1 K (2 + 2) | T < HH z}) hn' F)

end

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.mainBd :
    ForAllC fun K _ _ μ _ _ _ _ _ D _ _ A A' => ∀ (a : CC K (2 + 2)) (P : L2 μ →L[ℂ] L2 μ), IsOrthogonalProjectionTwoLines A.J A'.J P → IsLeftSmooth a → D.Hecke a → ∀ N' : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : ℝ) (x : G1 K (2 + 2)) (φ : L2 μ), 0 ≤ T → P φ = φ → ¬ Om T x → ‖lam T (rc μ a φ) x‖ ≤ C * (qht x ^ N')⁻¹ * ‖φ‖ := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' a P hP ha hD N'
  classical
  obtain ⟨ω, t, hR⟩ := redEx (K := K)
  have hq1 : ∀ x : G1 K (2 + 2), 1 ≤ qht x := (qhtBasic K (2 + 2)).1
  have hfA : ∀ i, SFun (A.sec (EuclideanSpace.basisFun (Fin d) ℂ i)) := fun i => by
    have h := (A.onto (A.sec (EuclideanSpace.basisFun (Fin d) ℂ i))).1 ⟨_, rfl⟩
    exact secFun μ₂ τ₁ τ₂ D hp.irr₁ hp.irr₂ _ h.1 h.2
  have hfB : ∀ i, SFun (A'.sec (EuclideanSpace.basisFun (Fin d') ℂ i)) := fun i => by
    have h := (A'.onto (A'.sec (EuclideanSpace.basisFun (Fin d') ℂ i))).1 ⟨_, rfl⟩
    exact secFun μ₂ τ₂ τ₁ D hp.irr₂ hp.irr₁ _ h.1 h.2
  obtain ⟨⟨Ca, Na, hCa, hNa⟩, hFarA⟩ := far_fam ω t hR _ hfA
  obtain ⟨⟨Cb, Nb, hCb, hNb⟩, hFarB⟩ := far_fam ω t hR _ hfB
  obtain ⟨C₀, hC₀⟩ := ctRep K μ μ₂ τ₁ τ₂ hp D d d' A A' a P hP hD

  set G : G1 K (2 + 2) → ℝ := fun z =>
    (∑ i, Real.exp (2 * HH z) * ‖A.sec (EuclideanSpace.basisFun (Fin d) ℂ i) z‖) +
      ∑ i, Real.exp (2 * HH z) * ‖A'.sec (EuclideanSpace.basisFun (Fin d') ℂ i) z‖ with hG
  have hct : ∀ φ, P φ = φ → ∀ z, ‖ct 2 (rc μ a φ) z‖ ≤ |C₀| * ‖φ‖ * G z := by
    intro φ hφ z
    obtain ⟨U, U', -, -, hU, -, -, hrep⟩ := hC₀ φ hφ
    have hB : ∀ s, ‖U s‖ ≤ |C₀| * ‖φ‖ ∧ ‖U' s‖ ≤ |C₀| * ‖φ‖ := fun s =>
      ⟨(hU s).1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)),
        (hU s).2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))⟩
    rw [hrep z, hG]
    simp only [mul_add]
    exact (norm_add_le _ _).trans (add_le_add (sec_norm_le _ U _ (fun s => (hB s).1) z)
      (sec_norm_le _ U' _ (fun s => (hB s).2) z))
  have hsum : ∀ φ, P φ = φ → ∀ (x : G1 K (2 + 2)) (S : Finset (Cos K)),
      ‖∑ q ∈ S, ct 2 (rc μ a φ) (qx q x)‖ ≤ |C₀| * ‖φ‖ * ∑ q ∈ S, G (qx q x) := by
    intro φ hφ x S
    rw [Finset.mul_sum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => hct φ hφ _)
  obtain ⟨ε, c, Q, M, hε, hc, hgeo⟩ := geo ω t hR
  obtain ⟨CA, hCA, hA⟩ := hFarA ε N' hε
  obtain ⟨CB, hCB, hB⟩ := hFarB ε N' hε
  obtain ⟨Cp, Np, hpoly⟩ := polyBdAll K (2 + 2) μ a
  obtain ⟨N₂, h₂⟩ := rootDecay μ a ha ω t hR.bor hR.pos 2 (by norm_num) (by norm_num)
  obtain ⟨N₁, h₁⟩ := rootDecay μ a ha ω t hR.bor hR.pos 1 (by norm_num) (by norm_num)
  obtain ⟨N₃, h₃⟩ := rootDecay μ a ha ω t hR.bor hR.pos 3 (by norm_num) (by norm_num)
  obtain ⟨k₂, hk₂⟩ := pow_arith c hc (M * N₂) N'
  obtain ⟨k₁, hk₁⟩ := pow_arith2 c hc N₁ N'
  obtain ⟨k₃, hk₃⟩ := pow_arith2 c hc N₃ N'
  obtain ⟨D₂, hD₂⟩ := h₂ k₂
  obtain ⟨D₁, hD₁⟩ := h₁ k₁
  obtain ⟨D₃, hD₃⟩ := h₃ k₃
  have hvan := (ctVanish K μ μ₂ τ₁ τ₂ hp D d d' A A' a P hP).1

  set E : ℝ := |C₀| * (CA + CB) with hE
  have hE0 : 0 ≤ E := mul_nonneg (abs_nonneg _) (add_nonneg hCA hCB)
  have hfar : ∀ φ, P φ = φ → ∀ (x : G1 K (2 + 2)) (S : Finset (Cos K)),
      (∀ q ∈ S, 0 ≤ HH (qx q x) ∧ Far ω t ε (qx q x)) →
      ‖∑ q ∈ S, ct 2 (rc μ a φ) (qx q x)‖ ≤ E * (qht x ^ N')⁻¹ * ‖φ‖ := by
    intro φ hφ x S hS
    refine (hsum φ hφ x S).trans ?_
    have h : ∑ q ∈ S, G (qx q x) ≤ (CA + CB) * (qht x ^ N')⁻¹ := by
      rw [hG]
      simp only [Finset.sum_add_distrib, add_mul]
      exact add_le_add (hA x S hS) (hB x S hS)
    calc |C₀| * ‖φ‖ * ∑ q ∈ S, G (qx q x) ≤ |C₀| * ‖φ‖ * ((CA + CB) * (qht x ^ N')⁻¹) :=
          mul_le_mul_of_nonneg_left h (mul_nonneg (abs_nonneg _) (norm_nonneg _))
      _ = E * (qht x ^ N')⁻¹ * ‖φ‖ := by rw [hE]; ring

  set Q' : ℝ := max Q 1 with hQ'
  have hQ1 : 1 ≤ Q' := le_max_right _ _
  set Cs : ℝ := (|Cp| * Q' ^ Np + |C₀| * (Ca * Q' ^ Na + Cb * Q' ^ Nb)) * Q' ^ N' with hCs
  have hCs0 : 0 ≤ Cs := by
    have : (0 : ℝ) ≤ Q' := by linarith
    positivity
  refine ⟨Cs + (|D₁| + |D₂| + |D₃|) + E, by positivity, fun T x φ hT hφ hOm => ?_⟩
  set y := qht x with hy
  have hy1 : 1 ≤ y := hq1 x
  have hy0 : 0 < y := by linarith
  have hyi : 0 < (y ^ N')⁻¹ := inv_pos.2 (pow_pos hy0 _)
  have hn0 : 0 ≤ ‖φ‖ := norm_nonneg _
  set ψ := rc μ a φ with hψ
  obtain ⟨S, hS, hth⟩ := th_hi_eq T (ct 2 ψ) x
  obtain ⟨-, -, hGam₀, hPK₀, -⟩ := (ctKv μ a).2 φ
  have hGam : ∀ γ ∈ Gam K (2 + 2), ∀ x, ψ (γ * x) = ψ x := hGam₀
  have hPK : ∀ γ ∈ PK K, ∀ z, ct 2 ψ (γ * z) = ct 2 ψ z := hPK₀
  have hlam : lam T ψ x = ψ x - ∑ q ∈ S, ct 2 ψ (qx q x) := by
    rw [lam, hth]
  rw [hlam]
  have hHH : ∀ q ∈ S, 0 ≤ HH (qx q x) := fun q hq => hT.trans ((hS q).1 hq).le
  by_cases hQ : y < Q
  ·
    have hyQ : y ≤ Q' := hQ.le.trans (le_max_left _ _)
    have hpw : ∀ n : ℕ, y ^ n ≤ Q' ^ n := fun n => pow_le_pow_left₀ hy0.le hyQ n
    have h1 : ‖ψ x‖ ≤ |Cp| * Q' ^ Np * ‖φ‖ := by
      refine (hpoly φ x).trans (mul_le_mul_of_nonneg_right ?_ hn0)
      exact (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_pos hy0 _).le).trans
        (mul_le_mul_of_nonneg_left (hpw _) (abs_nonneg _))
    have h2 : ‖∑ q ∈ S, ct 2 ψ (qx q x)‖ ≤ |C₀| * (Ca * Q' ^ Na + Cb * Q' ^ Nb) * ‖φ‖ := by
      refine (hsum φ hφ x S).trans ?_
      have h : ∑ q ∈ S, G (qx q x) ≤ Ca * Q' ^ Na + Cb * Q' ^ Nb := by
        rw [hG]
        simp only [Finset.sum_add_distrib]
        exact add_le_add ((hNa x S hHH).trans (mul_le_mul_of_nonneg_left (hpw _) hCa))
          ((hNb x S hHH).trans (mul_le_mul_of_nonneg_left (hpw _) hCb))
      calc |C₀| * ‖φ‖ * ∑ q ∈ S, G (qx q x) ≤ |C₀| * ‖φ‖ * (Ca * Q' ^ Na + Cb * Q' ^ Nb) :=
            mul_le_mul_of_nonneg_left h (mul_nonneg (abs_nonneg _) hn0)
        _ = _ := by ring
    have h3 : 1 ≤ Q' ^ N' * (y ^ N')⁻¹ := by
      rw [← div_eq_mul_inv, one_le_div (pow_pos hy0 _)]
      exact hpw _
    have hB0 : 0 ≤ |Cp| * Q' ^ Np + |C₀| * (Ca * Q' ^ Na + Cb * Q' ^ Nb) := by
      have : (0 : ℝ) ≤ Q' := by linarith
      positivity
    calc ‖ψ x - ∑ q ∈ S, ct 2 ψ (qx q x)‖
        ≤ (|Cp| * Q' ^ Np + |C₀| * (Ca * Q' ^ Na + Cb * Q' ^ Nb)) * ‖φ‖ := by
          rw [add_mul]
          exact (norm_sub_le _ _).trans (add_le_add h1 h2)
      _ ≤ (|Cp| * Q' ^ Np + |C₀| * (Ca * Q' ^ Na + Cb * Q' ^ Nb)) * (Q' ^ N' * (y ^ N')⁻¹) * ‖φ‖ :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hB0 h3) hn0
      _ = Cs * (y ^ N')⁻¹ * ‖φ‖ := by rw [hCs]; ring
      _ ≤ (Cs + (|D₁| + |D₂| + |D₃|) + E) * (y ^ N')⁻¹ * ‖φ‖ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hyi.le) hn0
          have := abs_nonneg D₁
          have := abs_nonneg D₂
          have := abs_nonneg D₃
          linarith
  · have hQy : Q ≤ y := not_lt.1 hQ

    have fin : ∀ (Dc : ℝ) (w : ℂ) (S' : Finset (Cos K)), |Dc| ≤ |D₁| + |D₂| + |D₃| →
        ‖w‖ ≤ |Dc| * (y ^ N')⁻¹ * ‖φ‖ → ‖∑ q ∈ S', ct 2 ψ (qx q x)‖ ≤ E * (y ^ N')⁻¹ * ‖φ‖ →
        ‖w‖ + ‖∑ q ∈ S', ct 2 ψ (qx q x)‖ ≤ (Cs + (|D₁| + |D₂| + |D₃|) + E) * (y ^ N')⁻¹ * ‖φ‖ := by
      intro Dc w S' hDc h1 h2
      have h3 : (|Dc| + E) * (y ^ N')⁻¹ * ‖φ‖ ≤ (Cs + (|D₁| + |D₂| + |D₃|) + E) * (y ^ N')⁻¹ * ‖φ‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hyi.le) hn0
      have h4 : (|Dc| + E) * (y ^ N')⁻¹ * ‖φ‖ = |Dc| * (y ^ N')⁻¹ * ‖φ‖ + E * (y ^ N')⁻¹ * ‖φ‖ := by ring
      linarith
    have scale : ∀ Dc v : ℝ, 0 ≤ v → v ≤ (y ^ N')⁻¹ → Dc * v * ‖φ‖ ≤ |Dc| * (y ^ N')⁻¹ * ‖φ‖ := by
      intro Dc v hv0 hv
      refine mul_le_mul_of_nonneg_right ?_ hn0
      exact (mul_le_mul_of_nonneg_right (le_abs_self _) hv0).trans
        (mul_le_mul_of_nonneg_left hv (abs_nonneg _))
    have hd1 : |D₁| ≤ |D₁| + |D₂| + |D₃| := by
      have := abs_nonneg D₂
      have := abs_nonneg D₃
      linarith
    have hd2 : |D₂| ≤ |D₁| + |D₂| + |D₃| := by
      have := abs_nonneg D₁
      have := abs_nonneg D₃
      linarith
    have hd3 : |D₃| ≤ |D₁| + |D₂| + |D₃| := by
      have := abs_nonneg D₁
      have := abs_nonneg D₂
      linarith
    rcases hgeo T x hT hQy hOm with ⟨q₀, δ, hδ, ρ, hSg, hFull, hTq, hratio, hRat, hoth⟩ | ⟨γ, hγ, ρ, R, hSg, hFull, hR1, hRat, hyR, hcase, hoth⟩
    ·
      obtain ⟨hρ, -⟩ := id hSg
      have hq₀ : q₀ ∈ S := (hS q₀).2 hTq
      rw [← Finset.add_sum_erase S _ hq₀]
      have hδG : δ ∈ Gam K (2 + 2) := by
        obtain ⟨p, -, rfl⟩ := hδ
        exact p.2
      have e1 : ψ x = ψ (δ * qx q₀ x) := by
        rw [hGam δ hδG, hGam _ q₀.out.2]
      have e2 : ct 2 ψ (qx q₀ x) = ct 2 ψ (δ * qx q₀ x) := (hPK δ hδ _).symm
      have hb : ‖ψ (δ * qx q₀ x) - ct 2 ψ (δ * qx q₀ x)‖ ≤
          D₂ * (ρ 2 / ρ 1) ^ k₂ * (y ^ M) ^ N₂ * ‖φ‖ :=
        hD₂ φ ρ _ (y ^ M) hSg hFull (one_le_pow₀ hy1) hRat
      have hu0 : 0 ≤ ρ 2 / ρ 1 := (div_pos (hρ 2) (hρ 1)).le
      have hu : ρ 2 / ρ 1 ≤ (y ^ c)⁻¹ := by
        rw [← inv_div (ρ 1) (ρ 2)]
        exact inv_anti₀ (Real.rpow_pos_of_pos hy0 _) hratio
      have hv := hk₂ y _ hy1 hu0 hu
      rw [pow_mul y M N₂] at hv
      have hb' : ‖ψ (δ * qx q₀ x) - ct 2 ψ (δ * qx q₀ x)‖ ≤ |D₂| * (y ^ N')⁻¹ * ‖φ‖ := by
        refine hb.trans ?_
        rw [mul_assoc D₂]
        exact scale _ _ (mul_nonneg (pow_nonneg hu0 _) (pow_pos (pow_pos hy0 _) _).le) hv
      have hd : ‖ψ x - (ct 2 ψ (qx q₀ x) + ∑ q ∈ S.erase q₀, ct 2 ψ (qx q x))‖ ≤
          ‖ψ (δ * qx q₀ x) - ct 2 ψ (δ * qx q₀ x)‖ + ‖∑ q ∈ S.erase q₀, ct 2 ψ (qx q x)‖ := by
        rw [e2, ← sub_sub, ← e1]
        exact norm_sub_le _ _
      exact hd.trans (fin D₂ _ _ hd2 hb' (hfar φ hφ x _ fun q hq =>
        ⟨hHH q (Finset.mem_of_mem_erase hq),
          hoth q (Finset.ne_of_mem_erase hq) ((hS q).1 (Finset.mem_of_mem_erase hq))⟩))
    ·
      obtain ⟨hρ, -⟩ := id hSg
      have e1 : ψ x = ψ (γ * x) := (hGam γ hγ x).symm
      have htail := hfar φ hφ x S fun q hq => ⟨hHH q hq, hoth q ((hS q).1 hq)⟩
      rw [e1]
      rcases hcase with hc1 | hc3
      · have hb : ‖ψ (γ * x) - ct 1 ψ (γ * x)‖ ≤ D₁ * (ρ 1 / ρ 0) ^ k₁ * R ^ N₁ * ‖φ‖ :=
          hD₁ φ ρ _ R hSg hFull hR1 hRat
        rw [(hvan φ hφ _).1, sub_zero] at hb
        have hu0 : 0 ≤ ρ 1 / ρ 0 := (div_pos (hρ 1) (hρ 0)).le
        have hu : ρ 1 / ρ 0 ≤ (R ^ c)⁻¹ := by
          rw [← inv_div (ρ 0) (ρ 1)]
          exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith) _) hc1
        have hv := hk₁ y R _ hy1 hR1 hyR hu0 hu
        have hb' : ‖ψ (γ * x)‖ ≤ |D₁| * (y ^ N')⁻¹ * ‖φ‖ := by
          refine hb.trans ?_
          rw [mul_assoc D₁]
          exact scale _ _ (mul_nonneg (pow_nonneg hu0 _) (pow_nonneg (by linarith) _)) hv
        exact (norm_sub_le _ _).trans (fin D₁ _ _ hd1 hb' htail)
      · have hb : ‖ψ (γ * x) - ct 3 ψ (γ * x)‖ ≤ D₃ * (ρ 3 / ρ 2) ^ k₃ * R ^ N₃ * ‖φ‖ :=
          hD₃ φ ρ _ R hSg hFull hR1 hRat
        rw [(hvan φ hφ _).2, sub_zero] at hb
        have hu0 : 0 ≤ ρ 3 / ρ 2 := (div_pos (hρ 3) (hρ 2)).le
        have hu : ρ 3 / ρ 2 ≤ (R ^ c)⁻¹ := by
          rw [← inv_div (ρ 2) (ρ 3)]
          exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith) _) hc3
        have hv := hk₃ y R _ hy1 hR1 hyR hu0 hu
        have hb' : ‖ψ (γ * x)‖ ≤ |D₃| * (y ^ N')⁻¹ * ‖φ‖ := by
          refine hb.trans ?_
          rw [mul_assoc D₃]
          exact scale _ _ (mul_nonneg (pow_nonneg hu0 _) (pow_nonneg (by linarith) _)) hv
        exact (norm_sub_le _ _).trans (fin D₃ _ _ hd3 hb' htail)
end
