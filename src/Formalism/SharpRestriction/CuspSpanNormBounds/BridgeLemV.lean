import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemVN
import Formalism.SharpRestriction.CuspSpanNormBounds.MassRatioBound
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.EulerFacMulConjInvSplit
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast

section
noncomputable section

namespace Formalism.MainNotions.BridgeLemVL

open NumberField Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.IdealNormInequalities

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def Z2 : ℝ := ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹

theorem zeta_two_eq_pi_sq_div_six : Z2 = Real.pi ^ 2 / 6 := by
  unfold Z2
  rw [← hasSum_zeta_two.tsum_eq]
  congr 1
  ext n
  rw [one_div]

theorem sum_resChar_le (s : Finset {P : Ideal (𝓞 K) // P.IsMaximal}) :
    ∑ P ∈ s, ((resChar P.1 : ℝ) ^ 2)⁻¹ ≤ (Module.finrank ℚ K : ℝ) * Z2 := by
  classical
  have hs : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := Real.summable_nat_pow_inv.mpr (by norm_num)
  have h1 : ∑ P ∈ s, ((resChar P.1 : ℝ) ^ 2)⁻¹ =
      ∑ n ∈ s.image (fun P => resChar P.1),
        ∑ P ∈ s.filter (fun P => resChar P.1 = n), ((resChar P.1 : ℝ) ^ 2)⁻¹ :=
    (Finset.sum_fiberwise_of_maps_to (fun P hP => Finset.mem_image_of_mem _ hP) _).symm
  rw [h1]
  calc ∑ n ∈ s.image (fun P => resChar P.1),
        ∑ P ∈ s.filter (fun P => resChar P.1 = n), ((resChar P.1 : ℝ) ^ 2)⁻¹
      ≤ ∑ n ∈ s.image (fun P => resChar P.1), (Module.finrank ℚ K : ℝ) * ((n : ℝ) ^ 2)⁻¹ := by
        refine Finset.sum_le_sum fun n _ => ?_
        have h2 : ∑ P ∈ s.filter (fun P => resChar P.1 = n), ((resChar P.1 : ℝ) ^ 2)⁻¹ =
            ((s.filter (fun P => resChar P.1 = n)).card : ℝ) * ((n : ℝ) ^ 2)⁻¹ := by
          rw [← nsmul_eq_mul, ← Finset.sum_const]
          refine Finset.sum_congr rfl fun P hP => ?_
          rw [(Finset.mem_filter.mp hP).2]
        rw [h2]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast card_filter_resChar_le s n
    _ = (Module.finrank ℚ K : ℝ) * ∑ n ∈ s.image (fun P => resChar P.1), ((n : ℝ) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℚ K : ℝ) * Z2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact hs.sum_le_tsum _ (fun n _ => by positivity)

theorem eulerFac_two_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    Formalism.HermitianLatticesTheory.eulerFac K 2 P ≤ Real.exp (2 * ((resChar P : ℝ) ^ 2)⁻¹) := by
  have hu := abs_smallTerm_le hK hP (le_refl 2)
  have hp : (2 : ℝ) ≤ (resChar P : ℝ) := by exact_mod_cast (resChar_prime hP).two_le
  have hq : ((resChar P : ℝ) ^ 2)⁻¹ ≤ 1 / 4 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  set u := smallTerm 2 P with hudef
  set y := ((resChar P : ℝ) ^ 2)⁻¹ with hy
  have hy0 : 0 ≤ y := by positivity
  have hua : |u| ≤ 1 / 2 := by linarith
  have hpos : 0 < 1 + u := by linarith [neg_abs_le u]
  have key : (1 + u)⁻¹ ≤ Real.exp (2 * y) := by
    have h1 : 0 < 1 - |u| := by linarith
    have h2 : (1 + u)⁻¹ ≤ (1 - |u|)⁻¹ := by
      apply inv_anti₀ h1
      linarith [neg_abs_le u]
    exact h2.trans ((Formalism.MainNotions.MassRatioZetaBound.inv_one_sub_le_exp (abs_nonneg u) hua).trans
      (Real.exp_le_exp.2 (by linarith)))
  rw [eulerFac_eq]
  split_ifs with hc
  · exact key
  · rcases le_or_gt 1 (1 + u) with h | h
    · calc (1 + u) ^ (-(1 : ℝ) / 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h (by norm_num)
        _ ≤ Real.exp (2 * y) := Real.one_le_exp (by positivity)
    · calc (1 + u) ^ (-(1 : ℝ) / 2) ≤ (1 + u) ^ (-(1 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_ge hpos h.le (by norm_num)
        _ = (1 + u)⁻¹ := Real.rpow_neg_one _
        _ ≤ Real.exp (2 * y) := key

theorem lValEta_two_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    Formalism.HermitianLatticesTheory.lValEta K 2 ≤ Real.exp (2 * ((Module.finrank ℚ K : ℝ) * Z2)) := by
  unfold Formalism.HermitianLatticesTheory.lValEta
  refine (multipliable_eulerFac hK 2 le_rfl).tprod_le_of_prod_le fun s => ?_
  calc ∏ P ∈ s, Formalism.HermitianLatticesTheory.eulerFac K 2 P.1
      ≤ ∏ P ∈ s, Real.exp (2 * ((resChar P.1 : ℝ) ^ 2)⁻¹) :=
        Finset.prod_le_prod (fun P _ => (eulerFac_pos hK P.2 2 (by norm_num)).le)
          (fun P _ => eulerFac_two_le hK P.2)
    _ = Real.exp (2 * ∑ P ∈ s, ((resChar P.1 : ℝ) ^ 2)⁻¹) := by
        rw [← Real.exp_sum, Finset.mul_sum]
    _ ≤ Real.exp (2 * ((Module.finrank ℚ K : ℝ) * Z2)) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (sum_resChar_le s) (by norm_num))

theorem mass_ratio_rank_two_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    Formalism.HermitianLatticesTheory.massRatioRightSide K 2 ≤ ((Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ 2) ^ Formalism.HermitianLatticesTheory.fDeg K *
      Real.exp (2 * ((Module.finrank ℚ K : ℝ) * Z2)) := by
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide
  have hv : 0 ≤ Formalism.HermitianLatticesTheory.vInv K := by
    have := Formalism.MainNotions.MassRatioZetaBound.one_le_two_vInv (K := K); linarith
  have e1 : (((Nat.factorial (2 - 1) : ℕ) : ℝ) * (Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ 2) =
      (Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ 2 := by norm_num
  rw [e1]
  set a : ℝ := ((Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ 2) ^ Formalism.HermitianLatticesTheory.fDeg K with ha
  have ha0 : 0 ≤ a := by positivity
  have hb1 : 1 ≤ Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) :=
    Real.one_le_sqrt.2 (one_le_pow₀ Formalism.MainNotions.MassRatioZetaBound.one_le_two_vInv)
  calc a / Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) * Formalism.HermitianLatticesTheory.lValEta K 2
      ≤ a / Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) *
          Real.exp (2 * ((Module.finrank ℚ K : ℝ) * Z2)) :=
        mul_le_mul_of_nonneg_left (lValEta_two_le hK) (div_nonneg ha0 (by linarith))
    _ ≤ a * Real.exp (2 * ((Module.finrank ℚ K : ℝ) * Z2)) :=
        mul_le_mul_of_nonneg_right (div_le_self ha0 hb1) (Real.exp_pos _).le

end Formalism.MainNotions.BridgeLemVL

end
end

section
noncomputable section

namespace Formalism.MainNotions.BridgeLemV

open NumberField Formalism.HermitianLatticesTheory Formalism.HermitianLattices.Ext.L3

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem std_form_eq (n : ℕ) : Formalism.MainNotions.StandardLattice.stdForm K n = stdForm K n := rfl

theorem std_lattice_eq (n : ℕ) : Formalism.MainNotions.StandardLattice.stdLat K n = stdLat K n := rfl

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem mass_two_eq (hK : IsCMUnram K) :
    mass (Formalism.MainNotions.StandardLattice.stdForm K 2) (Formalism.MainNotions.StandardLattice.stdLat K 2) =
      mass (Formalism.MainNotions.StandardLattice.stdForm K 1) (Formalism.MainNotions.StandardLattice.stdLat K 1) * massRatioRightSide K 2 := by
  rw [std_form_eq, std_form_eq, std_lattice_eq, std_lattice_eq]
  obtain ⟨F, _, _, _, hF⟩ := exists_fixF K hK
  obtain ⟨c₁, -, hall⟩ := massConst_all hermRepUnram liStat hK hF
  have mk : ∀ n : ℕ, 1 ≤ n →
      mass (stdForm K n) (stdLat K n) = c₁ * ∏ j ∈ Finset.Icc 2 n, massRatioRightSide K j := by
    intro n hn
    have hs := stdForm_isSymm K n
    have ho := stdLat_isOrtho K n
    have := finiteDimensional_of_ortho ho
    have e := hall n hn _ (stdForm K n) (stdLat K n) hs (isTotPosDef_of_ortho hK hs ho)
      (finrank_of_ortho ho) (isLattice_of_ortho ho) (isIntegralLat_of_ortho ho)
    rw [lamG_eq_one_of_ortho hK hF hs ho, mul_one] at e
    exact e
  rw [mk 2 (by norm_num), mk 1 le_rfl, Finset.Icc_self, Finset.prod_singleton,
    Finset.Icc_eq_empty (by norm_num), Finset.prod_empty, mul_one]

theorem classNumber_le (hK : IsCMUnram K) :
    (classNumber K : ℝ) ≤ (2 * vInv K) ^ fDeg K * (1 + (fDeg K : ℝ) * Real.log (2 * vInv K)) ^ (2 * fDeg K) := by
  have hc := Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.classNumberBound K (fun w => hK.1.isComplex w)
  have hsq : Real.sqrt |(discr K : ℝ)| = (2 * vInv K) ^ fDeg K := by
    obtain ⟨h1, -, h3⟩ := discrTower K (cmF K) hK (Formalism.MainNotions.BridgeLemVN.fixF K)
    rw [h1, Real.sqrt_sq_eq_abs, h3, abs_of_nonneg (pow_nonneg (by linarith [vInv_pos K]) _)]
  rw [hsq, finrank_eq_two_fDeg hK, Real.log_pow] at hc
  exact hc

def boundTwo (E : Type) [Field E] [NumberField E] : ℝ :=
  2 ^ fDeg E * (2 * vInv E) ^ fDeg E * (1 + (fDeg E : ℝ) * Real.log (2 * vInv E)) ^ (2 * fDeg E) *
    ((vInv E / Real.pi) ^ 2) ^ fDeg E * Real.exp (2 * Real.pi ^ 2 * fDeg E / 3)

def MassTwoBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], IsCMUnram E →
    mass (Formalism.MainNotions.StandardLattice.stdForm E 2) (Formalism.MainNotions.StandardLattice.stdLat E 2) ≤ boundTwo E

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem MassTwoBound_holds : MassTwoBound := by
  intro E _ _ _ hE
  rw [mass_two_eq hE]
  have h1 : mass (Formalism.MainNotions.StandardLattice.stdForm E 1) (Formalism.MainNotions.StandardLattice.stdLat E 1) ≤
      ((classNumber E * 2 ^ fDeg E : ℕ) : ℝ) := by
    rw [std_form_eq, std_lattice_eq]; exact Formalism.MainNotions.BridgeLemVN.mass_std_one_le hE
  have hc := classNumber_le hE
  have hv0 : 0 ≤ vInv E := (vInv_pos E).le
  have hA0 : 0 ≤ (2 * vInv E) ^ fDeg E * (1 + (fDeg E : ℝ) * Real.log (2 * vInv E)) ^ (2 * fDeg E) :=
    le_trans (Nat.cast_nonneg _) hc
  have hA : mass (Formalism.MainNotions.StandardLattice.stdForm E 1) (Formalism.MainNotions.StandardLattice.stdLat E 1) ≤
      (2 * vInv E) ^ fDeg E * (1 + (fDeg E : ℝ) * Real.log (2 * vInv E)) ^ (2 * fDeg E) * 2 ^ fDeg E := by
    refine h1.trans ?_
    push_cast
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hZ : Real.exp (2 * ((Module.finrank ℚ E : ℝ) * Formalism.MainNotions.BridgeLemVL.Z2)) =
      Real.exp (2 * Real.pi ^ 2 * fDeg E / 3) := by
    rw [Formalism.MainNotions.BridgeLemVL.zeta_two_eq_pi_sq_div_six, finrank_eq_two_fDeg hE]
    congr 1
    push_cast
    ring
  have hB := (Formalism.MainNotions.BridgeLemVL.mass_ratio_rank_two_le hE).trans (le_of_eq (by rw [hZ]))
  calc mass (Formalism.MainNotions.StandardLattice.stdForm E 1) (Formalism.MainNotions.StandardLattice.stdLat E 1) * massRatioRightSide E 2
      ≤ ((2 * vInv E) ^ fDeg E * (1 + (fDeg E : ℝ) * Real.log (2 * vInv E)) ^ (2 * fDeg E) * 2 ^ fDeg E) *
          (((vInv E / Real.pi) ^ 2) ^ fDeg E * Real.exp (2 * Real.pi ^ 2 * fDeg E / 3)) :=
        mul_le_mul hA hB (massRatio_pos hE 2 le_rfl).le (by positivity)
    _ = boundTwo E := by unfold boundTwo; ring

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem mass_two_le_pow (hK : IsCMUnram K) {Y : ℝ} (hY : 2 ≤ Y) (hv : 2 * vInv K ≤ Y)
    (hf : (fDeg K : ℝ) ≤ Y) :
    mass (Formalism.MainNotions.StandardLattice.stdForm K 2) (Formalism.MainNotions.StandardLattice.stdLat K 2) ≤ Y ^ (22 * fDeg K) := by
  refine (MassTwoBound_holds K hK).trans ?_
  unfold boundTwo
  have hv0 : 0 ≤ vInv K := (vInv_pos K).le
  have hr1 : 1 ≤ 2 * vInv K := Formalism.MainNotions.MassRatioZetaBound.one_le_two_vInv
  have hY0 : 0 ≤ Y := by linarith
  have hf0 : (0 : ℝ) ≤ fDeg K := Nat.cast_nonneg _
  have p1 : (2 : ℝ) ^ fDeg K ≤ Y ^ fDeg K := pow_le_pow_left₀ (by norm_num) hY _
  have p2 : (2 * vInv K) ^ fDeg K ≤ Y ^ fDeg K := pow_le_pow_left₀ (by linarith) hv _
  have hl0 : 0 ≤ Real.log (2 * vInv K) := Real.log_nonneg hr1
  have hl : Real.log (2 * vInv K) ≤ 2 * vInv K :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hL : 1 + (fDeg K : ℝ) * Real.log (2 * vInv K) ≤ Y ^ 3 := by
    have h1 : (fDeg K : ℝ) * Real.log (2 * vInv K) ≤ Y * Y := mul_le_mul hf (hl.trans hv) hl0 hY0
    nlinarith
  have hL0 : 0 ≤ 1 + (fDeg K : ℝ) * Real.log (2 * vInv K) := by positivity
  have p3 : (1 + (fDeg K : ℝ) * Real.log (2 * vInv K)) ^ (2 * fDeg K) ≤ (Y ^ 3) ^ (2 * fDeg K) :=
    pow_le_pow_left₀ hL0 hL _
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hq0 : 0 ≤ vInv K / Real.pi := div_nonneg hv0 (by linarith)
  have hq : vInv K / Real.pi ≤ Y := (div_le_self hv0 hpi).trans (by linarith)
  have p4 : ((vInv K / Real.pi) ^ 2) ^ fDeg K ≤ (Y ^ 2) ^ fDeg K :=
    pow_le_pow_left₀ (pow_nonneg hq0 2) (pow_le_pow_left₀ hq0 hq 2) _
  have he8 : Real.exp 8 ≤ 2 ^ 12 := by
    have e : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    calc Real.exp 1 ^ 8 ≤ (2.7182818286 : ℝ) ^ 8 :=
          pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 8
      _ ≤ 2 ^ 12 := by norm_num
  have p5 : Real.exp (2 * Real.pi ^ 2 * fDeg K / 3) ≤ (Y ^ 12) ^ fDeg K := by
    have hpi2 : Real.pi ^ 2 ≤ 12 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    calc Real.exp (2 * Real.pi ^ 2 * fDeg K / 3) ≤ Real.exp ((fDeg K : ℕ) * 8) :=
          Real.exp_le_exp.2 (by nlinarith)
      _ = Real.exp 8 ^ fDeg K := Real.exp_nat_mul 8 _
      _ ≤ (2 ^ 12) ^ fDeg K := pow_le_pow_left₀ (Real.exp_pos 8).le he8 _
      _ ≤ (Y ^ 12) ^ fDeg K := pow_le_pow_left₀ (by norm_num) (pow_le_pow_left₀ (by norm_num) hY 12) _
  have q1 := mul_le_mul p1 p2 (pow_nonneg (by linarith) _) (pow_nonneg hY0 _)
  have q2 := mul_le_mul q1 p3 (pow_nonneg hL0 _) (mul_nonneg (pow_nonneg hY0 _) (pow_nonneg hY0 _))
  have q3 := mul_le_mul q2 p4 (pow_nonneg (pow_nonneg hq0 2) _)
    (mul_nonneg (mul_nonneg (pow_nonneg hY0 _) (pow_nonneg hY0 _)) (pow_nonneg (pow_nonneg hY0 3) _))
  have q4 := mul_le_mul q3 p5 (Real.exp_pos _).le
    (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hY0 _) (pow_nonneg hY0 _))
      (pow_nonneg (pow_nonneg hY0 3) _)) (pow_nonneg (pow_nonneg hY0 2) _))
  refine q4.trans (le_of_eq ?_)
  rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
  congr 1
  ring

end Formalism.MainNotions.BridgeLemV

end
end
