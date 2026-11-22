module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgHonC

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

variable {lam₁ lam₂ : PowerSeries K} {Φ₁ Φ₂ : MvPowerSeries (Fin 2) K} {A₁ A₂ g : PowerSeries K}

theorem homE_coeff_one_subst {R : Type} [CommRing R] (f a : PowerSeries R) (ha : constantCoeff a = 0) :
    coeff 1 (f.subst a) = coeff 1 f * coeff 1 a := by
  have hs : HasSubst a := HasSubst.of_constantCoeff_zero ha
  have hX : X ∣ a := X_dvd_iff.mpr ha
  rw [PowerSeries.coeff_subst' hs, finsum_eq_single _ 1]
  · simp [smul_eq_mul]
  · intro d hd
    rcases Nat.lt_or_gt_of_ne hd with h | h
    · have : d = 0 := by omega
      subst this
      simp
    · have h2 : X ^ d ∣ a ^ d := pow_dvd_pow_of_dvd hX d
      have h3 := X_pow_dvd_iff.mp h2 1 h
      simp [h3]

private theorem mvPowerSeries_coeff_subst_X_eq_ite_single {S : Type} [CommRing S] {ι : Type} [DecidableEq ι] (i : ι) (f : PowerSeries S)
    (e : ι →₀ ℕ) :
    MvPowerSeries.coeff e (f.subst (MvPowerSeries.X i : MvPowerSeries ι S)) =
      if e = Finsupp.single i (e i) then coeff (e i) f else 0 := by
  have ha : HasSubst (MvPowerSeries.X i : MvPowerSeries ι S) :=
    HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  rw [PowerSeries.coeff_subst ha]
  simp only [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  split_ifs with h
  · rw [finsum_eq_single _ (e i)]
    · rw [if_pos h]
    · intro d hd
      rw [if_neg]
      intro he
      exact hd (by rw [he, Finsupp.single_eq_same])
  · rw [finsum_eq_zero_of_forall_eq_zero]
    intro d
    rw [if_neg]
    intro he
    exact h (by rw [he, Finsupp.single_eq_same])

theorem homE_norm_coeff_atX_mul_atY {x : K} (a b : PowerSeries K) (ha : IntegralPS a)
    (hb : ‖coeff 1 b‖ ≤ ‖x‖) (n : ℕ) :
    ‖MvPowerSeries.coeff (Finsupp.single 0 n + Finsupp.single 1 1) (atX a * atY b)‖ ≤ ‖x‖ := by
  unfold IntegralPS at ha
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_induction _ (fun y => ‖y‖ ≤ ‖x‖)
    (fun u v hu hv => (IsUltrametricDist.norm_add_le_max u v).trans (max_le hu hv))
    (by simp) fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  unfold atX atY
  rw [mvPowerSeries_coeff_subst_X_eq_ite_single, mvPowerSeries_coeff_subst_X_eq_ite_single]
  split_ifs with h1 h2
  · have e1 := congrArg (fun f => f 1) hp
    simp only [Finsupp.add_apply] at e1
    rw [h1] at e1
    simp at e1
    rw [norm_mul, e1]
    calc ‖coeff (p.1 0) a‖ * ‖coeff 1 b‖ ≤ 1 * ‖x‖ :=
          mul_le_mul (ha _) hb (norm_nonneg _) zero_le_one
      _ = ‖x‖ := one_mul _
  all_goals simp

theorem homE_norm_coeff_one_pow {x : K} (hg0 : constantCoeff g = 0) (h0 : ‖coeff 1 g‖ ≤ ‖x‖) (j : ℕ) :
    ‖coeff 1 (g ^ j)‖ ≤ ‖x‖ := by
  rcases j with _ | _ | j
  · simp
  · simpa using h0
  · have hX : X ∣ g := X_dvd_iff.mpr hg0
    have h2 := pow_dvd_pow_of_dvd hX (j + 1 + 1)
    rw [X_pow_dvd_iff.mp h2 1 (by omega), norm_zero]
    exact norm_nonneg _

theorem divBy_partialYAtZero_subst_atX_atY {x : K} (hΦ₂ : IntegralMv Φ₂) (hg0 : constantCoeff g = 0)
    (hg : IntegralPS g) (h0 : ‖coeff 1 g‖ ≤ ‖x‖) :
    DivBy x (d2 (Φ₂.subst ![atX g, atY g])) := by
  intro n
  have hX : PowerSeries.HasSubst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) :=
    PowerSeries.HasSubst.X 0
  have hY : PowerSeries.HasSubst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) :=
    PowerSeries.HasSubst.X 1
  have hP' : MvPowerSeries.HasSubst ![atX g, atY g] := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => ?_
    fin_cases i
    · exact PowerSeries.constantCoeff_subst_eq_zero (by simp) g hg0
    · exact PowerSeries.constantCoeff_subst_eq_zero (by simp) g hg0
  rw [d2, coeff_mk, MvPowerSeries.coeff_subst hP']
  refine Formalism.LT.LTL.norm_finsum_le' (norm_nonneg _) fun m => ?_
  rw [smul_eq_mul, norm_mul, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [atX, atY, ← PowerSeries.subst_pow hX, ← PowerSeries.subst_pow hY]
  have := homE_norm_coeff_atX_mul_atY (g ^ m 0) (g ^ m 1) (integralPS_pow hg _)
    (homE_norm_coeff_one_pow hg0 h0 _) n
  exact (mul_le_mul (hΦ₂ m) this (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem hom_eigen (hA₁ : constantCoeff A₁ = 0) (hA₂ : constantCoeff A₂ = 0)
    (hg : HomCls l Φ₁ A₁ Φ₂ A₂ g) (h : ‖coeff 1 A₁ - coeff 1 A₂‖ = 1) :
    ‖coeff 1 g‖ ≤ ‖(l : K)‖ := by
  have h0 := hg.eig
  unfold DivBy at h0
  have h1 := h0 1
  have e : coeff 1 g * coeff 1 A₁ - coeff 1 A₂ * coeff 1 g =
      coeff 1 g * (coeff 1 A₁ - coeff 1 A₂) := by ring
  rw [map_sub, homE_coeff_one_subst _ _ hA₁, homE_coeff_one_subst _ _ hg.g0, e, norm_mul, h,
    mul_one] at h1
  exact h1

theorem homE_expand_subst_map_congr {ι : Type} (hF : FrobField K l σ) {g₁ : PowerSeries K}
    (hg₁ : IntegralPS g₁) (hc : DivBy (l : K) (g - g₁.subst ((X : PowerSeries K) ^ l)))
    (P : MvPowerSeries ι K) (hP0 : MvPowerSeries.constantCoeff P = 0) (hP : IntegralMv P) :
    DivByMv (l : K) (MvPowerSeries.expand l hF.prime.ne_zero (g₁.subst (MvPowerSeries.map σ P))
      - g.subst P) := by
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  have hσ0 : MvPowerSeries.constantCoeff (MvPowerSeries.map σ P) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, hP0, map_zero]
  have hs : PowerSeries.HasSubst (MvPowerSeries.map σ P) :=
    PowerSeries.HasSubst.of_constantCoeff_zero hσ0
  have hPs : PowerSeries.HasSubst P := PowerSeries.HasSubst.of_constantCoeff_zero hP0
  rw [PowerSeries.expand_subst l hl0 hs g₁]
  have hfr := Formalism.LT.FrobCongr_valid K l l hl0 σ hF.funEqSetting ι P hP
  have T1 : DivByMv (l : K) (g₁.subst (MvPowerSeries.expand l hl0 (MvPowerSeries.map σ P))
      - g₁.subst (P ^ l)) := by
    refine divByMv_subst_congr hF.norm_l.le hg₁ ?_ ?_ ?_ (integralMv_pow hP l) ?_
    · rw [MvPowerSeries.constantCoeff_expand, hσ0]
    · rw [map_pow, hP0, zero_pow hl0]
    · exact (integralMv_iff_divBy_one _).2 ((divByMv_expand_iff 1 l hl0 _).2
        ((integralMv_iff_divBy_one _).1 (hF.integralMv_map hP)))
    · rw [← neg_sub]; exact divByMv_neg hfr
  have T2 : g₁.subst (P ^ l) = PowerSeries.subst P (g₁.subst ((X : PowerSeries K) ^ l) : PowerSeries K) := by
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X_pow hl0) hPs,
      PowerSeries.subst_pow hPs, PowerSeries.subst_X hPs]
  have T3 : DivByMv (l : K) (PowerSeries.subst P (g₁.subst ((X : PowerSeries K) ^ l) : PowerSeries K) - g.subst P) := by
    rw [← PowerSeries.subst_sub hPs]
    refine divByMv_subst ?_ hP0 hP
    rw [← neg_sub]; exact divBy_neg hc
  rw [T2] at T1
  have := divByMv_add T1 T3
  rwa [sub_add_sub_cancel] at this

theorem homE_vec_const {f : PowerSeries K} (hf0 : constantCoeff f = 0) (i : Fin 2) :
    MvPowerSeries.constantCoeff (![atX f, atY f] i) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  fin_cases i <;> simp [atX, atY, mvPowerSeries_coeff_subst_X_eq_ite_single, hf0]

theorem homE_vec_integral {f : PowerSeries K} (hf : IntegralPS f) (i : Fin 2) :
    IntegralMv (![atX f, atY f] i) := by
  unfold IntegralPS at hf
  unfold IntegralMv
  intro e
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, atX, atY, mvPowerSeries_coeff_subst_X_eq_ite_single]
  all_goals split_ifs
  all_goals first | exact hf _ | simp

theorem homE_vec_divBy {x : K} {f h : PowerSeries K} (hfh : DivBy x (f - h)) (i : Fin 2) :
    DivByMv x (![atX f, atY f] i - ![atX h, atY h] i) := by
  unfold DivBy at hfh
  unfold DivByMv
  intro e
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, atX, atY, map_sub, mvPowerSeries_coeff_subst_X_eq_ite_single]
  all_goals split_ifs
  all_goals first | (rw [← map_sub]; exact hfh _) | simp

theorem homE_expand_subst_X (hl0 : l ≠ 0) (f : PowerSeries K) (i : Fin 2) :
    MvPowerSeries.expand l hl0 (f.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K)) =
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K)
        (f.subst ((X : PowerSeries K) ^ l) : PowerSeries K) := by
  rw [PowerSeries.expand_subst l hl0 (PowerSeries.HasSubst.X i), MvPowerSeries.expand_X,
    PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X_pow hl0) (PowerSeries.HasSubst.X i),
    PowerSeries.subst_pow (PowerSeries.HasSubst.X i), PowerSeries.subst_X (PowerSeries.HasSubst.X i)]

end ReciprocityTheory.ChartRestriction.L1
