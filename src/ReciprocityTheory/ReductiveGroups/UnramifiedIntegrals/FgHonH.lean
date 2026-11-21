import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgHonC
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgDefs

section
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

theorem hom_deriv (hl1 : ‖(l : K)‖ ≤ 1) (h₁ : LawD lam₁ Φ₁) (h₂ : LawD lam₂ Φ₂)
    (hg : HomCls l Φ₁ A₁ Φ₂ A₂ g) (h0 : ‖coeff 1 g‖ ≤ ‖(l : K)‖) :
    DivBy (l : K) (derivative K g) := by
  have h1 := divBy_partialYAtZero hg.add
  rw [partialYAtZero_sub, h₁.coeffY_subst] at h1
  have h2 := divBy_partialYAtZero_subst_atX_atY (x := (l : K)) h₂.Φint hg.g0 hg.gInt h0
  have h3 : DivBy (l : K) (derivative K g * d2 Φ₁) := by
    unfold DivBy at h1 h2 ⊢
    intro n
    have h4 := IsUltrametricDist.norm_add_le_max
      (coeff n (derivative K g * d2 Φ₁ - d2 (Φ₂.subst ![atX g, atY g])))
      (coeff n (d2 (Φ₂.subst ![atX g, atY g])))
    rw [← map_add, sub_add_cancel] at h4
    exact h4.trans (max_le (h1 n) (h2 n))
  have e : derivative K g = derivative K lam₁ * (derivative K g * d2 Φ₁) := by
    linear_combination (-derivative K g) * h₁.deriv_mul
  rw [e]
  have hl := h₁.deriv_integral
  unfold DivBy at h3 ⊢
  unfold IntegralPS at hl
  intro n
  rw [coeff_mul]
  refine Finset.sum_induction _ (fun y => ‖y‖ ≤ ‖(l : K)‖)
    (fun a b ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb))
    (by simp) fun p _ => ?_
  rw [norm_mul]
  calc _ ≤ 1 * ‖(l : K)‖ := mul_le_mul (hl _) (h3 _) (norm_nonneg _) zero_le_one
    _ = ‖(l : K)‖ := one_mul _

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

theorem hom_desc (hF : FrobField K l σ) (hΦ₁0 : MvPowerSeries.constantCoeff Φ₁ = 0)
    (hΦ₁ : IntegralMv Φ₁) (hΦ₂0 : MvPowerSeries.constantCoeff Φ₂ = 0) (hΦ₂ : IntegralMv Φ₂)
    (hA₁0 : constantCoeff A₁ = 0) (hA₁ : IntegralPS A₁) (hA₂0 : constantCoeff A₂ = 0)
    (hA₂ : IntegralPS A₂) (hg : HomCls l Φ₁ A₁ Φ₂ A₂ g) (hg' : DivBy (l : K) (derivative K g)) :
    DivBy (l : K) (g - (desc l g).subst ((X : PowerSeries K) ^ l)) ∧
      HomCls l (MvPowerSeries.map σ Φ₁) (PowerSeries.map σ A₁) Φ₂ A₂ (desc l g) := by
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  have hc := (desc_congr hF.prime hF.norm_l g hg').1
  refine ⟨hc, ?_⟩
  have hg₁0 : constantCoeff (desc l g) = 0 := by rw [desc_const, hg.g0]
  have hg₁ : IntegralPS (desc l g) := desc_integral hg.gInt
  generalize desc l g = g₁ at hc hg₁0 hg₁ ⊢
  obtain ⟨E, hE⟩ : ∃ E : PowerSeries K, E = g₁.subst ((X : PowerSeries K) ^ l) := ⟨_, rfl⟩
  have hE0 : constantCoeff E = 0 := by
    rw [hE]; exact PowerSeries.constantCoeff_subst_eq_zero
      (by rw [map_pow]; exact (congrArg (· ^ l) (constantCoeff_X (R := K))).trans (zero_pow hl0)) g₁ hg₁0
  have hEint : IntegralPS E := by
    rw [hE]
    exact (integralPS_iff_divBy_one _).2 ((divBy_expand_iff 1 l hl0 g₁).2
      ((integralPS_iff_divBy_one _).1 hg₁))
  have hc' : DivBy (l : K) (g - E) := by rw [hE]; exact hc
  refine ⟨hg₁0, hg₁, ?_, ?_⟩
  · rw [← divByMv_expand_iff (l : K) l hl0, map_sub]
    have T := homE_expand_subst_map_congr hF hg₁ hc Φ₁ hΦ₁0 hΦ₁
    have hv : MvPowerSeries.HasSubst ![atX g₁, atY g₁] :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (homE_vec_const hg₁0)
    have hex : MvPowerSeries.expand l hl0 (Φ₂.subst ![atX g₁, atY g₁]) =
        Φ₂.subst ![atX E, atY E] := by
      rw [MvPowerSeries.expand_subst l hl0 hv]
      congr 1
      funext i
      fin_cases i
      · show MvPowerSeries.expand l hl0 (atX g₁) = atX E
        rw [atX, atX, homE_expand_subst_X hl0, hE]
      · show MvPowerSeries.expand l hl0 (atY g₁) = atY E
        rw [atY, atY, homE_expand_subst_X hl0, hE]
    have T5 : DivByMv (l : K) (Φ₂.subst ![atX g, atY g] - Φ₂.subst ![atX E, atY E]) :=
      divByMv_subst2_congr hF.norm_l.le hΦ₂ (homE_vec_const hg.g0) (homE_vec_const hE0)
        (homE_vec_integral hg.gInt) (homE_vec_integral hEint) (homE_vec_divBy hc')
    rw [hex]
    have := divByMv_add (divByMv_add T hg.add) T5
    rwa [sub_add_sub_cancel, sub_add_sub_cancel] at this
  · rw [divBy_iff_mv, ← divByMv_expand_iff (l : K) l hl0, map_sub]
    have T := homE_expand_subst_map_congr (ι := Unit) hF hg₁ hc A₁ hA₁0 ((integralPS_iff_mv _).1 hA₁)
    have hex : MvPowerSeries.expand l hl0 (A₂.subst g₁) = A₂.subst E := by
      rw [PowerSeries.expand_subst l hl0 (PowerSeries.HasSubst.of_constantCoeff_zero' hg₁0), hE]
      congr 1
      exact PowerSeries.expand_apply l hl0 g₁
    have T5 : DivByMv (l : K) (A₂.subst g - A₂.subst E) :=
      divByMv_subst_congr (ι := Unit) hF.norm_l.le hA₂ hg.g0 hE0 ((integralPS_iff_mv _).1 hg.gInt)
        ((integralPS_iff_mv _).1 hEint) ((divBy_iff_mv _ _).1 hc')
    rw [hex]
    have := divByMv_add (divByMv_add T ((divBy_iff_mv _ _).1 hg.eig)) T5
    rwa [sub_add_sub_cancel, sub_add_sub_cancel] at this

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

section Tools

variable {R : Type} [CommRing R]


theorem coeffOne_subst_zero {f s : PowerSeries R} (hs : constantCoeff s = 0) :
    coeff 1 (f.subst s) = coeff 1 f * coeff 1 s := by
  have ha : HasSubst s := HasSubst.of_constantCoeff_zero hs
  have hX : X ∣ s := X_dvd_iff.mpr hs
  rw [PowerSeries.coeff_subst' ha, finsum_eq_single _ 1]
  · simp [smul_eq_mul]
  · intro d hd
    rcases Nat.lt_or_gt_of_ne hd with h | h
    · have : d = 0 := by omega
      subst this
      simp
    · have h2 : X ^ d ∣ s ^ d := pow_dvd_pow_of_dvd hX d
      have h3 := X_pow_dvd_iff.mp h2 1 h
      simp [h3]

theorem subst_C_mul_mv {ι : Type} {P : MvPowerSeries ι R} (hP : HasSubst P) (c : R)
    (f : PowerSeries R) : (C c * f).subst P = MvPowerSeries.C c * f.subst P := by
  rw [← smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul, ← coe_substAlgHom hP, map_smul]

theorem subst_C_mul_ps {P : PowerSeries R} (hP : HasSubst P) (c : R)
    (f : PowerSeries R) : (C c * f).subst P = C c * f.subst P := by
  rw [← smul_eq_C_mul, ← smul_eq_C_mul, ← coe_substAlgHom hP, map_smul]

end Tools

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}

theorem LawD.map (hF : FrobField K l σ) (h : LawD lam Φ) :
    LawD (PowerSeries.map σ lam) (MvPowerSeries.map σ Φ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h.lam0,
      map_zero]
  · rw [coeff_map, h.lam1, map_one]
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.Φ0, map_zero]
  · have h1 := h.Φint
    unfold IntegralMv at h1 ⊢
    intro e
    rw [MvPowerSeries.coeff_map, hF.isom]
    exact h1 e
  · have h1 := congrArg (MvPowerSeries.map σ) h.log
    unfold atX atY at h1 ⊢
    rw [map_add] at h1
    erw [PowerSeries.map_subst (HasSubst.of_constantCoeff_zero h.Φ0),
      PowerSeries.map_subst (HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 0)),
      PowerSeries.map_subst (HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1)),
      MvPowerSeries.map_X, MvPowerSeries.map_X] at h1
    exact h1

theorem HD.map (hF : FrobField K l σ) (h : HD σ lam Φ A a) :
    HD σ (PowerSeries.map σ lam) (MvPowerSeries.map σ Φ) (PowerSeries.map σ A) (σ a) := by
  refine ⟨h.toLawD.map hF, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h.A0,
      map_zero]
  · have h1 := h.Aint
    unfold IntegralPS at h1 ⊢
    intro n
    rw [coeff_map, hF.isom]
    exact h1 n
  · have h1 := congrArg (PowerSeries.map σ) h.Alog
    erw [PowerSeries.map_subst (HasSubst.of_constantCoeff_zero h.A0)] at h1
    rw [map_mul, map_C] at h1
    exact h1
  · rw [h.a_sq, norm_sub_rev]
    exact h.a_ne
  · rw [h.a_sq]

theorem HD.coeff_one_A (h : HD σ lam Φ A a) : coeff 1 A = a := by
  have h1 := congrArg (coeff 1) h.Alog
  rw [coeffOne_subst_zero h.A0, coeff_C_mul, h.lam1, one_mul, mul_one] at h1
  exact h1

theorem HD.norm_a (h : HD σ lam Φ A a) : ‖a‖ ≤ 1 := by
  have h1 := h.Aint
  unfold IntegralPS at h1
  rw [← h.coeff_one_A]
  exact h1 1


theorem eigen_trick {A : PowerSeries K} {b : K} (hA0 : constantCoeff A = 0) (D : PowerSeries K)
    (hD0 : constantCoeff D = 0) (h : DivBy (l : K) (D.subst A - C b * D))
    (hb : ‖coeff 1 A - b‖ = 1) : ‖coeff 1 D‖ ≤ ‖(l : K)‖ := by
  have h0 := h
  unfold DivBy at h0
  have h1 := h0 1
  have e : coeff 1 D * coeff 1 A - b * coeff 1 D = coeff 1 D * (coeff 1 A - b) := by ring
  rw [map_sub, coeffOne_subst_zero hA0, coeff_C_mul, e, norm_mul, hb, mul_one] at h1
  exact h1


theorem divBy_C_mul' {x c : K} (hc : ‖c‖ ≤ ‖x‖) {f : PowerSeries K} (hf : IntegralPS f) :
    DivBy x (C c * f) := by
  unfold DivBy IntegralPS at *
  intro n
  rw [coeff_C_mul, norm_mul]
  calc ‖c‖ * ‖coeff n f‖ ≤ ‖x‖ * 1 := mul_le_mul hc (hf n) (norm_nonneg _) (norm_nonneg _)
    _ = ‖x‖ := mul_one _

theorem derivative_C_mul' (c : K) (f : PowerSeries K) :
    derivative K (C c * f) = C c * derivative K f := by
  rw [← smul_eq_C_mul, ← smul_eq_C_mul, Derivation.map_smul]

theorem QCls.norm_coeff_one {b : K} {D : PowerSeries K} (hD : QCls l Φ A b D) :
    ‖coeff 1 D‖ ≤ 1 := by
  have h0 := hD.dInt
  unfold IntegralPS at h0
  have h1 := h0 0
  rw [coeff_derivative] at h1
  simpa using h1

theorem HD.qcls_sub (h : HD σ lam Φ A a) {D : PowerSeries K} (hD : QCls l Φ A a D) :
    QCls l Φ A a (D - C (coeff 1 D) * lam) := by
  set c := coeff 1 D with hc
  have hc1 : ‖c‖ ≤ 1 := hD.norm_coeff_one
  have hΦ : HasSubst Φ := HasSubst.of_constantCoeff_zero h.Φ0
  have hA : HasSubst A := HasSubst.of_constantCoeff_zero h.A0
  have hX0 : HasSubst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) :=
    HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 0)
  have hX1 : HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) :=
    HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1)
  have sub_subst : ∀ {P : MvPowerSeries (Fin 2) K} (_ : HasSubst P) (f g : PowerSeries K),
      (f - g).subst P = f.subst P - g.subst P := fun hP f g => by
    rw [← coe_substAlgHom hP, map_sub]
  have sub_substA : (D - C c * lam).subst A = D.subst A - C c * lam.subst A := by
    rw [← coe_substAlgHom hA, map_sub, coe_substAlgHom hA, subst_C_mul_ps hA]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hD.D0, h.lam0]
  · have hd := hD.dInt
    have hl := h.toLawD.deriv_integral
    unfold IntegralPS at hd hl ⊢
    intro n
    rw [map_sub, derivative_C_mul', map_sub, coeff_C_mul, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hd n) ?_)
    rw [norm_neg, norm_mul]
    calc ‖c‖ * ‖coeff n (derivative K lam)‖ ≤ 1 * 1 :=
          mul_le_mul hc1 (hl n) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · have e : (D - C c * lam).subst Φ - atX (D - C c * lam) - atY (D - C c * lam) =
        (D.subst Φ - atX D - atY D) - MvPowerSeries.C c * (lam.subst Φ - atX lam - atY lam) := by
      unfold atX atY
      rw [sub_subst hΦ, sub_subst hX0, sub_subst hX1, subst_C_mul_mv hΦ, subst_C_mul_mv hX0,
        subst_C_mul_mv hX1]
      ring
    have e2 : lam.subst Φ - atX lam - atY lam = 0 := by rw [h.log]; ring
    rw [e, e2, mul_zero, sub_zero]
    exact hD.add
  · have e : (D - C c * lam).subst A - C a * (D - C c * lam) = D.subst A - C a * D := by
      rw [sub_substA, h.Alog]
      ring
    rw [e]
    exact hD.eig

theorem lemmaQ (hF : FrobField K l σ) (h : HD σ lam Φ A a) {D : PowerSeries K}
    (hD : QCls l Φ A a D) :
    ∃ Dp : PowerSeries K,
      QCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) a Dp ∧
      DivBy (l : K) (D - C (coeff 1 D) * lam - Dp.subst ((X : PowerSeries K) ^ (l ^ 2))) := by
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  set E : PowerSeries K := D - C (coeff 1 D) * lam with hE
  have hEq : QCls l Φ A a E := h.qcls_sub hD
  have hE' : DivBy (l : K) (derivative K E) := by
    have := hon_deriv h.toLawD (l : K) D hD.add
    rwa [hE, map_sub, derivative_C_mul']
  have h1 : QCls l (MvPowerSeries.map σ Φ) (PowerSeries.map σ A) a (desc l E) :=
    desc_QCls hF h.Φ0 h.Φint h.A0 h.Aint h.norm_a hEq hE'
  have c1 := (desc_congr hF.prime hF.norm_l E hE').1
  have hσ := h.map hF
  have hs : ‖coeff 1 (desc l E)‖ ≤ ‖(l : K)‖ :=
    eigen_trick hσ.A0 _ h1.D0 h1.eig (by rw [hσ.coeff_one_A]; exact h.a_ne)
  have h1' : DivBy (l : K) (derivative K (desc l E)) := by
    have h2 := hon_deriv hσ.toLawD (l : K) _ h1.add
    have h3 := divBy_add h2 (divBy_C_mul' hs hσ.toLawD.deriv_integral)
    rwa [sub_add_cancel] at h3
  have h2 : QCls l (MvPowerSeries.map σ (MvPowerSeries.map σ Φ))
      (PowerSeries.map σ (PowerSeries.map σ A)) a (desc l (desc l E)) :=
    desc_QCls hF hσ.Φ0 hσ.Φint hσ.A0 hσ.Aint h.norm_a h1 h1'
  have c2 := (desc_congr hF.prime hF.norm_l _ h1').1
  refine ⟨desc l (desc l E), ?_, ?_⟩
  · have e1 : MvPowerSeries.map (σ.comp σ) Φ = MvPowerSeries.map σ (MvPowerSeries.map σ Φ) := by
      ext d; simp
    have e2 : PowerSeries.map (σ.comp σ) A = PowerSeries.map σ (PowerSeries.map σ A) := by
      ext d; simp
    rw [e1, e2]; exact h2
  · have hXl : HasSubst ((X : PowerSeries K) ^ l) :=
      HasSubst.of_constantCoeff_zero' (by simp [hl0])
    have c3 := (divBy_expand_iff (l : K) l hl0 _).2 c2
    rw [subst_sub hXl, subst_comp_subst_apply hXl hXl, subst_pow hXl, subst_X hXl, ← pow_mul,
      ← sq] at c3
    have c4 := divBy_add c1 c3
    rwa [sub_add_sub_cancel] at c4

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}

theorem LawD.subst_of_log (h : LawD lam Φ) {e : PowerSeries K} {c : K} (he0 : constantCoeff e = 0)
    (hlog : lam.subst e = C c * lam) : e.subst Φ = Φ.subst ![atX e, atY e] := by
  have hes : PowerSeries.HasSubst e := PowerSeries.HasSubst.of_constantCoeff_zero' he0
  have hΦs : PowerSeries.HasSubst Φ := PowerSeries.HasSubst.of_constantCoeff_zero h.Φ0
  have hlog' : lam.subst e = c • lam := by rw [hlog, smul_eq_C_mul]
  have hX : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
    fun i => PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have hx0 : MvPowerSeries.constantCoeff (atX e) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X _) _ he0
  have hy0 : MvPowerSeries.constantCoeff (atY e) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X _) _ he0
  have hb : MvPowerSeries.HasSubst ![atX e, atY e] := Formalism.G.LogP.hs2 hx0 hy0
  have hb0 : ∀ i, MvPowerSeries.constantCoeff (![atX e, atY e] i) = 0 := by
    intro i; fin_cases i <;> simpa
  refine Formalism.G.LogP.psubst_injective h.lam0 h.lam1
    (PowerSeries.constantCoeff_subst_eq_zero h.Φ0 _ he0)
    (MvPowerSeries.constantCoeff_subst_eq_zero hb hb0 h.Φ0) ?_
  rw [← PowerSeries.subst_comp_subst_apply hes hΦs, hlog', PowerSeries.subst_smul hΦs, h.log,
    ← Formalism.G.LogP.psubst_subst lam h.Φ0 hb, h.log, MvPowerSeries.subst_add hb,
    Formalism.G.LogP.psubst_subst lam (MvPowerSeries.constantCoeff_X _) hb,
    Formalism.G.LogP.psubst_subst lam (MvPowerSeries.constantCoeff_X _) hb,
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]
  show _ = lam.subst (e.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K))
    + lam.subst (e.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K))
  rw [← PowerSeries.subst_comp_subst_apply hes (hX 0), ← PowerSeries.subst_comp_subst_apply hes (hX 1),
    hlog', PowerSeries.subst_smul (hX 0), PowerSeries.subst_smul (hX 1), smul_add]

theorem LawD.comm_of_log (h : LawD lam Φ) {e f : PowerSeries K} {c d : K}
    (he0 : constantCoeff e = 0) (hf0 : constantCoeff f = 0)
    (hlog : lam.subst e = C c * lam) (hlogf : lam.subst f = C d * lam) :
    e.subst f = f.subst e := by
  have hes : PowerSeries.HasSubst e := PowerSeries.HasSubst.of_constantCoeff_zero' he0
  have hfs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  have hlog' : lam.subst e = c • lam := by rw [hlog, smul_eq_C_mul]
  have hlogf' : lam.subst f = d • lam := by rw [hlogf, smul_eq_C_mul]
  refine Formalism.G.LogP.psubst_injective (σ := Unit) h.lam0 h.lam1
    (PowerSeries.constantCoeff_subst_eq_zero hf0 _ he0)
    (PowerSeries.constantCoeff_subst_eq_zero he0 _ hf0) ?_
  rw [← PowerSeries.subst_comp_subst_apply hes hfs, ← PowerSeries.subst_comp_subst_apply hfs hes,
    hlog', hlogf', PowerSeries.subst_smul hfs, PowerSeries.subst_smul hes, hlog', hlogf',
    smul_smul, smul_smul, mul_comm]

theorem mulL_homCls (h : HD σ lam Φ A a) {e : PowerSeries K} (he0 : constantCoeff e = 0)
    (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam) : HomCls l Φ A Φ A e where
  g0 := he0
  gInt := he
  add := by
    rw [h.toLawD.subst_of_log he0 hlog, sub_self]
    exact divByMv_zero _
  eig := by
    rw [h.toLawD.comm_of_log he0 h.A0 hlog h.Alog, sub_self]
    intro n
    simp

theorem mulL_deriv (h : LawD lam Φ) {e : PowerSeries K} (he0 : constantCoeff e = 0)
    (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam) :
    DivBy (l : K) (derivative K e) := by
  have hes : PowerSeries.HasSubst e := PowerSeries.HasSubst.of_constantCoeff_zero' he0
  have h1 : (derivative K lam).subst e * derivative K e = C (l : K) * derivative K lam := by
    rw [← PowerSeries.derivative_subst hes, hlog]
    simp
  have hi : IntegralPS ((derivative K lam).subst e) :=
    (integralPS_iff_mv _).2 (integralMv_subst h.deriv_integral he0 ((integralPS_iff_mv _).1 he))
  have hc : constantCoeff ((derivative K lam).subst e) = 1 := by
    rw [← h.deriv_const]
    exact Formalism.G.LogP.constantCoeff_subst_of_zero (σ := Unit) (τ := Unit) (derivative K lam)
      (b := fun _ => e) (fun _ => he0)
  refine divBy_of_mul_unit hi (by rw [hc, norm_one]) ?_
  rw [h1]
  intro n
  rw [coeff_C_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (h.deriv_integral n)

theorem hon_shape (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam) :
    ∃ hh : PowerSeries K,
      HomCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) Φ A hh ∧
      DivBy (l : K) (e - hh.subst ((X : PowerSeries K) ^ (l ^ 2))) ∧
      coeff 1 hh = coeff (l ^ 2) e := by
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  have hσ := h.map hF
  obtain ⟨hc1, hH1⟩ := hom_desc hF h.Φ0 h.Φint h.Φ0 h.Φint h.A0 h.Aint h.A0 h.Aint
    (mulL_homCls h he0 he hlog) (mulL_deriv h.toLawD he0 he hlog)
  have hsmall : ‖coeff 1 (desc l e)‖ ≤ ‖(l : K)‖ := by
    refine hom_eigen hσ.A0 h.A0 hH1 ?_
    rw [hσ.coeff_one_A, h.coeff_one_A]
    exact h.a_ne
  have hd1 : DivBy (l : K) (derivative K (desc l e)) :=
    hom_deriv hF.norm_l.le hσ.toLawD h.toLawD hH1 hsmall
  obtain ⟨hc2, hH2⟩ := hom_desc hF hσ.Φ0 hσ.Φint h.Φ0 h.Φint hσ.A0 hσ.Aint h.A0 h.Aint hH1 hd1
  refine ⟨desc l (desc l e), ?_, ?_, ?_⟩
  · have e1 : MvPowerSeries.map (σ.comp σ) Φ = MvPowerSeries.map σ (MvPowerSeries.map σ Φ) := by
      ext d; simp
    have e2 : PowerSeries.map (σ.comp σ) A = PowerSeries.map σ (PowerSeries.map σ A) := by
      ext d; simp
    rw [e1, e2]
    exact hH2
  · have hXs : PowerSeries.HasSubst ((X : PowerSeries K) ^ l) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hl0])
    have h3 := (divBy_expand_iff (l : K) l hl0 _).2 hc2
    rw [PowerSeries.subst_sub hXs, PowerSeries.subst_comp_subst_apply hXs hXs,
      PowerSeries.subst_pow hXs, PowerSeries.subst_X hXs, ← pow_mul, ← sq] at h3
    have h4 := divBy_add hc1 h3
    rwa [sub_add_sub_cancel] at h4
  · rw [coeff_one_desc, desc, coeff_mk, sq]

theorem hon_level (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam)
    (hlev : ∃ i, i ≤ l ^ 2 ∧ ‖coeff i e‖ = 1) : ‖coeff (l ^ 2) e‖ = 1 := by
  obtain ⟨hh, -, hc, -⟩ := hon_shape hF h he0 he hlog
  obtain ⟨i, hi, hi1⟩ := hlev
  have hq0 : l ^ 2 ≠ 0 := pow_ne_zero _ hF.prime.ne_zero
  by_cases hdvd : l ^ 2 ∣ i
  · rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [coeff_zero_eq_constantCoeff_apply, he0, norm_zero] at hi1
      exact absurd hi1 zero_ne_one
    · rw [← le_antisymm hi (Nat.le_of_dvd hpos hdvd)]
      exact hi1
  · have h1 := hc i
    rw [map_sub, coeff_subst_X_pow hq0, if_neg hdvd, sub_zero, hi1] at h1
    exact absurd h1 (not_le.2 hF.norm_l)

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}

theorem HD.map_frobenius_sq (hF : FrobField K l σ) (h : HD σ lam Φ A a) :
    HD σ (PowerSeries.map (σ.comp σ) lam) (MvPowerSeries.map (σ.comp σ) Φ)
      (PowerSeries.map (σ.comp σ) A) a := by
  have hτa : (σ.comp σ) a = a := h.a_sq
  have e := congrArg (PowerSeries.map (σ.comp σ)) h.Alog
  rw [map_mul, PowerSeries.map_C, hτa] at e
  have e2 := congrArg (MvPowerSeries.map (σ.comp σ)) h.log
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, h.a_ne, h.a_sq⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h.lam0, map_zero]
  · rw [PowerSeries.coeff_map, h.lam1, map_one]
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.Φ0, map_zero]
  · refine (integralMv_iff_divBy_one _).mpr fun d => ?_
    rw [MvPowerSeries.coeff_map, RingHom.comp_apply, hF.isom, hF.isom]
    exact (integralMv_iff_divBy_one Φ).mp h.Φint d
  · have hX : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
      fun i => PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
    unfold atX atY at e2 ⊢
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero h.Φ0), map_add,
      PowerSeries.map_subst (hX 0), PowerSeries.map_subst (hX 1), MvPowerSeries.map_X,
      MvPowerSeries.map_X] at e2
    exact e2
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h.A0, map_zero]
  · unfold IntegralPS
    intro n
    rw [PowerSeries.coeff_map, RingHom.comp_apply, hF.isom, hF.isom]
    exact h.Aint n
  · have e' : MvPowerSeries.map (σ.comp σ) (lam.subst A) = C a * PowerSeries.map (σ.comp σ) lam := e
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' h.A0)] at e'
    exact e'

theorem HD.map_sq (hF : FrobField K l σ) (h : HD σ lam Φ A a) (i : ℕ) :
    HD σ (PowerSeries.map ((σ.comp σ) ^ i) lam) (MvPowerSeries.map ((σ.comp σ) ^ i) Φ)
      (PowerSeries.map ((σ.comp σ) ^ i) A) a := by
  induction i with
  | zero =>
    simp only [pow_zero, RingHom.one_def, MvPowerSeries.map_id, PowerSeries.map_id, RingHom.id_apply]
    exact h
  | succ i ih =>
    have h1 := HD.map_frobenius_sq hF ih
    simp only [pow_succ', RingHom.mul_def, MvPowerSeries.map_comp, PowerSeries.map_comp,
      RingHom.comp_apply]
    exact h1

theorem honF_subst_subst {ι κ : Type} (φ : PowerSeries K) {u : MvPowerSeries ι K}
    (hu : MvPowerSeries.constantCoeff u = 0) {b : ι → MvPowerSeries κ K}
    (hb : MvPowerSeries.HasSubst b) : (φ.subst u).subst b = φ.subst (u.subst b) := by
  rw [PowerSeries.subst, PowerSeries.subst]
  first
  | exact MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.HasSubst.of_constantCoeff_zero (fun _ => hu)) hb φ
  | exact MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hu)) hb φ
  | exact MvPowerSeries.subst_comp_subst_apply
      ((PowerSeries.HasSubst.of_constantCoeff_zero hu).hasSubst) hb φ
  | exact MvPowerSeries.subst_comp_subst_apply
      ⟨fun _ => by rw [hu]; exact IsNilpotent.zero, by simp⟩ hb φ

theorem honF_integral_subst {f g : PowerSeries K} (hf : IntegralPS f) (hg0 : constantCoeff g = 0)
    (hg : IntegralPS g) : IntegralPS (f.subst g) :=
  (integralPS_iff_mv _).mpr (integralMv_subst hf hg0 ((integralPS_iff_mv g).mp hg))

theorem hon_mu (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e hh : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam)
    (hh1 : HomCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) Φ A hh)
    (hh2 : DivBy (l : K) (e - hh.subst ((X : PowerSeries K) ^ (l ^ 2)))) :
    QCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) a (lam.subst hh) ∧
      DivBy (l : K) (C (l : K) * lam - PowerSeries.subst ((X : PowerSeries K) ^ (l ^ 2)) (lam.subst hh : PowerSeries K)) ∧
      coeff 1 (lam.subst hh) = coeff 1 hh := by
  have hl := hF.prime
  have hl1 := hF.norm_l
  have hlam' : IntegralPS (derivative K lam) := h.toLawD.deriv_integral
  have h' := h.map_frobenius_sq hF
  have Hh : PowerSeries.HasSubst hh := PowerSeries.HasSubst.of_constantCoeff_zero' hh1.g0
  have HΦ' : PowerSeries.HasSubst (MvPowerSeries.map (σ.comp σ) Φ) :=
    PowerSeries.HasSubst.of_constantCoeff_zero h'.Φ0
  have HA' : PowerSeries.HasSubst (PowerSeries.map (σ.comp σ) A) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' h'.A0
  have HA : PowerSeries.HasSubst A := PowerSeries.HasSubst.of_constantCoeff_zero' h.A0
  have hq : l ^ 2 ≠ 0 := pow_ne_zero _ hl.ne_zero
  have hXq0 : constantCoeff ((X : PowerSeries K) ^ (l ^ 2)) = 0 := by
    rw [map_pow, constantCoeff_X, zero_pow hq]
  have HXq : PowerSeries.HasSubst ((X : PowerSeries K) ^ (l ^ 2)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hXq0
  have hX0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have HX : ∀ i : Fin 2, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
    fun i => PowerSeries.HasSubst.of_constantCoeff_zero (hX0 i)
  have hp0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff (![atX hh, atY hh] i) = 0 := by
    intro i
    fin_cases i
    · exact PowerSeries.constantCoeff_subst_eq_zero (hX0 0) hh hh1.g0
    · exact PowerSeries.constantCoeff_subst_eq_zero (hX0 1) hh hh1.g0
  have hpI : ∀ i : Fin 2, IntegralMv (![atX hh, atY hh] i) := by
    intro i
    fin_cases i
    · exact integralMv_subst hh1.gInt (hX0 0) (integralMv_X 0)
    · exact integralMv_subst hh1.gInt (hX0 1) (integralMv_X 1)
  have Hp : MvPowerSeries.HasSubst ![atX hh, atY hh] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hp0
  refine ⟨⟨PowerSeries.constantCoeff_subst_eq_zero hh1.g0 lam h.lam0, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [derivative_subst Hh]
    exact integralPS_mul (honF_integral_subst hlam' hh1.g0 hh1.gInt) (integralPS_derivative hh1.gInt)
  · have key := qls hl hl1 lam h.lam0 hlam' (hh.subst (MvPowerSeries.map (σ.comp σ) Φ))
      (Φ.subst ![atX hh, atY hh])
      (PowerSeries.constantCoeff_subst_eq_zero h'.Φ0 hh hh1.g0)
      (MvPowerSeries.constantCoeff_subst_eq_zero Hp hp0 h.Φ0)
      (integralMv_subst hh1.gInt h'.Φ0 h'.Φint) (integralMv_subst2 h.Φint hp0 hpI) hh1.add
    have ex : atX (lam.subst hh) = lam.subst (atX hh) :=
      PowerSeries.subst_comp_subst_apply Hh (HX 0) lam
    have ey : atY (lam.subst hh) = lam.subst (atY hh) :=
      PowerSeries.subst_comp_subst_apply Hh (HX 1) lam
    have ax : (atX lam).subst ![atX hh, atY hh] = lam.subst (atX hh) :=
      (honF_subst_subst lam (hX0 0) Hp).trans (by rw [MvPowerSeries.subst_X Hp]; rfl)
    have ay : (atY lam).subst ![atX hh, atY hh] = lam.subst (atY hh) :=
      (honF_subst_subst lam (hX0 1) Hp).trans (by rw [MvPowerSeries.subst_X Hp]; rfl)
    have e1 : lam.subst (Φ.subst ![atX hh, atY hh]) = atX (lam.subst hh) + atY (lam.subst hh) := by
      rw [ex, ey, ← honF_subst_subst lam h.Φ0 Hp, h.log, MvPowerSeries.subst_add Hp, ax, ay]
    rw [e1] at key
    rw [PowerSeries.subst_comp_subst_apply Hh HΦ', sub_sub]
    exact key
  · have key := qls1 hl hl1 lam h.lam0 hlam' (hh.subst (PowerSeries.map (σ.comp σ) A))
      (A.subst hh) (PowerSeries.constantCoeff_subst_eq_zero h'.A0 hh hh1.g0)
      (PowerSeries.constantCoeff_subst_eq_zero hh1.g0 A h.A0)
      (honF_integral_subst hh1.gInt h'.A0 h'.Aint) (honF_integral_subst h.Aint hh1.g0 hh1.gInt) hh1.eig
    rw [← PowerSeries.subst_comp_subst_apply HA Hh, h.Alog, PowerSeries.subst_mul Hh,
      PowerSeries.subst_C] at key
    rw [PowerSeries.subst_comp_subst_apply Hh HA']
    exact key
  · have key := qls1 hl hl1 lam h.lam0 hlam' e (hh.subst ((X : PowerSeries K) ^ (l ^ 2))) he0
      (PowerSeries.constantCoeff_subst_eq_zero hXq0 hh hh1.g0) he
      (honF_integral_subst hh1.gInt hXq0 (integralPS_pow integralPS_X _)) hh2
    rw [hlog] at key
    rw [PowerSeries.subst_comp_subst_apply Hh HXq]
    exact key
  · rw [Formalism.LT.PadicP.coeff_one_subst lam hh h.lam0 hh1.g0, h.lam1, one_mul]

theorem lemmaQ_tw (hF : FrobField K l σ) (h : HD σ lam Φ A a) (i : ℕ) {D : PowerSeries K}
    (hD : QCls l (MvPowerSeries.map ((σ.comp σ) ^ i) Φ) (PowerSeries.map ((σ.comp σ) ^ i) A) a D) :
    ∃ Dp : PowerSeries K,
      QCls l (MvPowerSeries.map ((σ.comp σ) ^ (i + 1)) Φ)
        (PowerSeries.map ((σ.comp σ) ^ (i + 1)) A) a Dp ∧
      DivBy (l : K) (D - C (coeff 1 D) * PowerSeries.map ((σ.comp σ) ^ i) lam
        - Dp.subst ((X : PowerSeries K) ^ (l ^ 2))) := by
  obtain ⟨Dp, hDp, hdiv⟩ := lemmaQ hF (HD.map_sq hF h i) hD
  refine ⟨Dp, ?_, hdiv⟩
  simp only [pow_succ', RingHom.mul_def, MvPowerSeries.map_comp, PowerSeries.map_comp,
    RingHom.comp_apply]
  exact hDp

theorem hon_series (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam)
    (hlev : ∃ i, i ≤ l ^ 2 ∧ ‖coeff i e‖ = 1) :
    ∃ c : ℕ → K, ‖c 0‖ = 1 ∧ (∀ i, ‖c i‖ ≤ 1) ∧ ∀ N : ℕ, ∃ R : PowerSeries K,
      constantCoeff R = 0 ∧
      DivBy (l : K) (C (l : K) * lam
        - ∑ i ∈ Finset.range N, C (c i) *
            (PowerSeries.map ((σ.comp σ) ^ (i + 1)) lam).subst
              ((X : PowerSeries K) ^ ((l ^ 2) ^ (i + 1)))
        - R.subst ((X : PowerSeries K) ^ ((l ^ 2) ^ (N + 1)))) := by
  obtain ⟨hh, hhom, hdiv, hc1⟩ := hon_shape hF h he0 he hlog
  obtain ⟨hQ, hmod, hcoef⟩ := hon_mu hF h he0 he hlog hhom hdiv
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  have hQ' : QCls l (MvPowerSeries.map ((σ.comp σ) ^ (0 + 1)) Φ)
      (PowerSeries.map ((σ.comp σ) ^ (0 + 1)) A) a (lam.subst hh) := by
    simpa using hQ

  let seq : (i : ℕ) → {D : PowerSeries K // QCls l (MvPowerSeries.map ((σ.comp σ) ^ (i + 1)) Φ)
      (PowerSeries.map ((σ.comp σ) ^ (i + 1)) A) a D} := fun i =>
    Nat.rec (motive := fun i => {D : PowerSeries K // QCls l (MvPowerSeries.map ((σ.comp σ) ^ (i + 1)) Φ)
      (PowerSeries.map ((σ.comp σ) ^ (i + 1)) A) a D}) ⟨lam.subst hh, hQ'⟩
      (fun i D => ⟨Classical.choose (lemmaQ_tw hF h (i + 1) D.2),
        (Classical.choose_spec (lemmaQ_tw hF h (i + 1) D.2)).1⟩) i
  have hstep : ∀ i, DivBy (l : K) ((seq i).1 - C (coeff 1 (seq i).1) *
      PowerSeries.map ((σ.comp σ) ^ (i + 1)) lam - (seq (i + 1)).1.subst ((X : PowerSeries K) ^ (l ^ 2))) :=
    fun i => (Classical.choose_spec (lemmaQ_tw hF h (i + 1) (seq i).2)).2

  have hsub : ∀ m : ℕ, m ≠ 0 → PowerSeries.HasSubst ((X : PowerSeries K) ^ m) := fun m hm =>
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hm])
  have hcomp : ∀ (f : PowerSeries K) (m q : ℕ), m ≠ 0 → q ≠ 0 →
      PowerSeries.subst ((X : PowerSeries K) ^ m) (f.subst ((X : PowerSeries K) ^ q) : PowerSeries K) =
        f.subst ((X : PowerSeries K) ^ (m * q)) := by
    intro f m q hm hq
    rw [PowerSeries.subst_comp_subst_apply (hsub q hq) (hsub m hm)]
    congr 1
    rw [← PowerSeries.coe_substAlgHom (hsub m hm), map_pow, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_X (hsub m hm), ← pow_mul]
  refine ⟨fun i => coeff 1 (seq i).1, ?_, fun i => (seq i).2.norm_coeff_one,
    fun N => ⟨(seq N).1, (seq N).2.D0, ?_⟩⟩
  · show ‖coeff 1 (lam.subst hh)‖ = 1
    rw [hcoef, hc1]
    exact hon_level hF h he0 he hlog hlev
  · induction N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, sub_zero, zero_add, pow_one]
      exact hmod
    | succ N ih =>
      have hm : (l ^ 2) ^ (N + 1) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hl0)
      have h1 := (divBy_expand_iff (l : K) ((l ^ 2) ^ (N + 1)) hm _).2 (hstep N)
      rw [← PowerSeries.coe_substAlgHom (hsub _ hm), map_sub, map_sub, ← PowerSeries.smul_eq_C_mul,
        map_smul, PowerSeries.smul_eq_C_mul, PowerSeries.coe_substAlgHom, hcomp _ _ _ hm (pow_ne_zero _ hl0), ← pow_succ] at h1
      have := divBy_add ih h1
      convert this using 1
      simp only [Finset.sum_range_succ]
      ring

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

def triSol {K : Type} [Field K] (a : ℕ → ℕ → K) (b : ℕ → K) : ℕ → K
  | m => (b m - ∑ i : Fin m, triSol a b i.1 * a i.1 m) / a m m

theorem triSol_eq {K : Type} [Field K] (a : ℕ → ℕ → K) (b : ℕ → K) (ha : ∀ m, a m m ≠ 0)
    (m : ℕ) : ∑ i ∈ Finset.range (m + 1), triSol a b i * a i m = b m := by
  have h : triSol a b m = (b m - ∑ i : Fin m, triSol a b i.1 * a i.1 m) / a m m := by
    rw [triSol]
  rw [Finset.sum_range_succ, Finset.sum_range, h, div_mul_cancel₀ _ (ha m)]
  ring

theorem triSol_norm (a : ℕ → ℕ → K) (b : ℕ → K) (ha1 : ∀ i m, ‖a i m‖ ≤ 1)
    (ha : ∀ m, ‖a m m‖ = 1) (r : ℝ) (hb : ∀ m, ‖b m‖ ≤ r) (m : ℕ) : ‖triSol a b m‖ ≤ r := by
  have hr : 0 ≤ r := (norm_nonneg _).trans (hb 0)
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [triSol, norm_div, ha, div_one, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hb m) ?_)
    rw [norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr fun i _ => ?_
    rw [norm_mul]
    calc ‖triSol a b i.1‖ * ‖a i.1 m‖ ≤ r * 1 :=
          mul_le_mul (ih i.1 i.2) (ha1 _ _) (norm_nonneg _) hr
      _ = r := mul_one r

theorem norm_pow_apply_of_isometric (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (i : ℕ) (x : K) :
    ‖(τ ^ i) x‖ = ‖x‖ := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, hτ, ih]

def triIter {K : Type} [Field K] (a : ℕ → ℕ → K) (π : K) : ℕ → ℕ → K
  | 0 => triSol a (fun m => if m = 0 then a 0 0 else 0)
  | k + 1 => triSol a (fun m => if m = 0 then 0 else π * triIter a π k (m + 1))

theorem triIter_norm (a : ℕ → ℕ → K) (π : K) (ha1 : ∀ i m, ‖a i m‖ ≤ 1)
    (ha : ∀ m, ‖a m m‖ = 1) (k m : ℕ) : ‖triIter a π k m‖ ≤ ‖π‖ ^ k := by
  induction k generalizing m with
  | zero =>
    rw [triIter, pow_zero]
    refine triSol_norm a _ ha1 ha 1 (fun j => ?_) m
    split_ifs
    · exact ha1 0 0
    · simp
  | succ k ih =>
    rw [triIter]
    refine triSol_norm a _ ha1 ha _ (fun j => ?_) m
    split_ifs
    · simp
    · rw [norm_mul, pow_succ']
      exact mul_le_mul_of_nonneg_left (ih _) (norm_nonneg _)

theorem twisted_division (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (π : K) (hπ : ‖π‖ < 1)
    (c : ℕ → K) (hc0 : ‖c 0‖ = 1) (hc : ∀ i, ‖c i‖ ≤ 1) :
    ∃ t : ℕ → K, t 0 = 1 ∧ (∀ n, ‖t n‖ ≤ 1) ∧
      ∀ n, 2 ≤ n → π * t n = ∑ i ∈ Finset.range n, t i * (τ ^ i) (c (n - 1 - i)) := by
  set a : ℕ → ℕ → K := fun i m => (τ ^ i) (c (m - i)) with ha_def
  have ha1 : ∀ i m, ‖a i m‖ ≤ 1 := fun i m => by
    rw [ha_def]; simp only; rw [norm_pow_apply_of_isometric τ hτ]; exact hc _
  have ha : ∀ m, ‖a m m‖ = 1 := fun m => by
    rw [ha_def]; simp only; rw [norm_pow_apply_of_isometric τ hτ, Nat.sub_self]; exact hc0
  have ha0 : ∀ m, a m m ≠ 0 := fun m h => by
    have := ha m; rw [h, norm_zero] at this; exact zero_ne_one this
  have hsum : ∀ m, Summable fun k => triIter a π k m := fun m =>
    Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg π) hπ)
      (fun k => triIter_norm a π ha1 ha k m)
  have hz0 : triIter a π 0 0 = 1 := by
    have h := triSol_eq a (fun m => if m = 0 then a 0 0 else 0) ha0 0
    simp only [zero_add, Finset.sum_range_one, if_true] at h
    rw [triIter]
    exact mul_right_cancel₀ (ha0 0) (h.trans (one_mul _).symm)
  have hzs : ∀ k, triIter a π (k + 1) 0 = 0 := fun k => by
    have h := triSol_eq a (fun m => if m = 0 then 0 else π * triIter a π k (m + 1)) ha0 0
    simp only [zero_add, Finset.sum_range_one, if_true] at h
    rw [triIter]
    exact (mul_eq_zero.mp h).resolve_right (ha0 0)
  refine ⟨fun m => ∑' k, triIter a π k m, ?_, fun n => ?_, fun n hn => ?_⟩
  · simp only
    rw [(hsum 0).tsum_eq_zero_add, hz0]
    simp [hzs]
  · refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one fun k => ?_
    exact (triIter_norm a π ha1 ha k n).trans (pow_le_one₀ (norm_nonneg _) hπ.le)
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hterm : ∀ i, (∑' k, triIter a π k i) * (τ ^ i) (c (m + 2 - 1 - i))
        = ∑' k, triIter a π k i * a i (m + 1) := fun i => by
      rw [tsum_mul_right]
      rfl
    simp only [hterm]
    rw [← Summable.tsum_finsetSum (fun i _ => (hsum i).mul_right _)]
    have hS : Summable fun k => ∑ i ∈ Finset.range (m + 2), triIter a π k i * a i (m + 1) :=
      summable_sum fun i _ => (hsum i).mul_right _
    rw [hS.tsum_eq_zero_add, ← tsum_mul_left]
    have h0 : ∑ i ∈ Finset.range (m + 2), triIter a π 0 i * a i (m + 1) = 0 := by
      have h := triSol_eq a (fun m => if m = 0 then a 0 0 else 0) ha0 (m + 1)
      simpa [triIter] using h
    rw [h0, zero_add]
    refine tsum_congr fun k => ?_
    have h := triSol_eq a (fun m => if m = 0 then 0 else π * triIter a π k (m + 1)) ha0 (m + 1)
    simpa [triIter] using h.symm

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

section Regroup

variable {K : Type} [Field K]

theorem hon_regroup (τ : K →+* K) (π : K) (c t w : ℕ → K) (M : ℕ) (hM : 1 ≤ M)
    (hw : ∀ m, M ≤ m → w m = 0) (ht0 : t 0 = 1)
    (ht : ∀ n, 2 ≤ n → π * t n = ∑ i ∈ Finset.range n, t i * (τ ^ i) (c (n - 1 - i))) :
    ∑ i ∈ Finset.range M, t i * (π * w i - ∑ j ∈ Finset.range M, (τ ^ i) (c j) * w (i + j + 1))
      = π * w 0 - (c 0 - π * t 1) * w 1 := by
  obtain ⟨K', rfl⟩ : ∃ K', M = K' + 1 := ⟨M - 1, by omega⟩

  have hS : ∑ i ∈ Finset.range (K' + 1), ∑ j ∈ Finset.range (K' + 1), t i * (τ ^ i) (c j) * w (i + j + 1)
      = ∑ n ∈ Finset.range (K' + 1), w (n + 1) * ∑ i ∈ Finset.range (n + 1), t i * (τ ^ i) (c (n - i)) := by
    have hA : ∀ i ∈ Finset.range (K' + 1),
        ∑ j ∈ Finset.range (K' + 1), t i * (τ ^ i) (c j) * w (i + j + 1)
          = ∑ j ∈ Finset.range (K' + 1 - i), t i * (τ ^ i) (c j) * w (i + j + 1) := by
      intro i _
      symm
      refine Finset.sum_subset (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega)
        fun j _ hj => ?_
      simp only [Finset.mem_range, not_lt] at hj
      rw [hw _ (by omega), mul_zero]
    rw [Finset.sum_congr rfl hA]
    have hflip := Finset.sum_range_diag_flip (K' + 1)
      (fun i j => t i * (τ ^ i) (c j) * w (i + j + 1))
    beta_reduce at hflip
    rw [← hflip]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    have e : i + (n - i) + 1 = n + 1 := by omega
    rw [e]
    ring
  have hsplit : ∀ i, t i * (π * w i - ∑ j ∈ Finset.range (K' + 1), (τ ^ i) (c j) * w (i + j + 1))
      = π * (t i * w i) - ∑ j ∈ Finset.range (K' + 1), t i * (τ ^ i) (c j) * w (i + j + 1) := by
    intro i
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  have hF : ∀ n ∈ Finset.range K',
      w (n + 1 + 1) * ∑ i ∈ Finset.range (n + 1 + 1), t i * (τ ^ i) (c (n + 1 - i))
        = π * (t (n + 1 + 1) * w (n + 1 + 1)) := by
    intro n _
    have h2 := ht (n + 1 + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h2
    rw [← mul_assoc, h2]
    ring
  have hF0 : w (0 + 1) * ∑ i ∈ Finset.range (0 + 1), t i * (τ ^ i) (c (0 - i)) = c 0 * w 1 := by
    simp [ht0] <;> ring
  have htel := Finset.sum_range_sub' (fun m => t (m + 1) * w (m + 1)) K'
  beta_reduce at htel
  rw [Finset.sum_sub_distrib, zero_add] at htel
  have hwM : w (K' + 1) = 0 := hw _ le_rfl
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_sub_distrib, ← Finset.mul_sum, hS,
    Finset.sum_range_succ', Finset.sum_range_succ']
  try beta_reduce
  rw [Finset.sum_congr rfl hF, ← Finset.mul_sum, hF0, ht0]
  linear_combination π * htel - π * t (K' + 1) * hwM

end Regroup

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] {l : ℕ}
  {σ : K →+* K}
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}

theorem hon_lt_sq_pow (hl : 2 ≤ l) (n : ℕ) : n < (l ^ 2) ^ n := by
  have h4 : 1 < l ^ 2 := by nlinarith
  first
  | exact Nat.lt_pow_self h4
  | exact Nat.lt_pow_self h4 n

private theorem coeff_subst_X_pow_eq_ite_dvd' (f : PowerSeries K) {k : ℕ} (hk : k ≠ 0) (m : ℕ) :
    coeff m (f.subst ((X : PowerSeries K) ^ k)) = if k ∣ m then coeff (m / k) f else 0 := by
  have ha : PowerSeries.HasSubst ((X : PowerSeries K) ^ k) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hk])
  rw [PowerSeries.coeff_subst' ha]
  simp only [← pow_mul, PowerSeries.coeff_X_pow]
  split_ifs with hd
  · obtain ⟨q, rfl⟩ := hd
    rw [finsum_eq_single _ q]
    · simp [Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero hk)]
    · intro d hd
      have : k * q ≠ k * d := fun h => hd (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) h).symm
      simp [this]
  · rw [finsum_eq_zero_of_forall_eq_zero]
    intro d
    have : m ≠ k * d := fun h => hd ⟨d, h⟩
    simp [this]

theorem hon_series_coeff (hl : 2 ≤ l) (τ : K →+* K) (c : ℕ → K)
    (h : ∀ N : ℕ, ∃ R : PowerSeries K, constantCoeff R = 0 ∧
      DivBy (l : K) (C (l : K) * lam
        - ∑ i ∈ Finset.range N, C (c i) *
            (PowerSeries.map (τ ^ (i + 1)) lam).subst ((X : PowerSeries K) ^ ((l ^ 2) ^ (i + 1)))
        - R.subst ((X : PowerSeries K) ^ ((l ^ 2) ^ (N + 1))))) (n : ℕ) :
    ‖(l : K) * coeff n lam - ∑ i ∈ (Finset.range n).filter (fun i => (l ^ 2) ^ (i + 1) ∣ n),
      c i * (τ ^ (i + 1)) (coeff (n / (l ^ 2) ^ (i + 1)) lam)‖ ≤ ‖(l : K)‖ := by
  obtain ⟨R, hR0, hR⟩ := h n
  have hq : l ^ 2 ≠ 0 := pow_ne_zero 2 (by omega)
  have hRn : coeff n (R.subst ((X : PowerSeries K) ^ ((l ^ 2) ^ (n + 1)))) = 0 := by
    rw [coeff_subst_X_pow_eq_ite_dvd' R (pow_ne_zero _ hq)]
    split_ifs
    · rw [Nat.div_eq_of_lt (lt_of_lt_of_le (hon_lt_sq_pow hl n)
          (Nat.pow_le_pow_right (Nat.pos_of_ne_zero hq) (Nat.le_succ n))),
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hR0]
    · rfl
  have hsum : coeff n (∑ i ∈ Finset.range n, C (c i) *
        (PowerSeries.map (τ ^ (i + 1)) lam).subst ((X : PowerSeries K) ^ ((l ^ 2) ^ (i + 1))))
      = ∑ i ∈ (Finset.range n).filter (fun i => (l ^ 2) ^ (i + 1) ∣ n),
          c i * (τ ^ (i + 1)) (coeff (n / (l ^ 2) ^ (i + 1)) lam) := by
    rw [map_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PowerSeries.coeff_C_mul, coeff_subst_X_pow_eq_ite_dvd' _ (pow_ne_zero _ hq)]
    split_ifs
    · rw [PowerSeries.coeff_map]
    · rw [mul_zero]
  unfold DivBy at hR
  have hcoef := hR n
  rw [map_sub, map_sub, PowerSeries.coeff_C_mul, hsum, hRn, sub_zero] at hcoef
  exact hcoef

def twC (l : ℕ) (τ : K →+* K) (lam : PowerSeries K) (n m : ℕ) : K :=
  if (l ^ 2) ^ m ∣ n then (τ ^ m) (coeff (n / (l ^ 2) ^ m) lam) else 0

theorem twC_zero (τ : K →+* K) (n : ℕ) : twC l τ lam n 0 = coeff n lam := by
  simp [twC]

theorem twC_one (τ : K →+* K) (n : ℕ) :
    twC l τ lam n 1 = if l ^ 2 ∣ n then τ (coeff (n / l ^ 2) lam) else 0 := by
  simp [twC]

theorem twC_eq_zero (hl : 2 ≤ l) (τ : K →+* K) (h0 : constantCoeff lam = 0) {n m : ℕ}
    (hnm : n ≤ m) : twC l τ lam n m = 0 := by
  unfold twC
  split_ifs with hd
  · have hlt : n < (l ^ 2) ^ m := lt_of_le_of_lt hnm (hon_lt_sq_pow hl m)
    rw [Nat.div_eq_of_lt hlt, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero]
  · rfl

theorem twC_shift (τ : K →+* K) {n i : ℕ} (hd : (l ^ 2) ^ i ∣ n) (j : ℕ) :
    (τ ^ i) (twC l τ lam (n / (l ^ 2) ^ i) j) = twC l τ lam n (i + j) := by
  unfold twC
  simp only [pow_add, RingHom.mul_def, RingHom.comp_apply, Nat.dvd_div_iff_mul_dvd hd,
    Nat.div_div_eq_div_mul]
  split_ifs <;> simp

theorem twC_of_not_dvd (τ : K →+* K) {n i : ℕ} (hd : ¬ (l ^ 2) ^ i ∣ n) (j : ℕ) :
    twC l τ lam n (i + j) = 0 := by
  unfold twC
  rw [if_neg]
  intro h
  exact hd (dvd_trans (pow_dvd_pow _ (Nat.le_add_right i j)) h)

theorem hon_norm_pow_apply (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (i : ℕ) (x : K) :
    ‖(τ ^ i) x‖ = ‖x‖ := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, hτ, ih]

theorem hon_coeff_unif (hl : 2 ≤ l) (τ : K →+* K) (c : ℕ → K) (h0 : constantCoeff lam = 0)
    (E : ∀ n, ‖(l : K) * coeff n lam - ∑ i ∈ (Finset.range n).filter (fun i => (l ^ 2) ^ (i + 1) ∣ n),
      c i * (τ ^ (i + 1)) (coeff (n / (l ^ 2) ^ (i + 1)) lam)‖ ≤ ‖(l : K)‖) {n M : ℕ} (hM : n ≤ M) :
    ‖(l : K) * coeff n lam - ∑ j ∈ Finset.range M, c j * twC l τ lam n (j + 1)‖ ≤ ‖(l : K)‖ := by
  have h1 : ∑ i ∈ (Finset.range n).filter (fun i => (l ^ 2) ^ (i + 1) ∣ n),
      c i * (τ ^ (i + 1)) (coeff (n / (l ^ 2) ^ (i + 1)) lam)
      = ∑ j ∈ Finset.range n, c j * twC l τ lam n (j + 1) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold twC
    split_ifs <;> simp
  have h2 : ∑ j ∈ Finset.range n, c j * twC l τ lam n (j + 1)
      = ∑ j ∈ Finset.range M, c j * twC l τ lam n (j + 1) := by
    refine Finset.sum_subset (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega)
      fun j _ hj => ?_
    rw [Finset.mem_range, not_lt] at hj
    rw [twC_eq_zero hl τ h0 (by omega), mul_zero]
  rw [← h2, ← h1]
  exact E n

theorem hon_coeff_shift (hl : 2 ≤ l) (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (c : ℕ → K)
    (h0 : constantCoeff lam = 0)
    (E : ∀ n, ‖(l : K) * coeff n lam - ∑ i ∈ (Finset.range n).filter (fun i => (l ^ 2) ^ (i + 1) ∣ n),
      c i * (τ ^ (i + 1)) (coeff (n / (l ^ 2) ^ (i + 1)) lam)‖ ≤ ‖(l : K)‖) {n M : ℕ} (hM : n ≤ M)
    (i : ℕ) :
    ‖(l : K) * twC l τ lam n i - ∑ j ∈ Finset.range M, (τ ^ i) (c j) * twC l τ lam n (i + j + 1)‖
      ≤ ‖(l : K)‖ := by
  by_cases hd : (l ^ 2) ^ i ∣ n
  · have e1 : twC l τ lam n i = (τ ^ i) (coeff (n / (l ^ 2) ^ i) lam) := by
      rw [← twC_zero (l := l) τ (n / (l ^ 2) ^ i), twC_shift τ hd 0, add_zero]
    have e2 : ∀ j, twC l τ lam n (i + j + 1) = (τ ^ i) (twC l τ lam (n / (l ^ 2) ^ i) (j + 1)) := by
      intro j
      rw [twC_shift τ hd (j + 1), add_assoc]
    have hn' : n / (l ^ 2) ^ i ≤ M := le_trans (Nat.div_le_self _ _) hM
    have key := hon_coeff_unif hl τ c h0 E hn'
    rw [← hon_norm_pow_apply τ hτ i] at key
    convert key using 2
    rw [map_sub, map_mul, map_natCast, e1, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, e2]
  · have e1 : twC l τ lam n i = 0 := by simpa using twC_of_not_dvd (lam := lam) τ hd 0
    have e2 : ∀ j, twC l τ lam n (i + j + 1) = 0 := fun j => by
      rw [add_assoc]
      exact twC_of_not_dvd τ hd (j + 1)
    simp only [e1, e2, mul_zero, Finset.sum_const_zero, sub_zero, norm_zero]
    exact norm_nonneg _

theorem hon_main (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam)
    (hlev : ∃ i, i ≤ l ^ 2 ∧ ‖coeff i e‖ = 1) :
    ∃ c : K, ‖c‖ = 1 ∧ IntegralPS (lam - (c / (l : K)) •
      (PowerSeries.map (σ.comp σ) lam).subst ((X : PowerSeries K) ^ (l ^ 2))) := by
  have hl : 2 ≤ l := hF.prime.two_le
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨c, hc0, hc, hN⟩ := hon_series hF h he0 he hlog hlev
  have hτ : ∀ x, ‖(σ.comp σ) x‖ = ‖x‖ := fun x => (hF.isom _).trans (hF.isom x)
  obtain ⟨t, ht0, htn, ht⟩ := twisted_division (σ.comp σ) hτ (l : K) hF.norm_l c hc0 hc
  have E := hon_series_coeff hl (σ.comp σ) c hN
  have hlt : ‖(l : K) * t 1‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (htn 1)).trans_lt hF.norm_l
  refine ⟨c 0 - (l : K) * t 1, ?_, fun n => ?_⟩
  · rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [norm_neg, hc0]; exact hlt.ne'), norm_neg, hc0]
    exact max_eq_left hlt.le
  · have key := hon_regroup (σ.comp σ) (l : K) c t (twC l (σ.comp σ) lam n) (n + 1) (by omega)
      (fun m hm => twC_eq_zero hl _ h.lam0 (by omega)) ht0 ht
    have bd : ‖(l : K) * twC l (σ.comp σ) lam n 0
        - (c 0 - (l : K) * t 1) * twC l (σ.comp σ) lam n 1‖ ≤ ‖(l : K)‖ := by
      rw [← key]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
      rw [norm_mul]
      exact (mul_le_mul (htn i) (hon_coeff_shift hl _ hτ c h.lam0 E (Nat.le_succ n) i)
        (norm_nonneg _) zero_le_one).trans (one_mul _).le
    rw [twC_zero, twC_one] at bd
    rw [map_sub, coeff_smul, coeff_subst_X_pow (pow_ne_zero _ (by omega)), smul_eq_mul]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    have : coeff n lam - (c 0 - (l : K) * t 1) / (l : K) *
        (if l ^ 2 ∣ n then coeff (n / l ^ 2) (PowerSeries.map (σ.comp σ) lam) else 0)
        = ((l : K) * coeff n lam - (c 0 - (l : K) * t 1) *
          (if l ^ 2 ∣ n then (σ.comp σ) (coeff (n / l ^ 2) lam) else 0)) / (l : K) := by
      rw [coeff_map]; field_simp
    rw [this, norm_div]
    exact div_le_one_of_le₀ bd (norm_nonneg _)

end ReciprocityTheory.ChartRestriction.L1
end
end
