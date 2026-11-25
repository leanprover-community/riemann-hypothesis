module

public import Formalism.TorsionNormIteration.InvIntegralOfClass
public import Mathlib.RingTheory.PowerSeries.Derivative
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.KurDefs
public import Mathlib.RingTheory.PowerSeries.Inverse

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K]

section Ring
variable {ι : Type}

theorem integralMv_iff_divBy_one (F : MvPowerSeries ι K) : IntegralMv F ↔ DivByMv (1 : K) F := by
  first
  | (unfold IntegralMv DivByMv; simp)
theorem integralPS_iff_mv (f : PowerSeries K) : IntegralPS f ↔ IntegralMv (ι := Unit) f := by
  rw [integralMv_iff_divBy_one]
  unfold IntegralPS DivByMv
  constructor
  · intro h d
    have hd : d = Finsupp.single () (d ()) := by
      refine Finsupp.ext fun u => ?_
      cases u
      simp
    rw [hd, norm_one]
    exact h (d ())
  · intro h n
    have := h (Finsupp.single () n)
    rw [norm_one] at this
    exact this
theorem divByMv_mul {x y : K} {F G : MvPowerSeries ι K} (hF : DivByMv x F) (hG : DivByMv y G) :
    DivByMv (x * y) (F * G) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul, norm_mul]
  refine Finset.sum_induction _ (fun z : K => ‖z‖ ≤ ‖x‖ * ‖y‖)
    (fun a b ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb))
    (by rw [norm_zero]; positivity) ?_
  intro p _
  rw [norm_mul]
  exact mul_le_mul (hF _) (hG _) (norm_nonneg _) (norm_nonneg _)
theorem integralMv_one : IntegralMv (1 : MvPowerSeries ι K) := by
  classical
  refine (integralMv_iff_divBy_one _).mpr fun d => ?_
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp
theorem integralMv_X (i : ι) : IntegralMv (MvPowerSeries.X i : MvPowerSeries ι K) := by
  classical
  refine (integralMv_iff_divBy_one _).mpr fun d => ?_
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp
theorem integralMv_mul {F G : MvPowerSeries ι K} (hF : IntegralMv F) (hG : IntegralMv G) :
    IntegralMv (F * G) := by
  rw [integralMv_iff_divBy_one] at *
  have h := divByMv_mul hF hG
  rwa [one_mul] at h
theorem integralMv_pow {F : MvPowerSeries ι K} (hF : IntegralMv F) (n : ℕ) : IntegralMv (F ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact integralMv_one
  | succ n ih => rw [pow_succ]; exact integralMv_mul ih hF

end Ring

section OneVar

theorem integralPS_X : IntegralPS (X : PowerSeries K) := by
  exact (integralPS_iff_mv _).mpr (integralMv_X ())
theorem integralPS_mul {f g : PowerSeries K} (hf : IntegralPS f) (hg : IntegralPS g) :
    IntegralPS (f * g) := by
  rw [integralPS_iff_mv] at *
  exact integralMv_mul hf hg
theorem integralPS_pow {f : PowerSeries K} (hf : IntegralPS f) (n : ℕ) : IntegralPS (f ^ n) := by
  rw [integralPS_iff_mv] at *
  exact integralMv_pow hf n

theorem integralPS_inv {f : PowerSeries K} (hf : IntegralPS f) (h0 : ‖constantCoeff f‖ = 1) :
    IntegralPS f⁻¹ := by
  unfold IntegralPS at hf ⊢
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih
  rw [PowerSeries.coeff_inv]
  split_ifs with hn
  · rw [norm_inv, h0, inv_one]
  · rw [norm_mul, norm_neg, norm_inv, h0, inv_one, one_mul]
    refine Finset.sum_induction _ (fun z : K => ‖z‖ ≤ 1)
      (fun a b ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb))
      (by rw [norm_zero]; exact zero_le_one) ?_
    intro p _
    split_ifs with hlt
    · rw [norm_mul]
      exact mul_le_one₀ (hf _) (norm_nonneg _) (ih _ hlt)
    · rw [norm_zero]
      exact zero_le_one

end OneVar

section Subst
variable {ι : Type}

private theorem norm_finsum_le_of_forall_norm_le {α : Type} (g : α → K) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖g i‖ ≤ C) : ‖∑ᶠ i, g i‖ ≤ C := by
  by_cases hs : (Function.support g).Finite
  · rw [finsum_eq_sum g hs]
    exact Finset.sum_induction _ (fun z : K => ‖z‖ ≤ C)
      (fun a b ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb))
      (by rw [norm_zero]; exact hC) (fun i _ => h i)
  · rw [finsum_of_infinite_support hs, norm_zero]
    exact hC

theorem divByMv_subst2 {x : K} {F : MvPowerSeries (Fin 2) K} {P : Fin 2 → MvPowerSeries ι K}
    (hF : DivByMv x F) (hP0 : ∀ i, MvPowerSeries.constantCoeff (P i) = 0)
    (hP : ∀ i, IntegralMv (P i)) : DivByMv x (F.subst P) := by
  have ha : MvPowerSeries.HasSubst P := by
    first
    | exact ⟨fun s => by rw [hP0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  have hprod : ∀ e : Fin 2 →₀ ℕ, IntegralMv (e.prod fun s k => P s ^ k) := by
    intro e
    unfold Finsupp.prod
    exact Finset.prod_induction _ IntegralMv (fun _ _ => integralMv_mul) integralMv_one
      (fun s _ => integralMv_pow (hP s) _)
  intro d
  rw [MvPowerSeries.coeff_subst ha]
  exact norm_finsum_le_of_forall_norm_le _ (norm_nonneg _) fun e => by
    rw [smul_eq_mul, norm_mul]
    have h1 := (integralMv_iff_divBy_one _).mp (hprod e) d
    rw [norm_one] at h1
    calc ‖MvPowerSeries.coeff e F‖ * ‖MvPowerSeries.coeff d (e.prod fun s k => P s ^ k)‖
        ≤ ‖x‖ * 1 := mul_le_mul (hF e) h1 (norm_nonneg _) (norm_nonneg _)
      _ = ‖x‖ := mul_one _
theorem integralMv_subst2 {F : MvPowerSeries (Fin 2) K} {P : Fin 2 → MvPowerSeries ι K}
    (hF : IntegralMv F) (hP0 : ∀ i, MvPowerSeries.constantCoeff (P i) = 0)
    (hP : ∀ i, IntegralMv (P i)) : IntegralMv (F.subst P) := by
  rw [integralMv_iff_divBy_one] at hF ⊢
  exact divByMv_subst2 hF hP0 hP

end Subst

end ReciprocityTheory.ChartRestriction.L1
