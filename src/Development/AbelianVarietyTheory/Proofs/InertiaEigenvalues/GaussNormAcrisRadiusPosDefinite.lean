import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGaussGCTarget
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisGaussNormEventuallyMonomial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisNormOfNonzero

section
section
noncomputable section

open scoped Formalism.Per
open Filter Topology

namespace GlobalTheory.PMon.Gauss

theorem iSup_monomial_logConvex (c : ℕ → ℝ) (h0 : ∀ n, 0 ≤ c n) (h1 : ∀ n, c n ≤ 1)
    {ρ₁ ρ₂ t : ℝ} (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) (hρ₁1 : ρ₁ ≤ 1) (hρ₂1 : ρ₂ ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (⨆ n, c n * (ρ₁ ^ t * ρ₂ ^ (1 - t)) ^ n) ≤
      (⨆ n, c n * ρ₁ ^ n) ^ t * (⨆ n, c n * ρ₂ ^ n) ^ (1 - t) := by
  have hb : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → BddAbove (Set.range fun n => c n * ρ ^ n) := fun ρ h0' h1' =>
    ⟨1, Set.forall_mem_range.2 fun n => mul_le_one₀ (h1 n) (pow_nonneg h0' n) (pow_le_one₀ h0' h1')⟩
  apply ciSup_le
  intro n
  have hc : c n = c n ^ t * c n ^ (1 - t) := by
    rw [← Real.rpow_add' (h0 n) (by norm_num), add_sub_cancel, Real.rpow_one]
  have e : c n * (ρ₁ ^ t * ρ₂ ^ (1 - t)) ^ n = (c n * ρ₁ ^ n) ^ t * (c n * ρ₂ ^ n) ^ (1 - t) := by
    rw [Real.mul_rpow (h0 n) (pow_nonneg hρ₁ n), Real.mul_rpow (h0 n) (pow_nonneg hρ₂ n), mul_pow,
      Real.rpow_pow_comm hρ₁, Real.rpow_pow_comm hρ₂]
    conv_lhs => rw [hc]
    ring
  rw [e]
  have ht1' : 0 ≤ 1 - t := by linarith
  exact mul_le_mul
    (Real.rpow_le_rpow (mul_nonneg (h0 n) (pow_nonneg hρ₁ n)) (le_ciSup (hb ρ₁ hρ₁ hρ₁1) n) ht0)
    (Real.rpow_le_rpow (mul_nonneg (h0 n) (pow_nonneg hρ₂ n)) (le_ciSup (hb ρ₂ hρ₂ hρ₂1) n) ht1')
    (Real.rpow_nonneg (mul_nonneg (h0 n) (pow_nonneg hρ₂ n)) _)
    (Real.rpow_nonneg ((mul_nonneg (h0 n) (pow_nonneg hρ₁ n)).trans (le_ciSup (hb ρ₁ hρ₁ hρ₁1) n)) _)

theorem gA_logConvex (l : ℕ) [Fact l.Prime] (a : Formalism.Per.Ainf l) {ρ₁ ρ₂ t : ℝ} (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂)
    (hρ₁1 : ρ₁ ≤ 1) (hρ₂1 : ρ₂ ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    gA l (ρ₁ ^ t * ρ₂ ^ (1 - t)) a ≤ gA l ρ₁ a ^ t * gA l ρ₂ a ^ (1 - t) :=
  iSup_monomial_logConvex _ (fun n => by positivity)
    (fun n => Real.rpow_le_one (norm_nonneg _) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.prop _)) (by positivity))
    hρ₁ hρ₂ hρ₁1 hρ₂1 ht0 ht1

theorem rpow_mul_rpow_one_sub_self {a t : ℝ} (ha : 0 ≤ a) : a ^ t * a ^ (1 - t) = a := by
  rw [← Real.rpow_add' ha (by norm_num), add_sub_cancel, Real.rpow_one]

theorem gC_logConvex : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) (ρ₁ ρ₂ t : ℝ), (l : ℝ)⁻¹ ≤ ρ₁ → ρ₁ ≤ ρ₂ →
    ρ₂ < 1 → 0 ≤ t → t ≤ 1 → gC l (ρ₁ ^ t * ρ₂ ^ (1 - t)) x ≤ gC l ρ₁ x ^ t * gC l ρ₂ x ^ (1 - t) := by
  intro l _ x ρ₁ ρ₂ t h1 h12 h2 ht0 ht1
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hρ₁ : 0 < ρ₁ := (inv_pos.2 hl0).trans_le h1
  have hρ₂ : 0 < ρ₂ := hρ₁.trans_le h12
  have ht1' : 0 ≤ 1 - t := by linarith
  set ρ := ρ₁ ^ t * ρ₂ ^ (1 - t) with hρdef
  have hρlo : ρ₁ ≤ ρ := by
    calc ρ₁ = ρ₁ ^ t * ρ₁ ^ (1 - t) := (rpow_mul_rpow_one_sub_self hρ₁.le).symm
      _ ≤ ρ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hρ₁.le h12 ht1') (Real.rpow_nonneg hρ₁.le _)
  have hρhi : ρ ≤ ρ₂ := by
    calc ρ ≤ ρ₂ ^ t * ρ₂ ^ (1 - t) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hρ₁.le h12 ht0) (Real.rpow_nonneg hρ₂.le _)
      _ = ρ₂ := rpow_mul_rpow_one_sub_self hρ₂.le
  have hρ0 : 0 < ρ := hρ₁.trans_le hρlo
  have G : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → IsGauss l σ (gC l σ) := fun σ a b => isGauss_gC_of_le l σ a b
  have Gl : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → gC l σ (l : Formalism.Per.Acris l) = σ := by
    intro σ a b
    rw [← map_natCast (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)) l, (G σ a b).2.2.2.2]
    exact GlobalTheory.GaussSlope.gauss_l l ((inv_pos.2 hl0).le.trans a)
  have g : IsGauss l ρ (gC l ρ) := G ρ (h1.trans hρlo) (hρhi.trans_lt h2)
  have g₁ : IsGauss l ρ₁ (gC l ρ₁) := G ρ₁ h1 (h12.trans_lt h2)
  have g₂ : IsGauss l ρ₂ (gC l ρ₂) := G ρ₂ (h1.trans h12) h2

  have P : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → ∀ (k : ℕ) (y : Formalism.Per.Acris l),
      gC l σ ((l : Formalism.Per.Acris l) ^ k * y) = σ ^ k * gC l σ y := by
    intro σ a b k y
    rw [GlobalTheory.GaussSlope.map_pow_mul _ (G σ a b).2.2.2.1, Gl σ a b]

  have hs : ∀ s : Formalism.Per.Acris0 l, gC l ρ (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s) ≤
      gC l ρ₁ (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s) ^ t *
        gC l ρ₂ (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s) ^ (1 - t) := by
    intro s
    obtain ⟨k, a, ha⟩ := GlobalTheory.GaussSlope.exists_pow_mul_eq l s
    set y := algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s
    have e : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → σ ^ k * gC l σ y = gA l σ a := by
      intro σ a' b
      rw [← P σ a' b, ha, (G σ a' b).2.2.2.2]
    have key := gA_logConvex l a hρ₁.le hρ₂.le (h12.trans h2.le) h2.le ht0 ht1
    rw [← e ρ (h1.trans hρlo) (hρhi.trans_lt h2), ← e ρ₁ h1 (h12.trans_lt h2), ← e ρ₂ (h1.trans h12) h2,
      Real.mul_rpow (pow_nonneg hρ₁.le _) (g₁.1 y).1, Real.mul_rpow (pow_nonneg hρ₂.le _) (g₂.1 y).1,
      ← Real.rpow_pow_comm hρ₁.le, ← Real.rpow_pow_comm hρ₂.le] at key
    have e2 : (ρ₁ ^ t) ^ k * gC l ρ₁ y ^ t * ((ρ₂ ^ (1 - t)) ^ k * gC l ρ₂ y ^ (1 - t)) =
        ρ ^ k * (gC l ρ₁ y ^ t * gC l ρ₂ y ^ (1 - t)) := by
      rw [hρdef, mul_pow]; ring
    rw [e2] at key
    exact le_of_mul_le_mul_left key (pow_pos hρ0 k)

  have F : ∀ r : ℕ, gC l ρ x ≤ max (max (gC l ρ₁ x) (ρ₁ ^ r) ^ t * max (gC l ρ₂ x) (ρ₂ ^ r) ^ (1 - t)) (ρ ^ r) := by
    intro r
    obtain ⟨s, z, hx⟩ := (GlobalTheory.MemLoc.acris_basic l).2.2.1 x r
    set y := algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s
    have hz : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → gC l σ ((l : Formalism.Per.Acris l) ^ r * z) ≤ σ ^ r := by
      intro σ a b
      rw [P σ a b]
      exact mul_le_of_le_one_right (pow_nonneg ((inv_pos.2 hl0).le.trans a) _) ((G σ a b).1 z).2
    have hy : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → gC l σ y ≤ max (gC l σ x) (σ ^ r) := by
      intro σ a b
      have : y = x + -((l : Formalism.Per.Acris l) ^ r * z) := by rw [hx]; ring
      rw [this]
      refine ((G σ a b).2.1 _ _).trans (max_le_max le_rfl ?_)
      rw [(G σ a b).2.2.1]
      exact hz σ a b
    conv_lhs => rw [hx]
    refine (g.2.1 _ _).trans (max_le_max ?_ (hz ρ (h1.trans hρlo) (hρhi.trans_lt h2)))
    refine (hs s).trans (mul_le_mul (Real.rpow_le_rpow (g₁.1 y).1 (hy ρ₁ h1 (h12.trans_lt h2)) ht0)
      (Real.rpow_le_rpow (g₂.1 y).1 (hy ρ₂ (h1.trans h12) h2) ht1') (Real.rpow_nonneg (g₂.1 y).1 _)
      (Real.rpow_nonneg ((g₁.1 x).1.trans (le_max_left _ _)) _))
  have T : Tendsto (fun r : ℕ => max (max (gC l ρ₁ x) (ρ₁ ^ r) ^ t * max (gC l ρ₂ x) (ρ₂ ^ r) ^ (1 - t)) (ρ ^ r))
      atTop (𝓝 (max (max (gC l ρ₁ x) 0 ^ t * max (gC l ρ₂ x) 0 ^ (1 - t)) 0)) := by
    have t1 := tendsto_pow_atTop_nhds_zero_of_lt_one hρ₁.le (h12.trans_lt h2)
    have t2 := tendsto_pow_atTop_nhds_zero_of_lt_one hρ₂.le h2
    have t0 := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le (hρhi.trans_lt h2)
    exact ((((tendsto_const_nhds.max t1).rpow_const (Or.inr ht0)).mul
      ((tendsto_const_nhds.max t2).rpow_const (Or.inr ht1'))).max t0)
  have := ge_of_tendsto' T F
  rwa [max_eq_left (g₁.1 x).1, max_eq_left (g₂.1 x).1,
    max_eq_left (mul_nonneg (Real.rpow_nonneg (g₁.1 x).1 _) (Real.rpow_nonneg (g₂.1 x).1 _))] at this

end GlobalTheory.PMon.Gauss

end
end

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussNormAcris_logConvex_in_radius : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) (ρ₁ ρ₂ t : ℝ), (l : ℝ)⁻¹ ≤ ρ₁ → ρ₁ ≤ ρ₂ → ρ₂ < 1 → 0 ≤ t → t ≤ 1 → gC l (ρ₁ ^ t * ρ₂ ^ (1 - t)) x ≤ gC l ρ₁ x ^ t * gC l ρ₂ x ^ (1 - t) := by
  atlas_forward_decl GlobalTheory.PMon.Gauss.gC_logConvex
end

section
section
noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem log_interp (a b c : ℝ) (h : b - a ≠ 0) :
    a * ((b - c) / (b - a)) + b * (1 - (b - c) / (b - a)) = c := by
  field_simp
  ring

theorem gC_pos_of_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 → ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ →
    ρ < 1 → 0 < gC l ρ x := by
  intro l _ x hx ρ hρ0 hρ1
  have hN : ∀ r : ℝ, (l : ℝ)⁻¹ ≤ r → r < 1 → IsGauss l r (gC l r) :=
    fun r h0 h1 => isGauss_gC_target l r h0 h1
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hi0 : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hi1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  have hnn : ∀ r, (l : ℝ)⁻¹ ≤ r → r < 1 → 0 ≤ gC l r x := fun r h0 h1 => ((hN r h0 h1).1 x).1
  have h0 : gC l (l : ℝ)⁻¹ x ≠ 0 := GlobalTheory.MemLoc.gauss_ne_zero l (fun r => gC l r) hN x hx
  rcases hρ0.eq_or_lt with h | h
  · subst h
    exact lt_of_le_of_ne (hnn _ le_rfl hi1) h0.symm
  by_contra hneg
  have hz : gC l ρ x = 0 := le_antisymm (not_lt.1 hneg) (hnn ρ hρ0 hρ1)
  obtain ⟨r₁, c, k, hr₁, -, hc, hmon⟩ := GlobalTheory.MemLoc.gauss_slope l (fun r => gC l r) hN x h0
  obtain ⟨ρ', h1', h2'⟩ := exists_between (lt_min hr₁ h)
  have hρ'0 : 0 < ρ' := hi0.trans h1'
  have hρ'r : ρ' < r₁ := h2'.trans_le (min_le_left _ _)
  have hρ'ρ : ρ' < ρ := h2'.trans_le (min_le_right _ _)
  have hρpos : 0 < ρ := hi0.trans h
  have hpos : 0 < gC l ρ' x := by
    have e : gC l ρ' x = c * ρ' ^ k := hmon ρ' h1' hρ'r
    rw [e]
    exact mul_pos hc (zpow_pos hρ'0 k)
  have hL1 : Real.log (l : ℝ)⁻¹ < Real.log ρ' := Real.log_lt_log hi0 h1'
  have hL2 : Real.log ρ' < Real.log ρ := Real.log_lt_log hρ'0 hρ'ρ
  have hd : 0 < Real.log ρ - Real.log (l : ℝ)⁻¹ := by linarith
  have ht0 : 0 ≤ (Real.log ρ - Real.log ρ') / (Real.log ρ - Real.log (l : ℝ)⁻¹) :=
    div_nonneg (by linarith) hd.le
  have ht1 : (Real.log ρ - Real.log ρ') / (Real.log ρ - Real.log (l : ℝ)⁻¹) < 1 :=
    (div_lt_one hd).2 (by linarith)
  have he : (l : ℝ)⁻¹ ^ ((Real.log ρ - Real.log ρ') / (Real.log ρ - Real.log (l : ℝ)⁻¹)) *
      ρ ^ (1 - (Real.log ρ - Real.log ρ') / (Real.log ρ - Real.log (l : ℝ)⁻¹)) = ρ' := by
    rw [Real.rpow_def_of_pos hi0, Real.rpow_def_of_pos hρpos, ← Real.exp_add,
      log_interp _ _ _ hd.ne', Real.exp_log hρ'0]
  have hcv := GlobalTheory.T.gaussNormAcris_logConvex_in_radius l x (l : ℝ)⁻¹ ρ _ le_rfl h.le hρ1 ht0 ht1.le
  rw [he, hz, Real.zero_rpow (sub_pos.2 ht1).ne', mul_zero] at hcv
  linarith

theorem gC_pos_target : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 → ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 →
    0 < gC l ρ x :=
  gC_pos_of_ne_zero

end GlobalTheory.PMon.Gauss

end
end

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussNormAcrisRadius_pos_definite : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 → ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → 0 < gC l ρ x := by
  atlas_forward_decl GlobalTheory.PMon.Gauss.gC_pos_target
end
