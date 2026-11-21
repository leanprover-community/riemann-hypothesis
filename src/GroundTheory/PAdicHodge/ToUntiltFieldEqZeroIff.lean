import Mathlib
import GroundTheory.PAdicHodge.ExistsIsRootForallNormPowMulLe
import GroundTheory.PAdicHodge.ExtRobbaPointDiv
import GroundTheory.PAdicHodge.ExtRobbaUnits

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem lowIdx_zero {ρ0 : Set.Ioo (0 : ℝ) 1} (σ : ℝ) : T.lowIdx (0 : T.RobbaExt ρ0) σ = 0 := by
  simp [lowIdx]

theorem highIdx_zero {ρ0 : Set.Ioo (0 : ℝ) 1} (σ : ℝ) : T.highIdx (0 : T.RobbaExt ρ0) σ = 0 := by
  simp [highIdx]

theorem idx_res {ρ0 ρ1 : Set.Ioo (0 : ℝ) 1} (h : (ρ1 : ℝ) ≤ ρ0) (x : T.RobbaExt ρ0) {σ : ℝ}
    (hσ : 0 < σ ∧ σ < ρ1) :
    T.lowIdx (T.res h x) σ = T.lowIdx x σ ∧ T.highIdx (T.res h x) σ = T.highIdx x σ := by
  by_cases hx : x = 0
  · subst hx; rw [map_zero, lowIdx_zero, lowIdx_zero, highIdx_zero, highIdx_zero]; exact ⟨rfl, rfl⟩
  have hxr : T.res h x ≠ 0 := fun h0 => hx (T.res_injective h (h0.trans (map_zero _).symm))
  set η := ((ρ1 : ℝ) - σ) / 2 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith [hσ.2]
  have hη1 : σ + η ≤ ρ1 := by rw [hηdef]; linarith [hσ.2]
  have hη0 : σ + η ≤ ρ0 := hη1.trans h
  obtain ⟨c, hc⟩ := T.exists_approx_norm hx ⟨σ, hσ.1, (hσ.2.le.trans h)⟩
    ⟨σ + η, by linarith [hσ.1], hη0⟩ (show σ ≤ σ + η by linarith)
  have h1 := T.idx_eq_of_approx hx ⟨hσ.1, hσ.2.trans_le h⟩ hη hη0 hc
  have hc' : ∀ τ : Set.Ioc (0 : ℝ) ρ1, σ ≤ τ → (τ : ℝ) ≤ σ + η →
      T.extNorm ρ1 τ (T.res h x - ((T.incl h c : T.Econ ρ1) : T.RobbaExt ρ1)) <
        T.extNorm ρ1 τ (T.res h x) := by
    intro τ h1' h2'
    rw [← T.res_coe h c, ← map_sub, T.extNorm_res, T.extNorm_res]
    exact hc ⟨τ, τ.2.1, τ.2.2.trans h⟩ h1' h2'
  have h2 := T.idx_eq_of_approx hxr hσ hη hη1 hc'
  rw [h2.1, h2.2, h1.1, h1.2]
  exact ⟨rfl, rfl⟩

theorem mult_res {ρ0 ρ1 : Set.Ioo (0 : ℝ) 1} (h : (ρ1 : ℝ) ≤ ρ0) (x : T.RobbaExt ρ0) {σ : ℝ}
    (hσ : 0 < σ ∧ σ < ρ1) : T.mult (T.res h x) σ = T.mult x σ := by
  obtain ⟨h1, h2⟩ := T.idx_res h x hσ
  rw [mult, mult, h1, h2]

variable {ξ : T.int} (hξ : T.IsPrimOne ξ)

theorem ptEval_res {ρ0 ρ1 : Set.Ioo (0 : ℝ) 1} (h : (ρ1 : ℝ) ≤ ρ0) (hr1 : T.ptRad ξ ≤ ρ1)
    (x : T.RobbaExt ρ0) :
    T.ptEval hξ hr1 (T.res h x) = T.ptEval hξ (hr1.trans h) x :=
  Completion.induction_on x
    (isClosed_eq ((T.continuous_ptEval hξ hr1).comp (T.continuous_res h))
      (T.continuous_ptEval hξ _))
    fun b => by rw [T.res_coe, ptEval_coe, ptEval_coe]; rfl

theorem res_ξExt {ρ0 ρ1 : Set.Ioo (0 : ℝ) 1} (h : (ρ1 : ℝ) ≤ ρ0) :
    T.res h (T.ξExt ξ ρ0) = T.ξExt ξ ρ1 := by
  rw [ξExt, T.res_coe]; rfl

theorem idx_eq_of_domSet_singleton {a : ℤ → L} {ρ : ℝ} (hρ : 0 < ρ) (hc : ConvergesAt a ρ)
    (ha : a ≠ 0) {k : ℤ} (hk : k ∈ domSet a ρ) (huniq : ∀ n ∈ domSet a ρ, n = k) :
    lowIndex a ρ = k ∧ highIndex a ρ = k :=
  ⟨huniq _ (lowIndex_mem hρ hc ha), huniq _ (highIndex_mem hρ hc ha)⟩

include hξ in
theorem idx_zcoeff_prim {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    lowIndex (T.zcoeff (ξ : Γ)) σ = (if σ ≤ T.ptRad ξ then 0 else 1) ∧
      highIndex (T.zcoeff (ξ : Γ)) σ = (if σ < T.ptRad ξ then 0 else 1) := by
  set r := T.ptRad ξ with hrdef
  have hr0 : 0 < r := T.ptRad_pos' hξ
  have hc := T.convergesAt_of_mem_int ξ.2 hσ0 hσ1
  have hne : T.zcoeff (ξ : Γ) ≠ 0 := by
    intro h; have := congrFun h 0; rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, T.zcoeff_natCast] at this
    exact hξ.coeff_zero_ne this
  have hg : gaussNorm (T.zcoeff (ξ : Γ)) σ = max r σ := T.gaussNorm_prim hξ hσ0 hσ1
  have w0 : ‖T.zcoeff (ξ : Γ) 0‖ * σ ^ (0 : ℤ) = r := by
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, T.zcoeff_natCast]; simp [hrdef, ptRad]
  have w1 : ‖T.zcoeff (ξ : Γ) 1‖ * σ ^ (1 : ℤ) = σ := by
    rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, T.zcoeff_natCast, hξ.norm_coeff_one, one_mul,
      Nat.cast_one, zpow_one]
  have wlarge : ∀ n : ℤ, 2 ≤ n → ‖T.zcoeff (ξ : Γ) n‖ * σ ^ n < σ := by
    intro n hn
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ n by omega)
    rw [T.zcoeff_natCast, zpow_natCast]
    have hk : 2 ≤ k := by omega
    calc ‖T.coeff (ξ : Γ) k‖ * σ ^ k ≤ 1 * σ ^ k :=
          mul_le_mul_of_nonneg_right (T.norm_coeff_prim_le hξ k) (by positivity)
      _ < σ := by
          rw [one_mul]
          calc σ ^ k ≤ σ ^ 2 := pow_le_pow_of_le_one hσ0.le hσ1.le hk
            _ < σ := by nlinarith
  have wneg : ∀ n : ℤ, n < 0 → ‖T.zcoeff (ξ : Γ) n‖ * σ ^ n = 0 := fun n hn => by
    rw [T.zcoeff_of_neg _ hn, norm_zero, zero_mul]
  have hdom : ∀ n, n ∈ domSet (T.zcoeff (ξ : Γ)) σ ↔
      ‖T.zcoeff (ξ : Γ) n‖ * σ ^ n = max r σ := fun n => by
    simp only [domSet, Set.mem_setOf_eq, hg]
  rcases lt_trichotomy σ r with hlt | heq | hgt
  · have h0 : (0 : ℤ) ∈ domSet (T.zcoeff (ξ : Γ)) σ := by
      rw [hdom, w0, max_eq_left hlt.le]
    have hu : ∀ n ∈ domSet (T.zcoeff (ξ : Γ)) σ, n = 0 := by
      intro n hn
      rw [hdom, max_eq_left hlt.le] at hn
      by_contra hn0
      rcases lt_or_gt_of_ne hn0 with hneg | hpos
      · rw [wneg n hneg] at hn; linarith
      · rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | h2
        · rw [w1] at hn; linarith
        · have := wlarge n h2; linarith
    have := idx_eq_of_domSet_singleton hσ0 hc hne h0 hu
    rw [if_pos hlt.le, if_pos hlt]
    exact this
  · have hs := T.idx_prim_self hξ
    subst heq
    rw [if_pos le_rfl, if_neg (lt_irrefl _)]
    exact hs
  · have h1 : (1 : ℤ) ∈ domSet (T.zcoeff (ξ : Γ)) σ := by
      rw [hdom, w1, max_eq_right hgt.le]
    have hu : ∀ n ∈ domSet (T.zcoeff (ξ : Γ)) σ, n = 1 := by
      intro n hn
      rw [hdom, max_eq_right hgt.le] at hn
      by_contra hn1
      rcases (show n < 0 ∨ n = 0 ∨ 2 ≤ n by omega) with hneg | rfl | h2
      · rw [wneg n hneg] at hn; linarith
      · rw [w0] at hn; linarith
      · have := wlarge n h2; linarith
    have := idx_eq_of_domSet_singleton hσ0 hc hne h1 hu
    rw [if_neg (not_le.2 hgt), if_neg (not_lt.2 hgt.le)]
    exact this

variable {ρ0 : Set.Ioo (0 : ℝ) 1}

include hξ in
theorem ptExt_ne_zero : T.ξExt ξ ρ0 ≠ 0 := by
  intro h
  have := T.ptRad_le_extNorm_ξExt (ξ := ξ) (ρ0 := ρ0) (topRad ρ0)
  rw [h, extNorm_zero] at this
  exact absurd this (not_le.2 (T.ptRad_pos' hξ))

include hξ in
theorem idx_ptExt {σ : ℝ} (hσ : 0 < σ ∧ σ < ρ0) :
    T.lowIdx (T.ξExt ξ ρ0) σ = (if σ ≤ T.ptRad ξ then 0 else 1) ∧
      T.highIdx (T.ξExt ξ ρ0) σ = (if σ < T.ptRad ξ then 0 else 1) := by
  have h := T.idx_coe (b := ⟨algebraMap Γ T.B ξ, T.algebraMap_ξ_mem_Econ (ξ := ξ) ρ0⟩)
    (T.ptExt_ne_zero hξ) hσ
  rw [show ((⟨algebraMap Γ T.B ξ, T.algebraMap_ξ_mem_Econ (ξ := ξ) ρ0⟩ : T.Econ ρ0) :
    T.RobbaExt ρ0) = T.ξExt ξ ρ0 from rfl] at h
  rw [h.1, h.2]
  show lowIndex (T.coeffB (algebraMap Γ T.B ξ)) σ = _ ∧ highIndex (T.coeffB (algebraMap Γ T.B ξ)) σ = _
  rw [coeffB_algebraMap]
  exact T.idx_zcoeff_prim hξ hσ.1 (hσ.2.trans ρ0.2.2)

include hξ in
theorem mult_ptExt {σ : ℝ} (hσ : 0 < σ ∧ σ < ρ0) :
    T.mult (T.ξExt ξ ρ0) σ = if σ = T.ptRad ξ then 1 else 0 := by
  obtain ⟨h1, h2⟩ := T.idx_ptExt hξ hσ
  rw [mult, h1, h2]
  rcases lt_trichotomy σ (T.ptRad ξ) with hlt | heq | hgt
  · rw [if_pos hlt.le, if_pos hlt, if_neg hlt.ne]; rfl
  · rw [if_pos heq.le, if_neg (lt_irrefl _ ∘ (heq ▸ ·)), if_pos heq]; rfl
  · rw [if_neg (not_le.2 hgt), if_neg (not_lt.2 hgt.le), if_neg hgt.ne']; rfl

def vInv : T.int := ↑((T.isUnit_ξtail hξ).unit⁻¹)

theorem ξtail_mul_vInv : (T.ξtail ξ : Γ) * (T.vInv hξ : Γ) = 1 := by
  have := (T.isUnit_ξtail hξ).mul_val_inv
  exact congrArg Subtype.val this

theorem norm_red_vInv : ‖T.red (T.vInv hξ : Γ)‖ = 1 := by
  have h1 := congrArg T.red (T.ξtail_mul_vInv hξ)
  rw [map_mul, map_one] at h1
  have hV := T.norm_red_le_one _ (T.ξtail ξ).2
  have hW := T.norm_red_le_one _ (T.vInv hξ).2
  have hprod := congrArg norm h1
  rw [norm_mul, norm_one] at hprod
  refine le_antisymm hW ?_
  nlinarith [norm_nonneg (T.red (T.ξtail ξ : Γ)), norm_nonneg (T.red (T.vInv hξ : Γ))]

def normU : Γ := T.teich (T.coeff (ξ : Γ) 0) * (T.vInv hξ : Γ)

theorem normU_mem_int : T.normU hξ ∈ T.int :=
  T.int.mul_mem (T.teich_mem_int (T.norm_coeff_prim_le hξ 0)) (T.vInv hξ).2

theorem gaussNorm_normU {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    gaussNorm (T.zcoeff (T.normU hξ)) ρ = T.ptRad ξ := by
  rw [normU, T.gaussNorm_zcoeff_mul hρ0 hρ1 (T.convergesAt_teich _ ρ)
    (T.convergesAt_of_mem_int (T.vInv hξ).2 hρ0 hρ1), T.gaussNorm_teich _ hρ0,
    T.gaussNorm_eq_one_of_mem_int (T.vInv hξ).2 (T.norm_red_vInv hξ) hρ0 hρ1, mul_one]
  rfl

def normPt : T.B := 1 + algebraMap Γ T.B (T.normU hξ) * IsLocalization.Away.invSelf T.π

theorem normPt_eq : T.normPt hξ =
    algebraMap Γ T.B ξ * algebraMap Γ T.B (T.vInv hξ) * IsLocalization.Away.invSelf T.π := by
  have hξe := T.coe_eq_teich_add ξ
  have hinv := IsLocalization.Away.mul_invSelf (S := T.B) T.π
  have hV := congrArg (algebraMap Γ T.B) (T.ξtail_mul_vInv hξ)
  rw [map_mul, map_one] at hV
  rw [normPt, normU]
  generalize T.coeff (ξ : Γ) 0 = c0 at hξe ⊢
  rw [hξe]
  simp only [map_add, map_mul]
  linear_combination (-(algebraMap Γ T.B (T.ξtail ξ : Γ) * algebraMap Γ T.B (T.vInv hξ : Γ)) *
    hinv - hV)

theorem algebraMap_int_mem_Econ {x : Γ} (hx : x ∈ T.int) (ρ : Set.Ioo (0 : ℝ) 1) :
    algebraMap Γ T.B x ∈ T.Econ ρ := by
  rw [mem_Econ, coeffB_algebraMap]
  exact T.convergesAt_of_mem_int hx ρ.2.1 ρ.2.2

theorem normPt_mem_Econ (ρ : Set.Ioo (0 : ℝ) 1) : T.normPt hξ ∈ T.Econ ρ :=
  (T.Econ ρ).add_mem (T.Econ ρ).one_mem
    ((T.Econ ρ).mul_mem (T.algebraMap_int_mem_Econ (T.normU_mem_int hξ) ρ) (T.invSelf_mem_Econ ρ))

def normPtExt (ρ0 : Set.Ioo (0 : ℝ) 1) : T.RobbaExt ρ0 :=
  ((⟨T.normPt hξ, T.normPt_mem_Econ hξ ρ0⟩ : T.Econ ρ0) : T.RobbaExt ρ0)

def normUnit (ρ0 : Set.Ioo (0 : ℝ) 1) : T.RobbaExt ρ0 :=
  ((⟨algebraMap Γ T.B (T.vInv hξ) * IsLocalization.Away.invSelf T.π,
    (T.Econ ρ0).mul_mem (T.algebraMap_int_mem_Econ (T.vInv hξ).2 ρ0) (T.invSelf_mem_Econ ρ0)⟩ :
      T.Econ ρ0) : T.RobbaExt ρ0)

def normUnitInv (ρ0 : Set.Ioo (0 : ℝ) 1) : T.RobbaExt ρ0 :=
  ((⟨algebraMap Γ T.B (T.ξtail ξ) * algebraMap Γ T.B T.π,
    (T.Econ ρ0).mul_mem (T.algebraMap_int_mem_Econ (T.ξtail ξ).2 ρ0) (T.algebraMap_π_mem_Econ ρ0)⟩ :
      T.Econ ρ0) : T.RobbaExt ρ0)

theorem normUnit_mul_inv (ρ0 : Set.Ioo (0 : ℝ) 1) : T.normUnit hξ ρ0 * T.normUnitInv (ξ := ξ) ρ0 = 1 := by
  rw [normUnit, normUnitInv, ← Completion.coe_mul, ← Completion.coe_one]
  congr 1
  apply Subtype.ext
  have hinv := IsLocalization.Away.mul_invSelf (S := T.B) T.π
  have hV := congrArg (algebraMap Γ T.B) (T.ξtail_mul_vInv hξ)
  rw [map_mul, map_one] at hV
  show algebraMap Γ T.B (T.vInv hξ) * IsLocalization.Away.invSelf T.π *
    (algebraMap Γ T.B (T.ξtail ξ) * algebraMap Γ T.B T.π) = 1
  linear_combination (algebraMap Γ T.B (T.ξtail ξ : Γ) * algebraMap Γ T.B (T.vInv hξ : Γ)) * hinv +
    hV

theorem normPtExt_eq (ρ0 : Set.Ioo (0 : ℝ) 1) :
    T.normPtExt hξ ρ0 = T.ξExt ξ ρ0 * T.normUnit hξ ρ0 := by
  rw [normPtExt, ξExt, normUnit, ← Completion.coe_mul]
  congr 1
  apply Subtype.ext
  show T.normPt hξ = algebraMap Γ T.B ξ * (algebraMap Γ T.B (T.vInv hξ) *
    IsLocalization.Away.invSelf T.π)
  rw [normPt_eq, mul_assoc]

theorem ξExt_eq_normPtExt (ρ0 : Set.Ioo (0 : ℝ) 1) :
    T.ξExt ξ ρ0 = T.normPtExt hξ ρ0 * T.normUnitInv (ξ := ξ) ρ0 := by
  rw [normPtExt_eq, mul_assoc, normUnit_mul_inv, mul_one]

theorem dvd_ξExt_iff_normPtExt {ρ0 : Set.Ioo (0 : ℝ) 1} (x : T.RobbaExt ρ0) :
    T.ξExt ξ ρ0 ∣ x ↔ T.normPtExt hξ ρ0 ∣ x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨T.normUnitInv (ξ := ξ) ρ0 * y, by rw [ξExt_eq_normPtExt, mul_assoc]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨T.normUnit hξ ρ0 * y, by rw [normPtExt_eq, mul_assoc]⟩

theorem extNorm_normPtExt_sub_one {ρ0 : Set.Ioo (0 : ℝ) 1} (ρ : Set.Ioc (0 : ℝ) ρ0) :
    T.extNorm ρ0 ρ (T.normPtExt hξ ρ0 - 1) = T.ptRad ξ / ρ := by
  rw [normPtExt, ← Completion.coe_one, ← Completion.coe_sub, extNorm_coe]
  show gaussNorm (T.coeffB (T.normPt hξ - 1)) ρ = _
  rw [normPt, add_sub_cancel_left]
  have hρ0 := rad_pos ρ0 ρ
  have hρ1 := rad_lt_one ρ0 ρ
  rw [(T.convergesAt_coeffB_mul hρ0 hρ1
    (T.algebraMap_int_mem_Econ (T.normU_mem_int hξ) ⟨ρ, hρ0, hρ1⟩)
    (T.invSelf_mem_Econ ⟨ρ, hρ0, hρ1⟩)).2, coeffB_algebraMap, T.gaussNorm_normU hξ hρ0 hρ1,
    coeffB_invSelf, gaussNorm_pi_single _ _ hρ0, norm_one, one_mul, zpow_neg, zpow_one, div_eq_mul_inv]

include hξ in
theorem extNorm_ptExt {ρ0 : Set.Ioo (0 : ℝ) 1} (ρ : Set.Ioc (0 : ℝ) ρ0) :
    T.extNorm ρ0 ρ (T.ξExt ξ ρ0) = max (T.ptRad ξ) ρ := by
  rw [ξExt, extNorm_coe]
  show gaussNorm (T.coeffB (algebraMap Γ T.B ξ)) ρ = _
  rw [coeffB_algebraMap, T.gaussNorm_prim hξ (rad_pos ρ0 ρ) (rad_lt_one ρ0 ρ)]
  rfl

theorem extNorm_normUnit {ρ0 : Set.Ioo (0 : ℝ) 1} (ρ : Set.Ioc (0 : ℝ) ρ0) :
    T.extNorm ρ0 ρ (T.normUnit hξ ρ0) = (ρ : ℝ)⁻¹ := by
  rw [normUnit, extNorm_coe]
  have hρ0 := rad_pos ρ0 ρ
  have hρ1 := rad_lt_one ρ0 ρ
  show gaussNorm (T.coeffB (algebraMap Γ T.B (T.vInv hξ) * IsLocalization.Away.invSelf T.π)) ρ = _
  rw [(T.convergesAt_coeffB_mul hρ0 hρ1
    (T.algebraMap_int_mem_Econ (T.vInv hξ).2 ⟨ρ, hρ0, hρ1⟩)
    (T.invSelf_mem_Econ ⟨ρ, hρ0, hρ1⟩)).2, coeffB_algebraMap,
    T.gaussNorm_eq_one_of_mem_int (T.vInv hξ).2 (T.norm_red_vInv hξ) hρ0 hρ1, one_mul,
    coeffB_invSelf, gaussNorm_pi_single _ _ hρ0, norm_one, one_mul, zpow_neg, zpow_one]

theorem extNorm_normPtExt {ρ0 : Set.Ioo (0 : ℝ) 1} (ρ : Set.Ioc (0 : ℝ) ρ0) :
    T.extNorm ρ0 ρ (T.normPtExt hξ ρ0) = max 1 (T.ptRad ξ / ρ) := by
  rw [normPtExt_eq, extNorm_mul, T.extNorm_ptExt hξ, T.extNorm_normUnit hξ]
  have hρ0 := rad_pos ρ0 ρ
  rw [← div_eq_mul_inv, ← max_div_div_right hρ0.le, div_self hρ0.ne', max_comm]

theorem lowIdx_const_of_mult_zero {x : T.RobbaExt ρ0} (hx : x ≠ 0)
    (h : ∀ σ : ℝ, 0 < σ → σ < ρ0 → T.mult x σ = 0) {ρ ρ1 : ℝ} (hρ : 0 < ρ) (hρρ1 : ρ ≤ ρ1)
    (hρ1 : ρ1 < ρ0) : T.lowIdx x ρ = T.lowIdx x ρ1 := by
  have hs := T.sum_mult_breaksR hx hρ hρρ1 hρ1
  have h0 : ∑ σ ∈ (T.breaksR_finite hx hρ hρρ1 hρ1).toFinset, T.mult x σ = 0 :=
    Finset.sum_eq_zero fun σ hσ => by
      simp only [Set.Finite.mem_toFinset, breaksR, Set.mem_setOf_eq] at hσ
      exact h σ (hρ.trans_le hσ.1.1) (hσ.1.2.trans_lt hρ1)
  have hm1 := h ρ1 (hρ.trans_le hρρ1) hρ1
  rw [mult] at hm1
  rw [h0] at hs
  omega

theorem normR_eq_of_mult_zero {x : T.RobbaExt ρ0} (hx : x ≠ 0)
    (h : ∀ σ : ℝ, 0 < σ → σ < ρ0 → T.mult x σ = 0) {ρ ρ1 : ℝ} (hρ : 0 < ρ) (hρρ1 : ρ ≤ ρ1)
    (hρ1 : ρ1 < ρ0) : T.normR x ρ = T.normR x ρ1 * (ρ / ρ1) ^ T.lowIdx x ρ1 := by
  set ρ2 := (ρ1 + (ρ0 : ℝ)) / 2 with hρ2
  have hρ2a : ρ1 < ρ2 := by rw [hρ2]; linarith
  have hρ2b : ρ2 ≤ ρ0 := by rw [hρ2]; linarith
  have hρ1pos : 0 < ρ1 := hρ.trans_le hρρ1
  obtain ⟨c, hc⟩ := T.exists_approx_norm hx ⟨ρ, hρ, (hρρ1.trans hρ1.le)⟩
    ⟨ρ2, by linarith, hρ2b⟩ (show ρ ≤ ρ2 by linarith)
  have key : ∀ σ : ℝ, ρ ≤ σ → σ ≤ ρ1 → T.normR x σ =
      ‖T.coeffB c (T.lowIdx x σ)‖ * σ ^ T.lowIdx x σ := by
    intro σ h1 h2
    have hσ0 : 0 < σ := hρ.trans_le h1
    set s : Set.Ioc (0 : ℝ) ρ0 := ⟨σ, hσ0, (h2.trans hρ1.le)⟩
    have hcs := hc s h1 (by show σ ≤ ρ2; linarith)
    have hidx := T.idx_eq_of_approx hx ⟨hσ0, h2.trans_lt hρ1⟩ (η := ρ2 - σ) (by linarith)
      (by linarith) fun τ hτ1 hτ2 => hc τ (h1.trans hτ1) (by linarith)
    have hc0 : T.coeffB c ≠ 0 := by
      intro h0
      have := T.coe_ne_zero_of_approx hcs
      obtain ⟨N, y, hy⟩ := IsLocalization.Away.surj T.π (c : T.B)
      have hy0 : y ≠ 0 := by rintro rfl; exact this (T.eq_zero_of_mul_pow (by rw [hy, map_zero]))
      rw [T.coeffB_eq hy] at h0
      apply hy0
      refine (T.zcoeff_eq_zero_iff y).1 (funext fun k => ?_)
      have := congrFun h0 (k - N)
      simpa using this
    rw [T.normR_eq x s, ← T.extNorm_eq_of_lt hcs, extNorm_coe, hidx.1]
    exact (lowIndex_mem hσ0 (T.convergesAt_rad ρ0 c s) hc0).symm
  have hconst := T.lowIdx_const_of_mult_zero hx h hρ hρρ1 hρ1
  rw [key ρ le_rfl hρρ1, key ρ1 hρρ1 le_rfl, hconst, div_zpow, mul_assoc,
    mul_div_assoc', mul_div_cancel_left₀ _ (zpow_pos hρ1pos _).ne']

variable [CompleteSpace L]

theorem isUnit_ofRad_of_mult_eq_zero {x : T.RobbaExt ρ0} (hx : x ≠ 0)
    (h : ∀ σ : ℝ, 0 < σ → σ < ρ0 → T.mult x σ = 0) : IsUnit (T.ofRad ρ0 x) := by
  set ρ1 := halfRad ρ0 with hρ1def
  have hρ1v : (ρ1 : ℝ) = ρ0 / 2 := rfl
  have hρ1lt : (ρ1 : ℝ) < ρ0 := by rw [hρ1v]; linarith [ρ0.2.1]
  have hρ1pos : (0 : ℝ) < ρ1 := ρ1.2.1
  set n := T.lowIdx x ρ1 with hndef
  set x1 := T.res (halfRad_le ρ0) x with hx1
  set w : T.RobbaExt ρ1 :=
    if 0 ≤ n then T.πInvExt ρ1 ^ n.toNat else T.πExt ρ1 ^ (-n).toNat with hwdef
  set wi : T.RobbaExt ρ1 :=
    if 0 ≤ n then T.πExt ρ1 ^ n.toNat else T.πInvExt ρ1 ^ (-n).toNat with hwidef
  have hwwi : w * wi = 1 := by
    rw [hwdef, hwidef]
    split_ifs
    · rw [← mul_pow, mul_comm, T.πExt_mul_πInvExt, one_pow]
    · rw [← mul_pow, T.πExt_mul_πInvExt, one_pow]
  have hNw : ∀ σ : Set.Ioc (0 : ℝ) ρ1, T.extNorm ρ1 σ w = (σ : ℝ) ^ (-n) := by
    intro σ
    have hσ := rad_pos ρ1 σ
    rw [hwdef]
    split_ifs with hn
    · rw [extNorm_pow, extNorm_πInvExt, inv_pow, ← zpow_natCast, Int.toNat_of_nonneg hn, zpow_neg]
    · rw [extNorm_pow, extNorm_πExt, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]
  set C := T.normR x ρ1 * (ρ1 : ℝ) ^ (-n) with hC
  have hC0 : 0 ≤ C := by
    rw [hC, T.normR_eq x ⟨ρ1, hρ1pos, hρ1lt.le⟩]
    exact mul_nonneg (T.extNorm_nonneg _ _) (zpow_pos hρ1pos _).le
  have hz : ∀ σ : Set.Ioc (0 : ℝ) ρ1, T.extNorm ρ1 σ (x1 * w) = C := by
    intro σ
    have hσ := rad_pos ρ1 σ
    rw [extNorm_mul, hNw, hx1, T.extNorm_res, ← T.normR_eq x,
      T.normR_eq_of_mult_zero hx h hσ σ.2.2 hρ1lt, hC, div_zpow, zpow_neg, zpow_neg]
    field_simp
    rw [← hndef]; ring
  obtain ⟨X, hX, hres⟩ := T.exists_gamma_of_bounded hC0 (fun σ => (hz σ).le)
  have hmem : T.ofRad ρ1 (x1 * w) ∈ T.edagToTilde.range := by
    refine ⟨⟨algebraMap Γ T.B X, T.Econ_le_Edag _ hX⟩, ?_⟩
    rw [T.edagToTilde_apply hX]
    show T.ofRad (halfRad ρ1) (((⟨algebraMap Γ T.B X, hX⟩ : T.Econ (halfRad ρ1))) :
      T.RobbaExt (halfRad ρ1)) = T.ofRad ρ1 (x1 * w)
    rw [← hres, T.ofRad_res]
  have hx10 : x1 ≠ 0 := fun h0 => hx (T.res_injective _ (h0.trans (map_zero _).symm))
  have hw0 : w ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hwwi; exact zero_ne_one hwwi
  have hz0 : T.ofRad ρ1 (x1 * w) ≠ 0 := by
    intro h0
    exact mul_ne_zero hx10 hw0 (T.ofRad_injective ρ1 (h0.trans (map_zero _).symm))
  have hu := (T.isUnit_iff _).2 ⟨hz0, hmem⟩
  have hx' : T.ofRad ρ0 x = T.ofRad ρ1 (x1 * w) * T.ofRad ρ1 wi := by
    rw [← map_mul, mul_assoc, hwwi, mul_one, hx1, T.ofRad_res]
  rw [hx']
  refine hu.mul (IsUnit.of_mul_eq_one (T.ofRad ρ1 w) ?_)
  rw [← map_mul, mul_comm, hwwi, map_one]

end TeichLift

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

def RootExists : Prop :=
  ∀ (ρ0 : Set.Ioo (0 : ℝ) 1) (x : T.RobbaExt ρ0), x ≠ 0 → ∀ r : ℝ, 0 < r → r < ρ0 →
    1 ≤ T.mult x r → ∃ (ξ : T.int) (hξ : T.IsPrimOne ξ), T.ptRad ξ = r ∧ ∃ y, x = T.ξExt ξ ρ0 * y

abbrev Pt := {ξ : T.int // T.IsPrimOne ξ}

variable {ρ0 : Set.Ioo (0 : ℝ) 1}

def ptProd (ρ0 : Set.Ioo (0 : ℝ) 1) (l : List T.Pt) : T.RobbaExt ρ0 :=
  (l.map fun P => T.ξExt P.1 ρ0).prod

theorem ptProd_nil : T.ptProd ρ0 [] = 1 := rfl

theorem ptProd_cons (P : T.Pt) (l : List T.Pt) :
    T.ptProd ρ0 (P :: l) = T.ξExt P.1 ρ0 * T.ptProd ρ0 l := by
  simp [ptProd]

theorem ptProd_ne_zero (l : List T.Pt) : T.ptProd ρ0 l ≠ 0 := by
  induction l with
  | nil => exact one_ne_zero
  | cons P l ih => rw [ptProd_cons]; exact mul_ne_zero (T.ptExt_ne_zero P.2) ih

theorem mult_sum_nonneg {x : T.RobbaExt ρ0} (hx : x ≠ 0) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < ρ0) : 0 ≤ T.highIdx x b - T.lowIdx x a := by
  rw [← T.sum_mult_breaksR hx ha hab hb]
  exact Finset.sum_nonneg fun σ _ => T.mult_nonneg x σ

theorem exists_factor_annulus (hRE : T.RootExists) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < ρ0) :
    ∀ {x : T.RobbaExt ρ0}, x ≠ 0 → ∃ (l : List T.Pt) (y : T.RobbaExt ρ0),
      (∀ P ∈ l, a ≤ T.ptRad P.1 ∧ T.ptRad P.1 ≤ b) ∧ x = T.ptProd ρ0 l * y ∧ y ≠ 0 ∧
        ∀ σ, a ≤ σ → σ ≤ b → T.mult y σ = 0 := by
  suffices H : ∀ M : ℕ, ∀ x : T.RobbaExt ρ0, x ≠ 0 → T.highIdx x b - T.lowIdx x a = M →
      ∃ (l : List T.Pt) (y : T.RobbaExt ρ0),
        (∀ P ∈ l, a ≤ T.ptRad P.1 ∧ T.ptRad P.1 ≤ b) ∧ x = T.ptProd ρ0 l * y ∧ y ≠ 0 ∧
          ∀ σ, a ≤ σ → σ ≤ b → T.mult y σ = 0 by
    intro x hx
    exact H _ x hx (Int.toNat_of_nonneg (T.mult_sum_nonneg hx ha hab hb)).symm
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
  intro x hx hM
  by_cases hz : ∀ σ, a ≤ σ → σ ≤ b → T.mult x σ = 0
  · exact ⟨[], x, by simp, by rw [ptProd_nil, one_mul], hx, hz⟩
  push_neg at hz
  obtain ⟨σ, hσa, hσb, hσm⟩ := hz
  have hσ1 : 1 ≤ T.mult x σ := by
    have := T.mult_nonneg x σ
    omega
  obtain ⟨ξ, hξ, hr, y', hxy⟩ := hRE ρ0 x hx σ (ha.trans_le hσa) (hσb.trans_lt hb) hσ1
  have hy'0 : y' ≠ 0 := by rintro rfl; rw [mul_zero] at hxy; exact hx hxy
  have hξ0 := T.ptExt_ne_zero (ρ0 := ρ0) hξ
  have hia := T.idx_mul hξ0 hy'0 ⟨ha, hab.trans_lt hb⟩
  have hib := T.idx_mul hξ0 hy'0 ⟨ha.trans_le hab, hb⟩
  have hla := (T.idx_ptExt (ρ0 := ρ0) hξ ⟨ha, hab.trans_lt hb⟩).1
  have hhb := (T.idx_ptExt (ρ0 := ρ0) hξ ⟨ha.trans_le hab, hb⟩).2
  rw [if_pos (hr ▸ hσa)] at hla
  rw [if_neg (not_lt.2 (hr ▸ hσb))] at hhb
  rw [← hxy] at hia hib
  have hM' : T.highIdx y' b - T.lowIdx y' a = (M - 1 : ℕ) := by
    have hnn := T.mult_sum_nonneg hy'0 ha hab hb
    have : T.highIdx y' b - T.lowIdx y' a + 1 = M := by
      rw [← hM, hib.2, hia.1, hla, hhb]; ring
    omega
  have hMpos : 0 < M := by
    have hnn := T.mult_sum_nonneg hy'0 ha hab hb
    have : T.highIdx y' b - T.lowIdx y' a + 1 = M := by
      rw [← hM, hib.2, hia.1, hla, hhb]; ring
    omega
  obtain ⟨l, y, hl, hy'e, hy0, hym⟩ := ih (M - 1) (by omega) y' hy'0 hM'
  refine ⟨⟨ξ, hξ⟩ :: l, y, ?_, ?_, hy0, hym⟩
  · intro P hP
    rcases List.mem_cons.1 hP with rfl | hP
    · exact ⟨hr ▸ hσa, hr ▸ hσb⟩
    · exact hl P hP
  · rw [ptProd_cons, hxy, hy'e, mul_assoc]

theorem cauchySeq_of_increments {z : ℕ → T.RobbaExt ρ0}
    (h : ∀ ρ, Tendsto (fun n => T.extNorm ρ0 ρ (z (n + 1) - z n)) atTop (𝓝 0)) :
    CauchySeq z := by
  refine T.cauchySeq_of_extNorm fun ρ ε hε => ?_
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.1 (h ρ)) ε hε
  have hinc : ∀ n ≥ J, T.extNorm ρ0 ρ (z (n + 1) - z n) < ε := fun n hn => by
    have := hJ n hn
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (T.extNorm_nonneg _ _)] at this
  have key : ∀ k ≥ J, ∀ j, T.extNorm ρ0 ρ (z (k + j) - z k) < ε := by
    intro k hk j
    induction j with
    | zero => rw [add_zero, sub_self, extNorm_zero]; exact hε
    | succ j ih =>
      have := T.extNorm_add_le ρ (z (k + j + 1) - z (k + j)) (z (k + j) - z k)
      rw [sub_add_sub_cancel] at this
      exact this.trans_lt (max_lt (hinc _ (by omega)) ih)
  refine ⟨J, fun j hj k hk => ?_⟩
  rcases le_total k j with hkj | hjk
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hkj
    exact key k hk i
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hjk
    rw [extNorm_sub_comm]
    exact key j hj i

structure InfProd (ρ0 : Set.Ioo (0 : ℝ) 1) where

  g : ℕ → T.RobbaExt ρ0
  one_le_norm : ∀ n ρ, 1 ≤ T.extNorm ρ0 ρ (g n)
  tendsto_sub_one : ∀ ρ, Tendsto (fun n => T.extNorm ρ0 ρ (g n - 1)) atTop (𝓝 0)

namespace InfProd

variable {T} (F : T.InfProd ρ0)

def part (n : ℕ) : T.RobbaExt ρ0 := ∏ i ∈ Finset.range n, F.g i

theorem part_zero : F.part 0 = 1 := by simp [part]

theorem part_succ (n : ℕ) : F.part (n + 1) = F.part n * F.g n := by
  simp [part, Finset.prod_range_succ]

theorem one_le_norm_part (n : ℕ) (ρ : Set.Ioc (0 : ℝ) ρ0) : 1 ≤ T.extNorm ρ0 ρ (F.part n) := by
  induction n with
  | zero => rw [part_zero, extNorm_one]
  | succ n ih =>
    rw [part_succ, extNorm_mul]
    exact one_le_mul_of_one_le_of_one_le ih (F.one_le_norm n ρ)

theorem part_ne_zero (n : ℕ) : F.part n ≠ 0 := by
  intro h
  have := F.one_le_norm_part n (topRad ρ0)
  rw [h, extNorm_zero] at this
  linarith

theorem eventually_norm_eq_one (ρ : Set.Ioc (0 : ℝ) ρ0) :
    ∀ᶠ n in atTop, T.extNorm ρ0 ρ (F.g n) = 1 := by
  filter_upwards [(F.tendsto_sub_one ρ).eventually (gt_mem_nhds one_pos)] with n hn
  refine le_antisymm ?_ (F.one_le_norm n ρ)
  have := T.extNorm_add_le ρ (F.g n - 1) 1
  rw [sub_add_cancel, extNorm_one] at this
  exact this.trans (max_le hn.le le_rfl)

theorem exists_bound (ρ : Set.Ioc (0 : ℝ) ρ0) : ∃ B, ∀ n, T.extNorm ρ0 ρ (F.part n) ≤ B := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (F.eventually_norm_eq_one ρ)
  refine ⟨T.extNorm ρ0 ρ (F.part N), fun n => ?_⟩
  have mono : ∀ k, T.extNorm ρ0 ρ (F.part k) ≤ T.extNorm ρ0 ρ (F.part (k + 1)) := fun k => by
    rw [part_succ, extNorm_mul]
    exact le_mul_of_one_le_right (T.extNorm_nonneg _ _) (F.one_le_norm k ρ)
  have stab : ∀ j, T.extNorm ρ0 ρ (F.part (N + j)) = T.extNorm ρ0 ρ (F.part N) := fun j => by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [← add_assoc, part_succ, extNorm_mul, hN (N + j) (by omega), mul_one, ih]
  have monoLe : ∀ a b, a ≤ b → T.extNorm ρ0 ρ (F.part a) ≤ T.extNorm ρ0 ρ (F.part b) := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b _ ih => exact ih.trans (mono b)
  rcases le_total n N with h | h
  · exact monoLe n N h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [stab]

theorem cauchySeq_part : CauchySeq F.part := by
  refine T.cauchySeq_of_increments fun ρ => ?_
  obtain ⟨B, hB⟩ := F.exists_bound ρ
  have hB0 : 0 ≤ B := (T.extNorm_nonneg _ _).trans (hB 0)
  have hmul := (F.tendsto_sub_one ρ).const_mul B
  rw [mul_zero] at hmul
  refine squeeze_zero (fun n => T.extNorm_nonneg _ _) (fun n => ?_) hmul
  rw [part_succ, show F.part n * F.g n - F.part n = F.part n * (F.g n - 1) by ring, extNorm_mul]
  exact mul_le_mul_of_nonneg_right (hB n) (T.extNorm_nonneg _ _)

def prod : T.RobbaExt ρ0 := Classical.choose (cauchySeq_tendsto_of_complete F.cauchySeq_part)

theorem tendsto_part : Tendsto F.part atTop (𝓝 F.prod) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete F.cauchySeq_part)

theorem one_le_norm_prod (ρ : Set.Ioc (0 : ℝ) ρ0) : 1 ≤ T.extNorm ρ0 ρ F.prod :=
  ge_of_tendsto (((T.continuous_extNorm ρ).tendsto _).comp F.tendsto_part)
    (Eventually.of_forall fun n => F.one_le_norm_part n ρ)

theorem prod_ne_zero : F.prod ≠ 0 := by
  intro h
  have := F.one_le_norm_prod (topRad ρ0)
  rw [h, extNorm_zero] at this
  linarith

theorem dvd_of_forall {x : T.RobbaExt ρ0} (h : ∀ n, F.part n ∣ x) : F.prod ∣ x := by
  choose y hy using h
  have hstep : ∀ n, y n = F.g n * y (n + 1) := fun n => by
    have e : F.part n * y n = F.part n * (F.g n * y (n + 1)) := by
      rw [← hy n, hy (n + 1), part_succ, mul_assoc]
    exact mul_left_cancel₀ (F.part_ne_zero n) e
  have hyb : ∀ n (ρ : Set.Ioc (0 : ℝ) ρ0), T.extNorm ρ0 ρ (y n) ≤ T.extNorm ρ0 ρ x := fun n ρ => by
    have e := congrArg (T.extNorm ρ0 ρ) (hy n)
    rw [extNorm_mul] at e
    rw [e]
    exact le_mul_of_one_le_left (T.extNorm_nonneg _ _) (F.one_le_norm_part n ρ)
  have hc : CauchySeq y := by
    refine T.cauchySeq_of_increments fun ρ => ?_
    have hmul := (F.tendsto_sub_one ρ).const_mul (T.extNorm ρ0 ρ x)
    rw [mul_zero] at hmul
    refine squeeze_zero (fun n => T.extNorm_nonneg _ _) (fun n => ?_) hmul
    rw [hstep n, show y (n + 1) - F.g n * y (n + 1) = -((F.g n - 1) * y (n + 1)) by ring,
      extNorm_neg, extNorm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hyb _ ρ) (T.extNorm_nonneg _ _)
  obtain ⟨yl, hyl⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨yl, ?_⟩
  have hlim : Tendsto (fun n => F.part n * y n) atTop (𝓝 (F.prod * yl)) :=
    F.tendsto_part.mul hyl
  have hconst : (fun n => F.part n * y n) = fun _ => x := funext fun n => (hy n).symm
  rw [hconst] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

def shift (k : ℕ) : T.InfProd ρ0 where
  g n := F.g (k + n)
  one_le_norm n ρ := F.one_le_norm (k + n) ρ
  tendsto_sub_one ρ := (F.tendsto_sub_one ρ).comp (tendsto_atTop_atTop_of_monotone
    (fun _ _ h => by omega) fun n => ⟨n, by omega⟩)

theorem part_add (k n : ℕ) : F.part (k + n) = F.part k * (F.shift k).part n := by
  simp only [part, shift]
  rw [Finset.prod_range_add]

theorem prod_eq_part_mul_shift (k : ℕ) : F.prod = F.part k * (F.shift k).prod := by
  have h1 : Tendsto (fun n => F.part (k + n)) atTop (𝓝 F.prod) :=
    F.tendsto_part.comp (tendsto_atTop_atTop_of_monotone (fun _ _ h => by omega)
      fun n => ⟨n, by omega⟩)
  have h2 : Tendsto (fun n => F.part k * (F.shift k).part n) atTop
      (𝓝 (F.part k * (F.shift k).prod)) := tendsto_const_nhds.mul (F.shift k).tendsto_part
  have e : (fun n => F.part (k + n)) = fun n => F.part k * (F.shift k).part n :=
    funext fun n => F.part_add k n
  rw [e] at h1
  exact tendsto_nhds_unique h1 h2

theorem part_dvd_prod (k : ℕ) : F.part k ∣ F.prod := ⟨_, F.prod_eq_part_mul_shift k⟩

end InfProd

def normProd (ρ0 : Set.Ioo (0 : ℝ) 1) (l : List T.Pt) : T.RobbaExt ρ0 :=
  (l.map fun P => T.normPtExt P.2 ρ0).prod

theorem normProd_nil : T.normProd ρ0 [] = 1 := rfl

theorem normProd_cons (P : T.Pt) (l : List T.Pt) :
    T.normProd ρ0 (P :: l) = T.normPtExt P.2 ρ0 * T.normProd ρ0 l := by
  simp [normProd]

theorem normProd_append (l l' : List T.Pt) :
    T.normProd ρ0 (l ++ l') = T.normProd ρ0 l * T.normProd ρ0 l' := by
  simp [normProd]

theorem ptProd_append (l l' : List T.Pt) :
    T.ptProd ρ0 (l ++ l') = T.ptProd ρ0 l * T.ptProd ρ0 l' := by
  simp [ptProd]

theorem one_le_norm_normPtExt (P : T.Pt) (ρ : Set.Ioc (0 : ℝ) ρ0) :
    1 ≤ T.extNorm ρ0 ρ (T.normPtExt P.2 ρ0) := by
  rw [T.extNorm_normPtExt P.2]; exact le_max_left _ _

theorem one_le_norm_normProd (l : List T.Pt) (ρ : Set.Ioc (0 : ℝ) ρ0) :
    1 ≤ T.extNorm ρ0 ρ (T.normProd ρ0 l) := by
  induction l with
  | nil => rw [normProd_nil, extNorm_one]
  | cons P l ih =>
    rw [normProd_cons, extNorm_mul]
    exact one_le_mul_of_one_le_of_one_le (T.one_le_norm_normPtExt P ρ) ih

theorem norm_normProd_of_le {l : List T.Pt} {s : ℝ} (hs : 0 ≤ s) (hl : ∀ P ∈ l, T.ptRad P.1 ≤ s)
    (ρ : Set.Ioc (0 : ℝ) ρ0) (hsρ : s ≤ ρ) :
    T.extNorm ρ0 ρ (T.normProd ρ0 l) = 1 ∧ T.extNorm ρ0 ρ (T.normProd ρ0 l - 1) ≤ s / ρ := by
  have hρ := rad_pos ρ0 ρ
  induction l with
  | nil =>
    rw [normProd_nil, extNorm_one, sub_self, extNorm_zero]
    exact ⟨rfl, div_nonneg hs hρ.le⟩
  | cons P l ih =>
    obtain ⟨h1, h2⟩ := ih fun Q hQ => hl Q (List.mem_cons_of_mem _ hQ)
    have hP := hl P List.mem_cons_self
    have hPr : T.ptRad P.1 / ρ ≤ 1 := by rw [div_le_one hρ]; linarith
    have hfP : T.extNorm ρ0 ρ (T.normPtExt P.2 ρ0) = 1 := by
      rw [T.extNorm_normPtExt P.2, max_eq_left hPr]
    refine ⟨by rw [normProd_cons, extNorm_mul, hfP, h1, one_mul], ?_⟩
    rw [normProd_cons, show T.normPtExt P.2 ρ0 * T.normProd ρ0 l - 1 =
      (T.normPtExt P.2 ρ0 - 1) * T.normProd ρ0 l + (T.normProd ρ0 l - 1) by ring]
    refine (T.extNorm_add_le ρ _ _).trans (max_le ?_ h2)
    rw [extNorm_mul, h1, mul_one, T.extNorm_normPtExt_sub_one P.2]
    exact div_le_div_of_nonneg_right hP hρ.le

def unitProd (ρ0 : Set.Ioo (0 : ℝ) 1) (l : List T.Pt) : T.RobbaExt ρ0 :=
  (l.map fun P => T.normUnit P.2 ρ0).prod

def unitProdInv (ρ0 : Set.Ioo (0 : ℝ) 1) (l : List T.Pt) : T.RobbaExt ρ0 :=
  (l.map fun P => T.normUnitInv (ξ := P.1) ρ0).prod

theorem unitProd_mul_inv (l : List T.Pt) : T.unitProd ρ0 l * T.unitProdInv ρ0 l = 1 := by
  induction l with
  | nil => simp [unitProd, unitProdInv]
  | cons P l ih =>
    simp only [unitProd, unitProdInv, List.map_cons, List.prod_cons] at ih ⊢
    rw [show T.normUnit P.2 ρ0 * (l.map fun P => T.normUnit P.2 ρ0).prod *
      (T.normUnitInv (ξ := P.1) ρ0 * (l.map fun P => T.normUnitInv (ξ := P.1) ρ0).prod) =
      (T.normUnit P.2 ρ0 * T.normUnitInv (ξ := P.1) ρ0) *
      ((l.map fun P => T.normUnit P.2 ρ0).prod * (l.map fun P => T.normUnitInv (ξ := P.1) ρ0).prod)
      by ring, T.normUnit_mul_inv, ih, one_mul]

theorem normProd_eq (l : List T.Pt) : T.normProd ρ0 l = T.ptProd ρ0 l * T.unitProd ρ0 l := by
  induction l with
  | nil => simp [normProd, ptProd, unitProd]
  | cons P l ih =>
    rw [normProd_cons, ih, T.normPtExt_eq P.2, ptProd_cons]
    simp only [unitProd, List.map_cons, List.prod_cons]
    ring

theorem ptProd_eq (l : List T.Pt) : T.ptProd ρ0 l = T.normProd ρ0 l * T.unitProdInv ρ0 l := by
  rw [normProd_eq, mul_assoc, unitProd_mul_inv, mul_one]

theorem normProd_dvd_iff (l : List T.Pt) (x : T.RobbaExt ρ0) :
    T.normProd ρ0 l ∣ x ↔ T.ptProd ρ0 l ∣ x := by
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨T.unitProd ρ0 l * y, by rw [normProd_eq, mul_assoc]⟩
  · rintro ⟨y, rfl⟩; exact ⟨T.unitProdInv ρ0 l * y, by rw [ptProd_eq, mul_assoc]⟩

def InfProd.ofLists (ρ0 : Set.Ioo (0 : ℝ) 1) (ls : ℕ → List T.Pt) (s : ℕ → ℝ)
    (hs0 : ∀ n, 0 ≤ s n) (hs : Tendsto s atTop (𝓝 0)) (hl : ∀ n, ∀ P ∈ ls n, T.ptRad P.1 ≤ s n) :
    T.InfProd ρ0 where
  g n := T.normProd ρ0 (ls n)
  one_le_norm n ρ := T.one_le_norm_normProd _ ρ
  tendsto_sub_one ρ := by
    have hρ := rad_pos ρ0 ρ
    have hlim : Tendsto (fun n => s n / ρ) atTop (𝓝 0) := by
      simpa using hs.div_const (ρ : ℝ)
    refine squeeze_zero' (Eventually.of_forall fun n => T.extNorm_nonneg _ _) ?_ hlim
    filter_upwards [hs.eventually (ge_mem_nhds hρ)] with n hn
    exact (T.norm_normProd_of_le (hs0 n) (hl n) ρ hn).2

theorem InfProd.ofLists_part (ls : ℕ → List T.Pt) (s : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n)
    (hs : Tendsto s atTop (𝓝 0)) (hl : ∀ n, ∀ P ∈ ls n, T.ptRad P.1 ≤ s n) (n : ℕ) :
    (InfProd.ofLists T ρ0 ls s hs0 hs hl).part n =
      T.normProd ρ0 ((List.range n).flatMap ls) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [InfProd.part_succ, ih, List.range_succ, List.flatMap_append, normProd_append]
    simp [InfProd.ofLists]

end TeichLift

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
  {ρ0 : Set.Ioo (0 : ℝ) 1} [CompleteSpace L]

theorem ptEval_ξExt_eq (Q : T.Pt) (hQ : T.ptRad Q.1 ≤ ρ0) (X : T.int) :
    T.ptEval Q.2 hQ (T.ξExt X ρ0) = T.toUntiltField Q.2 (T.toUntilt Q.1 X) := by
  rw [ξExt, ptEval_coe]
  show T.ptEvalB Q.2 (algebraMap Γ T.B X) = _
  rw [ptEvalB_algebraMap, T.ptE_int Q.2 X.2]

theorem toUntiltField_eq_zero_iff (Q : T.Pt) (q : T.Untilt Q.1) :
    T.toUntiltField Q.2 q = 0 ↔ q = 0 := by
  constructor
  · intro h
    have := congrArg norm h
    rw [norm_zero, T.norm_toUntiltField] at this
    exact (T.untiltNorm_eq_zero_iff Q.2).1 this
  · rintro rfl; exact map_zero _

theorem ξExt_mul_of_eq (P Q : T.Pt) {B : Γ} (hB : B ∈ T.int) (h : (P.1 : Γ) = Q.1 * B) :
    T.ξExt P.1 ρ0 = T.ξExt Q.1 ρ0 *
      ((⟨algebraMap Γ T.B B, T.algebraMap_int_mem_Econ hB ρ0⟩ : T.Econ ρ0) : T.RobbaExt ρ0) := by
  rw [ξExt, ξExt, ← Completion.coe_mul]
  congr 1
  apply Subtype.ext
  show algebraMap Γ T.B P.1 = algebraMap Γ T.B Q.1 * algebraMap Γ T.B B
  rw [h, map_mul]

theorem ptEval_iff_of_ptEval_ξExt (P Q : T.Pt) (hP : T.ptRad P.1 < ρ0) (hQ : T.ptRad Q.1 < ρ0)
    (h : T.ptEval Q.2 hQ.le (T.ξExt P.1 ρ0) = 0) :
    T.ptRad P.1 = T.ptRad Q.1 ∧
      ∀ z : T.RobbaExt ρ0, T.ptEval P.2 hP.le z = 0 ↔ T.ptEval Q.2 hQ.le z = 0 := by
  rw [T.ptEval_ξExt_eq Q hQ.le, T.toUntiltField_eq_zero_iff] at h
  obtain ⟨B, hB, hPB⟩ := (T.toUntilt_eq_zero_iff (ξ := Q.1)).1 h
  have hPQB := T.ξExt_mul_of_eq (ρ0 := ρ0) P Q hB hPB
  set cB : T.RobbaExt ρ0 := ((⟨algebraMap Γ T.B B, T.algebraMap_int_mem_Econ hB ρ0⟩ : T.Econ ρ0) :
    T.RobbaExt ρ0) with hcB
  have hcB0 : cB ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hPQB
    exact T.ptExt_ne_zero P.2 hPQB
  have hQr : 0 < T.ptRad Q.1 ∧ T.ptRad Q.1 < ρ0 := ⟨T.ptRad_pos' Q.2, hQ⟩
  have hm := T.mult_mul (T.ptExt_ne_zero Q.2) hcB0 hQr
  rw [← hPQB, T.mult_ptExt P.2 hQr, T.mult_ptExt Q.2 hQr, if_pos rfl] at hm
  have hr : T.ptRad Q.1 = T.ptRad P.1 := by
    by_contra hne
    rw [if_neg hne] at hm
    have := T.mult_nonneg cB (T.ptRad Q.1)
    omega
  refine ⟨hr.symm, ?_⟩

  have hredB : ‖T.red B‖ = 1 := by
    have e := congrArg T.red hPB
    rw [map_mul] at e
    have e2 := congrArg norm e
    rw [norm_mul, ← coeff_zero, ← coeff_zero] at e2
    have hQ0 : 0 < ‖T.coeff (Q.1 : Γ) 0‖ := T.ptRad_pos' Q.2
    have : ‖T.coeff (P.1 : Γ) 0‖ = ‖T.coeff (Q.1 : Γ) 0‖ := hr.symm
    rw [this] at e2
    field_simp at e2
    linarith [e2]
  have hBu : IsUnit (⟨B, hB⟩ : T.int) := T.isUnit_int_iff.2 hredB
  obtain ⟨Binv, hBinv⟩ := hBu.exists_right_inv
  set cBi : T.RobbaExt ρ0 :=
    ((⟨algebraMap Γ T.B Binv, T.algebraMap_int_mem_Econ Binv.2 ρ0⟩ : T.Econ ρ0) : T.RobbaExt ρ0)
    with hcBi
  have hQP : T.ξExt Q.1 ρ0 = T.ξExt P.1 ρ0 * cBi := by
    refine T.ξExt_mul_of_eq (ρ0 := ρ0) Q P Binv.2 ?_
    have e := congrArg Subtype.val hBinv
    simp only [Subring.coe_mul, Subring.coe_one] at e
    rw [hPB, mul_assoc, e, mul_one]
  intro z
  rw [T.ptEval_eq_zero_iff P.2 hP.le, T.ptEval_eq_zero_iff Q.2 hQ.le]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨cB * y, by rw [hPQB, mul_assoc]⟩
  · rintro ⟨y, rfl⟩; exact ⟨cBi * y, by rw [hQP, mul_assoc]⟩

theorem ptEval_πExt (P : T.Pt) (hr : T.ptRad P.1 ≤ ρ0) :
    T.ptEval P.2 hr (T.πExt ρ0) = T.ptPi P.2 := by
  rw [πExt, ptEval_coe]
  show T.ptEvalB P.2 (algebraMap Γ T.B T.π) = _
  rw [ptEvalB_algebraMap, ← pow_one T.π, T.ptE_π_pow P.2 1, pow_one]

theorem ptEval_πInvExt (P : T.Pt) (hr : T.ptRad P.1 ≤ ρ0) :
    T.ptEval P.2 hr (T.πInvExt ρ0) = (T.ptPi P.2)⁻¹ := by
  have h := congrArg (T.ptEval P.2 hr) (T.πExt_mul_πInvExt ρ0)
  rw [map_mul, map_one, ptEval_πExt] at h
  exact eq_inv_of_mul_eq_one_right h

theorem exists_bezout_pt (P : T.Pt) (hr : T.ptRad P.1 ≤ ρ0) {z : T.RobbaExt ρ0}
    (hz : T.ptEval P.2 hr z ≠ 0) :
    ∃ a b : T.RobbaExt ρ0, a * T.normPtExt P.2 ρ0 + b * z = 1 := by
  set v := (T.ptEval P.2 hr z)⁻¹ with hv
  have hv0 : v ≠ 0 := inv_ne_zero hz
  have hpi : ‖T.ptPi P.2‖ < 1 := by rw [T.norm_ptPi P.2]; exact T.ptRad_lt_one' P.2
  have hpi0 : T.ptPi P.2 ≠ 0 := T.ptPi_ne_zero P.2
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < 1 / ‖v‖ by positivity) hpi
  set w := v * T.ptPi P.2 ^ m with hw
  have hw1 : ‖w‖ ≤ 1 := by
    rw [hw, norm_mul, norm_pow]
    rw [lt_div_iff₀ (norm_pos_iff.2 hv0)] at hm
    linarith [mul_comm ‖v‖ (‖T.ptPi P.2‖ ^ m)]
  obtain ⟨zz, hzz, V, hV, hVe⟩ := T.exists_lift_value P.2 hw1
  have hzz1 : ‖zz‖ ≤ 1 := hzz ▸ hw1
  set b : T.RobbaExt ρ0 := ((⟨algebraMap Γ T.B (T.teich zz * V),
    T.coe_teich_mul_mem_Econ hzz1 hV⟩ : T.Econ ρ0) : T.RobbaExt ρ0) * T.πInvExt ρ0 ^ m with hb
  have hbv : T.ptEval P.2 hr b = v := by
    rw [hb, map_mul, map_pow, ptEval_πInvExt, ptEval_coe]
    show T.ptEvalB P.2 (algebraMap Γ T.B (T.teich zz * V)) * _ = v
    rw [ptEvalB_algebraMap, hVe, hw, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hpi0),
      mul_one]
  have h0 : T.ptEval P.2 hr (b * z - 1) = 0 := by
    rw [map_sub, map_mul, map_one, hbv, hv, inv_mul_cancel₀ hz, sub_self]
  obtain ⟨q, hq⟩ := (T.ptEval_eq_zero_iff P.2 hr _).1 h0
  refine ⟨-(T.normUnitInv (ξ := P.1) ρ0 * q), b, ?_⟩
  rw [T.ξExt_eq_normPtExt P.2] at hq
  linear_combination hq

theorem exists_bezout_list (z : T.RobbaExt ρ0) (l : List T.Pt)
    (h : ∀ P ∈ l, ∃ hr : T.ptRad P.1 ≤ ρ0, T.ptEval P.2 hr z ≠ 0) :
    ∃ a b : T.RobbaExt ρ0, a * T.normProd ρ0 l + b * z = 1 := by
  induction l with
  | nil => exact ⟨1, 0, by rw [normProd_nil]; ring⟩
  | cons P l ih =>
    obtain ⟨hr, hP⟩ := h P List.mem_cons_self
    obtain ⟨a1, b1, h1⟩ := T.exists_bezout_pt P hr hP
    obtain ⟨a2, b2, h2⟩ := ih fun Q hQ => h Q (List.mem_cons_of_mem _ hQ)
    refine ⟨a1 * a2, b1 + b2 - b1 * b2 * z, ?_⟩
    rw [normProd_cons]
    linear_combination (a2 * T.normProd ρ0 l) * h1 + (1 - b1 * z) * h2

theorem ptEval_ptProd_eq_zero {l : List T.Pt} (Q : T.Pt) (hQ : T.ptRad Q.1 ≤ ρ0)
    (h : T.ptEval Q.2 hQ (T.ptProd ρ0 l) = 0) : ∃ P ∈ l, T.ptEval Q.2 hQ (T.ξExt P.1 ρ0) = 0 := by
  rw [ptProd, map_list_prod, List.prod_eq_zero_iff, List.map_map] at h
  obtain ⟨P, hP, hP0⟩ := List.mem_map.1 h
  exact ⟨P, hP, hP0⟩

theorem exists_greedy (l : List T.Pt) (hl : ∀ P ∈ l, T.ptRad P.1 < ρ0) (y : T.RobbaExt ρ0) :
    ∃ (R K : List T.Pt) (y'' : T.RobbaExt ρ0),
      y = T.ptProd ρ0 R * y'' ∧ T.ptProd ρ0 l = T.ptProd ρ0 R * T.ptProd ρ0 K ∧
      (∀ P ∈ R, P ∈ l) ∧ (∀ P ∈ K, P ∈ l) ∧
      ∀ P ∈ K, ∀ hr : T.ptRad P.1 ≤ ρ0, T.ptEval P.2 hr y'' ≠ 0 := by
  induction l generalizing y with
  | nil => exact ⟨[], [], y, by rw [ptProd_nil, one_mul], by simp [ptProd], by simp, by simp, by simp⟩
  | cons P l ih =>
    have hPr := hl P List.mem_cons_self
    have hl' : ∀ Q ∈ l, T.ptRad Q.1 < ρ0 := fun Q hQ => hl Q (List.mem_cons_of_mem _ hQ)
    by_cases h0 : T.ptEval P.2 hPr.le y = 0
    · obtain ⟨y1, hy1⟩ := (T.ptEval_eq_zero_iff P.2 hPr.le y).1 h0
      obtain ⟨R, K, y'', hy, hlRK, hR, hK, hKev⟩ := ih hl' y1
      refine ⟨P :: R, K, y'', ?_, ?_, ?_, fun Q hQ => List.mem_cons_of_mem _ (hK Q hQ), hKev⟩
      · rw [hy1, hy, ptProd_cons, mul_assoc]
      · rw [ptProd_cons, ptProd_cons, hlRK, mul_assoc]
      · intro Q hQ
        rcases List.mem_cons.1 hQ with rfl | hQ
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hR Q hQ)
    · obtain ⟨R, K, y'', hy, hlRK, hR, hK, hKev⟩ := ih hl' y
      refine ⟨R, P :: K, y'', hy, ?_, fun Q hQ => List.mem_cons_of_mem _ (hR Q hQ), ?_, ?_⟩
      · rw [ptProd_cons, ptProd_cons, hlRK]; ring
      · intro Q hQ
        rcases List.mem_cons.1 hQ with rfl | hQ
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hK Q hQ)
      · intro Q hQ hr
        rcases List.mem_cons.1 hQ with rfl | hQ
        · intro hQ0
          apply h0
          rw [hy, map_mul, hQ0, mul_zero]
        · exact hKev Q hQ hr

theorem exists_stage (hRE : T.RootExists) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < ρ0)
    {x y : T.RobbaExt ρ0} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ (R : List T.Pt) (x' y' : T.RobbaExt ρ0), x = T.ptProd ρ0 R * x' ∧ y = T.ptProd ρ0 R * y' ∧
      (∀ P ∈ R, a ≤ T.ptRad P.1 ∧ T.ptRad P.1 ≤ b) ∧ x' ≠ 0 ∧ y' ≠ 0 ∧
      ∀ Q : T.Pt, ∀ hQ : a ≤ T.ptRad Q.1 ∧ T.ptRad Q.1 ≤ b,
        ¬ (T.ptEval Q.2 (hQ.2.trans hb.le) x' = 0 ∧ T.ptEval Q.2 (hQ.2.trans hb.le) y' = 0) := by
  obtain ⟨l, w, hlrad, hxl, hw0, hwm⟩ := T.exists_factor_annulus hRE ha hab hb hx
  obtain ⟨R, K, y'', hy'', hlRK, hR, hK, hKev⟩ :=
    T.exists_greedy l (fun P hP => (hlrad P hP).2.trans_lt hb) y
  refine ⟨R, T.ptProd ρ0 K * w, y'', ?_, hy'', fun P hP => hlrad P (hR P hP),
    mul_ne_zero (T.ptProd_ne_zero K) hw0, ?_, ?_⟩
  · rw [hxl, hlRK, mul_assoc]
  · rintro rfl; rw [mul_zero] at hy''; exact hy hy''
  · rintro Q hQ ⟨hQx, hQy⟩
    have hs : 0 < T.ptRad Q.1 ∧ T.ptRad Q.1 < ρ0 := ⟨ha.trans_le hQ.1, hQ.2.trans_lt hb⟩
    rw [map_mul, mul_eq_zero] at hQx
    rcases hQx with hK0 | hw
    · obtain ⟨P, hP, hP0⟩ := T.ptEval_ptProd_eq_zero Q _ hK0
      have hPr : T.ptRad P.1 < ρ0 := (hlrad P (hK P hP)).2.trans_lt hb
      obtain ⟨-, hiff⟩ := T.ptEval_iff_of_ptEval_ξExt P Q hPr hs.2 hP0
      exact hKev P hP hPr.le ((hiff y'').2 hQy)
    · obtain ⟨w', hw'⟩ := (T.ptEval_eq_zero_iff Q.2 _ w).1 hw
      have hw'0 : w' ≠ 0 := by rintro rfl; rw [mul_zero] at hw'; exact hw0 hw'
      have hm := T.mult_mul (T.ptExt_ne_zero Q.2) hw'0 hs
      rw [← hw', hwm _ hQ.1 hQ.2, T.mult_ptExt Q.2 hs, if_pos rfl] at hm
      have := T.mult_nonneg w' (T.ptRad Q.1)
      omega

structure GcdSt (ρ0 : Set.Ioo (0 : ℝ) 1) where
  x : T.RobbaExt ρ0
  y : T.RobbaExt ρ0
  hx : x ≠ 0
  hy : y ≠ 0

def annLo (ρ0 : Set.Ioo (0 : ℝ) 1) (k : ℕ) : ℝ := (ρ0 : ℝ) / 2 ^ (k + 2)
def annHi (ρ0 : Set.Ioo (0 : ℝ) 1) (k : ℕ) : ℝ := (ρ0 : ℝ) / 2 ^ (k + 1)

theorem annLo_pos (k : ℕ) : 0 < annLo ρ0 k := by unfold annLo; have := ρ0.2.1; positivity

theorem annLo_le (k : ℕ) : annLo ρ0 k ≤ annHi ρ0 k := by
  unfold annLo annHi
  exact div_le_div_of_nonneg_left ρ0.2.1.le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))

theorem annHi_lt (k : ℕ) : annHi ρ0 k < ρ0 := by
  unfold annHi
  rw [div_lt_iff₀ (by positivity)]
  have := ρ0.2.1
  have : (1 : ℝ) < 2 ^ (k + 1) := one_lt_pow₀ (by norm_num) (by omega)
  nlinarith


theorem exists_ann {s : ℝ} (hs0 : 0 < s) (hs : s ≤ (ρ0 : ℝ) / 2) :
    ∃ k, annLo ρ0 k ≤ s ∧ s ≤ annHi ρ0 k := by
  have ht : 1 ≤ (ρ0 : ℝ) / 2 / s := by rw [le_div_iff₀ hs0, one_mul]; exact hs
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near ht (show (1 : ℝ) < 2 by norm_num)
  refine ⟨n, ?_, ?_⟩
  · unfold annLo
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hs0] at hn2
    have e : s * 2 ^ (n + 2) = 2 * (2 ^ (n + 1) * s) := by ring
    rw [e]; linarith
  · unfold annHi
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ hs0] at hn1
    have e : s * 2 ^ (n + 1) = 2 * (2 ^ n * s) := by ring
    rw [e]; linarith

variable (hRE : T.RootExists)
include hRE

def gcdStep (k : ℕ) (S : T.GcdSt ρ0) : List T.Pt × T.GcdSt ρ0 :=
  let h := T.exists_stage hRE (annLo_pos (ρ0 := ρ0) k) (annLo_le k) (annHi_lt k) S.hx S.hy
  (Classical.choose h, ⟨Classical.choose (Classical.choose_spec h),
    Classical.choose (Classical.choose_spec (Classical.choose_spec h)),
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))).2.2.2.1,
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))).2.2.2.2.1⟩)

theorem gcdStep_spec (k : ℕ) (S : T.GcdSt ρ0) :
    S.x = T.ptProd ρ0 (T.gcdStep hRE k S).1 * (T.gcdStep hRE k S).2.x ∧
      S.y = T.ptProd ρ0 (T.gcdStep hRE k S).1 * (T.gcdStep hRE k S).2.y ∧
      (∀ P ∈ (T.gcdStep hRE k S).1, annLo ρ0 k ≤ T.ptRad P.1 ∧ T.ptRad P.1 ≤ annHi ρ0 k) ∧
      ∀ Q : T.Pt, ∀ hQ : annLo ρ0 k ≤ T.ptRad Q.1 ∧ T.ptRad Q.1 ≤ annHi ρ0 k,
        ¬ (T.ptEval Q.2 (hQ.2.trans (annHi_lt k).le) (T.gcdStep hRE k S).2.x = 0 ∧
          T.ptEval Q.2 (hQ.2.trans (annHi_lt k).le) (T.gcdStep hRE k S).2.y = 0) := by
  have h := T.exists_stage hRE (annLo_pos (ρ0 := ρ0) k) (annLo_le k) (annHi_lt k) S.hx S.hy
  have hs := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.2.2⟩

def gcdStates (S0 : T.GcdSt ρ0) : ℕ → T.GcdSt ρ0
  | 0 => S0
  | k + 1 => (T.gcdStep hRE k (gcdStates S0 k)).2

def gcdRemoved (S0 : T.GcdSt ρ0) (k : ℕ) : List T.Pt := (T.gcdStep hRE k (T.gcdStates hRE S0 k)).1

theorem gcdStates_spec (S0 : T.GcdSt ρ0) (k : ℕ) :
    S0.x = T.ptProd ρ0 ((List.range k).flatMap (T.gcdRemoved hRE S0)) * (T.gcdStates hRE S0 k).x ∧
      S0.y = T.ptProd ρ0 ((List.range k).flatMap (T.gcdRemoved hRE S0)) *
        (T.gcdStates hRE S0 k).y := by
  induction k with
  | zero => simp [gcdStates, ptProd]
  | succ k ih =>
    obtain ⟨hx, hy, -, -⟩ := T.gcdStep_spec hRE k (T.gcdStates hRE S0 k)
    rw [List.range_succ, List.flatMap_append, ptProd_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine ⟨?_, ?_⟩
    · rw [ih.1, hx, mul_assoc]; rfl
    · rw [ih.2, hy, mul_assoc]; rfl

omit hRE in
theorem tendsto_annHi : Tendsto (annHi ρ0) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 : ℝ) / 2 < 1 by norm_num)).const_mul ((ρ0 : ℝ) / 2)
  rw [mul_zero] at h
  refine h.congr fun k => ?_
  unfold annHi
  rw [pow_succ, div_pow, one_pow]
  field_simp

omit hRE in
theorem annHi_nonneg (k : ℕ) : 0 ≤ annHi ρ0 k := (annLo_pos k).le.trans (annLo_le k)

theorem exists_gcd {x y : T.RobbaExt ρ0} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ (d x' y' : T.RobbaExt ρ0), d ≠ 0 ∧ x = d * x' ∧ y = d * y' ∧
      ∀ Q : T.Pt, ∀ hQ : T.ptRad Q.1 ≤ (ρ0 : ℝ) / 2,
        ¬ (T.ptEval Q.2 (hQ.trans (half_le_self ρ0.2.1.le)) x' = 0 ∧
          T.ptEval Q.2 (hQ.trans (half_le_self ρ0.2.1.le)) y' = 0) := by
  set S0 : T.GcdSt ρ0 := ⟨x, y, hx, hy⟩
  have hl : ∀ k, ∀ P ∈ T.gcdRemoved hRE S0 k, T.ptRad P.1 ≤ annHi ρ0 k := fun k P hP =>
    ((T.gcdStep_spec hRE k (T.gcdStates hRE S0 k)).2.2.1 P hP).2
  set D := InfProd.ofLists T ρ0 (T.gcdRemoved hRE S0) (annHi ρ0) annHi_nonneg tendsto_annHi hl
  have hpart : ∀ k, D.part k = T.normProd ρ0 ((List.range k).flatMap (T.gcdRemoved hRE S0)) :=
    fun k => InfProd.ofLists_part T _ _ _ _ _ k
  have hdx : ∀ k, D.part k ∣ x := fun k => by
    rw [hpart, normProd_dvd_iff]; exact ⟨_, (T.gcdStates_spec hRE S0 k).1⟩
  have hdy : ∀ k, D.part k ∣ y := fun k => by
    rw [hpart, normProd_dvd_iff]; exact ⟨_, (T.gcdStates_spec hRE S0 k).2⟩
  obtain ⟨x', hx'⟩ := D.dvd_of_forall hdx
  obtain ⟨y', hy'⟩ := D.dvd_of_forall hdy
  refine ⟨D.prod, x', y', D.prod_ne_zero, hx', hy', ?_⟩
  rintro Q hQ ⟨h1, h2⟩
  have hs0 := T.ptRad_pos' Q.2
  obtain ⟨k, hk1, hk2⟩ := exists_ann (ρ0 := ρ0) hs0 hQ
  set F := (List.range (k + 1)).flatMap (T.gcdRemoved hRE S0)
  have hQr : T.ptRad Q.1 ≤ ρ0 := hQ.trans (half_le_self ρ0.2.1.le)

  have key : ∀ (w w' W : T.RobbaExt ρ0), w = D.prod * w' → w = T.ptProd ρ0 F * W →
      T.ptEval Q.2 hQr w' = 0 → T.ptEval Q.2 hQr W = 0 := by
    intro w w' W hw hW hw'
    have e : T.ptProd ρ0 F * W = T.ptProd ρ0 F * (T.unitProd ρ0 F * (D.shift (k + 1)).prod * w') := by
      rw [← hW, hw, D.prod_eq_part_mul_shift (k + 1), hpart, normProd_eq]; ring
    have hW' := mul_left_cancel₀ (T.ptProd_ne_zero F) e
    rw [hW', map_mul, hw', mul_zero]
  have hX := key x x' _ hx' (T.gcdStates_spec hRE S0 (k + 1)).1 h1
  have hY := key y y' _ hy' (T.gcdStates_spec hRE S0 (k + 1)).2 h2
  exact (T.gcdStep_spec hRE k (T.gcdStates hRE S0 k)).2.2.2 Q ⟨hk1, hk2⟩ ⟨hX, hY⟩

end TeichLift

end GroundTheory.PAdicHodge
end
end
