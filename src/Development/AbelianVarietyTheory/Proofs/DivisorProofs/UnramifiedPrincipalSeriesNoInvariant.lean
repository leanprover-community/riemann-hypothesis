import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD
import BuildAid.ForwardExisting

section
section
noncomputable section

open Matrix

namespace GlobalTheory.PrinTwo

theorem eq_zero_of_ev_one_of_coord {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : PSp μ₁ μ₂) (h1 : ev f 1 = 0)
    (hc : ∀ x : k, coord f x = 0) : f = 0 := by
  apply ext_ev
  intro g
  have hz : ev (0 : PSp μ₁ μ₂) g = 0 := by
    have := ev_smul (0 : ℂ) (0 : PSp μ₁ μ₂) g
    simpa using this
  rw [hz]
  have hdet : (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k).det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit |>.ne_zero
  rw [Matrix.det_fin_two] at hdet
  by_cases hr : (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 0 = 0
  · rw [hr, mul_zero, sub_zero] at hdet
    have hp : (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
    have hs : (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
    have hg : g = bor (Units.mk0 _ hp) (Units.mk0 _ hs) ((g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 0 1) * 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [hr]
    rw [hg, ev_bor, h1, mul_zero]
  · set D := (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 0 0 * (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 1 -
      (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 0 1 * (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 0 with hD
    have hA : -D / (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 0 ≠ 0 := div_ne_zero (neg_ne_zero.2 hdet) hr
    have hg : g = bor (Units.mk0 _ hA) (Units.mk0 _ hr) ((g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 0 0) *
        (wE * nU ((g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 1 / (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 0)) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hD] <;> field_simp <;> ring
    rw [hg, ev_bor]
    have := hc ((g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 1 / (g : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) 1 0)
    rw [coord] at this
    rw [this, mul_zero]

end GlobalTheory.PrinTwo
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_series_zero_of_coordinate_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), GlobalTheory.PrinTwo.ev f 1 = 0 → (∀ x : k, GlobalTheory.PrinTwo.coord f x = 0) → f = 0 := by
  atlas_forward_decl GlobalTheory.PrinTwo.eq_zero_of_ev_one_of_coord
end

section
section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped Topology

namespace GlobalTheory.PrinTwo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nL_inv (x : k) : ((nL x)⁻¹ : GL (Fin (1 + 1)) k) = nL (-x) := by
  rw [inv_eq_iff_mul_eq_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem continuous_nL : Continuous (nL : k → GL (Fin (1 + 1)) k) := by
  have h : Continuous fun x : k => ((nL x : GL (Fin (1 + 1)) k) : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [nL_inv]
  exact h.comp continuous_neg

theorem nL_zero : (nL (0 : k) : GL (Fin (1 + 1)) k) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem exists_ev_nL_eq {μ₁ μ₂ : kˣ →* ℂˣ} (f : PSp μ₁ μ₂) :
    ∃ r : kˣ, ∀ z : k, valuation k z < valuation k (r : k) → ev f (nL z) = ev f 1 := by
  have hS : IsOpen {g : GL (Fin (1 + 1)) k | psRep μ₁ μ₂ g f = f} := isSmooth_parInd _ _ f
  have hU : nL ⁻¹' {g : GL (Fin (1 + 1)) k | psRep μ₁ μ₂ g f = f} ∈ 𝓝 (0 : k) :=
    (hS.preimage continuous_nL).mem_nhds (by simp [nL_zero])
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).mp hU
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero k)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact γ.ne_zero (by simpa using hy.symm)
  refine ⟨Units.mk0 y hy0, fun z hz => ?_⟩
  have hz' : psRep μ₁ μ₂ (nL z) f = f := hγ (by rw [← hy]; exact hz)
  rw [← one_mul (nL z), ← ev_act, hz']

theorem coord_eq_of_far : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), ∃ R : kˣ, ∀ x : kˣ,
    ValuativeRel.valuation k (R : k) < ValuativeRel.valuation k (x : k) →
      GlobalTheory.PrinTwo.coord f x = GlobalTheory.PrinTwo.bchar μ₁ μ₂ (-x⁻¹) x * GlobalTheory.PrinTwo.ev f 1 := by
  intro k _ _ _ _ μ₁ μ₂ f
  obtain ⟨r, hr⟩ := exists_ev_nL_eq f
  refine ⟨r⁻¹, fun x hx => ?_⟩
  rw [coord, wE_mul_nU_eq, ev_bor, hr]
  have hx0 : (0 : ValueGroupWithZero k) < valuation k (x : k) := by simp [zero_lt_iff]
  have hr0 : (0 : ValueGroupWithZero k) < valuation k (r : k) := by simp [zero_lt_iff]
  simp only [Units.val_inv_eq_inv_val, map_inv₀] at hx ⊢
  exact (inv_lt_comm₀ hr0 hx0).mp hx

end GlobalTheory.PrinTwo
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_series_coordinate_near_infinity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), ∃ R : kˣ, ∀ x : kˣ, ValuativeRel.valuation k (R : k) < ValuativeRel.valuation k (x : k) → GlobalTheory.PrinTwo.coord f x = GlobalTheory.PrinTwo.bchar μ₁ μ₂ (-x⁻¹) x * GlobalTheory.PrinTwo.ev f 1 := by
  atlas_forward_decl GlobalTheory.PrinTwo.coord_eq_of_far
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PrinTwo

namespace GlobalTheory.PrinTwo.NoFix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

theorem exists_unif : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
  exact ⟨Units.mk0 x (by rintro rfl; exact uniformizer_ne_zero (R := k) (by simpa using hx.symm)), hx⟩

theorem isUnram_mul {χ ψ : kˣ →* ℂˣ} (h : IsUnram χ) (h' : IsUnram ψ) : IsUnram (χ * ψ) := fun x hx => by
  rw [MonoidHom.mul_apply, h x hx, h' x hx, one_mul]

theorem bchar_shift (μ₁ μ₂ : kˣ →* ℂˣ) (a d t : kˣ) :
    bchar μ₁ μ₂ (a * t) (d * t⁻¹) = bchar μ₁ μ₂ a d * ((μ₁ t * absPow k 1 t / μ₂ t : ℂˣ) : ℂ) := by
  have h1 : absPow k 1 = absPow k (1 / 2) * absPow k (1 / 2) := by rw [← absPow_add]; norm_num
  have h2 : absPow k (-1 / 2) = (absPow k (1 / 2))⁻¹ := by rw [neg_div, absPow_neg]
  simp only [bchar, h1, h2, MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv, Units.val_mul,
    Units.val_inv_eq_inv_val, Units.val_div_eq_div_val]
  have e1 : ((μ₂ t : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have e2 : ((absPow k (1 / 2) d : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have e3 : ((absPow k (1 / 2) t : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

theorem val_lt_val_mul_inv {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (y : kˣ) :
    valuation k (y : k) < valuation k ((y * ϖ⁻¹ : kˣ) : k) := by
  rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
  have hy0 : 0 < valuation k (y : k) := zero_lt_iff.2 (by simp)
  have hϖ0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
  have hu : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  exact lt_mul_of_one_lt_right hy0 ((one_lt_inv₀ hϖ0).2 hu)

end GlobalTheory.PrinTwo.NoFix

namespace GlobalTheory.PrinTwo.NoFix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_zero_of_fixed_of
    (hinj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), GlobalTheory.PrinTwo.ev f 1 = 0 → (∀ x : k, GlobalTheory.PrinTwo.coord f x = 0) → f = 0)
    (hasy : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), ∃ R : kˣ, ∀ x : kˣ, ValuativeRel.valuation k (R : k) < ValuativeRel.valuation k (x : k) → GlobalTheory.PrinTwo.coord f x = GlobalTheory.PrinTwo.bchar μ₁ μ₂ (-x⁻¹) x * GlobalTheory.PrinTwo.ev f 1)
    {μ₁ μ₂ : kˣ →* ℂˣ} (h₁ : IsUnram μ₁) (h₂ : IsUnram μ₂) (hne : μ₂ ≠ μ₁ * absPow k 1)
    (f : PSp μ₁ μ₂) (hf : ∀ x : k, psRep μ₁ μ₂ (nU x) f = f) : f = 0 := by
  have hc : ∀ x : k, coord f x = ev f wE := fun x => by
    rw [coord, ← ev_act, hf x]
  obtain ⟨R, hR⟩ := hasy k μ₁ μ₂ f
  obtain ⟨ϖ, hϖ⟩ := exists_unif k
  obtain ⟨x, hx⟩ : ∃ x : kˣ, x = R * ϖ⁻¹ := ⟨_, rfl⟩
  have hxR : valuation k (R : k) < valuation k (x : k) := hx ▸ val_lt_val_mul_inv hϖ R
  have hx'R : valuation k (R : k) < valuation k ((x * ϖ⁻¹ : kˣ) : k) :=
    hxR.trans (val_lt_val_mul_inv hϖ x)
  have h1 : ev f 1 = 0 := by
    by_contra h0
    apply hne
    have e := (hR x hxR).symm.trans ((hc x).trans ((hc _).symm.trans (hR _ hx'R)))
    have e2 : bchar μ₁ μ₂ (-(x * ϖ⁻¹)⁻¹) (x * ϖ⁻¹) =
        bchar μ₁ μ₂ (-x⁻¹) x * ((μ₁ ϖ * absPow k 1 ϖ / μ₂ ϖ : ℂˣ) : ℂ) := by
      rw [← bchar_shift]
      congr 1
      rw [mul_inv_rev, inv_inv, neg_mul, mul_comm]
    rw [e2, mul_assoc] at e
    have e3 := mul_left_cancel₀ (bchar_ne_zero μ₁ μ₂ _ _) e
    have e4 : ((μ₁ ϖ * absPow k 1 ϖ / μ₂ ϖ : ℂˣ) : ℂ) = 1 := by
      have := mul_right_cancel₀ h0 (e3.symm.trans (one_mul _).symm)
      exact this
    have e5 : μ₂ ϖ = (μ₁ * absPow k 1) ϖ := by
      rw [MonoidHom.mul_apply]
      exact (div_eq_one.1 (Units.ext e4)).symm
    rw [eq_unrChar h₂ hϖ, eq_unrChar (isUnram_mul h₁ (isUnram_absPow k 1)) hϖ, e5]
  refine hinj k μ₁ μ₂ f h1 fun y => ?_
  rw [hc y, ← hc x, hR x hxR, h1, mul_zero]

end GlobalTheory.PrinTwo.NoFix

theorem GlobalTheory.PrinTwo.NoFix.eq_zero_of_nU_fixed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (μ₁ μ₂ : kˣ →* ℂˣ), GlobalTheory.SplitWeil.IsUnram μ₁ → GlobalTheory.SplitWeil.IsUnram μ₂ → μ₂ ≠ μ₁ * GlobalTheory.SmGL.absPow k 1 → ∀ f : GlobalTheory.PrinTwo.PSp μ₁ μ₂, (∀ x : k, GlobalTheory.PrinTwo.psRep μ₁ μ₂ (GlobalTheory.PrinTwo.nU x) f = f) → f = 0 :=
  fun _ _ _ _ _ _ _ h₁ h₂ hne f hf =>
    GlobalTheory.PrinTwo.NoFix.eq_zero_of_fixed_of GlobalTheory.T.principal_series_zero_of_coordinate_zero GlobalTheory.T.principal_series_coordinate_near_infinity h₁ h₂ hne f hf
end
end
