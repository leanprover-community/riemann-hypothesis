import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameMatrixHasSum
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LaurentCoeffNegEqZeroOfBounded

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory

theorem powerSeries_dvd_of_sum_bounded : ∀ (G H : PowerSeries ℂ) (T C : ℝ) (g h : ℂ → ℂ), H ≠ 0 →
    (∀ w : ℂ, T < w.im → SumsAt G w (g w) ∧ SumsAt H w (h w) ∧ (h w ≠ 0 → ‖g w‖ ≤ C * ‖h w‖)) →
    H ∣ G := by
  intro G H T C g h hH hyp
  set m : ℕ := H.order.toNat with hm
  set T₀ : ℝ := max T 0 + 1 with hT₀
  have hT₀T : T < T₀ := by have := le_max_left T 0; linarith
  set w₁ : ℂ := Complex.I * (T₀ : ℂ) with hw₁
  have hw₁im : w₁.im = T₀ := by simp [hw₁]
  set q₁ := eTwoPi w₁ with hq₁
  set ρ₁ : ℝ := GlobalTheory.Conv.cuspRadius T₀ with hρ₁
  have hρ₁pos : 0 < ρ₁ := GlobalTheory.Conv.cuspRadius_pos T₀
  have hq₁n : ‖q₁‖ = ρ₁ := by rw [hq₁, GlobalTheory.Conv.norm_eTwoPi, hw₁im]
  have hH₁ : HasSum (fun j : ℕ => PowerSeries.coeff j H * q₁ ^ j) (h w₁) :=
    (hyp w₁ (by rw [hw₁im]; exact hT₀T)).2.1
  have hS₁ : Summable (fun j : ℕ => ‖PowerSeries.coeff j H * q₁ ^ j‖) := hH₁.summable.norm
  set S₁ := ∑' j : ℕ, ‖PowerSeries.coeff j H * q₁ ^ j‖ with hS₁def

  have hbnd : ∀ w : ℂ, T₀ ≤ w.im → ‖h w‖ ≤ (‖eTwoPi w‖ / ρ₁) ^ m * S₁ := by
    intro w hw
    have hHw : HasSum (fun j : ℕ => PowerSeries.coeff j H * eTwoPi w ^ j) (h w) :=
      (hyp w (lt_of_lt_of_le hT₀T hw)).2.1
    set ρ := ‖eTwoPi w‖ with hρ
    have hρ0 : 0 ≤ ρ := norm_nonneg _
    have hρle : ρ ≤ ρ₁ := by
      rw [hρ, GlobalTheory.Conv.norm_eTwoPi]; exact GlobalTheory.Conv.cuspRadius_strictAnti.antitone hw
    have hterm : ∀ j : ℕ, ‖PowerSeries.coeff j H * eTwoPi w ^ j‖ ≤
        (ρ / ρ₁) ^ m * ‖PowerSeries.coeff j H * q₁ ^ j‖ := by
      intro j
      by_cases hj : j < m
      · rw [PowerSeries.coeff_of_lt_order_toNat j hj]; simp
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hj)
        rw [norm_mul, norm_mul, norm_pow, norm_pow, ← hρ, hq₁n, div_pow, pow_add, pow_add]
        have hc := norm_nonneg (PowerSeries.coeff (m + d) H)
        have hpow : ρ ^ d ≤ ρ₁ ^ d := pow_le_pow_left₀ hρ0 hρle d
        have hρ₁m : 0 < ρ₁ ^ m := pow_pos hρ₁pos m
        calc ‖PowerSeries.coeff (m + d) H‖ * (ρ ^ m * ρ ^ d)
            ≤ ‖PowerSeries.coeff (m + d) H‖ * (ρ ^ m * ρ₁ ^ d) := by gcongr
          _ = ρ ^ m / ρ₁ ^ m * (‖PowerSeries.coeff (m + d) H‖ * (ρ₁ ^ m * ρ₁ ^ d)) := by
            field_simp
    rw [← hHw.tsum_eq]
    exact tsum_of_norm_bounded (hS₁.hasSum.mul_left _) hterm

  have hconv : (H : ℂ⸨X⸩) ∈ GlobalTheory.Conv.convLaurent :=
    GlobalTheory.Conv.halfRing_le_convLaurent T (GlobalTheory.Conv.coe_mem_halfRing.2 fun w hw => ⟨_, (hyp w hw).2.1⟩)
  have hH' : (H : ℂ⸨X⸩) ≠ 0 := fun h0 => hH ((map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective).1 h0)
  obtain ⟨T₂, hT₂⟩ := GlobalTheory.Conv.exists_lsum_eTwoPi_ne_zero hconv hH'
  have hne : ∀ w : ℂ, T < w.im → T₂ < w.im → h w ≠ 0 := by
    intro w hw hw2
    have := hT₂ w hw2
    rwa [GlobalTheory.Conv.lsum_coe, GlobalTheory.Conv.sum, (hyp w hw).2.1.tsum_eq] at this

  set F : ℂ⸨X⸩ := HahnSeries.single (-(m : ℤ)) (1 : ℂ) * (G : ℂ⸨X⸩) with hF
  have hFb := GlobalTheory.laurent_coeff_neg_eq_zero_of_bounded F (max T₀ T₂) (max C 0 * (S₁ / ρ₁ ^ m))
    (by
      intro w hw
      have hw0 : T₀ < w.im := lt_of_le_of_lt (le_max_left _ _) hw
      have hw2 : T₂ < w.im := lt_of_le_of_lt (le_max_right _ _) hw
      have hwT : T < w.im := hT₀T.trans hw0
      have hq0 : eTwoPi w ≠ 0 := GlobalTheory.Conv.eTwoPi_ne_zero w
      refine ⟨eTwoPi w ^ (-(m : ℤ)) * g w,
        GlobalTheory.Conv.hasSum_single_mul hq0 (-(m : ℤ)) (GlobalTheory.Conv.sumsAt_iff.1 (hyp w hwT).1), ?_⟩
      have hρpos : 0 < ‖eTwoPi w‖ := norm_pos_iff.2 hq0
      have hg := (hyp w hwT).2.2 (hne w hwT hw2)
      have hb := hbnd w hw0.le
      have hS₁0 : 0 ≤ S₁ := tsum_nonneg fun _ => norm_nonneg _
      have hρm : 0 < ‖eTwoPi w‖ ^ m := pow_pos hρpos m
      have hρ₁m : 0 < ρ₁ ^ m := pow_pos hρ₁pos m
      rw [norm_mul, norm_zpow, zpow_neg, zpow_natCast]
      have h1 : ‖g w‖ ≤ max C 0 * ((‖eTwoPi w‖ / ρ₁) ^ m * S₁) :=
        hg.trans ((mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_left hb (le_max_right C 0)))
      rw [div_pow] at h1
      rw [inv_mul_le_iff₀ hρm]
      calc ‖g w‖ ≤ max C 0 * (‖eTwoPi w‖ ^ m / ρ₁ ^ m * S₁) := h1
        _ = ‖eTwoPi w‖ ^ m * (max C 0 * (S₁ / ρ₁ ^ m)) := by ring)
  have hcoeff : ∀ i < m, PowerSeries.coeff i G = 0 := by
    intro i hi
    have := hFb ((i : ℤ) + -(m : ℤ)) (by omega)
    rw [hF, HahnSeries.coeff_single_mul_add, one_mul] at this
    simpa using this
  have hXG : (PowerSeries.X : PowerSeries ℂ) ^ m ∣ G := PowerSeries.X_pow_dvd_iff.2 hcoeff
  obtain ⟨u, hu⟩ := PowerSeries.isUnit_divided_by_X_pow_order hH
  have hHe : H = PowerSeries.X ^ m * (u : PowerSeries ℂ) := by
    rw [hu, hm, PowerSeries.X_pow_order_mul_divXPowOrder]
  have hHX : H ∣ (PowerSeries.X : PowerSeries ℂ) ^ m :=
    ⟨(u⁻¹ : (PowerSeries ℂ)ˣ), by rw [hHe, mul_assoc, Units.mul_inv, mul_one]⟩
  exact hHX.trans hXG

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nomePowerSeries_dvd_of_sum_bounded : ∀ (G H : PowerSeries ℂ) (T C : ℝ) (g h : ℂ → ℂ), H ≠ 0 → (∀ w : ℂ, T < w.im → SumsAt G w (g w) ∧ SumsAt H w (h w) ∧ (h w ≠ 0 → ‖g w‖ ≤ C * ‖h w‖)) → H ∣ G := by
  atlas_forward_decl GlobalTheory.powerSeries_dvd_of_sum_bounded
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcReg

theorem valR_eq_ev {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : valR x U f = ev x U h f := by
  rw [valR, dif_pos h]; rfl

theorem not_pole_of_bounded : ∀ (X : Scheme.{0}) (U₀ W₀ : X.Opens) (f₀ : Γ(X, W₀)) (χ : Sp (PowerSeries ℂ) ⟶ X) (y : ℂ → (Sp ℂ ⟶ X)), IsAffineOpen U₀ → W₀ ≤ U₀ → ⊤ ≤ χ ⁻¹ᵁ U₀ → (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ χ ⁻¹ᵁ U → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ⊤ ≤ y w ⁻¹ᵁ U ∧ SumsAt (valR χ U f) w (valAt' (y w) U f)) → (∃ T C : ℝ, ∀ w : ℂ, T < w.im → ∀ hy : ⊤ ≤ y w ⁻¹ᵁ W₀, ‖ev (y w) W₀ hy f₀‖ ≤ C) → ∀ h : ⊤ ≤ (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) ⁻¹ᵁ W₀, ev (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) W₀ h f₀ ∈ (HahnSeries.ofPowerSeries ℤ ℂ).range := by
  intro X U₀ W₀ f₀ χ y hU₀ hWU hχ harc hbd h
  have hηW : (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) (default : PrimeSpectrum (LaurentSeries ℂ)) ∈ W₀ :=
    h trivial
  obtain ⟨s, hsW, hsη⟩ := hU₀.exists_basicOpen_le (V := W₀) ⟨_, hηW⟩ (hWU hηW)
  obtain ⟨n, t, ht⟩ := exists_eq_pow_mul_of_isAffineOpen X U₀ hU₀ s
    ((X.presheaf.map (homOfLE hsW).op).hom f₀)
  have hsU : X.basicOpen s ≤ U₀ := X.basicOpen_le s

  have key : ∀ (A : Type) [CommRing A] (z : Sp A ⟶ X) (hz : ⊤ ≤ z ⁻¹ᵁ X.basicOpen s),
      valR z U₀ (t * s) = valR z U₀ (s ^ (n + 1)) * valR z W₀ f₀ := by
    intro A _ z hz
    have hzU : ⊤ ≤ z ⁻¹ᵁ U₀ := GlobalTheory.FlagMod.le_preimage_mono hsU hz
    have e := congrArg (GlobalTheory.HolHom.evalHom z _ hz) ht
    rw [map_mul, map_pow] at e
    simp only [← GlobalTheory.HolHom.valR_eq z _ hz] at e
    erw [GlobalTheory.HolHom.valR_res z hsU t hz, GlobalTheory.HolHom.valR_res z hsU s hz, GlobalTheory.HolHom.valR_res z hsW f₀ hz] at e
    rw [GlobalTheory.HolHom.valR_eq z U₀ hzU, GlobalTheory.HolHom.valR_eq z U₀ hzU, map_mul, map_pow,
      ← GlobalTheory.HolHom.valR_eq z U₀ hzU, ← GlobalTheory.HolHom.valR_eq z U₀ hzU, e]
    ring

  have hηs : ⊤ ≤ (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) ⁻¹ᵁ X.basicOpen s := fun p _ => by
    obtain rfl : p = (default : PrimeSpectrum (LaurentSeries ℂ)) := Subsingleton.elim _ _
    exact hsη
  have hηU : ⊤ ≤ (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) ⁻¹ᵁ U₀ := GlobalTheory.FlagMod.le_preimage_mono hsU hηs
  have hu : IsUnit (HahnSeries.ofPowerSeries ℤ ℂ (valR χ U₀ (s ^ (n + 1)))) := by
    rw [← GlobalTheory.HolHom.valR_spMap _ χ U₀ hχ, GlobalTheory.HolHom.valR_eq _ U₀ hηU, map_pow, ← GlobalTheory.HolHom.valR_eq _ U₀ hηU]
    exact ((GlobalTheory.ArcLie.le_basicOpen_iff_isUnit _ hηU s).1 hηs).pow _
  have kη := key _ _ hηs
  rw [GlobalTheory.HolHom.valR_spMap _ χ U₀ hχ, GlobalTheory.HolHom.valR_spMap _ χ U₀ hχ, valR_eq_ev _ W₀ h] at kη
  have hH : valR χ U₀ (s ^ (n + 1)) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hu
    exact not_isUnit_zero hu
  obtain ⟨T₁, h₁⟩ := harc U₀ (t * s) hχ
  obtain ⟨T₂, h₂⟩ := harc U₀ (s ^ (n + 1)) hχ
  obtain ⟨T₃, C, h₃⟩ := hbd
  obtain ⟨Q, hQ⟩ := GlobalTheory.T.nomePowerSeries_dvd_of_sum_bounded (valR χ U₀ (t * s)) (valR χ U₀ (s ^ (n + 1))) (max T₁ (max T₂ T₃)) C
    (fun w => valAt' (y w) U₀ (t * s)) (fun w => valAt' (y w) U₀ (s ^ (n + 1))) hH (fun w hw => by
      have hw1 : T₁ < w.im := lt_of_le_of_lt (le_max_left _ _) hw
      have hw2 : T₂ < w.im := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hw
      have hw3 : T₃ < w.im := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hw
      obtain ⟨hyU, hG⟩ := h₁ w hw1
      obtain ⟨-, hH'⟩ := h₂ w hw2
      refine ⟨hG, hH', fun hne => ?_⟩
      have hys : ⊤ ≤ y w ⁻¹ᵁ X.basicOpen s := by
        rw [GlobalTheory.HolHom.le_basicOpen_iff (y w) hyU s]
        intro h0
        apply hne
        rw [GlobalTheory.HolHom.valAt'_eq_valR, GlobalTheory.HolHom.valR_eq _ _ hyU, map_pow]
        rw [GlobalTheory.HolHom.valAt'_eq_valR, GlobalTheory.HolHom.valR_eq _ _ hyU] at h0
        rw [h0, zero_pow (Nat.succ_ne_zero n)]
      have hyW : ⊤ ≤ y w ⁻¹ᵁ W₀ := GlobalTheory.FlagMod.le_preimage_mono hsW hys
      show ‖valR (y w) U₀ (t * s)‖ ≤ C * ‖valR (y w) U₀ (s ^ (n + 1))‖
      rw [key ℂ (y w) hys, valR_eq_ev (y w) W₀ hyW, norm_mul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (h₃ w hw3 hyW) (norm_nonneg _))
  rw [hQ, map_mul] at kη
  exact ⟨Q, hu.mul_left_cancel kη⟩

end GlobalTheory.ArcReg
end
end
