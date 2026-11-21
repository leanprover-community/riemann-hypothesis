import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.InvInvSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.MeasOrbSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.UnfoldAbs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Unimod
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.HformSmulRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FinTheta
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoMeas
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoClose

section
noncomputable section

namespace PI.VolStabSW

open MeasureTheory Set
open scoped ENNReal Pointwise

section Abs2

variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
  [MulAction G Y]

theorem lint_fibre {Γ H : Subgroup G} [Countable Γ] (μ' : Measure H) [μ'.IsMulLeftInvariant]
    [μ'.IsInvInvariant] (y0 : Y) (hH : ∀ k : G, k ∈ H ↔ k • y0 = y0) [Countable (orbS Γ y0)]
    {A : Set G} (hA : MeasurableSet A)
    (𝓕' : Set H) (h𝓕' : IsFundamentalDomain ((Γ ⊓ H).subgroupOf H) 𝓕' μ')
    (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (hρi : ∀ γ ∈ Γ, ∀ g, ρ (γ * g) = ρ g) (s : G) :
    ∫⁻ k, cfun Γ A y0 (s * (k : G)) * ρ ((s * (k : G))⁻¹) ∂μ' =
      ∫⁻ k in 𝓕', cntN Γ A ((k : G) * s⁻¹) * ρ ((k : G) * s⁻¹) ∂μ' := by
  haveI : Countable ((Γ ⊓ H).subgroupOf H) := countable_subgroupOf
  have memΓ : ∀ δ : (Γ ⊓ H).subgroupOf H, ((δ : H) : G) ∈ Γ := fun δ =>
    (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 δ.2)).1
  have h1 : ∀ (δ : (Γ ⊓ H).subgroupOf H) (k : H),
      cfun Γ A y0 (s * (((δ • k)⁻¹ : H) : G)) * ρ ((s * (((δ • k)⁻¹ : H) : G))⁻¹) =
        (∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞))
          (repO Γ y0 x * ((δ : H) : G) * ((k : G) * s⁻¹))) * ρ ((k : G) * s⁻¹) := by
    intro δ k
    have e : (((δ • k)⁻¹ : H) : G) = (k : G)⁻¹ * ((δ : H) : G)⁻¹ := by
      show ((((δ : H) * k)⁻¹ : H) : G) = _
      rw [Subgroup.coe_inv, Subgroup.coe_mul, mul_inv_rev]
    rw [e]
    have eρ : ρ ((s * ((k : G)⁻¹ * ((δ : H) : G)⁻¹))⁻¹) = ρ ((k : G) * s⁻¹) := by
      rw [show (s * ((k : G)⁻¹ * ((δ : H) : G)⁻¹))⁻¹ = ((δ : H) : G) * ((k : G) * s⁻¹) by group]
      exact hρi _ (memΓ δ) _
    rw [eρ]
    congr 1
    unfold cfun
    refine tsum_congr fun x => ?_
    congr 1
    group
  have hm : ∀ δ : (Γ ⊓ H).subgroupOf H, Measurable fun k : H =>
      (∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞))
          (repO Γ y0 x * ((δ : H) : G) * ((k : G) * s⁻¹))) * ρ ((k : G) * s⁻¹) := fun δ =>
    (Measurable.ennreal_tsum fun _ => (measurable_const.indicator hA).comp
      ((measurable_const_mul _).comp ((measurable_mul_const _).comp measurable_subtype_coe))).mul
      (hρ.comp ((measurable_mul_const _).comp measurable_subtype_coe))
  calc ∫⁻ k, cfun Γ A y0 (s * (k : G)) * ρ ((s * (k : G))⁻¹) ∂μ'
      = ∫⁻ k, cfun Γ A y0 (s * ((k⁻¹ : H) : G)) * ρ ((s * ((k⁻¹ : H) : G))⁻¹) ∂μ' :=
        (lintegral_inv_eq_self
          (fun k : H => cfun Γ A y0 (s * (k : G)) * ρ ((s * (k : G))⁻¹))).symm
    _ = ∑' δ : (Γ ⊓ H).subgroupOf H, ∫⁻ k in 𝓕',
          cfun Γ A y0 (s * (((δ • k)⁻¹ : H) : G)) * ρ ((s * (((δ • k)⁻¹ : H) : G))⁻¹) ∂μ' :=
        h𝓕'.lintegral_eq_tsum'' _
    _ = ∑' δ : (Γ ⊓ H).subgroupOf H, ∫⁻ k in 𝓕',
          (∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞))
            (repO Γ y0 x * ((δ : H) : G) * ((k : G) * s⁻¹))) * ρ ((k : G) * s⁻¹) ∂μ' :=
        tsum_congr fun δ => lintegral_congr fun k => h1 δ k
    _ = ∫⁻ k in 𝓕', ∑' δ : (Γ ⊓ H).subgroupOf H,
          (∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞))
            (repO Γ y0 x * ((δ : H) : G) * ((k : G) * s⁻¹))) * ρ ((k : G) * s⁻¹) ∂μ' :=
        (lintegral_tsum fun δ => (hm δ).aemeasurable).symm
    _ = ∫⁻ k in 𝓕', cntN Γ A ((k : G) * s⁻¹) * ρ ((k : G) * s⁻¹) ∂μ' := by
        refine lintegral_congr fun k => ?_
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_comm]
        congr 1
        exact sum_rep_eq y0 hH (fun g => A.indicator (fun _ => (1 : ℝ≥0∞)) (g * ((k : G) * s⁻¹)))

end Abs2

end PI.VolStabSW
end
end

section
noncomputable section

namespace PI.VolStabSW

open MeasureTheory Set
open scoped ENNReal Pointwise

section Abs3

variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
  [MulAction G Y] [MeasurableSpace Y]

theorem unfold_abs {Γ H : Subgroup G} [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (μ' : Measure H) [μ'.IsMulLeftInvariant] [μ'.IsInvInvariant]
    (y0 : Y) (hH : ∀ k : G, k ∈ H ↔ k • y0 = y0)
    (ν : Measure Y) (Φ : Y → ℝ≥0∞) (hΦ : AEMeasurable Φ ν)
    (hΨ : Measurable fun g : G => Φ (g • y0))
    (hcov : ν {y | ¬ ∃ g : G, g • y0 = y} = 0)
    (hcomp : ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : Y → G,
      (∀ y, (∃ g : G, g • y0 = y) → s y • y0 = y) →
      ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ k, f (s y * (k : G)) ∂μ' ∂ν)
    (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (𝓕' : Set H) (h𝓕' : IsFundamentalDomain ((Γ ⊓ H).subgroupOf H) 𝓕' μ') :
    ∫⁻ h in 𝓕, ∑' x : orbS Γ y0, Φ (h⁻¹ • (x : Y)) ∂μ = μ' 𝓕' * ∫⁻ y, Φ y ∂ν := by
  classical
  have hsub : orbS Γ y0 ⊆ Set.range (fun γ : Γ => (γ : G) • y0) := by
    rintro x ⟨γ, hγ, e⟩
    exact ⟨⟨γ, hγ⟩, e⟩
  have hcO : Countable (orbS Γ y0) :=
    ((Set.countable_range fun γ : Γ => (γ : G) • y0).mono hsub).to_subtype
  obtain ⟨A, hA𝓕, hAm, hAe⟩ := h𝓕.nullMeasurableSet.exists_measurable_subset_ae_eq
  have hA : IsFundamentalDomain Γ A μ := fd_of_subset h𝓕 hA𝓕 hAm (ae_eq_set.1 hAe).2
  have hNm : Measurable (cntN Γ A) := meas_cntN Γ hAm
  have hcm : Measurable (cfun Γ A y0) := meas_cfun Γ y0 hAm
  have hN1 : ∀ᵐ g ∂μ, cntN Γ A g⁻¹ = 1 := by
    have h0 : μ {g | cntN Γ A g ≠ 1} = 0 := measure_eq_zero_iff_ae_notMem.2 (by
      filter_upwards [fd_count_ae hA] with g hg
      exact fun h => h hg)
    have h0' : μ (Inv.inv ⁻¹' {g | cntN Γ A g ≠ 1}) = 0 := by
      rw [Measure.measure_preimage_inv]; exact h0
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0'] with g hg
    by_contra h
    exact hg h

  have step1 : ∫⁻ h in 𝓕, ∑' x : orbS Γ y0, Φ (h⁻¹ • (x : Y)) ∂μ =
      ∫⁻ g, Φ (g • y0) * cfun Γ A y0 g ∂μ := by
    rw [setLIntegral_congr hAe.symm, ← lintegral_indicator hAm, ← lintegral_inv_eq_self]
    have hpt : ∀ g : G, A.indicator (fun h => ∑' x : orbS Γ y0, Φ (h⁻¹ • (x : Y))) g⁻¹ =
        ∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞)) g⁻¹ *
          Φ ((g * repO Γ y0 x) • y0) := by
      intro g
      by_cases hg : g⁻¹ ∈ A
      · simp only [indicator_of_mem hg, one_mul, inv_inv]
        refine tsum_congr fun x => ?_
        rw [mul_smul, repO_smul]
      · simp only [indicator_of_notMem hg, zero_mul, tsum_zero]
    have hmx : ∀ x : orbS Γ y0, Measurable fun g : G =>
        A.indicator (fun _ => (1 : ℝ≥0∞)) g⁻¹ * Φ ((g * repO Γ y0 x) • y0) := fun x =>
      ((measurable_const.indicator hAm).comp measurable_inv).mul
        (hΨ.comp (measurable_mul_const _))
    have hmx' : ∀ x : orbS Γ y0, Measurable fun g : G =>
        A.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * g⁻¹) * Φ (g • y0) := fun x =>
      ((measurable_const.indicator hAm).comp ((measurable_const_mul _).comp measurable_inv)).mul hΨ
    calc ∫⁻ g, A.indicator (fun h => ∑' x : orbS Γ y0, Φ (h⁻¹ • (x : Y))) g⁻¹ ∂μ
        = ∑' x : orbS Γ y0, ∫⁻ g, A.indicator (fun _ => (1 : ℝ≥0∞)) g⁻¹ *
            Φ ((g * repO Γ y0 x) • y0) ∂μ := by
          rw [lintegral_congr hpt, lintegral_tsum fun x => (hmx x).aemeasurable]
      _ = ∑' x : orbS Γ y0, ∫⁻ g, A.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * g⁻¹) *
            Φ (g • y0) ∂μ := by
          refine tsum_congr fun x => ?_
          rw [← lint_mul_right (μ := μ) (fun g => A.indicator (fun _ => (1 : ℝ≥0∞))
            (repO Γ y0 x * g⁻¹) * Φ (g • y0)) (repO Γ y0 x)]
          refine lintegral_congr fun g => ?_
          simp only [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
      _ = ∫⁻ g, ∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * g⁻¹) *
            Φ (g • y0) ∂μ := (lintegral_tsum fun x => (hmx' x).aemeasurable).symm
      _ = ∫⁻ g, Φ (g • y0) * cfun Γ A y0 g ∂μ := by
          refine lintegral_congr fun g => ?_
          rw [ENNReal.tsum_mul_right, mul_comm]
          rfl

  let s : Y → G := fun y => if h : ∃ g : G, g • y0 = y then h.choose else 1
  have hs : ∀ y, (∃ g : G, g • y0 = y) → s y • y0 = y := fun y h => by
    simp only [s, dif_pos h]; exact h.choose_spec
  have hΨs : ∀ y, (∃ g : G, g • y0 = y) → ∀ k : H, Φ ((s y * (k : G)) • y0) = Φ y :=
    fun y h k => by rw [mul_smul, (hH _).1 k.2, hs y h]
  have hOrb : ∀ᵐ y ∂ν, ∃ g : G, g • y0 = y := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hcov] with y hy
    by_contra h
    exact hy h
  have hmk : ∀ s0 : G, Measurable fun k : H => s0 * (k : G) :=
    fun s0 => (measurable_const_mul s0).comp measurable_subtype_coe

  let ρ1 : G → ℝ≥0∞ := {g | cntN Γ A g = 1}.indicator (fun _ => 1)
  have hρ1m : Measurable ρ1 := measurable_const.indicator (hNm (measurableSet_singleton 1))
  have hρ1i : ∀ γ ∈ Γ, ∀ g, ρ1 (γ * g) = ρ1 g := by
    intro γ hγ g
    simp only [ρ1, Set.indicator, Set.mem_setOf_eq, cntN_mul Γ A hγ]
  have upper : ∫⁻ g, Φ (g • y0) * cfun Γ A y0 g ∂μ ≤ μ' 𝓕' * ∫⁻ y, Φ y ∂ν := by
    have e1 : ∫⁻ g, Φ (g • y0) * cfun Γ A y0 g ∂μ =
        ∫⁻ g, Φ (g • y0) * cfun Γ A y0 g * ρ1 g⁻¹ ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hN1] with g hg
      simp [ρ1, hg]
    rw [e1, hcomp (fun g => Φ (g • y0) * cfun Γ A y0 g * ρ1 g⁻¹)
      ((hΨ.mul hcm).mul (hρ1m.comp measurable_inv)) s hs]
    calc ∫⁻ y, ∫⁻ k, Φ ((s y * (k : G)) • y0) * cfun Γ A y0 (s y * (k : G)) *
            ρ1 (s y * (k : G))⁻¹ ∂μ' ∂ν
        ≤ ∫⁻ y, Φ y * μ' 𝓕' ∂ν := by
          refine lintegral_mono_ae ?_
          filter_upwards [hOrb] with y hy
          simp only [hΨs y hy, mul_assoc]
          rw [lintegral_const_mul (Φ y) (f := fun k : H => cfun Γ A y0 (s y * (k : G)) * ρ1 (s y * (k : G))⁻¹)
            ((hcm.comp (hmk _)).mul (hρ1m.comp (measurable_inv.comp (hmk _))))]
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          rw [lint_fibre μ' y0 hH hAm 𝓕' h𝓕' ρ1 hρ1m hρ1i (s y)]
          calc ∫⁻ k in 𝓕', cntN Γ A ((k : G) * (s y)⁻¹) * ρ1 ((k : G) * (s y)⁻¹) ∂μ'
              ≤ ∫⁻ k in 𝓕', 1 ∂μ' := by
                refine lintegral_mono fun k => ?_
                by_cases hk : cntN Γ A ((k : G) * (s y)⁻¹) = 1
                · simp [ρ1, hk]
                · simp [ρ1, hk]
            _ = μ' 𝓕' := by rw [setLIntegral_const, one_mul]
      _ = μ' 𝓕' * ∫⁻ y, Φ y ∂ν := by rw [lintegral_mul_const'' _ hΦ, mul_comm]

  let ρt : G → ℝ≥0∞ := {g | cntN Γ A g ≠ 1}.indicator (fun _ => ∞)
  have hρtm : Measurable ρt := measurable_const.indicator (hNm (measurableSet_singleton 1).compl)
  have lowerF : ∀ s0 : G, μ' 𝓕' ≤ ∫⁻ k, cfun Γ A y0 (s0 * (k : G)) + ρt (s0 * (k : G))⁻¹ ∂μ' := by
    intro s0
    have hSm : MeasurableSet {k : H | cntN Γ A (s0 * (k : G))⁻¹ ≠ 1} :=
      (hNm.comp (measurable_inv.comp (hmk s0))) (measurableSet_singleton 1).compl
    by_cases hz : μ' {k : H | cntN Γ A (s0 * (k : G))⁻¹ ≠ 1} = 0
    · have hae : ∀ᵐ k : H ∂μ', cntN Γ A ((k : G) * s0⁻¹) = 1 := by
        have h0 : μ' ((Inv.inv : H → H) ⁻¹' {k : H | cntN Γ A (s0 * (k : G))⁻¹ ≠ 1}) = 0 := by
          rw [Measure.measure_preimage_inv]; exact hz
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with k hk
        by_contra h
        apply hk
        show cntN Γ A (s0 * ((k⁻¹ : H) : G))⁻¹ ≠ 1
        rwa [Subgroup.coe_inv, mul_inv_rev, inv_inv]
      calc μ' 𝓕' = ∫⁻ k in 𝓕', 1 ∂μ' := by rw [setLIntegral_const, one_mul]
        _ = ∫⁻ k in 𝓕', cntN Γ A ((k : G) * s0⁻¹) * (fun _ => (1 : ℝ≥0∞)) ((k : G) * s0⁻¹) ∂μ' := by
            refine lintegral_congr_ae (ae_restrict_of_ae ?_)
            filter_upwards [hae] with k hk
            rw [hk, mul_one]
        _ = ∫⁻ k, cfun Γ A y0 (s0 * (k : G)) * (fun _ => (1 : ℝ≥0∞)) ((s0 * (k : G))⁻¹) ∂μ' :=
            (lint_fibre μ' y0 hH hAm 𝓕' h𝓕' (fun _ => 1) measurable_const
              (fun _ _ _ => rfl) s0).symm
        _ ≤ ∫⁻ k, cfun Γ A y0 (s0 * (k : G)) + ρt (s0 * (k : G))⁻¹ ∂μ' :=
            lintegral_mono fun k => by rw [mul_one]; exact le_self_add
    · calc μ' 𝓕' ≤ ⊤ := le_top
        _ = ∫⁻ k, ρt (s0 * (k : G))⁻¹ ∂μ' := by
            rw [show (fun k : H => ρt (s0 * (k : G))⁻¹) =
                {k : H | cntN Γ A (s0 * (k : G))⁻¹ ≠ 1}.indicator (fun _ => ∞) from by
                  funext k; rfl,
              lintegral_indicator_const hSm, ENNReal.top_mul hz]
        _ ≤ _ := lintegral_mono fun k => le_add_self
  have lower : μ' 𝓕' * ∫⁻ y, Φ y ∂ν ≤ ∫⁻ g, Φ (g • y0) * cfun Γ A y0 g ∂μ := by
    have e2 : ∫⁻ g, Φ (g • y0) * cfun Γ A y0 g ∂μ =
        ∫⁻ g, Φ (g • y0) * (cfun Γ A y0 g + ρt g⁻¹) ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hN1] with g hg
      simp [ρt, hg]
    rw [e2, hcomp (fun g => Φ (g • y0) * (cfun Γ A y0 g + ρt g⁻¹))
      (hΨ.mul (hcm.add (hρtm.comp measurable_inv))) s hs]
    calc μ' 𝓕' * ∫⁻ y, Φ y ∂ν = ∫⁻ y, Φ y * μ' 𝓕' ∂ν := by
          rw [lintegral_mul_const'' _ hΦ, mul_comm]
      _ ≤ _ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hOrb] with y hy
          simp only [hΨs y hy]
          rw [lintegral_const_mul (Φ y) (f := fun k : H => cfun Γ A y0 (s y * (k : G)) + ρt (s y * (k : G))⁻¹)
            ((hcm.comp (hmk _)).add (hρtm.comp (measurable_inv.comp (hmk _))))]
          exact mul_le_mul_of_nonneg_left (lowerF (s y)) zero_le
  rw [step1]
  exact le_antisymm upper lower

end Abs3

end PI.VolStabSW
end
end

section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Set
open scoped TensorProduct ENNReal Pointwise

section Inst

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem inclR_comp_sigma :
    (inclR (F := F) (AF F) : E →+* AF F ⊗[F] E).comp (σ : E →+* E) = (sigR (AF F) σ).comp (inclR (F := F) (AF F)) := by
  ext e
  simp [inclR, sigR]

def ratEl (g : GL (Fin M) E) (hg : g ∈ Formalism.UG.UJ (σ : E →+* E) J) : HFinIn (AF F) σ J :=
  ⟨⟨Formalism.UG.bc (inclR (F := F) (AF F)) g, Formalism.UG.P.bc_mem _ _ _ (inclR_comp_sigma σ) J g hg⟩,
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨g, hg, rfl⟩)⟩

def GamA : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J

def ratElA (g : GL (Fin M) E) (hg : g ∈ Formalism.UG.UJ (σ : E →+* E) J) : HA (AF F) σ J :=
  (ratEl σ J g hg : HR (AF F) σ J)

theorem ratElA_mem (g : GL (Fin M) E) (hg : g ∈ Formalism.UG.UJ (σ : E →+* E) J) :
    ratElA σ J g hg ∈ GamA σ J := (ratEl σ J g hg).2

theorem ratElA_smul (g : GL (Fin M) E) (hg : g ∈ Formalism.UG.UJ (σ : E →+* E) J) {a : ℕ}
    (X : Fin a → Fin M → E) :
    ratElA σ J g hg • ratTup (F := F) (AF F) X =
      ratTup (F := F) (AF F) (fun i => (g : Matrix (Fin M) (Fin M) E).mulVec (X i)) := by
  funext i j
  exact (RingHom.map_mulVec (inclR (F := F) (AF F)) (g : Matrix (Fin M) (Fin M) E) (X i) j).symm

instance nontrivAF : Nontrivial (AF F) := by
  haveI : Nontrivial (Ainf F) := by
    first
    | exact inferInstance
    | (haveI : Nonempty (NumberField.InfinitePlace F) := inferInstance; exact Pi.nontrivial)
  first
  | exact inferInstance
  | exact inferInstanceAs (Nontrivial (Ainf F × Af F))
  | exact (Prod.nontrivial_left : Nontrivial (Ainf F × Af F))

theorem ratTup_injective {a : ℕ} : Function.Injective (ratTup (F := F) (E := E) (M := M) (n := a) (AF F)) := by
  intro X X' h
  funext i j
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F (AF F)).injective
    (congrFun (congrFun h i) j)

end Inst

end PI.VolStabSW
end
end

section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Set
open scoped TensorProduct ENNReal Pointwise

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem gram_orbit_equiv {a : ℕ} (X0 : Fin a → Fin M → E)
    (hW : ∀ X : Fin a → Fin M → E, gramE σ J X = gramE σ J X0 →
      ∃ g ∈ Formalism.UG.UJ (σ : E →+* E) J, ∀ i, (g : Matrix (Fin M) (Fin M) E).mulVec (X0 i) = X i) :
    ∃ e : {X : Fin a → Fin M → E | gramE σ J X = gramE σ J X0} ≃
        orbS (GamA σ J) (ratTup (F := F) (AF F) X0),
      ∀ X, (e X : Fin a → Fin M → AF F ⊗[F] E) = ratTup (F := F) (AF F) (X : Fin a → Fin M → E) := by
  let f : {X : Fin a → Fin M → E | gramE σ J X = gramE σ J X0} →
      orbS (GamA σ J) (ratTup (F := F) (AF F) X0) := fun X =>
    ⟨ratTup (F := F) (AF F) (X : Fin a → Fin M → E), by
      obtain ⟨g, hg, hgX⟩ := hW X X.2
      refine ⟨ratElA σ J g hg, ratElA_mem σ J g hg, ?_⟩
      rw [ratElA_smul]
      congr 1
      funext i
      exact hgX i⟩
  have hinj : Function.Injective f := fun X X' h =>
    Subtype.ext (ratTup_injective (congrArg Subtype.val h))
  have hsurj : Function.Surjective f := by
    rintro ⟨x, ⟨γ, hγ, rfl⟩⟩
    obtain ⟨g, hg, hgγ⟩ := Subgroup.mem_map.1
      (Subgroup.mem_subgroupOf.1 (show (show HR (AF F) σ J from γ) ∈ HFinIn (AF F) σ J from hγ))
    have hγe : γ = ratElA σ J g hg := Subtype.ext hgγ.symm
    have hg' : Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J *
        (g : Matrix (Fin M) (Fin M) E) = J := hg
    refine ⟨⟨fun i => (g : Matrix (Fin M) (Fin M) E).mulVec (X0 i), ?_⟩, ?_⟩
    · show gramE σ J _ = gramE σ J X0
      ext i j
      show Formalism.UG.hform (σ : E →+* E) J _ _ = Formalism.UG.hform (σ : E →+* E) J _ _
      rw [Formalism.UG.P.hform_mulVec, hg']
    · apply Subtype.ext
      show ratTup (F := F) (AF F) _ = γ • ratTup (F := F) (AF F) X0
      rw [hγe, ratElA_smul]
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun X => rfl⟩

end Main

section Of

theorem unfold_of (hW : Witt) (hFT : FinTheta) (hI : InvInv) (hMO : MeasOrb) (hMG : MeasGrp) :
    Unfold := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν μ' hμ'H hμ'C
    𝓕' h𝓕' φ hφ0 hadm hθ
  haveI : MeasurableMul (HA (AF F) σ J) := (hMG F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).1
  haveI : MeasurableInv (HA (AF F) σ J) := (hMG F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).2
  haveI : μ.IsHaarMeasure := hμ
  haveI : μ'.IsHaarMeasure := hμ'H
  haveI : μ.IsInvInvariant := (hI F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).1 μ hμ
  haveI : μ'.IsInvInvariant :=
    (hI F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet).2 ψ hψ μ hμ νX hν μ' hμ'H hμ'C
  haveI : Countable (HFinIn (AF F) σ J) := um_countable_HFinIn F E σ M J
  haveI hΓc : Countable (GamA σ J) := um_countable_HFinIn F E σ M J
  obtain ⟨e, he⟩ := gram_orbit_equiv σ J X0 (hW F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet)
  have hsub : orbS (GamA σ J) (ratTup (F := F) (AF F) X0) ⊆
      Set.range (fun γ : (GamA σ J) =>
        (γ : HA (AF F) σ J) • ratTup (F := F) (AF F) X0) := by
    rintro x ⟨γ, hγ, e⟩
    exact ⟨⟨γ, hγ⟩, e⟩
  haveI hcO : Countable (orbS (GamA σ J)
      (ratTup (F := F) (AF F) X0)) := ((Set.countable_range _).mono hsub).to_subtype
  have hmφ : Measurable fun g : HA (AF F) σ J => φ (g • ratTup (F := F) (AF F) X0) := by
    have := hMO F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet _ hadm
    have h2 := Complex.measurable_re.comp this
    simp only [Function.comp_def, Complex.ofReal_re] at h2
    exact h2
  have hint : Integrable (fun X => (φ X : ℂ)) νX := by
    obtain ⟨d, b, Φinf, Φf, Φv, h1, h2, h3, h4⟩ := id hadm
    obtain ⟨⟨μinf, hμinf⟩, k1⟩ := hν.2
    obtain ⟨⟨νinf, hνinf⟩, k2⟩ := k1 μinf hμinf
    obtain ⟨⟨μv, hμv⟩, k3⟩ := k2 νinf hνinf
    obtain ⟨⟨νv, hνv⟩, k4⟩ := k3 μv hμv
    obtain ⟨⟨fI, hfI⟩, k5⟩ := k4 νv hνv
    obtain ⟨⟨fV, hfV⟩, k6⟩ := k5 fI hfI
    exact (k6 fV hfV d b _ Φinf Φf Φv h1 h2 h3 h4).1
  have hφae : AEMeasurable φ νX := by
    have h2 := Complex.measurable_re.comp_aemeasurable hint.aestronglyMeasurable.aemeasurable
    simp only [Function.comp_def, Complex.ofReal_re] at h2
    exact h2
  have key : ∫⁻ h in 𝓕, ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) ∂μ =
      μ' 𝓕' * ∫⁻ X, ENNReal.ofReal (φ X) ∂νX :=
    unfold_abs (Γ := GamA σ J) (H := stabT (AF F) σ J X0) μ μ' (ratTup (F := F) (AF F) X0) (fun k => MulAction.mem_stabilizer_iff) νX
      (fun X => ENNReal.ofReal (φ X)) hφae.ennreal_ofReal hmφ.ennreal_ofReal hμ'C.1 hμ'C.2 𝓕 h𝓕 𝓕' h𝓕'
  have hθS : ∀ h : HA (AF F) σ J, ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) =
      ∑' X : {X : Fin a → Fin M → E | gramE σ J X = gramE σ J X0},
        ENNReal.ofReal (φ (h⁻¹ • ratTup (F := F) (AF F) (X : Fin a → Fin M → E))) := by
    intro h
    rw [← e.tsum_eq (fun x => ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))))]
    exact tsum_congr fun X => by rw [he X]
  have hfin : ∀ h : HA (AF F) σ J, ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) ≠ ⊤ := by
    intro h
    have hF := hFT F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet (fun X => (φ X : ℂ)) hadm h
    rw [hθS h]
    refine ENNReal.tsum_coe_ne_top_iff_summable.2 (summable_of_finite_support ?_)
    refine (hF.preimage Subtype.val_injective.injOn).subset ?_
    intro X hX
    simp only [Function.mem_support, ne_eq, Real.toNNReal_eq_zero, not_le] at hX
    show (φ _ : ℂ) ≠ 0
    exact Complex.ofReal_ne_zero.2 hX.ne'
  have hθm : Measurable fun h : HA (AF F) σ J => ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) := by
    refine Measurable.ennreal_tsum fun x => ?_
    have hx : (fun h : HA (AF F) σ J => ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E)))) =
        fun h => ENNReal.ofReal (φ ((h⁻¹ * repO _ _ x) • ratTup (F := F) (AF F) X0)) := by
      funext h
      rw [mul_smul, repO_smul]
    rw [hx]
    exact (hmφ.comp (measurable_inv.mul_const _)).ennreal_ofReal
  have hθeq : ∀ h, thetaS F E σ M J (fun X => (φ X : ℂ)) {X | gramE σ J X = gramE σ J X0} h =
      (((∑' x : orbS (GamA σ J) (ratTup (F := F) (AF F) X0),
        ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E)))).toReal : ℝ) : ℂ) := by
    intro h
    unfold thetaS
    rw [← Complex.ofReal_tsum, hθS h, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    congr 1
    exact tsum_congr fun X => (ENNReal.toReal_ofReal (hφ0 _)).symm
  have hI1 : ∫ h in 𝓕, thetaS F E σ M J (fun X => (φ X : ℂ)) {X | gramE σ J X = gramE σ J X0} h ∂μ =
      (((∫⁻ h in 𝓕, ∑' x : orbS (GamA σ J)
        (ratTup (F := F) (AF F) X0), ENNReal.ofReal (φ (h⁻¹ • (x : Fin a → Fin M → AF F ⊗[F] E))) ∂μ).toReal
          : ℝ) : ℂ) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hθeq), integral_complex_ofReal,
      integral_toReal hθm.aemeasurable (Filter.Eventually.of_forall fun h => (hfin h).lt_top)]
  have hI2 : ∫ X, (φ X : ℂ) ∂νX = (((∫⁻ X, ENNReal.ofReal (φ X) ∂νX).toReal : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hφ0)
      hφae.aestronglyMeasurable]
  rw [hI1] at hθ ⊢
  rw [hI2, key]
  rw [key] at hθ
  have hL0 : (μ' 𝓕' * ∫⁻ X, ENNReal.ofReal (φ X) ∂νX).toReal ≠ 0 := fun h0 => hθ (by rw [h0]; simp)
  have hR0 : ∫⁻ X, ENNReal.ofReal (φ X) ∂νX ≠ 0 := fun h => hL0 (by simp [h])
  have hμ'top : μ' 𝓕' ≠ ⊤ := fun h => hL0 (by rw [h, ENNReal.top_mul hR0]; simp)
  refine ⟨hμ'top, ?_⟩
  rw [ENNReal.toReal_mul, Complex.ofReal_mul, Complex.real_smul]

end Of

end PI.VolStabSW
end
end

section
noncomputable section

namespace PI.VolStabSW

open MeasureTheory Measure Topology Set Function
open scoped Pointwise ENNReal NNReal

section Gen

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem us_exists_open (μ : Measure G) [IsHaarMeasure μ] :
    ∃ U : Set G, IsOpen U ∧ (1 : G) ∈ U ∧ U⁻¹ = U ∧ 0 < μ U ∧ μ U < ⊤ := by
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : G)
  set U := interior V ∩ (interior V)⁻¹ with hUdef
  have h1 : (1 : G) ∈ U := ⟨mem_interior_iff_mem_nhds.2 hV1,
    by rw [Set.mem_inv, inv_one]; exact mem_interior_iff_mem_nhds.2 hV1⟩
  have hUo : IsOpen U := isOpen_interior.inter isOpen_interior.inv
  refine ⟨U, hUo, h1, ?_, hUo.measure_pos μ ⟨1, h1⟩, ?_⟩
  · rw [hUdef, Set.inter_inv, inv_inv, inter_comm]
  · exact lt_of_le_of_lt (measure_mono (inter_subset_left.trans interior_subset))
      hVc.measure_lt_top

theorem us_invInv [SigmaCompactSpace G] (μ : Measure G) [IsHaarMeasure μ]
    [IsMulRightInvariant μ] : IsInvInvariant μ := by
  have hc : μ.inv = haarScalarFactor μ.inv μ • μ := um_eq_smul_of_sigmaCompact _ _
  obtain ⟨U, hUo, -, hUi, hpos, hfin⟩ := us_exists_open μ
  have h : μ.inv U = μ U := by rw [Measure.inv_apply, hUi]
  rw [hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
  have hc1 : haarScalarFactor μ.inv μ = 1 := by
    have : ((haarScalarFactor μ.inv μ : ℝ≥0) : ℝ≥0∞) = 1 := by
      rw [← ENNReal.mul_left_inj hpos.ne' hfin.ne, one_mul]
      exact h
    exact_mod_cast this
  exact ⟨by rw [hc, hc1, one_smul]⟩

theorem us_rightInv_of_compat (μ : Measure G) [IsHaarMeasure μ] [IsMulRightInvariant μ]
    {S : Type*} [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [LocallyCompactSpace S]
    [T2Space S] [MeasurableSpace S] [BorelSpace S] [SigmaCompactSpace S] (ι : S →* G)
    (μ' : Measure S) [IsHaarMeasure μ'] {Y : Type*} [MeasurableSpace Y] (νX : Measure Y)
    (s : Y → G)
    (hcompat : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h', f (s y * ι h') ∂μ' ∂νX) :
    IsMulRightInvariant μ' := by
  obtain ⟨U, hUo, -, -, hpos, hfin⟩ := us_exists_open μ
  set f : G → ℝ≥0∞ := U.indicator 1 with hfdef
  have hfm : Measurable f := measurable_one.indicator hUo.measurableSet
  have hI : ∫⁻ g, f g ∂μ = μ U := lintegral_indicator_one hUo.measurableSet
  refine ⟨fun k => ?_⟩
  set c := haarScalarFactor (map (· * k) μ') μ' with hcdef
  have hc : map (· * k) μ' = c • μ' := um_eq_smul_of_sigmaCompact _ _
  have h1 := hcompat (fun g => f (g * ι k)) (hfm.comp (measurable_mul_const _))
  rw [lintegral_mul_right_eq_self f (ι k)] at h1
  have hin : ∀ y, ∫⁻ h', f (s y * ι h' * ι k) ∂μ' = c * ∫⁻ h', f (s y * ι h') ∂μ' := by
    intro y
    have e1 : (fun h' => f (s y * ι h' * ι k)) = fun h' => f (s y * ι (h' * k)) := by
      funext h'
      rw [map_mul, mul_assoc]
    rw [e1]
    have e2 := lintegral_map_equiv (μ := μ') (fun h' => f (s y * ι h')) (MeasurableEquiv.mulRight k)
    have e3 : (⇑(MeasurableEquiv.mulRight k) : S → S) = (· * k) := rfl
    rw [e3, hc, lintegral_smul_measure] at e2
    rw [← e2]
    rfl
  simp_rw [hin] at h1
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← hcompat f hfm, hI] at h1
  have hc1 : c = 1 := by
    have : (c : ℝ≥0∞) = 1 := by
      rw [← ENNReal.mul_left_inj hpos.ne' hfin.ne, one_mul]
      exact h1.symm
    exact_mod_cast this
  rw [hc, hc1, one_smul]

end Gen

section Spec

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.VolFromSW PI.AdicCompletionValuation NumberField
open scoped TensorProduct

theorem us_isClosed_stab (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] (σ : E →ₐ[F] E) (M a : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (X0 : Fin a → Fin M → E) :
    IsClosed ((stabT (AF F) σ J X0 : Subgroup (HA (AF F) σ J)) : Set (HA (AF F) σ J)) := by
  have hcont : Continuous fun g : HA (AF F) σ J => g • ratTup (F := F) (AF F) X0 := by
    show Continuous fun g : HA (AF F) σ J =>
      actTup (AF F) (HA.mat (AF F) σ J g) (ratTup (F := F) (AF F) X0)
    unfold actTup HA.mat
    refine continuous_pi fun b => Continuous.matrix_mulVec ?_ continuous_const
    exact Units.continuous_val.comp
      (continuous_subtype_val : Continuous fun g : HR (AF F) σ J => (g : GL (Fin M) (AF F ⊗[F] E)))
  have : ((stabT (AF F) σ J X0 : Subgroup (HA (AF F) σ J)) : Set (HA (AF F) σ J)) =
      {g | g • ratTup (F := F) (AF F) X0 = ratTup (F := F) (AF F) X0} := by
    ext g
    exact MulAction.mem_stabilizer_iff
  rw [this]
  exact isClosed_eq hcont continuous_const

def InvG : Prop := InCtx fun F E _ _ _ _ _ σ M J _a _X0 _hT =>
  ∀ μ, IsHaarH F E σ M J μ → μ.IsInvInvariant

def InvS : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μ, IsHaarH F E σ M J μ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
    ∀ μ' : Measure (stabT (AF F) σ J X0), μ'.IsHaarMeasure → IsCompatT F E σ M J X0 μ μ' νX →
      μ'.IsInvInvariant

theorem unimodStab_holds : UnimodStab := by
  intro F E _ _ _ _ _ σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet ψ _ μ hμ νX _ μ' hμ' hC
  classical
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have : μ.IsHaarMeasure := hμ
  have : SigmaCompactSpace (HA (AF F) σ J) := um_sigmaCompact_HA F E σ M J hSWa1
  have : IsMulRightInvariant μ :=
    unimod_holds F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet μ hμ
  have hcl := us_isClosed_stab F E σ M a J X0
  have : LocallyCompactSpace (stabT (AF F) σ J X0) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SigmaCompactSpace (stabT (AF F) σ J X0) := hcl.sigmaCompactSpace
  let s : (Fin a → Fin M → AF F ⊗[F] E) → HA (AF F) σ J := fun y =>
    if h : ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) X0 = y then h.choose else 1
  have hs : ∀ y, (∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) X0 = y) →
      s y • ratTup (F := F) (AF F) X0 = y := by
    intro y h
    simp only [s, dif_pos h]
    exact h.choose_spec
  exact us_rightInv_of_compat μ (stabT (AF F) σ J X0).subtype μ' νX s
    (fun f hf => hC.2 f hf s hs)

theorem invG_holds : InvG := by
  intro F E _ _ _ _ _ σ hσ M J hJ hSWa1 hSWc1 _a ha1 ha2 X0 hT hdet μ hμ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have : μ.IsHaarMeasure := hμ
  have : SigmaCompactSpace (HA (AF F) σ J) := um_sigmaCompact_HA F E σ M J hSWa1
  have : IsMulRightInvariant μ :=
    unimod_holds F E σ hσ M J hJ hSWa1 hSWc1 _a ha1 ha2 X0 hT hdet μ hμ
  exact us_invInv μ

theorem invS_holds : InvS := by
  intro F E _ _ _ _ _ σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν μ' hμ' hC
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have : SigmaCompactSpace (HA (AF F) σ J) := um_sigmaCompact_HA F E σ M J hSWa1
  have hcl := us_isClosed_stab F E σ M a J X0
  have : LocallyCompactSpace (stabT (AF F) σ J X0) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SigmaCompactSpace (stabT (AF F) σ J X0) := hcl.sigmaCompactSpace
  have : IsMulRightInvariant μ' :=
    unimodStab_holds F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν μ' hμ' hC
  exact us_invInv μ'

theorem invInv_holds : InvInv := fun F E _ _ _ _ _ σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet =>
  ⟨invG_holds F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet,
    invS_holds F E σ hσ M J hJ hSWa1 hSWc1 a ha1 ha2 X0 hT hdet⟩

end Spec

end PI.VolStabSW
end
end

section
namespace PI.VolStabSW

theorem unfold_holds : Unfold :=
  unfold_of witt_holds finTheta_holds invInv_holds measOrb_holds measGrp_holds

end PI.VolStabSW
end
