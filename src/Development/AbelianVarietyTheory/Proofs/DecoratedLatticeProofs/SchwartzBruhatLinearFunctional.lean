import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzBruhatConvolutionLocalFieldPower
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralScaledBoxPiSupersetOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinsetIntegralScaledBoxPiCosetReps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumIntegralScaledBoxPiCosetRepsShiftInvariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralBoxInvariantEqMeasureRealMulSumReps

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.SliceIntegral

theorem integral_slice_mem_SB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k)
    (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂]
    (Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))) :
    (fun x => ∫ a, Φ.1 (x, 0, a) ∂(Measure.pi fun _ => ν)) ∈ SB (I₀ → k) := by
  haveI := t2Space k
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_,
    HasCompactSupport.intro (IsCompact.image Φ.2.2 continuous_fst) fun x hx => ?_⟩
  · have ht : Filter.Tendsto (fun x' : I₀ → k => ((x - x', (0 : I₁ → k), (0 : I₂ → k)) :
        (I₀ → k) × (I₁ → k) × (I₂ → k))) (𝓝 x) (𝓝 0) := by
      have hc : Continuous (fun x' : I₀ → k => ((x - x', (0 : I₁ → k), (0 : I₂ → k)) :
          (I₀ → k) × (I₁ → k) × (I₂ → k))) := by fun_prop
      have := hc.tendsto x
      rwa [sub_self, ← Prod.zero_eq_mk, ← Prod.zero_eq_mk] at this
    filter_upwards [ht.eventually (GlobalTheory.SBConv.eventually_translate Φ.2)] with x' hx'
    congr 1
    funext a
    have := hx' (x, 0, a)
    simpa using this
  · have h0 : ∀ a, Φ.1 (x, 0, a) = 0 := fun a =>
      image_eq_zero_of_notMem_tsupport fun h => hx ⟨_, h, rfl⟩
    simp [h0]

end GlobalTheory.SliceIntegral
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_last_factor_slice_mem_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (fun x => ∫ a, Φ.1 (x, 0, a) ∂(Measure.pi fun _ => ν)) ∈ SB (I₀ → k) := by
  atlas_forward_decl GlobalTheory.SliceIntegral.integral_slice_mem_SB
end

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.CharCutoff

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dot_eq_one {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) {n : Type} [Fintype n]
    (R : kˣ) {t y : n → k} (ht : t ∈ box n (c * R⁻¹)) (hy : y ∈ box n R) : ψ (t ⬝ᵥ y) = 1 := by
  apply h.eq_one
  show valuation k (∑ i, t i * y i) ≤ valuation k (c : k)
  refine Valuation.map_sum_le (valuation k) fun i _ => ?_
  have h2 : valuation k (t i * y i) ≤ valuation k (((c * R⁻¹ : kˣ) : k) * R) := by
    rw [map_mul, map_mul]
    exact mul_le_mul' (ht i trivial) (hy i trivial)
  rwa [← Units.val_mul, inv_mul_cancel_right] at h2

theorem exists_dot_ne_one {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) {n : Type} [Fintype n]
    (s : kˣ) {y : n → k} (hy : y ∉ box n s) : ∃ b ∈ box n (c * s⁻¹), ψ (b ⬝ᵥ y) ≠ 1 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, y i ∉ cball s := by
    by_contra hne
    push_neg at hne
    exact hy fun i _ => hne i
  have hcs : c * (c * s⁻¹)⁻¹ = s := by
    rw [_root_.mul_inv_rev, inv_inv, mul_comm s, mul_inv_cancel_left]
  obtain ⟨t, ht, hne⟩ := h.exists_ne_one (c * s⁻¹) (x := y i) (by rwa [hcs])
  refine ⟨Pi.single i t, fun j _ => ?_, ?_⟩
  · by_cases hj : j = i
    · subst hj; simpa using ht
    · simp [Pi.single_eq_of_ne hj, cball]
  · rwa [single_dotProduct]

theorem sum_char {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) {n : Type} [Fintype n]
    (s R : kˣ) (S : Finset (n → k)) (hS : ∀ b ∈ S, b ∈ box n (c * s⁻¹))
    (hU : ∀ a ∈ box n (c * s⁻¹), ∃! b, b ∈ S ∧ a - b ∈ box n (c * R⁻¹)) {y : n → k}
    (hy : y ∈ box n R) :
    ∑ b ∈ S, (ψ (b ⬝ᵥ y) : ℂ) = (box n s).indicator (fun _ => (1 : ℂ)) y * S.card := by
  by_cases hys : y ∈ box n s
  · rw [Set.indicator_of_mem hys, one_mul]
    rw [Finset.sum_congr rfl fun b hb => by rw [dot_eq_one h s (hS b hb) hys, Circle.coe_one]]
    simp
  · rw [Set.indicator_of_notMem hys, zero_mul]
    obtain ⟨a, ha, hne⟩ := exists_dot_ne_one h s hys
    have key := GlobalTheory.T.sum_integralScaledBoxPi_coset_reps_shift_invariant k n (c * R⁻¹) (c * s⁻¹) S hS hU (fun b => (ψ (b ⬝ᵥ y) : ℂ))
      (fun t ht z => by
        rw [add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, dot_eq_one h R ht hy,
          Circle.coe_one, mul_one]) a ha
    simp only [add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, ← Finset.mul_sum] at key
    have h3 : (ψ (a ⬝ᵥ y) : ℂ) - 1 ≠ 0 := fun h4 => hne (Circle.ext (by simpa using sub_eq_zero.mp h4))
    refine (mul_eq_zero.mp ?_).resolve_left h3
    rw [sub_mul, key, one_mul, sub_self]

theorem exists_cutoff_of_char_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) →ₗ[ℂ] M), (∀ (b : I₁ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x) → l Φ' = l Φ) → ∀ (Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))) (s : kˣ), ∃ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)), (∀ x, Φ'.1 x = (box I₁ s).indicator (fun _ => (1 : ℂ)) x.2.1 * Φ.1 x) ∧ l Φ = l Φ' := by
  intro k _ _ _ _ ψ hψ h1 I₀ I₁ I₂ _ _ _ M _ _ l hl Φ s
  haveI := t2Space k
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
  have hK : IsCompact ((fun x : (I₀ → k) × (I₁ → k) × (I₂ → k) => x.2.1) '' tsupport Φ.1) :=
    Φ.2.2.image (by fun_prop)
  obtain ⟨R, hsR, hKR⟩ := GlobalTheory.T.exists_integralScaledBoxPi_superset_of_isCompact k I₁ _ hK s
  have hvr : valuation k ((c * R⁻¹ : kˣ) : k) ≤ valuation k ((c * s⁻¹ : kˣ) : k) := by
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
    exact mul_le_mul' le_rfl (inv_anti₀ (by simp [zero_lt_iff]) hsR)
  obtain ⟨S, hS, hU⟩ := GlobalTheory.T.exists_finset_integralScaledBoxPi_coset_reps k I₁ (c * R⁻¹) (c * s⁻¹) hvr
  have hmem : ∀ b : I₁ → k,
      (fun x : (I₀ → k) × (I₁ → k) × (I₂ → k) => (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x) ∈
        SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) := fun b => by
    have hcont : Continuous fun x : (I₀ → k) × (I₁ → k) × (I₂ → k) => b ⬝ᵥ x.2.1 :=
      continuous_const.dotProduct (continuous_fst.comp continuous_snd)
    have h2 : IsLocallyConstant fun x : (I₀ → k) × (I₁ → k) × (I₂ → k) => (ψ (b ⬝ᵥ x.2.1) : ℂ) :=
      (IsLocallyConstant.comp_continuous hc.isLocallyConstant hcont).comp (fun z : Circle => (z : ℂ))
    exact ⟨IsLocallyConstant.mul h2 Φ.2.1, Φ.2.2.mul_left⟩
  let Φb : (I₁ → k) → SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) := fun b => ⟨_, hmem b⟩
  have hlb : ∀ b, l (Φb b) = l Φ := fun b => hl b Φ (Φb b) (fun x => rfl)
  have h0 : (0 : I₁ → k) ∈ box I₁ (c * s⁻¹) := fun i _ => by simp [cball]
  obtain ⟨b0, ⟨hb0, _⟩, _⟩ := hU 0 h0
  have hcard : (S.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨b0, hb0⟩).ne'
  refine ⟨(S.card : ℂ)⁻¹ • ∑ b ∈ S, Φb b, fun x => ?_, ?_⟩
  · simp only [Submodule.coe_smul, Submodule.coe_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    show (S.card : ℂ)⁻¹ * ∑ b ∈ S, (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x = _
    rw [← Finset.sum_mul]
    by_cases hx : x ∈ tsupport Φ.1
    · rw [sum_char hc s R S hS hU (hKR ⟨x, hx, rfl⟩), ← mul_assoc, mul_comm ((S.card : ℂ)⁻¹),
        mul_inv_cancel_right₀ hcard]
    · rw [image_eq_zero_of_notMem_tsupport hx]; simp
  · rw [map_smul, map_sum, Finset.sum_congr rfl fun b _ => hlb b, Finset.sum_const,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

end GlobalTheory.CharCutoff
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cutoff_of_addChar_translation_invariant_functional : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) →ₗ[ℂ] M), (∀ (b : I₁ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x) → l Φ' = l Φ) → ∀ (Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))) (s : kˣ), ∃ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)), (∀ x, Φ'.1 x = (box I₁ s).indicator (fun _ => (1 : ℂ)) x.2.1 * Φ.1 x) ∧ l Φ = l Φ' := by
  atlas_forward_decl GlobalTheory.CharCutoff.exists_cutoff_of_char_invariant
end

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.SplitWeil.FourierPi

theorem map_eq_zero_of_translation_invariant_of_fibre_integral_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) →ₗ[ℂ] M), (∀ (a : I₂ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = Φ.1 (x + (0, 0, a))) → l Φ' = l Φ) → ∀ Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)), (∀ x₀ x₁, ∫ a, Φ.1 (x₀, x₁, a) ∂(Measure.pi fun _ => ν) = 0) → l Φ = 0 := by
  intro k _ _ _ _ _ _ ν hν I₀ I₁ I₂ _ _ _ M _ _ l hl Φ hΦ
  haveI := secondCountable k
  haveI := hν

  have hU : {t : I₂ → k | ∀ g : (I₀ → k) × (I₁ → k) × (I₂ → k), Φ.1 (g + (0, 0, t)) = Φ.1 g} ∈
      𝓝 (0 : I₂ → k) := by
    have ht : Filter.Tendsto
        (fun t : I₂ → k => ((0, 0, -t) : (I₀ → k) × (I₁ → k) × (I₂ → k))) (𝓝 0) (𝓝 0) := by
      have hc : Continuous
          (fun t : I₂ → k => ((0, 0, -t) : (I₀ → k) × (I₁ → k) × (I₂ → k))) := by fun_prop
      have e : (((0 : I₀ → k), (0 : I₁ → k), -(0 : I₂ → k))) = 0 := by rw [neg_zero]; rfl
      have h := hc.tendsto 0
      rwa [e] at h
    filter_upwards [ht.eventually (GlobalTheory.SBConv.eventually_translate Φ.2)] with t h g
    have := h g
    simpa [sub_eq_add_neg] using this
  obtain ⟨r, hr⟩ := exists_box_subset hU
  have hK : IsCompact ((fun x : (I₀ → k) × (I₁ → k) × (I₂ → k) => x.2.2) '' tsupport Φ.1) :=
    Φ.2.2.isCompact.image (by fun_prop)
  obtain ⟨R, hrR, hKR⟩ := GlobalTheory.T.exists_integralScaledBoxPi_superset_of_isCompact k I₂ _ hK r
  obtain ⟨S, hSR, hS⟩ := GlobalTheory.T.exists_finset_integralScaledBoxPi_coset_reps k I₂ r R hrR
  have h0R : (0 : I₂ → k) ∈ box I₂ R := fun i _ => by simp [cball]
  have h0r : (0 : I₂ → k) ∈ box I₂ r := fun i _ => by simp [cball]
  have hSne : S.Nonempty := by
    obtain ⟨b, ⟨hb, -⟩, -⟩ := hS 0 h0R
    exact ⟨b, hb⟩

  let T : (I₂ → k) → SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) := fun b =>
    ⟨fun x => Φ.1 (x + (0, 0, b)), Φ.2.1.comp_continuous (continuous_add_right _),
      Φ.2.2.comp_homeomorph (Homeomorph.addRight _)⟩
  have hT : ∀ b, l (T b) = l Φ := fun b => hl b Φ (T b) fun _ => rfl

  have hvol : (Measure.pi fun _ : I₂ => ν).real (box I₂ r) ≠ 0 := by
    rw [measureReal_def]
    exact (ENNReal.toReal_pos ((isOpen_box r).measure_ne_zero _ ⟨0, h0r⟩)
      (isCompact_box r).measure_lt_top.ne).ne'
  have hsum : ∑ b ∈ S, T b = 0 := by
    apply Subtype.ext
    funext x
    obtain ⟨x₀, x₁, a⟩ := x
    have hF1 : ∀ t ∈ box I₂ r, ∀ y, Φ.1 (x₀, x₁, y + t) = Φ.1 (x₀, x₁, y) := fun t ht y => by
      have := hr ht (x₀, x₁, y)
      simpa using this
    have hF2 : ∀ y ∉ box I₂ R, Φ.1 (x₀, x₁, y) = 0 := fun y hy =>
      image_eq_zero_of_notMem_tsupport fun hm => hy (hKR ⟨_, hm, rfl⟩)
    have hval : (∑ b ∈ S, T b).1 (x₀, x₁, a) = ∑ b ∈ S, Φ.1 (x₀, x₁, a + b) := by
      rw [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [T]
    rw [hval]
    by_cases ha : a ∈ box I₂ R
    · rw [GlobalTheory.T.sum_integralScaledBoxPi_coset_reps_shift_invariant k I₂ r R S hSR hS (fun y => Φ.1 (x₀, x₁, y)) hF1 a ha]
      have h := GlobalTheory.T.integral_box_invariant_eq_measureReal_mul_sum_reps k ν hν I₂ r R S hSR hS (fun y => Φ.1 (x₀, x₁, y)) hF1 hF2
      rw [hΦ x₀ x₁] at h
      have h' := (mul_eq_zero.mp h.symm).resolve_left (by exact_mod_cast hvol)
      simpa using h'
    · refine Finset.sum_eq_zero fun b hb => hF2 _ fun hab => ha fun i _ => ?_
      have := add_mem_cball (hab i trivial) (neg_mem_cball (hSR b hb i trivial))
      simpa using this
  have hz : (S.card : ℂ) • l Φ = 0 := by
    have h1 : l (∑ b ∈ S, T b) = (S.card : ℂ) • l Φ := by
      rw [map_sum, Finset.sum_congr rfl fun b _ => hT b, Finset.sum_const, Nat.cast_smul_eq_nsmul]
    rw [← h1, hsum, map_zero]
  exact (smul_eq_zero.mp hz).resolve_left (by exact_mod_cast hSne.card_ne_zero)

end GlobalTheory.SplitWeil.FourierPi
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_functional_zero_of_fibre_integral_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) →ₗ[ℂ] M), (∀ (a : I₂ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = Φ.1 (x + (0, 0, a))) → l Φ' = l Φ) → ∀ Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)), (∀ x₀ x₁, ∫ a, Φ.1 (x₀, x₁, a) ∂(Measure.pi fun _ => ν) = 0) → l Φ = 0 := by
  atlas_forward_decl GlobalTheory.SplitWeil.FourierPi.map_eq_zero_of_translation_invariant_of_fibre_integral_eq_zero
end

section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.CoinvSB

theorem isLocallyConstant_indicator_const {X : Type*} [TopologicalSpace X] {U : Set X} (h1 : IsOpen U)
    (h2 : IsClosed U) (c : ℂ) : IsLocallyConstant (U.indicator fun _ => c) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  by_cases hx : x ∈ U
  · filter_upwards [h1.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
  · filter_upwards [h2.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]

theorem kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) →ₗ[ℂ] M), (∀ (b : I₁ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x) → l Φ' = l Φ) → (∀ (a : I₂ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = Φ.1 (x + (0, 0, a))) → l Φ' = l Φ) → ∀ D : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)), (∀ x₀, ∫ a, D.1 (x₀, 0, a) ∂(Measure.pi fun _ => ν) = 0) → l D = 0 := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν I₀ I₁ I₂ _ _ _ M _ _ l h1 h2 D hD
  obtain ⟨s, hs⟩ : ∃ s : kˣ, ∀ t ∈ box I₁ s, ∀ y : (I₀ → k) × (I₁ → k) × (I₂ → k),
      D.1 (y + (0, t, 0)) = D.1 y := by
    have h := GlobalTheory.SBConv.eventually_translate D.2
    have hT : Filter.Tendsto (fun t : I₁ → k => ((0 : I₀ → k), -t, (0 : I₂ → k))) (𝓝 0) (𝓝 0) := by
      have : Continuous (fun t : I₁ → k => ((0 : I₀ → k), -t, (0 : I₂ → k))) := by fun_prop
      exact this.tendsto' 0 0 (by simp)
    obtain ⟨s, hs⟩ := exists_box_subset (hT.eventually h)
    refine ⟨s, fun t ht y => ?_⟩
    have := hs ht y
    simpa [sub_eq_add_neg] using this
  obtain ⟨Φ', hΦ', hl⟩ := GlobalTheory.T.exists_cutoff_of_addChar_translation_invariant_functional k ψ hψc hψ1 I₀ I₁ I₂ M l h1 D s
  have hz : ∀ x₀ x₁, ∫ a, Φ'.1 (x₀, x₁, a) ∂(Measure.pi fun _ => ν) = 0 := by
    intro x₀ x₁
    simp_rw [hΦ']
    by_cases hx : x₁ ∈ box I₁ s
    · have e : ∀ a, D.1 (x₀, x₁, a) = D.1 (x₀, 0, a) := fun a => by
        simpa using hs x₁ hx (x₀, 0, a)
      simp only [Set.indicator_of_mem hx, one_mul, e]
      exact hD x₀
    · simp [Set.indicator_of_notMem hx]
  rw [hl]
  exact GlobalTheory.T.schwartzBruhat_functional_zero_of_fibre_integral_zero k ν hν I₀ I₁ I₂ M l h2 Φ' hz

theorem coinvariants : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) →ₗ[ℂ] M), (∀ (b : I₁ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x) → l Φ' = l Φ) → (∀ (a : I₂ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = Φ.1 (x + (0, 0, a))) → l Φ' = l Φ) → ∃! l₀ : SB (I₀ → k) →ₗ[ℂ] M, ∀ Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)), ∃ Ψ : SB (I₀ → k), (∀ x, Ψ.1 x = ∫ a, Φ.1 (x, 0, a) ∂(Measure.pi fun _ => ν)) ∧ l Φ = l₀ Ψ := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν I₀ I₁ I₂ _ _ _ M _ _ l h1 h2
  haveI := secondCountable k
  haveI := t2Space k
  set μ : Measure (I₂ → k) := Measure.pi fun _ => ν with hμ
  haveI : μ.IsAddHaarMeasure := by rw [hμ]; infer_instance
  set vol : ℝ := μ.real (box I₂ 1) with hvol
  have hvol0 : vol ≠ 0 := by
    refine (ENNReal.toReal_pos ?_ ?_).ne'
    · exact (isOpen_box 1).measure_ne_zero μ ⟨0, fun i _ => by simp [cball]⟩
    · exact (isCompact_box 1).measure_lt_top.ne
  have hlc : ∀ (n : Type) [Fintype n] (c : ℂ), IsLocallyConstant ((box n (1 : kˣ)).indicator fun _ => c) :=
    fun n _ c => isLocallyConstant_indicator_const (isOpen_box 1) (isCompact_box 1).isClosed c
  let σf : SB (I₀ → k) → (I₀ → k) × (I₁ → k) × (I₂ → k) → ℂ := fun Ψ x =>
    Ψ.1 x.1 * ((box I₁ (1 : kˣ)).indicator (fun _ => (1 : ℂ)) x.2.1 *
      (box I₂ (1 : kˣ)).indicator (fun _ => ((vol : ℂ))⁻¹) x.2.2)
  have hσ : ∀ Ψ, σf Ψ ∈ SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) := by
    intro Ψ
    refine ⟨(Ψ.2.1.comp_continuous continuous_fst).mul
      (((hlc I₁ 1).comp_continuous (by fun_prop)).mul ((hlc I₂ _).comp_continuous (by fun_prop))), ?_⟩
    refine HasCompactSupport.intro (Ψ.2.2.prod ((isCompact_box (1 : kˣ)).prod (isCompact_box (1 : kˣ)))) ?_
    intro x hx
    simp only [σf]
    by_cases h0 : x.1 ∈ tsupport Ψ.1
    · by_cases h1' : x.2.1 ∈ box I₁ (1 : kˣ)
      · have h2' : x.2.2 ∉ box I₂ (1 : kˣ) := fun h => hx ⟨h0, h1', h⟩
        simp [Set.indicator_of_notMem h2']
      · simp [Set.indicator_of_notMem h1']
    · simp [image_eq_zero_of_notMem_tsupport h0]
  let σ : SB (I₀ → k) →ₗ[ℂ] SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) :=
    { toFun := fun Ψ => ⟨σf Ψ, hσ Ψ⟩
      map_add' := fun Ψ Ψ' => by
        apply Subtype.ext; funext x; simp only [σf, Submodule.coe_add, Pi.add_apply]; ring
      map_smul' := fun c Ψ => by
        apply Subtype.ext; funext x; simp only [σf, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]; ring }
  have hσv : ∀ Ψ x, (σ Ψ).1 x = σf Ψ x := fun _ _ => rfl
  have hInt : ∀ (Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))) (x : I₀ → k),
      Integrable (fun a => Φ.1 (x, 0, a)) μ := by
    intro Φ x
    refine Continuous.integrable_of_hasCompactSupport (Φ.2.1.continuous.comp (by fun_prop)) ?_
    refine HasCompactSupport.intro (IsCompact.image Φ.2.2 (continuous_snd.comp continuous_snd)) fun a ha => ?_
    exact image_eq_zero_of_notMem_tsupport fun h => ha ⟨_, h, rfl⟩
  have hσi : ∀ Ψ x, ∫ a, (σ Ψ).1 (x, 0, a) ∂μ = Ψ.1 x := by
    intro Ψ x
    simp only [hσv, σf]
    have h0 : (0 : I₁ → k) ∈ box I₁ (1 : kˣ) := fun i _ => by simp [cball]
    simp only [Set.indicator_of_mem h0, one_mul]
    rw [integral_const_mul, integral_indicator_const _ (isOpen_box _).measurableSet]
    rw [← hvol, Complex.real_smul, mul_inv_cancel₀ (by exact_mod_cast hvol0), mul_one]
  refine ⟨l ∘ₗ σ, fun Φ => ⟨⟨_, GlobalTheory.T.integral_last_factor_slice_mem_schwartzBruhat k ν I₀ I₁ I₂ Φ⟩, fun x => rfl, ?_⟩, ?_⟩
  · set Ψ : SB (I₀ → k) := ⟨_, GlobalTheory.T.integral_last_factor_slice_mem_schwartzBruhat k ν I₀ I₁ I₂ Φ⟩
    have hk := kernel k ψ ν hψc hψ1 hν I₀ I₁ I₂ M l h1 h2 (Φ - σ Ψ) (fun x₀ => by
      simp only [Submodule.coe_sub, Pi.sub_apply]
      rw [integral_sub (hInt Φ x₀) (hInt (σ Ψ) x₀), hσi]
      exact sub_self _)
    rw [map_sub, sub_eq_zero] at hk
    simpa using hk
  · intro l₀ hl₀
    ext1 Ψ
    obtain ⟨Ψ', hΨ', hl⟩ := hl₀ (σ Ψ)
    have : Ψ' = Ψ := Subtype.ext (funext fun x => (hΨ' x).trans (hσi Ψ x))
    subst this
    simp [← hl]

end GlobalTheory.CoinvSB
end
end
