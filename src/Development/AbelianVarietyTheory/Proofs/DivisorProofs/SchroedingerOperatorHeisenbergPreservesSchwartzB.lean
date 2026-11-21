import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Mathlib

section
namespace GlobalTheory.PositiveFormRecursion

theorem step (w : ℂ) (h : ‖w - 1‖ < 1/2) : (3/2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have h1 : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
  have h2 : (3/2 : ℝ) ≤ ‖w + 1‖ := by
    have e : (2 : ℂ) = (w + 1) - (w - 1) := by ring
    have h3 : ‖(2 : ℂ)‖ ≤ ‖w + 1‖ + ‖w - 1‖ := by
      rw [e]; exact norm_sub_le _ _
    have h4 : ‖(2 : ℂ)‖ = 2 := by norm_num
    linarith
  rw [h1, norm_mul]
  nlinarith [norm_nonneg (w - 1)]

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ (2 : ℕ) ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z hz
  have key : ∀ n : ℕ, (3/2 : ℝ) ^ n * ‖z - 1‖ ≤ ‖z ^ (2 : ℕ) ^ n - 1‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : z ^ (2 : ℕ) ^ (n + 1) = (z ^ (2 : ℕ) ^ n) ^ 2 := by rw [pow_succ, pow_mul]
      rw [e]
      have hs := step (z ^ (2 : ℕ) ^ n) (hz n)
      calc (3/2 : ℝ) ^ (n + 1) * ‖z - 1‖ = (3/2) * ((3/2) ^ n * ‖z - 1‖) := by ring
        _ ≤ (3/2) * ‖z ^ (2 : ℕ) ^ n - 1‖ := by gcongr
        _ ≤ _ := hs
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / (2 * ‖z - 1‖)) (by norm_num : (1 : ℝ) < 3/2)
  have hn' := (div_lt_iff₀ (by positivity)).mp hn
  have h1 := key n
  have h2 := hz n
  nlinarith

end GlobalTheory.PositiveFormRecursion
end

section
namespace SchrodingerSchwartzBruhat
section
open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.SchrSB

theorem eq_one_of_pow_two_pow_near {z : ℂ} (h : ∀ n : ℕ, ‖z ^ (2 ^ n) - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.PositiveFormRecursion.main
  | exact _root_.GlobalTheory.PositiveFormRecursion.main
  | (apply _root_.GlobalTheory.PositiveFormRecursion.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PositiveFormRecursion.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PositiveFormRecursion.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PositiveFormRecursion.main ..)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLocallyConstant_addChar (ψ : AddChar k ℂ) (hψ : Continuous ψ) : IsLocallyConstant ψ := by
  have hb := IsValuativeTopology.hasBasis_nhds_zero' k
  have hU : ψ ⁻¹' Metric.ball 1 (1 / 2) ∈ nhds (0 : k) :=
    hψ.continuousAt.preimage_mem_nhds (by
      rw [AddChar.map_zero_eq_one]; exact Metric.ball_mem_nhds _ (by norm_num))
  obtain ⟨γ, hγ, hsub⟩ := hb.mem_iff.mp hU
  have hker : ∀ x, ValuativeRel.valuation k x < γ → ψ x = 1 := by
    intro x hx
    have h2 : ∀ n : ℕ, ValuativeRel.valuation k ((2 ^ n : ℕ) • x) < γ := by
      intro n
      induction n with
      | zero => simpa using hx
      | succ n ih =>
        have e : (2 ^ (n + 1) : ℕ) • x = (2 ^ n : ℕ) • x + (2 ^ n : ℕ) • x := by
          rw [pow_succ, mul_two, add_smul]
        rw [e]
        exact Valuation.map_add_lt _ ih ih
    apply eq_one_of_pow_two_pow_near
    intro n
    have h3 : ψ ((2 ^ n : ℕ) • x) ∈ Metric.ball (1 : ℂ) (1 / 2) := hsub (h2 n)
    rw [AddChar.map_nsmul_eq_pow, Metric.mem_ball, dist_eq_norm] at h3
    exact h3
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hn : {y : k | ValuativeRel.valuation k (y - x) < γ} ∈ nhds x := by
    have hc : ContinuousAt (fun y : k => y - x) x := by fun_prop
    exact hc.preimage_mem_nhds (by simpa using hb.mem_of_mem hγ)
  filter_upwards [hn] with y hy
  have e : ψ y = ψ (y - x) * ψ x := by
    rw [← AddChar.map_add_eq_mul]; simp
  rw [e, hker _ hy, one_mul]

theorem schr_mem_SB : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    ∀ {κ : Type} [Fintype κ] (w : (κ → k) × (κ → k)), ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), GlobalTheory.WeilM.schr ψ0 w φ ∈ GlobalTheory.WeilM.SB (κ → k) := by
  intro k _ _ _ _ _ ψ0 hψ κ _ w φ hφ
  obtain ⟨h1, h2⟩ : IsLocallyConstant φ ∧ HasCompactSupport φ := hφ
  have hl := isLocallyConstant_addChar ψ0 hψ
  have hcont : Continuous fun x : κ → k => x ⬝ᵥ w.2 + ⅟(2 : k) * (w.1 ⬝ᵥ w.2) := by
    refine Continuous.add ?_ continuous_const
    exact continuous_id.dotProduct continuous_const
  have hs : HasCompactSupport fun x : κ → k => φ (x + w.1) :=
    h2.comp_homeomorph (Homeomorph.addRight w.1)
  have hf : IsLocallyConstant fun x : κ → k => φ (x + w.1) :=
    h1.comp_continuous (continuous_add_const w.1)
  refine ⟨?_, ?_⟩
  · exact (hl.comp_continuous hcont).mul hf
  · exact HasCompactSupport.mul_left hs

end GlobalTheory.CompanionTheory.SchrSB

end

end SchrodingerSchwartzBruhat
section

open MeasureTheory Matrix

theorem _root_.GlobalTheory.Adopt.schroedingerOperatorHeisenberg_preserves_schwartzBruhat : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    ∀ {κ : Type} [Fintype κ] (w : (κ → k) × (κ → k)), ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), GlobalTheory.WeilM.schr ψ0 w φ ∈ GlobalTheory.WeilM.SB (κ → k) := by
  first | exact @SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.schr_mem_SB | exact SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.schr_mem_SB | (intros; apply SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.schr_mem_SB <;> assumption)

end
end
