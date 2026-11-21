import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiltIntegersCpEquivCompatibleUntilt
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltToComplexPAdicBasicLawsStatement

section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tiltIntegersCpEquiv_compatible_untilt : ∀ (l : ℕ) [Fact l.Prime], ∃ e : Fl l ≃+* PreTilt (GroundTheory.PAdicHodge.normInteger ℂ_[l]) l, ∀ x : Fl l, ((PreTilt.untilt (e x) : GroundTheory.PAdicHodge.normInteger ℂ_[l]) : ℂ_[l]) = sh x := by
  first | exact @GlobalTheory.PSer.exists_flEquiv_untilt | exact GlobalTheory.PSer.exists_flEquiv_untilt | (intros; apply GlobalTheory.PSer.exists_flEquiv_untilt <;> assumption)
end

section
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem untilt_injective_zero_and_dvd_of_norm_sh_le :
    ∀ (l : ℕ) [Fact l.Prime], (∀ x : Fl l, sh x = 0 → x = 0) ∧
      ∀ x y : Fl l, ‖sh x‖ ≤ ‖sh y‖ → y ∣ x := by
  intro l _
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_tiltIntegersCpEquiv_compatible_untilt l
  refine ⟨fun x hx => ?_, fun x y hxy => ?_⟩
  · have h0 : e x = 0 := GroundTheory.PAdicHodge.untilt_eq_zero_iff.1 (by rw [he]; exact hx)
    exact e.injective (by rw [h0, map_zero])
  · have hd : e y ∣ e x := by
      rw [GroundTheory.PAdicHodge.preTilt_dvd_iff_norm_le, GroundTheory.PAdicHodge.preTilt_norm_def,
        GroundTheory.PAdicHodge.preTilt_norm_def, he, he]
      exact hxy
    obtain ⟨c, hc⟩ := hd
    exact ⟨e.symm c, e.injective (by rw [map_mul, e.apply_symm_apply, hc])⟩

end GlobalTheory.PSer
end

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_untilt_injective_and_dvd_of_norm_le : ∀ (l : ℕ) [Fact l.Prime], (∀ x : Fl l, sh x = 0 → x = 0) ∧ ∀ x y : Fl l, ‖sh x‖ ≤ ‖sh y‖ → y ∣ x := by
  atlas_forward_decl GlobalTheory.PSer.untilt_injective_zero_and_dvd_of_norm_sh_le
end

section
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem tiltUntilt_add_estimate_of_norm_le (l : ℕ) [Fact l.Prime] (x y : Fl l) (hxy : ‖sh x‖ ≤ ‖sh y‖) :
    ‖sh (x + y) - sh x - sh y‖ ≤ ‖(l : ℂ_[l])‖ * ‖sh y‖ ∧ ‖sh (x + y)‖ ≤ ‖sh y‖ := by
  obtain ⟨h1, -, hmul, -, hle1, -, hadd, -⟩ := GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l
  obtain ⟨u, rfl⟩ := (GlobalTheory.T.tilt_untilt_injective_and_dvd_of_norm_le l).2 x y hxy
  have hsum : y * u + y = y * (u + 1) := by ring
  rw [hsum, hmul, hmul]
  constructor
  · have key : sh y * sh (u + 1) - sh y * sh u - sh y
        = sh y * (sh (u + 1) - sh u - sh (1 : Fl l)) := by rw [h1]; ring
    rw [key, norm_mul, mul_comm ‖(l : ℂ_[l])‖]
    exact mul_le_mul_of_nonneg_left (hadd u 1) (norm_nonneg _)
  · rw [norm_mul]
    calc ‖sh y‖ * ‖sh (u + 1)‖ ≤ ‖sh y‖ * 1 :=
          mul_le_mul_of_nonneg_left (hle1 _) (norm_nonneg _)
      _ = ‖sh y‖ := mul_one _

theorem sh_add_le : ∀ (l : ℕ) [Fact l.Prime] (r : ℝ) (x y : Fl l), ‖sh x‖ ≤ r → ‖sh y‖ ≤ r →
    ‖sh (x + y) - sh x - sh y‖ ≤ ‖(l : ℂ_[l])‖ * r ∧ ‖sh (x + y)‖ ≤ r := by
  intro l _ r x y hx hy
  have hl : 0 ≤ ‖(l : ℂ_[l])‖ := norm_nonneg _
  rcases le_total ‖sh x‖ ‖sh y‖ with h | h
  · obtain ⟨h1, h2⟩ := tiltUntilt_add_estimate_of_norm_le l x y h
    exact ⟨h1.trans (mul_le_mul_of_nonneg_left hy hl), h2.trans hy⟩
  · obtain ⟨h1, h2⟩ := tiltUntilt_add_estimate_of_norm_le l y x h
    rw [add_comm x y]
    refine ⟨?_, h2.trans hx⟩
    have e : sh (y + x) - sh x - sh y = sh (y + x) - sh y - sh x := by ring
    rw [e]
    exact h1.trans (mul_le_mul_of_nonneg_left hx hl)

end GlobalTheory.PSer
end

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tiltUntilt_add_estimate_le : ∀ (l : ℕ) [Fact l.Prime] (r : ℝ) (x y : Fl l), ‖sh x‖ ≤ r → ‖sh y‖ ≤ r → ‖sh (x + y) - sh x - sh y‖ ≤ ‖(l : ℂ_[l])‖ * r ∧ ‖sh (x + y)‖ ≤ r := by
  atlas_forward_decl GlobalTheory.PSer.sh_add_le
end
