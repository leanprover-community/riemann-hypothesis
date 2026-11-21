import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeGap.HCFdegRGapHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeGap.HCFdegRGap
import Mathlib.Analysis.Complex.ExponentialBounds
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.HarishChandraMultiplicityBound

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.HCFdegRGap

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S MeasureTheory Matrix

theorem gap_big {p q N ep0 h0 : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hN : N = p + q)
    (he1 : Real.exp (-N) ≤ ep0) (he2 : ep0 < 1 / 2)
    (hh : 8192 * min p q * (p * q) ^ 3 * Real.log N / ep0 ^ 2 ≤ h0) :
    32 * N * p * q + 2 < h0 := by
  have hN2 : (2 : ℝ) ≤ N := by linarith
  have hlog2 := Real.log_two_gt_d9
  have hlog : (0.69 : ℝ) < Real.log N :=
    lt_of_lt_of_le (by norm_num at hlog2 ⊢; linarith) (Real.log_le_log (by norm_num) hN2)
  have hep : 0 < ep0 := lt_of_lt_of_le (Real.exp_pos _) he1
  have hmin : 1 ≤ min p q := le_min hp hq
  have hpq : 1 ≤ p * q := by nlinarith
  have hpq3 : (p * q) ^ 2 ≤ (p * q) ^ 3 := by nlinarith
  have hsum : p + q ≤ 2 * (p * q) := by nlinarith
  set X := 8192 * min p q * (p * q) ^ 3 * Real.log N with hXdef
  have hX : 8192 * 0.69 * (p * q) ^ 3 ≤ X := by
    have h3 : 0 ≤ (p * q) ^ 3 := by positivity
    have h4 : (1 : ℝ) * 0.69 ≤ min p q * Real.log N := mul_le_mul hmin hlog.le (by norm_num) (by linarith)
    rw [hXdef]
    nlinarith
  have hdiv : 4 * X ≤ X / ep0 ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have h5 : ep0 ^ 2 ≤ 1 / 4 := by nlinarith
    have hXpos : 0 ≤ X := le_trans (by positivity) hX
    nlinarith
  rw [hN]
  nlinarith



end PI.UnitaryGroupMassFormula.HCFdegRGap
end
end

section
noncomputable section

open MeasureTheory

namespace PI.UnitaryGroupMassFormula.HCFdegRGap

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.StandardLattice

theorem dsigEx_at (D : D7) (hd : dsigTie D) (ρ : D.what₂.Tau)
    (hex : ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)),
      IsDS (epsSH D.R) (lamSH D.R (D.hc ρ)) σ) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)),
      IsDS (epsSH D.R) (lamSH D.R (D.hc ρ)) σ ∧
      IsFdeg ((D.s.cdScale _ (epsSH D.R) : ENNReal) • Formalism.REAL.muG (epsSH D.R)) σ (D.dsig ρ) := by
  obtain ⟨H, i1, i2, σ, hσ⟩ := hex
  haveI : CompleteSpace H := hσ.1
  obtain ⟨d, hd0, hdI⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS _ σ hσ
  have hc : (0 : ℝ) < (D.s.cdScale _ (epsSH D.R) : ℝ) := D.s.cdScale_pos _ _
  have hF : IsFdeg ((D.s.cdScale _ (epsSH D.R) : ENNReal) • Formalism.REAL.muG (epsSH D.R)) σ
      (d / (D.s.cdScale _ (epsSH D.R) : ℝ)) := by
    refine ⟨div_pos hd0 hc, fun v w v' w' => ⟨(hdI v w v' w').1.smul_measure ENNReal.coe_ne_top, ?_⟩⟩
    rw [MeasureTheory.integral_smul_measure, (hdI v w v' w').2, ENNReal.coe_toReal]
    have hc' : ((D.s.cdScale _ (epsSH D.R) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hd' : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    rw [Complex.real_smul]
    push_cast
    field_simp
  have key := hd ρ H σ _ hσ hF
  refine ⟨H, i1, i2, σ, hσ, ?_⟩
  rw [← key]
  exact hF



end PI.UnitaryGroupMassFormula.HCFdegRGap
end
end
