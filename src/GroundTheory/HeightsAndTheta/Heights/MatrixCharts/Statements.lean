module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

def logDetGram {g rk : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (F : Matrix (Fin g) (Fin rk) ℂ) : ℝ :=
  Real.log (Fᴴ * (Y⁻¹).map (fun x : ℝ => (x : ℂ)) * F).det.re

def cuspCoord {n a : ℕ} (h : a ≤ n) (z : Fin n → ℂ) (j : Fin a) : ℂ := z (Fin.castLE h j)

def cuspTime {n a : ℕ} (h : a ≤ n) (z : Fin n → ℂ) (j : Fin a) : ℝ :=
  (2 * Real.pi)⁻¹ * Real.log ‖cuspCoord h z j‖⁻¹

def puncturedChart {n a : ℕ} (h : a ≤ n) (U : Set (Fin n → ℂ)) : Set (Fin n → ℂ) :=
  {z | z ∈ U ∧ ∀ j, cuspCoord h z j ≠ 0}

def chartRadius {n a : ℕ} (h : a ≤ n) (z : Fin n → ℂ) : ℝ :=
  Real.exp 1 + ∑ j, Real.log (‖cuspCoord h z j‖ ^ 2)⁻¹

def chartImag {n a g : ℕ} (h : a ≤ n) (τ0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℝ) (z : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℝ :=
  (τ0 z).map Complex.im + ∑ j, cuspTime h z j • B j

namespace PeriodChartData

variable (D : PeriodChartData)

end PeriodChartData

end

end GroundTheory.Heights₂.Heights
