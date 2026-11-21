import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.ProperDiscontinuity

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def oneFrame (Ψ : Finset (E →+* ℂ)) (r : ℕ) : Frame Ψ r :=
  fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)

omit [NumberField E] [IsCMField E] in
theorem mat_oneFrame (Ψ : Finset (E →+* ℂ)) (r : ℕ) (τ : Ψ) : mat (oneFrame Ψ r) τ = 1 := rfl

omit [NumberField E] [IsCMField E] in
theorem oneFrame_mem (Ψ : Finset (E →+* ℂ)) (r : ℕ) : oneFrame Ψ r ∈ Bor Ψ r := by
  intro τ
  refine ⟨by rw [mat_oneFrame]; simp, fun a c h => ?_⟩
  exact Matrix.one_apply_ne (ne_of_gt h)

omit [NumberField E] [IsCMField E] in
theorem rmul_oneFrame {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x : Frame Ψ r) :
    rmul x (oneFrame Ψ r) = x := by
  funext τ
  show mat x τ * mat (oneFrame Ψ r) τ = _
  rw [mat_oneFrame, Matrix.mul_one]
  rfl

omit [NumberField E] [IsCMField E] in
theorem lact_one {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x : Frame Ψ r) :
    lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = _
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  rfl


end GlobalTheory.ProperDiscontinuity
