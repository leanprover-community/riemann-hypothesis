import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.GsFramesOfLocal

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

def LocB : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ D0 : GfBaseD k r z z', ∀ g₀ ∈ B.GV k r, 0 < Gf k r z z' g₀ →
      ∃ (O : Set (B.Mat k r)) (bf : B.Mat k r → B.Mat k r),
        IsOpen O ∧ g₀ ∈ O ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) bf O ∧
        ∀ g ∈ O, g ∈ B.GV k r → 0 < Gf k r z z' g →
          bf g ∈ UWset k r z' ∧ ∃ t : ℝ, 0 < t ∧ omW' k r z z' (g * bf g) = (t : ℂ) • D0.nu'

def LocA : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ D0 : GfBaseD k r z z', ∀ g₀ ∈ B.GV k r, 0 < Gf k r z z' g₀ →
      ∀ (O : Set (B.Mat k r)) (bf : B.Mat k r → B.Mat k r), IsOpen O → g₀ ∈ O →
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) bf O →
        (∀ g ∈ O, g ∈ B.GV k r → 0 < Gf k r z z' g →
          bf g ∈ UWset k r z' ∧ ∃ t : ℝ, 0 < t ∧ omW' k r z z' (g * bf g) = (t : ℂ) • D0.nu') →
        ∃ (O' : Set (B.Mat k r)) (af : B.Mat k r → B.Mat k r),
          O' ⊆ O ∧ IsOpen O' ∧ g₀ ∈ O' ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) af O' ∧
          ∀ g ∈ O', g ∈ B.GV k r → 0 < Gf k r z z' g →
            af g ∈ UWset k r z ∧ af g * g * bf g ∈ gfSig D0



end PI.UnitaryGroupMassFormula.GsFr
