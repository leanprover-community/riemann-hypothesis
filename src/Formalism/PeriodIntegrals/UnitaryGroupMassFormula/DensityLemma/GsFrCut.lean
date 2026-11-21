import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PGsWitt

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm.Gram

def GsSliceP : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
  ∃ S : Set (B.Mat k r),
    (∀ y ∈ S, ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, n * y * n' ∈ S) ∧
    (∀ y ∈ S, ∀ α ∈ UWset k r z, ∀ β ∈ UWset k r z', α * y * β ∈ S → Rel z z' y (α * y * β)) ∧
    (∀ g₀ ∈ B.GV k r, 0 < Gf k r z z' g₀ → ∃ (O : Set (B.Mat k r)) (Fl : B.Mat k r → B.Mat k r × B.Mat k r),
      IsOpen O ∧ g₀ ∈ O ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Fl O ∧
      ∀ g ∈ O, g ∈ B.GV k r → 0 < Gf k r z z' g →
        (Fl g).1 ∈ UWset k r z ∧ (Fl g).2 ∈ UWset k r z' ∧ (Fl g).1 * g * (Fl g).2 ∈ S)



end PI.UnitaryGroupMassFormula.DLm.Gram
