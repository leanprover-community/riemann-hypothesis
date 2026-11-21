import Formalism.PeriodIntegrals.PhMeasCore

open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace ContDiff

noncomputable section

namespace PI.PhMeasCore.UnitaryGroupMassFormula

open PI.PhMeasCore

def MulOnUH {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Hm : Matrix (Fin n) (Fin n) ℂ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  σ 1 = 1 ∧ ∀ a ∈ UH Hm, ∀ b ∈ UH Hm, σ (a * b) = (σ a).comp (σ b)

def StepRed : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Hm : Matrix (Fin n) (Fin n) ℂ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P : Matrix (Fin n) (Fin n) ℂ),
    IsUnit P → Pᴴ * Jm ε * P = Hm →
    (σ (P⁻¹ * 1 * P) = 1 ∧ ∀ a ∈ UJset ε, ∀ b ∈ UJset ε,
      σ (P⁻¹ * (a * b) * P) = (σ (P⁻¹ * a * P)).comp (σ (P⁻¹ * b * P))) →
    IsUnit Hm ∧ MulOnUH Hm σ

def StepExp : Prop :=
  ∀ (n : ℕ) (Hm X : Matrix (Fin n) (Fin n) ℂ), IsUnit Hm → InLie Hm X →
    ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ UH Hm

def StepSub : Prop :=
  ∀ (n : ℕ) (Hm : Matrix (Fin n) (Fin n) ℂ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H),
    MulOnUH Hm σ → w ∈ smoothVecs Hm σ →
    (∀ g ∈ UH Hm, σ g w ∈ smoothVecs Hm σ) ∧
    ∀ v ∈ smoothVecs Hm σ, ∀ v' ∈ smoothVecs Hm σ, v - v' ∈ smoothVecs Hm σ

section Deriv

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def StepExpDeriv : Prop :=
  ∀ (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ),
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0

end Deriv

def StepWord : Prop :=
  ∀ (n : ℕ) (Hm : Matrix (Fin n) (Fin n) ℂ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H),
    MulOnUH Hm σ → (∀ X, InLie Hm X → ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ UH Hm) →
    w ∈ smoothVecs Hm σ →
    ∀ ws : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ ws, InLie Hm X) →
      ContinuousOn (fun g => dsigW σ ws (σ g w)) (UH Hm) ∧
      ∀ g ∈ UH Hm, ∀ g₀ ∈ UH Hm,
        dsigW σ ws (σ g w - σ g₀ w) = dsigW σ ws (σ g w) - dsigW σ ws (σ g₀ w)

theorem isClosed_UH {n : ℕ} (Hm : Matrix (Fin n) (Fin n) ℂ) : IsClosed (UH Hm) := isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
  continuous_id) continuous_const



end PI.PhMeasCore.UnitaryGroupMassFormula

end
