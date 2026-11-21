import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.DensLemmaOfCut

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

structure TopModel where
  V : Type
  [ng : NormedAddCommGroup V]
  [ns : NormedSpace ℂ V]
  [cs : CompleteSpace V]

attribute [instance] TopModel.ng TopModel.ns TopModel.cs

def TopDensity (C₂ C CV : ℕ) : Prop :=
  StepAdm CV → ∀ m : ℕ, ZeroUpTo CV m →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) (μR : Measure (Mt k r))
    (θ : B.SS k r → ℝ) (i : ℕ),
    B.IsHaarOn (Rset γ) μR → Hyps CV D A ε mm F' →
    IsRelevant D γ → 0 < Gf k r D.z D.z' γ → zc D γ ≤ m + 1 → HasRun D γ i (r + 1) → admitted D γ μR θ →
    Integrable (fun p => θ p • (B.xiTau D (1, 1) p • B.rho D p F' γ)) D.μSS →
    ∃ (β : ℂ) (p m' : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (M : TopModel)
      (Φ0 : G.Mat (p + (m' + 1 + 1)) → M.V) (e : ℕ → ℝ) (K Cp : ℝ) (P : Seminorm ℂ M.V) (D' z₀ : ℂ),
      β ≠ 0 ∧ (∀ a, d a ≠ 0) ∧ p + (m' + 1 + 1) = r + 1 ∧ D' ≠ 0 ∧
      z₀ ∈ G.rootSet (m' + 2) ((-1) ^ (m' + 3) * D') ∧ 0 ≤ Cp ∧ (∀ v, P v ≤ Cp * ‖v‖) ∧
      U.DecayAll (C₂ * (m' + 2) ^ 2) e K Φ0 ∧
      (∀ j ≤ C₂ * (m' + 2) ^ 2,
        (A - (C : ℝ) * (((2 * r + k + 2 : ℕ) : ℝ) ^ 2 + (r : ℝ) ^ 3 + r * j)) / (5 * ((r : ℝ) + 1))
          - (C : ℝ) * (r : ℝ) ^ 2 ≤ e j / (5 * ((r : ℝ) + 1))) ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ t c : ℂ, t ≠ 0 → ‖t‖ < δ → c * t ^ (m' + 1) = D' →
        P (G.OmBlock β (m' + 1) (U.PhiTop β σ d Φ0) t c) = 0) ∧
      (P (G.OmLong β (m' + 1) (U.PhiTop β σ d Φ0) z₀) = 0 → orbI D γ θ F' = 0)




end PI.UnitaryGroupMassFormula.DLm
