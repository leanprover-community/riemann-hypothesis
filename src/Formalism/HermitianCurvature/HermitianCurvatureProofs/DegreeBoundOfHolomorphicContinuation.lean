import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJmuDeg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJmuHC

namespace Formalism.FourierDecayAlt.P.CutBP.Jmu

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData MeasureTheory Finset
open scoped ENNReal

noncomputable section

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def DegHC (p : KB.Pl P Wp Wq) (F : JFam P.k P.r Wp Wq) (lam0 : Fin (2 * P.r + P.k + 1) → ℤ) (q0 : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ μ, LatticeNorms.N1 (μ - lam0) ≤ q0 → Present F μ →
    (F.A μ).deg p.T.base.μG = C * PI.UpqRep.fdegHC (lamOf F.sh μ)

def FdegHpkHC : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (μG : Measure (Formalism.QuantumDeterminants.Mt k r)),
    PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG →
    ∃ C : ℝ, 0 < C ∧ ∀ (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (σ : Mx k r → (H →L[ℂ] H)) (w : H),
      Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ → w ≠ 0 →
      PI.BesselPeriodGGP.fdegH μG σ w = C * PI.UpqRep.fdegHC lam


theorem fdegHC_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ PI.UpqRep.fdegHC x := by
  unfold PI.UpqRep.fdegHC
  refine div_nonneg (prod_nonneg fun a _ => prod_nonneg fun b _ => abs_nonneg _)
    (prod_nonneg fun a _ => prod_nonneg fun b hb => ?_)
  have := (mem_filter.1 hb).2
  have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast this
  linarith




end

end Formalism.FourierDecayAlt.P.CutBP.Jmu
