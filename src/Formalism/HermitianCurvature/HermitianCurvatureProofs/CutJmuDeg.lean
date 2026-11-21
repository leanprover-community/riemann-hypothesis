import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJmu

namespace Formalism.FourierDecayAlt.P.CutBP.Jmu

open Formalism.FourierDecayAlt MeasureTheory Finset
open scoped ENNReal

noncomputable section

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def Present (F : JFam P.k P.r Wp Wq) (μ : Fin (2 * P.r + P.k + 1) → ℤ) : Prop :=
  Formalism.QuantumDeterminants.IsHCParam (lamOf F.sh μ) ∧ (F.A μ).l (F.A μ).w0 ≠ 0 ∧ (F.A μ).l' (F.A μ).w0 ≠ 0




def NormDeg (p : KB.Pl P Wp Wq) (F : JFam P.k P.r Wp Wq) (lam0 : Fin (2 * P.r + P.k + 1) → ℤ) (q0 : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ μ, LatticeNorms.N1 (μ - lam0) ≤ q0 → Present F μ →
    TBB.jN2 p (F.J p.T.base μ) = ENNReal.ofReal (c * (F.A μ).deg p.T.base.μG)

def DegPos (p : KB.Pl P Wp Wq) (F : JFam P.k P.r Wp Wq) (lam0 : Fin (2 * P.r + P.k + 1) → ℤ) (q0 : ℕ) : Prop :=
  ∀ μ, LatticeNorms.N1 (μ - lam0) ≤ q0 → Present F μ → 0 < (F.A μ).deg p.T.base.μG

def DegRatio (p : KB.Pl P Wp Wq) (F : JFam P.k P.r Wp Wq) (lam0 : Fin (2 * P.r + P.k + 1) → ℤ) (q0 : ℕ) : Prop :=
  ∀ μ (I : Finset (Fin (2 * P.r + P.k + 1))), I.card = P.r + 1 → LatticeNorms.N1 (μ - lam0) ≤ q0 →
    LatticeNorms.N1 (μ + LatticeNorms.eI I - lam0) ≤ q0 → Present F μ → Present F (μ + LatticeNorms.eI I) →
    (F.A (μ + LatticeNorms.eI I)).deg p.T.base.μG ≤
      (Real.exp 1 * ((2 * P.r + P.k + 1 : ℕ) : ℝ)) ^ (P.r + 1) * (F.A μ).deg p.T.base.μG


end

end Formalism.FourierDecayAlt.P.CutBP.Jmu
