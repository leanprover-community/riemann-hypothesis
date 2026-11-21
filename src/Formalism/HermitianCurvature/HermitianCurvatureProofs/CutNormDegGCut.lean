import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJmuDegG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLemB

namespace Formalism.FourierDecayAlt.P.CutBP.Jmu.NDG

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section

def Acc (k r : ℕ) : ℝ := ((64 * (2 * r + k + 1) ^ 3 : ℕ) : ℝ)


def NormSquareTransferIdentity : Prop :=
  ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), TBB.jN2 p F = B.normSq p.T.base F

def CoefCC : Prop :=
  PI.KFinSmooth → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (u u' : Fin k → ℝ)
    (νq νq' : Measure (Formalism.QuantumDeterminants.Mt k r)) (A : JDat k r Wp Wq),
    A.Good Bs ε lam h u u' νq νq' → B.InCC (Acc k r) 5 (A.coef Bs.μG)

def BetaInfAbs : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.AB k r ≤ A → B.InCC A 5 F →
    Integrable (fun p => B.xiTau D (1, 1) p * B.Ph D F F p) D.μSS →
    B.betaInf D F F = ∫ p, B.xiTau D (1, 1) p * B.Ph D F F p ∂D.μSS

def BetaInfCoef : Prop :=
  SchurH → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq]
    [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (u u' : Fin k → ℝ)
    (νq νq' : Measure (Formalism.QuantumDeterminants.Mt k r)) (A : JDat k r Wp Wq),
    A.Good Bs ε lam h u u' νq νq' → A.l A.w0 ≠ 0 → A.l' A.w0 ≠ 0 →
    Integrable (fun p => B.xiTau Bs (1, 1) p * B.Ph Bs (A.coef Bs.μG) (A.coef Bs.μG) p) Bs.μSS ∧
    ∫ p, B.xiTau Bs (1, 1) p * B.Ph Bs (A.coef Bs.μG) (A.coef Bs.μG) p ∂Bs.μSS = ((A.deg Bs.μG : ℝ) : ℂ)

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]




end

end Formalism.FourierDecayAlt.P.CutBP.Jmu.NDG
