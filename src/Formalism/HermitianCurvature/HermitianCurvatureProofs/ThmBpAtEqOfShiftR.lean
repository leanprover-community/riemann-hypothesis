module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqShift
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

structure ShiftAtR {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (n₀ : ℕ) where
  up : ℕ → ℝ
  up' : ℕ → ℝ
  um : ℕ → ℝ
  um' : ℕ → ℝ
  Wqp : Type
  Wqm : Type
  [iNp : NormedAddCommGroup Wqp]
  [iIp : InnerProductSpace ℂ Wqp]
  [iFp : FiniteDimensional ℂ Wqp]
  [iNm : NormedAddCommGroup Wqm]
  [iIm : InnerProductSpace ℂ Wqm]
  [iFm : FiniteDimensional ℂ Wqm]
  pp : KB.Pl (shP P up up') Wp Wqp
  pm : KB.Pl (shP P um um') Wp Wqm
  Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)
  Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq)
  ApPt : C.LPt → (Wqp →L[ℂ] Wq)
  AmPt : C.LPt → (Wqm →L[ℂ] Wq)
  hzp : pp.T.base.z = p.T.base.z
  hzp' : pp.T.base.z' = p.T.base.z'
  hzm : pm.T.base.z = p.T.base.z
  hzm' : pm.T.base.z' = p.T.base.z'
  polyP : PolyOp (n₀ * (P.r + 1)) Ap
  polyM : PolyOp (n₀ * (P.r + 1)) Am
  amaps : AmapsSh p pp pm f Ap Am ApPt AmPt b n₀

attribute [instance] ShiftAtR.iNp ShiftAtR.iIp ShiftAtR.iFp ShiftAtR.iNm ShiftAtR.iIm ShiftAtR.iFm

section pieces

variable {P : M.Par} {Wp Wq Wq' : Type}
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
  {u u' : ℕ → ℝ}

def SwapTie (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq') : Prop :=
  q.T.base.z = p.T.base.z ∧ q.T.base.z' = p.T.base.z' ∧ q.T.base.π = p.T.base.π ∧
    q.T.base.μW = p.T.base.μW ∧ q.T.base.μN = p.T.base.μN ∧ q.T.base.μW' = p.T.base.μW' ∧
    q.ν' = p.ν' ∧ q.m₀ = p.m₀

end pieces

def WigEquiv {k r : ℕ} {Wq Wq' : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] (z z' : Fin (2 * r + k + 1) → ℂ) (π' : B.Mat k r → (Wq →L[ℂ] Wq))
    (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (A : B.Mat k r → (Wq' →L[ℂ] Wq)) : Prop :=
  (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, A (n * g * n') = A g) ∧
  (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ h ∈ UWset k r z, A (h * g) = A g) ∧
  (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ h' ∈ UWset k r z', A (g * h') = (π' h'⁻¹).comp ((A g).comp (π'' h')))

def WigUpper {k r : ℕ} {Wq Wq' : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] (z z' : Fin (2 * r + k + 1) → ℂ) (n₀ : ℕ) (A : B.Mat k r → (Wq' →L[ℂ] Wq)) : Prop :=
  ∀ g ∈ B.GV k r, ‖A g‖ ^ 2 ≤ (Gf k r z z' g / Tz k r z') ^ n₀

def WigLower {k r : ℕ} {Wq Wqp Wqm : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp]
    [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm]
    (z z' : Fin (2 * r + k + 1) → ℂ) (b : ℝ) (n₀ : ℕ)
    (Ap : B.Mat k r → (Wqp →L[ℂ] Wq)) (Am : B.Mat k r → (Wqm →L[ℂ] Wq)) : Prop :=
  ∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ v : Wq,
    ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (Tz k r z' / Gf k r z z' g) ^ n₀ *
      (‖(ContinuousLinearMap.adjoint (Ap g)) v‖ ^ 2 + ‖(ContinuousLinearMap.adjoint (Am g)) v‖ ^ 2)

end

end Formalism.FourierDecayAlt.P.CutBPEq
