import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

section
noncomputable section

set_option linter.dupNamespace false

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation
open Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped InnerProductSpace

namespace Formalism.L2.SG.RowsJoinS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S : D.what₂.Tau → SPar}

def RowsJoinS (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
    (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X)
    (ιG : GA D (D.sp.Y 0) ≃* X.B.I.GA) (c : ℝ) (ιH : D.s.HH ≃ₗᵢ[ℂ] HHX X) : Prop :=
  ∃ v₀ : M.Vec, (∀ τ, ‖(v₀ τ : M.H τ)‖ = 1) ∧ ∃ (j : E ≃ₗ[ℂ] EEC X G) (k : D.what₂.EE ≃ₗ[ℂ] E),
    (∀ T : E, ((j T : EEC X G) : L2X X) =ᵐ[muX X] (fun x => ev M v₀ (T : MMap M) (ιG.symm x)) ∧
      ‖((j T : EEC X G) : L2X X)‖ ^ 2 = c * (ipM M μ 𝓕 (T : MMap M) (T : MMap M)).re) ∧
    ∀ F : D.what₂.EE, ιH (D.sEE F) = conjHH X G (j (k F))

variable {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
  {E : Submodule ℂ (MMap M)} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {G : GoodOp X}
  {ιG : GA D (D.sp.Y 0) ≃* X.B.I.GA} {c : ℝ} {ιH : D.s.HH ≃ₗᵢ[ℂ] HHX X}

end Formalism.L2.SG.RowsJoinS
end
end

section
noncomputable section

set_option linter.dupNamespace false

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Links Formalism.L2.DIV
open Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped InnerProductSpace

namespace Formalism.L2.SG.RowsJoinPinned

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def castGA {I I' : Formalism.MainNotions.S.AutInst} (h : I = I') : I.GA ≃ₜ* I'.GA := h ▸ ContinuousMulEquiv.refl I.GA

variable {D : D7}

def iotaX (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) :
    GA D (D.sp.Y 0) ≃ₜ* X.B.I.GA :=
  (Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)

variable {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev MP (R : RealDat D A Ks) : DSModel (D.sp.Y 0) (parB (tparRec D) 0) := R.MY 0

abbrev EP (R : RealDat D A Ks) (F : Face D A) : Submodule ℂ (MMap (MP R)) := R.EEat (R.levR F true)

def RowsJoinPinned (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (ιH : D.s.HH ≃ₗᵢ[ℂ] HHX X) : Prop :=
  ∃ c : ℝ, 0 < c ∧ (X.B.I.muA X.B.μf).map (iotaX X h).symm = ENNReal.ofReal c • R.ν0 ∧
    ∃ v₀ : (MP R).Vec, IsLowVec (MP R) v₀ ∧
      ∃ (j : EP R F ≃ₗ[ℂ] EEC X G) (k : D.what₂.EE ≃ₗ[ℂ] EP R F),
        (∀ T : EP R F, ((j T : EEC X G) : L2X X) =ᵐ[muX X]
            (fun x => ev (MP R) v₀ (T : MMap (MP R)) ((iotaX X h).symm x)) ∧
          ‖((j T : EEC X G) : L2X X)‖ ^ 2 = c * (ipM (MP R) R.ν0 R.fd0 (T : MMap (MP R)) (T : MMap (MP R))).re) ∧
        ∀ F' : D.what₂.EE, ιH (D.sEE F') = conjHH X G (j (k F'))

variable {R : RealDat D A Ks} {F : Face D A} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {G : GoodOp X}
  {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {ιH : D.s.HH ≃ₗᵢ[ℂ] HHX X}

end Formalism.L2.SG.RowsJoinPinned

end
end
