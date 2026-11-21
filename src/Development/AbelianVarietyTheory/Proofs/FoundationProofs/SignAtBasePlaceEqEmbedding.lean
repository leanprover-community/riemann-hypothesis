import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LiftWeightComplexPointEqTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnCoord

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Cx
open GlobalTheory.FormTies GlobalTheory.OnTies
open GlobalTheory.OntoChain (coordMap thetaMat thetaOp liftLvl liftSub supLat Mir mirIncl uni mirToGL)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Block

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {Z : Submodule K B.S.Forms} {v0 : InfinitePlace K} {s : ℕ}



end Block

end GlobalTheory.OnCoord
end
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnCoord

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Cx
open GlobalTheory.FormTies GlobalTheory.OnTies
open GlobalTheory.OntoChain (coordMap thetaMat thetaOp liftLvl liftSub supLat Mir mirIncl uni mirToGL)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar


section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem inner_jV (hM : R.IsModels) (i : Fin D.R.m) (t : T0) (x y : (A.MtCSD i t).Forms) :
    inner ℂ (jVx R i t x) (jVx R i t y) = D.what₂.embLL ((A.MtCSD i t).csum x.1 y.1) :=
  ((hM.HV i t).2.2 (jVx R i t x) (jVx R i t y)).trans
    ((congrArg₂ (Bridge.adInner _ _ _) (hM.jV i t x) (hM.jV i t y)).trans (GlobalTheory.PresBasic.isom (R.B.L i t).pres x y))




theorem sign_at_base_place_eq_embedding (R : RealDat D A Ks) : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0




theorem chi_eq_one (hG : R.IsGrp F) (i : Fin D.R.m) {g : G} (hg : g ∈ F.P0) : (R.FW i).chi g = 1 := by
  obtain ⟨u, hu, rfl⟩ := (OntoChain.mem_base_iff hG.levels g).1 hg
  have h1 := (OntoChain.mem_pi_unip_iff R _).2 ⟨u, hu, rfl⟩
  refine Units.ext (D.what₂.embLL.injective ?_)
  rw [hG.chiW, Units.val_one, map_one, OntoChain.eG_mirIncl]
  refine Finset.prod_eq_one fun v _ => ?_
  have h2 := h1 v (Set.mem_univ v)
  have h3 : Matrix.GeneralLinearGroup.det (mirToGL R u v) = 1 := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular h2.1]
    exact Finset.prod_eq_one fun k _ => h2.2 k
  rw [h3, map_one, Units.val_one]

end Real

end GlobalTheory.OnCoord
end
end
