import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RelAmpleOfGenericIso
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfSymmetric

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TangentConstLB

theorem symIso_of_comm {S₀ S₁ : Scheme.{0}} {X : Over S₀} {A' : Over S₁} [GrpObj X] [GrpObj A']
    {L : LB X.left} (hL : L.IsLB)
    (hS : LBIso L (L.pull (GrpObj.inv : X ⟶ X).left)) (f : A'.left ⟶ X.left)
    (hf : (GrpObj.inv : A' ⟶ A').left ≫ f = f ≫ (GrpObj.inv : X ⟶ X).left) :
    LBIso ((L.pull f).pull (GrpObj.inv : A' ⟶ A').left) (L.pull f) := by
  have h1 := GlobalTheory.FamRep.lbIso_pull_pull hL f (GrpObj.inv : A' ⟶ A').left
  rw [hf] at h1
  have h2 := (GlobalTheory.FamRep.lbIso_pull_pull hL (GrpObj.inv : X ⟶ X).left f).symm
  have h3 := GlobalTheory.FamRep.lbIso_pull hS.symm f
  have hinv := pull_isLB hL (GrpObj.inv : X ⟶ X).left
  exact LBIso.trans (pull_isLB (pull_isLB hL f) _) (pull_isLB hL _) (pull_isLB hL f) h1
    (LBIso.trans (pull_isLB hL _) (pull_isLB hinv f) (pull_isLB hL f) h2 h3)

theorem lbIso_tangent_const :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (x₀ : Sp K ⟶ Xo.X) (x' : Sp (DualNumber K) ⟶ Xo.X) (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G x₀ π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → LBIso (Xo.univ.t.PP.L.pull π') (Xo.univ.t.PP.L.pull (q ≫ π)) := by
  intro E _ _ _ H Dw l Xo c K _ _ x₀ x' A _ A' _ π π' i q hi hπ hπ' hiπ hiq hq
  haveI : CharZero K := (RingHom.charZero_iff (algebraMap c.F K).injective).1 inferInstance
  have hAbG : IsAbelianScheme Xo.univ.t.G := by
    haveI := Xo.univ.proper
    exact AbelianSchemeGerms.isAbelianScheme_of_proper _ Xo.univ.t.semi
  have hA : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hAbG hπ
  have hL := Xo.univ.t.PP.isLB
  obtain ⟨-, w, hw, -⟩ := Xo.univ.t.sym
  have hS : LBIso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull (GrpObj.inv : Xo.univ.t.G ⟶ Xo.univ.t.G).left) := ⟨w, hw⟩
  have c1 : (GrpObj.inv : A' ⟶ A').left ≫ π' = π' ≫ (GrpObj.inv : Xo.univ.t.G ⟶ Xo.univ.t.G).left :=
    GlobalTheory.PolBaseChange.inv_comm hπ'
  have c2 : (GrpObj.inv : A' ⟶ A').left ≫ (q ≫ π) = (q ≫ π) ≫ (GrpObj.inv : Xo.univ.t.G ⟶ Xo.univ.t.G).left := by
    rw [← Category.assoc, GlobalTheory.PolBaseChange.inv_comm hq, Category.assoc, GlobalTheory.PolBaseChange.inv_comm hπ,
      Category.assoc]
  have f1 := GlobalTheory.FamRep.lbIso_pull_pull hL π' i
  rw [hiπ] at f1
  have f2 := GlobalTheory.FamRep.lbIso_pull_pull hL (q ≫ π) i
  rw [← Category.assoc, hiq, Category.id_comp] at f2
  exact GlobalTheory.SymFirstOrder.lbIso_of_symmetric K A A' i q hA hi hq hiq _ _ (pull_isLB hL π') (pull_isLB hL (q ≫ π))
    (symIso_of_comm hL hS π' c1) (symIso_of_comm hL hS (q ≫ π) c2)
    (LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) f1 f2.symm)

end GlobalTheory.TangentConstLB
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_iso_tangent_pull_constant_deformation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (x₀ : Sp K ⟶ Xo.X) (x' : Sp (DualNumber K) ⟶ Xo.X) (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G x₀ π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → LBIso (Xo.univ.t.PP.L.pull π') (Xo.univ.t.PP.L.pull (q ≫ π)) := by
  first | exact @GlobalTheory.TangentConstLB.lbIso_tangent_const | exact GlobalTheory.TangentConstLB.lbIso_tangent_const | (intros; apply GlobalTheory.TangentConstLB.lbIso_tangent_const <;> assumption)
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.ConstDefCub

theorem isPullCubical_constPt : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') (g : o.t.G.left ⟶ A'.left), g ≫ π' = m.cm.F → g ≫ A'.hom = o.t.G.hom → ∀ hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π), (cubeMapOf hF).IsPullCubical o.t.cub Xo.univ.t.cub := by
  intro hP hGD E _ _ _ H Dw l Xo c K _ _ y x' hpq htan A _ A' _ π π' i q hi hπ hπ' hiπ hiq hq o m g hg1 hg2 hF
  haveI : IsProper o.t.G.hom := o.proper
  have hA : IsAbelianScheme o.t.G := AbelianSchemeGerms.isAbelianScheme_of_proper o.t.G o.t.semi
  refine GlobalTheory.TripleModel.isPullCubical_of_lbIso GlobalTheory.SemiRigid.globalFns hA hF o.t.cub Xo.univ.t.cub ?_
  obtain ⟨w, -, hw, -⟩ := rigIso_congr rfl m.cm m.lin rfl rfl
  have K2 : LBIso (Xo.univ.t.PP.L.pull π') (Xo.univ.t.PP.L.pull (q ≫ π)) :=
    GlobalTheory.T.lineBundle_iso_tangent_pull_constant_deformation E H Dw l Xo c K y.x x' A A' π π' i q hi hπ hπ' hiπ hiq hq
  have hM := Xo.univ.t.PP.isLB
  have h1 : LBIso o.t.PP.L (Xo.univ.t.PP.L.pull (g ≫ π')) := hg1 ▸ ⟨w, hw⟩
  have h2 : LBIso ((Xo.univ.t.PP.L.pull π').pull g) (Xo.univ.t.PP.L.pull (g ≫ q ≫ π)) :=
    GlobalTheory.Ex.GenericFibre.lbIso_pull K2 g rfl
  have h3 : LBIso ((Xo.univ.t.PP.L.pull π').pull g) (Xo.univ.t.PP.L.pull (g ≫ π')) :=
    GlobalTheory.FamRep.lbIso_pull_pull hM π' g
  exact LBIso.trans o.t.PP.isLB (pull_isLB hM _) (pull_isLB hM _) h1
    (LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) h3.symm h2)

end GlobalTheory.ConstDefCub
end
