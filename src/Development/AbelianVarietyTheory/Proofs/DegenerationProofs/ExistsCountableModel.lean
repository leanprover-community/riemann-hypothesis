import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullDegOfVal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolAVDescendsToCountableSubfield
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedRingActionDescendOfGenerators
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdditivePointsDescendFieldExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiEvenTauBimultDescendOfInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQkPullEquiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CorrOfValFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomIffOfIsGrpPullback
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleTrivialIsoDescendField
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationPreDataOverSubfield
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullDegCancelTowerOfFields
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRatioDescendsDegenerationPsiFamily
import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValuesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationValuesIsoFieldPullback
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsPullQk
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAddInjective

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polAV_descends_to_countable_subfield' : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (J I : Type) [Finite J] [Finite I] (a : J → (P.A ⟶ P.A)) (x : I → (𝟙_ (Over (Sp K)) ⟶ P.A)), ∃ (K₀ : Subfield K) (P₀ : PolAV (Sp K₀)) (Φ : P.A.left ⟶ P₀.A.left) (a₀ : J → (P₀.A ⟶ P₀.A)) (x₀ : I → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A)), Countable K₀ ∧ IsGrpPullback P.A P₀.A (spMap K₀.subtype) Φ ∧ LBIso P.L (P₀.L.pull Φ) ∧ (∀ j, (a j).left ≫ Φ = Φ ≫ (a₀ j).left) ∧ ∀ i, (x i).left ≫ Φ = spMap K₀.subtype ≫ (x₀ i).left := by
  first | exact @GlobalTheory.PolCountableDescent.polAV_descends_to_countable_subfield | exact GlobalTheory.PolCountableDescent.polAV_descends_to_countable_subfield | (intros; apply GlobalTheory.PolCountableDescent.polAV_descends_to_countable_subfield <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedRingAction_descend_of_generators : ∀ (O : Type) [CommRing O] [StarRing O] (J : Type) (gen : J → O), Subring.closure (Set.range gen) = ⊤ → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (P₀ : PolAV (Sp K₀)) (P : PolAV (Sp K)) (Φ : P.A.left ⟶ P₀.A.left), IsGrpPullback P.A P₀.A (spMap i) Φ → LBIso P.L (P₀.L.pull Φ) → ∀ (oa : P.OAct O) (a₀ : J → (P₀.A ⟶ P₀.A)), (∀ j, (oa.act (gen j)).left ≫ Φ = Φ ≫ (a₀ j).left) → ∃ oa₀ : P₀.OAct O, ∀ c, (oa.act c).left ≫ Φ = Φ ≫ (oa₀.act c).left := by
  first | exact @GlobalTheory.polOAct_descend_of_generators | exact GlobalTheory.polOAct_descend_of_generators | (intros; apply GlobalTheory.polOAct_descend_of_generators <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_points_descend_field_extension : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (P₀ : PolAV (Sp K₀)) (P : PolAV (Sp K)) (Φ : P.A.left ⟶ P₀.A.left), IsGrpPullback P.A P₀.A (spMap i) Φ → ∀ (X : Type) [AddCommGroup X] (I : Type) (b : I → X), AddSubgroup.closure (Set.range b) = ⊤ → ∀ c : X → (𝟙_ (Over (Sp K)) ⟶ P.A), (∀ y z, c (y + z) = padd P.A (c y) (c z)) → ∀ x₀ : I → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A), (∀ k, (c (b k)).left ≫ Φ = spMap i ≫ (x₀ k).left) → ∃ c₀ : X → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A), (∀ y z, c₀ (y + z) = padd P₀.A (c₀ y) (c₀ z)) ∧ ∀ y, (c y).left ≫ Φ = spMap i ≫ (c₀ y).left := by
  first | exact @GlobalTheory.PointDescent.additive_points_descend | exact GlobalTheory.PointDescent.additive_points_descend | (intros; apply GlobalTheory.PointDescent.additive_points_descend <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiEven_tauBimult_descend_of_injective : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R'), Function.Injective φ → ∀ (D : DegPre R) (D' : DegPre R') (_ : IsPullDeg φ D D'), (D'.PsiEven → D.PsiEven) ∧ (D'.TauBimult → D.TauBimult) := by
  first | exact @GlobalTheory.psiEven_tauBimult_of_isPullDeg_injective | exact GlobalTheory.psiEven_tauBimult_of_isPullDeg_injective | (intros; apply GlobalTheory.psiEven_tauBimult_of_isPullDeg_injective <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ArcPull PsiEvenPull

theorem exists_oAct_of_field_extension : GlobalFnsSt → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K₀) (D' : DegPre K) (hD : IsPullDeg i D D') (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X] (oB : D.P.OAct O) (oa' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (oa'.onB.act a).left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ (oB.act a).left) → ∃ oa : D.OAct O, oa.onB = oB := by
  intro hG K₀ K _ _ i D D' hD O _ _ _ _ oB oa' hx ho
  have gp := pull_grp hD
  have hφ : Function.Injective i := i.injective
  have := FieldBaseChange.flat_spMap i
  have := FieldBaseChange.surjective_spMap i
  have : Epi (spMap i) := Flat.epi_of_flat_of_surjective _
  have cl : ∀ (a : O) y, D.c (a • y) = D.c y ≫ oB.act a := fun a y => by
    obtain ⟨y, rfl⟩ := hD.xe.surjective y
    refine Over.OverMorphism.ext ((cancel_epi (spMap i)).1 ?_)
    have e₁ := hD.c_pr (a • y)
    have e₂ := hD.c_pr y
    rw [oa'.c_lin, Over.comp_left, Category.assoc, hx] at e₁
    refine e₁.symm.trans ((congrArg (_ ≫ ·) (ho a)).trans ?_)
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₂).trans (Category.assoc _ _ _))
  refine ⟨⟨oB, cl, fun a u hu u₀ y y' => ?_⟩, rfl⟩
  obtain ⟨y, rfl⟩ := hD.xe.surjective y
  obtain ⟨y', rfl⟩ := hD.xe.surjective y'
  refine corr_of_val_field_extension _ _ (fracMap hφ) _ _ D.P.isLB _ _ _ _ _ _ _ _ fun z J hJ => ?_
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
  have := oa'.onB.hom a
  have := oa'.onB.hom (star a)
  have := oB.hom a
  have := oB.hom (star a)
  obtain ⟨u', hu', h₀⟩ := exists_ros hG D'.P.isAb D'.P.isLB _ _ (oa'.onB.rosati a)
  have sq := fracMap_sq hφ
  have hh : (TK K).hom ≫ spMap i = genMap hφ ≫ (TK K₀).hom := (Category.id_comp _).symm.trans sq
  have e := val_corr hJ' (oa'.tau_bal a u' hu' h₀ y y') (𝟙 (TK K).left)
  have v := ros_val hG gp D'.P.isAb D.P.isLB D'.P.isLB hD.w_gen (ho a) (ho (star a)) ⟨hu, u₀⟩ ⟨hu', h₀⟩
    (cP D' (TK K) y) (cP D' (TK K) y') (genMap hφ ≫ D.pt2 (hD.xe y) (hD.xe y'))
    ((cPoint_proj hD _ hh y).trans (by
      rw [Category.assoc, DegPre.pt2, ← Over.comp_left, lift_fst]; rfl))
    ((cPoint_proj hD _ hh y').trans (by
      rw [Category.assoc, DegPre.pt2, ← Over.comp_left, lift_snd]; rfl)) hJ hJ'
  have cs : ∀ (a : O) y, cP D' (TK K) y ≫ oa'.onB.act a = cP D' (TK K) (a • y) := fun a y => by
    rw [cP, cP, oa'.c_lin, Category.assoc]
  rw [cs, cs, ← cPoint_add, ← cPoint_add] at v
  rw [val_mul hJ', val_pull hJ'] at e
  erw [Category.id_comp] at e
  beta_reduce at e
  show val _ (genMap hφ) z J = val _ (genMap hφ) z J
  rw [val_mul hJ, val_pull hJ, v]
  beta_reduce
  rw [← hx, ← hx, tau_val hD _ _ sq hJ hJ', tau_val hD _ _ sq hJ hJ']
  simp only [Category.id_comp]
  have e' := congrArg Additive.ofMul e
  apply Additive.ofMul.injective
  have c₀ : ∀ x, (cP D' (TK K) x).left = D'.xK x := fun _ => rfl
  have c₁ : val₂ u' z J' (cP D' (TK K) y) (cP D' (TK K) y') = val u' (D'.pt2 y y') z J' := rfl
  simp only [ofMul_mul, ofMul_inv, c₀, c₁] at e' ⊢
  linear_combination (norm := abel) e'

end GlobalTheory
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orderAction_descent_field_extension : GlobalFnsSt → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K₀) (D' : DegPre K) (hD : IsPullDeg i D D') (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X] (oB : D.P.OAct O) (oa' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (oa'.onB.act a).left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ (oB.act a).left) → ∃ oa : D.OAct O, oa.onB = oB := by
  atlas_forward_decl GlobalTheory.exists_oAct_of_field_extension
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiRelationDescent

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)

def chartPullComb {X Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) :
    ChartPull ((LB.LinComb L φ ε).pull h) (LB.LinComb L (fun k => h ≫ φ k) ε) (𝟙 Y') :=
  have le : ∀ J : PUnit → K → L.ι, ((LB.LinComb L φ ε).pull h).U J ≤
      LB.wchart L (fun k => h ≫ φ k) (J PUnit.unit) :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (mem_pull.1 hy) k
  { idx := fun J => J PUnit.unit
    le := le
    g := fun y J J' hj hj' => by
      refine (gm_pull_g (LB.LinComb L φ ε) h (𝟙 Y') y J J' hj hj').trans
        ((gm_linComb L φ ε (𝟙 Y' ≫ h) y _ _ (mem_pull.1 hj) (mem_pull.1 hj')).trans
          (Eq.trans ?_ (gm_linComb L (fun k => h ≫ φ k) ε (𝟙 Y') y _ _ (le J hj) (le J' hj')).symm))
      simp only [Category.assoc] }

section

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]
  (oa : D.OAct O) (w : O)

abbrev mor : Fin 4 → (D.P.A.left ⟶ D.P.A.left) :=
  ![(padd D.P.A (𝟙 _) (oa.onB.act w)).left, 𝟙 D.P.A.left, (oa.onB.act w).left, (toUnit D.P.A ≫ η[D.P.A]).left]

theorem prod_mor {T : Over (Sp R)} (x : T ⟶ D.P.A) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ k : Fin 4, h (x.left ≫ mor oa w k) ^ (![1, -2, -1, 2] : Fin 4 → ℤ) k =
      h (x * (x ≫ oa.onB.act w)).left * (h x.left ^ 2)⁻¹ * (h (x ≫ oa.onB.act w).left)⁻¹ *
        h (1 : T ⟶ D.P.A).left ^ 2 := by
  have a₀ : x ≫ padd D.P.A (𝟙 _) (oa.onB.act w) = x * (x ≫ oa.onB.act w) :=
    (MonObj.comp_mul _ _ _).trans (by rw [Category.comp_id])
  have a₁ : x ≫ toUnit D.P.A ≫ η[D.P.A] = 1 := MonObj.comp_one (M := D.P.A) x
  rw [Fin.prod_univ_four]
  show h (x ≫ padd D.P.A (𝟙 _) (oa.onB.act w)).left ^ (1 : ℤ) * h (x.left ≫ 𝟙 _) ^ (-2 : ℤ) *
    h (x ≫ oa.onB.act w).left ^ (-1 : ℤ) * h (x ≫ toUnit D.P.A ≫ η[D.P.A]).left ^ (2 : ℤ) = _
  rw [a₀, a₁, Category.comp_id]
  simp only [zpow_neg, zpow_ofNat, pow_one]

theorem prod_mor_one {T : Over (Sp R)} {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ k : Fin 4, h ((1 : T ⟶ D.P.A).left ≫ mor oa w k) ^ (![1, -2, -1, 2] : Fin 4 → ℤ) k = 1 := by
  have := oa.onB.hom w
  rw [prod_mor, MonObj.one_comp, _root_.mul_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one]
  abel

theorem exists_normalised (u : LB.Gen (LB.LinComb D.P.L (mor oa w) ![1, -2, -1, 2])) (hu : u.IsGen) :
    ∃ t : LB.Gen (LB.LinComb D.P.L (mor oa w) ![1, -2, -1, 2]), t.IsGen ∧
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ t (eSec D.P.A)) (LB.oneGen D.P.L) := by
  obtain ⟨t, ht, hv⟩ := exists_gen D.P.isLB (φ' := mor oa w) (ε' := ![1, -2, -1, 2])
    (fun V _ k => by
      refine Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := V) _
        (c := ∏ i, k (mor oa w i) ^ (![1, -2, -1, 2] : Fin 4 → ℤ) i) rfl
        (prod_neg _ _ (prod_mor_one oa w (T := D.P.A) k))) ?_
      simp)
    (LB.mulGen D.P.L _ _ _ _ u (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ u (1 : D.P.A ⟶ D.P.A).left)))
    (mulGen_isGen _ _ _ _ _ _ _ hu (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hu _)))
  refine ⟨t, ht, corr_of_val D.P.isLB fun y J hJ => ?_⟩
  have e : eSec D.P.A ≫ (1 : D.P.A ⟶ D.P.A).left = eSec D.P.A :=
    (congrArg (fun q => q.left) (MonObj.comp_one (M := D.P.A) η[D.P.A])).trans (Category.id_comp _)
  rw [val_pull hJ, val_one, Category.id_comp, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, e, mul_inv_cancel]

end

end GlobalTheory.PsiRelationDescent

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcPull GlobalTheory.PsiRelationDescent in

theorem psi_relation_descend_field : GlobalFnsSt → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K₀) (D' : DegPre K) (hD : IsPullDeg i D D') (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X] (oa : D.OAct O) (oa' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (oa'.onB.act a).left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ (oa.onB.act a).left) → ∀ w : O, TraceFormTwistIso D' oa' w → TraceFormTwistIso D oa w := by
  intro hG K₀ K _ _ i D D' hD O _ _ _ _ oa oa' hx ho w ⟨u', hu', u₀', hy'⟩
  have gp := pull_grp hD
  have hφ : Function.Injective i := i.injective
  have i₁ : (𝟙 D'.P.A : D'.P.A ⟶ _).left ≫ PsiEvenPull.proj hD =
      PsiEvenPull.proj hD ≫ (𝟙 D.P.A : D.P.A ⟶ _).left :=
    (Category.id_comp _).trans (Category.comp_id _).symm
  have i₂ : (toUnit D'.P.A ≫ η[D'.P.A]).left ≫ PsiEvenPull.proj hD =
      PsiEvenPull.proj hD ≫ (toUnit D.P.A ≫ η[D.P.A]).left := by
    show (D'.P.A.hom ≫ eSec D'.P.A) ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ D.P.A.hom ≫ eSec D.P.A
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hD.he).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) gp.1.w.symm).trans (Category.assoc _ _ _))))
  have hψ : ∀ k, mor oa' w k ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ mor oa w k := fun k => by
    fin_cases k
    exacts [mul_push gp _ i₁ (ho w), i₁, ho w, i₂]
  obtain ⟨s, hs, -⟩ := exists_up_om ((isGen_iff _).1 hD.w_gen) D.P.isLB D'.P.isLB (mor oa' w)
    (fun k => PsiEvenPull.proj hD ≫ mor oa w k) _ hψ u' hu'
  obtain ⟨u₁, hu₁⟩ := (lb_gen_iso_descend_field K₀ K i _ _ D.P.A.hom D'.P.A.hom (PsiEvenPull.proj hD)
    D.P.isAb.smooth D.P.isAb.proper D.P.isAb.geomConnected gp.1).1 (LB.LinComb D.P.L (mor oa w) ![1, -2, -1, 2])
    (LB.isLB_linComb D.P.isLB _ _) ⟨_, GtBaseChange.genPull_isGen (chartPullComb D.P.L (mor oa w) _ _) hs⟩
  obtain ⟨u, hu, u₀⟩ := exists_normalised oa w u₁ hu₁
  obtain ⟨t, ht, vt⟩ := exists_down_om hD.w_gen D.P.isLB D'.P.isLB (φ' := mor oa' w) (PsiEvenPull.proj hD) hψ u hu
  have tu := gen_unique D'.P.isLB D'.P.A.hom (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2 ht hu'
    fun y J' hJ' => by
      obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
      have o₁ : (1 : 𝟙_ (Over (Sp K)) ⟶ D'.P.A).left = eSec D'.P.A := Category.id_comp _
      have e := vt _ (1 : 𝟙_ (Over (Sp K)) ⟶ D'.P.A).left y J J' hJ hJ'
      rw [prod_mor_one, _root_.one_mul, o₁, hD.he] at e
      have e₁ := (val_pull hJ _ _ _).symm.trans ((val_corr hJ u₀ (specOf i)).trans (val_one _))
      have e₂ := (val_pull hJ' _ _ _).symm.trans ((val_corr hJ' u₀' (𝟙 _)).trans (val_one _))
      rw [Category.id_comp] at e₂
      exact e.symm.trans (e₁.trans e₂.symm)
  refine ⟨u, hu, u₀, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hD.xe.surjective y
  refine corr_of_val_field_extension _ _ (fracMap hφ) _ _ D.P.isLB _ _ _ _ _ _ _ _ fun z J hJ => ?_
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB (Z := (TK K).left) z
  have sq := fracMap_sq hφ
  have hh : (TK K).hom ≫ spMap i = genMap hφ ≫ (TK K₀).hom := (Category.id_comp _).symm.trans sq
  have e := val_corr hJ' (hy' x) (𝟙 _)
  have v := vt _ (cP D' (TK K) x).left z J J' hJ hJ'
  rw [prod_mor, cPoint_proj hD _ hh, ← TorusExt.cPoint_smul oa', ← cPoint_add, tu _ _ z J' hJ'] at v
  have c₀ : ∀ x, (cP D' (TK K) x).left = D'.xK x := fun _ => rfl
  have c₁ : ∀ x, (cP D (TK K₀) x).left = D.xK x := fun _ => rfl
  simp only [c₀, c₁] at v
  rw [val_mul hJ', val_mul hJ', val_pull hJ', Category.id_comp] at e
  show val (LB.mulGen D.P.L _ _ _ _ (D.tau (hD.xe x) (w • hD.xe x)) (LB.pullGen D.P.L _ _ u (D.xK (hD.xe x))))
    (genMap hφ) z J = val (LB.mulGen D.P.L _ _ _ _ (D.psi (hD.xe x)) D.rigK) (genMap hφ) z J
  have hJ₀ : Good (Z := (TK K).left) D.P.L z J := hJ
  rw [val_mul hJ₀, val_mul hJ₀, val_pull hJ₀, v, ← hx, tau_val hD _ _ sq hJ₀ hJ', psi_val hD _ _ sq hJ₀ hJ',
    rig_val hD _ _ sq hJ₀ hJ']
  simp only [Category.id_comp]
  have e' := congrArg Additive.ofMul e
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow] at e' ⊢
  linear_combination (norm := abel) e'

end GlobalTheory
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_relation_descends_field_extension : GlobalFnsSt → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K₀) (D' : DegPre K) (hD : IsPullDeg i D D') (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X] (oa : D.OAct O) (oa' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (oa'.onB.act a).left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ (oa.onB.act a).left) → ∀ w : O, TraceFormTwistIso D' oa' w → TraceFormTwistIso D oa w := by
  first | exact @GlobalTheory.psi_relation_descend_field | exact GlobalTheory.psi_relation_descend_field | (intros; apply GlobalTheory.psi_relation_descend_field <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degenerationPreData_over_subfield : Laws → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K) (P₀ : PolAV (Sp K₀)) (Φ : D.P.A.left ⟶ P₀.A.left), IsGrpPullback D.P.A P₀.A (spMap i) Φ → LBIso D.P.L (P₀.L.pull Φ) → ∀ c₀ : D.X → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A), (∀ y z, c₀ (y + z) = padd P₀.A (c₀ y) (c₀ z)) → (∀ y, (D.c y).left ≫ Φ = spMap i ≫ (c₀ y).left) → ∃ (D₀ : DegPre K₀) (ψ : TauTwist.PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen) (hD : IsPullDeg i D₀ (TauTwist.withPsi D ψ hψ)), D₀.P = P₀ ∧ HEq (PsiEvenPull.proj hD) Φ := by
  first | exact @GlobalTheory.FieldPull.exists_pre_below | exact GlobalTheory.FieldPull.exists_pre_below | (intros; apply GlobalTheory.FieldPull.exists_pre_below <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullDeg_cancel_tower_of_fields : ∀ (K₀ K₁ K : Type) [Field K₀] [Field K₁] [Field K] (α : K₀ →+* K₁) (β : K₁ →+* K) (D₀ : DegPre K₀) (D₁ : DegPre K₁) (D : DegPre K) (h₁ : IsPullDeg α D₀ D₁) (h : IsPullDeg (β.comp α) D₀ D), ∃ hD : IsPullDeg β D₁ D, PsiEvenPull.proj hD ≫ PsiEvenPull.proj h₁ = PsiEvenPull.proj h := by
  first | exact @GlobalTheory.FieldPull.exists_isPullDeg_cancel | exact GlobalTheory.FieldPull.exists_isPullDeg_cancel | (intros; apply GlobalTheory.FieldPull.exists_isPullDeg_cancel <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ratio_descends_degenerationPsiFamily : ∀ (K : Type) [Field K] (D : DegPre K) (ψ : TauTwist.PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen), ∃ a : D.X → K, ∀ (K₁ : Type) [Field K₁] (β : K₁ →+* K) (D₁ : DegPre K₁) (h : IsPullDeg β D₁ (TauTwist.withPsi D ψ hψ)), (∀ χ, a χ ∈ Set.range β) → ∃ (ψ₁ : TauTwist.PsiFam D₁) (hψ₁ : ∀ χ, (ψ₁ χ).IsGen) (hD : IsPullDeg β (TauTwist.withPsi D₁ ψ₁ hψ₁) D), PsiEvenPull.proj hD = PsiEvenPull.proj h := by
  first | exact @GlobalTheory.FieldPull.exists_ratio_descends | exact GlobalTheory.FieldPull.exists_ratio_descends | (intros; apply GlobalTheory.FieldPull.exists_ratio_descends <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section
namespace GlobalTheory.FieldPull
open GlobalTheory.ArcPull GlobalTheory.PsiEvenPull

theorem exists_countable_closed {K : Type} [Field K] [IsAlgClosed K] (K₀ : Subfield K) [Countable K₀] {X : Type}
    [Countable X] (a : X → K) : ∃ (F₁ : Type) (_ : Field F₁) (_ : IsAlgClosed F₁) (_ : Countable F₁) (α : K₀ →+* F₁)
      (β : F₁ →+* K), β.comp α = K₀.subtype ∧ ∀ x, a x ∈ Set.range β := by
  let K₁ : Subfield K := Subfield.closure ((K₀ : Set K) ∪ Set.range a)
  have hc : ((K₀ : Set K) ∪ Set.range a).Countable := (Set.to_countable _).union (Set.countable_range a)
  have c₁ : Cardinal.mk K₁ ≤ Cardinal.aleph0 :=
    (Subfield.cardinalMk_closure_le_max _).trans (max_le (Cardinal.mk_le_aleph0_iff.2 hc.to_subtype) le_rfl)
  have h : K₀ ≤ K₁ := fun x hx => Subfield.subset_closure (Or.inl hx)
  let β : AlgebraicClosure K₁ →ₐ[K₁] K := IsAlgClosed.lift
  refine ⟨AlgebraicClosure K₁, inferInstance, inferInstance, ?_, (algebraMap K₁ _).comp (Subfield.inclusion h),
    β.toRingHom, RingHom.ext fun x => β.commutes _, fun x =>
      ⟨algebraMap K₁ _ ⟨a x, Subfield.subset_closure (Or.inr ⟨x, rfl⟩)⟩, β.commutes _⟩⟩
  exact Cardinal.mk_le_aleph0_iff.1 ((Algebra.IsAlgebraic.cardinalMk_le_max K₁ _).trans (max_le c₁ le_rfl))

theorem exists_pre (hL : Laws) {K : Type} [Field K] [IsAlgClosed K] {O : Type} [CommRing O] [StarRing O]
    [Module.Finite ℤ O] (D : DegPre K) (o : D.P.OAct O) :
    ∃ (F₁ : Type) (_ : Field F₁) (_ : IsAlgClosed F₁) (_ : Countable F₁) (β : F₁ →+* K) (D₁ : DegPre F₁)
      (hD : IsPullDeg β D₁ D) (o₁ : D₁.P.OAct O), ∀ a, (o.act a).left ≫ proj hD = proj hD ≫ (o₁.act a).left := by
  obtain ⟨n, gen, hgen⟩ := Module.Finite.exists_fin (R := ℤ) (M := O)
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := D.X)
  have hgen' : Subring.closure (Set.range gen) = ⊤ := top_le_iff.1 fun x _ => by
    have hx : x ∈ Submodule.span ℤ (Set.range gen) := hgen ▸ Submodule.mem_top
    rw [← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure] at hx
    exact (AddSubgroup.closure_le (Subring.closure (Set.range gen)).toAddSubgroup).2 Subring.subset_closure hx
  have hb' : AddSubgroup.closure (Set.range b) = ⊤ := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, hb]; rfl
  obtain ⟨K₀, P₀, Φ, a₀, x₀, hc, gp, hw, ha, hx⟩ :=
    GlobalTheory.T.polAV_descends_to_countable_subfield' K D.P (Fin n) (Fin m) (fun j => o.act (gen j)) (fun k => D.c (b k))
  obtain ⟨o₀, ho₀⟩ := GlobalTheory.T.polarisedRingAction_descend_of_generators O _ gen hgen' K₀ K _ P₀ D.P Φ gp hw o a₀ ha
  obtain ⟨c₀, hc₀, hc₁⟩ := GlobalTheory.T.additive_points_descend_field_extension K₀ K _ P₀ D.P Φ gp D.X _ b hb' D.c D.c_add x₀ hx
  obtain ⟨D₀, ψ, hψ, h₀, rfl, e⟩ := GlobalTheory.T.exists_degenerationPreData_over_subfield hL K₀ K _ D P₀ Φ gp hw c₀ hc₀ hc₁
  obtain rfl := eq_of_heq e
  obtain ⟨a, Ha⟩ := GlobalTheory.T.exists_ratio_descends_degenerationPsiFamily K D ψ hψ
  have : Countable D.X := Finsupp.Countable.of_moduleFinite (R := ℤ)
  obtain ⟨F₁, _, _, _, α, β, hαβ, hβ⟩ := exists_countable_closed K₀ a
  obtain ⟨D', h₁, -, -⟩ := DegPull.exists_isPullDeg hL.polBaseChange K₀ F₁ α D₀ ⊤ (nonempty_psiOn_field D₀) trivial
  generalize K₀.subtype = i at h₀ ho₀ hαβ
  subst hαβ
  obtain ⟨h₂, e₂⟩ := GlobalTheory.T.exists_pullDeg_cancel_tower_of_fields K₀ F₁ K α β D₀ D' _ h₁ h₀
  obtain ⟨ψ₁, hψ₁, hD, e₃⟩ := Ha F₁ β D' h₂ hβ
  obtain ⟨o₁, ho₁⟩ := polOActPull _ _ _ D₀.P D'.P _ (pull_grp h₁) (LBIso.symm ⟨h₁.w, h₁.w_gen⟩) O o₀
  refine ⟨F₁, inferInstance, inferInstance, inferInstance, β, _, hD, o₁, fun c => ?_⟩
  rw [e₃]
  refine (pull_grp h₁).1.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₂).trans ((ho₀ c).trans ((congrArg (· ≫ _) e₂.symm).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (ho₁ c).symm).trans (Category.assoc _ _ _).symm)))))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pull_grp h₂).1.w).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (Over.w (o.act c))).trans ((pull_grp h₂).1.w.symm.trans
        ((congrArg (_ ≫ ·) (Over.w (o₁.act c)).symm).trans (Category.assoc _ _ _).symm)))))

theorem exists_data (hL : Laws) {K : Type} [Field K] [IsAlgClosed K] {O : Type} [CommRing O] [StarRing O]
    [Module.Finite ℤ O] (D : DegPre K) [Module O D.X] (oa : D.OAct O) :
    ∃ (F₁ : Type) (_ : Field F₁) (_ : IsAlgClosed F₁) (_ : Countable F₁) (β : F₁ →+* K) (D₁ : DegPre F₁)
      (hD : IsPullDeg β D₁ D) (_ : Module O D₁.X) (oa₁ : D₁.OAct O), (∀ (a : O) y, hD.xe (a • y) = a • hD.xe y) ∧
      (∀ a, (oa.onB.act a).left ≫ proj hD = proj hD ≫ (oa₁.onB.act a).left) ∧ (D.PsiEven → D₁.PsiEven) ∧
      (D.TauBimult → D₁.TauBimult) ∧ ∀ w, TraceFormTwistIso D oa w → TraceFormTwistIso D₁ oa₁ w := by
  obtain ⟨F₁, _, _, _, β, D₁, hD, o₁, ho⟩ := exists_pre hL D oa.onB
  letI : Module O D₁.X := hD.xe.symm.module O
  have hx : ∀ (a : O) y, hD.xe (a • y) = a • hD.xe y := fun a y => by
    show _ = hD.xe (a • hD.xe.symm (hD.xe y))
    rw [AddEquiv.symm_apply_apply]
  obtain ⟨oa₁, rfl⟩ := GlobalTheory.T.exists_orderAction_descent_field_extension hL.globalFns F₁ K β D₁ D hD O o₁ oa hx ho
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.psiEven_tauBimult_descend_of_injective hL.globalFns F₁ K β β.injective D₁ D hD
  exact ⟨F₁, inferInstance, inferInstance, inferInstance, β, D₁, hD, inferInstance, oa₁, hx, ho, h₁, h₂,
    GlobalTheory.T.psi_relation_descends_field_extension hL.globalFns F₁ K β D₁ D hD O oa₁ oa hx ho⟩

end GlobalTheory.FieldPull
end
end

section
open GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.HomCalc
variable {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O''] {f : O →+* O'} {g : O' →+* O''}
  {N : NumD O} {N' : NumD O'} {N'' : NumD O''}

def comp (I : NumD.Hom f N N') (I' : NumD.Hom g N' N'') : NumD.Hom (g.comp f) N N'' where
  φ := I'.φ.comp I.φ
  h x := I'.h (I.φ x) * Units.map g.toMonoidHom (I.h x)
  h_one := by rw [map_one, I'.h_one, I.h_one, map_one, mul_one]
  θ_eq x y u := by
    have a := congrArg (fun v => Additive.ofMul (Units.map g.toMonoidHom v)) (I.θ_eq x y u)
    have b := congrArg Additive.ofMul (I'.θ_eq (I.φ x) (I.φ y) (I.φ u))
    have c : Units.map (g.comp f).toMonoidHom (N.θ x y u) =
      Units.map g.toMonoidHom (Units.map f.toMonoidHom (N.θ x y u)) := rfl
    apply Additive.ofMul.injective
    simp only [c, map_mul, ofMul_mul, MonoidHom.comp_apply] at a b ⊢
    linear_combination (norm := abel) a + b
  σ_eq x := by
    have a := congrArg (fun v => Additive.ofMul (Units.map g.toMonoidHom v)) (I.σ_eq x)
    have b := congrArg Additive.ofMul (I'.σ_eq (I.φ x))
    have c : Units.map (g.comp f).toMonoidHom (N.σ x) =
      Units.map g.toMonoidHom (Units.map f.toMonoidHom (N.σ x)) := rfl
    apply Additive.ofMul.injective
    simp only [c, map_mul, ofMul_mul, MonoidHom.comp_apply, map_inv I.φ] at a b ⊢
    linear_combination (norm := abel) a + b
  lam := I'.lam * Units.map g.toMonoidHom I.lam
  th_eq x := by
    rw [MonoidHom.comp_apply, I'.th_eq, I.th_eq]
    simp only [map_mul, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.comp_apply]
    ring
  e := I.e.trans I'.e
  c_eq χ := by rw [AddEquiv.trans_apply, I'.c_eq, I.c_eq]; rfl
  ψ_eq χ := by
    have c : Units.map (g.comp f).toMonoidHom (N.ψ χ) =
      Units.map g.toMonoidHom (Units.map f.toMonoidHom (N.ψ χ)) := rfl
    rw [c, ← I.ψ_eq, map_mul, ← I'.ψ_eq, I.c_eq, AddEquiv.trans_apply, mul_assoc]

theorem comp_rel {I : NumD.Hom f N N'} {I' : NumD.Hom g N' N''} {a : N.Gt} {b : N'.Gt} {c : N''.Gt} (h : I.Rel a b)
    (h' : I'.Rel b c) : (comp I I').Rel a c := by
  refine ⟨h'.1.trans (congrArg I'.φ h.1), fun χ => ?_⟩
  have u := congrArg (fun v => Additive.ofMul (Units.map g.toMonoidHom v)) (h.2 χ)
  have v := congrArg Additive.ofMul (h'.2 (I.e χ))
  have w : Units.map (g.comp f).toMonoidHom (a.s χ) = Units.map g.toMonoidHom (Units.map f.toMonoidHom (a.s χ)) := rfl
  rw [I.c_eq, h.1] at v
  show c.s (I'.e (I.e χ)) * (I'.h (I.φ _) * Units.map g.toMonoidHom (I.h _)) =
    _ * (I'.h (I.φ _) * Units.map g.toMonoidHom (I.h _)) * (I'.h (I.φ _) * Units.map g.toMonoidHom (I.h _))
  apply Additive.ofMul.injective
  simp only [w, map_mul, ofMul_mul] at u v ⊢
  linear_combination (norm := abel) u + v

def inv {M M' : NumD O} (I : NumD.Iso M' M) : NumD.Hom (RingHom.id O) M M' where
  φ := I.φ.symm.toMonoidHom
  h x := (I.h (I.φ.symm x))⁻¹
  h_one := by rw [map_one, I.h_one, inv_one]
  θ_eq x y u := by
    have a := congrArg Additive.ofMul (I.θ_eq (I.φ.symm x) (I.φ.symm y) (I.φ.symm u))
    show M'.θ (I.φ.symm x) (I.φ.symm y) (I.φ.symm u) * _ * _ * _ = M.θ x y u * _ * _ * _ * _
    apply Additive.ofMul.injective
    simp only [map_mul, ofMul_mul, ofMul_inv, MulEquiv.apply_symm_apply] at a ⊢
    linear_combination (norm := abel) -a
  σ_eq x := by
    have a := congrArg Additive.ofMul (I.σ_eq (I.φ.symm x))
    show M'.σ (I.φ.symm x) * _ = M.σ x * _
    apply Additive.ofMul.injective
    simp only [map_inv I.φ.symm, ofMul_mul, ofMul_inv, MulEquiv.apply_symm_apply] at a ⊢
    linear_combination (norm := abel) -a
  lam := I.lam⁻¹
  th_eq x := by
    have a := I.th_eq (I.φ.symm x)
    rw [MulEquiv.apply_symm_apply] at a
    show M'.th (I.φ.symm x) = _ * M.th x
    rw [a, ← mul_inv, Units.inv_mul_cancel_left]
  e := I.e.symm
  c_eq χ := by
    show _ = I.φ.symm _
    rw [MulEquiv.eq_symm_apply, ← I.c_eq, AddEquiv.apply_symm_apply]
  ψ_eq χ := by
    obtain ⟨χ, rfl⟩ := I.e.surjective χ
    show _ = M.ψ _
    rw [AddEquiv.symm_apply_apply, I.c_eq, MulEquiv.symm_apply_apply, ← I.ψ_eq, mul_inv_cancel_right]

theorem inv_rel {M M' : NumD O} {I : NumD.Iso M' M} {a : M'.Gt} {b : M.Gt} (h : I.Rel a b) : (inv I).Rel b a := by
  refine ⟨(I.φ.symm_apply_eq.2 h.1).symm, fun χ => ?_⟩
  obtain ⟨χ, rfl⟩ := I.e.surjective χ
  have u := congrArg Additive.ofMul (h.2 χ)
  show a.s (I.e.symm _) * (I.h (I.φ.symm _))⁻¹ = b.s _ * (I.h (I.φ.symm _))⁻¹ * (I.h (I.φ.symm _))⁻¹
  rw [AddEquiv.symm_apply_apply, I.c_eq, h.1, ← map_mul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, MulEquiv.symm_apply_apply] at u ⊢
  linear_combination (norm := abel) -u

end GlobalTheory.HomCalc
end
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.ValuesSubfield
open GlobalTheory.TorusExt GlobalTheory.ArcExt

theorem exists_numOf_th {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {N : NumD F} (ν : NumOf D F N) (th : H0 D.P.L 1)
    (hth : ∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j) :
    ∃ (N₁ : NumD F) (ν₁ : NumOf D F N₁), ν₁.J = ν.J ∧ ν₁.th = th :=
  ⟨{ N with th := fun x => sF th (ν.eA x).left ν.J / rigVal ν },
    { ν with th := th, th_gen := hth, th_eq := fun _ => div_mul_cancel₀ _ (vF_ne_zero ν.good _ _) }, rfl, rfl⟩

theorem exists_values_subfield : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (F F' : Type) [Field F] [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (f : F →+* F'), f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' → ∀ (N' : NumD F') (ν' : NumOf D F' N'), ∃ (N : NumD F) (ν : NumOf D F N) (I : NumD.Hom f N N'), (∀ y, ν'.eX (I.e y) = ν.eX y) ∧ ∀ (k : ℕ) (p : QkPt D F k) (p' : QkPt D F' k) (c : N.Gt) (c' : N'.Gt), QkExt f p p' → ν.Pt p.g c → ν'.Pt p'.g c' → I.Rel c c' := by
  intro hG R _ _ D he hb F F' _ _ _ _ f hf N' ν'
  obtain ⟨N₀, ν₀, h₀⟩ := ValuesExist.exists_numOf D F hG he hb ν'.th ν'.th_gen (fun ψ => ν'.J (spMap f ≫ ψ))
    fun ψ z _ => (Subsingleton.elim (α := PrimeSpectrum F) (spMap f (IsLocalRing.closedPoint F')) z) ▸
      ν'.good (spMap f ≫ ψ) (Set.mem_univ (IsLocalRing.closedPoint F'))
  obtain ⟨N, ν, h₁, h₂⟩ := exists_numOf_th ν₀ ν'.th ν'.th_gen
  have hJ : ∀ ψ, ν'.J (spMap f ≫ ψ) = ν.J ψ := fun ψ => by rw [h₁, h₀]
  refine ⟨N, ν, numHom f hf ν ν' hJ h₂.symm, eX_numHom f hf ν ν' hJ h₂.symm, fun k p p' c c' h hc hc' => ?_⟩
  obtain rfl := (qkExt_iff hb f hf p p').1 h
  exact numHom_rel f hf ν ν' hJ h₂.symm hc hc'

end GlobalTheory.ValuesSubfield
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degenerationValues_over_subfield : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (F F' : Type) [Field F] [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (f : F →+* F'), f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' → ∀ (N' : NumD F') (ν' : NumOf D F' N'), ∃ (N : NumD F) (ν : NumOf D F N) (I : NumD.Hom f N N'), (∀ y, ν'.eX (I.e y) = ν.eX y) ∧ ∀ (k : ℕ) (p : QkPt D F k) (p' : QkPt D F' k) (c : N.Gt) (c' : N'.Gt), QkExt f p p' → ν.Pt p.g c → ν'.Pt p'.g c' → I.Rel c c' := by
  atlas_forward_decl GlobalTheory.ValuesSubfield.exists_values_subfield
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

namespace GlobalTheory.QkDescent

theorem exists_qkExt_of_isAlgClosed : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R), D.TauBimult → ∀ (F F' : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (f : F →+* F'), f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' → ∀ k : ℕ, 1 ≤ k → ∀ p' : QkPt D F' k, ∃ p : QkPt D F k, QkExt f p p' := by
  intro hL R _ _ _ D hB F F' _ _ _ _ _ _ _ f hf k hk p'
  have hk' : (k : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨p, hp⟩ := GlobalTheory.ArcExt.exists_qkExt f hf hB hL hk' p'
  exact ⟨p, (GlobalTheory.TorusExt.qkExt_iff hB f hf p p').2 hp.symm⟩

end GlobalTheory.QkDescent
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionPair_descent_algClosed_subfield : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R), D.TauBimult → ∀ (F F' : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (f : F →+* F'), f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' → ∀ k : ℕ, 1 ≤ k → ∀ p' : QkPt D F' k, ∃ p : QkPt D F k, QkExt f p p' := by
  atlas_forward_decl GlobalTheory.QkDescent.exists_qkExt_of_isAlgClosed
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degenerationValuesIso_fieldPullback : GlobalFnsSt → ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] (φ : R →+* K) (D : DegPre R) (D' : DegPre K) (hD : IsPullDeg φ D D') (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing K) F], ArcPull.Compat φ F → ∀ (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N'), ∃ I : NumD.Iso N' N, (∀ y, ν.eX (I.e y) = hD.xe (ν'.eX y)) ∧ ∀ (g : GtPtF D F) (g' : GtPtF D' F) (c : N.Gt) (c' : N'.Gt), ν.Pt g c → ν'.Pt g' c' → IsPullGtF φ hD F g g' → I.Rel c' c := by
  first | exact @GlobalTheory.ValuesPullIso.exists_values_iso | exact GlobalTheory.ValuesPullIso.exists_values_iso | (intros; apply GlobalTheory.ValuesPullIso.exists_values_iso <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.FieldPull
open GlobalTheory.ArcPull GlobalTheory.PsiEvenPull GlobalTheory.TorusExt GlobalTheory.QkPullEquiv

attribute [local instance] gtGroup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

section Exact
variable {R R' R'' F F' F'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R''] [IsDomain R'']
  [Field F] [Field F'] [Field F''] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F']
  [Algebra (FractionRing R'') F'']

def Exact (f : F →+* F') (A : ArcF D R F) (A' : ArcF D R' F') : Prop :=
  ∃ I : NumD.Hom f A.N A'.N, f A.ρ = A'.ρ ∧ (∀ n, 0 < n → f (A.I.ζ n) = A'.I.ζ n) ∧
    (∀ a y, I.e (A.act a y) = A'.act a (I.e y)) ∧
    ∀ n a, 0 < n → (A'.q n a).1.1.toAdd = I.e (A.q n a).1.1.toAdd ∧ I.Rel (A.q n a).1.2 (A'.q n a).1.2

theorem Exact.over {f : F →+* F'} {A : ArcF D R F} {A' : ArcF D R' F'} (h : Exact f A A') : A.Over f A' := by
  obtain ⟨I, h₁, h₂, h₃, h₄⟩ := h
  exact ⟨I, h₁, h₂, h₃, fun n a hn => ⟨_, (h₄ n a hn).1, (h₄ n a hn).2, (A'.N.qEq_equivalence n).refl _⟩⟩

theorem Exact.comp {f : F →+* F'} {g : F' →+* F''} {A : ArcF D R F} {A' : ArcF D R' F'} {A'' : ArcF D R'' F''}
    (h : Exact f A A') (h' : Exact g A' A'') : Exact (g.comp f) A A'' := by
  obtain ⟨I, h₁, h₂, h₃, h₄⟩ := h
  obtain ⟨I', k₁, k₂, k₃, k₄⟩ := h'
  exact ⟨HomCalc.comp I I', (congrArg g h₁).trans k₁, fun n hn => (congrArg g (h₂ n hn)).trans (k₂ n hn),
    fun a y => (congrArg I'.e (h₃ a y)).trans (k₃ a _), fun n a hn =>
      ⟨(k₄ n a hn).1.trans (congrArg I'.e (h₄ n a hn).1), HomCalc.comp_rel (h₄ n a hn).2 (k₄ n a hn).2⟩⟩
end Exact

section Pull
variable {R K F : Type} [CommRing R] [IsDomain R] [Field K] [Field F] [Algebra (FractionRing R) F]
  [Algebra (FractionRing K) F] {φ : R →+* K}

theorem exact_of_pull (hG : GlobalFnsSt) {A : ArcF D R F} {A' : ArcF D K F} (hD : IsPullDeg φ A.D₀ A'.D₀)
    (hF : ArcPull.Compat φ F) (hx : ∀ (a : 𝓞 E) y, hD.xe (a • y) = a • hD.xe y) (hρ : A.ρ = A'.ρ) (hζ : A.I.ζ = A'.I.ζ)
    (hev : ∀ n a, A'.I.ev n a = pullQk hD hG hF A.bimult A'.bimult (A.I.ev n a)) :
    Exact (RingHom.id F) A A' ∧ Exact (RingHom.id F) A' A := by
  obtain ⟨I, he, hr⟩ := GlobalTheory.T.exists_degenerationValuesIso_fieldPullback hG R K φ _ _ hD F hF _ _ A.ν A'.ν
  have act : ∀ a y, I.e (A'.act a y) = A.act a (I.e y) := fun a y => A.ν.eX.injective (by
    rw [he, ArcF.act, ArcF.act, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, he, hx])
  have hq : ∀ n a, (A.q n a).1.1.toAdd = I.e (A'.q n a).1.1.toAdd ∧ I.Rel (A'.q n a).1.2 (A.q n a).1.2 := fun n a => by
    obtain ⟨a₁, a₂⟩ := (eq_pullQk_iff hD hG hF _ _ _ _).1 (hev n a)
    refine ⟨A.ν.eX.injective ?_, hr _ _ _ _ (A.hq n a).2 (A'.hq n a).2 a₂⟩
    rw [he, (A.hq n a).1, (A'.hq n a).1, a₁, AddEquiv.apply_symm_apply]
  refine ⟨⟨HomCalc.inv I, hρ, fun n _ => congrArg (fun z => ((z n : Fˣ) : F)) hζ, fun a y => ?_, fun n a _ =>
    ⟨I.e.eq_symm_apply.2 (hq n a).1.symm, HomCalc.inv_rel (hq n a).2⟩⟩,
    ⟨TateInh.homOfIso I, hρ.symm, fun n _ => congrArg (fun z => ((z n : Fˣ) : F)) hζ.symm, act, fun n a _ => hq n a⟩⟩
  refine I.e.symm_apply_eq.2 ?_
  rw [act]
  exact congrArg (A.act a) (I.e.apply_symm_apply y).symm

theorem exists_pushTate (hG : GlobalFnsSt) {D₀ : DegPre R} {D' : DegPre K} (hD : IsPullDeg φ D₀ D')
    [Module (𝓞 E) D₀.X] [Module (𝓞 E) D'.X]
    {oa : letI := H.starRing; D₀.OAct (𝓞 E)} {oa' : letI := H.starRing; D'.OAct (𝓞 E)}
    (hx : ∀ (a : 𝓞 E) y, hD.xe (a • y) = a • hD.xe y)
    (ho : letI := H.starRing; ∀ a, (oa'.onB.act a).left ≫ proj hD = proj hD ≫ (oa.onB.act a).left)
    (hB : D₀.TauBimult) (hB' : D'.TauBimult) (hF : ArcPull.Compat φ F) (I' : TateIsoQ D D' oa' F) :
    ∃ I : TateIsoQ D D₀ oa F, I.ζ = I'.ζ ∧ ∀ n a, I'.ev n a = pullQk hD hG hF hB hB' (I.ev n a) := by
  let _ := H.starRing
  choose ev hev using fun n a => pullQk_surjective hD hG hF hB hB' (I'.ev n a)
  refine ⟨{ ζ := I'.ζ, ζ_prim := I'.ζ_prim, ζ_pow := I'.ζ_pow, ev := ev, add := fun n hn a b => ?_,
            lin := fun n hn x a => ?_, ker := fun n hn a b => ?_, onto := fun n hn p => ?_,
            tower := fun n m hn hm a => ?_, isom := fun n hn a b => ?_ }, rfl, fun n a => (hev n a).symm⟩
  · rw [qkAdd_pullQk_iff hD hG hF hB hB', hev, hev, hev]; exact I'.add n hn a b
  · rw [qkAct_pullQk_iff hD hG hF hB hB' hx ho, hev, hev]; exact I'.lin n hn x a
  · rw [← equiv_pullQk hD hG hF hB hB', hev, hev]; exact I'.ker n hn a b
  · obtain ⟨a, ha⟩ := I'.onto n hn (pullQk hD hG hF hB hB' p)
    exact ⟨a, by rw [← equiv_pullQk hD hG hF hB hB', hev]; exact ha⟩
  · obtain ⟨q', h₁, h₂, h₃⟩ := I'.tower n m hn hm a
    obtain ⟨q, rfl⟩ := pullQk_surjective hD hG hF hB hB' q'
    rw [← hev] at h₁ h₂ h₃
    refine ⟨q, hD.xe.symm.injective h₁, (isNsmul_iff_eq _ _ _).2 (pullGt_injective hD hG hF ?_),
      (equiv_pullQk hD hG hF hB hB' _ _).1 h₃⟩
    rw [map_nsmul]; exact (isNsmul_iff_eq _ _ _).1 h₂
  · rw [weilQkIs_pullQk_iff hD hG hF hB hB', hev, hev]; exact I'.isom n hn a b

theorem det_iff {D₀ : DegPre R} {D' : DegPre K} (hD : IsPullDeg φ D₀ D') [Module (𝓞 E) D₀.X] [Module (𝓞 E) D'.X]
    {oa : letI := H.starRing; D₀.OAct (𝓞 E)} {oa' : letI := H.starRing; D'.OAct (𝓞 E)}
    (hx : ∀ (a : 𝓞 E) y, hD.xe (a • y) = a • hD.xe y)
    (ho : letI := H.starRing; ∀ a, (oa'.onB.act a).left ≫ proj hD = proj hD ≫ (oa.onB.act a).left)
    (hF : ArcPull.Compat φ F) (τ : 𝓞 E →+* F) (m : ℕ) : letI := H.starRing
    (∃ n, LieMult (ofRingAct oa'.onB.toRingAct) (spMap ((algebraMap (FractionRing K) F).comp (algebraMap K _))) τ n ∧
      n + Module.finrank (𝓞 E) D'.X = m) ↔
    ∃ n, LieMult (ofRingAct oa.onB.toRingAct) (spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _))) τ n ∧
      n + Module.finrank (𝓞 E) D₀.X = m := by
  let _ := H.starRing
  refine exists_congr fun n => and_congr ?_ ?_
  · rw [LiePull.lieMult_pull _ _ _ _ _ _ _ (ofRingAct oa.onB.toRingAct) _ (pull_grp hD) ho F _ τ n, ← spMap_comp,
      show ((algebraMap (FractionRing K) F).comp (algebraMap K _)).comp φ =
        (algebraMap (FractionRing R) F).comp (algebraMap R _) from RingHom.ext fun r => (hF r).symm]
  · rw [(({ hD.xe with map_smul' := hx } : D'.X ≃ₗ[𝓞 E] D₀.X)).finrank_eq]

theorem exists_values (hL : Laws) (hGt : BrGtSt) [IsAlgClosed F] (D' : DegPre K) (he : D'.PsiEven) (hB : D'.TauBimult) :
    ∃ (N : NumD F) (ν : NumOf D' F N), ∀ k (p : QkPt D' F k), ∃ q, ν.QPt p q := by
  obtain ⟨N, ν, -⟩ := GlobalTheory.T.exists_integral_degeneration_values hL K D' he hB F ⊤ fun _ => trivial
  exact ⟨N, ν, fun k p => (((hGt K D' he hB F N ν).2.2.2.2 k).1 p).exists⟩

theorem exists_up (hL : Laws) (hGt : BrGtSt) [IsAlgClosed F] (hF : ArcPull.Compat φ F) (A : ArcF D R F) :
    ∃ A' : ArcF D K F, Exact (RingHom.id F) A' A := by
  let _ := H.starRing
  have hG := hL.globalFns
  have hφ : Function.Injective φ := fun x y h => IsFractionRing.injective R (FractionRing R)
    ((algebraMap (FractionRing R) F).injective ((hF x).trans (h ▸ (hF y).symm)))
  obtain ⟨W, hW, hψ⟩ := PsiSpread.exists_psiOn A.D₀ A.bimult
  obtain ⟨D', hD, -, -⟩ := DegPull.exists_isPullDeg hL.polBaseChange R K φ A.D₀ W hψ (by
    have : (specOf φ).base (genericPoint (Spec (CommRingCat.of K))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective φ hφ)
    rw [this]; exact hW)
  let _ : Module (𝓞 E) D'.X := hD.xe.module (𝓞 E)
  have hx : ∀ (a : 𝓞 E) y, hD.xe (a • y) = a • hD.xe y := fun a y => hD.xe.apply_symm_apply _
  have hB' := TauPull.tauBimult_pull hG hD A.bimult
  have he' := psiEven_pull hG _ _ φ _ _ hD A.even
  obtain ⟨oa', ho⟩ := exists_oAct hD hG hφ A.oa hx
  obtain ⟨N, ν, hq⟩ := exists_values (F := F) hL hGt D' he' hB'
  choose q hq using hq
  let A' : ArcF D K F :=
    { D₀ := D', oa := oa', even := he', bimult := hB', w0 := traceFormTwistIso_of_pullback hD hφ hx ho A.w0, ρ := A.ρ, ρ_sq := A.ρ_sq,
      det := fun τ => (det_iff hD hx ho hF τ _).2 (A.det τ), I := pullTate hG hD hx ho A.bimult hB' hF A.I,
      N := N, ν := ν, q := fun n a => q n _, hq := fun n a => hq n _, closed := inferInstance }
  exact ⟨A', (exact_of_pull hG (A := A) (A' := A') hD hF hx rfl rfl fun _ _ => rfl).2⟩

end Pull

theorem exists_down (hL : Laws) (hGt : BrGtSt) {K F : Type} [Field K] [IsAlgClosed K] [Field F] [IsAlgClosed F]
    [Algebra (FractionRing K) F] (A' : ArcF D K F) :
    ∃ (K₁ : Type) (_ : Field K₁) (_ : IsAlgClosed K₁) (_ : Countable K₁) (_ : Algebra (FractionRing K₁) F)
      (A : ArcF D K₁ F), Exact (RingHom.id F) A A' := by
  let _ := H.starRing
  have hG := hL.globalFns
  obtain ⟨K₁, _, _, _, β, D₁, hD, _, oa, hx, ho, he, hB, hw⟩ := exists_data hL A'.D₀ A'.oa
  let _ : Algebra (FractionRing K₁) F := ((algebraMap (FractionRing K) F).comp (fracMap β.injective)).toAlgebra
  have hF : ArcPull.Compat β F := fun x => congrArg (algebraMap (FractionRing K) F) (fracMap_algebraMap β.injective x)
  obtain ⟨I, hζ, hev⟩ := exists_pushTate hG hD hx ho (hB A'.bimult) A'.bimult hF A'.I
  obtain ⟨N, ν, hq⟩ := exists_values (F := F) hL hGt D₁ (he A'.even) (hB A'.bimult)
  choose q hq using hq
  let A : ArcF D K₁ F :=
    { D₀ := D₁, oa := oa, even := he A'.even, bimult := hB A'.bimult, w0 := hw _ A'.w0, ρ := A'.ρ, ρ_sq := A'.ρ_sq,
      det := fun τ => (det_iff hD hx ho hF τ _).1 (A'.det τ), I := I,
      N := N, ν := ν, q := fun n a => q n _, hq := fun n a => hq n _, closed := inferInstance }
  exact ⟨K₁, inferInstance, inferInstance, inferInstance, inferInstance, A,
    (exact_of_pull hG (A := A) (A' := A') hD hF hx rfl hζ hev).1⟩

theorem mem_range_of_pow_eq {F F' : Type} [Field F] [IsAlgClosed F] [Field F'] (f : F →+* F') {n : ℕ} (hn : 0 < n)
    {x : F'} {c : F} (h : x ^ n = f c) : ∃ y, f y = x :=
  (IsAlgClosed.splits (Polynomial.X ^ n - Polynomial.C c)).mem_range_of_isRoot
    (Polynomial.X_pow_sub_C_ne_zero hn c) (i := f) (x := x) (by simp [h])

theorem exists_sub (hL : Laws) (hGt : BrGtSt) (hWp : BrWpSt) {R F F' : Type} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Field F] [IsAlgClosed F] [CharZero F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F]
    [Algebra (FractionRing R) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') (A' : ArcF D R F') :
    ∃ A : ArcF D R F, Exact f A A' := by
  let _ := H.starRing
  have hG := hL.globalFns
  have hB := A'.bimult
  obtain ⟨N, ν, I, he, hr⟩ := GlobalTheory.T.exists_degenerationValues_over_subfield hG R A'.D₀ A'.even hB F F' f hf _ A'.ν
  choose q hq using fun k (p : QkPt A'.D₀ F k) => (((hGt R _ A'.even hB F N ν).2.2.2.2 k).1 p).exists
  obtain ⟨ρ, hρ⟩ := mem_range_of_pow_eq f two_pos (c := -(H.d : F)) (A'.ρ_sq.trans (by simp))
  have : ∀ n, ∃ z : Fˣ, 0 < n → f z = A'.I.ζ n := fun n => by
    rcases n.eq_zero_or_pos with rfl | hn
    · exact ⟨1, fun h => absurd h (lt_irrefl _)⟩
    · obtain ⟨y, hy⟩ := mem_range_of_pow_eq f hn (x := A'.I.ζ n) (c := 1) (by
        rw [← Units.val_pow_eq_pow_val, (A'.I.ζ_prim n hn).pow_eq_one, map_one, Units.val_one])
      exact ⟨Units.mk0 y fun h => (A'.I.ζ n).ne_zero (by rw [← hy, h, map_zero]), fun _ => hy⟩
  choose ζ hζ using this
  have hζ' : ∀ n, 0 < n → Units.map f.toMonoidHom (ζ n) = A'.I.ζ n := fun n hn => Units.ext (hζ n hn)
  have inj : Function.Injective (Units.map f.toMonoidHom) := Units.map_injective f.injective
  have : ∀ n a, ∃ p : QkPt A'.D₀ F n, 0 < n → qkExt hB f hf p = A'.I.ev n a := fun n a => by
    rcases n.eq_zero_or_pos with rfl | hn
    · exact ⟨qkZero hB F 0, fun h => absurd h (lt_irrefl _)⟩
    · obtain ⟨p, hp⟩ := GlobalTheory.T.exists_torsionPair_descent_algClosed_subfield hL R _ hB F F' f hf n hn (A'.I.ev n a)
      exact ⟨p, fun _ => ((qkExt_iff hB f hf _ _).1 hp).symm⟩
  choose ev hev using this
  have eqv : ∀ {n} (p p' : QkPt A'.D₀ F n), QkPt.Equiv _ F' (qkExt hB f hf p) (qkExt hB f hf p') ↔ QkPt.Equiv _ F p p' :=
    fun p p' => ⟨fun h => by
      obtain ⟨z, h₁, h₂⟩ := (equiv_iff hB _ _).1 h
      refine (equiv_iff hB _ _).2 ⟨z, h₁, Balanced.gtExt_injective f hf _ ?_⟩
      rw [map_add, gtExt_iota]; exact h₂, qkExt_congr hB f hf⟩
  have rel : ∀ n a, 0 < n → (A'.q n a).1.1.toAdd = I.e (q n (ev n a)).1.1.toAdd ∧
      I.Rel (q n (ev n a)).1.2 (A'.q n a).1.2 := fun n a hn =>
    ⟨A'.ν.eX.injective (by rw [he, (hq n _).1, (A'.hq n a).1, ← hev n a hn]; rfl),
      hr n _ _ _ _ ((qkExt_iff hB f hf _ _).2 (hev n a hn).symm) (hq n _).2 (A'.hq n a).2⟩
  let T : TateIsoQ D A'.D₀ A'.oa F :=
    { ζ := ζ
      ζ_prim := fun n hn => IsPrimitiveRoot.of_map_of_injective (hζ' n hn ▸ A'.I.ζ_prim n hn) inj
      ζ_pow := fun n m hn hm => inj (by
        rw [map_pow, hζ' _ (Nat.mul_pos hn hm), hζ' n hn, A'.I.ζ_pow n m hn hm])
      ev := ev
      add := fun n hn a b => by
        rw [qkAdd_iff hB, ← eqv, qkExt_qkAdd, ← qkAdd_iff hB, hev n _ hn, hev n _ hn, hev n _ hn]
        exact A'.I.add n hn a b
      lin := fun n hn x a => by
        rw [qkAct_iff hB hG, ← eqv, qkExt_qkSmul, ← qkAct_iff hB hG, hev n _ hn, hev n _ hn]
        exact A'.I.lin n hn x a
      ker := fun n hn a b => by rw [← eqv, hev n _ hn, hev n _ hn]; exact A'.I.ker n hn a b
      onto := fun n hn p => by
        obtain ⟨a, ha⟩ := A'.I.onto n hn (qkExt hB f hf p)
        exact ⟨a, by rw [← eqv, hev n _ hn]; exact ha⟩
      tower := fun n m hn hm a => by
        obtain ⟨q', h₁, h₂, h₃⟩ := A'.I.tower n m hn hm a
        rw [← hev _ _ (Nat.mul_pos hn hm)] at h₁ h₂
        rw [← hev _ _ hn] at h₃
        let p := qkMk hB (k := n) (ev (n * m) a).y (m • (ev (n * m) a).g) (by rw [← mul_nsmul', qk_nsmul hB])
        have e : qkExt hB f hf p = q' :=
          qk_ext h₁.symm ((map_nsmul (gtExt _ f hf) _ _).trans ((isNsmul_iff_eq _ _ _).1 h₂).symm)
        exact ⟨p, rfl, (isNsmul_iff_eq _ _ _).2 rfl, (eqv _ _).1 (e ▸ h₃)⟩
      isom := fun n hn a b => by
        refine (hWp R _ A'.even hB F N ν n hn _ _ _ _ _ (hq n _) (hq n _)).2 (congrArg Units.val (inj ?_))
        have u := (hWp R _ A'.even hB F' _ A'.ν n hn _ _ _ _ _ (A'.hq n a) (A'.hq n b)).1 (A'.I.isom n hn a b)
        rw [map_zpow, hζ' n hn, Units.ext u]
        exact (NumD.hom_transport _ _ f _ _ I).2.2.2.1 n _ _ _ _ (rel n a hn).1 (rel n a hn).2 (rel n b hn).1
          (rel n b hn).2 }
  let A : ArcF D R F :=
    { D₀ := A'.D₀, oa := A'.oa, even := A'.even, bimult := hB, w0 := A'.w0, ρ := ρ
      ρ_sq := f.injective (by rw [map_pow, hρ, A'.ρ_sq]; simp)
      det := fun τ => by
        obtain ⟨n, h₁, h₂⟩ := A'.det (f.comp τ)
        have := A'.D₀.P.isAb.smooth
        refine ⟨n, (DetExtend.lieMult_extend f _ _ τ n).1 ?_, h₂.trans ?_⟩
        · rw [← spMap_comp, ← RingHom.comp_assoc, hf]; exact h₁
        · rw [← hρ, RingHom.comp_apply, f.injective.eq_iff]
      I := T, N := N, ν := ν, q := fun n a => q n _, hq := fun n a => hq n _, closed := inferInstance }
  refine ⟨A, I, hρ, hζ, fun a y => A'.ν.eX.injective ?_, rel⟩
  rw [he, ArcF.act, ArcF.act, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, he]

theorem exists_countable_model : Laws → BrGtSt → BrWpSt → AllD fun D => ∀ (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing R) F] (A : ArcF D R F), ∃ (R₁ F₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : Field F₁) (_ : IsAlgClosed F₁) (_ : Countable F₁) (_ : Algebra (FractionRing R₁) F₁) (f : F₁ →+* F) (A₁ : ArcF D R₁ F₁), A₁.Over f A := by
  intro hL hGt hWp E _ _ _ H D R _ _ F _ _ _ _ A
  let _ : Algebra (FractionRing F) F := (FractionRing.algEquiv F F).toRingHom.toAlgebra
  obtain ⟨A₃, h₃⟩ := exists_up (K := F) (φ := (algebraMap (FractionRing R) F).comp (algebraMap R _)) hL hGt
    (fun r => ((FractionRing.algEquiv F F).commutes _).symm) A
  obtain ⟨K₁, _, _, _, _, A₂, h₂⟩ := exists_down hL hGt A₃
  let _ : Algebra (FractionRing K₁) K₁ := (FractionRing.algEquiv K₁ K₁).toRingHom.toAlgebra
  let f : K₁ →+* F := (algebraMap (FractionRing K₁) F).comp (FractionRing.algEquiv K₁ K₁).symm.toRingHom
  have : CharZero K₁ := f.charZero
  obtain ⟨A₁, h₁⟩ := exists_sub hL hGt hWp f (RingHom.ext fun x =>
    congrArg (algebraMap (FractionRing K₁) F) ((FractionRing.algEquiv K₁ K₁).symm_apply_apply x)) A₂
  exact ⟨K₁, K₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, _, A₁,
    ((h₁.comp h₂).comp h₃).over⟩

end GlobalTheory.FieldPull
end
end
