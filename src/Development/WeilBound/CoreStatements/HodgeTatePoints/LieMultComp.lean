import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RulePow
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelGoodAtAllPrimesAndIdx
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLieCoordinatesLieMultIff
import Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoHost
import Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoDefs
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaCubIsPullCubical
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsGrpPullbackPow
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieCombIffProd
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusProdSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFibrePowerAndExternalTensorSectionNonzeroClo
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomFamilyOfPureTypeComplexTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTateIsoOfPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelStructureDescendsFieldExtension
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyDataDescendCountableSubrings
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NonemptyRingHomComplex
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsObjOfUniformisedTripleComplex
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPullback
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.CompletionDVR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels GlobalTheory.KeyUnitModels

namespace PositivityTheory.HtPt.Kftwo

section Fibre

open GlobalTheory GlobalTheory.KeyPow

theorem isFibreOf_pow {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {G G₂ : Over (Sp R)} [GrpObj G]
    [IsCommMonObj G] [GrpObj G₂] [IsCommMonObj G₂] {j n : ℕ} (p : Out.IsPowGrp G₂ G j) {L : LB G.left} (hL : L.IsLB)
    {M : LB G₂.left} (hM : M.IsLB) (rig : LB.Gen (L.pull (eSec G))) (rig₂ : LB.Gen (M.pull (eSec G₂))) (θ : L.Sec)
    (θ₂ : M.Sec) (v : Fin n → (epsR R ⟶ G)) (v₂ : Fin (j * n) → (epsR R ⟶ G₂)) (a : LB.Iso M (Out.boxLB L p.pr))
    (ha : a.IsGen)
    (pr : LB.Gen.Maps (LB.linCombIso a (K := PUnit) (fun _ => eSec G₂) (fun _ => 1)) rig₂ (Out.boxRig p L rig))
    (pth : ∀ (jj : Fin j → L.ι) (b : M.ι) (h : ∀ i, (Out.boxLB L p.pr).U jj ⊓ M.U b ≤ (p.pr i).left ⁻¹ᵁ L.U (jj i)),
      ∏ i, ((p.pr i).left.appLE _ _ (h i)).hom (θ.f (jj i)) =
        (show Γ(G₂.left, (Out.boxLB L p.pr).U jj ⊓ M.U b) from (a.s (jj, b)).val) * resG _ inf_le_right (θ₂.f b))
    (pv : ∀ (i i' : Fin j) (k : Fin n), v₂ (finProdFinEquiv (i, k)) ≫ p.pr i' = if i = i' then v k else 1)
    {x y : KeyIn R'} (hx₀ : IsFibreOf x G L rig θ v f) (hy : IsKeyPow y x j) : IsFibreOf y G₂ M rig₂ θ₂ v₂ f := by
  obtain ⟨φ, he, w, hg, F, hφ, hw, hr, hth, hF₁, hF₂, hv⟩ := hx₀
  obtain ⟨p', hp', pr', pth', pv'⟩ := hy
  have := x.P.isAb.comm
  have := y.P.isAb.comm
  obtain ⟨ψ, hψ, hc⟩ := exists_isGrpPullback_pow hφ p p'.toIsPowGrp
  obtain ⟨u, hu, hu'⟩ := exists_boxIso hc w ((isGen_iff w).1 hw)
  obtain ⟨W, hW, hW'⟩ := exists_conjIso (DVR.linComb_isLB _ hL _ _) hM (DVR.linComb_isLB _ x.P.isLB _ _)
    y.P.isLB u hu a ha p'.w p'.w_gen
  have heψ : eSec y.P.A ≫ ψ = spMap f ≫ eSec G₂ := PolBaseChange.eSec_comm hψ
  have hgy : y.P.g = j * n := by rw [← hp', hg]
  have hFe : spMap F ≫ (epsR R).hom = (epsR R').hom ≫ spMap f := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hF₁
  refine ⟨ψ, heψ, W, hgy, F, hψ, (isGen_iff W).2 hW, ?_, appLE_eq_of_stalk W θ₂ y.th fun z b b' hb hb' => ?_,
    hF₁, hF₂, fun q₀ => ?_⟩
  · refine (maps_iff W _ (fun _ => eSec G₂) _ y.rig rig₂ (spMap f) _ (rigPull_le ψ _ heψ M) (fun _ => rfl)).2 ?_
    have hx := (maps_iff w _ (fun _ => eSec G) _ x.rig rig (spMap f) _ (rigPull_le φ _ he L)
      (fun _ => rfl)).1 hr
    intro Z r z b b' hb hb'
    obtain ⟨c, hcx⟩ := exists_chart hL (φ (eSec x.P.A (r z)))
    obtain ⟨c', hcx'⟩ := exists_chart x.P.isLB (eSec x.P.A (r z))
    have hc₁ : eSec G ((r ≫ spMap f) z) ∈ L.U c := (congrArg (fun q => q (r z) ∈ L.U c) he).mp hcx
    have hb₁ : eSec G₂ ((r ≫ spMap f) z) ∈ M.U (b PUnit.unit) :=
      (congrArg (fun q => q (r z) ∈ M.U (b PUnit.unit)) heψ).mp (hb PUnit.unit)
    have m₁ : eSec G₂ ((r ≫ spMap f) z) ∈ (Out.boxLB L p.pr).U (fun _ => c) := mem_wchart_iff.2 fun i =>
      (congrArg (fun q => q ((r ≫ spMap f) z) ∈ L.U c) (eSec_pr p i)).mpr hc₁
    have m₂ : eSec y.P.A (r z) ∈ (Out.boxLB x.P.L p'.pr).U (fun _ => c') := mem_wchart_iff.2 fun i =>
      (congrArg (fun q => q (r z) ∈ x.P.L.U c') (eSec_pr p'.toIsPowGrp i)).mpr hcx'
    have m₃ : ψ ((r ≫ eSec y.P.A) z) ∈ (Out.boxLB L p.pr).U (fun _ => c) :=
      (congrArg (fun q => q (r z) ∈ (Out.boxLB L p.pr).U (fun _ => c)) heψ).mpr m₁
    have e₁ := (gm_boxRig p L rig (r ≫ spMap f) z c hc₁).symm.trans
      (gm_maps_pt pr (r ≫ spMap f) z (fun _ => c) (b PUnit.unit) m₁ hb₁)
    have e₂ := (gm_boxRig p'.toIsPowGrp x.P.L x.rig r z c' hcx').symm.trans
      (gm_maps_pt pr' r z (fun _ => c') (b' PUnit.unit) m₂ (hb' PUnit.unit))
    have e₃ := hx Z r z (fun _ => c) (fun _ => c') (fun _ => hcx) (fun _ => hcx')
    have e₄ := hW' Z (r ≫ eSec y.P.A) z (fun _ => c) (fun _ => c') (b PUnit.unit) (b' PUnit.unit) m₃ m₂
      (hb PUnit.unit) (hb' PUnit.unit)
    rw [hu' Z (r ≫ eSec y.P.A) z _ _ m₃ m₂, Category.assoc, heψ, ← Category.assoc] at e₄
    simp only [Category.assoc, eSec_pr p'.toIsPowGrp] at e₄
    rw [Fintype.prod_unique, zpow_one] at e₃ ⊢
    rw [e₃, Finset.prod_mul_distrib, e₂, ← _root_.mul_assoc, Category.assoc] at e₁
    exact (mul_left_cancel (e₁.symm.trans ((congrArg (· * _) e₄.symm).trans (_root_.mul_assoc _ _ _))))
  · choose c hcx using fun i => exists_chart hL (φ ((p'.pr i).left z))
    choose c' hcx' using fun i => exists_chart x.P.isLB ((p'.pr i).left z)
    have m₁ : ψ z ∈ LB.wchart L (fun i => (p.pr i).left) c := mem_wchart_iff.2 fun i =>
      (congrArg (fun q => q z ∈ L.U (c i)) (hc i)).mp (hcx i)
    have m₂ : z ∈ LB.wchart x.P.L (fun i => (p'.pr i).left) c' := mem_wchart_iff.2 hcx'
    have e₁ := gs_box_of_appLE a θ θ₂ pth (𝟙 _ ≫ ψ) z c b m₁ hb
    have e₂ := gs_box_of_appLE p'.w x.th y.th pth' (𝟙 _) z c' b' m₂ hb'
    have e₃ := fun i => gs_pull_of_appLE w θ x.th hth (𝟙 _ ≫ (p'.pr i).left) z (c i) (c' i) (hcx i) (hcx' i)
    have e₄ := hW' _ (𝟙 _) z c c' b b' m₁ m₂ hb hb'
    rw [hu' _ (𝟙 _) z c c' m₁ m₂] at e₄
    have e₅ : ∀ i, (𝟙 _ ≫ ψ) ≫ (p.pr i).left = (𝟙 _ ≫ (p'.pr i).left) ≫ φ := fun i => by
      rw [Category.assoc, Category.assoc, hc]
    simp only [e₅, e₃] at e₁
    rw [Finset.prod_mul_distrib, e₂, ← Units.coe_prod, ← _root_.mul_assoc, ← Units.val_mul, ← e₄, Units.val_mul,
      _root_.mul_assoc] at e₁
    exact ((Units.mul_right_inj _).1 e₁).symm
  · obtain ⟨⟨i, k⟩, rfl⟩ : ∃ q : Fin j × Fin x.P.g, (finProdFinEquiv q).cast hp' = q₀ :=
      ⟨finProdFinEquiv.symm (q₀.cast hp'.symm), by rw [Equiv.apply_symm_apply]; rfl⟩
    have hn : ((finProdFinEquiv (i, k)).cast hp').cast hgy = finProdFinEquiv (i, k.cast hg) :=
      Fin.ext (by simp only [Fin.val_cast, finProdFinEquiv_apply_val, hg])
    rw [hn]
    refine pow_left_ext p ?_ fun i' => ?_
    · rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w, hFe]
    · rw [Category.assoc, ← hc, ← Category.assoc, Category.assoc (spMap F), ← Over.comp_left, ← Over.comp_left, pv, pv']
      split_ifs
      · exact hv k
      · show ((epsR R').hom ≫ eSec x.P.A) ≫ φ = spMap F ≫ (epsR R).hom ≫ eSec G
        rw [Category.assoc, he, ← Category.assoc, ← hFe, Category.assoc]

end Fibre

section Act

open scoped CategoryTheory.Obj

variable {S : Scheme.{0}} {G G₂ : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj G₂] [IsCommMonObj G₂] {O : Type}
  [CommRing O] (a : OAct O G) (p : Out.IsPowGrp G₂ G 2)

def matEnd (m : Matrix (Fin 2) (Fin 2) O) : G₂ ⟶ G₂ :=
  p.lim.lift (Fan.mk G₂ fun i => (p.pr 0 ≫ a.act (m i 0)) * (p.pr 1 ≫ a.act (m i 1)))

omit [IsCommMonObj G] [IsCommMonObj G₂] in
theorem matEnd_pr (m : Matrix (Fin 2) (Fin 2) O) (i : Fin 2) :
    matEnd a p m ≫ p.pr i = (p.pr 0 ≫ a.act (m i 0)) * (p.pr 1 ≫ a.act (m i 1)) :=
  p.lim.fac (Fan.mk G₂ fun i => (p.pr 0 ≫ a.act (m i 0)) * (p.pr 1 ≫ a.act (m i 1))) ⟨i⟩

omit [IsCommMonObj G] [IsCommMonObj G₂] in
theorem pow_ext {T : Over S} {u v : T ⟶ G₂} (h : ∀ i, u ≫ p.pr i = v ≫ p.pr i) : u = v :=
  p.lim.hom_ext fun ⟨i⟩ => h i

theorem act_zero' : a.act 0 = 1 := by
  have h := a.add 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

omit [IsCommMonObj G₂] in
theorem isMonHom_matEnd (m : Matrix (Fin 2) (Fin 2) O) : IsMonHom (matEnd a p m) := by
  have := p.hom
  have := a.hom
  have h : ∀ i, IsMonHom (matEnd a p m ≫ p.pr i) := fun i => by
    rw [matEnd_pr]
    exact GlobalTheory.Serre.isMonHom_mul _ _
  refine ⟨pow_ext p fun i => ?_, pow_ext p fun i => ?_⟩
  · rw [Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · rw [Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, tensorHom_comp_tensorHom]

omit [IsCommMonObj G₂] in
theorem matEnd_scalar (c : O) (i : Fin 2) : matEnd a p (Matrix.scalar (Fin 2) c) ≫ p.pr i = p.pr i ≫ a.act c := by
  rw [matEnd_pr]
  fin_cases i <;> simp [act_zero', MonObj.comp_one]

omit [IsCommMonObj G₂] in
theorem matEnd_one : matEnd a p 1 = 𝟙 G₂ := pow_ext p fun i => by
  rw [← map_one (Matrix.scalar (Fin 2)), matEnd_scalar, a.one, Category.comp_id, Category.id_comp]

omit [IsCommMonObj G₂] in
theorem matEnd_mul (m m' : Matrix (Fin 2) (Fin 2) O) : matEnd a p (m * m') = matEnd a p m' ≫ matEnd a p m :=
  pow_ext p fun i => by
    have := a.hom
    rw [Category.assoc, matEnd_pr, matEnd_pr, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, matEnd_pr, matEnd_pr]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, a.add, MonObj.comp_mul, MonObj.mul_comp, Category.assoc, ← a.mul,
      _root_.mul_comm (m i 0), _root_.mul_comm (m i 1)]
    exact mul_mul_mul_comm _ _ _ _

omit [IsCommMonObj G₂] in
theorem matEnd_add (m m' : Matrix (Fin 2) (Fin 2) O) : matEnd a p (m + m') = matEnd a p m * matEnd a p m' :=
  pow_ext p fun i => by
    have := p.hom
    rw [MonObj.mul_comp, matEnd_pr, matEnd_pr, matEnd_pr]
    simp only [Matrix.add_apply, a.add, MonObj.comp_mul]
    exact mul_mul_mul_comm _ _ _ _

def matAct {O' : Type} [CommRing O'] (ψ : O' →+* Matrix (Fin 2) (Fin 2) O) : OAct O' G₂ where
  act c := matEnd a p (ψ c)
  hom _ := isMonHom_matEnd a p _
  one := by rw [map_one, matEnd_one]
  mul c d := by rw [_root_.mul_comm, map_mul, matEnd_mul]
  add c d := by rw [map_add, matEnd_add]

end Act

section Triple

open GlobalTheory.CechPic GlobalTheory.HermTensorLB GlobalTheory.HomComb
open scoped CategoryTheory.Obj

variable {E E' : Type} [Field E] [NumberField E] [IsCMField E] [Field E'] [NumberField E'] [IsCMField E']
  {H : Host E} {H' : Host E'} {S : Scheme.{0}}

theorem lam_act_sab (t : SAB H S) {T : Over S} (x y : T ⟶ t.G) (c : 𝓞 E) :
    lam (cls t.PP.L t.PP.isLB) (x ≫ t.act.act c) y = lam (cls t.PP.L t.PP.isLB) x (y ≫ t.act.act (H.bar c)) := by
  have hL := t.PP.isLB
  have h₀ := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (t.adj c)
  have h' := congrArg (pull (lift x y).left)
    ((cls_cube_two hL _ _ _).symm.trans (h₀.trans (cls_cube_two hL _ _ _)))
  simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h'

abbrev sqRig (t : SAB H S) : RigLB (Out.powObj t.G 2) :=
  combRig (fun i : Fin 2 => Out.powPr t.G i) (fun _ => 1) t.PP

theorem cls_sq (t : SAB H S) : cls _ (sqRig t).isLB =
    ∑ i : Fin 2, pull (Out.powPr t.G i).left (cls t.PP.L t.PP.isLB) := by
  refine (cls_linComb t.PP.isLB _ _ _).trans ?_
  simp only [one_smul]

theorem lam_sq (t : SAB H S) {T : Over S} (x z : T ⟶ Out.powObj t.G 2) : lam (cls _ (sqRig t).isLB) x z =
    lam (cls t.PP.L t.PP.isLB) (x ≫ Out.powPr t.G (0 : Fin 2)) (z ≫ Out.powPr t.G (0 : Fin 2)) +
      lam (cls t.PP.L t.PP.isLB) (x ≫ Out.powPr t.G (1 : Fin 2)) (z ≫ Out.powPr t.G (1 : Fin 2)) := by
  rw [cls_sq, lam_sum, Fin.sum_univ_two, lam_pull, lam_pull]

def square (Q : PairHost H H') (t : SAB H S) : SAB H' S where
  G := Out.powObj t.G 2
  semi := GlobalTheory.PowGrp.isSemiAbelian_pow S _ t.G 2 (Out.powIsPowGrp t.G 2) t.semi
  act := matAct t.act (Out.powIsPowGrp t.G 2) Q.ψ
  PP := sqRig t
  cub := combCub _ _ t.cub
  sym := combRig_isSymmetric _ _ t.cub t.sym
  adj c := by
    have hN := (sqRig t).isLB
    have hΘ : ∃ s : LB.Gen (Theta t.G t.PP.L), s.IsGen := ⟨t.cub.t, t.cub.isGen⟩
    refine (cls_eq_iff (LB.isLB_linComb hN _ _) (LB.isLB_linComb hN _ _)).1 ?_
    refine (cls_cube_two hN _ _ _).trans (Eq.trans ?_ (cls_cube_two hN _ _ _).symm)
    have e : ∀ (c : 𝓞 E') (i : Fin 2), (matAct t.act (Out.powIsPowGrp t.G 2) Q.ψ).act c ≫ Out.powPr t.G i =
        (Out.powPr t.G (0 : Fin 2) ≫ t.act.act (Q.ψ c i 0)) * (Out.powPr t.G (1 : Fin 2) ≫ t.act.act (Q.ψ c i 1)) :=
      fun c i => matEnd_pr t.act (Out.powIsPowGrp t.G 2) _ i
    rw [lam_sq, lam_sq, Category.assoc, Category.assoc, Category.assoc, Category.assoc, e, e, e, e]
    simp only [MonObj.comp_mul, lam_mul_left t.PP.isLB hΘ, lam_mul_right t.PP.isLB hΘ, ← Category.assoc, lam_act_sab,
      Q.bar]
    abel
  prim := by
    have hN := (sqRig t).isLB
    have e₀ : cls t.PP.L t.PP.isLB = lam (cls t.PP.L t.PP.isLB) (𝟙 t.G) (t.act.act H.w0) :=
      ((cls_eq_iff t.PP.isLB (LB.isLB_linComb t.PP.isLB _ _)).2 t.prim).trans (cls_cube_two t.PP.isLB _ _ _)
    refine (cls_eq_iff hN (LB.isLB_linComb hN _ _)).1 (Eq.trans ?_ (cls_cube_two hN _ _ _).symm)
    have e : ∀ i : Fin 2, (matAct t.act (Out.powIsPowGrp t.G 2) Q.ψ).act H'.w0 ≫ Out.powPr t.G i =
        Out.powPr t.G i ≫ t.act.act H.w0 := fun i =>
      (congrArg (fun m => matEnd t.act (Out.powIsPowGrp t.G 2) m ≫ Out.powPr t.G i) Q.w0).trans
        (matEnd_scalar t.act (Out.powIsPowGrp t.G 2) H.w0 i)
    rw [lam_sq, cls_sq, Fin.sum_univ_two, e, e, Category.id_comp, Category.id_comp]
    refine congrArg₂ (· + ·) ?_ ?_ <;>
    · refine (congrArg (pull _) e₀).trans ?_
      rw [pull_lam, Category.comp_id]

theorem sqRig_rig (t : SAB H S) : (sqRig t).rig = Out.boxRig (Out.powIsPowGrp t.G 2) t.PP.L t.PP.rig := by
  unfold sqRig combRig combGen Out.boxRig Out.GeneratorPullback.boxGen
  simp only [zpow_one]
  rfl

end Triple

variable {E E' : Type} [Field E] [NumberField E] [IsCMField E] [Field E'] [NumberField E'] [IsCMField E']
  {H : Host E} {H' : Host E'}

theorem exists_square (Q : PairHost H H') {V K : Type} [CommRing V] [IsLocalRing V] [Field K] (f : V →+* K)
    (t : SAB H (Sp V)) (θ : t.PP.L.Sec) {n : ℕ} (w : Fin n → (epsR V ⟶ t.G)) (x y : KeyIn K)
    (hx : IsFibreOf x t.G t.PP.L t.PP.rig θ w f) (hw : IsLieBasis w) (hθ : NonzeroClosed (X := t.G) θ)
    (hy : GlobalTheory.KeyPow.IsKeyPow y x 2) :
    ∃ (T : SAB H' (Sp V)) (s : T.G ≅ T.G) (θ₂ : T.PP.L.Sec) (m : ℕ) (w₂ : Fin m → (epsR V ⟶ T.G)),
      IsMonHom s.hom ∧ (∀ a, T.act.act (Q.σ a) ≫ s.hom = s.hom ≫ T.act.act a) ∧ IsLieBasis w₂ ∧
      NonzeroClosed (X := T.G) θ₂ ∧ IsFibreOf y T.G T.PP.L T.PP.rig θ₂ w₂ f := by
  let p := Out.powIsPowGrp t.G 2
  let D : Matrix (Fin 2) (Fin 2) (𝓞 E) := Matrix.diagonal ![1, -1]
  have hD : D * D = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  have hs : matEnd t.act p D ≫ matEnd t.act p D = 𝟙 _ := by rw [← matEnd_mul, hD, matEnd_one]
  obtain ⟨θ₂, hθ₂, hne⟩ := GlobalTheory.BoxSection.exists_boxSec _ _ _ 2 p t.PP.L (fun _ => θ) t.PP.isLB
  obtain ⟨v, hv, hvp⟩ := GlobalTheory.PowLie.isLieBasis_pow V _ _ 2 n p w hw
  have hL := (sqRig t).isLB
  have hr' : (Out.boxRig p t.PP.L t.PP.rig).IsGen := sqRig_rig t ▸ (sqRig t).rigGen
  refine ⟨square Q t, ⟨matEnd t.act p D, matEnd t.act p D, hs, hs⟩, θ₂, 2 * n, v, isMonHom_matEnd t.act p D, fun a => ?_, hv,
    hne _ fun _ => hθ, ?_⟩
  · change matEnd t.act p (Q.ψ (Q.σ a)) ≫ matEnd t.act p D = matEnd t.act p D ≫ matEnd t.act p (Q.ψ a)
    rw [← matEnd_mul, ← matEnd_mul]
    congr 1
    have e : Q.ψ (Q.σ a) * D = D * Q.ψ a := Q.conj a
    calc D * Q.ψ (Q.σ a) = D * (Q.ψ (Q.σ a) * D) * D := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hD, Matrix.mul_one]
      _ = Q.ψ a * D := by rw [e, ← Matrix.mul_assoc, hD, Matrix.one_mul]
  · change IsFibreOf y (Out.powObj t.G 2) (sqRig t).L (sqRig t).rig θ₂ v f
    rw [sqRig_rig]
    refine isFibreOf_pow f p t.PP.isLB hL t.PP.rig _ θ θ₂ w v (idIso _) (idIso_isGen hL) (fun q => hr' q.1 q.2)
      (fun jj b h => ?_) hvp hx hy
    refine Eq.trans ?_ (θ₂.compat jj b)
    rw [hθ₂ jj fun i => LB.wchart_le t.PP.L _ jj i, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact (congrArg (fun f => f.hom (θ.f (jj i))) (Scheme.Hom.appLE_map (Out.powPr t.G i).left
      (LB.wchart_le t.PP.L (fun i => (Out.powPr t.G i).left) jj i)
      (homOfLE (inf_le_left (b := (Out.boxLB t.PP.L p.pr).U b))).op)).symm

end PositivityTheory.HtPt.Kftwo
end
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.HtPt.Kftwo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_datum_tate_complex (T : GlobalTheory.CM.PAT H (Sp ℂ)) (hg : 1 ≤ T.g) (p q : ℕ)
    (hty : ∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult T.t.act (𝟙 (Sp ℂ)) τ p) ∧
      (τ H.rt ≠ H.rt0 → LieMult T.t.act (𝟙 (Sp ℂ)) τ q)) :
    ∃ D : Datum H, D.p = p ∧ D.q = q ∧ 1 ≤ p + q ∧
      Nonempty (TateIso D ℂ (Over.mk (𝟙 (Sp ℂ)) ⟶ T.t.G) (fun a g => g ≫ T.t.act.act a)
        (fun n g g' c => Out.WeilIs T.t.G T.t.PP.L n g g' (unitOn c))) := by
  have hT := GlobalTheory.thetaUnifAV_all
  obtain ⟨g, ty, hfn⟩ := GlobalTheory.AllClasses.exists_isTypeFn H p q
  obtain ⟨u, Hm, χ, Ef, hAH, -, -, -, -, -, hE, -, hW⟩ := hT T.pol T.t.PP.rig T.t.PP.rigGen
  obtain ⟨D, Pe, F, hp, hq, hP, hF, hEF, hact⟩ :=
    GlobalTheory.CM.PureTriple.exists_datum_period hT GlobalTheory.firstFiveLaws.1 T hfn hty u hAH
  refine ⟨D, hp, hq, ?_, ?_⟩
  · have hgg : g = T.g := by simpa using F.finrank_eq
    let j : Fin g := ⟨0, by omega⟩
    have : Nonempty {i // ty i = ty j} := ⟨⟨j, rfl⟩⟩
    have hc : 0 < Nat.card {i // ty i = ty j} := Nat.card_pos
    by_cases h : ty j (H.rt : E) = H.rt0
    · have := (hfn _).1 h
      omega
    · have := (hfn _).2 h
      omega
  · obtain ⟨I, -⟩ := GlobalTheory.UnifObj.exists_tateIso D D ty Pe (Q := 𝟙_ (Over (Sp ℂ)) ⟶ T.t.G)
      (fun a g => g ≫ T.t.act.act a) (fun n g g' c => Out.WeilIs T.t.G T.t.PP.L n g g' (unitOn c))
      (fun z => u.ex (F z)) (fun _ => LinearMap.id) hP.1 hP.2.1 (fun z z' => by rw [map_add, u.ex_add])
      (u.ex_onto.comp F.surjective) (fun z => (u.ker _).trans (hF z)) hact
      (fun k a b c hk hc => by
        have ha : F (Pe a) ∈ u.Λ := (hF _).2 ⟨a, rfl⟩
        have hb : F (Pe b) ∈ u.Λ := (hF _).2 ⟨b, rfl⟩
        have e : Ef ⟨_, ha⟩ ⟨_, hb⟩ = D.EF a b := by
          have := (hE ⟨_, ha⟩ ⟨_, hb⟩).trans (hEF a b)
          exact_mod_cast this
        have := hW k ⟨_, ha⟩ ⟨_, hb⟩ c hk (by rw [e]; exact hc)
        simp only [map_smul]
        exact this)
      (fun n m _ _ a => ⟨0, by simp⟩) (fun n _ => ⟨fun a => Iff.rfl, fun a => ⟨a, 0, by simp⟩⟩)
      (fun n _ a a' => by simp)
    exact ⟨I⟩

theorem exists_countable_algClosed {Ω : Type} [Field Ω] [IsAlgClosed Ω] (s : Set Ω) (hs : s.Countable) :
    ∃ K₀ : Subfield Ω, s ⊆ K₀ ∧ Countable K₀ ∧ IsAlgClosed K₀ := by
  let F := Subfield.closure s
  have hF : Countable F := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (Subfield.cardinalMk_closure_le_max s).trans (max_le ?_ le_rfl)
    exact Cardinal.mk_le_aleph0_iff.2 hs.to_subtype
  refine ⟨(algebraicClosure F Ω).toSubfield, fun x hx => ?_, ?_, ?_⟩
  · exact (algebraicClosure F Ω).algebraMap_mem (⟨x, Subfield.subset_closure hx⟩ : F)
  · show Countable (algebraicClosure F Ω)
    rw [← Cardinal.mk_le_aleph0_iff]
    exact (Algebra.IsAlgebraic.cardinalMk_le_max F _).trans (max_le Cardinal.mk_le_aleph0 le_rfl)
  · show IsAlgClosed (algebraicClosure F Ω)
    exact IsAlgClosure.isAlgClosed F

theorem exists_pat_descent {Ω : Type} [Field Ω] [IsAlgClosed Ω] (T : GlobalTheory.CM.PAT H (Sp Ω)) :
    ∃ (K₀ : Subfield Ω) (T₀ : GlobalTheory.CM.PAT H (Sp K₀)) (φ : T.t.G.left ⟶ T₀.t.G.left), Countable K₀ ∧ IsAlgClosed K₀ ∧
      T₀.g = T.g ∧ IsGrpPullback T.t.G T₀.t.G (spMap K₀.subtype) φ ∧ LBIso T.t.PP.L (T₀.t.PP.L.pull φ) ∧
      ∀ a, (T.t.act.act a).left ≫ φ = φ ≫ (T₀.t.act.act a).left := by
  have hL := GlobalTheory.firstFiveLaws.1
  obtain ⟨R₁, _, _, P₁, j, hc₁, hG, hiso, hgg⟩ := GlobalTheory.KeyCountableDescent.exists_polAV_descent hL Ω T.pol
  have := P₁.isAb.proper
  have := P₁.isAb.smooth
  choose S hS using fun a : 𝓞 E => GlobalTheory.morphism_descends_to_subring Ω R₁ T.t.G.left P₁.A.left P₁.A.left T.t.G.hom
    P₁.A.hom P₁.A.hom j ((T.t.act.act a).left ≫ j) hG.1 (by
      have w : j ≫ P₁.A.hom = T.t.G.hom ≫ spMap R₁.subtype := hG.1.w
      rw [Category.assoc, w, ← Category.assoc, Over.w])
  have hcE : Countable (𝓞 E) := (RingOfIntegers.basis E).repr.injective.countable
  obtain ⟨K₀, hsub, hcK, hK⟩ := exists_countable_algClosed ((R₁ : Set Ω) ∪ ⋃ a, (S a : Set Ω))
    ((Set.countable_coe_iff.1 hc₁).union (Set.countable_iUnion fun a => (S a).countable_toSet))
  have h₁ : R₁ ≤ K₀.toSubring := fun x hx => hsub (Or.inl hx)
  let f : R₁ →+* K₀ := Subring.inclusion h₁
  obtain ⟨P₂, π, hπ⟩ := GlobalTheory.exists_isPolFibre hL.polBaseChange f P₁
  obtain ⟨ψ, hψ, hψ'⟩ := GlobalTheory.CM.EllComp.exists_isPolFibre_lift (g := K₀.subtype) (P'' := T.pol) (χ := j) hπ
    ⟨hgg, hG, hiso.symm⟩
  have hψG : IsGrpPullback T.t.G P₂.A (spMap K₀.subtype) ψ := hψ'.2.1
  have hfl := GlobalTheory.FieldBaseChange.flat_spMap K₀.subtype
  have hsj := GlobalTheory.FieldBaseChange.surjective_spMap K₀.subtype
  obtain ⟨r, hr⟩ := GlobalTheory.ActDescent.exists_oAct hψG T.t.act fun a => by
    obtain ⟨b, b₁, b₂⟩ := hS a K₀.toSubring h₁ (fun x hx => hsub (Or.inr (Set.mem_iUnion.2 ⟨a, hx⟩))) P₂.A.left P₂.A.hom
      π ψ hπ.2.1.1 hψ hψG.1.w
    have w : b ≫ P₁.A.hom = P₂.A.hom ≫ spMap f := b₂.trans hπ.2.1.1.w
    refine ⟨Over.homMk (hπ.2.1.1.lift b _ w) (hπ.2.1.1.lift_snd _ _ _), hπ.2.1.1.hom_ext ?_ ?_⟩
    · show _ = (ψ ≫ hπ.2.1.1.lift b _ w) ≫ π
      rw [Category.assoc, hψ, Category.assoc, IsPullback.lift_fst, b₁]
    · show _ = (ψ ≫ hπ.2.1.1.lift b _ w) ≫ _
      rw [Category.assoc, Category.assoc, IsPullback.lift_snd, hψG.1.w, ← Category.assoc, Over.w]
  obtain ⟨τ₀, e, he, heL, heact⟩ := GlobalTheory.exists_triple_of_fieldExtension hL E H K₀ Ω K₀.subtype T.t P₂.A ψ P₂.L r P₂.isAb
    hψG P₂.isLB hψ'.2.2.symm hr
  have hE := isGrpPullback_of_iso e
  obtain ⟨h₁', h₂, h₃⟩ := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally _ _ P₂.A τ₀.G _ _
    P₂.L τ₀.PP.L P₂.isLB τ₀.PP.isLB P₂.isAb hE heL
  have hs : Out.Sym τ₀.G τ₀.PP.L := by
    obtain ⟨-, w, hw, -⟩ := τ₀.sym
    exact fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff w).1 hw) _⟩
  have hd : SmoothOfRelativeDimension P₂.g τ₀.G.hom :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} P₂.g
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension P₂.g) hE.1 P₂.smoothDim
  have hinv : (ψ ≫ e.inv.left) ≫ e.hom.left = ψ := by
    rw [Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left, Category.comp_id]
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  refine ⟨K₀, ⟨τ₀, h₁', P₂.g, hd, hs, h₂ P₂.ample, h₃ P₂.ktriv⟩, ψ ≫ e.inv.left, hcK, hK, hψ'.1.symm,
    (hψG.comp (isGrpPullback_of_iso e.symm)).congr (Category.comp_id _) rfl, ?_, fun a => ?_⟩
  · refine LBIso.trans T.t.PP.isLB (pull_isLB P₂.isLB ψ) (pull_isLB τ₀.PP.isLB _) hψ'.2.2.symm ?_
    have := GlobalTheory.CM.EllComp.lbIso_pull_comp heL.symm (ψ ≫ e.inv.left)
    rwa [hinv] at this
  · have e₁ : r.act a ≫ e.inv = e.inv ≫ τ₀.act.act a := by
      rw [Iso.comp_inv_eq, Category.assoc, heact, Iso.inv_hom_id_assoc]
    show _ = (ψ ≫ e.inv.left) ≫ (τ₀.act.act a).left
    rw [← Category.assoc, hr, Category.assoc, Category.assoc, ← Over.comp_left, e₁, Over.comp_left]

theorem exists_embedding {K : Type} [Field K] [CharZero K] [Countable K] (ρ : K) (hρ : ρ ^ 2 = -(H.d : K)) :
    ∃ σ : K →+* ℂ, σ ρ = H.rt0 := by
  obtain ⟨σ⟩ := GlobalTheory.KeyRuleUnique.nonempty_ringHom_complex K
  have h : σ ρ ^ 2 = H.rt0 ^ 2 := by rw [← map_pow, hρ, map_neg, map_natCast, H.sqrt_neg_disc_sq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · exact ⟨σ, h⟩
  · refine ⟨(starRingEnd ℂ).comp σ, ?_⟩
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have h₁ := congrArg Complex.re H.sqrt_neg_disc_sq
    have h₂ := congrArg Complex.im H.sqrt_neg_disc_sq
    simp [sq] at h₁ h₂
    have hre : H.rt0.re = 0 := by
      by_contra hne
      have : H.rt0.im = 0 := by
        have : H.rt0.re * H.rt0.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at h₁
      nlinarith [mul_self_nonneg H.rt0.re]
    rw [RingHom.comp_apply, h]
    apply Complex.ext <;> simp [hre]

theorem exists_datum_tate {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (T : GlobalTheory.CM.PAT H (Sp Ω)) (hg : 1 ≤ T.g)
    (ρ : Ω) (hρ : ρ ^ 2 = -(H.d : Ω)) (p q : ℕ)
    (hty : ∀ τ : 𝓞 E →+* Ω, (τ H.rt = ρ → LieMult T.t.act (𝟙 (Sp Ω)) τ p) ∧ (τ H.rt ≠ ρ → LieMult T.t.act (𝟙 (Sp Ω)) τ q)) :
    ∃ D : Datum H, D.p = p ∧ D.q = q ∧ 1 ≤ p + q ∧
      Nonempty (TateIso D Ω (Over.mk (𝟙 (Sp Ω)) ⟶ T.t.G) (fun a g => g ≫ T.t.act.act a)
        (fun n g g' c => Out.WeilIs T.t.G T.t.PP.L n g g' (unitOn c))) := by
  have hL := GlobalTheory.firstFiveLaws.1
  obtain ⟨K₀, T₀, φ, hc, hK, hgg, hG, hiso, hact⟩ := exists_pat_descent T
  obtain ⟨ρ₀, hρ₀, hρ₁⟩ : ∃ ρ₀ : K₀, ρ₀ ^ 2 = -(H.d : K₀) ∧ K₀.subtype ρ₀ = ρ := by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-(H.d : K₀)) two_pos
    have h : K₀.subtype z ^ 2 = ρ ^ 2 := by rw [← map_pow, hz, map_neg, map_natCast, hρ]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
    · exact ⟨z, hz, h⟩
    · exact ⟨-z, by rw [neg_sq, hz], by rw [map_neg, h, neg_neg]⟩
  obtain ⟨σ, hσ⟩ := exists_embedding ρ₀ hρ₀
  obtain ⟨T₁, m, hg₁⟩ := GlobalTheory.CM.PAT.exists_pullback E H _ _ (spMap σ) T₀
  have hsm := T₀.ab.smooth
  have hm : LBIso T₁.t.PP.L (T₀.t.PP.L.pull m.φ) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have sq : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B), spMap f ≫ 𝟙 _ = 𝟙 _ ≫ spMap f := fun f => by simp
  have key : ∀ (τ : 𝓞 E →+* K₀) (n : ℕ), LieMult T₁.t.act (𝟙 _) (σ.comp τ) n ↔
      LieMult T.t.act (𝟙 _) (K₀.subtype.comp τ) n := fun τ n => by
    rw [GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ T₀.t.act T₁.t.act m.cart m.act,
      GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ T₀.t.act T.t.act hG hact, ← sq, ← sq,
      GlobalTheory.DetExtend.lieMult_extend, GlobalTheory.DetExtend.lieMult_extend]
  obtain ⟨D, hp, hq, hpq, ⟨I₁⟩⟩ := exists_datum_tate_complex T₁ (by omega) p q fun τ => by
    obtain ⟨τ₀, rfl⟩ := GlobalTheory.DetExtend.exists_factor σ τ
    rw [key, key, ← hσ, RingHom.comp_apply]
    have := hty (K₀.subtype.comp τ₀)
    rw [← hρ₁, RingHom.comp_apply] at this
    exact ⟨fun h => this.1 (congrArg _ (σ.injective h)), fun h => this.2 fun h' => h (congrArg _ (K₀.subtype.injective h'))⟩
  refine ⟨D, hp, hq, hpq, ?_⟩
  obtain ⟨I₂, -⟩ := (GlobalTheory.PELDesc.tate_pull (D := D) T₀.t.PP.isLB T₁.t.PP.isLB m.cart hm T₀.t.act.act T₁.t.act.act m.act
    _ _ (sq σ)).1 I₁
  obtain ⟨I₃, -⟩ := (GlobalTheory.TateIsoFieldExt.tateIso_fieldExt hL E H D _ T₀.pol T₀.t.act.act K₀ ℂ σ (𝟙 _)).2 I₂ T₀.t.act.hom
  obtain ⟨I₄, -⟩ := (GlobalTheory.TateIsoFieldExt.tateIso_fieldExt hL E H D _ T₀.pol T₀.t.act.act K₀ Ω K₀.subtype (𝟙 _)).1 I₃
  obtain ⟨I₅, -⟩ := (GlobalTheory.PELDesc.tate_pull (D := D) T₀.t.PP.isLB T.t.PP.isLB hG hiso T₀.t.act.act T.t.act.act hact
    _ _ (sq K₀.subtype)).2 I₄
  exact ⟨I₅⟩

end PositivityTheory.HtPt.Kftwo
end
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.HtPt.Kftwo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_finset_point {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {Z : Scheme.{0}} (p : Z ⟶ Sp K)
    [LocallyOfFinitePresentation p] (x : Sp Ω ⟶ Z) (hx : x ≫ p = spMap (algebraMap K Ω)) :
    ∃ S : Finset Ω, ∀ K' : IntermediateField K Ω, (S : Set Ω) ⊆ K' →
      ∃ y : Sp K' ⟶ Z, spMap K'.val.toRingHom ≫ y = x := by
  obtain ⟨R, ψ, ⟨S, rfl⟩, -, h⟩ := GlobalTheory.Spread.exists_fg_comp_eq (A := Ω) (𝟙 (Sp K)) p (pullback.snd _ _ ≫ x) (by
    rw [Category.assoc, hx, pullback.condition])
  refine ⟨S, fun K' hS => ?_⟩
  have hle : Algebra.adjoin K (S : Set Ω) ≤ K'.toSubalgebra := Algebra.adjoin_le hS
  let g : Algebra.adjoin K (S : Set Ω) →+* K' := (Subalgebra.inclusion hle).toRingHom
  refine ⟨spMap g ≫ inv (pullback.snd (𝟙 (Sp K)) _) ≫ ψ, ?_⟩
  have e : spMap K'.val.toRingHom ≫ spMap g = spMap (Algebra.adjoin K (S : Set Ω)).val.toRingHom :=
    (Spec.map_comp _ _).symm
  rw [← cancel_epi (pullback.snd (𝟙 (Sp K)) (spMap (algebraMap K Ω))), ← h, ← Category.assoc (spMap _), e,
    ← Category.assoc, ← GlobalTheory.Spread.bcMap_snd, Category.assoc, IsIso.hom_inv_id_assoc]

theorem exists_coeff_embedding {l : Level H} (c : Coeff l) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (ρ : Ω)
    (hρ : ρ ^ 2 = -(H.d : Ω)) : ∃ β : c.F →+* Ω, β (IntermediateField.inclusion c.le (baseKA l).ρ) = ρ := by
  have := c.fin
  set r : c.F := IntermediateField.inclusion c.le (baseKA l).ρ with hr
  have hr2 : r ^ 2 = -(H.d : c.F) := by rw [hr, ← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have hd : (0 : ℚ) < H.d := by exact_mod_cast H.d_prime.pos
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C (-(H.d : ℚ))) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two fun b hb => by nlinarith [sq_nonneg b]
  have hmin : Polynomial.X ^ 2 - Polynomial.C (-(H.d : ℚ)) = minpoly ℚ r :=
    minpoly.eq_of_irreducible_of_monic hirr (by simp [hr2]) (Polynomial.monic_X_pow_sub_C _ two_ne_zero)
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval (F := ℚ) (E := c.F) (K := Ω)
    (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) (x := r) (y := ρ) (by rw [← hmin]; simp [hρ])
  exact ⟨φ.toRingHom, hφ⟩

theorem exists_point {D : Datum H} {l : Level H} (hA : l.A = 1) (Xo : Moduli D l) (c : Coeff l) {K : Type} [Field K]
    [CharZero K] (T : GlobalTheory.CM.PAT H (Sp K)) (ρ : AlgebraicClosure K) (hρ : ρ ^ 2 = -(H.d : AlgebraicClosure K))
    (hdet : DetCond D T.t.act (spMap (algebraMap K (AlgebraicClosure K))) ρ)
    (I : TateIso D (AlgebraicClosure K) (Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ T.t.G)
      (fun a g => g ≫ T.t.act.act a) (fun n g g' c => Out.WeilIs T.t.G T.t.PP.L n g g' (unitOn c))) :
    ∃ (K' : IntermediateField K (AlgebraicClosure K)) (_ : FiniteDimensional K K') (y : Sp K' ⟶ Xo.XF c)
      (t' : SAB H (Sp K')), Nonempty (SABMap t' T.t (spMap (algebraMap K K'))) ∧
        Nonempty (SABMap t' Xo.univ.t (y ≫ pullback.fst _ _)) := by
  classical
  have hL := GlobalTheory.firstFiveLaws.1
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have := c.fin
  have hsm := T.ab.smooth
  obtain ⟨β, hβ⟩ := exists_coeff_embedding c ρ hρ
  have hcard := (hL.mulN _ T.pol l.M hM).2.2.2.2 _ (spMap (algebraMap K (AlgebraicClosure K))) (Nat.cast_ne_zero.2 hM.ne')
  have hfin : Finite {x : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ T.t.G // x ^ l.M = 1} :=
    Nat.finite_of_card_ne_zero (by erw [hcard]; positivity)
  choose S hS using fun x : {x : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ T.t.G // x ^ l.M = 1} =>
    exists_finset_point T.t.G.hom x.1.left (Over.w x.1)
  let b := Module.finBasis ℚ c.F
  let U : Set (AlgebraicClosure K) := (⋃ x, (S x : Set (AlgebraicClosure K))) ∪ Set.range fun i => β (b i)
  have hU : Finite U := ((Set.finite_iUnion fun x => (S x).finite_toSet).union (Set.finite_range _)).to_subtype
  let K' := IntermediateField.adjoin K U
  have hfd : FiniteDimensional K K' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hβm : ∀ z, β z ∈ K' := fun z => by
    rw [← b.sum_repr z, map_sum]
    refine sum_mem fun i _ => ?_
    rw [Rat.smul_def, map_mul, map_ratCast]
    exact mul_mem (SubfieldClass.ratCast_mem _ _) (IntermediateField.subset_adjoin K U (Or.inr ⟨i, rfl⟩))
  let β' : c.F →+* K' := β.codRestrict K' hβm
  let i : K' →+* AlgebraicClosure K := K'.val.toRingHom
  have hi : spMap (algebraMap K (AlgebraicClosure K)) = spMap i ≫ spMap (algebraMap K K') :=
    Spec.map_comp (CommRingCat.ofHom (algebraMap K K')) (CommRingCat.ofHom i)
  obtain ⟨T', m, -⟩ := GlobalTheory.CM.PAT.exists_pullback E H _ _ (spMap (algebraMap K K')) T
  have hm : LBIso T'.t.PP.L (T.t.PP.L.pull m.φ) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨I', -, hI'⟩ := (GlobalTheory.PELDesc.tate_pull (D := D) T.t.PP.isLB T'.t.PP.isLB m.cart hm T.t.act.act T'.t.act.act m.act
    _ _ hi).2 I
  have hdet' : DetCond D T'.t.act (spMap i) ρ := (GlobalTheory.PELDesc.detCond_pull m.cart _ _ m.act _ _ hi ρ).2 hdet
  have hepi : Epi (spMap i) :=
    have := GlobalTheory.FieldBaseChange.flat_spMap i
    have := GlobalTheory.FieldBaseChange.surjective_spMap i
    Flat.epi_of_flat_of_surjective _
  have hex : ∀ a, ∃ e : 𝟙_ (Over (Sp K')) ⟶ T'.t.G, toUnit (Over.mk (spMap i)) ≫ e = I'.ev l.M a := fun a => by
    obtain ⟨y, hy⟩ := hS ⟨I.ev l.M a, (I.onto _ hM _).2 ⟨a, rfl⟩⟩ K' fun z hz =>
      IntermediateField.subset_adjoin K U (Or.inl (Set.mem_iUnion.2 ⟨_, hz⟩))
    replace hy : spMap i ≫ y = (I.ev l.M a).left := hy
    have w : y ≫ T.t.G.hom = 𝟙 _ ≫ spMap (algebraMap K K') := by
      rw [← cancel_epi (spMap i), ← Category.assoc, hy, Category.id_comp, ← hi]
      exact Over.w (I.ev l.M a)
    refine ⟨Over.homMk (m.cart.1.lift y _ w) (m.cart.1.lift_snd _ _ _), Over.OverMorphism.ext ?_⟩
    rw [Over.comp_left, Over.toUnit_left]
    show spMap i ≫ m.cart.1.lift y _ w = _
    refine m.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, IsPullback.lift_fst, hy]
      exact hI' _ _
    · rw [Category.assoc, IsPullback.lift_snd, Category.comp_id]
      exact (Over.w (I'.ev l.M a)).symm
  choose e he using hex
  have inj := GlobalTheory.HeckePoint.toUnit_comp_injective (spMap i) T'.t.G
  obtain ⟨u, hu, π, hπ, huπ⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 l.coprime)
  have hη : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      I'.ev l.M (π • a) = I'.ev l.M a := fun a h => by
    conv_rhs => rw [← one_smul (𝓞 E) a, ← huπ, add_smul, I'.add,
      (I'.ker _ hM _).2 (GlobalTheory.UnifObj.exists_smul_eq l.prod hu h), _root_.one_mul]
  let κ : KA l →+* K' := β'.comp (IntermediateField.inclusion c.le).toRingHom
  have hsm' := T'.ab.smooth
  let o : Obj D l (baseKA l) (spMap κ) :=
    { t := T'.t
      proper := T'.ab.proper
      ample := T'.ample
      ktriv := T'.ktriv
      eta := fun a => e (π • a)
      eta_add := fun a c => inj (by
        show toUnit _ ≫ _ = toUnit _ ≫ _
        rw [MonObj.comp_mul, he, he, he, smul_add, I'.add])
      eta_ker := fun a h => inj (by
        show toUnit _ ≫ _ = toUnit _ ≫ _
        rw [MonObj.comp_one, he]
        exact (I'.ker _ hM _).2 (GlobalTheory.UnifObj.exists_smul_eq ((mul_comm _ _).trans l.prod) hπ h))
      etaA := fun _ => 1
      etaA_add := fun _ _ => (_root_.mul_one _).symm
      etaA_ker := fun _ => rfl
      geom := fun k _ _ x δ hx => by
        obtain ⟨φ, rfl⟩ : ∃ φ : K' →+* k, x = spMap φ := ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩
        obtain rfl : φ.comp κ = δ :=
          congrArg CommRingCat.Hom.hom (Spec.map_injective ((Spec.map_comp _ _).trans hx))
        obtain ⟨ψ, rfl⟩ : ∃ ψ : AlgebraicClosure K →+* k, ψ.comp i = φ := by
          letI := φ.toAlgebra
          exact ⟨(IsAlgClosed.lift (R := K') (S := AlgebraicClosure K) (M := k)).toRingHom,
            RingHom.ext fun z => (IsAlgClosed.lift (R := K') (S := AlgebraicClosure K) (M := k)).commutes z⟩
        have hx' : spMap (ψ.comp i) = spMap ψ ≫ spMap i := Spec.map_comp (CommRingCat.ofHom i) (CommRingCat.ofHom ψ)
        rw [hx']
        obtain ⟨J, hJ⟩ := (GlobalTheory.TateIsoFieldExt.tateIso_fieldExt hL E H D _ T'.pol T'.t.act.act _ k ψ (spMap i)).1 I'
        refine ⟨?_, J, ?_, fun a => ?_, fun a h => ?_⟩
        · have := (GlobalTheory.detCond_iff_of_field_extension E H D _ T'.t.G _ k ψ (spMap i) T'.t.act ρ hsm').2 hdet'
          rw [← hβ] at this
          exact this
        · have h₁ := J.ζ_prim _ l.A_pos
          have h₂ := (baseKA l).ζ_prim
          rw [hA, IsPrimitiveRoot.one_right_iff] at h₁ h₂
          rw [hA, h₁, h₂, map_one, Units.val_one]
        · rw [hA, MonObj.comp_one]
          exact ((J.ker 1 one_pos a).2 ⟨a, (one_smul _ _).symm⟩).symm
        · refine Eq.trans ?_ ((hJ _ hM).2 a).symm
          rw [← hη a h, ← he, ← Category.assoc]
          exact congrArg (· ≫ e (π • a)) (toUnit_unique _ _) }
  obtain ⟨f, ⟨hf, ⟨n⟩⟩, -⟩ := Xo.rep _ (spMap κ) inferInstance o
  have hκ : f ≫ Xo.s = spMap β' ≫ spMap (IntermediateField.inclusion c.le).toRingHom :=
    hf.trans (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom β'))
  refine ⟨K', hfd, pullback.lift f _ hκ, T'.t, ⟨m⟩, ?_⟩
  rw [pullback.lift_fst]
  exact ⟨n.toSABMap⟩

end PositivityTheory.HtPt.Kftwo
end
end

section
noncomputable section

open IsLocalRing Formalism.L2.Pj

namespace PositivityTheory.HtPt.Kftwo

theorem exists_completion (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W] :
    ∃ (T : CDVR) (g : W →+* T.V), IsLocalHom g ∧ Function.Injective g := by
  obtain ⟨⟨hdom, hdvr⟩, hcpl, hinj, hloc, -⟩ := ReciprocityTheory.CA.Pt.completionDVR W
  haveI : CharZero (AdicCompletion (maximalIdeal W) W) := charZero_of_injective_algebraMap hinj
  exact ⟨CDVR.mk (AdicCompletion (maximalIdeal W) W),
    algebraMap W (AdicCompletion (maximalIdeal W) W), hloc, hinj⟩

theorem exists_cdvr_of_isIntegral {V A : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing A]
    [IsDedekindDomain A] [CharZero A] [Algebra V A] [Algebra.IsIntegral V A] (hinj : Function.Injective (algebraMap V A)) :
    ∃ (T : CDVR) (g : A →+* T.V), IsLocalHom (g.comp (algebraMap V A)) ∧ Function.Injective g := by
  have hker : RingHom.ker (algebraMap V A) ≤ maximalIdeal V := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  obtain ⟨P, hPmax, hPc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (maximalIdeal V) hker
  haveI : P.IsPrime := hPmax.isPrime
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    apply IsDiscreteValuationRing.not_a_field V
    rw [← hPc, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hinj]
  haveI : IsDomain (Localization.AtPrime P) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors P)
  haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP0 (Localization.AtPrime P)
  have hAinj : Function.Injective (algebraMap A (Localization.AtPrime P)) :=
    IsLocalization.injective (Localization.AtPrime P) (Ideal.primeCompl_le_nonZeroDivisors P)
  haveI : CharZero (Localization.AtPrime P) := charZero_of_injective_algebraMap hAinj
  obtain ⟨T, g0, hg0, hg0inj⟩ := exists_completion (Localization.AtPrime P)
  refine ⟨T, g0.comp (algebraMap A (Localization.AtPrime P)), ⟨fun x hx => ?_⟩, hg0inj.comp hAinj⟩
  simp only [RingHom.comp_apply] at hx
  have h1 : IsUnit (algebraMap A (Localization.AtPrime P) (algebraMap V A x)) := isUnit_of_map_unit g0 _ hx
  rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P] at h1
  by_contra hxu
  have hx' : x ∈ maximalIdeal V := hxu
  rw [← hPc] at hx'
  exact h1 (Ideal.mem_comap.mp hx')

theorem exists_cdvr {V K K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [CharZero K]
    [Algebra V K] [IsFractionRing V K] [Field K'] [Algebra K K'] [FiniteDimensional K K'] :
    ∃ (T : CDVR) (g : V →+* T.V) (j : K' →+* T.Fr), IsLocalHom g ∧
      (algebraMap T.V T.Fr).comp g = (j.comp (algebraMap K K')).comp (algebraMap V K) := by
  letI : Algebra V K' := ((algebraMap K K').comp (algebraMap V K)).toAlgebra
  haveI : IsScalarTower V K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  haveI : IsDedekindDomain (integralClosure V K') := integralClosure.isDedekindDomain V K K'
  haveI : IsFractionRing (integralClosure V K') K' :=
    integralClosure.isFractionRing_of_finite_extension K K'
  haveI : CharZero (integralClosure V K') :=
    ⟨fun m n h => Nat.cast_injective (R := K')
      (by simpa using congrArg (algebraMap (integralClosure V K') K') h)⟩
  have hVK' : Function.Injective (algebraMap V K') :=
    (algebraMap K K').injective.comp (IsFractionRing.injective V K)
  have hinj : Function.Injective (algebraMap V (integralClosure V K')) := by
    refine Function.Injective.of_comp (f := algebraMap (integralClosure V K') K') ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
    exact hVK'
  obtain ⟨T, g, hg, hginj⟩ := exists_cdvr_of_isIntegral hinj
  have hjinj : Function.Injective ((algebraMap T.V T.Fr).comp g) :=
    (IsFractionRing.injective T.V T.Fr).comp hginj
  refine ⟨T, g.comp (algebraMap V (integralClosure V K')),
    IsFractionRing.lift (K := K') hjinj, hg, ?_⟩
  ext x
  simp only [RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply V K K',
    IsScalarTower.algebraMap_apply V (integralClosure V K') K', IsFractionRing.lift_algebraMap]
  rfl

end PositivityTheory.HtPt.Kftwo
end
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels GlobalTheory.KeyUnitModels GlobalTheory.KeyCancel IsLocalRing

namespace PositivityTheory.HtPt.Kftwo

theorem isFibreOf_trans {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {G : Over (Sp R)} [GrpObj G]
    [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) {rig : LB.Gen (L.pull (eSec G))} {θ : L.Sec} {n : ℕ}
    {v : Fin n → (epsR R ⟶ G)} {x' : KeyIn R'} {x'' : KeyIn R''} {f : R →+* R'} {f' : R' →+* R''}
    (H : IsFibreOf x' G L rig θ v f) (H' : KeyPB x'' x' f') : IsFibreOf x'' G L rig θ v (f'.comp f) := by
  obtain ⟨φ, he, w, hg, F, hp, hw, hr, hs, hF, hε, hv⟩ := H
  obtain ⟨φ', he', w', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩ := H'
  have g := (isGen_iff w).1 hw
  have g' := (isGen_iff w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp x'.P.isLB w w' g g' hL x''.P.isLB
  have he'' : eSec x''.P.A ≫ φ' ≫ φ = spMap (f'.comp f) ≫ eSec G := by
    rw [← Category.assoc, he', Category.assoc, he, spMap_comp, Category.assoc]
  refine ⟨φ' ≫ φ, he'', w'', hg'.trans hg, F'.comp F, (hp'.comp hp).congr (spMap_comp f f').symm rfl,
    (isGen_iff w'').2 (T.pgen_comp x'.P.isLB g g'), ?_, ?_, fun a => ?_, ?_, fun i => ?_⟩
  · have r₀ := (maps_iff w _ (fun _ => eSec G) _ x'.rig rig (spMap f) _
      (rigPull_le φ (spMap f) he L) (fun _ => rfl)).1 hr
    have r₁ := (maps_iff w' _ (fun _ => eSec x'.P.A) _ x''.rig x'.rig (spMap f') _
      (rigPull_le φ' (spMap f') he' x'.P.L) (fun _ => rfl)).1 hr'
    have r₂ := T.pmaps_comp x'.P.isLB (fun _ => he') r₀ r₁
    rw [← spMap_comp] at r₂
    exact (maps_iff w'' _ (fun _ => eSec G) _ x''.rig rig (spMap (f'.comp f)) _
      (rigPull_le (φ' ≫ φ) (spMap (f'.comp f)) he'' L) (fun _ => rfl)).2 r₂
  · refine (appLE_eq_iff_stalk w'' θ x''.th).2 fun Z q z j k hj hk => ?_
    obtain ⟨i, hi⟩ := exists_chart x'.P.isLB (φ' (q z))
    have a := (appLE_eq_iff_stalk w θ x'.th).1 hs Z (q ≫ φ') z j i hj hi
    have b := (appLE_eq_iff_stalk w' x'.th x''.th).1 hs' Z q z i k hi hk
    rw [T _ q z j i k hj hi hk, ← Category.assoc, a, b, Units.val_mul, _root_.mul_assoc]
  · rw [RingHom.comp_apply, hF, hF', RingHom.comp_apply]
  · rw [RingHom.comp_apply, hε, hε']
  · rw [← Category.assoc, hv', Category.assoc, hv, spMap_comp, Category.assoc]
    rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_isFibreOf_pull {R R' R'' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] [CommRing R'']
    {f : R →+* R'} [IsLocalHom f] {f' : R' →+* R''} {t : SAB H (Sp R)} {t' : SAB H (Sp R')} (m : SABMap t' t (spMap f))
    {θ : t.PP.L.Sec} {n : ℕ} {v : Fin n → (epsR R ⟶ t.G)} (hθ : NonzeroClosed (X := t.G) θ) (hv : IsLieBasis v)
    {x : KeyIn R''} (hx : IsFibreOf x t.G t.PP.L t.PP.rig θ v (f'.comp f)) :
    ∃ (θ' : t'.PP.L.Sec) (v' : Fin n → (epsR R' ⟶ t'.G)), NonzeroClosed (X := t'.G) θ' ∧ IsLieBasis v' ∧
      IsFibreOf x t'.G t'.PP.L t'.PP.rig θ' v' f' := by
  obtain ⟨φ'', he'', w'', hg'', F'', hc'', hw'', hr'', hs'', hF'', hFe'', hv''⟩ := hx
  obtain ⟨w, hw, hr, -⟩ := m.lin
  have g := (isGen_iff w).1 hw
  have g'' := (isGen_iff w'').1 hw''
  obtain ⟨θ', hs⟩ := sec_pull_down g t.PP.isLB t'.PP.isLB θ
  obtain ⟨v', hv', hvv⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ f t.G t'.G m.φ m.cart t.semi.smooth n v hv
  have he : eSec t'.G ≫ m.φ = spMap f ≫ eSec t.G := m.cm.e_comm.trans (congrArg (· ≫ eSec t.G) m.base)
  have hrig : m.cm.rigPull t.PP.L t.PP.rig = rigPullOf m.φ (spMap f) he t.PP.L t.PP.rig := by
    have key : ∀ (a b : Sp R' ⟶ Sp R) (_ : a = b) ha hb,
        rigPullOf (G' := t'.G) m.φ a ha t.PP.L t.PP.rig = rigPullOf m.φ b hb t.PP.L t.PP.rig := by
      rintro a b rfl _ _
      rfl
    exact key _ _ m.base _ _
  rw [hrig] at hr
  refine ⟨θ', v', ?_, hv', ?_⟩
  · obtain ⟨z, hz, hz'⟩ := hθ
    obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback m.cart.1 z (closedPoint R')
      (hz.trans (IsLocalRing.comap_closedPoint f).symm)
    obtain ⟨k, hb⟩ := TopologicalSpace.Opens.mem_iSup.1 hz'
    have hk : m.φ y ∈ t.PP.L.U k := t.G.left.basicOpen_le _ hb
    obtain ⟨l, hl⟩ := exists_chart t'.PP.isLB y
    have u : IsUnit (gs (𝟙 _) (m.φ y) _ (θ.f k)) := by
      rw [gs_eq (𝟙 _) (m.φ y) _ hk]; exact (t.G.left.mem_basicOpen _ _ hk).1 hb
    have u₁ : IsUnit (gs m.φ y _ (θ.f k)) := by rw [gs_stalkMap m.φ y _ hk]; exact u.map _
    have e := hs _ (𝟙 _) y k l hk hl
    rw [Category.id_comp] at e
    have u₂ := isUnit_of_mul_isUnit_right (e ▸ u₁)
    rw [gs_eq (𝟙 _) y _ hl] at u₂
    exact ⟨y, hy, TopologicalSpace.Opens.mem_iSup.2 ⟨l, (t'.G.left.mem_basicOpen _ _ hl).2 u₂⟩⟩
  have hsp : spMap (f'.comp f) = spMap f' ≫ spMap f := spMap_comp _ _
  have hc := m.cart
  have hp := hc.1
  obtain ⟨φ', hφ, hw0⟩ : ∃ φ' : x.P.A.left ⟶ t'.G.left, φ' ≫ m.φ = φ'' ∧ φ' ≫ t'.G.hom = x.P.A.hom ≫ spMap f' :=
    ⟨hp.lift φ'' (x.P.A.hom ≫ spMap f') (by rw [hc''.1.w, Category.assoc, hsp]), hp.lift_fst _ _ _,
      hp.lift_snd _ _ _⟩
  subst hφ
  have he' : eSec x.P.A ≫ φ' = spMap f' ≫ eSec t'.G := by
    apply hp.hom_ext
    · rw [Category.assoc, he'', hsp, Category.assoc, Category.assoc, he]
    · have a₁ : eSec x.P.A ≫ x.P.A.hom = 𝟙 _ := Over.w η[x.P.A]
      have a₂ : eSec t'.G ≫ t'.G.hom = 𝟙 _ := Over.w η[t'.G]
      rw [Category.assoc, hw0, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  obtain ⟨w', T⟩ := exists_cancel t.PP.isLB w w'' g g'' t'.PP.isLB x.P.isLB
  have r := (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig (spMap f) _ (rigPull_le m.φ (spMap f) he t.PP.L)
    (fun _ => rfl)).1 hr
  have r'' := (maps_iff w'' _ (fun _ => eSec t.G) _ x.rig t.PP.rig (spMap (f'.comp f)) _
    (rigPull_le (φ' ≫ m.φ) (spMap (f'.comp f)) he'' t.PP.L) (fun _ => rfl)).1 hr''
  rw [hsp] at r''
  have hFF : (Chart.dualMapR f').comp (Chart.dualMapR f) = F'' := dualNumber_ringHom_ext
    (fun a => by
      rw [RingHom.comp_apply, hF'']
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by
      rw [RingHom.comp_apply, hFe'']
      ext <;> simp [Chart.dualMapR])
  refine ⟨φ', he', w', hg'', Chart.dualMapR f', hc.cancel (hc''.congr hsp rfl) hw0,
    (isGen_iff w').2 (T.pgen_cancel t.PP.isLB g g''),
    (maps_iff w' _ (fun _ => eSec t'.G) _ x.rig t'.PP.rig (spMap f') _ (rigPull_le φ' (spMap f') he' t'.PP.L)
      (fun _ => rfl)).2 (T.pmaps_cancel t.PP.isLB (fun _ => he') r r''),
    (appLE_eq_iff_stalk w' θ' x.th).2 fun Z q z i k hi hk => ?_, fun a => ?_, ?_, fun i => ?_⟩
  · obtain ⟨j, hj⟩ := exists_chart t.PP.isLB (m.φ (φ' (q z)))
    have a := hs Z (q ≫ φ') z j i hj hi
    have b := (appLE_eq_iff_stalk w'' θ x.th).1 hs'' Z q z j k hj hk
    rw [T Z q z j i k hj hi hk, ← Category.assoc, a, Units.val_mul, _root_.mul_assoc] at b
    exact (Units.mul_right_inj _).1 b
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]
  · apply hp.hom_ext
    · rw [Category.assoc, hv'', Category.assoc, hvv, ← hFF, ← Category.assoc, spMap_comp]
    · rw [Category.assoc, hw0, ← Category.assoc, Over.w, Category.assoc, Over.w]
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_pat_of_isFibreOf {R R' : Type} [CommRing R] [CommRing R'] {f : R →+* R'} {t : SAB H (Sp R)}
    {t' : SAB H (Sp R')} (m : SABMap t' t (spMap f)) {θ : t.PP.L.Sec} {n : ℕ} {v : Fin n → (epsR R ⟶ t.G)}
    {x : KeyIn R'} (hx : IsFibreOf x t.G t.PP.L t.PP.rig θ v f) : ∃ T : GlobalTheory.CM.PAT H (Sp R'), T.t = t' ∧ T.g = x.P.g := by
  obtain ⟨φ, -, w, -, -, hc, hw, -⟩ := hx
  obtain ⟨w'', hw'', -⟩ := m.lin
  obtain ⟨ψ, hψ, hψ₀⟩ : ∃ ψ : t'.G.left ⟶ x.P.A.left, ψ ≫ φ = m.φ ∧ ψ ≫ x.P.A.hom = t'.G.hom ≫ 𝟙 _ :=
    ⟨hc.1.lift m.φ t'.G.hom m.cart.1.w, hc.1.lift_fst _ _ _, (hc.1.lift_snd _ _ _).trans (Category.comp_id _).symm⟩
  have hp : IsGrpPullback t'.G x.P.A (𝟙 _) ψ := hc.cancel (m.cart.congr (Category.id_comp _).symm hψ.symm) hψ₀
  have e : LBIso t'.PP.L (x.P.L.pull ψ) := by
    have key : ∀ (χ : t'.G.left ⟶ t.G.left) (_ : ψ ≫ φ = χ) (u : LB.Iso t'.PP.L (t.PP.L.pull χ)), u.IsGen →
        LBIso t'.PP.L (x.P.L.pull ψ) := by
      rintro _ rfl u hu
      have g := (isGen_iff w).1 hw
      have g'' := (isGen_iff u).1 hu
      obtain ⟨w', T⟩ := exists_cancel t.PP.isLB w u g g'' x.P.isLB t'.PP.isLB
      exact ⟨w', (isGen_iff w').2 (T.pgen_cancel t.PP.isLB g g'')⟩
    exact key _ hψ w'' hw''
  obtain ⟨h₁, h₂, h₃⟩ := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally _ _ x.P.A t'.G _ ψ
    x.P.L t'.PP.L x.P.isLB t'.PP.isLB x.P.isAb hp e
  have hs : Out.Sym t'.G t'.PP.L := by
    obtain ⟨-, w, hw, -⟩ := t'.sym
    exact fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff w).1 hw) _⟩
  have hd : SmoothOfRelativeDimension x.P.g t'.G.hom :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} x.P.g
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension x.P.g) hp.1 x.P.smoothDim
  exact ⟨⟨t', h₁, x.P.g, hd, hs, h₂ x.P.ample, h₃ x.P.ktriv⟩, rfl, rfl⟩

theorem nonzeroClosed_of_primitive {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {G : Over (Sp V)}
    [Smooth G.hom] {L : LB G.left} (θ : L.Sec)
    (h : ∀ (d : V) (θ' : L.Sec), (∀ i, θ.f i = constFn G.hom _ d * θ'.f i) → IsUnit d) : NonzeroClosed (X := G) θ := by
  by_contra hn
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hred : IsReduced (pullback G.hom (Spec.map (CommRingCat.ofHom (residue V)))) :=
    isReduced_of_smooth (pullback.snd G.hom (spMap (residue V)))
  obtain ⟨σ, hσ⟩ := DVR.exists_div_sec_of_thick G.hom (maximalIdeal V) hϖ.ne_zero hϖ.maximalIdeal_eq.le θ
    (fun j z hz => by
      have : IsReduced (pullback G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal V))))) := hred
      have z₀ : ((pullback.fst G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal V))))).app
          (L.U j)).hom (θ.f j) = 0 := by
        rw [← basicOpen_eq_bot_iff, eq_bot_iff]
        intro y hy
        rw [← Scheme.preimage_basicOpen] at hy
        refine (hn ⟨_, ?_, TopologicalSpace.Opens.mem_iSup.2 ⟨j, hy⟩⟩).elim
        exact (congrArg (fun q : pullback G.hom (spMap (residue V)) ⟶ Sp V => q y) pullback.condition).trans
          (PrimeSpectrum.comap_residue V _)
      rw [gs_eq _ _ _ hz, z₀, map_zero]
      exact dvd_zero _)
  exact hϖ.not_isUnit (h ϖ σ hσ)

end PositivityTheory.HtPt.Kftwo
end
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels Formalism.L2.Pj

namespace PositivityTheory.HtPt.Kftwo

theorem exists_valuationSubring_two : ∃ W : ValuationSubring ℂ, ((2 : ℕ) : ℂ) ∈ W.nonunits := by
  have h : Ideal.span {(2 : (⊥ : Subring ℂ))} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    obtain ⟨⟨b, hb⟩, e⟩ := hu.exists_right_inv
    obtain ⟨n, rfl⟩ := Subring.mem_bot.1 hb
    have e' : (2 : ℂ) * n = 1 := congrArg Subtype.val e
    have e'' : (2 : ℤ) * n = 1 := by exact_mod_cast e'
    omega
  obtain ⟨W, -, hW⟩ := Ideal.image_subset_nonunits_valuationSubring _ h
  exact ⟨W, hW ⟨2, Ideal.mem_span_singleton_self _, (map_ofNat _ 2).trans (by simp)⟩⟩

theorem exists_place (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] {V K : Type} [CommRing V] [IsDomain V]
    [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (io : F →+* K) :
    ∃ (p : ℕ) (W : ValuationSubring ℂ) (b : W.comap F.val.toRingHom →+* V), p.Prime ∧ (p : ℂ) ∈ W.nonunits ∧
      (algebraMap V K).comp b = io.comp (W.comap F.val.toRingHom).subtype := by
  have hinj := IsFractionRing.injective V K
  let U : ValuationSubring F :=
    { (algebraMap V K).range.comap io with
      mem_or_inv_mem' := fun a => by
        have := ValuationRing.isInteger_or_isInteger V (io a)
        rw [← map_inv₀] at this
        exact this }
  obtain ⟨p, W, hp, hW, hle⟩ : ∃ (p : ℕ) (W : ValuationSubring ℂ), p.Prime ∧ (p : ℂ) ∈ W.nonunits ∧
      W.comap F.val.toRingHom ≤ U := by
    by_cases h : ∃ p : ℕ, p.Prime ∧ (p : F) ∈ U.nonunits
    · obtain ⟨p, hp, hpU⟩ := h
      obtain ⟨W, hWe, hWn⟩ := GlobalTheory.Reg.exists_valuationSubring_comap_eq_nonunits F.val.toRingHom U
      exact ⟨p, W, hp, by simpa using hWn _ hpU, hWe.le⟩
    · obtain ⟨W, hW⟩ := exists_valuationSubring_two
      refine ⟨2, W, Nat.prime_two, hW, fun a _ => ?_⟩
      have hn : ∀ n : ℕ, (n : F)⁻¹ ∈ U := fun n => by
        induction n using Nat.recOnMul with
        | zero => simp
        | one => simp
        | prime p hp =>
          by_contra hc
          refine h ⟨p, hp, ?_⟩
          rw [ValuationSubring.mem_nonunits_iff_or]
          exact Or.inr hc
        | mul a b ha hb => rw [Nat.cast_mul, mul_inv]; exact U.mul_mem _ _ ha hb
      have hq : ∀ q : ℚ, algebraMap ℚ F q ∈ U := fun q => by
        rw [eq_ratCast, Rat.cast_def, div_eq_mul_inv]
        exact U.mul_mem _ _ (intCast_mem U _) (hn _)
      let _ : Algebra ℚ U := ((algebraMap ℚ F).codRestrict U.toSubring hq).toAlgebra
      have : IsScalarTower ℚ U F := IsScalarTower.of_algebraMap_eq fun _ => rfl
      have hi : IsIntegral U a := (Algebra.IsIntegral.isIntegral (R := ℚ) a).tower_top
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
      exact hy ▸ y.2
  let e := RingEquiv.ofBijective (algebraMap V K).rangeRestrict
    ⟨fun a a' h => hinj (congrArg Subtype.val h), (algebraMap V K).rangeRestrict_surjective⟩
  refine ⟨p, W, e.symm.toRingHom.comp ((io.comp (W.comap F.val.toRingHom).subtype).codRestrict (algebraMap V K).range
    fun a => hle a.2), hp, hW, RingHom.ext fun a => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem key_unit {κ : KeyRule} (hκ : IsKeyRule κ) (hpq : 1 ≤ Dw.p + Dw.q) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p)
    {T : CDVR} (z : Sp T.Fr ⟶ Xo.XF c) {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)}
    (m1 : SABMap t' Xo.univ.t (z ≫ pullback.fst _ _)) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))) {n : ℕ}
    {w : Fin n → (epsR T.V ⟶ G.G)} (hw : IsLieBasis w) {θ : G.PP.L.Sec} (hθ : Generates (X := G.G) θ) (k : KeyIn T.Fr)
    (hk : IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr)) :
    ∃ u : T.Vˣ, (κ T.Fr k : T.Fr) = algebraMap T.V T.Fr u := by
  classical
  obtain ⟨io, hzs⟩ : ∃ io : c.F →+* T.Fr, spMap io = z ≫ pullback.snd _ _ := ⟨_, Spec.map_preimage _⟩
  have := c.fin
  obtain ⟨p, W, b, hp, hW, hb⟩ := exists_place c.F (V := T.V) io
  have key : ∀ X : ∀ l : Level H, Moduli Dw l, ∃ Y : Model (X l) c (c.V W).subtype,
      Y.LevelStructureConditions p ∧ Y.N3 ∧ Y.N4 ∧ Y.SplitFibres := fun X => by
    obtain ⟨Y, hY, -⟩ := GlobalTheory.partI_closed.2 E H Dw hpq X
    obtain ⟨h1, h2⟩ := hY p W hp hW
    obtain ⟨h3, h4, h5⟩ := h2 ⟨l, c, hg p hp⟩
    exact ⟨_, h1.1 ⟨l, c, hg p hp⟩, h4, h5, h3⟩
  have h := key (Function.update (fun l' => Classical.choice (GlobalTheory.Moduli.moduli_scheme_exists E H Dw l' hpq)) l Xo)
  rw [Function.update_self] at h
  obtain ⟨Y, h2, h3, h4, h5⟩ := h
  have hx : z ≫ Y.j ≫ Y.s = Out.jK T.V ≫ spMap b := by
    show z ≫ (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, ← hzs]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) hb.symm
  obtain ⟨yt, h1, -⟩ := extPt Y T b z hx
  obtain ⟨tP, ⟨mP'⟩⟩ : ∃ t : SAB H (Sp T.V), Nonempty (SABMap t Y.t yt) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull yt Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨mF, -⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t Y.oF.t t' (pullback.fst _ _) z Y.m0.toSABMap m1
  obtain ⟨mJ, -⟩ := sabComp pullCubComp E H _ _ _ Y.t Y.oF.t t' (Y.jQ ≫ pullback.fst _ _) z Y.m mF
  have hj : z ≫ Y.jQ ≫ pullback.fst _ _ = Out.jK T.V ≫ yt := h1.symm
  obtain ⟨mK, -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t tP t' yt (Out.jK T.V) mP' (PullbackSections.sabMapCast mJ hj)
  have hprop : IsProper t'.G.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) m1.cart.1 Xo.univ.proper
  obtain ⟨ψ, -⟩ := GlobalTheory.semiAbelian_model_determined_by_generic_fibre E H T.V inferInstance G tP t' hprop m2 mK
  obtain ⟨n', -⟩ := sabComp pullCubComp E H _ _ _ Y.t tP G yt (𝟙 _) mP' ψ
  exact (((GlobalTheory.T.thetaKeyScalar_isUnit_on_integralModels κ hκ E H Dw l Xo c _ _ Y p hpq (isBaseRing_local c W) hp h2 h3 h4 h5).1 T.V T.Fr z yt h1 G
    (PullbackSections.sabMapCast n' (Category.id_comp yt)) n w hw θ k hk).1 hθ).1

end PositivityTheory.HtPt.Kftwo
end
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.HtPt.Kftwo

section Unit

open GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels GlobalTheory.KeyUnitModels Formalism.L2.Pj

theorem lieMult_comp {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] (act : OAct O G) (σ : O ≃+* O)
    (s : G ≅ G) [IsMonHom s.hom] (hs : ∀ a, act.act (σ a) ≫ s.hom = s.hom ≫ act.act a) {k : Type} [Field k]
    (z : Sp k ⟶ S) (τ : O →+* k) (n : ℕ) (h : LieMult act z τ n) : LieMult act z (τ.comp σ.toRingHom) n := by
  have e := GlobalTheory.LiePull.lieMult_pull O S S G G (𝟙 S) s.hom.left act (GlobalTheory.Serre.comapAct act σ.toRingHom)
    (isGrpPullback_of_iso s) (fun c => congrArg (fun q => q.left) (hs c)) k z (τ.comp σ.toRingHom) n
  rw [Category.comp_id] at e
  refine e.1 ?_
  have key : ∀ v, IsLieEigen (GlobalTheory.Serre.comapAct act σ.toRingHom) z (τ.comp σ.toRingHom) v ↔ IsLieEigen act z τ v :=
    fun v => and_congr_right fun _ => ⟨fun hv a => by
      obtain ⟨b, rfl⟩ := σ.surjective a
      exact hv b, fun hv a => hv (σ a)⟩
  obtain ⟨v, h₁, h₂⟩ := h
  exact ⟨v, fun i => (key _).2 (h₁ i), fun w hw => h₂ w ((key _).1 hw)⟩

variable {E E' : Type} [Field E] [NumberField E] [IsCMField E] [Field E'] [NumberField E'] [IsCMField E']
  {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {H' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E'}

theorem exists_type (Q : PairHost H H') {V Ω : Type} [CommRing V] [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (f : V →+* Ω)
    (T : SAB H' (Sp V)) (s : T.G ≅ T.G) [IsMonHom s.hom] (hs : ∀ a, T.act.act (Q.σ a) ≫ s.hom = s.hom ≫ T.act.act a)
    {m : ℕ} {w : Fin m → (epsR V ⟶ T.G)} (hw : IsLieBasis w) :
    ∃ (ρ : Ω) (p q : ℕ), ρ ^ 2 = -(H'.d : Ω) ∧ ∀ τ : 𝓞 E' →+* Ω,
      (τ H'.rt = ρ → LieMult T.act (spMap f) τ p) ∧ (τ H'.rt ≠ ρ → LieMult T.act (spMap f) τ q) := by
  obtain ⟨M, hM⟩ := GlobalTheory.exists_lie_coordinates_lieMult_iff _ V T.G T.act m w T.semi.smooth hw
  obtain ⟨M', -, hM'⟩ := hM Ω f
  let τ₀ : 𝓞 E' →+* Ω := (IsAlgClosed.lift (R := ℚ) (S := E') (M := Ω)).toRingHom.comp (algebraMap (𝓞 E') E')
  let τ₁ : 𝓞 E' →+* Ω := τ₀.comp H'.bar.toRingHom
  have sq : ∀ τ : 𝓞 E' →+* Ω, τ H'.rt ^ 2 = -(H'.d : Ω) := fun τ => by rw [← map_pow, H'.rt_sq, map_neg, map_natCast]
  have h₁ : τ₁ H'.rt = -τ₀ H'.rt := by
    show τ₀ (H'.bar H'.rt) = _
    rw [GlobalTheory.HostModel.bar_rt, map_neg]
  have mv : ∀ (τ τ' : 𝓞 E' →+* Ω) (n : ℕ), τ H'.rt = τ' H'.rt → LieMult T.act (spMap f) τ n →
      LieMult T.act (spMap f) τ' n := fun τ τ' n e h => by
    rcases Q.chars Ω τ τ' e with rfl | rfl
    · exact h
    · exact lieMult_comp T.act Q.σ s hs _ τ n h
  refine ⟨τ₀ H'.rt, _, _, sq τ₀, fun τ => ⟨fun e => mv τ₀ τ _ e.symm ((hM' τ₀ _).2 rfl),
    fun e => mv τ₁ τ _ ?_ ((hM' τ₁ _).2 rfl)⟩⟩
  rw [h₁]
  exact ((sq_eq_sq_iff_eq_or_eq_neg.1 ((sq τ).trans (sq τ₀).symm)).resolve_left e).symm

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

theorem key_isUnit {κ : KeyRule} (hκ : IsKeyRule κ) (hpow : ∀ (K : Type) [Field K] [CharZero K] (x y : KeyIn K) (j : ℕ),
      GlobalTheory.KeyPow.IsKeyPow y x j → κ K y = κ K x ^ j)
    {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [CharZero K] [Algebra V K]
    [IsFractionRing V K] (t : SAB H (Sp V)) (θ : t.PP.L.Sec) {n : ℕ} (w : Fin n → (epsR V ⟶ t.G)) (x : KeyIn K)
    (hx : IsFibreOf x t.G t.PP.L t.PP.rig θ w (algebraMap V K)) (hw : IsLieBasis w) (hθ : NonzeroClosed (X := t.G) θ) :
    ∃ u : Vˣ, (κ K x : K) = algebraMap V K u := by
  obtain ⟨E', _, _, _, H', ⟨Q⟩⟩ := exists_pairHost H
  obtain ⟨y, hy⟩ := GlobalTheory.KeyPow.exists_isKeyPow K x 2 (by norm_num)
  obtain ⟨T, s, θ₂, m, w₂, hs₁, hs₂, hw₂, hθ₂, hy₂⟩ := exists_square Q _ t θ w x y hx hw hθ hy
  let Ω := AlgebraicClosure K
  let i := algebraMap K Ω
  obtain ⟨ρ, p, q, hρ, hty⟩ := exists_type Q (i.comp (algebraMap V K)) T s hs₂ hw₂
  obtain ⟨tK, ⟨mK⟩⟩ := exists_pull (spMap (algebraMap V K)) T
  obtain ⟨TK, rfl, hgK⟩ := exists_pat_of_isFibreOf mK hy₂
  obtain ⟨tΩ, ⟨mΩ⟩⟩ := exists_pull (spMap i) TK.t
  obtain ⟨⟨TΩ, rfl, hgΩ⟩, hL⟩ := GlobalTheory.CM.PAT.exists_of_sabMap E' H' _ _ _ TK tΩ mΩ
  have lK : ∀ τ N, LieMult T.act (spMap (i.comp (algebraMap V K))) τ N → LieMult TK.t.act (spMap i) τ N := fun τ N h =>
    (GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ T.act TK.t.act mK.cart mK.act Ω (spMap i) τ N).2 (by rwa [← spMap_comp])
  have lΩ : ∀ τ N, LieMult TK.t.act (spMap i) τ N → LieMult TΩ.t.act (𝟙 _) τ N := fun τ N h =>
    (GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ TK.t.act TΩ.t.act mΩ.cart mΩ.act Ω (𝟙 _) τ N).2 (by rwa [Category.id_comp])
  obtain ⟨D, rfl, rfl, hpq, ⟨I⟩⟩ := exists_datum_tate TΩ (by rw [hgΩ, hgK]; exact y.g_pos) ρ hρ p q
    fun τ => ⟨fun e => lΩ _ _ (lK _ _ ((hty τ).1 e)), fun e => lΩ _ _ (lK _ _ ((hty τ).2 e))⟩
  obtain ⟨I', -⟩ := (GlobalTheory.PELDesc.tate_pull (D := D) TK.t.PP.isLB TΩ.t.PP.isLB mΩ.cart (LBIso.symm hL) TK.t.act.act
    TΩ.t.act.act mΩ.act (𝟙 _) (spMap i) (Category.id_comp _).symm).1 I
  obtain ⟨l, hA, hgood, -⟩ := GlobalTheory.exists_level_goodAt_all_primes_and_idx E' H' 1 one_pos
  obtain ⟨Xo⟩ := GlobalTheory.Moduli.moduli_scheme_exists E' H' D l hpq
  obtain ⟨K', _, z, t', ⟨m₁⟩, ⟨m₂⟩⟩ := exists_point hA Xo (GlobalTheory.LevelExist.minCoeff l) TK ρ hρ
    (fun τ => ⟨fun e => lK _ _ ((hty τ).1 e), fun e => lK _ _ ((hty τ).2 e)⟩) I'
  obtain ⟨T₀, g, j, _, hgj⟩ := exists_cdvr (V := V) (K := K) (K' := K')
  have : CharZero T₀.Fr := charZero_of_injective_algebraMap (IsFractionRing.injective T₀.V T₀.Fr)
  let j₀ : K →+* T₀.Fr := j.comp (algebraMap K K')
  obtain ⟨G, ⟨mG⟩⟩ := exists_pull (spMap g) T
  obtain ⟨t'', ⟨m₃⟩⟩ := exists_pull (spMap j) t'
  obtain ⟨n₁, -⟩ := sabComp pullCubComp E' H' _ _ _ _ _ _ _ _ m₂ m₃
  obtain ⟨n₂, -⟩ := sabComp pullCubComp E' H' _ _ _ _ _ _ _ _ m₁ m₃
  obtain ⟨n₃, -⟩ := sabComp pullCubComp E' H' _ _ _ _ _ _ _ _ mK n₂
  obtain ⟨n₄, -⟩ := sabCancel pullCubCancel E' H' _ _ _ T G t'' (spMap g) (spMap (algebraMap T₀.V T₀.Fr)) mG
    (PullbackSections.sabMapCast n₃ (by rw [← spMap_comp, ← spMap_comp, ← spMap_comp, hgj, RingHom.comp_assoc]))
  obtain ⟨y', hy'⟩ := GlobalTheory.KeyPow.exists_keyPB_ring y j₀
  have hf := isFibreOf_trans T.PP.isLB hy₂ hy'
  rw [← hgj] at hf
  obtain ⟨θ', w', hθ', hw', hf'⟩ := exists_isFibreOf_pull mG hθ₂ hw₂ hf
  have := G.semi.smooth
  obtain ⟨u, hu⟩ := key_unit hκ hpq hgood (spMap j ≫ z) (PullbackSections.sabMapCast n₁ (Category.assoc _ _ _).symm) n₄ hw'
    (generates_of_isFibreOf G.PP.isLB hf' hθ') y' hf'
  rw [hκ.2.1 K T₀.Fr j₀ y y' hy', hpow K x y 2 hy, Units.val_pow_eq_pow_val] at hu
  have hj : ∀ a : V, j₀ (algebraMap V K a) = algebraMap T₀.V T₀.Fr (g a) := fun a => (RingHom.congr_fun hgj a).symm
  have inj := IsFractionRing.injective T₀.V T₀.Fr
  rcases ValuationRing.isInteger_or_isInteger V (κ K x : K) with ⟨a, ha⟩ | ⟨a, ha⟩
  · rw [← ha, ← map_pow, hj] at hu
    have hau : IsUnit a := isUnit_of_dvd_unit (dvd_pow_self a two_ne_zero)
      (isUnit_of_map_unit g _ (inj hu ▸ u.isUnit))
    exact ⟨hau.unit, ha.symm⟩
  · have e : algebraMap T₀.V T₀.Fr (g (a ^ 2) * u) = algebraMap T₀.V T₀.Fr 1 := by
      rw [map_mul, ← hu, ← hj, ← map_mul, map_pow, ha, ← mul_pow, inv_mul_cancel₀ (κ K x).ne_zero, one_pow, map_one, map_one]
    have hau : IsUnit a := isUnit_of_dvd_unit (dvd_pow_self a two_ne_zero)
      (isUnit_of_map_unit g _ (IsUnit.of_mul_eq_one _ (inj e)))
    refine ⟨hau.unit⁻¹, ?_⟩
    rw [map_units_inv, IsUnit.unit_spec, ha, inv_inv]

end Unit

section Main

open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights TensorProduct GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem key_integral : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.UnitSp κ →
    GlobalTheory.KeyCl.ThetaOne κ → GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDomain R]
      [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (t : SAB H (Sp R))
      (th : t.PP.L.Sec) (x : KeyIn K) (v : Fin x.P.g → (epsR R ⟶ t.G)),
      KeyOver (algebraMap R K) t th x v → IsLieBasis v →
      (∀ (d : R) (th' : t.PP.L.Sec), (∀ i, th.f i = constFn t.G.hom _ d * th'.f i) → IsUnit d) →
      (κ K x : K) ∈ Set.range (algebraMap R K) := by
  intro κ k₁ k₂ k₃ k₄ k₅ E _ _ _ H R K _ _ _ _ _ _ _ t th x v ⟨φ, he, w, h1, h2, h3, h4, h5⟩ hv hprim
  have hκ : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ := by
    refine ⟨?_, k₂, k₃, k₄, ?_⟩
    · simpa only [GlobalTheory.KeyCl.Homog, _root_.mul_one] using k₁
    · simpa only [GlobalTheory.KeyCl.ArchNorm, _root_.mul_one] using k₅
  have := t.semi.smooth
  obtain ⟨u, hu⟩ := key_isUnit hκ (GlobalTheory.KeyCl.rule_pow κ k₁ k₂ k₄) t th v x
    ⟨φ, he, w, rfl, dualMap (algebraMap R K), h1, h2, h3, h4,
      fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl], by ext <;> simp [dualMap], h5⟩
    hv (nonzeroClosed_of_primitive th hprim)
  exact ⟨u, hu.symm⟩

theorem kp : KeyBadSt :=
  fun κ k₁ k₂ k₃ k₄ k₅ E _ _ _ H R K _ _ _ _ _ _ _ _ => key_integral κ k₁ k₂ k₃ k₄ k₅ E H R K

end Main

end PositivityTheory.HtPt.Kftwo
end
end
