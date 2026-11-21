import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumProjSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBCTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckDeformationOfLifting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomLiftingNilpotentDividedPowersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueTorsionLiftOfHenselian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentCompatibility
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsGluedFirstOrderDeformationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFirstOrderDeformationsBasisCountStatement

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harris_taylor_object_maps_compose_cancel : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp R) (s₂ : S₂ ⟶ Sp R) (s₃ : S₃ ⟶ Sp R) (o₁ : GlobalTheory.UPel.HT.Obj b N s₁) (o₂ : GlobalTheory.UPel.HT.Obj b N s₂) (o₃ : GlobalTheory.UPel.HT.Obj b N s₃) (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃), (Nonempty (GlobalTheory.UPel.HT.ObjMap o₁ o₂ f) → Nonempty (GlobalTheory.UPel.HT.ObjMap o₂ o₃ g) → Nonempty (GlobalTheory.UPel.HT.ObjMap o₁ o₃ (f ≫ g))) ∧ (Nonempty (GlobalTheory.UPel.HT.ObjMap o₁ o₃ (f ≫ g)) → Nonempty (GlobalTheory.UPel.HT.ObjMap o₂ o₃ g) → Nonempty (GlobalTheory.UPel.HT.ObjMap o₁ o₂ f)) := by
  first | exact @GlobalTheory.UPel.HT.objMap_comp_cancel | exact GlobalTheory.UPel.HT.objMap_comp_cancel | (intros; apply GlobalTheory.UPel.HT.objMap_comp_cancel <;> assumption)
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.UPel.HT.Pull

section Act

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

def OActN.pullback {O : Type} [Ring O] (A : Over S) [GrpObj A] (a : GlobalTheory.UPel.HT.OActN O A) :
    GlobalTheory.UPel.HT.OActN O ((Over.pullback f).obj A) where
  act x := (Over.pullback f).map (a.act x)
  hom x := by have := a.hom x; infer_instance
  one := by rw [a.one, CategoryTheory.Functor.map_id]
  mul x y := by rw [a.mul, CategoryTheory.Functor.map_comp]
  add x y := by rw [a.add]; exact CategoryTheory.Functor.map_mul _ _ _

theorem OActN.pullback_left {O : Type} [Ring O] (A : Over S) [GrpObj A] (a : GlobalTheory.UPel.HT.OActN O A) (c : O) :
    ((OActN.pullback f A a).act c).left ≫ pullback.fst A.hom f = pullback.fst A.hom f ≫ (a.act c).left :=
  pullback.lift_fst _ _ _

end Act

section Sq

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}

def sqMap (w : φ ≫ A.hom = A'.hom ≫ f) : (G2 A').left ⟶ (G2 A).left :=
  (lift (pushPt w (fst A' A')) (pushPt w (snd A' A'))).left

theorem pushPt_left (w : φ ≫ A.hom = A'.hom ≫ f) {T : Over S'} (x : T ⟶ A') : (pushPt w x).left = x.left ≫ φ := rfl

theorem pushPt_comp (w : φ ≫ A.hom = A'.hom ≫ f) {T U : Over S'} (g : T ⟶ U) (x : U ⟶ A') :
    pushPt w (g ≫ x) = (Over.homMk g.left (by
      show g.left ≫ U.hom ≫ f = T.hom ≫ f
      rw [← Category.assoc, Over.w g]) : Over.mk (T.hom ≫ f) ⟶ Over.mk (U.hom ≫ f)) ≫ pushPt w x :=
  Over.OverMorphism.ext (Category.assoc _ _ _)

theorem lift_sqMap (w : φ ≫ A.hom = A'.hom ≫ f) {T : Over S'} (a b : T ⟶ A') :
    (lift a b).left ≫ sqMap w = (lift (pushPt w a) (pushPt w b)).left := by
  have e := pushPt_comp w (lift a b) (fst A' A')
  have e' := pushPt_comp w (lift a b) (snd A' A')
  rw [lift_fst] at e
  rw [lift_snd] at e'
  rw [e, e', ← comp_lift]
  rfl

theorem isSquare_sqMap (w : φ ≫ A.hom = A'.hom ≫ f) : IsSquare φ (sqMap w) := by
  constructor
  · show (lift (pushPt w (fst A' A')) (pushPt w (snd A' A')) ≫ fst A A).left = _
    rw [lift_fst]; rfl
  · show (lift (pushPt w (fst A' A')) (pushPt w (snd A' A')) ≫ snd A A).left = _
    rw [lift_snd]; rfl

end Sq

section Tate

variable {p : ℕ} [Fact p.Prime]

def tateMoveO {D : GlobalTheory.UPel.HT.Datum p} {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q']
    {act : D.O → Q → Q} {act' : D.O → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop}
    (Φ : Q' ≃* Q) (hact : ∀ c x, Φ (act' c x) = act c (Φ x)) (he : ∀ n x y c, e n (Φ x) (Φ y) c → e' n x y c)
    (I : GlobalTheory.UPel.HT.TateIsoO D k Q act e) : GlobalTheory.UPel.HT.TateIsoO D k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev := fun n a => Φ.symm (I.ev n a)
  add := fun n a b => by simp only [I.add, map_mul]
  lin := fun n c a => by
    apply Φ.injective
    rw [MulEquiv.apply_symm_apply, hact, MulEquiv.apply_symm_apply]
    exact I.lin n c a
  ker := fun n hn hp a => (map_eq_one_iff _ Φ.symm.injective).trans (I.ker n hn hp a)
  onto := fun n hn hp x => by
    rw [← map_eq_one_iff Φ Φ.injective, map_pow, I.onto n hn hp]
    exact exists_congr fun a => Φ.symm_apply_eq.symm
  tower := fun n m hn hm hp a => by rw [← map_pow, I.tower n m hn hm hp a]
  isom := fun n hn hp a b => he _ _ _ _ (by
    rw [Φ.apply_symm_apply, Φ.apply_symm_apply]
    exact I.isom n hn hp a b)

theorem tateMoveO_ev {D : GlobalTheory.UPel.HT.Datum p} {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q']
    {act : D.O → Q → Q} {act' : D.O → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop}
    (Φ : Q' ≃* Q) (hact : ∀ c x, Φ (act' c x) = act c (Φ x)) (he : ∀ n x y c, e n (Φ x) (Φ y) c → e' n x y c)
    (I : GlobalTheory.UPel.HT.TateIsoO D k Q act e) (n : ℕ) (a : D.La) :
    (tateMoveO Φ hact he I).ev n a = Φ.symm (I.ev n a) := rfl

end Tate

section Pts

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}

theorem sqMap_of (w : φ ≫ A.hom = A'.hom ≫ f) {T : Over S'} {T₀ : Over S} (u : Over.mk (T.hom ≫ f) ⟶ T₀)
    (a' b' : T ⟶ A') (a b : T₀ ⟶ A) (ha : pushPt w a' = u ≫ a) (hb : pushPt w b' = u ≫ b) :
    (lift a' b').left ≫ sqMap w = u.left ≫ (lift a b).left := by
  rw [lift_sqMap, ha, hb, ← comp_lift]
  rfl

end Pts

end GlobalTheory.UPel.HT.Pull
end
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.UPel.HT.Pull

theorem tanScal_iff {S S' : Scheme.{0}} (f : S' ⟶ S) {O : Type} [Ring O] (A : Over S) [GrpObj A] (A' : Over S')
    [GrpObj A'] (φ : A'.left ⟶ A.left) (act : GlobalTheory.UPel.HT.OActN O A) (act' : GlobalTheory.UPel.HT.OActN O A')
    (h : IsGrpPullback A' A f φ) (hact : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) (R' : Type) [CommRing R']
    (x : Sp R' ⟶ S') (b : O) (c : R') (v : GlobalTheory.UPel.HT.epsPtR x ⟶ A') (v₀ : GlobalTheory.UPel.HT.epsPtR (x ≫ f) ⟶ A)
    (hv : v₀.left = v.left ≫ φ) :
    GlobalTheory.UPel.HT.IsTanScal act' x b c v ↔ GlobalTheory.UPel.HT.IsTanScal act (x ≫ f) b c v₀ := by
  have one : (1 : Over.mk (x ≫ f) ⟶ A).left = (1 : Over.mk x ⟶ A').left ≫ φ :=
    (congrArg (fun z => z.left) (map_one (pushHom h (Over.mk x)))).symm
  have sc : spMap (epsScaleR c) ≫ spMap (algebraMap R' (DualNumber R')) =
      spMap (algebraMap R' (DualNumber R')) := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have E : (v₀ ≫ act.act b).left = (v ≫ act'.act b).left ≫ φ := by
    rw [Over.comp_left, Over.comp_left, hv, Category.assoc, Category.assoc, hact]
  refine and_congr ?_ ?_
  · rw [one, hv]
    refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
      fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
    refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ A')).symm
    refine (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
  · rw [E, hv]
    refine ⟨fun E' => by rw [E']; exact Category.assoc _ _ _,
      fun E' => h.1.hom_ext (E'.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w (v ≫ act'.act b)).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) sc)

theorem kerGen {S S' : Scheme.{0}} {f : S' ⟶ S} (A : Over S) [GrpObj A] (A' : Over S') [GrpObj A']
    (φ : A'.left ⟶ A.left) (h : IsGrpPullback A' A f φ) (P : LB (G2 A).left) (T : Over S') (x : T ⟶ A')
    (ht : ∃ t : ((P.pull (sqMap h.1.w)).pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) :
    ∃ t : (P.pull (lift (snd A (Over.mk (T.hom ≫ f)) ≫ pushPt h.1.w x) (fst A (Over.mk (T.hom ≫ f)))).left).Gen,
      t.IsGen := by
  obtain ⟨t, ht⟩ := ht
  let T₀ : Over S := Over.mk (T.hom ≫ f)
  let Z' : Over S' := Over.mk ((snd A T₀).left ≫ T.hom)
  have eq : (fst A T₀).left ≫ A.hom = Z'.hom ≫ f :=
    (Over.w (fst A T₀)).trans ((Over.w (snd A T₀)).symm.trans (Category.assoc _ _ _).symm)
  let a' : Z' ⟶ A' := Over.homMk (h.1.lift (fst A T₀).left Z'.hom eq) (h.1.lift_snd _ _ _)
  let t' : Z' ⟶ T := Over.homMk (snd A T₀).left rfl
  let u : Over.mk (Z'.hom ≫ f) ⟶ A ⊗ T₀ := Over.homMk (𝟙 _) (by
    show 𝟙 _ ≫ (A ⊗ T₀).hom = ((snd A T₀).left ≫ T.hom) ≫ f
    rw [Category.id_comp, Category.assoc]
    exact (Over.w (snd A T₀)).symm)
  have hc : (lift (t' ≫ x) a').left ≫ sqMap h.1.w = u.left ≫ (lift (snd A T₀ ≫ pushPt h.1.w x) (fst A T₀)).left :=
    sqMap_of h.1.w u _ _ _ _ (Over.OverMorphism.ext (by
      show ((snd A T₀).left ≫ x.left) ≫ φ = 𝟙 _ ≫ (snd A T₀).left ≫ x.left ≫ φ
      rw [Category.id_comp, Category.assoc]))
      (Over.OverMorphism.ext (by
        show h.1.lift (fst A T₀).left Z'.hom eq ≫ φ = 𝟙 _ ≫ (fst A T₀).left
        rw [Category.id_comp, h.1.lift_fst]))
  have hψ : (lift a' t').left ≫ (lift (snd A' T ≫ x) (fst A' T)).left = (lift (t' ≫ x) a').left := by
    rw [← Over.comp_left, comp_lift, lift_snd_assoc, lift_fst]
  obtain ⟨t₁, ht₁⟩ := gen_chartPull (chartPullIn P (fun _ : PUnit => sqMap h.1.w) (fun _ => 1)
    (lift (snd A' T ≫ x) (fst A' T)).left) t ht
  refine gen_chartPull (chartPullSame P (fun _ : PUnit => (lift (snd A T₀ ≫ pushPt h.1.w x) (fst A T₀)).left)
    (fun _ => (lift (snd A' T ≫ x) (fst A' T)).left ≫ sqMap h.1.w) (fun _ => 1) (lift a' t').left fun _ => ?_) t₁ ht₁
  rw [← Category.assoc, hψ, hc]
  exact (Category.id_comp _).symm

end GlobalTheory.UPel.HT.Pull

namespace GlobalTheory.UPel.HT.Pull

open GlobalTheory.UPel.HT

theorem exists_objMap : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (f : S' ⟶ S) (o : GlobalTheory.UPel.HT.Obj b N s), ∃ o' : GlobalTheory.UPel.HT.Obj b N (f ≫ s), Nonempty (GlobalTheory.UPel.HT.ObjMap o' o f) := by
  intro p _ D R _ b N S S' s f o
  have h := isGrpPullback_pullback o.A f
  have hact := OActN.pullback_left f o.A o.act
  have w := h.1.w
  let A' := (Over.pullback f).obj o.A
  let φ := pullback.fst o.A.hom f
  let act' := OActN.pullback f o.A o.act
  let φ₂ := sqMap w
  let P' := o.P.pull φ₂
  let u : Over.mk (A'.hom ≫ f) ⟶ o.A := Over.homMk φ w
  let U : Over.mk ((G2 A').hom ≫ f) ⟶ G2 o.A := lift (pushPt w (fst A' A')) (pushPt w (snd A' A'))
  have pa : ∀ {T : Over S'} (x : T ⟶ A') c, pushPt w (x ≫ act'.act c) = pushPt w x ≫ o.act.act c := fun x c =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  have p1 : ∀ (T : Over S'), pushPt w (1 : T ⟶ A') = 1 := fun T => map_one (pushHom h T)
  have hP' : P'.IsLB := pull_isLB o.isLB φ₂

  have hΔ : (lift (𝟙 A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left :=
    sqMap_of w u _ _ _ _ (Over.OverMorphism.ext (by simp [u, φ, pushPt_left])) (Over.OverMorphism.ext (by simp [u, φ, pushPt_left]))
  have hL : LBIso (P'.pull (lift (𝟙 A') (𝟙 A')).left) ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull φ) :=
    LBIso.chartPull (chartPullOut o.P (fun _ => φ₂) (fun _ => 1) _ (fun _ => _ ≫ φ₂) fun _ => rfl)
      (chartPullOut o.P (fun _ => _) (fun _ => 1) φ (fun _ => _ ≫ φ₂) fun _ => hΔ)
      (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB o.isLB _))
  obtain ⟨hab, hamp, -⟩ := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally S S' o.A A' f φ
    _ _ (pull_isLB o.isLB _) (pull_isLB hP' _) o.ab h hL

  have r₁ : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (1 : o.A ⟶ o.A) (𝟙 o.A)).left :=
    sqMap_of w u _ _ _ _ ((p1 A').trans (MonObj.comp_one u).symm) (Over.OverMorphism.ext (by simp [u, φ, pushPt_left]))
  have r₂ : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ₂ = φ ≫ (lift (𝟙 o.A) (1 : o.A ⟶ o.A)).left :=
    sqMap_of w u _ _ _ _ (Over.OverMorphism.ext (by simp [u, φ, pushPt_left])) ((p1 A').trans (MonObj.comp_one u).symm)
  have sw : (lift (snd A' A') (fst A' A')).left ≫ φ₂ = φ₂ ≫ (lift (snd o.A o.A) (fst o.A o.A)).left :=
    sqMap_of w U _ _ _ _ (lift_snd _ _).symm (lift_fst _ _).symm
  have ro : ∀ c : D.O, (lift (fst A' A' ≫ act'.act c) (snd A' A')).left ≫ φ₂ =
      φ₂ ≫ (lift (fst o.A o.A ≫ o.act.act c) (snd o.A o.A)).left := fun c =>
    sqMap_of w U _ _ _ _ (by rw [pa, ← Category.assoc, lift_fst]) (lift_snd _ _).symm
  have ro' : ∀ c : D.O, (lift (fst A' A') (snd A' A' ≫ act'.act c)).left ≫ φ₂ =
      φ₂ ≫ (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act c)).left := fun c =>
    sqMap_of w U _ _ _ _ (lift_fst _ _).symm (by rw [pa, ← Category.assoc, lift_snd])
  have pul : ∀ {Y : Scheme.{0}} (g' : Y ⟶ (G2 A').left) {Y₀ : Scheme.{0}} (k : Y ⟶ Y₀) (g₀ : Y₀ ⟶ (G2 o.A).left), g' ≫ φ₂ = k ≫ g₀ → ChartPull (P'.pull g') (o.P.pull g₀) k :=
    fun g' _ k g₀ e => chartPullLinComb o.P φ₂ (fun _ => g') (fun _ => g₀) (fun _ => 1) k fun _ => e
  refine ⟨{ A := A'
            ab := hab
            act := act'
            P := P'
            isLB := hP'
            rig₁ := ?_
            rig₂ := ?_
            symm := ?_
            ample := hamp o.ample
            kerP := ?_
            rosati := ?_
            lie := ?_
            lieRank := ?_
            eta := fun y => GlobalTheory.ObjPull.secPull h (o.eta y)
            eta_add := fun x y => by rw [o.eta_add, map_mul]
            eta_lin := ?_
            eta_ker := fun x => by rw [o.eta_ker, map_one]
            geom := ?_ },
    ⟨{ φ := φ
       φ₂ := φ₂
       cart := h
       sq := isSquare_sqMap w
       act := hact
       pol := GlobalTheory.PolBaseChange.lbIso_refl hP'
       eta := fun y => GlobalTheory.ObjPull.secPull_left h _ }⟩⟩
  · obtain ⟨t, ht⟩ := o.rig₁
    exact gen_chartPull (pul _ φ _ r₁) t ht
  · obtain ⟨t, ht⟩ := o.rig₂
    exact gen_chartPull (pul _ φ _ r₂) t ht
  · exact LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o.P φ₂ φ₂ rfl) (pul _ φ₂ _ sw) o.symm
  · obtain ⟨e, he, hk⟩ := o.kerP
    refine ⟨e, he, fun T x hx => ?_⟩
    have h0 := hk _ (pushPt w x) (kerGen o.A A' φ h o.P T x hx)
    apply (GlobalTheory.ObjPull.pushEquiv h T).injective
    rw [map_pow, map_one]
    exact h0
  · intro c
    exact LBIso.chartPull (pul _ φ₂ _ (ro c)) (pul _ φ₂ _ (ro' _)) (o.rosati c)
  · intro R' _ β x hx v hv
    obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv h (epsPtR x) (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ f)
      (Category.assoc _ _ _).symm
    have key := fun (c : D.O) (r : R') (v : epsPtR x ⟶ A') =>
      tanScal_iff f o.A A' φ o.act act' h hact R' x c r v (e v) (he v)
    obtain ⟨w₀, hw₀, hv₀⟩ := o.lie R' β (x ≫ f) (by rw [Category.assoc]; exact hx) (e v) ((key _ _ v).1 hv)
    refine ⟨fun i => e.symm (w₀ i), fun i c => (key _ _ _).2 (by rw [MulEquiv.apply_symm_apply]; exact hw₀ i c), ?_⟩
    apply e.injective
    rw [hv₀, map_list_prod, List.map_ofFn]
    simp [Function.comp_def]
  · intro k _ _ x β hx i
    exact (GlobalTheory.LiePull.lieMult_pull _ S S' o.A A' f φ (o.act.toF D) (act'.toF D) h (fun c => hact _) k x _ _).2
      (o.lieRank k (x ≫ f) β (by rw [Category.assoc]; exact hx) i)
  · intro c y
    rw [o.eta_lin]
    apply (GlobalTheory.ObjPull.pushEquiv h _).injective
    apply Over.OverMorphism.ext
    show (GlobalTheory.ObjPull.secPull h (o.eta y ≫ o.act.act c)).left ≫ φ =
      (GlobalTheory.ObjPull.secPull h (o.eta y) ≫ act'.act c).left ≫ φ
    rw [GlobalTheory.ObjPull.secPull_left, Over.comp_left, Over.comp_left, Category.assoc, hact,
      reassoc_of% (GlobalTheory.ObjPull.secPull_left h (o.eta y))]
  · intro k _ _ x β hx
    obtain ⟨I, hI⟩ := o.geom k (x ≫ f) β (by rw [Category.assoc]; exact hx)
    refine ⟨tateMoveO (GlobalTheory.ObjPull.pushEquiv h (Over.mk x)) (fun c g => ?_) (fun n g g' z hz => ?_) I, fun y => ?_⟩
    · apply Over.OverMorphism.ext
      show (g.left ≫ _) ≫ φ = (g.left ≫ φ) ≫ _
      rw [Category.assoc, hact, Category.assoc]
    · exact (GlobalTheory.weilIs_grpPullback_of_comm S S' o.A A' f φ _ _ (pull_isLB o.isLB _) (pull_isLB hP' _) h hL
        (Over.mk x) n g g' _ _ _ rfl rfl).2 hz
    · rw [tateMoveO_ev]
      exact (MulEquiv.eq_symm_apply _).2 ((GlobalTheory.ObjPull.pushEquiv_secPull h _ _).trans (hI y))

end GlobalTheory.UPel.HT.Pull
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harrisTaylorObject_pullback_along : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (f : S' ⟶ S) (o : GlobalTheory.UPel.HT.Obj b N s), ∃ o' : GlobalTheory.UPel.HT.Obj b N (f ≫ s), Nonempty (GlobalTheory.UPel.HT.ObjMap o' o f) := by
  atlas_forward_decl GlobalTheory.UPel.HT.Pull.exists_objMap
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftFilEq

open GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

set_option maxHeartbeats 1000000 in

theorem liftFil_le (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (A₁ A₂ : Over (Sp (DualNumber k)))
    [GrpObj A₁] [GrpObj A₂] (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₀.left ⟶ A₂.left)
    (h₁ : IsGrpPullback A₀ A₁ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i₁)
    (h₂ : IsGrpPullback A₀ A₂ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i₂)
    (hA₁ : IsAbelianScheme A₁) (g : HdR A₀ → HdR A₀)
    (H₁ : ∀ x ∈ Fil A₀, IsFilLift h₁ x (g x)) (H₂ : ∀ x ∈ Fil A₀, IsFilLift h₂ x (g x)) :
    liftFil (epsDP k) h₁ ≤ liftFil (epsDP k) h₂ := by
  have P : AbelianDeRham := GlobalTheory.T.abelianScheme_firstDeRham_structure
  obtain ⟨g₁, hg₁⟩ := GlobalTheory.AbelianDim.exists_relDim (DualNumber k) A₁ hA₁
  have hA₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA₁ h₁
  have gA₀ := (smoothOfRelativeDimension_isStableUnderBaseChange g₁).of_isPullback h₁.1 hg₁
  obtain ⟨C, _, φ, j, hφ, hic, e1⟩ := exists_const A₀
  have hBC := constMor_isBC P hA₀ gA₀ hφ hic e1
  have HC : Canonical (epsDP k) (TrivSqZeroExt.fstHom k k k).toRingHom :=
    canonical_of_abelianDeRham P (isDPNilpotent_squareZero _) (fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩) rfl
  have step : ∀ x ∈ liftFil (epsDP k) h₁, ∃ y ∈ liftFil (epsDP k) h₁ ⊓ liftFil (epsDP k) h₂,
      ∃ z : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀, x = y + (DualNumber.eps : DualNumber k) • z := by
    intro x hx
    have ha := crysLo_mem_Fil P hA₁ hg₁ h₁ hx
    obtain ⟨d₁, hd₁, e₁⟩ := H₁ _ ha
    obtain ⟨d₂, hd₂, e₂⟩ := H₂ _ ha
    have e : d₁ = d₂ := crys_ext P hA₀ gA₀ fun c ↦ (e₁ c).trans (e₂ c).symm
    obtain ⟨z, hz⟩ := hBC.exists (crysHi x - g (crysLo x))
    have hd₁₂ : d₁ ∈ liftFil (epsDP k) h₂ := by rw [e]; exact hd₂
    refine ⟨d₁, ⟨hd₁, hd₁₂⟩, z, crys_ext P hA₀ gA₀ fun c ↦ ?_⟩
    rw [LinearMap.add_apply, LinearMap.smul_apply, e₁, hz c, crys_constMor x c]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hEq : liftFil (epsDP k) h₁ = liftFil (epsDP k) h₁ ⊓ liftFil (epsDP k) h₂ := by
    refine eq_of_le_of_le_add_eps ?_ inf_le_left step
    obtain ⟨N, hN⟩ := (HC g₁ A₀ A₁ i₁ h₁ hA₁ hg₁).2.1
    have c := HC.crysToDR_bijective h₁ hA₁ hg₁
    exact ⟨_, (Submodule.orderIsoMapComap (LinearEquiv.ofBijective _ c)).symm.isCompl hN⟩
  exact fun x hx ↦ (hEq.le hx).2

theorem liftFil_eq : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (A₁ A₂ : Over (Sp (DualNumber k))) [GrpObj A₁] [GrpObj A₂] (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₀.left ⟶ A₂.left) (h₁ : IsGrpPullback A₀ A₁ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i₁) (h₂ : IsGrpPullback A₀ A₂ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i₂), IsAbelianScheme A₁ → IsAbelianScheme A₂ → ∀ g : HdR A₀ → HdR A₀, (∀ x ∈ Fil A₀, IsFilLift h₁ x (g x)) → (∀ x ∈ Fil A₀, IsFilLift h₂ x (g x)) → liftFil (epsDP k) h₁ = liftFil (epsDP k) h₂ := by
  intro k _ A₀ _ A₁ A₂ _ _ i₁ i₂ h₁ h₂ hA₁ hA₂ g H₁ H₂
  exact le_antisymm (liftFil_le k A₀ A₁ A₂ i₁ i₂ h₁ h₂ hA₁ g H₁ H₂)
    (liftFil_le k A₀ A₂ A₁ i₂ i₁ h₂ h₁ hA₂ g H₂ H₁)

end GlobalTheory.LiftFilEq
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftedHodgeFiltration_eq_of_same_lifts : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (A₁ A₂ : Over (Sp (DualNumber k))) [GrpObj A₁] [GrpObj A₂] (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₀.left ⟶ A₂.left) (h₁ : IsGrpPullback A₀ A₁ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i₁) (h₂ : IsGrpPullback A₀ A₂ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i₂), IsAbelianScheme A₁ → IsAbelianScheme A₂ → ∀ g : HdR A₀ → HdR A₀, (∀ x ∈ Fil A₀, IsFilLift h₁ x (g x)) → (∀ x ∈ Fil A₀, IsFilLift h₂ x (g x)) → liftFil (epsDP k) h₁ = liftFil (epsDP k) h₂ := by
  first | (exact @GlobalTheory.LiftFilEq.liftFil_eq) | (exact GlobalTheory.LiftFilEq.liftFil_eq) | (intros; apply GlobalTheory.LiftFilEq.liftFil_eq  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UPel.HT.PolIsoLift

theorem pol_iso : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (s₁ s₂ : Sp (DualNumber k) ⟶ Sp R) (o₁ : GlobalTheory.UPel.HT.Obj b N s₁) (o₂ : GlobalTheory.UPel.HT.Obj b N s₂) (m₁ : GlobalTheory.UPel.HT.ObjMap o₀ o₁ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (m₂ : GlobalTheory.UPel.HT.ObjMap o₀ o₂ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (e : o₁.A ≅ o₂.A), IsMonHom e.hom → m₁.φ ≫ e.hom.left = m₂.φ → ∀ φ₂ : (G2 o₁.A).left ⟶ (G2 o₂.A).left, IsSquare e.hom.left φ₂ → LBIso o₁.P (o₂.P.pull φ₂) := by
  intro p _ D R _ b N k _ t o₀ s₁ s₂ o₁ o₂ m₁ m₂ e he hφ φ₂ hsq
  haveI := he
  have hκ : IsNilDP (epsDP k) := isDPNilpotent_squareZero _
  have hπ : Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom := fun x ↦ ⟨TrivSqZeroExt.inl x, rfl⟩
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim (DualNumber k) o₁.A o₁.ab
  have hred : m₁.φ₂ ≫ φ₂ = m₂.φ₂ := by
    apply GlobalTheory.AbDual.left_ext (P := o₂.A) (Q := o₂.A)
    · rw [Category.assoc, hsq.1, ← Category.assoc, m₁.sq.1, Category.assoc, hφ, m₂.sq.1]
    · rw [Category.assoc, hsq.2, ← Category.assoc, m₁.sq.2, Category.assoc, hφ, m₂.sq.2]
  have hP' : (o₂.P.pull φ₂).IsLB := pull_isLB o₂.isLB φ₂
  have axis : ∀ (u v : o₁.A ⟶ o₁.A) (u' v' : o₂.A ⟶ o₂.A),
      (lift u v).left ≫ φ₂ = e.hom.left ≫ (lift u' v').left → Triv (ev o₂.P u' v') →
        Triv (ev (o₂.P.pull φ₂) u v) := by
    intro u v u' v' hc h
    rw [triv_ev_iff hP', evc, cls_pull o₂.isLB φ₂ hP', ← GlobalTheory.CechPic.pull_comp, hc, GlobalTheory.CechPic.pull_comp]
    rw [triv_ev_iff o₂.isLB, evc] at h
    rw [h, map_zero]
  have t₁ : Triv (ev (o₂.P.pull φ₂) (1 : o₁.A ⟶ o₁.A) (𝟙 o₁.A)) := by
    refine axis _ _ (1 : o₂.A ⟶ o₂.A) (𝟙 o₂.A) ?_ o₂.rig₁
    apply GlobalTheory.AbDual.left_ext (P := o₂.A) (Q := o₂.A)
    · rw [Category.assoc, hsq.1, lift_left_fst_assoc, Category.assoc, lift_left_fst, ← Over.comp_left,
        ← Over.comp_left, MonObj.one_comp, MonObj.comp_one]
    · rw [Category.assoc, hsq.2, lift_left_snd_assoc, Category.assoc, lift_left_snd]
      simp
  have t₂ : Triv (ev (o₂.P.pull φ₂) (𝟙 o₁.A) (1 : o₁.A ⟶ o₁.A)) := by
    refine axis _ _ (𝟙 o₂.A) (1 : o₂.A ⟶ o₂.A) ?_ o₂.rig₂
    apply GlobalTheory.AbDual.left_ext (P := o₂.A) (Q := o₂.A)
    · rw [Category.assoc, hsq.1, lift_left_fst_assoc, Category.assoc, lift_left_fst]
      simp
    · rw [Category.assoc, hsq.2, lift_left_snd_assoc, Category.assoc, lift_left_snd, ← Over.comp_left,
        ← Over.comp_left, MonObj.one_comp, MonObj.comp_one]
  have e' : LBIso ((o₂.P.pull φ₂).pull m₁.φ₂) o₀.P := by
    refine (cls_eq_iff (pull_isLB hP' _) o₀.isLB).1 ?_
    rw [cls_pull hP', cls_pull o₂.isLB φ₂ hP', ← GlobalTheory.CechPic.pull_comp, hred,
      ← cls_pull o₂.isLB m₂.φ₂ (pull_isLB o₂.isLB _)]
    exact (cls_eq_iff _ _).2 (LBIso.symm m₂.pol)
  have hL : (o₁.P.pull (lift (𝟙 o₁.A) (𝟙 o₁.A)).left).IsLB := pull_isLB o₁.isLB _
  exact GlobalTheory.BirigidLift.lift_unique (κ := epsDP k)
    (grothendieckDeformation_of_lifting GlobalTheory.T.abelianScheme_firstDeRham_structure GlobalTheory.T.print_abelianLifting) GlobalTheory.T.dualAbelianScheme_exists_biduality hκ hπ rfl
    o₁.ab hg o₁.ab hg m₁.cart m₁.cart m₁.sq.1 m₁.sq.2 hL o₁.ample hL o₁.ample o₀.isLB o₁.isLB o₁.rig₁ o₁.rig₂
    (LBIso.symm m₁.pol) hP' t₁ t₂ e'

end GlobalTheory.UPel.HT.PolIsoLift
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_polarisation_bundles_correspond_deformations : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (s₁ s₂ : Sp (DualNumber k) ⟶ Sp R) (o₁ : GlobalTheory.UPel.HT.Obj b N s₁) (o₂ : GlobalTheory.UPel.HT.Obj b N s₂) (m₁ : GlobalTheory.UPel.HT.ObjMap o₀ o₁ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (m₂ : GlobalTheory.UPel.HT.ObjMap o₀ o₂ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (e : o₁.A ≅ o₂.A), IsMonHom e.hom → m₁.φ ≫ e.hom.left = m₂.φ → ∀ φ₂ : (G2 o₁.A).left ⟶ (G2 o₂.A).left, IsSquare e.hom.left φ₂ → LBIso o₁.P (o₂.P.pull φ₂) := by
  first | (exact @GlobalTheory.UPel.HT.PolIsoLift.pol_iso) | (exact GlobalTheory.UPel.HT.PolIsoLift.pol_iso) | (intros; apply GlobalTheory.UPel.HT.PolIsoLift.pol_iso  <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section
namespace GlobalTheory.HTFirstOrderIso

theorem isGrpPullback_of_iso {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom] :
    IsGrpPullback A B (𝟙 S) e.hom.left := by
  have : IsIso e.hom.left := by change IsIso ((Over.forget S).map e.hom); infer_instance
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let j : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have e₁ : x₀ = j ≫ x ≫ e.hom := Over.OverMorphism.ext (by simp [hx, j])
  have e₂ : y₀ = j ≫ y ≫ e.hom := Over.OverMorphism.ext (by simp [hy, j])
  rw [e₁, e₂, ← MonObj.comp_mul, ← MonObj.mul_comp]
  simp [j]

theorem gd : GlobalTheory.Published.GrothendieckDeformation :=
  GlobalTheory.Published.grothendieckDeformation_of_lifting GlobalTheory.T.abelianScheme_firstDeRham_structure GlobalTheory.T.print_abelianLifting

theorem liftHom_eps (k : Type) [Field k] :
    GlobalTheory.Published.GrothendieckMessing.LiftHom (epsDP k) (TrivSqZeroExt.fstHom k k k).toRingHom :=
  (gd.at_dualNumber k).2.2

theorem henselian_of_artinian (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] :
    HenselianLocalRing C := by
  obtain ⟨n, hn⟩ : IsNilpotent (IsLocalRing.maximalIdeal C) := by
    have := IsArtinianRing.isNilpotent_jacobson_bot (R := C)
    rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at this
  have hz : ∀ k, n ≤ k → (IsLocalRing.maximalIdeal C) ^ k = ⊥ := fun k hk => by
    rw [← Nat.add_sub_cancel' hk, pow_add, hn, zero_mul]; rfl
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal C) C := by
    refine { haus' := fun x hx => ?_, prec' := fun f hf => ⟨f n, fun k => ?_⟩ }
    · have := SModEq.zero.1 (hx n)
      rw [hz n le_rfl, Submodule.bot_smul] at this
      simpa using this
    · rcases le_total k n with h | h
      · exact hf h
      · have e := SModEq.sub_mem.1 (hf h)
        rw [hz n le_rfl, Submodule.bot_smul, Submodule.mem_bot, sub_eq_zero] at e
        rw [e]
  refine { is_henselian := ?_ }
  intro f hf a₀ h₁ h₂
  exact HenselianRing.is_henselian f hf a₀ h₁ (h₂.map _)

instance isArtinianRing_dualNumber (k : Type) [Field k] : IsArtinianRing (DualNumber k) := by
  haveI : Module.Finite k (DualNumber k) := inferInstanceAs (Module.Finite k (k × k))
  exact IsArtinianRing.of_finite k (DualNumber k)

end GlobalTheory.HTFirstOrderIso

namespace GlobalTheory.HTFirstOrderIso

theorem eta_pow {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R] {b : GlobalTheory.UPel.HT.Base D R}
    {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : GlobalTheory.UPel.HT.Obj b N s) (a : D.La) (n : ℕ) :
    o.eta (n • a) = o.eta a ^ n := by
  have h0 : o.eta 0 = 1 := by
    have := o.eta_add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  induction n with
  | zero => rw [zero_smul, h0, pow_zero]
  | succ n ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]

theorem comp_pow {S : Scheme.{0}} {T T' G : Over S} [GrpObj G] (ρ : T' ⟶ T) (x : T ⟶ G) (n : ℕ) :
    ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => simp [MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem pow_comp {S : Scheme.{0}} {G H Z : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ]
    (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => simp [MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem objMap_of_filLift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∀ (s₁ s₂ : Sp (DualNumber k) ⟶ Sp R) (o₁ : GlobalTheory.UPel.HT.Obj b N s₁) (o₂ : GlobalTheory.UPel.HT.Obj b N s₂) (m₁ : GlobalTheory.UPel.HT.ObjMap o₀ o₁ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (m₂ : GlobalTheory.UPel.HT.ObjMap o₀ o₂ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (g : HdR o₀.A → HdR o₀.A), (∀ x ∈ Fil o₀.A, IsFilLift m₁.cart x (g x)) → (∀ x ∈ Fil o₀.A, IsFilLift m₂.cart x (g x)) → Nonempty (GlobalTheory.UPel.HT.ObjMap o₁ o₂ (𝟙 _)) := by
  intro p _ D R _ b N hN3 hNp k _ _ t o₀ s₁ s₂ o₁ o₂ m₁ m₂ g hg₁ hg₂
  have hF := GlobalTheory.T.liftedHodgeFiltration_eq_of_same_lifts k o₀.A o₁.A o₂.A m₁.φ m₂.φ m₁.cart m₂.cart o₁.ab o₂.ab g hg₁ hg₂
  obtain ⟨d₁, hd₁⟩ := GlobalTheory.AbelianDim.exists_relDim (DualNumber k) o₁.A o₁.ab
  obtain ⟨d₂, hd₂⟩ := GlobalTheory.AbelianDim.exists_relDim (DualNumber k) o₂.A o₂.ab
  obtain ⟨e, he, em⟩ := ((liftHom_eps k).exists_iso_iff m₁.cart o₁.ab hd₁ m₂.cart o₂.ab hd₂).2 hF
  have hact : ∀ c : D.O, (o₁.act.act c).left ≫ e.hom.left = e.hom.left ≫ (o₂.act.act c).left := by
    intro c
    haveI := o₁.act.hom c
    haveI := o₂.act.hom c
    haveI := o₀.act.hom c
    have := (liftHom_eps k).unique m₁.cart o₁.ab hd₁ m₂.cart o₂.ab hd₂ (o₀.act.act c)
      (f := o₁.act.act c ≫ e.hom) (f' := e.hom ≫ o₂.act.act c)
      (by rw [Over.comp_left, ← Category.assoc, ← m₁.act c, Category.assoc, em])
      (by rw [Over.comp_left, ← Category.assoc, em, m₂.act c])
    rw [← Over.comp_left, this, Over.comp_left]

  have hNu : IsUnit (N : DualNumber k) := by simpa using (b.unit N hNp).map (Spec.preimage s₂).hom
  have heta : ∀ y : D.La, (o₁.eta y).left ≫ e.hom.left = 𝟙 _ ≫ (o₂.eta y).left := by
    intro a
    haveI := henselian_of_artinian (DualNumber k)
    let π : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom
    have hπ : Function.Surjective π := fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
    have h2 : RingHom.ker π ^ 2 = 0 := GlobalTheory.FODef.sqZero k k
    have hk : RingHom.ker π ≤ IsLocalRing.maximalIdeal (DualNumber k) := by
      intro x hx
      by_contra hc
      have hu : IsUnit x := by
        rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hc
      have : x * x ∈ RingHom.ker π ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hx hx
      rw [h2] at this
      exact (hu.mul hu).ne_zero (by simpa using this)
    obtain ⟨ρ, hρ⟩ : ∃ ρ : k →+* IsLocalRing.ResidueField (DualNumber k),
        ρ.comp π = IsLocalRing.residue (DualNumber k) :=
      ⟨π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ)
        ⟨IsLocalRing.residue (DualNumber k), fun x hx => by
          rw [RingHom.mem_ker, IsLocalRing.residue_eq_zero_iff]; exact hk hx⟩,
        RingHom.liftOfRightInverse_comp _ _ _ _⟩
    have hs : IsSemiAbelian o₂.A := GlobalTheory.isSemiAbelian_of_isAbelianScheme _ o₂.ab
    let y₁ : Over.mk (𝟙 (Sp (DualNumber k))) ⟶ o₂.A := o₁.eta a ≫ e.hom
    let y₂ : Over.mk (𝟙 (Sp (DualNumber k))) ⟶ o₂.A := o₂.eta a
    have t₁ : y₁ ^ N = 1 := by
      simp only [y₁]
      rw [← pow_comp, ← eta_pow, o₁.eta_ker, MonObj.one_comp]
    have t₂ : y₂ ^ N = 1 := by
      simp only [y₂]
      rw [← eta_pow, o₂.eta_ker]
    have r : spMap π ≫ y₁.left = spMap π ≫ y₂.left := by
      simp only [y₁, y₂, Over.comp_left]
      rw [← Category.assoc, ← m₁.eta a, Category.assoc, em, m₂.eta a]
    have r' : spMap (IsLocalRing.residue (DualNumber k)) ≫ y₁.left =
        spMap (IsLocalRing.residue (DualNumber k)) ≫ y₂.left := by
      rw [← hρ, Cris.spMap_comp, Category.assoc, r, ← Category.assoc]
    let x₀ : Over.mk (spMap (IsLocalRing.residue (DualNumber k)) ≫ 𝟙 (Sp (DualNumber k))) ⟶ o₂.A :=
      toUnit _ ≫ y₂
    have hx₀ : x₀ ^ N = 1 := by
      simp only [x₀]
      rw [← comp_pow, t₂, MonObj.comp_one]
    have hl : x₀.left = spMap (IsLocalRing.residue (DualNumber k)) ≫ y₂.left := by
      simp only [x₀, Over.comp_left]
      congr 1
    obtain ⟨x, -, hu⟩ := GlobalTheory.existsUnique_torsion_lift_of_henselian (DualNumber k) (Sp (DualNumber k)) o₂.A hs
      (𝟙 _) N hNu x₀ hx₀
    have := (hu y₁ ⟨t₁, r'.trans hl.symm⟩).trans (hu y₂ ⟨t₂, hl.symm⟩).symm
    rw [Category.id_comp, ← Over.comp_left]
    exact congrArg Over.Hom.left this
  let φ₂ : (G2 o₁.A).left ⟶ (G2 o₂.A).left :=
    (lift (fst o₁.A o₁.A ≫ e.hom) (snd o₁.A o₁.A ≫ e.hom)).left
  have hsq : IsSquare e.hom.left φ₂ := by
    constructor
    · simp only [φ₂]; rw [← Over.comp_left, lift_fst, Over.comp_left]
    · simp only [φ₂]; rw [← Over.comp_left, lift_snd, Over.comp_left]
  have hpol := GlobalTheory.T.harrisTaylor_polarisation_bundles_correspond_deformations p D R b N k t o₀ s₁ s₂ o₁ o₂ m₁ m₂ e he em φ₂ hsq
  exact ⟨{ φ := e.hom.left
           φ₂ := φ₂
           cart := isGrpPullback_of_iso e
           sq := hsq
           act := hact
           pol := hpol
           eta := heta }⟩

end GlobalTheory.HTFirstOrderIso
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_firstOrder_iso_of_same_hodge_filtration : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∀ (s₁ s₂ : Sp (DualNumber k) ⟶ Sp R) (o₁ : GlobalTheory.UPel.HT.Obj b N s₁) (o₂ : GlobalTheory.UPel.HT.Obj b N s₂) (m₁ : GlobalTheory.UPel.HT.ObjMap o₀ o₁ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (m₂ : GlobalTheory.UPel.HT.ObjMap o₀ o₂ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (g : HdR o₀.A → HdR o₀.A), (∀ x ∈ Fil o₀.A, IsFilLift m₁.cart x (g x)) → (∀ x ∈ Fil o₀.A, IsFilLift m₂.cart x (g x)) → Nonempty (GlobalTheory.UPel.HT.ObjMap o₁ o₂ (𝟙 _)) := by
  atlas_forward_decl GlobalTheory.HTFirstOrderIso.objMap_of_filLift
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HTUniv.Nat

open GlobalTheory.CechPic GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

theorem pull_cls_diag {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : Obj b N s} {o' : Obj b N s'}
    {f : S' ⟶ S} (mp : ObjMap o' o f) :
    pull mp.φ (cls (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (pull_isLB o.isLB _)) =
      cls (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) (pull_isLB o'.isLB _) := by
  have hs := mp.sq
  have e : (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ mp.φ₂ = mp.φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left := by
    have a₁ := congrArg (fun q => q.left) (lift_fst (𝟙 o.A) (𝟙 o.A))
    have a₂ := congrArg (fun q => q.left) (lift_snd (𝟙 o.A) (𝟙 o.A))
    have b₁ := congrArg (fun q => q.left) (lift_fst (𝟙 o'.A) (𝟙 o'.A))
    have b₂ := congrArg (fun q => q.left) (lift_snd (𝟙 o'.A) (𝟙 o'.A))
    simp only [Over.comp_left, Over.id_left] at a₁ a₂ b₁ b₂
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst o.A o.A).left = (_ ≫ _) ≫ (fst o.A o.A).left
      rw [Category.assoc, hs.1, ← Category.assoc, b₁, Category.assoc, a₁]; simp
    · show (_ ≫ _) ≫ (snd o.A o.A).left = (_ ≫ _) ≫ (snd o.A o.A).left
      rw [Category.assoc, hs.2, ← Category.assoc, b₂, Category.assoc, a₂]; simp
  have h1 : pull mp.φ₂ (cls o.P o.isLB) = cls o'.P o'.isLB :=
    ((cls_eq_iff o'.isLB (pull_isLB o.isLB mp.φ₂)).2 mp.pol).symm
  rw [cls_pull o.isLB, cls_pull o'.isLB, ← pull_comp, ← e, pull_comp, h1]

theorem phi_eq (hN : 3 ≤ N) (hNp : N.Coprime p) {k : Type} [Field k] [IsAlgClosed k] {t : Sp k ⟶ Sp R}
    (o₀ : Obj b N t) {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) {z : Sp k ⟶ S}
    {φ φ' : o₀.A.left ⟶ o.A.left} (h : IsGrpPullback o₀.A o.A z φ) (h' : IsGrpPullback o₀.A o.A z φ')
    (hc : pull φ (cls (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (pull_isLB o.isLB _)) =
      pull φ' (cls (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (pull_isLB o.isLB _)))
    (he : ∀ y, (o₀.eta y).left ≫ φ = z ≫ (o.eta y).left) (he' : ∀ y, (o₀.eta y).left ≫ φ' = z ≫ (o.eta y).left) :
    φ = φ' := by
  have hN0 : 0 < N := by omega
  have hNK : (N : k) ≠ 0 := by
    have hu := (b.unit N hNp).map (Spec.preimage t).hom
    rw [map_natCast] at hu
    exact hu.ne_zero
  refine GlobalTheory.SiegRigid.eq_of_field (pull_isLB o.isLB _) o.ample o₀.ab h h' hc hN hNK fun Ω _ _ x y hy => ?_
  obtain ⟨I, hI⟩ := o₀.geom Ω x (Spec.preimage (x ≫ t)).hom (Spec.map_preimage _).symm
  obtain ⟨a, ha⟩ := (I.onto N hN0 hNp y).1 hy
  rw [← ha, ← hI a]
  simp only [Over.comp_left, Category.assoc, he, he']

theorem corr_of_isBC {R₀ R₁ R₂ : Type} [CommRing R₀] [CommRing R₁] [CommRing R₂] [Algebra R₀ R₁]
    {I₀ : Ideal R₀} {I₁ : Ideal R₁} {I₂ : Ideal R₂} {κ₀ : DividedPowers I₀} {κ₁ : DividedPowers I₁}
    {κ₂ : DividedPowers I₂} {S₀ S₁ S₂ : Scheme.{0}} {t₀ : S₀ ⟶ Sp R₀} {t₁ : S₁ ⟶ Sp R₁} {t₂ : S₂ ⟶ Sp R₂}
    {A₀ : Over S₀} {A₁ : Over S₁} {A₂ : Over S₂} [GrpObj A₀] [GrpObj A₁] [GrpObj A₂] {b₁ : S₁ ⟶ S₀}
    {b₂ : S₂ ⟶ S₁} {φ₁ : A₁.left ⟶ A₀.left} {φ₂ : A₂.left ⟶ A₁.left} {σ : R₁ →+* R₂}
    {m : GrpMor κ₀ t₀ A₀ κ₁ t₁ A₁ (algebraMap R₀ R₁) b₁ φ₁} (hm : m.IsBC)
    (M : GrpMor κ₁ t₁ A₁ κ₂ t₂ A₂ σ b₂ φ₂) {h : Crys κ₁ t₁ A₁} {h' : Crys κ₂ t₂ A₂}
    (e : ∀ q, h' (M.pull (m.pull q)) = σ (h (m.pull q))) : M.Corr h h' := by
  intro q
  obtain ⟨w, rfl⟩ := hm.2 q
  induction w with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul r q =>
    rw [liftSemi_tmul, LinearMap.map_smulₛₗ, map_smul, map_smul, e, smul_eq_mul, smul_eq_mul, map_mul]

set_option maxHeartbeats 1000000 in

theorem main : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∀ (d : ℕ) (s : Sp (TrivSqZeroExt k (Fin d → k)) ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)) (c : (Fin d → k) →ₗ[k] k) (s' : Sp (DualNumber k) ⟶ Sp R) (o' : GlobalTheory.UPel.HT.Obj b N s') (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (n : GlobalTheory.UPel.HT.ObjMap o' o (spMap (TrivSqZeroExt.map c).toRingHom)) (x : HdR o₀.A) (y : primDR o₀.A →ₗ[k] (Fin d → k)), GlobalTheory.FODef.IsFilLiftV m.cart x y → IsFilLift m'.cart x (c ∘ₗ y) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀ d s o m c s' o' m' n x y hxy
  obtain ⟨dd, hdd, edd⟩ := hxy
  let σ : TrivSqZeroExt k (Fin d → k) →+* DualNumber k := (TrivSqZeroExt.map c).toRingHom
  have hz : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap σ =
      spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom := by
    rw [← Cris.spMap_comp]
    congr 1
    ext a <;> simp [σ]

  have hrig : m'.φ ≫ n.φ = m.φ := by
    refine (phi_eq hN hNp o₀ o ((m'.cart.comp n.cart).congr hz rfl) m.cart ?_ ?_ m.eta).symm.symm
    · rw [pull_comp, pull_cls_diag n, pull_cls_diag m', pull_cls_diag m]
    · intro y
      rw [← Category.assoc, m'.eta y, Category.assoc, n.eta y, ← Category.assoc, hz]

  have hdp : (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))).IsDPMorphism (epsDP k) σ := by
    unfold epsDP
    refine isDPMorphism_sqDP _ _ σ fun a ha => ?_
    have ha' : a.fst = 0 := ha
    change (σ a).fst = 0
    simp [σ, ha']
  have M : GrpMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)
      o₀.A (epsDP k) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A σ (𝟙 _) (Over.Hom.left (𝟙 o₀.A)) :=
    GrpMor.of_hom hdp hz.symm (𝟙 o₀.A)
  have hBC : (constMor o₀.A).IsBC := GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k k o₀.A o₀.ab _ (constMor o₀.A)
  have hBCV : (GlobalTheory.FODef.constMorV k (Fin d → k) o₀.A).IsBC :=
    GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k (Fin d → k) o₀.A o₀.ab _ _
  let d' : Crys (epsDP k) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A :=
    hBC.bcMap x + (TrivSqZeroExt.inr (1 : k) : DualNumber k) • hBC.bcMap (c ∘ₗ y)
  have ed' : ∀ q, d' ((constMor o₀.A).pull q) = TrivSqZeroExt.inl (x q) + TrivSqZeroExt.inr (c (y q)) := by
    intro q
    have e1 := (hBC.corr_iff (h := x)).2 rfl q
    have e2 := (hBC.corr_iff (h := c ∘ₗ y)).2 rfl q
    simp only [d', LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, e1, e2]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hMc : M.Corr dd d' := corr_of_isBC hBCV M fun q => by
    rw [GrpMor.pull_pull (GlobalTheory.FODef.constMorV k (Fin d → k) o₀.A) M (constMor o₀.A) (fun _ => by
      ext <;> simp [σ, TrivSqZeroExt.algebraMap_eq_inl]) (by simp) q, ed', edd q]
    ext <;> simp [σ]
  have Nm : GrpMor (dp0 _) (𝟙 _) o.A (dp0 _) (𝟙 _) o'.A σ (spMap σ) n.φ :=
    GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) n.cart
  have hNc := crysToDR_corr (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) m.cart m'.cart M Nm
    (by rw [hrig]; simp) hMc
  refine ⟨d', ?_, fun q => ?_⟩
  · letI : Algebra (TrivSqZeroExt k (Fin d → k)) (DualNumber k) := σ.toAlgebra
    obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim (TrivSqZeroExt k (Fin d → k)) o.A o.ab
    have hF := (GlobalTheory.abelianDeRham.2.2.1 _ o.A g o.ab hg (DualNumber k) o'.A n.φ n.cart).2
    exact mem_Fil_of_corr (hφ := n.cart) hF hNc hdd
  · rw [ed']
    rfl

end GlobalTheory.HTUniv.Nat
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_hodgeFiltration_naturality : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∀ (d : ℕ) (s : Sp (TrivSqZeroExt k (Fin d → k)) ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)) (c : (Fin d → k) →ₗ[k] k) (s' : Sp (DualNumber k) ⟶ Sp R) (o' : GlobalTheory.UPel.HT.Obj b N s') (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (n : GlobalTheory.UPel.HT.ObjMap o' o (spMap (TrivSqZeroExt.map c).toRingHom)) (x : HdR o₀.A) (y : primDR o₀.A →ₗ[k] (Fin d → k)), GlobalTheory.FODef.IsFilLiftV m.cart x y → IsFilLift m'.cart x (c ∘ₗ y) := by
  first | (exact @GlobalTheory.HTUniv.Nat.main) | (exact GlobalTheory.HTUniv.Nat.main) | (intros; apply GlobalTheory.HTUniv.Nat.main  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem GlobalTheory.HTUniv.main : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∃ o : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) ≫ t), Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o (spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom)) ∧ ∀ o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t), Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) → ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, Nonempty (GlobalTheory.UPel.HT.ObjMap o' o (spMap (TrivSqZeroExt.map c).toRingHom)) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀
  obtain ⟨f, hdir, huniq⟩ := GlobalTheory.T.harrisTaylor_firstOrder_deformations_basis_count p D R b N hN hNp k t o₀
  obtain ⟨o, m, hm⟩ := GlobalTheory.T.harrisTaylor_exists_glued_firstOrder_deformation p D R b N hN hNp k t o₀ _ f hdir
  refine ⟨o, ⟨m⟩, fun o' ho' => ?_⟩
  obtain ⟨m'⟩ := ho'
  have key : ∀ (s' : Sp (DualNumber k) ⟶ Sp R) (o'' : GlobalTheory.UPel.HT.Obj b N s')
      (m'' : GlobalTheory.UPel.HT.ObjMap o₀ o'' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom))
      (c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k)
      (n : GlobalTheory.UPel.HT.ObjMap o'' o (spMap (TrivSqZeroExt.map c).toRingHom)),
      ∀ x ∈ Fil o₀.A, IsFilLift m''.cart x (∑ j, c (Pi.single j 1) • f j x) := by
    intro s' o'' m'' c n x hx
    have h := GlobalTheory.T.harrisTaylor_hodgeFiltration_naturality p D R b N hN hNp k t o₀ _ _ o m c s' o'' m'' n x _ (hm x hx)
    rw [GlobalTheory.HTUniv.comp_pi] at h
    exact h
  obtain ⟨c₀, hc₀, hc₀u⟩ := huniq o' m'
  let c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k := ∑ j, c₀ j • LinearMap.proj j
  have hcj : ∀ j, c (Pi.single j 1) = c₀ j := fun j => GlobalTheory.HTUniv.sum_proj_single c₀ j
  obtain ⟨oc, ⟨nc⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback_along p D R b N _ _ _ (spMap (TrivSqZeroExt.map c).toRingHom) o
  have hcomp : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (TrivSqZeroExt.map c).toRingHom =
      spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom := by
    rw [← GlobalTheory.Cris.spMap_comp]
    congr 1
    ext x
    simp
  obtain ⟨mc⟩ := (GlobalTheory.T.harris_taylor_object_maps_compose_cancel p D R b N _ _ _ _ _ _ o₀ oc o
    (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (spMap (TrivSqZeroExt.map c).toRingHom)).2
    (by rw [hcomp]; exact ⟨m⟩) ⟨nc⟩
  have hfc := key _ oc mc c nc
  simp only [hcj] at hfc
  obtain ⟨iso⟩ := GlobalTheory.T.harrisTaylor_firstOrder_iso_of_same_hodge_filtration p D R b N hN hNp k t o₀ _ _ o' oc m' mc (fun x => ∑ j, c₀ j • f j x) hc₀ hfc
  refine ⟨c, ?_, ?_⟩
  · have h := (GlobalTheory.T.harris_taylor_object_maps_compose_cancel p D R b N _ _ _ _ _ _ o' oc o (𝟙 _)
      (spMap (TrivSqZeroExt.map c).toRingHom)).1 ⟨iso⟩ ⟨nc⟩
    rwa [Category.id_comp] at h
  · rintro c' ⟨n'⟩
    have h1 := key _ o' m' c' n'
    have h2 := hc₀u (fun j => c' (Pi.single j 1)) h1
    refine LinearMap.ext fun v => ?_
    rw [GlobalTheory.HTUniv.coord c' v, GlobalTheory.HTUniv.coord c v]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcj]
    exact congrArg _ (congrFun h2 j)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universal_firstOrder_deformation_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∃ o : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) ≫ t), Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o (spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom)) ∧ ∀ o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t), Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) → ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, Nonempty (GlobalTheory.UPel.HT.ObjMap o' o (spMap (TrivSqZeroExt.map c).toRingHom)) := by
  first | (exact @GlobalTheory.HTUniv.main) | (exact GlobalTheory.HTUniv.main) | (intros; apply GlobalTheory.HTUniv.main  <;> assumption)
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.RepTangent

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := by
  simp only [spMap]; exact Spec.map_id _

theorem exists_univ_tangent : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ F : RepFam b N, IsQProjOver F.s → Smooth F.s → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ F.X), ∃ u : Sp (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k)) ⟶ F.X, spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom ≫ u = x ∧ u ≫ F.s = spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) ≫ x ≫ F.s ∧ ∀ v : Sp (DualNumber k) ⟶ F.X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ F.s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ F.s → ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u := by
  intro p _ D R _ _ b N hN hNp F _ _ k _ _ x
  obtain ⟨o₀, ⟨m₀⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback_along p D R b N F.X (Sp k) F.s x F.univ
  obtain ⟨o, ⟨mo⟩, huniv⟩ := GlobalTheory.T.exists_universal_firstOrder_deformation_harrisTaylor p D R b N hN hNp k (x ≫ F.s) o₀
  obtain ⟨u, ⟨hu1, ⟨mu⟩⟩, -⟩ := F.rep _ _ o
  have hfst : spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom ≫
      spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) = 𝟙 _ := by
    rw [spMap_comp_spMap]
    convert spMap_id' k
    ext a; simp
  refine ⟨u, ?_, hu1, ?_⟩
  · obtain ⟨f, -, hf⟩ := F.rep _ _ o₀
    have e1 := hf x ⟨rfl, ⟨m₀⟩⟩
    have e2 := hf (spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom ≫ u)
      ⟨by rw [Category.assoc, hu1, ← Category.assoc, hfst, Category.id_comp], ⟨MapComp.comp mo mu⟩⟩
    exact e2.trans e1.symm
  · intro v hv1 hv2
    obtain ⟨o', ⟨m'⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback_along p D R b N F.X (Sp (DualNumber k)) F.s v F.univ
    have main : ∀ (s₁ : Sp (DualNumber k) ⟶ Sp R) (o' : Obj b N s₁), s₁ = v ≫ F.s → ObjMap o' F.univ v →
        ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u := by
      intro s₁ o' hs m'
      rw [hv2] at hs
      subst hs
      have h0 : Nonempty (ObjMap o₀ F.univ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v)) := by
        rw [hv1]; exact ⟨m₀⟩
      have m'' := (GlobalTheory.UPel.HT.objMap_comp_cancel p D R b N _ _ _ _ _ _ o₀ o' F.univ _ v).2 h0 ⟨m'⟩
      obtain ⟨c, ⟨mc⟩, hc⟩ := huniv o' m''
      have hbase : ∀ c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k,
          (spMap (TrivSqZeroExt.map c).toRingHom ≫ u) ≫ F.s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ F.s := by
        intro c
        rw [Category.assoc, hu1, ← Category.assoc, spMap_comp_spMap]
        congr 2
        exact (TrivSqZeroExt.map c).comp_algebraMap
      refine ⟨c, ?_, ?_⟩
      · obtain ⟨f, -, hf⟩ := F.rep _ _ o'
        exact (hf v ⟨hv2, ⟨m'⟩⟩).trans (hf _ ⟨hbase c, ⟨MapComp.comp mc mu⟩⟩).symm
      · intro c' hc'
        apply hc
        rw [hc'] at m'
        exact (GlobalTheory.UPel.HT.objMap_comp_cancel p D R b N _ _ _ _ _ _ o' o F.univ _ u).2 ⟨m'⟩ ⟨mu⟩
    exact main _ o' rfl m'

end GlobalTheory.UPel.HT.RepTangent
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universal_tangent_harrisTaylor_representingFamily : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ F : RepFam b N, IsQProjOver F.s → Smooth F.s → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ F.X), ∃ u : Sp (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k)) ⟶ F.X, spMap (TrivSqZeroExt.fstHom k k (Fin (D.a * (D.n - 1)) → k)).toRingHom ≫ u = x ∧ u ≫ F.s = spMap (algebraMap k (TrivSqZeroExt k (Fin (D.a * (D.n - 1)) → k))) ≫ x ≫ F.s ∧ ∀ v : Sp (DualNumber k) ⟶ F.X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ F.s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ F.s → ∃! c : (Fin (D.a * (D.n - 1)) → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u := by
  first | (exact @GlobalTheory.UPel.HT.RepTangent.exists_univ_tangent) | (exact GlobalTheory.UPel.HT.RepTangent.exists_univ_tangent) | (intros; apply GlobalTheory.UPel.HT.RepTangent.exists_univ_tangent  <;> assumption)
end
