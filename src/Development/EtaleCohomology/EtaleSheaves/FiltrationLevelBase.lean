import Development.EtaleCohomology.EtaleSheaves.KernelLocalization.RangeOfBd
import Development.EtaleCohomology.EtaleSheaves.TruncKerPf
import Development.EtaleCohomology.EtaleSheaves.LocalDescent.DescLocOf
import Development.EtaleCohomology.EtaleSheaves.RelDescPf
import Development.EtaleCohomology.EtaleSheaves.CechLevelsGeneration.CechLevelIso
import Development.EtaleCohomology.EtaleSheaves.CechLevelIsomorphism.BaseChangeLimit
import Development.EtaleCohomology.EtaleSheaves.DescIntPf
import Development.EtaleCohomology.EtaleSheaves.CechFiltPf
import Development.EtaleCohomology.EtaleSheaves.LeafConeExactPf

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.FiltrationLevelInjectivity

def gN {D Y' E Y'' : CommRingCat.{0}} (φ' : D ⟶ Y') (e : D ⟶ E) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'')
    (h : φ' ≫ u = e ≫ φ'') : cech (Spec.map u) ⟶ cech (Spec.map e) :=
  Arrow.mapCechNerve (f := Arrow.mk (yoneda.map (Spec.map u))) (g := Arrow.mk (yoneda.map (Spec.map e)))
    ⟨yoneda.map (Spec.map φ''), yoneda.map (Spec.map φ'), by
      simp only [Arrow.mk_hom, Functor.id_map, Functor.id_obj, Arrow.mk_left, Arrow.mk_right,
        ← Functor.map_comp, ← Spec.map_comp, h]⟩

def iN {Y X : Scheme.{0}} (f : Y ⟶ X) : sch.obj Y ⟶ cech f where
  app _ := WidePullback.lift (yoneda.map f) (fun _ => 𝟙 _) (fun _ => Category.id_comp _)
  naturality := by
    intro x y θ
    apply WidePullback.hom_ext
    · intro j
      erw [Category.assoc, WidePullback.lift_π, Category.assoc, WidePullback.lift_π, WidePullback.lift_π]
      exact Category.id_comp _
    · erw [Category.assoc, WidePullback.lift_base, Category.assoc, WidePullback.lift_base, WidePullback.lift_base]
      exact Category.id_comp _

theorem iN_aug {Y X : Scheme.{0}} (f : Y ⟶ X) : iN f ≫ cechAug f = sch.map f := by
  refine NatTrans.ext (funext fun x => ?_)
  erw [NatTrans.comp_app, WidePullback.lift_base]
  rfl

theorem iN_app_zero_iso {Y X : Scheme.{0}} (f : Y ⟶ X) : IsIso ((iN f).app (op ⦋0⦌)) := by
  refine ⟨⟨WidePullback.π (fun _ : Fin 1 => yoneda.map f) 0, ?_, ?_⟩⟩
  · erw [WidePullback.lift_π]
  · apply WidePullback.hom_ext
    · intro j
      have hj : j = 0 := Fin.fin_one_eq_zero j
      subst hj
      erw [Category.assoc, WidePullback.lift_π, Category.id_comp]
      exact Category.comp_id _
    · erw [Category.assoc, WidePullback.lift_base, Category.id_comp]
      exact WidePullback.π_arrow _ _

theorem gN_aug {D Y' E Y'' : CommRingCat.{0}} (φ' : D ⟶ Y') (e : D ⟶ E) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'')
    (h : φ' ≫ u = e ≫ φ'') :
    gN φ' e u φ'' h ≫ cechAug (Spec.map e) = cechAug (Spec.map u) ≫ sch.map (Spec.map φ') := by
  refine NatTrans.ext (funext fun x => ?_)
  erw [NatTrans.comp_app, WidePullback.lift_base]
  rfl

theorem gN_iN {D Y' E Y'' : CommRingCat.{0}} (φ' : D ⟶ Y') (e : D ⟶ E) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'')
    (h : φ' ≫ u = e ≫ φ'') :
    sch.map (Spec.map φ'') ≫ iN (Spec.map e) = iN (Spec.map u) ≫ gN φ' e u φ'' h := by
  have hw : yoneda.map (Spec.map φ'') ≫ yoneda.map (Spec.map e) = yoneda.map (Spec.map u) ≫ yoneda.map (Spec.map φ') := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Spec.map_comp, ← Spec.map_comp, h]
  refine NatTrans.ext (funext fun x => ?_)
  apply WidePullback.hom_ext
  · intro j
    erw [Category.assoc, WidePullback.lift_π, Category.assoc, WidePullback.lift_π, ← Category.assoc,
      WidePullback.lift_π, Category.id_comp]
    exact Category.comp_id _
  · erw [Category.assoc, WidePullback.lift_base, Category.assoc, WidePullback.lift_base, ← Category.assoc,
      WidePullback.lift_base]
    exact hw

def Filt : Prop := Hyp → ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {Z' Z : PSh} {X' X : Spc} (g : X' ⟶ X)
  (h : Z' ⟶ Z) (a : disc.obj Z ⟶ X) (b : disc.obj Z' ⟶ X') (comm : disc.map h ≫ a = b ≫ g),
  IsIso (a.app (op ⦋0⦌)) → IsIso (b.app (op ⦋0⦌)) →
  (∀ p : ℕ, 1 ≤ p → ∀ m : ℤ, m < n → Function.Injective (pull R (disc.map (g.app (op ⦋p⦌))) F m) ∧
    Function.Surjective (pull R (disc.map (g.app (op ⦋p⦌))) F (m - 1))) →
  Function.Injective (rpull R g (disc.map h) b a comm F n)

def LvlRel : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e → SpS e → P E (d ≫ e) → ∀ hpo : IsPushout φ' e u φ'',
  ∀ p : ℕ, 1 ≤ p → ∀ m : ℤ, m < n →
    Function.Injective (pull (ZMod q) (disc.map ((gN φ' e u φ'' hpo.w).app (op ⦋p⦌))) (tw q i) m) ∧
    Function.Surjective (pull (ZMod q) (disc.map ((gN φ' e u φ'' hpo.w).app (op ⦋p⦌))) (tw q i) (m - 1))

theorem LevelInj_of (hF : Filt) (hL : LvlRel) : LateralTheory.E.RelDescPf.LevelInj := by
  intro hH q _ i n A Y φ hq P hP hE hB D d hD Y' w φ' hpo E e Y'' u φ'' he hs hPE hpo'
  refine ⟨gN φ' e u φ'' hpo'.w, gN_aug _ _ _ _ _, iN (Spec.map e), iN (Spec.map u), gN_iN _ _ _ _ _,
    iN_aug _, iN_aug _, ?_⟩
  exact hF hH (ZMod q) (tw q i) n (gN φ' e u φ'' hpo'.w) (yoneda.map (Spec.map φ'')) (iN (Spec.map e))
    (iN (Spec.map u)) (gN_iN _ _ _ _ _) (iN_app_zero_iso _) (iN_app_zero_iso _)
    (hL hH q i n φ hq P hP hE hB D d hD Y' w φ' hpo E e Y'' u φ'' he hs hPE hpo')

end LateralTheory.E.FiltrationLevelInjectivity
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.TruncCokPf LateralTheory.E.LevelsPf.Tp Opposite LateralTheory.E.CechLevelIsoPf.Gen

namespace LateralTheory.E.CechLevelIsoPf

abbrev y {A B : CommRingCat.{0}} (f : A ⟶ B) := yoneda.map (Spec.map f)

lemma y_comp {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) : y (f ≫ g) = y g ≫ y f := by
  simp [y]

lemma ypb {A B C P : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {inl : B ⟶ P} {inr : C ⟶ P}
    (h : IsPushout f g inl inr) : IsPullback (y inl) (y inr) (y f) (y g) :=
  (isPullback_SpecMap_of_isPushout f g inl inr h).map yoneda

lemma mk_congr {C : Type*} [Category C] {ι : Type*} {S X W : C} {f : X ⟶ S} {b b' : W ⟶ S}
    {π π' : ι → (W ⟶ X)} (hb : b = b') (hπ : π = π') (h : ∀ i, π i ≫ f = b) (h' : ∀ i, π' i ≫ f = b') :
    WidePullbackCone.mk (f := fun _ : ι => f) b π h = WidePullbackCone.mk (f := fun _ : ι => f) b' π' h' := by
  subst hb; subst hπ; rfl

def lim0 {C : Type*} [Category C] {S X : C} (f : X ⟶ S) :
    IsLimit (WidePullbackCone.mk (f := fun _ : Fin 1 => f) f (fun _ => 𝟙 X) (fun _ => Category.id_comp f)) := by
  refine WidePullbackCone.IsLimit.mk _ (fun t => t.π 0) ?_ ?_ ?_
  · intro t
    have : t.π 0 ≫ f = t.base := WidePullbackCone.condition t 0
    exact this
  · intro t i
    have : t.π 0 ≫ 𝟙 X = t.π i := by rw [Category.comp_id, Subsingleton.elim i 0]
    exact this
  · intro t m _ hπ
    have key : ∀ m : t.pt ⟶ X, m ≫ 𝟙 X = t.π 0 → m = t.π 0 := fun m h => by rwa [Category.comp_id] at h
    exact key m (hπ 0)

def ι {D E : CommRingCat.{0}} (e : D ⟶ E) : (p : ℕ) → Fin (p+1) → (E ⟶ (tp e p).1)
  | 0 => fun _ => 𝟙 E
  | p+1 => Fin.lastCases (pushout.inr (tp e p).2 e) (fun i => ι e p i ≫ pushout.inl (tp e p).2 e)

lemma ι_zero {D E : CommRingCat.{0}} (e : D ⟶ E) (i : Fin 1) : ι e 0 i = 𝟙 E := rfl

lemma ι_last {D E : CommRingCat.{0}} (e : D ⟶ E) (p : ℕ) :
    ι e (p+1) (Fin.last _) = pushout.inr (tp e p).2 e := by
  first | rfl | (dsimp only [ι]; exact Fin.lastCases_last) | (dsimp only [ι]; rw [Fin.lastCases_last])

lemma ι_cast {D E : CommRingCat.{0}} (e : D ⟶ E) (p : ℕ) (i : Fin (p+1)) :
    ι e (p+1) (Fin.castSucc i) = ι e p i ≫ pushout.inl (tp e p).2 e := by
  first | rfl | (dsimp only [ι]; exact Fin.lastCases_castSucc i) | (dsimp only [ι]; rw [Fin.lastCases_castSucc])

lemma ι_w {D E : CommRingCat.{0}} (e : D ⟶ E) : ∀ (p : ℕ) (i : Fin (p+1)), e ≫ ι e p i = (tp e p).2
  | 0, i => Category.comp_id e
  | p+1, i => by
    induction i using Fin.lastCases with
    | last => rw [ι_last]; exact pushout.condition.symm
    | cast i =>
      rw [ι_cast]
      show e ≫ ι e p i ≫ pushout.inl _ _ = (tp e p).2 ≫ pushout.inl _ _
      rw [← Category.assoc, ι_w e p i]

lemma hπE {D E : CommRingCat.{0}} (e : D ⟶ E) (p : ℕ) (i : Fin (p+1)) : y (ι e p i) ≫ y e = y (tp e p).2 := by
  rw [← y_comp, ι_w]

def limE {D E : CommRingCat.{0}} (e : D ⟶ E) : ∀ p : ℕ,
    IsLimit (WidePullbackCone.mk (f := fun _ : Fin (p+1) => y e) (y (tp e p).2) (fun i => y (ι e p i)) (hπE e p))
  | 0 => cast (congrArg IsLimit (mk_congr rfl (funext fun i => (show y (𝟙 E) = 𝟙 _ by simp [y]).symm) _ _)) (lim0 (y e))
  | p+1 => by
    have hpb := ypb (IsPushout.of_hasPushout (tp e p).2 e)
    have h' : ∀ i, (Fin.lastCases (y (pushout.inr (tp e p).2 e)) (fun i => y (pushout.inl (tp e p).2 e) ≫ y (ι e p i)) i :
        _ ⟶ _) ≫ y e = y (pushout.inl (tp e p).2 e) ≫ y (tp e p).2 := by
      intro i
      induction i using Fin.lastCases with
      | last => rw [Fin.lastCases_last]; exact hpb.w.symm
      | cast i => rw [Fin.lastCases_castSucc, Category.assoc, hπE]
    have := stepLimit (fun i => y (ι e p i)) (hπE e p) (limE e p) _ _ hpb h'
    refine cast (congrArg IsLimit (mk_congr ?_ ?_ _ _)) this
    · exact (y_comp _ _).symm
    · funext i
      induction i using Fin.lastCases with
      | last => rw [Fin.lastCases_last, ι_last]; rfl
      | cast i => rw [Fin.lastCases_castSucc, ι_cast]; exact (y_comp _ _).symm

section Y
variable {D E Y' Y'' : CommRingCat.{0}} {e : D ⟶ E} {φ' : D ⟶ Y'} {u : Y' ⟶ Y''} {φ'' : E ⟶ Y''}

def κ (hpo : IsPushout φ' e u φ'') (p : ℕ) (i : Fin (p+1)) : Y'' ⟶ pushout φ' (tp e p).2 :=
  hpo.desc (pushout.inl _ _) (ι e p i ≫ pushout.inr _ _) (by rw [← Category.assoc, ι_w]; exact pushout.condition)

lemma hπY (hpo : IsPushout φ' e u φ'') (p : ℕ) (i : Fin (p+1)) :
    y (κ hpo p i) ≫ y u = y (pushout.inl φ' (tp e p).2) := by
  rw [← y_comp, κ, hpo.inl_desc]

lemma hgi (hpo : IsPushout φ' e u φ'') (p : ℕ) (i : Fin (p+1)) :
    y (κ hpo p i) ≫ y φ'' = y (pushout.inr φ' (tp e p).2) ≫ y (ι e p i) := by
  rw [← y_comp, κ, hpo.inr_desc, y_comp]

def limY (hpo : IsPushout φ' e u φ'') (p : ℕ) :
    IsLimit (WidePullbackCone.mk (f := fun _ : Fin (p+1) => y u) (y (pushout.inl φ' (tp e p).2))
      (fun i => y (κ hpo p i)) (hπY hpo p)) :=
  baseChangeLimit (fun i => y (ι e p i)) (hπE e p) (limE e p) (ypb hpo).flip
    (ypb (IsPushout.of_hasPushout φ' (tp e p).2)).flip (fun i => y (κ hpo p i)) (hπY hpo p) (hgi hpo p)

end Y

theorem CechLevelIso_of : LateralTheory.E.LevelsPf.Tp.CechLevelIso := by
  intro p D E Y' Y'' e φ' u φ'' hpo
  let R := (limE e p).conePointUniqueUpToIso (limit.isLimit _)
  let L := (limY hpo p).conePointUniqueUpToIso (limit.isLimit _)
  have hR : ∀ j, R.hom ≫ WidePullback.π (fun _ : Fin (p+1) => y e) j = y (ι e p j) := fun j =>
    (limE e p).conePointUniqueUpToIso_hom_comp (limit.isLimit _) (some j)
  have hRb : R.hom ≫ WidePullback.base (fun _ : Fin (p+1) => y e) = y (tp e p).2 :=
    (limE e p).conePointUniqueUpToIso_hom_comp (limit.isLimit _) none
  have hL : ∀ j, L.hom ≫ WidePullback.π (fun _ : Fin (p+1) => y u) j = y (κ hpo p j) := fun j =>
    (limY hpo p).conePointUniqueUpToIso_hom_comp (limit.isLimit _) (some j)
  have hLb : L.hom ≫ WidePullback.base (fun _ : Fin (p+1) => y u) = y (pushout.inl φ' (tp e p).2) :=
    (limY hpo p).conePointUniqueUpToIso_hom_comp (limit.isLimit _) none
  have hw : L.hom ≫ (Arrow.mapCechNerve (sq e φ' u φ'' hpo.w)).app (op (SimplexCategory.mk p)) =
      y (pushout.inr φ' (tp e p).2) ≫ R.hom := by
    apply WidePullback.hom_ext
    · intro j
      simp only [Arrow.mapCechNerve_app, Category.assoc, WidePullback.lift_π]
      have key : (L.hom ≫ WidePullback.π (fun _ : Fin (p+1) => y u) j) ≫ y φ'' =
          y (pushout.inr φ' (tp e p).2) ≫ R.hom ≫ WidePullback.π (fun _ : Fin (p+1) => y e) j := by
        exact (congrArg (· ≫ y φ'') (hL j)).trans ((hgi hpo p j).trans
          (congrArg (y (pushout.inr φ' (tp e p).2) ≫ ·) (hR j).symm))
      rw [← Category.assoc]
      exact key
    · simp only [Arrow.mapCechNerve_app, Category.assoc, WidePullback.lift_base]
      have key : (L.hom ≫ WidePullback.base (fun _ : Fin (p+1) => y u)) ≫ y φ' =
          y (pushout.inr φ' (tp e p).2) ≫ R.hom ≫ WidePullback.base (fun _ : Fin (p+1) => y e) := by
        exact (congrArg (· ≫ y φ') hLb).trans (((ypb (IsPushout.of_hasPushout φ' (tp e p).2)).w).trans
          (congrArg (y (pushout.inr φ' (tp e p).2) ≫ ·) hRb.symm))
      rw [← Category.assoc]
      exact key
  exact ⟨(Arrow.isoMk (f := Arrow.mk (y (pushout.inr φ' (tp e p).2)))
    (g := Arrow.mk ((Arrow.mapCechNerve (sq e φ' u φ'' hpo.w)).app (op (SimplexCategory.mk p)))) L R hw).symm⟩

end LateralTheory.E.CechLevelIsoPf
end
end

section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.LeafGhostCut
theorem LateralTheory.E.TruncationCokernelLevelRelations.TruncCok_of (hD : LateralTheory.E.TruncationKernel.RelDesc) : LateralTheory.E.DescLocPf.Fine.TruncCok := by
  intro hH q _ i n A Y φ hq P hpush het hlow D d hPD Y' w φ' hpo E e Y'' u φ'' he hs hE hpo' m hm y ⟨x, hx⟩
  have hinj := hD hH q i n φ hq P @hpush @het hlow D d hPD Y' w φ' hpo E e Y'' u φ'' he hs hE hpo'
  refine LateralTheory.E.KernelLocalization.range_of_bd _ _ _ m n (by omega) y ((injective_iff_map_eq_zero _).1 hinj _ ?_)
  refine (LateralTheory.E.KernelLocalization.rpull_bd ..).trans ?_
  rw [← hx]
  exact LateralTheory.E.KernelLocalization.bd_pull ..
theorem LateralTheory.E.TruncationCokernelLevelRelations.LvlRel_of : LateralTheory.E.FiltrationLevelInjectivity.LvlRel := by
  intro hH q _ i n A Y φ hq P hpush het hlow D d hPD Y' w φ' hpo E e Y'' u φ'' he hs hE hpo' p _ m hm
  have h := LateralTheory.E.LevelsPf.Tp.Levels_of' LateralTheory.E.CechLevelIsoPf.CechLevelIso_of hH q i n φ hq P @hpush @het hlow D d hPD Y' w φ' hpo E e Y'' u φ'' hpo' he hs hE p m hm
  exact ⟨h.2, h.1 (m - 1) (by omega)⟩
end

section
noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.FiltGenPf

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

lemma ofHom_comp_fromSingleMk {X Y : C} {I : CochainComplex C ℤ} (k : ℤ) (h : X ⟶ Y) {q m : ℤ}
    (g : Y ⟶ I.X q) (hq : k + m = q) :
    (Cochain.ofHom ((singleFunctor C k).map h)).comp
      (Cochain.fromSingleMk (p := k) g hq) (zero_add m) = Cochain.fromSingleMk (p := k) (h ≫ g) hq := by
  ext p q' hpq
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  by_cases hp : p = k
  · subst hp
    obtain rfl : q' = q := by lia
    rw [Cochain.fromSingleMk_v, Cochain.fromSingleMk_v]
    change ((HomologicalComplex.single C (ComplexShape.up ℤ) p).map h).f p ≫ _ = _
    simp [HomologicalComplex.single_map_f_self]
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _

lemma smul_fromSingleMk {X : C} {I : CochainComplex C ℤ} (k : ℤ) (ε : ℤˣ) {q m : ℤ}
    (g : X ⟶ I.X q) (hq : k + m = q) :
    ε • Cochain.fromSingleMk (p := k) g hq = Cochain.fromSingleMk (p := k) (ε • g) hq := by
  rcases Int.units_eq_one_or ε with h | h <;> subst h <;> simp

lemma desc_eta {K L I : CochainComplex C ℤ} (φ : K ⟶ L) {m n : ℤ} (hmn : m + 1 = n)
    (c : Cochain (mappingCone φ) I n) :
    c = mappingCone.descCochain φ ((mappingCone.inl φ).comp c (by lia))
      ((Cochain.ofHom (mappingCone.inr φ)).comp c (zero_add n)) hmn := by
  rw [mappingCone.ext_cochain_from_iff φ m n hmn]
  simp

lemma δ_desc_fromSingle {X Y : C} {I : CochainComplex C ℤ} (k : ℤ) (h : X ⟶ Y) {m m' qa qb qc : ℤ}
    (hm : m + 1 = m') (a : X ⟶ I.X qa) (b : Y ⟶ I.X qb) (ha : k + (m - 1) = qa) (hb : k + m = qb)
    (hc : k + m' = qc) :
    δ m m' (mappingCone.descCochain ((singleFunctor C k).map h) (Cochain.fromSingleMk a ha)
      (Cochain.fromSingleMk b hb) (by lia)) =
    mappingCone.descCochain ((singleFunctor C k).map h)
      (Cochain.fromSingleMk (a ≫ I.d qa qb + m'.negOnePow • (h ≫ b)) hb)
      (Cochain.fromSingleMk (b ≫ I.d qb qc) hc) (by lia) := by
  rw [mappingCone.δ_descCochain _ _ _ _ m' hm, Cochain.δ_fromSingleMk _ _ m qb hb,
    Cochain.δ_fromSingleMk _ _ m' qc hc, ofHom_comp_fromSingleMk, smul_fromSingleMk,
    ← Cochain.fromSingleMk_add]
  rfl

lemma level_of {K L I : CochainComplex C ℤ} (φ : K ⟶ L) (k n : ℤ)
    (hk : Subsingleton (CohomologyClass (mappingCone
      ((HomologicalComplex.single C (ComplexShape.up ℤ) k).map (φ.f k))) I n))
    (f : K.X k ⟶ I.X (k + (n - 1))) (g : L.X k ⟶ I.X (k + n))
    (hg : g ≫ I.d (k + n) (k + (n + 1)) = 0)
    (hf : f ≫ I.d (k + (n - 1)) (k + n) + (n + 1).negOnePow • (φ.f k ≫ g) = 0) :
    ∃ (a : K.X k ⟶ I.X (k + (n - 1 - 1))) (b : L.X k ⟶ I.X (k + (n - 1))),
      f = a ≫ I.d _ _ + n.negOnePow • (φ.f k ≫ b) ∧ g = b ≫ I.d _ _ := by
  have hk' : Subsingleton (CohomologyClass (mappingCone ((singleFunctor C k).map (φ.f k))) I n) := hk
  let w : Cochain (mappingCone ((singleFunctor C k).map (φ.f k))) I n := mappingCone.descCochain ((singleFunctor C k).map (φ.f k))
    (Cochain.fromSingleMk f (show k + (n - 1) = k + (n - 1) from rfl))
    (Cochain.fromSingleMk g (show k + n = k + n from rfl)) (by lia)
  have hw : δ n (n + 1) w = 0 := by
    simp only [w]
    rw [δ_desc_fromSingle k (φ.f k) rfl f g rfl rfl rfl, hf, hg]
    simp [mappingCone.descCochain]
  have h0 := Subsingleton.elim (CohomologyClass.mk (Cocycle.mk w (n + 1) rfl hw)) 0
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by lia)] at h0
  obtain ⟨c, hc⟩ := h0
  obtain ⟨a, ha⟩ := Cochain.fromSingleMk_surjective
    ((mappingCone.inl ((singleFunctor C k).map (φ.f k))).comp c (show -1 + (n - 1) = n - 1 - 1 by lia)) (k + (n - 1 - 1)) rfl
  obtain ⟨b, hb⟩ := Cochain.fromSingleMk_surjective
    ((Cochain.ofHom (mappingCone.inr ((singleFunctor C k).map (φ.f k)))).comp c (zero_add (n - 1))) (k + (n - 1)) rfl
  rw [desc_eta ((singleFunctor C k).map (φ.f k)) (show n - 1 - 1 + 1 = n - 1 by lia) c, ← ha, ← hb,
    δ_desc_fromSingle k (φ.f k) (show n - 1 + 1 = n by lia) a b (by lia) rfl rfl] at hc
  refine ⟨a, b, ?_, ?_⟩
  · have := congrArg (fun x => (mappingCone.inl ((singleFunctor C k).map (φ.f k))).comp x (show -1 + n = n - 1 by lia)) hc
    simp only [w, Cocycle.mk_coe, mappingCone.inl_descCochain] at this
    have := congrArg (Cochain.fromSingleEquiv (show k + (n - 1) = k + (n - 1) from rfl)) this
    simpa using this.symm
  · have := congrArg (fun x => (Cochain.ofHom (mappingCone.inr ((singleFunctor C k).map (φ.f k)))).comp x (zero_add n)) hc
    simp only [w, Cocycle.mk_coe, mappingCone.inr_descCochain] at this
    have := congrArg (Cochain.fromSingleEquiv (show k + n = k + n from rfl)) this
    simpa using this.symm

lemma δ_desc {K L I : CochainComplex C ℤ} (φ : K ⟶ L) {m n n' : ℤ} (h : m + 1 = n) (hn' : n + 1 = n')
    (α : Cochain K I m) (β : Cochain L I n) :
    δ n n' (mappingCone.descCochain φ α β h) = mappingCone.descCochain φ
      (δ m n α + n'.negOnePow • (Cochain.ofHom φ).comp β (zero_add n)) (δ n n' β) (by omega) :=
  mappingCone.δ_descCochain φ α β h n' hn'

def V {K L I : CochainComplex C ℤ} (φ : K ⟶ L) (k n : ℤ) (z : Cochain (mappingCone φ) I n) : Prop :=
  (∀ p q (hpq : p + (n - 1) = q), k < p →
    ((mappingCone.inl φ).comp z (show -1 + n = n - 1 by omega)).v p q hpq = 0) ∧
  (∀ p q (hpq : p + n = q), k < p →
    ((Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add n)).v p q hpq = 0)

lemma step {K L I : CochainComplex C ℤ} (φ : K ⟶ L) (k n : ℤ)
    (hk : Subsingleton (CohomologyClass (mappingCone
      ((HomologicalComplex.single C (ComplexShape.up ℤ) k).map (φ.f k))) I n))
    (z : Cochain (mappingCone φ) I n) (hz : δ n (n + 1) z = 0) (hV : V φ k n z) :
    ∃ c : Cochain (mappingCone φ) I (n - 1), V φ (k - 1) n (z - δ (n - 1) n c) := by
  obtain ⟨hV1, hV2⟩ := hV
  have hzd := desc_eta φ (show n - 1 + 1 = n by omega) z
  generalize hα : (mappingCone.inl φ).comp z (show -1 + n = n - 1 by omega) = α at hV1 hzd
  generalize hβ : (Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add n) = β at hV2 hzd
  have hV1' : ∀ p q (hpq : p + (n - 1) = q), k < p → α.v p q hpq = 0 := fun p q hpq h => by
    rw [← hα]; exact hV1 p q hpq h
  have hδ := hz
  rw [hzd, δ_desc φ (by omega) rfl] at hδ
  have e1 : δ (n - 1) n α + (n + 1).negOnePow • (Cochain.ofHom φ).comp β (zero_add n) = 0 := by
    have := congrArg (fun x => (mappingCone.inl φ).comp x (show -1 + (n + 1) = n by omega)) hδ
    simpa only [mappingCone.inl_descCochain, Cochain.comp_zero] using this
  have e2 : δ n (n + 1) β = 0 := by
    have := congrArg (fun x => (Cochain.ofHom (mappingCone.inr φ)).comp x (zero_add (n + 1))) hδ
    simpa only [mappingCone.inr_descCochain, Cochain.comp_zero] using this
  have hg : β.v k (k + n) rfl ≫ I.d (k + n) (k + (n + 1)) = 0 := by
    have := Cochain.congr_v e2 k (k + (n + 1)) rfl
    rw [δ_v n (n + 1) rfl β k (k + (n + 1)) rfl (k + n) (k + 1) (by omega) rfl, Cochain.zero_v,
      hV2 (k + 1) (k + (n + 1)) (by omega) (by omega), comp_zero, smul_zero, add_zero] at this
    exact this
  have hf : α.v k (k + (n - 1)) rfl ≫ I.d (k + (n - 1)) (k + n) +
      (n + 1).negOnePow • (φ.f k ≫ β.v k (k + n) rfl) = 0 := by
    have := Cochain.congr_v e1 k (k + n) rfl
    rw [Cochain.add_v, Cochain.units_smul_v,
      δ_v (n - 1) n (by omega) α k (k + n) rfl (k + (n - 1)) (k + 1) (by omega) rfl,
      Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v,
      hV1' (k + 1) (k + n) (by omega) (by omega), comp_zero, smul_zero, add_zero] at this
    exact this
  obtain ⟨a, b, ha, hb⟩ := level_of φ k n hk _ _ hg hf
  refine ⟨mappingCone.descCochain φ (Cochain.single a (n - 1 - 1)) (Cochain.single b (n - 1))
    (by omega), ?_, ?_⟩
  · intro p q hpq hp
    rw [Cochain.comp_sub, δ_desc φ (by omega) (by omega), mappingCone.inl_descCochain,
      Cochain.sub_v, Cochain.add_v, Cochain.units_smul_v,
      δ_v (n - 1 - 1) (n - 1) (by omega) _ p q hpq (p + (n - 1 - 1)) (p + 1) (by omega) rfl,
      Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      Cochain.single_v_eq_zero a _ (p + 1) q _ (by omega)]
    rcases eq_or_lt_of_le (show k ≤ p by omega) with hkp | hkp
    · subst hkp
      obtain rfl : q = k + (n - 1) := by omega
      have h1 : ((mappingCone.inl φ).comp z (show -1 + n = n - 1 by omega)).v k (k + (n - 1)) hpq =
        α.v k (k + (n - 1)) hpq := by rw [hα]
      rw [Cochain.single_v, Cochain.single_v, h1, ha]
      simp
    · rw [hV1 p q hpq hkp, Cochain.single_v_eq_zero a _ p _ _ (by omega),
        Cochain.single_v_eq_zero b _ p _ _ (by omega)]
      simp
  · intro p q hpq hp
    rw [Cochain.comp_sub, δ_desc φ (by omega) (by omega), mappingCone.inr_descCochain,
      Cochain.sub_v,
      δ_v (n - 1) n (by omega) _ p q hpq (p + (n - 1)) (p + 1) (by omega) rfl,
      Cochain.single_v_eq_zero b _ (p + 1) q _ (by omega)]
    rcases eq_or_lt_of_le (show k ≤ p by omega) with hkp | hkp
    · subst hkp
      obtain rfl : q = k + n := by omega
      have h2 : ((Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add n)).v k (k + n) hpq =
        β.v k (k + n) hpq := by rw [hβ]
      rw [Cochain.single_v, h2, hb]
      simp
    · rw [(show ((Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add n)).v p q hpq = 0 by rw [hβ]; exact hV2 p q hpq hkp), Cochain.single_v_eq_zero b _ p _ _ (by omega)]
      simp

theorem FiltGen_of : LateralTheory.E.CechFiltPf.FiltGen.{u, v} := by
  intro C _ _ K L I φ n hK hL hI hlev
  have claim : ∀ m : ℕ, ∀ z : Cochain (mappingCone φ) I n, δ n (n + 1) z = 0 →
      ∃ c : Cochain (mappingCone φ) I (n - 1), V φ (-(m : ℤ)) n (z - δ (n - 1) n c) := by
    intro m
    induction m with
    | zero =>
      intro z hz
      refine ⟨0, ?_, ?_⟩
      · intro p q hpq hp
        exact (hK p (by omega)).eq_of_src _ _
      · intro p q hpq hp
        exact (hL p (by omega)).eq_of_src _ _
    | succ m ih =>
      intro z hz
      obtain ⟨c, hc⟩ := ih z hz
      obtain ⟨c', hc'⟩ := step φ (-(m : ℤ)) n (hlev _ (by omega)) (z - δ (n - 1) n c)
        (by rw [δ_sub, δ_δ, sub_zero]; exact hz) hc
      refine ⟨c + c', ?_⟩
      have e : (-((m + 1 : ℕ) : ℤ)) = -(m : ℤ) - 1 := by push_cast; ring
      rw [e, δ_add, ← sub_sub]
      exact hc'
  constructor
  intro x y
  suffices h : ∀ x : CohomologyClass (mappingCone φ) I n, x = 0 by rw [h x, h y]
  intro x
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨c, hc1, hc2⟩ := claim (n.toNat + 1) z (Cocycle.δ_eq_zero z (n + 1))
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨c, ?_⟩
  have h0 : (z : Cochain (mappingCone φ) I n) - δ (n - 1) n c = 0 := by
    rw [mappingCone.ext_cochain_from_iff φ (n - 1) n (by omega)]
    constructor
    · ext p q hpq
      simp only [Cochain.comp_zero, Cochain.zero_v]
      rcases lt_or_ge (-((n.toNat + 1 : ℕ) : ℤ)) p with hp | hp
      · exact hc1 p q hpq hp
      · exact (hI q (by omega)).eq_of_tgt _ _
    · ext p q hpq
      simp only [Cochain.comp_zero, Cochain.zero_v]
      rcases lt_or_ge (-((n.toNat + 1 : ℕ) : ℤ)) p with hp | hp
      · exact hc2 p q hpq hp
      · exact (hI q (by omega)).eq_of_tgt _ _
  rw [sub_eq_zero] at h0
  exact h0.symm

end LateralTheory.E.FiltGenPf
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.DiscLvlPf

variable (R : Type) [CommRing R]

def e0 (E : Spc) : ((chains R).obj E).X 0 ≅ (free R).obj (E.obj (op (SimplexCategory.mk 0))) :=
  ((chainsN R).obj E).extendXIso ComplexShape.embeddingDownNat (i := 0) rfl

theorem etale_discrete_chains_degree_zero_iso_free_naturality {E E' : Spc} (g : E ⟶ E') :
    ((chains R).map g).f 0 ≫ (e0 R E').hom = (e0 R E).hom ≫ (free R).map (g.app (op (SimplexCategory.mk 0))) := by
  have : ((chains R).map g).f 0 = (e0 R E).hom ≫ ((chainsN R).map g).f 0 ≫ (e0 R E').inv :=
    HomologicalComplex.extendMap_f (φ := (chainsN R).map g) (e := ComplexShape.embeddingDownNat) (i := 0) (i' := 0) rfl
  rw [this]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem d_zero (P : PSh) : ((chains R).obj (disc.obj P)).d (-1) 0 = 0 := by
  change (HomologicalComplex.extend ((chainsN R).obj (disc.obj P)) ComplexShape.embeddingDownNat).d (-1) 0 = 0
  rw [HomologicalComplex.extend_d_eq (K := (chainsN R).obj (disc.obj P)) (e := ComplexShape.embeddingDownNat) (i' := -1) (j' := 0) (i := 1) (j := 0) rfl rfl]
  have : ((chainsN R).obj (disc.obj P)).d 1 0 = 0 := by
    change (AlgebraicTopology.AlternatingFaceMapComplex.obj (((SimplicialObject.whiskering _ _).obj (free R)).obj (disc.obj P))).d (0 + 1) 0 = 0
    have h01 : (((SimplicialObject.whiskering _ _).obj (free R)).obj (disc.obj P)).δ (0 : Fin 2) =
      (((SimplicialObject.whiskering _ _).obj (free R)).obj (disc.obj P)).δ (1 : Fin 2) := rfl
    rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq, Fin.sum_univ_two, h01]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul, add_neg_cancel]
  rw [this, zero_comp, comp_zero]

def e0d (P : PSh) : ((chains R).obj (disc.obj P)).X 0 ≅ (free R).obj P := e0 R (disc.obj P)

@[reassoc]
theorem etale_discrete_simplicial_chains_degree_zero_iso_naturality {P Q : PSh} (h : P ⟶ Q) :
    ((chains R).map (disc.map h)).f 0 ≫ (e0d R Q).hom = (e0d R P).hom ≫ (free R).map h :=
  etale_discrete_chains_degree_zero_iso_free_naturality R (disc.map h)

def pr (P : PSh) : (chains R).obj (disc.obj P) ⟶ (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj ((free R).obj P) :=
  HomologicalComplex.mkHomToSingle (e0d R P).hom (fun i hi => by
    have hi' : i = -1 := by simp at hi; omega
    subst hi'
    rw [d_zero, zero_comp])

def sec (P : PSh) : (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj ((free R).obj P) ⟶ (chains R).obj (disc.obj P) :=
  HomologicalComplex.mkHomFromSingle (e0d R P).inv (fun k hk =>
    (LateralTheory.E.CechFiltPf.chains_isZero R (disc.obj P) k (by simp at hk; omega)).eq_of_tgt _ _)

theorem sec_pr (P : PSh) : sec R P ≫ pr R P = 𝟙 _ := by
  ext
  simp [sec, pr]

theorem pr_comm {P Q : PSh} (h : P ⟶ Q) :
    (chains R).map (disc.map h) ≫ pr R Q = pr R P ≫ (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map h) := by
  ext
  simp [pr, etale_discrete_simplicial_chains_degree_zero_iso_naturality_assoc, HomologicalComplex.single_map_f_self]

theorem sec_comm {P Q : PSh} (h : P ⟶ Q) :
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map h) ≫ sec R Q = sec R P ≫ (chains R).map (disc.map h) := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, sec, HomologicalComplex.mkHomFromSingle_f, HomologicalComplex.single_map_f_self,
    Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  rw [Iso.eq_inv_comp, ← etale_discrete_simplicial_chains_degree_zero_iso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

theorem cone_map_congr {K₁ L₁ K₂ L₂ : Cx R} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) {a a' : K₁ ⟶ K₂} {b b' : L₁ ⟶ L₂}
    (c : φ₁ ≫ b = a ≫ φ₂) (c' : φ₁ ≫ b' = a' ≫ φ₂) (ha : a = a') (hb : b = b') :
    mappingCone.map φ₁ φ₂ a b c = mappingCone.map φ₁ φ₂ a' b' c' := by
  subst ha hb; rfl

theorem pull_comp' {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem pull_id' (K : Cx R) (F : Shv R) (n : ℤ) (x : HK R K F n) : HK.pull R (𝟙 K) F n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

end LateralTheory.E.DiscLvlPf

open LateralTheory.E.DiscLvlPf in
theorem LateralTheory.E.DiscLvlPf.DiscLvl_of : LateralTheory.E.CechFiltPf.DiscLvl := by
  intro R _ F P Q h m hs
  let φ₁ := (chains R).map (disc.map h)
  let φ₂ := (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map h)
  let Pm := mappingCone.map φ₁ φ₂ (pr R P) (pr R Q) (pr_comm R h)
  let Sm := mappingCone.map φ₂ φ₁ (sec R P) (sec R Q) (sec_comm R h)
  have hSP : Sm ≫ Pm = 𝟙 _ := by
    rw [← mappingCone.map_comp]
    rw [cone_map_congr R φ₂ φ₂ _ (by rw [Category.id_comp, Category.comp_id]) (sec_pr R P) (sec_pr R Q)]
    exact mappingCone.map_id φ₂
  have : Subsingleton (HK R (mappingCone φ₁) F m) := hs
  refine Function.Injective.subsingleton (f := HK.pull R Pm F m) ?_
  intro x y hxy
  have := congrArg (HK.pull R Sm F m) hxy
  rwa [← pull_comp', ← pull_comp', hSP, pull_id', pull_id'] at this
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.ShiftLvlPf

universe u v

section General

variable {C : Type u} [Category.{v} C] [Abelian C]

def coneIso {A B A' B' : CochainComplex C ℤ} (φ : A ⟶ B) (ψ : A' ⟶ B') (e₁ : A ≅ A') (e₂ : B ≅ B')
    (h : φ ≫ e₂.hom = e₁.hom ≫ ψ) : mappingCone φ ≅ mappingCone ψ where
  hom := mappingCone.map φ ψ e₁.hom e₂.hom h
  inv := mappingCone.map ψ φ e₁.inv e₂.inv
    (by rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc])
  hom_inv_id := by
    rw [← mappingCone.map_comp]
    simp only [Iso.hom_inv_id]
    exact mappingCone.map_id φ
  inv_hom_id := by
    rw [← mappingCone.map_comp]
    simp only [Iso.inv_hom_id]
    exact mappingCone.map_id ψ

theorem sub_of_iso {K K' : CochainComplex C ℤ} (L : CochainComplex C ℤ) (n : ℤ) (e : K ≅ K')
    (h : Subsingleton (CohomologyClass K' L n)) : Subsingleton (CohomologyClass K L n) := by
  rw [(CohomologyClass.homAddEquiv (K := K) (L := L) (n := n)).toEquiv.subsingleton_congr]
  rw [(CohomologyClass.homAddEquiv (K := K') (L := L) (n := n)).toEquiv.subsingleton_congr] at h
  exact @Equiv.subsingleton _ _ ((((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapIso e).homCongr (Iso.refl ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (L⟦n⟧))))) h

theorem sub_of_shift {A0 Ap : CochainComplex C ℤ} (I : CochainComplex C ℤ) (p n : ℤ) (e : Ap ≅ A0⟦p⟧)
    (h : Subsingleton (CohomologyClass A0 I (n - p))) : Subsingleton (CohomologyClass Ap I n) := by
  rw [(CohomologyClass.homAddEquiv (K := Ap) (L := I) (n := n)).toEquiv.subsingleton_congr]
  rw [(CohomologyClass.homAddEquiv (K := A0) (L := I) (n := n - p)).toEquiv.subsingleton_congr] at h
  let Q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let α : (Q.obj A0)⟦p⟧ ≅ Q.obj Ap := ((Q.commShiftIso p).app A0).symm ≪≫ Q.mapIso e.symm
  let β : (Q.obj (I⟦n - p⟧))⟦p⟧ ≅ Q.obj (I⟦n⟧) :=
    ((Q.commShiftIso p).app _).symm ≪≫ Q.mapIso ((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) (n - p) p n (by omega)).app I).symm
  have e1 := (Functor.FullyFaithful.ofFullyFaithful (CategoryTheory.shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) p)).homEquiv
    (X := Q.obj A0) (Y := Q.obj (I⟦n - p⟧))
  exact @Equiv.subsingleton _ _ (e1.trans (α.homCongr β)).symm h

def singleConeIso {X Y : C} (f : X ⟶ Y) (p : ℤ) :
    mappingCone ((HomologicalComplex.single C (ComplexShape.up ℤ) (-p)).map f) ≅
      (mappingCone ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map f))⟦p⟧ :=
  let σ := (CochainComplex.singleFunctors C).shiftIso p (-p) 0 (by omega)
  coneIso _ _ (σ.app X).symm (σ.app Y).symm (σ.inv.naturality f) ≪≫
    (mappingCone.shiftIso ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map f) p).symm

end General

theorem chains_f_comm (R : Type) [CommRing R] {E₀ E : Spc} (g : E₀ ⟶ E) (p : ℕ) :
    ((chains R).map g).f (-(p : ℤ)) ≫ (chainsXIso R E p).hom =
      (chainsXIso R E₀ p).hom ≫ (free R).map (g.app (op (SimplexCategory.mk p))) := by
  unfold chains chainsXIso
  rw [Functor.comp_map]
  show (HomologicalComplex.extendMap ((chainsN R).map g) ComplexShape.embeddingDownNat).f (ComplexShape.embeddingDownNat.f p) ≫
      (HomologicalComplex.extendXIso ((chainsN R).obj E) ComplexShape.embeddingDownNat (i := p) rfl).hom =
    (HomologicalComplex.extendXIso ((chainsN R).obj E₀) ComplexShape.embeddingDownNat (i := p) rfl).hom ≫ _
  rw [HomologicalComplex.extendMap_f _ _ (i := p) rfl]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  congr 1

theorem ShiftLvl_of : LateralTheory.E.CechFiltPf.ShiftLvl := by
  intro R _ F E₀ E g p n h
  have h1 := sub_of_shift (res R F) (p : ℤ) n
    (singleConeIso ((free R).map (g.app (op (SimplexCategory.mk p)))) (p : ℤ)) h
  refine sub_of_iso (res R F) n ?_ h1
  exact coneIso _ _ ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).mapIso (chainsXIso R E₀ p))
    ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).mapIso (chainsXIso R E p))
    (by simp only [Functor.mapIso_hom, ← Functor.map_comp, chains_f_comm])

end LateralTheory.E.ShiftLvlPf
end
end

section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.LeafGhostCut LateralTheory.E.DescIntPf LateralTheory.E.KernelLocalization
namespace LateralTheory.E.RelativeTruncationSingleDegree
theorem sub_of (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ) (h : RelZS R F n f)
    (hf : ∀ z : Hrel R f F n, pull R f F n (fgt R f F n z) = 0) : Subsingleton (Hrel R f F n) := by
  refine subsingleton_of_forall_eq 0 fun z => ?_
  have h1 : fgt R f F n z = 0 := (injective_iff_map_eq_zero _).1 h.2 _ (hf z)
  exact (injective_iff_map_eq_zero _).1 (LateralTheory.E.TruncationKernel.fgt_injective_of_pull_surjective R F f n h.1) z h1
theorem rel_of (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ) (h : Subsingleton (Hrel R f F n)) :
    RelZS R F n f := by
  refine ⟨fun m hm y => range_of_bd R F f m n (by omega) y (Subsingleton.elim _ _), ?_⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := LateralTheory.E.TruncationKernel.exists_fgt_eq_of_pull_eq_zero R F f n x hx
  rw [Subsingleton.elim y 0, map_zero]
theorem pull_fgt (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ) (z : Hrel R f F n) :
    pull R f F n (fgt R f F n z) = 0 := by
  obtain ⟨c, rfl⟩ := z.mk_surjective
  exact LateralTheory.E.LeafConeExactPf.pre_inr_eq_zero _ _ c
theorem etale_relK_single_degree_pieces_of_piece_and_filtration : EtaleRelativeIsoTruncationFromLevels := by
  intro R _ F U E u n hlow h0
  refine rel_of R F u n (LateralTheory.E.CechFiltPf.CechFilt_of_disc_shift_filtGen LateralTheory.E.DiscLvlPf.DiscLvl_of LateralTheory.E.ShiftLvlPf.ShiftLvl_of
    LateralTheory.E.FiltGenPf.FiltGen_of R F u n fun p => sub_of R F _ _ ?_ (pull_fgt R F _ _))
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simpa using h0
  · exact hlow p _ (by omega)
end LateralTheory.E.RelativeTruncationSingleDegree
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
  LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.FiltrationLevelBase

def Step0 : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {Z' Z : PSh} {X' X : Spc} (g : X' ⟶ X)
  (h : Z' ⟶ Z) (a : disc.obj Z ⟶ X) (b : disc.obj Z' ⟶ X') (comm : disc.map h ≫ a = b ≫ g),
  IsIso (a.app (op ⦋0⦌)) → IsIso (b.app (op ⦋0⦌)) →
  ∀ z : Cocycle (mappingCone ((chains R).map g)) (res R F) n,
    rpull R g (disc.map h) b a comm F n (CohomologyClass.mk z) = 0 →
    ∃ c : Cochain (mappingCone ((chains R).map g)) (res R F) (n - 1),
      LateralTheory.E.FiltGenPf.V ((chains R).map g) (-1) n ((z : Cochain _ _ n) - δ (n - 1) n c)

theorem Filt_of (h0 : Step0) : LateralTheory.E.FiltrationLevelInjectivity.Filt := by
  intro _ R _ F n Z' Z X' X g h a b comm ha hb hlev
  have hk : ∀ p : ℕ, 1 ≤ p → Subsingleton (CohomologyClass (mappingCone
      ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (((chains R).map g).f (-(p : ℤ)))))
      (res R F) n) := by
    intro p hp
    refine LateralTheory.E.CechFiltPf.Piece_of LateralTheory.E.DiscLvlPf.DiscLvl_of LateralTheory.E.ShiftLvlPf.ShiftLvl_of R F g p n ?_
    obtain ⟨hi, hs⟩ := hlev p hp (n - p) (by omega)
    refine LateralTheory.E.RelativeTruncationSingleDegree.sub_of R F _ _ ⟨fun m hm => ?_, hi⟩ (LateralTheory.E.RelativeTruncationSingleDegree.pull_fgt R F _ _)
    obtain rfl : m = n - p - 1 := by omega
    exact hs
  have hk' : ∀ k : ℤ, k ≤ -1 → Subsingleton (CohomologyClass (mappingCone
      ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) k).map (((chains R).map g).f k))) (res R F) n) := by
    intro k hk1
    obtain ⟨p, rfl⟩ : ∃ p : ℕ, k = -(p : ℤ) := ⟨(-k).toNat, by omega⟩
    exact hk p (by omega)
  have claim : ∀ m : ℕ, ∀ z : Cocycle (mappingCone ((chains R).map g)) (res R F) n,
      rpull R g (disc.map h) b a comm F n (CohomologyClass.mk z) = 0 →
      ∃ c : Cochain (mappingCone ((chains R).map g)) (res R F) (n - 1),
        LateralTheory.E.FiltGenPf.V ((chains R).map g) (-((m : ℤ) + 1)) n ((z : Cochain _ _ n) - δ (n - 1) n c) := by
    intro m
    induction m with
    | zero =>
      intro z hz
      have e : (-(((0 : ℕ) : ℤ) + 1)) = -1 := by norm_num
      rw [e]
      exact h0 R F n g h a b comm ha hb z hz
    | succ m ih =>
      intro z hz
      obtain ⟨c, hc⟩ := ih z hz
      have hkm := hk' (-((m : ℤ) + 1)) (by omega)
      have hs1 := LateralTheory.E.FiltGenPf.step ((chains R).map g) (-((m : ℤ) + 1)) n hkm
      have hzz : δ n (n + 1) ((z : Cochain (mappingCone ((chains R).map g)) (res R F) n) - δ (n - 1) n c) = 0 := by
        rw [δ_sub, δ_δ, sub_zero]; exact Cocycle.δ_eq_zero z (n + 1)
      have hs2 := hs1 _ hzz
      obtain ⟨c', hc'⟩ := hs2 hc
      refine ⟨c + c', ?_⟩
      have e : (-((((m + 1 : ℕ) : ℤ)) + 1)) = -((m : ℤ) + 1) - 1 := by push_cast; ring
      rw [e, δ_add, ← sub_sub]
      exact hc'
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨c, hc1, hc2⟩ := claim (n.toNat + 1) z hx
  change CohomologyClass.mk z = 0
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨c, ?_⟩
  have hz0 : (z : Cochain (mappingCone ((chains R).map g)) (res R F) n) - δ (n - 1) n c = 0 := by
    rw [mappingCone.ext_cochain_from_iff _ (n - 1) n (by omega)]
    constructor
    · simp only [Cochain.comp_zero]
      refine Cochain.ext _ _ (fun p q hpq => ?_)
      rw [Cochain.zero_v]
      rcases lt_or_ge (-((((n.toNat + 1 : ℕ) : ℤ)) + 1)) p with hp | hp
      · exact hc1 p q hpq hp
      · exact (LateralTheory.E.CechFiltPf.res_isZero R F q (by omega)).eq_of_tgt _ _
    · simp only [Cochain.comp_zero]
      refine Cochain.ext _ _ (fun p q hpq => ?_)
      rw [Cochain.zero_v]
      rcases lt_or_ge (-((((n.toNat + 1 : ℕ) : ℤ)) + 1)) p with hp | hp
      · exact hc2 p q hpq hp
      · exact (LateralTheory.E.CechFiltPf.res_isZero R F q (by omega)).eq_of_tgt _ _
  rw [sub_eq_zero] at hz0
  exact hz0.symm

theorem goal_of (h0 : Step0) : LateralTheory.E.RelDescPf.LevelInj :=
  LateralTheory.E.FiltrationLevelInjectivity.LevelInj_of (Filt_of h0) LateralTheory.E.TruncationCokernelLevelRelations.LvlRel_of

end LateralTheory.E.FiltrationLevelBase
end
end
