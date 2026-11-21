import Development.EtaleCohomology.EtaleSheaves.LocalDescent.DescLocOf

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf Opposite

namespace LateralTheory.E.TruncCokPf

def sq {D E Y' Y'' : CommRingCat.{0}} (e : D ⟶ E) (φ' : D ⟶ Y') (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'') (h : φ' ≫ u = e ≫ φ'') :
    Arrow.mk (yoneda.map (Spec.map u)) ⟶ Arrow.mk (yoneda.map (Spec.map e)) :=
  Arrow.homMk (yoneda.map (Spec.map φ'')) (yoneda.map (Spec.map φ')) (by
    simp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom]
    rw [← Functor.map_comp, ← Functor.map_comp, ← Spec.map_comp, ← Spec.map_comp, h])

def LevelLow (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {D E Y' Y'' : CommRingCat.{0}} (e : D ⟶ E) (φ' : D ⟶ Y')
    (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'') (h : φ' ≫ u = e ≫ φ'') : Prop :=
  ∀ (p : ℕ) (m : ℤ), m < n →
    (∀ k : ℤ, k + 1 = m → Function.Surjective (pull R (disc.map ((Arrow.mapCechNerve (sq e φ' u φ'' h)).app (op (SimplexCategory.mk p)))) F k)) ∧
    Function.Injective (pull R (disc.map ((Arrow.mapCechNerve (sq e φ' u φ'' h)).app (op (SimplexCategory.mk p)))) F m)

def Desc : Prop := Hyp → ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {D E Y' Y'' : CommRingCat.{0}} (e : D ⟶ E) (φ' : D ⟶ Y')
    (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'') (hpo : IsPushout φ' e u φ''), Et e → SpS e →
    LevelLow R F n e φ' u φ'' hpo.w →
    ∀ m : ℤ, m + 1 = n → ∀ y : H R (sch.obj (Spec Y')) F m,
      pull R (sch.map (Spec.map u)) F m y ∈ Set.range (pull R (sch.map (Spec.map φ'')) F m) →
      y ∈ Set.range (pull R (sch.map (Spec.map φ')) F m)

def Levels : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'')
    (hpo : IsPushout φ' e u φ''), Et e → SpS e → P E (d ≫ e) →
    LevelLow (ZMod q) (tw q i) n e φ' u φ'' hpo.w

theorem TruncCok_of (hD : Desc) (hL : Levels) : LateralTheory.E.DescLocPf.Fine.TruncCok := by
  intro hH q _ i n A Y φ hq P hpush het hlow D d hD' Y' w φ' hpo E e Y'' u φ'' he hs hE hpo' m hm y hy
  exact hD hH (ZMod q) (tw q i) n e φ' u φ'' hpo' he hs
    (hL hH q i n φ hq P hpush het hlow D d hD' Y' w φ' hpo E e Y'' u φ'' hpo' he hs hE) m hm y hy

end LateralTheory.E.TruncCokPf
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.TruncCokPf Opposite

namespace LateralTheory.E.LevelsPf

def CechLevel : Prop := ∀ (p : ℕ) {D E Y' Y'' : CommRingCat.{0}} (e : D ⟶ E) (φ' : D ⟶ Y') (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'')
    (hpo : IsPushout φ' e u φ''),
    ∃ (Ep Yp : CommRingCat.{0}) (dp : D ⟶ Ep) (wp : Y' ⟶ Yp) (φp : Ep ⟶ Yp), IsPushout φ' dp wp φp ∧
      (∀ {A : CommRingCat.{0}} (d : A ⟶ D) (P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop), PushClosed P → P D d →
        P E (d ≫ e) → P Ep (d ≫ dp)) ∧
      Nonempty (Arrow.mk ((Arrow.mapCechNerve (sq e φ' u φ'' hpo.w)).app (op (SimplexCategory.mk p))) ≅
        Arrow.mk (yoneda.map (Spec.map φp)))

theorem pull_iso_bij (R : Type) [CommRing R] {E E' : Spc} (a : E ≅ E') (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R a.hom F n) := by
  have h1 : ∀ x, pull R a.inv F n (pull R a.hom F n x) = x := fun x => by
    rw [← pull_comp, Iso.inv_hom_id, pull_id]
  have h2 : ∀ x, pull R a.hom F n (pull R a.inv F n x) = x := fun x => by
    rw [← pull_comp, Iso.hom_inv_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem transfer (R : Type) [CommRing R] (F : Shv R) {P Q P' Q' : PSh} (f : P ⟶ Q) (g : P' ⟶ Q')
    (α : Arrow.mk f ≅ Arrow.mk g) (n : ℤ) :
    (Function.Surjective (pull R (disc.map g) F n) → Function.Surjective (pull R (disc.map f) F n)) ∧
    (Function.Injective (pull R (disc.map g) F n) → Function.Injective (pull R (disc.map f) F n)) := by
  let αl : P ≅ P' := Arrow.leftFunc.mapIso α
  let αr : Q ≅ Q' := Arrow.rightFunc.mapIso α
  have hw : f ≫ αr.hom = αl.hom ≫ g := by
    exact (Arrow.w α.hom).symm
  have hf : f = αl.hom ≫ g ≫ αr.inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]; exact hw
  have he : ⇑(pull R (disc.map f) F n) =
      pull R (disc.mapIso αl).hom F n ∘ pull R (disc.map g) F n ∘ pull R (disc.mapIso αr).symm.hom F n := by
    funext x
    rw [hf, Functor.map_comp, Functor.map_comp, pull_comp, pull_comp]; rfl
  have bl := pull_iso_bij R (disc.mapIso αl) F n
  have br := pull_iso_bij R (disc.mapIso αr).symm F n
  refine ⟨fun hs => ?_, fun hi => ?_⟩
  · rw [he]; exact bl.2.comp (hs.comp br.2)
  · rw [he]; exact bl.1.comp (hi.comp br.1)

theorem Levels_of (hC : CechLevel) : LateralTheory.E.TruncCokPf.Levels := by
  intro hH q _ i n A Y φ hq P hpush het hlow D d hD Y' w φ' hpo E e Y'' u φ'' hpo' he hs hE p m hm
  obtain ⟨Ep, Yp, dp, wp, φp, hpp, hP, ⟨α⟩⟩ := hC p e φ' u φ'' hpo'
  have hsq : IsPushout φ (d ≫ dp) (w ≫ wp) φp := hpo.paste_vert hpp
  have hrel : RelZ q i m φp := hlow m hm Ep (d ≫ dp) (hP d P hpush hD hE) Yp (w ≫ wp) φp hsq
  have ht := fun k => transfer (ZMod q) (tw q i) _ _ α k
  refine ⟨fun k hk => (ht k).1 (hrel.1 k hk), (ht m).2 hrel.2⟩

end LateralTheory.E.LevelsPf
end
end
