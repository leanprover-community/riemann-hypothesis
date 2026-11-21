import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

def LCoprodEmpty : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (E : Scheme.{0}), IsInitial E → ∀ (N : ℤ) (u : V l E N), u = 0

def LCoprodTwo : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] {A B E : Scheme.{0}} (i : A ⟶ E) (j : B ⟶ E),
  IsColimit (BinaryCofan.mk i j) → ∀ (N : ℤ) (u : V l E N), pb l i N u = 0 → pb l j N u = 0 → u = 0

def splitCofan {n : ℕ} {W : Fin (n + 1) → Scheme.{0}} {E : Scheme.{0}} (ι : ∀ i, W i ⟶ E)
    (hc : IsColimit (Cofan.mk E ι)) :
    IsColimit (BinaryCofan.mk (ι 0) (Sigma.desc (fun i : Fin n => ι i.succ))) :=
  BinaryCofan.IsColimit.mk _
    (fun {T} f g => hc.desc (Cofan.mk T (Fin.cases (motive := fun i => W i ⟶ T) f (fun i => Sigma.ι (fun i : Fin n => W i.succ) i ≫ g))))
    (fun {T} f g => by
      have := hc.fac (Cofan.mk T (Fin.cases (motive := fun i => W i ⟶ T) f (fun i => Sigma.ι (fun i : Fin n => W i.succ) i ≫ g))) ⟨0⟩
      exact this)
    (fun {T} f g => by
      show Sigma.desc (fun i : Fin n => ι i.succ) ≫ hc.desc (Cofan.mk T (Fin.cases (motive := fun i => W i ⟶ T) f (fun i => Sigma.ι (fun i : Fin n => W i.succ) i ≫ g))) = g
      apply Sigma.hom_ext
      intro i
      have := hc.fac (Cofan.mk T (Fin.cases (motive := fun i => W i ⟶ T) f (fun i => Sigma.ι (fun i : Fin n => W i.succ) i ≫ g))) ⟨i.succ⟩
      rw [Sigma.ι_desc_assoc]
      exact this)
    (fun {T} f g (m : E ⟶ T) h1 h2 => by
      apply hc.hom_ext
      rintro ⟨i⟩
      rw [hc.fac]
      refine Fin.cases ?_ (fun i => ?_) i
      · exact h1
      · have h2' : Sigma.desc (fun i : Fin n => ι i.succ) ≫ m = g := h2
        show ι i.succ ≫ m = Sigma.ι (fun i : Fin n => W i.succ) i ≫ g
        rw [← h2', ← Category.assoc, Sigma.ι_desc])

def LEmptyH : Prop := Base → ∀ (R : Type) [CommRing R] (E : Scheme.{0}), IsInitial E → ∀ (F : Shv R) (n : ℤ),
  Subsingleton (H R (sch.obj E) F n)

def LTwoH : Prop := Base → ∀ (R : Type) [CommRing R] {A B E : Scheme.{0}} (i : A ⟶ E) (j : B ⟶ E),
  IsColimit (BinaryCofan.mk i j) → ∀ (F : Shv R) (n : ℤ) (x : H R (sch.obj E) F n),
  pull R (sch.map i) F n x = 0 → pull R (sch.map j) F n x = 0 → x = 0

def LFreeEmpty : Prop := ∀ (R : Type) [CommRing R] (E : Scheme.{0}), IsInitial E → IsZero ((free R).obj (yoneda.obj E))

theorem chains_zero (R : Type) [CommRing R] (E : Scheme.{0}) (hZ : IsZero ((free R).obj (yoneda.obj E))) (p : ℤ) :
    IsZero (((chains R).obj (sch.obj E)).X p) := by
  rcases le_or_gt p 0 with h | h
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, p = -(m : ℤ) := ⟨p.natAbs, by omega⟩
    exact hZ.of_iso (chainsXIso R (sch.obj E) m)
  · apply HomologicalComplex.isZero_extend_X
    intro i hi
    have : (ComplexShape.embeddingDownNat).f i = -(i : ℤ) := rfl
    omega

theorem H_sub (R : Type) [CommRing R] (E : Scheme.{0}) (hZ : IsZero ((free R).obj (yoneda.obj E))) (F : Shv R) (n : ℤ) :
    Subsingleton (H R (sch.obj E) F n) := by
  have : Subsingleton (CochainComplex.HomComplex.Cochain ((chains R).obj (sch.obj E)) (res R F) n) :=
    ⟨fun a b => CochainComplex.HomComplex.Cochain.ext _ _ (fun p q _ => (chains_zero R E hZ p).eq_of_src _ _)⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := CochainComplex.HomComplex.CohomologyClass.mk_surjective x
  obtain ⟨b, rfl⟩ := CochainComplex.HomComplex.CohomologyClass.mk_surjective y
  have hab : a = b := Subtype.ext (@Subsingleton.elim _ this _ _)
  rw [hab]

end LateralTheory.EtaleTrace

end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

def LTwoCover : Prop := ∀ (R : Type) [CommRing R] {A B E : Scheme.{0}} (i : A ⟶ E) (j : B ⟶ E),
  IsColimit (BinaryCofan.mk i j) → Cover2 R (sch.map i) (sch.map j)

def LTwoOverlap : Prop := ∀ (R : Type) [CommRing R] {A B E : Scheme.{0}} (i : A ⟶ E) (j : B ⟶ E),
  IsColimit (BinaryCofan.mk i j) → ∀ (F : Shv R) (n : ℤ), Subsingleton (H R (pullback (sch.map i) (sch.map j)) F n)

def LTwoMV : Prop := Base → ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g →
  ∀ (F : Shv R), (∀ m : ℤ, Subsingleton (H R (pullback f g) F m)) →
  ∀ (n : ℤ) (x : H R E F n), pull R f F n x = 0 → pull R g F n x = 0 → x = 0

def LTwoEpi : Prop := ∀ (R : Type) [CommRing R] {A B E : Scheme.{0}} (i : A ⟶ E) (j : B ⟶ E),
  IsColimit (BinaryCofan.mk i j) → ∀ n, Epi (biprod.desc ((free R).map ((sch.map i).app n)) ((free R).map ((sch.map j).app n)))

instance : PreservesLimitsOfSize.{0, 0} (disc : PSh ⥤ Spc) := by
  unfold disc SimplicialObject.const
  infer_instance

instance : PreservesLimitsOfSize.{0, 0} (sch : Scheme.{0} ⥤ Spc) := by
  unfold sch
  infer_instance

end LateralTheory.EtaleTrace
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

theorem ltwo_fm (R : Type) [CommRing R] {X Y : Type} (g : X ⟶ Y) (x : X) :
    ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map g)).hom
      (ModuleCat.freeMk (X := uliftFunctor.{1}.obj X) (ULift.up x)) =
      ModuleCat.freeMk (X := uliftFunctor.{1}.obj Y) (ULift.up (g x)) :=
  Finsupp.mapDomain_single

end LateralTheory.EtaleTrace
end
end
