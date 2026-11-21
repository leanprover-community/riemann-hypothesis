import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PhiAsm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PhiExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendChainMapAlongQuasiIsoKInjectiveStatement

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem single_key {R : Type} [CommRing R] (Φ : Shv R ⥤ Shv R) [Φ.Additive] (F : Shv R) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (Φ.obj F)).inv ≫
      ((HomologicalComplex.singleMapHomologicalComplex Φ (ComplexShape.up ℤ) 0).inv.app F).f 0 =
    Φ.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv := by
  rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  simp
  rfl

theorem UpperTheory.Gal.TranscendenceTraces.phiQis_of :
    PhiQis := by
  intro R _ Φ _ hΦ F
  obtain ⟨-, -, -, hq, hι, -, -, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F
  haveI : Φ.PreservesHomology := (Φ.exact_tfae.out 1 2).1 hΦ
  let e := (HomologicalComplex.singleMapHomologicalComplex Φ (ComplexShape.up ℤ) 0).app F
  let φ : (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0 ⋙
      Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj F ⟶
      (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj (res R F) :=
    (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map (resAug F)
  haveI hφ : QuasiIso φ :=
    (inferInstance : QuasiIso ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map (resAug F)))
  haveI he : QuasiIso e.inv := inferInstance
  refine ⟨e.inv ≫ φ, quasiIso_comp e.inv φ, ?_⟩
  erw [HomologicalComplex.comp_f]
  rw [← Category.assoc]
  erw [single_key]
  exact (Φ.map_comp _ _).symm.trans (congrArg Φ.map hι)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.extRes_of :
    ExtRes := by
  intro R _ F G T ε _
  obtain ⟨hKI, -, hGE, -, hι, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R G
  haveI := hKI
  haveI := hGE
  have key := GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective R F T (res R G) ε
  refine ⟨fun a => ?_, fun m m' h U i n k hin hnk y hy => ?_⟩
  · obtain ⟨m, hm⟩ := key.1 ((CochainComplex.singleFunctor (Shv R) 0).map a ≫ resAug G)
    refine ⟨m, ?_⟩
    have h0 : ε.f 0 ≫ m.f 0 = ((CochainComplex.singleFunctor (Shv R) 0).map a).f 0 ≫ (resAug G).f 0 := by
      rw [← HomologicalComplex.comp_f, hm, HomologicalComplex.comp_f]
    rw [h0, ← hι]
    change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫
        ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map a).f 0 ≫ (resAug G).f 0 =
      a ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).inv ≫ (resAug G).f 0
    rw [HomologicalComplex.single_map_f_self]
    exact (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans
      ((Iso.inv_hom_id_assoc _ _).trans (Category.assoc _ _ _))
  · have hε : ε ≫ m = ε ≫ m' := by
      refine HomologicalComplex.from_single_hom_ext (j := 0) ?_
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
      exact (Iso.cancel_iso_inv_left (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F) _ _).1 h
    obtain ⟨H⟩ := key.2 m m' hε
    have hc := H.comm n
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel n k from hnk),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel i n from hin)] at hc
    have e1 : Sec.map (T.d n k ≫ H.hom k n) y = 0 := by
      change Sec.map (H.hom k n) (Sec.map (T.d n k) y) = 0
      rw [hy]
      exact map_zero _
    have e2 : Sec.map (H.hom n i ≫ (res R G).d i n) y = Sec.map ((res R G).d i n) (Sec.map (H.hom n i) y) := rfl
    have e3 : ∀ {A B : Shv R} (f g : A ⟶ B) (x : Sec A U), Sec.map (f + g) x = Sec.map f x + Sec.map g x :=
      fun _ _ _ => rfl
    refine ⟨Sec.map (H.hom n i) y, ?_⟩
    rw [hc, e3, e3, e1, e2, zero_add, add_sub_cancel_right]
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private noncomputable def postFam {Z S : Scheme.{0}} {p : Z ⟶ S} {R : Type} [CommRing R] {G K J : Shv R}
    (t : Fam0 p G K) (m : K ⟶ J) : Fam0 p G J where
  app A := ((m.hom.app (op A.U)).hom.toAddMonoidHom).comp (t.app A)
  nat {A B} s a := by
    change Sec.res s.g (Sec.map m (t.app B a)) = Sec.map m (t.app A (Sec.res s.k a))
    rw [← t.nat s a, map_res]

private noncomputable def preFam {Z S : Scheme.{0}} {p : Z ⟶ S} {R : Type} [CommRing R] {G K J : Shv R}
    (d : G ⟶ K) (t : Fam0 p K J) : Fam0 p G J where
  app A := (t.app A).comp ((d.hom.app (op A.V)).hom.toAddMonoidHom)
  nat {A B} s a := by
    change Sec.res s.g (t.app B (Sec.map d a)) = t.app A (Sec.map d (Sec.res s.k a))
    rw [t.nat s, map_res]

theorem UpperTheory.Gal.TranscendenceTraces.famHom_of :
    FamHom := by
  intro Q Z S p Φ _ e hrep I J
  constructor
  · intro m
    refine ⟨⟨fun n => postFam (e (I.X n)) (m.f n), fun A s t a => ?_⟩, fun n A a => rfl⟩
    have hc := congrArg (fun φ => Sec.map φ ((e (I.X s)).app A a)) (m.comm s t)
    exact hc.trans (congrArg (Sec.map (m.f t)) (hrep.nat (I.d s t) A a))
  · intro τ
    choose mm hmm _ using fun n => hrep.univ (I.X n) (J.X n) (τ.deg n)
    refine ⟨⟨mm, fun i j _ => ?_⟩, fun n A a => (hmm n A a).symm⟩
    apply (hrep.univ (I.X i) (J.X j) (postFam (τ.deg i) (J.d i j))).unique
    · intro A a
      exact congrArg (Sec.map (J.d i j)) (hmm i A a)
    · intro A a
      exact ((congrArg (Sec.map (mm j)) (hrep.nat (I.d i j) A a)).trans (hmm j A _)).trans
        (τ.comm A i j a).symm
end

section
namespace UpperTheory.Gal.TranscendenceTraces

theorem fL_of : PhiEx → FL := fL_of_parts phiQis_of extRes_of famHom_of

end UpperTheory.Gal.TranscendenceTraces
end
