import Development.EtaleCohomology.TateTwists.EtaleRestrictScalarsResolutionCompatible
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import Mathlib.Algebra.Homology.Localization
import Mathlib.CategoryTheory.Abelian.Injective.Extend

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleSheafRestrictScalarsInjectiveResolutionHomExists : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S),
    ∃ m : ∀ n : ℤ, (restr φ).obj ((res S F).X n) ⟶ (res R ((restr φ).obj F)).X n,
      (∀ i j : ℤ, (restr φ).map ((res S F).d i j) ≫ m j = m i ≫ (res R ((restr φ).obj F)).d i j) ∧
      (restr φ).map (resι S F) ≫ m 0 = resι R ((restr φ).obj F)

namespace LateralTheory.EtaleFoundations

theorem etaleSheaf_restrictScalars_resolution_comparison_of_hom (hH : EtaleSheafRestrictScalarsInjectiveResolutionHomExists) : EtaleRestrictScalarsResolutionCompatible := by
  intro R S _ _ φ F U a
  obtain ⟨m, hc, h0⟩ := hH R S φ F
  have hex : ∃ ρ : SemiMap (res S F) (res R ((restr φ).obj F)), ∀ (U : Scheme.{0}) (a : Sec F U),
      ρ.app U 0 (Sec.map (resι S F) a) = Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a) := by
    refine ⟨⟨fun U s => ((m s).hom.app (op U)).hom.toAddMonoidHom, ?_, ?_⟩, ?_⟩
    · intro V U g s x
      have h := (m s).hom.naturality g.op
      exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) x).symm
    · intro U s t x
      have h := congrArg (fun f : (restr φ).obj ((res S F).X s) ⟶ (res R ((restr φ).obj F)).X t => (f.hom.app (op U)).hom x) (hc s t)
      exact h.symm
    · intro U x
      exact congrArg (fun f : (restr φ).obj F ⟶ (res R ((restr φ).obj F)).X 0 => (f.hom.app (op U)).hom x) h0
  exact pick_spec hex U a

end LateralTheory.EtaleFoundations
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

lemma restr_ex_hom_ext_of_qis {C : Type*} [Category C] [Abelian C] {K K' L : CochainComplex C ℤ}
    [L.IsKInjective] (s : K ⟶ K') [QuasiIso s] (f : K ⟶ L) :
    ∃ g : K' ⟶ L, Nonempty (Homotopy (s ≫ g) f) := by
  have hL := CochainComplex.IsKInjective.rightOrthogonal L
  rw [← ObjectProperty.isLocal_trW] at hL
  have hs : (HomotopyCategory.subcategoryAcyclic C).trW ((HomotopyCategory.quotient C _).map s) := by
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic, HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact (HomologicalComplex.mem_quasiIso_iff _).2 inferInstance
  obtain ⟨g', hg'⟩ := (hL _ hs).2 ((HomotopyCategory.quotient C _).map f)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C _).map_surjective g'
  refine ⟨g, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  simpa using hg'

def EtaleSheafRestrictScalarsFunctorExact : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S),
    PreservesFiniteLimits (restr φ) ∧ PreservesFiniteColimits (restr φ)

theorem etaleSheaf_restrictScalars_resolution_hom_exists_of_exact (hE : EtaleSheafRestrictScalarsFunctorExact) : EtaleSheafRestrictScalarsInjectiveResolutionHomExists := by
  intro R S _ _ φ F
  obtain ⟨h1, h2⟩ := hE R S φ
  let G := restr φ
  have : G.Additive := G.additive_of_preserves_binary_products
  let IS := injectiveResolution F
  let IR := injectiveResolution (G.obj F)
  have : (res R (G.obj F)).IsKInjective := inferInstanceAs IR.cochainComplex.IsKInjective
  have : (res R (G.obj F)).IsStrictlyGE 0 := inferInstanceAs (IR.cochainComplex.IsStrictlyGE 0)
  let s := (G.mapHomologicalComplex (ComplexShape.up ℤ)).map IS.ι'
  have : QuasiIso s := inferInstance
  let f0 := (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app F ≫ IR.ι'
  obtain ⟨g, ⟨h⟩⟩ := restr_ex_hom_ext_of_qis (L := res R (G.obj F)) s f0
  refine ⟨fun n => g.f n, fun i j => (g.comm i j).symm, ?_⟩
  have hz1 : IsZero (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)).X 1) :=
    G.map_isZero (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F 1 (by decide))
  have key : (s ≫ g).f 0 = f0.f 0 := by
    rw [h.comm 0]
    have e1 : dNext 0 h.hom = 0 := by
      have e : h.hom 1 0 = 0 := hz1.eq_of_src _ _
      rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel 0 1 from rfl), e, comp_zero]
    have e2 : prevD 0 h.hom = 0 := by
      rw [prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl),
        ((res R (G.obj F)).isZero_of_isStrictlyGE 0 (-1) (by decide)).eq_of_tgt (h.hom 0 (-1)) 0, zero_comp]
    rw [e1, e2, zero_add, zero_add]
  have key2 := congrArg (fun x => G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ x) key
  simp only [s, f0, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self, ← Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id, Functor.map_id, Category.id_comp] at key2
  have key3 : G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ G.map (IS.ι'.f 0) ≫ g.f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (G.obj F)).inv ≫ IR.ι'.f 0 := by
    refine key2.trans ?_
    have c2 : ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app F).f 0 =
        G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (G.obj F)).inv :=
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self _ _ _ _
    calc _ = G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ ((G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (G.obj F)).inv) ≫ IR.ι'.f 0) := by
          exact congrArg (fun x => G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ x) (congrArg (fun y => y ≫ IR.ι'.f 0) c2)
      _ = _ := by
          have aux : ∀ {A B : Shv S} {Y Z : Shv R} (e : A ≅ B) (u : G.obj B ⟶ Y) (v : Y ⟶ Z),
              G.map e.inv ≫ (G.map e.hom ≫ u) ≫ v = u ≫ v := by
            intro A B Y Z e u v
            rw [← Category.assoc, ← Category.assoc, ← G.map_comp, Iso.inv_hom_id, G.map_id, Category.id_comp]
          exact aux _ _ _
  simp only [resι]
  erw [Functor.map_comp, Category.assoc]
  exact key3

end LateralTheory.EtaleFoundations
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

lemma restr_isRightAdjoint (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) :
    (restr φ).IsRightAdjoint := by
  unfold restr
  exact (Sheaf.adjunction Scheme.etaleTopology.{0} (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1}
    ((ULift.ringEquiv.symm : S ≃+* ULift.{1} S).toRingHom.comp (φ.comp (ULift.ringEquiv : ULift.{1} R ≃+* R).toRingHom)))).isRightAdjoint

lemma restr_isLeftAdjoint (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) :
    (restr φ).IsLeftAdjoint := by
  unfold restr
  set f := ((ULift.ringEquiv.symm : S ≃+* ULift.{1} S).toRingHom.comp (φ.comp (ULift.ringEquiv : ULift.{1} R ≃+* R).toRingHom))
  have hpl : PreservesLimitsOfSize.{0, 1} (ModuleCat.coextendScalars.{1, 1, 1} f) :=
    (ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} f).rightAdjoint_preservesLimits
  have : Scheme.etaleTopology.{0}.HasSheafCompose (ModuleCat.coextendScalars.{1, 1, 1} f) :=
    hasSheafCompose_of_preservesLimitsOfSize _
  have adj := Sheaf.adjunction Scheme.etaleTopology.{0} (ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} f)
  have := (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).counit_isIso_of_R_fully_faithful
  have e : Sheaf.composeAndSheafify Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} f) ≅
      sheafCompose Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} f) :=
    NatIso.ofComponents (fun X => (asIso (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).counit).app
      ((sheafCompose Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} f)).obj X)) (by
        intro X Y g
        exact (sheafificationAdjunction _ _).counit.naturality
          ((sheafCompose Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} f)).map g))
  exact ⟨_, ⟨adj.ofNatIsoLeft e⟩⟩

theorem etaleSheaf_restrictScalars_functor_exact_of_adjoints : EtaleSheafRestrictScalarsFunctorExact := by
  intro R S _ _ φ
  have := restr_isRightAdjoint R S φ
  have := restr_isLeftAdjoint R S φ
  exact ⟨inferInstance, inferInstance⟩

end LateralTheory.EtaleFoundations
end
