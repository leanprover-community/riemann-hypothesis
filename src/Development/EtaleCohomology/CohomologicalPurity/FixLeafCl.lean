import Development.EtaleCohomology.CohomologicalPurity.FinLeafThom
import Development.EtaleCohomology.CohomologicalPurity.FinLeafChart
import Development.EtaleCohomology.CohomologicalPurity.LeafExcIdentPf
import Development.EtaleCohomology.CohomologicalPurity.LeafExcDegPf
import Development.EtaleCohomology.CohomologicalPurity.LeafFreeCokInjPf
import Development.EtaleCohomology.CohomologicalPurity.LeafSurjGeoPf
import Development.EtaleCohomology.CohomologicalPurity.LeafInjGeoPf
import Development.EtaleCohomology.CohomologicalPurity.LeafDescOSepPf
import Development.EtaleCohomology.CohomologicalPurity.LeafDescOGluePfP
import Development.EtaleCohomology.CohomologicalPurity.LeafDictPf
import Development.EtaleCohomology.CohomologicalPurity.LeafDiscNrmPf
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Development.EtaleCohomology.CohomologicalPurity.LeafZornPf
import Development.EtaleCohomology.CohomologicalPurity.LeafFlqPf
import Development.EtaleCohomology.CohomologicalPurity.LeafZlocPf
import Development.EtaleCohomology.CohomologicalPurity.LeafStepPf
import Development.EtaleCohomology.CohomologicalPurity.LeafClCut
import Development.EtaleCohomology.CohomologicalPurity.LeafVanRingPf
import Development.EtaleCohomology.CohomologicalPurity.LeafGenRingPf
import Development.EtaleCohomology.CohomologicalPurity.LeafGenKerPf
import Development.EtaleCohomology.CohomologicalPurity.LeafMatPf
import Development.EtaleCohomology.CohomologicalPurity.LeafCmpPf

section
namespace LateralTheory.Fin.LeafExc
theorem etale_excision_identification_of_excision : LateralTheory.CohomologicalPurity.LeafExcIdent := by
  apply LateralTheory.CohomologicalPurity.EtaleExcIdent
theorem etale_excision_cohomological_degree_of_excision : LateralTheory.CohomologicalPurity.LeafExcDeg := by
  apply LateralTheory.CohomologicalPurity.LeafExcDeg_of
theorem etale_excision_formal_reduction_of_excision : LateralTheory.CohomologicalPurity.LeafExcFormal := by
  apply LateralTheory.CohomologicalPurity.LeafExcFormal_of <;> first | exact etale_excision_identification_of_excision | exact etale_excision_cohomological_degree_of_excision
theorem etale_excision_free_cokernel_injective_of_excision : LateralTheory.CohomologicalPurity.LeafFreeCokInj := by
  apply LateralTheory.CohomologicalPurity.LeafFreeCokInj_of
theorem etale_excision_cokernel_free_of_excision : LateralTheory.CohomologicalPurity.LeafFreeCok := by
  apply LateralTheory.CohomologicalPurity.LeafFreeCok_of_inj <;> first | exact etale_excision_free_cokernel_injective_of_excision
theorem etale_excision_surjective_geometric_points_of_excision : LateralTheory.CohomologicalPurity.LeafSurjGeo := by
  apply LateralTheory.CohomologicalPurity.LeafSurjGeo_of
theorem etale_excision_injective_geometric_points_of_excision : LateralTheory.CohomologicalPurity.LeafInjGeo := by
  apply LateralTheory.CohomologicalPurity.LeafInjGeo_of
theorem etale_excision_sheaf_level_of_excision : LateralTheory.CohomologicalPurity.LeafExcSheaf := by
  apply LateralTheory.CohomologicalPurity.LeafExcSheaf_of <;> first | exact etale_excision_cokernel_free_of_excision | exact etale_excision_surjective_geometric_points_of_excision | exact etale_excision_injective_geometric_points_of_excision
theorem etale_excision_isomorphism_of_excision : LateralTheory.CohomologicalPurity.LeafExc := by
  apply LateralTheory.CohomologicalPurity.LeafExc_of <;> first | exact etale_excision_formal_reduction_of_excision | exact etale_excision_sheaf_level_of_excision
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafExc := etale_excision_isomorphism_of_excision
end LateralTheory.Fin.LeafExc
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.DictPf

theorem LeafDbl_pf : LeafDbl := by
  refine ⟨fun U => (PreservesPushout.iso disc (yoneda.map U.ι) (yoneda.map U.ι)).symm, ?_, ?_, ?_⟩
  · intro X U
    exact PreservesPushout.inl_iso_inv disc _ _
  · intro X U
    exact PreservesPushout.inr_iso_inv disc _ _
  · intro X' X f U' U h
    dsimp only
    refine (Iso.inv_comp_eq _).1 ?_
    apply pushout.hom_ext
    · have a1 : pushout.inl (opn U').hom (opn U').hom ≫ (PreservesPushout.iso disc (yoneda.map U'.ι) (yoneda.map U'.ι)).hom =
          disc.map (pushout.inl _ _) := PreservesPushout.inl_iso_hom disc _ _
      have a2 : disc.map (pushout.inl (yoneda.map U.ι) (yoneda.map U.ι)) ≫
          (PreservesPushout.iso disc (yoneda.map U.ι) (yoneda.map U.ι)).symm.hom = pushout.inl (opn U).hom (opn U).hom :=
        PreservesPushout.inl_iso_inv disc _ _
      have il : pushout.inl _ _ ≫ Qmap f U' U h = yoneda.map f ≫ pushout.inl _ _ := pushout.inl_desc _ _ _
      show pushout.inl (opn U').hom (opn U').hom ≫ (PreservesPushout.iso disc (yoneda.map U'.ι) (yoneda.map U'.ι)).hom ≫
        disc.map (Qmap f U' U h) ≫ (PreservesPushout.iso disc (yoneda.map U.ι) (yoneda.map U.ι)).symm.hom = _
      erw [← Category.assoc, a1, ← Category.assoc, ← Functor.map_comp, il, Functor.map_comp, Category.assoc, a2]
      exact (pushout.inl_desc _ _ _).symm
    · have a1 : pushout.inr (opn U').hom (opn U').hom ≫ (PreservesPushout.iso disc (yoneda.map U'.ι) (yoneda.map U'.ι)).hom =
          disc.map (pushout.inr _ _) := PreservesPushout.inr_iso_hom disc _ _
      have a2 : disc.map (pushout.inr (yoneda.map U.ι) (yoneda.map U.ι)) ≫
          (PreservesPushout.iso disc (yoneda.map U.ι) (yoneda.map U.ι)).symm.hom = pushout.inr (opn U).hom (opn U).hom :=
        PreservesPushout.inr_iso_inv disc _ _
      have il : pushout.inr _ _ ≫ Qmap f U' U h = yoneda.map f ≫ pushout.inr _ _ := pushout.inr_desc _ _ _
      show pushout.inr (opn U').hom (opn U').hom ≫ (PreservesPushout.iso disc (yoneda.map U'.ι) (yoneda.map U'.ι)).hom ≫
        disc.map (Qmap f U' U h) ≫ (PreservesPushout.iso disc (yoneda.map U.ι) (yoneda.map U.ι)).symm.hom = _
      erw [← Category.assoc, a1, ← Category.assoc, ← Functor.map_comp, il, Functor.map_comp, Category.assoc, a2]
      exact (pushout.inr_desc _ _ _).symm

theorem LeafDict_of' (hD : Cl.LeafDisc) (hE : LeafEv) (hP : LeafPair) : Cl.LeafDict := LeafDict_of hD hE hP LeafDbl_pf

end LateralTheory.CohomologicalPurity.DictPf
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.KummerTheory.FlasquePf

namespace LateralTheory.CohomologicalPurity.DictPf

section
variable {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}}

theorem ev_res' (m : (free R).obj (yoneda.obj X) ⟶ G) {V : Scheme.{0}} (h : V ⟶ X) :
    (m.hom.app (op V)).hom (freeGen R (yoneda.obj X) V h) = Sec.res h (ev m) := by
  calc (m.hom.app (op V)).hom (freeGen R (yoneda.obj X) V h)
      = (m.hom.app (op V)).hom (freeGen R (yoneda.obj X) V ((yoneda.obj X).map h.op (𝟙 X))) := by simp
    _ = (m.hom.app (op V)).hom (Sec.res h (freeGen R (yoneda.obj X) X (𝟙 X))) := by rw [freeGen_res]
    _ = Sec.res h (ev m) := by
      have := congrArg (fun φ => ModuleCat.Hom.hom φ (freeGen R (yoneda.obj X) X (𝟙 X))) (m.hom.naturality h.op)
      exact this

theorem eq_ofSec (m : (free R).obj (yoneda.obj X) ⟶ G) : m = ofSec G (ev m) := by
  apply ((sheafificationAdjunction _ _).homEquiv _ G).injective
  unfold ofSec
  rw [Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext V
  apply ModuleCat.free_hom_ext
  intro x
  change (m.hom.app V).hom (freeGen R (yoneda.obj X) V.unop x.down) = _
  rw [ev_res']
  unfold toG
  symm
  change ModuleCat.freeDesc _ (ModuleCat.freeMk x) = _
  refine (ModuleCat.freeDesc_apply _ _).trans ?_
  rfl

end

theorem LeafEv_of : LeafEv := by
  intro R _ G X
  refine ⟨?_, ?_, ?_⟩
  · intro m m' h
    rw [eq_ofSec m, eq_ofSec m', h]
  · intro m m'
    rfl
  · intro Y f m
    change (m.hom.app (op Y)).hom ((((free R).map (yoneda.map f)).hom.app (op Y)).hom
      (freeGen R (yoneda.obj Y) Y (𝟙 Y))) = _
    rw [freeGen_map]
    simp only [yoneda_map_app]
    exact ev_res' m f

end LateralTheory.CohomologicalPurity.DictPf
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.KummerTheory.FlasquePf

namespace LateralTheory.CohomologicalPurity.LeafPairPf

instance presFreeMod (R : Type) [CommRing R] :
    PreservesColimitsOfShape WalkingSpan (ModuleCat.free (ULift.{1, 0} R)) :=
  (ModuleCat.adj (ULift.{1, 0} R)).leftAdjoint_preservesColimits.preservesColimitsOfShape

instance presL (R : Type) [CommRing R] :
    PreservesColimitsOfShape WalkingSpan (uliftFunctor.{1, 0} ⋙ ModuleCat.free (ULift.{1, 0} R)) :=
  inferInstance

instance presFreeP (R : Type) [CommRing R] : PreservesColimitsOfShape WalkingSpan (freeP R) := by
  unfold freeP; infer_instance

instance presFree (R : Type) [CommRing R] : PreservesColimitsOfShape WalkingSpan (free R) := by
  unfold free; infer_instance

theorem gen_eq {R : Type} [CommRing R] {G : Shv R} {X V : Scheme.{0}} (m : (free R).obj (yoneda.obj X) ⟶ G)
    (g : V ⟶ X) : (m.hom.app (op V)).hom (freeGen R (yoneda.obj X) V g) = Sec.res g (DictPf.ev m) := by
  have nat := congrArg (fun k => k.hom (freeGen R (yoneda.obj X) X (𝟙 X))) (m.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at nat
  change _ = (G.obj.map g.op).hom ((m.hom.app (op X)).hom (freeGen R (yoneda.obj X) X (𝟙 X)))
  rw [← nat]
  change _ = (m.hom.app (op V)).hom (Sec.res g (freeGen R (yoneda.obj X) X (𝟙 X)))
  rw [freeGen_res]
  congr 2

theorem ext_gen {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} (m m' : (free R).obj (yoneda.obj X) ⟶ G)
    (h : DictPf.ev m = DictPf.ev m') : m = m' := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ G.property
  ext V : 2
  apply ModuleCat.free_hom_ext
  intro x
  change (m.hom.app V).hom (freeGen R (yoneda.obj X) V.unop x.down) = (m'.hom.app V).hom (freeGen R (yoneda.obj X) V.unop x.down)
  rw [gen_eq m x.down, gen_eq m' x.down, h]

theorem ev_ofSec {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} (s : Sec G X) : DictPf.ev (ofSec G s) = s :=
  ofSec_gen G s

theorem ev_pre {R : Type} [CommRing R] {G : Shv R} {Y X : Scheme.{0}} (f : Y ⟶ X)
    (m : (free R).obj (yoneda.obj X) ⟶ G) : DictPf.ev ((free R).map (yoneda.map f) ≫ m) = Sec.res f (DictPf.ev m) := by
  rw [← gen_eq]
  change (m.hom.app (op Y)).hom ((((free R).map (yoneda.map f)).hom.app (op Y)).hom (freeGen R (yoneda.obj Y) Y (𝟙 Y))) = _
  rw [freeGen_map]
  congr 2

theorem LeafPair_of : DictPf.LeafPair := by
  intro R _ G X U
  refine ⟨fun s s' hs => ?_, fun m m' h1 h2 => ?_⟩
  · have w : (free R).map (yoneda.map U.ι) ≫ ofSec G s = (free R).map (yoneda.map U.ι) ≫ ofSec G s' := by
      apply ext_gen
      rw [ev_pre, ev_pre, ev_ofSec, ev_ofSec]; exact hs
    refine ⟨(PreservesPushout.iso (free R) (yoneda.map U.ι) (yoneda.map U.ι)).inv ≫ pushout.desc _ _ w, ?_, ?_⟩
    · rw [← Category.assoc, PreservesPushout.inl_iso_inv, pushout.inl_desc, ev_ofSec]
    · rw [← Category.assoc, PreservesPushout.inr_iso_inv, pushout.inr_desc, ev_ofSec]
  · apply (cancel_epi (PreservesPushout.iso (free R) (yoneda.map U.ι) (yoneda.map U.ι)).hom).1
    apply pushout.hom_ext
    · rw [← Category.assoc, ← Category.assoc, PreservesPushout.inl_iso_hom]; exact h1
    · rw [← Category.assoc, ← Category.assoc, PreservesPushout.inr_iso_hom]; exact h2

end LateralTheory.CohomologicalPurity.LeafPairPf
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl.Flq

theorem etale_section_boundary_of_mem_addSubgroup_closure {R : Type} [CommRing R] (K : Cx R) {Y : Scheme.{0}} (U' : Y.Opens) (n : ℤ)
    (a : Sec (K.X n) Y) (ha : a ∈ AddSubgroup.closure {a | Bd K U' n a}) : Bd K U' n a := by
  induction ha using AddSubgroup.closure_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, map_zero _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb0, hb⟩ := hx
    obtain ⟨c, hc0, hc⟩ := hy
    refine ⟨b + c, ?_, ?_⟩
    · show ((K.X (n-1)).obj.map U'.ι.op).hom (b + c) = 0
      rw [map_add, show ((K.X (n-1)).obj.map U'.ι.op).hom b = 0 from hb0, show ((K.X (n-1)).obj.map U'.ι.op).hom c = 0 from hc0, add_zero]
    · show ((K.d (n - 1) n).hom.app (op Y)).hom (b + c) = x + y
      rw [map_add]; rw [← hb, ← hc]
  | neg x _ hx =>
    obtain ⟨b, hb0, hb⟩ := hx
    refine ⟨-b, ?_, ?_⟩
    · show ((K.X (n-1)).obj.map U'.ι.op).hom (-b) = 0
      rw [map_neg]; rw [show ((K.X (n-1)).obj.map U'.ι.op).hom b = 0 from hb0, neg_zero]
    · show ((K.d (n - 1) n).hom.app (op Y)).hom (-b) = -x
      rw [map_neg]; rw [← hb]

theorem LeafBdAdd_of : LeafBdAdd := by
  intro R _ K X U n W a ha
  exact etale_section_boundary_of_mem_addSubgroup_closure K _ n a ha

end LateralTheory.CohomologicalPurity.Cl.Flq
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl.Flq

theorem LeafBZ_of : LeafBZ := by
  intro R _ K X U n W a ⟨b, hb0, hba⟩
  subst hba
  refine ⟨?_, ?_⟩
  · show ((K.X n).obj.map (W.ι ⁻¹ᵁ U).ι.op).hom (((K.d (n - 1) n).hom.app (op W.toScheme)).hom b) = 0
    have e := congrArg (fun φ => φ.hom b) ((K.d (n - 1) n).hom.naturality (W.ι ⁻¹ᵁ U).ι.op)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    rw [← e]
    have hb0' : ((K.X (n - 1)).obj.map (W.ι ⁻¹ᵁ U).ι.op).hom b = 0 := hb0
    rw [hb0', map_zero]
  · show ((K.d n (n + 1)).hom.app (op W.toScheme)).hom (((K.d (n - 1) n).hom.app (op W.toScheme)).hom b) = 0
    change ((K.d (n - 1) n ≫ K.d n (n + 1)).hom.app (op W.toScheme)).hom b = 0
    rw [K.d_comp_d]
    rfl

end LateralTheory.CohomologicalPurity.Cl.Flq
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Cl.Flq

theorem sec_eq_zero_of_isZero {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} (hG : IsZero G) (a : Sec G X) :
    a = 0 := by
  have h1 : Sec.map (𝟙 G) a = a := rfl
  have h2 : Sec.map (0 : G ⟶ G) a = 0 := rfl
  rw [← h1, hG.eq_of_src (𝟙 G) 0, h2]

theorem LeafZero_of : LeafZero := by
  intro R _ K X U n hz
  refine ⟨?_, ?_, ?_⟩
  · intro V W h a _
    rw [sec_eq_zero_of_isZero hz (rs h a)]
    exact zero_mem _
  · intro W a _
    rw [sec_eq_zero_of_isZero hz a]
    exact zero_mem _
  · intro V W h a _
    exact ⟨0, zero_mem _, (sec_eq_zero_of_isZero hz _).trans (sec_eq_zero_of_isZero hz a).symm⟩

end LateralTheory.CohomologicalPurity.Cl.Flq
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl.Flq

theorem etale_sheaf_sections_restrict_restrict_eq_restrict_comp {R : Type} [CommRing R] {F : Shv R} {Y Z W : Scheme.{0}} (f : Y ⟶ Z) (g : Z ⟶ W) (a : Sec F W) :
    Sec.res f (Sec.res g a) = Sec.res (f ≫ g) a := by
  show (F.obj.map f.op).hom ((F.obj.map g.op).hom a) = (F.obj.map (f ≫ g).op).hom a
  rw [op_comp, Functor.map_comp]; rfl

theorem etale_sheaf_sections_restriction_of_zero_eq_zero {R : Type} [CommRing R] {F : Shv R} {Y Z : Scheme.{0}} (f : Y ⟶ Z) :
    Sec.res f (0 : Sec F Z) = 0 := by
  show (F.obj.map f.op).hom 0 = 0
  exact map_zero _

theorem etale_sheaf_sections_map_restrict_comm {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {Y Z : Scheme.{0}} (f : Y ⟶ Z) (a : Sec F Z) :
    Sec.map φ (Sec.res f a) = Sec.res f (Sec.map φ a) := by
  show (φ.hom.app (op Y)).hom ((F.obj.map f.op).hom a) = (G.obj.map f.op).hom ((φ.hom.app (op Z)).hom a)
  have h := φ.hom.naturality f.op
  exact congrArg (fun ψ => ψ.hom a) h

theorem LeafTop_of : LeafTop := by
  intro R _ K X U n c' hc'
  obtain ⟨h1, h2⟩ := (mem_Zc c').1 hc'
  refine ⟨Sec.res X.topIso.inv c', (mem_Zc _).2 ⟨?_, ?_⟩, ?_⟩
  · have : IsIso (⊤ : X.Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
    have e : U.ι ≫ X.topIso.inv = inv ((⊤ : X.Opens).ι ∣_ U) ≫ ((⊤ : X.Opens).ι ⁻¹ᵁ U).ι := by
      rw [← cancel_mono X.topIso.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
        Scheme.topIso_hom, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    rw [etale_sheaf_sections_restrict_restrict_eq_restrict_comp, e, ← etale_sheaf_sections_restrict_restrict_eq_restrict_comp, h1, etale_sheaf_sections_restriction_of_zero_eq_zero]
  · rw [etale_sheaf_sections_map_restrict_comm, h2, etale_sheaf_sections_restriction_of_zero_eq_zero]
  · intro V
    rw [etale_sheaf_sections_restrict_restrict_eq_restrict_comp]
    congr 1
    rw [← cancel_mono X.topIso.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, Scheme.topIso_hom,
      Scheme.homOfLE_ι]

end LateralTheory.CohomologicalPurity.Cl.Flq
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.NbPf

variable {A B : Type} [CommRing A] [CommRing B]

def psi (φ : A →+* B) (I : Ideal A) (hb : Function.Bijective (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) :
    B →+* A ⧸ I :=
  (RingEquiv.ofBijective _ hb).symm.toRingHom.comp (Ideal.Quotient.mk (I.map φ))

theorem psi_comp (φ : A →+* B) (I : Ideal A) (hb) : (psi φ I hb).comp φ = Ideal.Quotient.mk I := by
  ext a
  simp only [psi, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [RingEquiv.symm_apply_eq]
  simp [RingEquiv.ofBijective_apply, Ideal.quotientMap_mk]

theorem isPushout_psi (φ : A →+* B) (I : Ideal A) (hb) :
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (psi φ I hb)) (𝟙 (CommRingCat.of (A ⧸ I))) := by
  refine ⟨⟨by ext a; simpa using congrArg (fun f => f a) (psi_comp φ I hb)⟩, ⟨PushoutCocone.IsColimit.mk _
    (fun s => s.inr) ?_ ?_ ?_⟩⟩
  · intro s
    have hk : I.map φ ≤ RingHom.ker s.inl.hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro i hi
      have := congrArg (fun f => f.hom i) s.condition
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
      simp [RingHom.mem_ker, this, Ideal.Quotient.eq_zero_iff_mem.mpr hi]
    ext b
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (psi φ I hb b)
    have e1 : Ideal.Quotient.mk (I.map φ) (φ a) = Ideal.Quotient.mk (I.map φ) b := by
      have : (RingEquiv.ofBijective _ hb) (psi φ I hb b) = Ideal.Quotient.mk (I.map φ) b := by
        simp [psi]
      rw [← this, ← ha]; simp [RingEquiv.ofBijective_apply, Ideal.quotientMap_mk]
    rw [Ideal.Quotient.eq] at e1
    have e2 : s.inl.hom (φ a) = s.inl.hom b := by
      have := hk e1; rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this; exact this
    have e3 := congrArg (fun f => f.hom a) s.condition
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at e3
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, ← ha]
    rw [← e2, e3]
  · intro s; simp
  · intro s m _ h2; simpa using h2

theorem nb (hE : LeafExc) : Cl.LeafNb := by
  intro hA1 q A B _ _ φ I J hN hJ h
  subst hJ
  obtain ⟨he, hb⟩ := hN
  have : Etale (Spec.map (CommRingCat.ofHom φ)) := HasRingHomProperty.Spec_iff.mpr he
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hP := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_psi φ I hb)
  rw [Spec.map_id] at hP
  refine hE hA1 q (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom (psi φ I hb)))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) hP (off B (I.map φ)) (off A I) ?_ (Cl.off_map φ I)
  change (PrimeSpectrum.zeroLocus (I : Set A))ᶜ = _
  congr 1
  have hr := range_comap_of_surjective _ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker] at hr
  rw [← hr]; rfl

end LateralTheory.CohomologicalPurity.NbPf
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.Cl

theorem van_preimage {d : ℕ} (P : SP d) (V : P.X.affineOpens) :
    off Γ(P.X, V.1) (P.ι.ker.ideal V) = V.2.fromSpec ⁻¹ᵁ P.U := by
  have := P.cl
  have hsupp : (P.ι.ker.support : Set P.X) = Set.range P.ι := by
    rw [Scheme.Hom.support_ker, P.ι.isClosedEmbedding.isClosed_range.closure_eq]
  ext y
  have hmem : V.2.fromSpec y ∈ V.1 := by
    rw [← SetLike.mem_coe, ← V.2.range_fromSpec]; exact Set.mem_range_self y
  have h1 := Set.ext_iff.mp (V.2.fromSpec_preimage_zeroLocus ((P.ι.ker.ideal V : Ideal Γ(P.X, V.1)) : Set Γ(P.X, V.1))) y
  have h2 := Scheme.IdealSheafData.mem_support_iff_of_mem (I := P.ι.ker) hmem
  have h3 : V.2.fromSpec y ∈ (P.U : Set P.X) ↔ V.2.fromSpec y ∉ Set.range P.ι := by rw [P.hU]; rfl
  have h4 : V.2.fromSpec y ∈ P.ι.ker.support ↔ V.2.fromSpec y ∈ Set.range P.ι := by
    rw [← SetLike.mem_coe, hsupp]
  exact (not_congr (h1.symm.trans (h2.symm.trans h4))).trans h3.symm

theorem LeafVan_of (hC : LeafChart) (hR : LeafVanRing) : LeafVan := by
  intro hH d q _ P hq i x W hxW
  obtain ⟨V, hxV, hVW, -, hch⟩ := hC d P x W hxW
  have hqV : IsUnit (q : Γ(P.X, V.1)) := by
    have := hq.map (P.X.presheaf.map (homOfLE le_top : V.1 ⟶ ⊤).op).hom
    simpa using this
  refine ⟨⟨Spec (CommRingCat.of Γ(P.X, V.1)), V.2.fromSpec, V.2.isOpenImmersion_fromSpec, off Γ(P.X, V.1) (P.ι.ker.ideal V),
    van_preimage P V⟩, ?_, ?_, ?_⟩
  · rw [V.2.range_fromSpec]; exact hxV
  · rw [V.2.range_fromSpec]; exact hVW
  · intro n hn
    exact hR hH d q Γ(P.X, V.1) _ hch hqV n i hn

end LateralTheory.CohomologicalPurity.Cl
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.Cl

theorem range_frame_ι {d : ℕ} {P : SP d} (F : Frame P) :
    ((off F.B F.I : (Spec (CommRingCat.of F.B)).Opens) : Set (Spec (CommRingCat.of F.B))) =
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk F.I))))ᶜ := by
  have h := range_comap_of_surjective (f := Ideal.Quotient.mk F.I) (hf :=
    Ideal.Quotient.mk_surjective)
  rw [Ideal.mk_ker] at h
  change (PrimeSpectrum.zeroLocus (F.I : Set F.B))ᶜ = _
  rw [← h]
  rfl

def Frame.sp {d : ℕ} {P : SP d} (F : Frame P) (hw : Etale F.w) : SP d where
  X := Spec (CommRingCat.of F.B)
  Z := Spec (CommRingCat.of (F.B ⧸ F.I))
  S := P.S
  p := F.w ≫ P.p
  ι := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk F.I))
  e := P.e
  U := off F.B F.I
  cl := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  smX := by
    have := P.smX
    have : SmoothOfRelativeDimension 0 F.w := inferInstance
    simpa using (inferInstance : SmoothOfRelativeDimension (0 + (P.e + d)) (F.w ≫ P.p))
  smZ := by
    have hz : Etale F.z := MorphismProperty.of_isPullback F.cart hw
    have := P.smZ
    have : SmoothOfRelativeDimension 0 F.z := inferInstance
    have e : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk F.I)) ≫ F.w ≫ P.p = F.z ≫ P.ι ≫ P.p := by
      rw [← Category.assoc, F.cart.w, Category.assoc]
    rw [e]
    simpa using (inferInstance : SmoothOfRelativeDimension (0 + P.e) (F.z ≫ P.ι ≫ P.p))
  hU := range_frame_ι F

theorem LeafVanF_of (hV : LeafVan) : LeafVanF := by
  intro hH d q _ P hq F hw i
  refine hV hH d q (F.sp hw) ?_ i
  have h := hq.map F.w.appTop.hom
  rw [map_natCast] at h
  exact h

end LateralTheory.CohomologicalPurity.Cl
end
end

section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.CohomologicalPurity.Cl

theorem LeafOff_of : LeafOff := by
  intro d P F
  apply le_antisymm F.h
  intro y hy
  change y ∉ PrimeSpectrum.zeroLocus (F.I : Set F.B)
  intro hz
  have hk : RingHom.ker (Ideal.Quotient.mk F.I) = F.I := Ideal.mk_ker
  have hr : y ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk F.I)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, hk]; exact hz
  obtain ⟨y0, rfl⟩ := hr
  have hw := congrArg (fun g => g.base y0) F.cart.w
  simp only [Scheme.Hom.comp_base] at hw
  have hU : F.w.base ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk F.I))).base y0) ∈ (P.U : Set P.X) := hy
  rw [P.hU] at hU
  exact hU ⟨F.z.base y0, hw.symm⟩

end LateralTheory.CohomologicalPurity.Cl
end

section
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.CohomologicalPurity.Cl

theorem LeafCmpNb_pf : LeafCmpNb := by
  intro X B B₀ _ _ w w₀ h₀ y hy
  let W : (Spec (CommRingCat.of B)).Opens := w ⁻¹ᵁ w₀.opensRange
  have hs : IsOpen (X := PrimeSpectrum B) (W : Set (Spec (CommRingCat.of B))) := W.2
  have hyW : (y : PrimeSpectrum B) ∈ (W : Set (Spec (CommRingCat.of B))) := hy
  obtain ⟨_, ⟨g, rfl⟩, hyg, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := B)).exists_subset_of_mem_open hyW hs
  let l : B →+* Localization.Away g := algebraMap B (Localization.Away g)
  have hr : Set.range (PrimeSpectrum.comap l) = PrimeSpectrum.basicOpen g :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away g) g
  have H : Set.range (Spec.map (CommRingCat.ofHom l) ≫ w) ⊆ Set.range w₀ := by
    rintro _ ⟨t, rfl⟩
    have : (Spec.map (CommRingCat.ofHom l)) t ∈ W :=
      hsub (by
        have h1 : PrimeSpectrum.comap l t ∈ Set.range (PrimeSpectrum.comap l) := ⟨t, rfl⟩
        rw [hr] at h1; exact h1)
    exact this
  let u := IsOpenImmersion.lift w₀ _ H
  refine ⟨Localization.Away g, inferInstance, l, (Spec.preimage u).hom, ?_, ?_, ?_⟩
  · exact Scheme.isOpenImmersion_SpecMap_localizationAway (R := CommRingCat.of B) g
  · have h2 : (y : PrimeSpectrum B) ∈ Set.range (PrimeSpectrum.comap l) := by rw [hr]; exact hyg
    obtain ⟨t, ht⟩ := h2
    exact ⟨show Spec (CommRingCat.of (Localization.Away g)) from t, ht⟩
  · rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    exact (IsOpenImmersion.lift_fac w₀ _ H).symm


end LateralTheory.CohomologicalPurity.Cl
end
end

section
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.CohomologicalPurity.Cl

theorem le_map_of {d : ℕ} {P : SP d} (F F₀ : Frame P) (C : Type) [CommRing C] (φ : F.B →+* C) (ψ : F₀.B →+* C)
    (e : Spec.map (CommRingCat.ofHom φ) ≫ F.w = Spec.map (CommRingCat.ofHom ψ) ≫ F₀.w) : F.I.map φ ≤ F₀.I.map ψ := by
  let J := F₀.I.map ψ
  let π : C →+* C ⧸ J := Ideal.Quotient.mk J
  let ψ' : F₀.B ⧸ F₀.I →+* C ⧸ J := Ideal.Quotient.lift F₀.I (π.comp ψ)
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem ψ ha))
  have hψ : ψ'.comp (Ideal.Quotient.mk F₀.I) = π.comp ψ := RingHom.ext fun a => rfl
  have hw : (Spec.map (CommRingCat.ofHom π) ≫ Spec.map (CommRingCat.ofHom φ)) ≫ F.w =
      (Spec.map (CommRingCat.ofHom ψ') ≫ F₀.z) ≫ P.ι := by
    rw [Category.assoc, e, Category.assoc, ← F₀.cart.w, ← Category.assoc, ← Category.assoc,
      ← spec_comp_ofHom, ← spec_comp_ofHom, hψ]
  let t := F.cart.lift _ _ hw
  have ht : t ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk F.I)) =
      Spec.map (CommRingCat.ofHom π) ≫ Spec.map (CommRingCat.ofHom φ) := F.cart.lift_fst _ _ _
  let τ : F.B ⧸ F.I →+* C ⧸ J := (Spec.preimage t).hom
  have h1 : Spec.map (CommRingCat.ofHom (τ.comp (Ideal.Quotient.mk F.I))) =
      Spec.map (CommRingCat.ofHom (π.comp φ)) := by
    rw [spec_comp_ofHom, spec_comp_ofHom, ← ht]
    congr 1
    exact Spec.map_preimage t
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
  change (π.comp φ) a = 0
  rw [← show (τ.comp (Ideal.Quotient.mk F.I)) = π.comp φ from h2, RingHom.comp_apply,
    Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]

theorem LeafCmpId_pf : LeafCmpId := fun _ _ F F₀ C _ φ ψ e =>
  le_antisymm (le_map_of F F₀ C φ ψ e) (le_map_of F₀ F C ψ φ e.symm)

end LateralTheory.CohomologicalPurity.Cl
end
end

section
namespace LateralTheory.CohomologicalPurity.Cl

theorem LeafCmp_of_Mat (hMat : LeafMat) : LeafCmp := LeafCmp_of hMat LeafCmpNb_pf LeafCmpId_pf

end LateralTheory.CohomologicalPurity.Cl
end

section
theorem LateralTheory.Fix.LeafCl.intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafCl := by
  have h54 : LateralTheory.CohomologicalPurity.LeafThom := LateralTheory.Fin.LeafThom.intersectionNumber_baseChange
  have h80 : LateralTheory.CohomologicalPurity.LeafChart := LateralTheory.Fin.LeafChart.intersectionNumber_baseChange
  have h89 : LateralTheory.CohomologicalPurity.LeafExc := LateralTheory.Fin.LeafExc.intersectionNumber_baseChange
  have h55 : LateralTheory.CohomologicalPurity.Cl.LeafDisc := LateralTheory.CohomologicalPurity.Cl.LeafDisc_of'
  have h56 : LateralTheory.CohomologicalPurity.DictPf.LeafEv := LateralTheory.CohomologicalPurity.DictPf.LeafEv_of
  have h57 : LateralTheory.CohomologicalPurity.DictPf.LeafPair := LateralTheory.CohomologicalPurity.LeafPairPf.LeafPair_of
  have h58 : LateralTheory.CohomologicalPurity.Cl.LeafDict := LateralTheory.CohomologicalPurity.DictPf.LeafDict_of' h55 h56 h57
  have h59 : LateralTheory.CohomologicalPurity.Cl.LeafZorn := LateralTheory.CohomologicalPurity.ZornPf.LeafZorn_of
  have h60 : LateralTheory.CohomologicalPurity.Cl.Flq.LeafBdAdd := LateralTheory.CohomologicalPurity.Cl.Flq.LeafBdAdd_of
  have h61 : LateralTheory.CohomologicalPurity.Cl.Flq.LeafBZ := LateralTheory.CohomologicalPurity.Cl.Flq.LeafBZ_of
  have h62 : LateralTheory.CohomologicalPurity.Cl.Flq.LeafZloc := LateralTheory.CohomologicalPurity.ZlocPf.LeafZloc_of
  have h63 : LateralTheory.CohomologicalPurity.Cl.Flq.LeafZero := LateralTheory.CohomologicalPurity.Cl.Flq.LeafZero_of
  have h64 : LateralTheory.CohomologicalPurity.Cl.Flq.LeafStep := LateralTheory.CohomologicalPurity.Cl.Flq.StepPf.LeafStep_of
  have h65 : LateralTheory.CohomologicalPurity.Cl.Flq.LeafTop := LateralTheory.CohomologicalPurity.Cl.Flq.LeafTop_of
  have h66 : LateralTheory.CohomologicalPurity.Cl.LeafFlq := LateralTheory.CohomologicalPurity.Cl.Flq.LeafFlq_of h59 h60 h61 h62 h63 h64 h65
  have h67 : LateralTheory.CohomologicalPurity.Cl.LeafDescOSep := LateralTheory.CohomologicalPurity.Cl.LeafDescOSep_of
  have h68 : LateralTheory.CohomologicalPurity.Cl.LeafDescOGlue := LateralTheory.CohomologicalPurity.Cl.LeafDescOGlue_of
  have h69 : LateralTheory.CohomologicalPurity.Cl.LeafDesc := LateralTheory.CohomologicalPurity.Cl.LeafDesc_of' h58 h66 h67 h68
  have h90 : LateralTheory.CohomologicalPurity.Cl.LeafNb := LateralTheory.CohomologicalPurity.NbPf.nb h89
  have h91 : LateralTheory.CohomologicalPurity.Cl.LeafVanRing := LateralTheory.CohomologicalPurity.Cl.LeafVanRing_of h90 h54
  have h92 : LateralTheory.CohomologicalPurity.Cl.LeafVan := LateralTheory.CohomologicalPurity.Cl.LeafVan_of h80 h91
  have h93 : LateralTheory.CohomologicalPurity.Cl.LeafVanF := LateralTheory.CohomologicalPurity.Cl.LeafVanF_of h92
  have h94 : LateralTheory.CohomologicalPurity.Cl.LeafOff := LateralTheory.CohomologicalPurity.Cl.LeafOff_of
  have h95 : LateralTheory.CohomologicalPurity.Cl.LeafGenRing := LateralTheory.CohomologicalPurity.Cl.LeafGenRing_of
  have h96 : LateralTheory.CohomologicalPurity.Cl.LeafGenKer := LateralTheory.CohomologicalPurity.Cl.LeafGenKer_of
  have h97 : LateralTheory.CohomologicalPurity.Cl.LeafGen := LateralTheory.CohomologicalPurity.Cl.LeafGen_of h80 h95 h96
  have h98 : LateralTheory.CohomologicalPurity.Cl.LeafMat := LateralTheory.CohomologicalPurity.Cl.LeafMat_of
  have h99 : LateralTheory.CohomologicalPurity.Cl.LeafCmp := LateralTheory.CohomologicalPurity.Cl.LeafCmp_of_Mat h98
  exact LateralTheory.CohomologicalPurity.Cl.goal_of h54 h69 h92 h93 h94 h97 h99
end
