import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsValuationSubringComplexComapValEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentGeometricallyIrreducible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelChangeMap

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_geometrically_irreducible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l), FnAlgClosed Xo c → ∀ Z : Comp Xo c,
    ∃ U : (Xo.XF c).Opens, (U : Set (Xo.XF c)) = Z ∧ ∀ (k : Type) [Field k] (f : c.F →+* k),
      IrreducibleSpace ↑(pullback (U.ι ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (spMap f)) := by
  first | exact @GlobalTheory.GeomIrrComp.exists_open_irreducibleSpace_baseChange | exact GlobalTheory.GeomIrrComp.exists_open_irreducibleSpace_baseChange | (intros; apply GlobalTheory.GeomIrrComp.exists_open_irreducibleSpace_baseChange <;> assumption)
end

section
namespace GlobalTheory

theorem clopen_image_irreducibleComponent : ∀ {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (f : A → B), Continuous f → IsOpenMap f → IsClosedMap f →
    (∀ C ∈ irreducibleComponents A, IsOpen C) → ∀ S : Set B, IsClopen S → IsPreconnected S → ∀ a : A, f a ∈ S →
    ∃ C ∈ irreducibleComponents A, a ∈ C ∧ f '' C = S := by
  intro A B _ _ f hf hop hcl hcomp S hS hSc a ha
  refine ⟨irreducibleComponent a, irreducibleComponent_mem_irreducibleComponents a,
    mem_irreducibleComponent, ?_⟩
  have hCc : IsClosed (irreducibleComponent a) := isClosed_irreducibleComponent
  have hCo : IsOpen (irreducibleComponent a) :=
    hcomp _ (irreducibleComponent_mem_irreducibleComponents a)
  have hCp : IsPreconnected (irreducibleComponent a) :=
    (IsIrreducible.isConnected (isIrreducible_irreducibleComponent (x := a))).isPreconnected
  have hsub : irreducibleComponent a ⊆ f ⁻¹' S :=
    hCp.subset_isClopen (hS.preimage hf) ⟨a, mem_irreducibleComponent, ha⟩
  have himg : f '' irreducibleComponent a ⊆ S := Set.image_subset_iff.mpr hsub
  have hclo : IsClopen (f '' irreducibleComponent a) := ⟨hcl _ hCc, hop _ hCo⟩
  refine le_antisymm himg ?_
  exact hSc.subset_isClopen hclo ⟨f a, ha, a, mem_irreducibleComponent, rfl⟩

end GlobalTheory

alias _root_.GlobalTheory.T.exists_component_surjects_clopen := _root_.GlobalTheory.clopen_image_irreducibleComponent
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory

theorem exists_lift_of_range_subset_of_isAlgClosed :
    ∀ {X Y : AlgebraicGeometry.Scheme.{0}} (f : X ⟶ Y) [AlgebraicGeometry.LocallyOfFiniteType f]
      (k : Type) [Field k] [IsAlgClosed k]
      (y : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ Y), Set.range y ⊆ Set.range f →
      ∃ x : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ X, x ≫ f = y := by
  intro X Y f _ k _ _ y hr
  obtain ⟨x₀, hx₀⟩ := hr ⟨IsLocalRing.closedPoint k, rfl⟩
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := y) x₀
    (IsLocalRing.closedPoint k) hx₀
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd f y)
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints (X := (Limits.pullback f y : Scheme))
    (Z := Set.univ) ⟨z, trivial⟩ isClosed_univ.isLocallyClosed
  have hc' : IsClosed {c} := hc
  refine ⟨pointOfClosedPoint (pullback.snd f y) c hc' ≫ pullback.fst f y, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp,
    Category.id_comp]

end GlobalTheory

alias _root_.GlobalTheory.T.exists_lift_algebraically_closed_point := _root_.GlobalTheory.exists_lift_of_range_subset_of_isAlgClosed
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FlatModel

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace GlobalTheory.FlatModel

theorem exists_comp_cover_lift : (∀ {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (f : A → B), Continuous f → IsOpenMap f → IsClosedMap f →
    (∀ C ∈ irreducibleComponents A, IsOpen C) → ∀ S : Set B, IsClopen S → IsPreconnected S → ∀ a : A, f a ∈ S →
    ∃ C ∈ irreducibleComponents A, a ∈ C ∧ f '' C = S) → (∀ {X Y : AlgebraicGeometry.Scheme.{0}} (f : X ⟶ Y) [AlgebraicGeometry.LocallyOfFiniteType f] (k : Type) [Field k] [IsAlgClosed k]
    (y : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ Y), Set.range y ⊆ Set.range f →
    ∃ x : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ X, x ≫ f = y) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (hle : c.F ≤ c'.F),
    (∀ Z : Comp Xo c, ∃ U : (Xo.XF c).Opens, (U : Set (Xo.XF c)) = Z ∧ ∀ (k : Type) [Field k] (f : c.F →+* k),
      IrreducibleSpace ↑(pullback (U.ι ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (spMap f))) →
    (∀ Z : Comp Xo' c', ∃ U : (Xo'.XF c').Opens, (U : Set (Xo'.XF c')) = Z ∧ ∀ (k : Type) [Field k] (f : c'.F →+* k),
      IrreducibleSpace ↑(pullback (U.ι ≫ pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom)) (spMap f))) →
    ∀ (r : Xo'.XF c' ⟶ Xo.XF c)
      (h : r ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) =
        pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom) ≫ spMap (IntermediateField.inclusion hle).toRingHom),
      IsFinite (pullback.lift r _ h) → Etale (pullback.lift r _ h) → Surjective (pullback.lift r _ h) →
    ∀ Z : Comp Xo c, ∃ U : (Xo'.XF c').Opens, (∀ z ∈ U, r z ∈ (Z : Set (Xo.XF c))) ∧
      (∀ (k : Type) [Field k] (f : c'.F →+* k),
        IrreducibleSpace ↑(pullback (U.ι ≫ pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom)) (spMap f))) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (fK : c'.F →+* k) (x : Sp k ⟶ Xo.XF c),
        x ≫ pullback.snd _ _ = spMap (fK.comp (IntermediateField.inclusion hle).toRingHom) →
        Set.range x ⊆ (Z : Set (Xo.XF c)) →
        ∃ yy : Sp k ⟶ Xo'.XF c', yy ≫ pullback.snd _ _ = spMap fK ∧ yy ≫ r = x ∧ Set.range yy ⊆ (U : Set (Xo'.XF c')) := by
  intro hTop hPt E _ _ _ H Dw l l' Xo Xo' c c' hle hIrr hIrr' r h hfin het hsurj Z
  set sF := pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) with hsF
  set g := spMap (IntermediateField.inclusion hle).toRingHom with hg
  set r' := pullback.lift r _ h with hr'
  obtain ⟨U₀, hU₀, hU₀irr⟩ := hIrr Z

  have hirrB : IrreducibleSpace ↑(pullback (U₀.ι ≫ sF) g) := hU₀irr c'.F (IntermediateField.inclusion hle).toRingHom
  have hZc_eq : Set.range (pullback.snd U₀.ι (pullback.fst sF g)) = pullback.fst sF g ⁻¹' (Z : Set (Xo.XF c)) := by
    rw [IsOpenImmersion.range_pullbackSnd]
    ext w
    simp only [Scheme.Hom.coe_preimage, Set.mem_preimage, SetLike.mem_coe, Scheme.Hom.coe_opensRange, Scheme.Opens.range_ι, hU₀]
  have hZc_irr : IsIrreducible (pullback.fst sF g ⁻¹' (Z : Set (Xo.XF c))) := by
    have hr : Set.range ((pullbackRightPullbackFstIso sF g U₀.ι).inv ≫ pullback.snd U₀.ι (pullback.fst sF g)) =
        Set.range (pullback.snd U₀.ι (pullback.fst sF g)) := by
      rw [show ⇑((pullbackRightPullbackFstIso sF g U₀.ι).inv ≫ pullback.snd U₀.ι (pullback.fst sF g)) =
          ⇑(pullback.snd U₀.ι (pullback.fst sF g)) ∘ ⇑(pullbackRightPullbackFstIso sF g U₀.ι).inv from rfl, Set.range_comp, ((pullbackRightPullbackFstIso sF g U₀.ι).inv).surjective.range_eq,
        Set.image_univ]
    rw [← hZc_eq, ← hr, ← Set.image_univ]
    exact IrreducibleSpace.isIrreducible_univ _ |>.image _
      ((pullbackRightPullbackFstIso sF g U₀.ι).inv ≫ pullback.snd U₀.ι (pullback.fst sF g)).continuous.continuousOn
  have hZclosed : IsClosed (Z : Set (Xo.XF c)) := isClosed_of_mem_irreducibleComponents _ Z.2
  have hZopen : IsOpen (Z : Set (Xo.XF c)) := by rw [← hU₀]; exact U₀.2
  have hZc_clopen : IsClopen (pullback.fst sF g ⁻¹' (Z : Set (Xo.XF c))) :=
    ⟨hZclosed.preimage (pullback.fst sF g).continuous, hZopen.preimage (pullback.fst sF g).continuous⟩
  have hr'open : IsOpenMap r' := r'.isOpenMap
  have hr'closed : IsClosedMap r' := r'.isClosedMap
  have hcompOpen : ∀ C ∈ irreducibleComponents (Xo'.XF c'), IsOpen C := by
    intro C hC
    obtain ⟨U, hU, -⟩ := hIrr' ⟨C, hC⟩
    rw [show C = (U : Set _) from hU.symm]; exact U.2
  obtain ⟨z, hz⟩ := (Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).nonempty
  obtain ⟨b, hb⟩ := (pullback.fst sF g).surjective z
  obtain ⟨a, ha⟩ := r'.surjective b
  have haZ : r' a ∈ pullback.fst sF g ⁻¹' (Z : Set (Xo.XF c)) := by
    simp only [Set.mem_preimage]; rw [ha, hb]; exact hz
  obtain ⟨C, hC, haC, hCim⟩ := hTop r' r'.continuous hr'open hr'closed hcompOpen _ hZc_clopen
    (IsIrreducible.isConnected hZc_irr).isPreconnected a haZ
  obtain ⟨U, hU, hUirr⟩ := hIrr' ⟨C, hC⟩
  have hUC : (U : Set (Xo'.XF c')) = C := hU
  have hr'fst : r' ≫ pullback.fst sF g = r := pullback.lift_fst _ _ _
  have hr'snd : r' ≫ pullback.snd sF g = pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom) :=
    pullback.lift_snd _ _ _
  refine ⟨U, ?_, hUirr, ?_⟩
  · intro w hw
    have hw' : r' w ∈ pullback.fst sF g ⁻¹' (Z : Set (Xo.XF c)) := by
      rw [← hCim]; exact ⟨w, hUC ▸ hw, rfl⟩
    have : r w = pullback.fst sF g (r' w) := by rw [← hr'fst]; rfl
    rw [this]; exact hw'
  · intro k _ _ fK x hx hxZ
    have hcomm : x ≫ sF = spMap fK ≫ g := by
      rw [hx, hg]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    set x' := pullback.lift x (spMap fK) hcomm with hx'
    have hx'fst : x' ≫ pullback.fst sF g = x := pullback.lift_fst _ _ _
    have hx'snd : x' ≫ pullback.snd sF g = spMap fK := pullback.lift_snd _ _ _
    have hrange : Set.range x' ⊆ Set.range (U.ι ≫ r') := by
      rintro _ ⟨q, rfl⟩
      have hq : x' q ∈ pullback.fst sF g ⁻¹' (Z : Set (Xo.XF c)) := by
        simp only [Set.mem_preimage]
        have : pullback.fst sF g (x' q) = x q := by rw [← hx'fst]; rfl
        rw [this]; exact hxZ ⟨q, rfl⟩
      rw [← hCim] at hq
      obtain ⟨w, hwC, hw⟩ := hq
      have hwU : w ∈ Set.range U.ι := by rw [Scheme.Opens.range_ι, hUC]; exact hwC
      obtain ⟨u, rfl⟩ := hwU
      exact ⟨u, by rw [← hw]; rfl⟩
    obtain ⟨yy₀, hyy₀⟩ := hPt (U.ι ≫ r') k x' hrange
    refine ⟨yy₀ ≫ U.ι, ?_, ?_, ?_⟩
    · rw [← hr'snd, ← hx'snd, ← hyy₀]; simp only [Category.assoc]
    · rw [← hr'fst, ← hx'fst, ← hyy₀]; simp only [Category.assoc]
    · rintro _ ⟨q, rfl⟩
      rw [← Scheme.Opens.range_ι U]
      exact ⟨yy₀ q, rfl⟩

end GlobalTheory.FlatModel
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_surjects_of_open_closed : (∀ {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (f : A → B), Continuous f → IsOpenMap f → IsClosedMap f →
    (∀ C ∈ irreducibleComponents A, IsOpen C) → ∀ S : Set B, IsClopen S → IsPreconnected S → ∀ a : A, f a ∈ S →
    ∃ C ∈ irreducibleComponents A, a ∈ C ∧ f '' C = S) → (∀ {X Y : AlgebraicGeometry.Scheme.{0}} (f : X ⟶ Y) [AlgebraicGeometry.LocallyOfFiniteType f] (k : Type) [Field k] [IsAlgClosed k]
    (y : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ Y), Set.range y ⊆ Set.range f →
    ∃ x : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ X, x ≫ f = y) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (hle : c.F ≤ c'.F),
    (∀ Z : Comp Xo c, ∃ U : (Xo.XF c).Opens, (U : Set (Xo.XF c)) = Z ∧ ∀ (k : Type) [Field k] (f : c.F →+* k),
      IrreducibleSpace ↑(pullback (U.ι ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (spMap f))) →
    (∀ Z : Comp Xo' c', ∃ U : (Xo'.XF c').Opens, (U : Set (Xo'.XF c')) = Z ∧ ∀ (k : Type) [Field k] (f : c'.F →+* k),
      IrreducibleSpace ↑(pullback (U.ι ≫ pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom)) (spMap f))) →
    ∀ (r : Xo'.XF c' ⟶ Xo.XF c)
      (h : r ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) =
        pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom) ≫ spMap (IntermediateField.inclusion hle).toRingHom),
      IsFinite (pullback.lift r _ h) → Etale (pullback.lift r _ h) → Surjective (pullback.lift r _ h) →
    ∀ Z : Comp Xo c, ∃ U : (Xo'.XF c').Opens, (∀ z ∈ U, r z ∈ (Z : Set (Xo.XF c))) ∧
      (∀ (k : Type) [Field k] (f : c'.F →+* k),
        IrreducibleSpace ↑(pullback (U.ι ≫ pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom)) (spMap f))) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (fK : c'.F →+* k) (x : Sp k ⟶ Xo.XF c),
        x ≫ pullback.snd _ _ = spMap (fK.comp (IntermediateField.inclusion hle).toRingHom) →
        Set.range x ⊆ (Z : Set (Xo.XF c)) →
        ∃ yy : Sp k ⟶ Xo'.XF c', yy ≫ pullback.snd _ _ = spMap fK ∧ yy ≫ r = x ∧ Set.range yy ⊆ (U : Set (Xo'.XF c')) := by
  atlas_forward_decl GlobalTheory.FlatModel.exists_comp_cover_lift
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FlatModel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatModel.ModelOpen

theorem exists_geomIrr_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype)
    (p : ℕ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ U : (Xo'.XF c').Opens,
    (∀ (k : Type) [Field k] (f : c'.F →+* k),
      IrreducibleSpace ↑(pullback (U.ι ≫ pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom)) (spMap f))) →
    ∃ Xw : Y.X.Opens, (Xw : Set Y.X) ⊆ Set.range Y.j ∧ Xw ≤ Y.X.basicOpen (p : Γ(Y.X, ⊤)) ∧
      (∀ z, Y.j z ∈ Xw ↔ z ∈ U) ∧ GeomIrr Y.s Xw := by
  intro E _ _ _ H Dw l' Xo' c' W Y p hp hW U hU
  have hj : IsOpenImmersion Y.j := GlobalTheory.LocM.BaseMdl.isOpenImmersion_j hp hW Y
  have := c'.fin
  have hV : (p : c'.F) ∈ (c'.V W).nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
    refine Or.inr fun h => hW.elim (Nat.cast_ne_zero.2 hp.ne_zero) fun h' => h' ?_
    have h2 : c'.F.val.toRingHom (p : c'.F)⁻¹ ∈ W := h
    simpa using h2
  have := GlobalTheory.LocM.BaseMdl.away_of_valuation c'.F (c'.V W) p hp hV
  have hβ : IsOpenImmersion (spMap (c'.V W).subtype) :=
    IsOpenImmersion.of_isLocalization (S := c'.F) ((p : ℕ) : c'.V W)
  refine ⟨Y.j ''ᵁ U, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  · rintro _ ⟨z, -, rfl⟩
    have hF : IsUnit (p : Γ(Sp c'.F, ⊤)) := by
      have h0 : IsUnit (p : c'.F) := IsUnit.mk0 _ (Nat.cast_ne_zero.2 hp.ne_zero)
      have h1 := h0.map (Scheme.ΓSpecIso (CommRingCat.of c'.F)).inv.hom
      rw [map_natCast] at h1
      exact h1
    have hunit : IsUnit (p : Γ(Xo'.XF c', ⊤)) := by
      have h1 := hF.map (Scheme.Hom.appTop (pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom))).hom
      rw [map_natCast] at h1
      exact h1
    have hz : z ∈ Y.j ⁻¹ᵁ Y.X.basicOpen (p : Γ(Y.X, ⊤)) := by
      rw [Scheme.preimage_basicOpen, map_natCast]
      exact (Scheme.basicOpen_of_isUnit _ hunit).ge trivial
    exact hz
  · intro z
    constructor
    · rintro ⟨z', hz', e⟩
      rwa [← Y.j.isOpenEmbedding.injective e]
    · intro hz
      exact ⟨z, hz, rfl⟩
  · intro k _ f hf
    let β := (c'.V W).subtype
    let f' : c'.F →+* k := IsFractionRing.lift hf
    have hff : f'.comp β = f := by
      ext x
      exact IsFractionRing.lift_algebraMap hf x
    let a := U.ι ≫ pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom)
    have := hU k f'
    let e := Y.j.isoImage U
    have h1 : a ≫ spMap β = e.hom ≫ (Y.j ''ᵁ U).ι ≫ Y.s := by
      rw [Scheme.Hom.isoImage_hom_ι_assoc, GlobalTheory.LocM.BaseMdl.j_s]
      exact Category.assoc _ _ _
    have h2 : spMap f' ≫ spMap β = spMap f := by
      rw [← hff]
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    let φ := pullback.map a (spMap f') ((Y.j ''ᵁ U).ι ≫ Y.s) (spMap f) e.hom (𝟙 _) (spMap β) h1
      (by rw [h2, Category.id_comp])
    let ψ : pullback ((Y.j ''ᵁ U).ι ≫ Y.s) (spMap f) ⟶ pullback a (spMap f') :=
      pullback.lift (pullback.fst _ _ ≫ e.inv) (pullback.snd _ _) (by
        rw [← cancel_mono (spMap β)]
        simp only [Category.assoc, h1, Iso.inv_hom_id_assoc, h2]
        exact pullback.condition)
    have hφψ : ψ ≫ φ = 𝟙 _ := by
      apply pullback.hom_ext
      · simp only [φ, ψ, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Iso.inv_hom_id,
          Category.comp_id, Category.id_comp]
      · simp only [φ, ψ, pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
          Category.comp_id, Category.id_comp]
    have hsurj : Function.Surjective φ := fun x => ⟨ψ x, by rw [← Scheme.Hom.comp_apply, hφψ]; rfl⟩
    exact hsurj.irreducibleSpace φ.continuous

end GlobalTheory.FlatModel.ModelOpen
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_component_irreducible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype)
    (p : ℕ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ U : (Xo'.XF c').Opens,
    (∀ (k : Type) [Field k] (f : c'.F →+* k),
      IrreducibleSpace ↑(pullback (U.ι ≫ pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom)) (spMap f))) →
    ∃ Xw : Y.X.Opens, (Xw : Set Y.X) ⊆ Set.range Y.j ∧ Xw ≤ Y.X.basicOpen (p : Γ(Y.X, ⊤)) ∧
      (∀ z, Y.j z ∈ Xw ↔ z ∈ U) ∧ GeomIrr Y.s Xw := by
  atlas_forward_decl GlobalTheory.FlatModel.ModelOpen.exists_geomIrr_open
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_change_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (hle : c.F ≤ c'.F),
    1 ≤ Dw.p + Dw.q → l.Dvd l' →
    ∃ (r : Xo'.XF c' ⟶ Xo.XF c)
      (h : r ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) =
        pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom) ≫ spMap (IntermediateField.inclusion hle).toRingHom)
      (r₀ : Xo'.X ⟶ Xo.X) (_ : SABMap Xo'.univ.t Xo.univ.t r₀),
      r ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r₀ ∧ IsFinite (pullback.lift r _ h) ∧ Etale (pullback.lift r _ h) ∧
        Surjective (pullback.lift r _ h) := by
  first | exact @GlobalTheory.LevelMapBase.levelMap_coeff_le | exact GlobalTheory.LevelMapBase.levelMap_coeff_le | (intros; apply GlobalTheory.LevelMapBase.levelMap_coeff_le <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem coverSt_holds : CoverSt := by
  intro E _ _ _ H Dw l Xo c hpq hA hgood hfac Z la p n hp hpla
  classical
  let l' : Level H := { l with A := p ^ n, A_pos := pow_pos hp.pos n }
  have hdvd : l.Dvd l' := ⟨dvd_rfl, le_rfl, by rw [hA]; exact one_dvd _⟩
  let fam : ∀ l₀ : Level H, Moduli Dw l₀ := fun l₀ => Classical.choice (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.1 E H Dw l₀ hpq)
  let Xo' := fam l'
  obtain ⟨c₁⟩ : Nonempty (Coeff l') := inferInstance
  let c₀ : Coeff l' :=
    { F := c.F ⊔ c₁.F
      fin := by
        have := c.fin
        have := c₁.fin
        exact IntermediateField.finiteDimensional_sup _ _
      conj := fun τ a => (le_sup_right : c₁.F ≤ c.F ⊔ c₁.F) (c₁.conj τ a)
      zeta_mem := (le_sup_right : c₁.F ≤ c.F ⊔ c₁.F) c₁.zeta_mem
      le := c₁.le.trans le_sup_right }
  obtain ⟨-, c', hc', hall⟩ := GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed E H Dw l' Xo' c₀ hpq
  have hfac' : FnAlgClosed Xo' c' := hall c' le_rfl
  have hle : c.F ≤ c'.F := le_sup_left.trans hc'
  have hpU : (p : c.F) ∈ (la.valuation c.F).valuationSubring.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff]
    have h1 : la.valuation c.F (algebraMap (𝓞 c.F) c.F (p : 𝓞 c.F)) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem la _).2 hpla
    rw [map_natCast] at h1
    exact ((Valuation.isEquiv_valuation_valuationSubring (la.valuation c.F)).lt_one_iff_lt_one).1 h1
  obtain ⟨W, hpW, hWU⟩ := GlobalTheory.exists_valuationSubring_complex_comap_val_eq c.F _ p hpU
  obtain ⟨Ysys, -⟩ := GlobalTheory.T.compactifiedModuli_partOne.2 E H Dw hpq fam
  let Y : Model Xo' c' (c'.V W).subtype := Ysys p W hp hpW ⟨l', c', hgood p hp⟩
  obtain ⟨r, hr, r₀, m, hr₀, hfin, het, hsurj⟩ := GlobalTheory.T.exists_level_change_map E H Dw l l' Xo Xo' c c' hle hpq hdvd
  obtain ⟨ν₀, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m Y.m0.toSABMap
  obtain ⟨U, hUZ, hUirr, hUlift⟩ := GlobalTheory.T.component_surjects_of_open_closed GlobalTheory.T.exists_component_surjects_clopen GlobalTheory.T.exists_lift_algebraically_closed_point E H Dw l l' Xo Xo' c c' hle (GlobalTheory.T.component_geometrically_irreducible E H Dw l Xo c hfac)
    (GlobalTheory.T.component_geometrically_irreducible E H Dw l' Xo' c' hfac') r hr hfin het hsurj Z
  obtain ⟨Xw, hXj, hXp, hXU, hXg⟩ := GlobalTheory.T.integral_model_component_irreducible E H Dw l' Xo' c' W Y p hp hpW U hUirr
  refine ⟨l', Xo', c', W, Y, r, hr₀ ▸ ν₀, hle, Xw, rfl, hr, fun x => ?_, hpW, ?_, hXj, hXp,
    fun z hz => hUZ z ((hXU z).1 hz), hXg, ?_⟩
  · rw [← Valuation.mem_valuationSubring_iff, ← hWU, ValuationSubring.mem_comap]
    rfl
  · have h := hpW
    rw [ValuationSubring.mem_nonunits_iff_or] at h ⊢
    rcases h with h | h
    · exact absurd (by exact_mod_cast h) hp.ne_zero
    · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')
  · intro k _ _ fK x hx hxZ
    obtain ⟨yy, h1, h2, h3⟩ := hUlift k fK x hx hxZ
    refine ⟨yy, h1, h2, ?_⟩
    rintro _ ⟨w, rfl⟩
    exact (hXU _).2 (h3 ⟨w, rfl⟩)

end GlobalTheory.FlatModel

end
end

open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_statement_holds : CoverSt := by
  atlas_forward_decl GlobalTheory.FlatModel.coverSt_holds
end
