module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InjectiveOfApplyEqGenericPoint
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace PositivityTheory.HtPt.Ml

theorem preimm_frac {O F : Type} [CommRing O] [Field F] (β : O →+* F)
    (h : letI := β.toAlgebra; IsFractionRing O F) : IsPreimmersion (spMap β) := by
  letI := β.toAlgebra
  haveI := h
  exact IsPreimmersion.of_isLocalization (nonZeroDivisors O)

theorem lift_frac {O F : Type} [CommRing O] [Field F] (β : O →+* F)
    (h : letI := β.toAlgebra; IsFractionRing O F) {X : Scheme.{0}} (s : X ⟶ Sp O) {K : Type} [Field K]
    (x : Sp K ⟶ X) (hx : Set.range x ⊆ Set.range (pullback.fst s (spMap β))) :
    ∃ y : Sp K ⟶ pullback s (spMap β), y ≫ pullback.fst _ _ = x := by
  haveI : IsPreimmersion (spMap β) := preimm_frac β h
  obtain ⟨⟨p, a⟩, rfl⟩ := (X.SpecToEquivOfField K).symm.surjective x
  have hp : p ∈ Set.range (pullback.fst s (spMap β)) := by
    apply hx
    exact ⟨IsLocalRing.closedPoint K, Scheme.fromSpecResidueField_apply p _⟩
  obtain ⟨q, rfl⟩ := hp
  have hsurj : Function.Surjective (Scheme.Hom.residueFieldMap (pullback.fst s (spMap β)) q) := by
    have h1 : Function.Surjective
        (Scheme.Hom.stalkMap (pullback.fst s (spMap β)) q ≫ (pullback s (spMap β)).residue q) :=
      ((pullback s (spMap β)).residue_surjective q).comp
        (Scheme.Hom.stalkMap_surjective (pullback.fst s (spMap β)) q)
    rw [← Scheme.residue_residueFieldMap] at h1
    intro b
    obtain ⟨c, hc⟩ := h1 b
    exact ⟨X.residue _ c, hc⟩
  haveI : IsIso (Scheme.Hom.residueFieldMap (pullback.fst s (spMap β)) q) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨(Scheme.Hom.residueFieldMap (pullback.fst s (spMap β)) q).hom.injective, hsurj⟩
  refine ⟨Spec.map (inv (Scheme.Hom.residueFieldMap (pullback.fst s (spMap β)) q) ≫ a) ≫
    (pullback s (spMap β)).fromSpecResidueField q, ?_⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
    ← Spec.map_comp]
  simp [Scheme.SpecToEquivOfField]

theorem lift_generic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), (letI := β.toAlgebra; IsFractionRing O c.F) → ∀ (K : Type) [Field K] (x : Sp K ⟶ Y.X), Set.range x ⊆ Set.range Y.j → ∃ y : Sp K ⟶ Xo.XF c, y ≫ Y.j = x := by
  intro E _ _ _ H D l Xo c O _ β Y h K _ x hx
  haveI : IsPreimmersion (spMap β) := preimm_frac β h
  haveI := Y.jQ_open
  have hx' : Set.range x ⊆ Set.range (pullback.fst Y.s (spMap β)) := by
    refine hx.trans ?_
    rintro _ ⟨w, rfl⟩
    exact ⟨Y.jQ w, by simp [Model.j]⟩
  obtain ⟨y1, hy1⟩ := lift_frac β h Y.s x hx'
  have hr : Set.range y1 ⊆ Set.range Y.jQ := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := hx ⟨z, rfl⟩
    refine ⟨w, (pullback.fst Y.s (spMap β)).isEmbedding.injective ?_⟩
    rw [← hy1] at hw
    simpa [Model.j] using hw
  refine ⟨IsOpenImmersion.lift Y.jQ y1 hr, ?_⟩
  simp [Model.j, hy1]

end PositivityTheory.HtPt.Ml
