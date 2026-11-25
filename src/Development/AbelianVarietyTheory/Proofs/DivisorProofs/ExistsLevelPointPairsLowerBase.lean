module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQkZeroOver

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

theorem spMap_comp_tf {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (f : R →+* V) {F₀ F : Type}
    [Field F₀] [Algebra (FractionRing R) F₀] [Field F] [Algebra (FractionRing V) F] (j : F₀ →+* F) (hj : Ext f j) :
    spMap j ≫ (TF (R := R) F₀).hom = (TF (R := V) F).hom ≫ spMap f := by
  simp only [TF, jFK, jK, spMap, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  exact hj r

theorem tr_base {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {f : R →+* V} {D₀ : DegPre R}
    {D : DegPre V} {hD : IsPullDeg f D₀ D} {F₀ F : Type} [Field F₀] [Algebra (FractionRing R) F₀] [Field F]
    [Algebra (FractionRing V) F] {j : F₀ →+* F} (hj : Ext f j) {g₀ : GtPtF D₀ F₀} {g : GtPtF D F}
    (h : Tr f hD j g₀ g) {X : Scheme.{0}} (m : D₀.P.A.left ⟶ X) (k : Sp R ⟶ X)
    (hg₀ : g₀.b.left ≫ m = (TF (R := R) F₀).hom ≫ k) :
    g.b.left ≫ (hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf f)) ≫ m = (TF (R := V) F).hom ≫ spMap f ≫ k := by
  obtain ⟨g₁, ⟨hb, -⟩, hp⟩ := h
  rw [← Category.assoc, hp.1, hb, Category.assoc, hg₀, ← Category.assoc, spMap_comp_tf f j hj, Category.assoc]

end GlobalTheory.TInj
