module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapFromSpecStalk
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtFractionNoetherianClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermStalkClosedPointToBaseChange
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateLatticeLeOmegaStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompatStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsBaseChangeGroupStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalBaseChangeStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsHodgeTateFunctionalStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalUniqueStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChangeStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeMapStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueEquivStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.QuasiFiniteGroupFiniteStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongOrderDividesStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongBaseChangeStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongGroupPullbackStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongUniqueUpToIsoStatement
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.HeightPullbackDominatingMap

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HTPull

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (c : A →+* B) (d : B →+* C) :
    (dualMap d).comp (dualMap c) = dualMap (d.comp c) := by
  ext r <;> simp [dualMap]

theorem lieBC {S : Scheme.{0}} {G : Over S} [GrpObj G] {A B : Type} [CommRing A] [CommRing B] (c : A →+* B)
    (x : Sp A ⟶ S) (y : Sp B ⟶ S) (hy : y = Spec.map (CommRingCat.ofHom c) ≫ x) (hsm : Smooth G.hom)
    {E E' : Type} [AddCommGroup E] [Module A E] [AddCommGroup E'] [Module B E']
    (M : LieModel G x E) (M' : LieModel G y E') :
    ∃ j : E →+ E', (∀ e, (M'.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap c)) ≫ (M.pt e).left) ∧
      (∀ (a : A) e, j (a • e) = c a • j e) ∧ Submodule.span B (Set.range j) = ⊤ ∧
      ∀ l : Module.Dual A E, ∃ l' : Module.Dual B E', ∀ e, l' (j e) = c (l e) := by
  subst hy
  letI : Algebra A B := c.toAlgebra
  letI : Module A E' := Module.compHom E' c
  haveI : IsScalarTower A B E' := ⟨fun a b e => by
    show (c a * b) • e = c a • b • e
    rw [mul_smul]⟩
  haveI : Smooth G.hom := hsm
  obtain ⟨j, h1, h2, -⟩ := GlobalTheory.T.lie_model_base_change_map S G A B x E E' M M'
  let β : E →ₗ[A] E' := { toFun := j, map_add' := map_add j, map_smul' := fun a e => h2 a e }
  have hbc : IsBaseChange B β := (GlobalTheory.T.lie_model_finite_base_change S G A x E M).2.2 B E' M' β h1
  refine ⟨j, h1, h2, ?_, ?_⟩
  · refine eq_top_iff.2 fun e _ => ?_
    refine hbc.inductionOn e ?_ ?_ ?_
    · exact fun m => Submodule.subset_span ⟨m, rfl⟩
    · exact fun s n h => Submodule.smul_mem _ s h
    · exact fun a b ha hb => Submodule.add_mem _ ha hb
  · intro l
    refine ⟨hbc.lift ((Algebra.linearMap A B).comp l), fun e => ?_⟩
    exact hbc.lift_eq _ e

section Setup

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R']
  {X X' : Scheme.{0}} {x : Sp R ⟶ X} {x' : Sp R' ⟶ X'} {f : X' ⟶ X}
  {G : Over X} {G' : Over X'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left}
  {Ω Ω' : Type} [Field Ω] [Field Ω'] {k : R →+* Ω} {k' : R' →+* Ω'} {i : Ω →+* Ω'}
  {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'} {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V']
  {M : LieModel G ξ V} {M' : LieModel G' ξ' V'} {j : V →+ V'}

end Setup

section Back

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R']
  {X X' : Scheme.{0}} {x : Sp R ⟶ X} {x' : Sp R' ⟶ X'} {f : X' ⟶ X}
  {G : Over X} {G' : Over X'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left}
  {Ω Ω' : Type} [Field Ω] [Field Ω'] {k : R →+* Ω} {k' : R' →+* Ω'} {i : Ω →+* Ω'}
  {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'} {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V']
  {M : LieModel G ξ V} {M' : LieModel G' ξ' V'} {j : V →+ V'}

end Back

end GlobalTheory.CompanionTheory.Ar.HTPull

theorem GlobalTheory.CompanionTheory.Ar.HTPull.main : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (G : Over X) (G' : Over X') [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left) (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (M : LieModel G ξ V) (M' : LieModel G' ξ' V') (j : V →+ V'), IsCptGen ξ → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsGrpPullback G' G f φ → Smooth G.hom → (∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left) → ∀ (jd : Module.Dual Ω V →+ Module.Dual Ω' V'), (∀ w e, jd w (j e) = i (w e)) → ∀ (N : ℕ), 0 < N → ∀ (p' : Cpt ξ') (h : genPt ξ ⤳ f p'.1), IsIntegrallyClosed (X.presheaf.stalk (f p'.1)) → IsNoetherianRing (X.presheaf.stalk (f p'.1)) → (∃ ζ : Ω, IsPrimitiveRoot ζ N) → M.IsHTFormAt N ⟨f p'.1, h⟩ 0 → M'.htLat N p' = (M.htLat N).pull ξ' f jd p' :=
  GlobalTheory.CompanionTheory.Ar.HTPullK.main
