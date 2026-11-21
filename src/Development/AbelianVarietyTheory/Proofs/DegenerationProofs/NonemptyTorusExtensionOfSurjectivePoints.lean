import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusQuotientNoCocharacter
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMonHomFactorOfFlatSurjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import BuildAid.ForwardExisting

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem splitTorus_hom_eq_one_of_no_cocharacter :
    ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
      [Module.Finite ℤ X], (∀ f : Gm S ⟶ B, IsMonHom f → f = 1) →
      ∀ u : splitTorus S X ⟶ B, IsMonHom u → u = 1 := by
  intro S B _ X _ _ _ h u hu
  classical
  let b := Module.Free.chooseBasis ℤ X
  let l : _ → (X →+ ULift.{0} ℤ) := fun i =>
    (AddEquiv.ulift : ULift.{0} ℤ ≃+ ℤ).symm.toAddMonoidHom.comp (b.coord i).toAddMonoidHom
  let c : _ → (ULift.{0} ℤ →+ X) := fun i => SplitTorus.uliftMultiples X (b i)
  have h1 : ∀ i, SplitTorus.torusMap S ((c i).comp (l i)) ≫ u = 1 := fun i => by
    have e : SplitTorus.torusMap S (l i) ≫ u = 1 := h _ (inferInstanceAs
      (IsMonHom (SplitTorus.torusMap S (l i) ≫ u)))
    rw [SplitTorus.torusMap_comp, Category.assoc, e, MonObj.comp_one]
  have h2 : ∀ s : Finset (Module.Free.ChooseBasisIndex ℤ X),
      SplitTorus.torusMap S (∑ i ∈ s, (c i).comp (l i)) ≫ u = 1 := fun s => by
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, SplitTorus.torusMap_zero, MonObj.one_comp]
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, SplitTorus.torusMap_add, MonObj.mul_comp, h1, ih, _root_.mul_one]
  have h3 : (∑ i, (c i).comp (l i)) = AddMonoidHom.id X := by
    ext x
    rw [AddMonoidHom.finset_sum_apply]
    exact b.sum_repr x
  have := h2 Finset.univ
  rwa [h3, SplitTorus.torusMap_id, Category.id_comp] at this

end GlobalTheory.SS
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitTorus_hom_eq_one_of_no_cocharacter' : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X], (∀ f : Gm S ⟶ B, IsMonHom f → f = 1) → ∀ u : splitTorus S X ⟶ B, IsMonHom u → u = 1 := by
  atlas_forward_decl GlobalTheory.SS.splitTorus_hom_eq_one_of_no_cocharacter
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem nonempty_torusExtension_of_surjective_points : ∀ (k : Type) [Field k] [IsAlgClosed k] (G G₁ : Over (Sp k)) [GrpObj G] [GrpObj G₁], SmConn G₁ → Nonempty (TorusExtension G) → ∀ r : G ⟶ G₁, IsMonHom r → (∀ y : (𝟙_ (Over (Sp k)) ⟶ G₁), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ≫ r = y) → Nonempty (TorusExtension G₁) := by
  intro k _ _ G G₁ _ _ hG₁ ⟨E⟩ r hr hsurj
  obtain ⟨X, _, _, _, B₁, _, i₁, q₁, ⟨hi, hq, hfl, hsu, haf, hker, hc, hsm, hsep, hqc, hgc⟩, hno⟩ :=
    MaxTorus.exists_quot_no_cocharacter k G₁ hG₁
  let _ := E.addCommGroup
  let _ := E.free
  let _ := E.finite
  let _ := E.grpB
  have := E.i_hom
  have := E.q_hom
  have hkill : E.i ≫ r ≫ q₁ = 1 := GlobalTheory.T.splitTorus_hom_eq_one_of_no_cocharacter' _ B₁ E.X hno _ inferInstance
  obtain ⟨⟨ψ, -, hψ⟩, -⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective _ G E.B B₁ E.q (r ≫ q₁)
    E.q_hom inferInstance E.q_flat E.q_surjective E.q_quasiCompact (fun T x hx => by
      have h := E.isKernel.lift_fst x (toUnit T) hx
      rw [← h, Category.assoc, hkill, MonObj.comp_one])
  have := E.isAbelian.proper
  have : UniversallyClosed (ψ.left ≫ B₁.hom) := by rw [Over.w]; infer_instance
  have : UniversallyClosed ψ.left := .of_comp_of_isSeparated _ B₁.hom
  have := hG₁.2.1
  have : JacobsonSpace G₁.left := LocallyOfFiniteType.jacobsonSpace G₁.hom
  have hZ : IsClosed (q₁.left ⁻¹' Set.range ψ.left) :=
    ψ.left.isClosedMap.isClosed_range.preimage q₁.left.continuous
  let pt : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k
  have hsub : closedPoints G₁.left ⊆ q₁.left ⁻¹' Set.range ψ.left := by
    intro y hy
    obtain ⟨x, hx⟩ := hsurj (Over.homMk (pointOfClosedPoint (K := k) G₁.hom y hy)
      (pointOfClosedPoint_comp (K := k) G₁.hom y hy))
    have hy' : r.left (x.left pt) = y := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hx]
      exact pointOfClosedPoint_apply (K := k) G₁.hom y hy pt
    refine ⟨E.q.left (x.left pt), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hψ, Over.comp_left, Scheme.Hom.comp_apply, hy']
  have hall := closure_minimal hsub hZ
  rw [closure_closedPoints] at hall
  have : Surjective ψ.left := ⟨fun b => by
    obtain ⟨g, rfl⟩ := q₁.left.surjective b
    exact hall (Set.mem_univ g)⟩
  have : UniversallyClosed B₁.hom := .of_comp_surjective ψ.left _
  have : IsProper B₁.hom := {}
  exact ⟨{ X := X, B := B₁, isAbelian := ⟨hc, hsm, this, hgc⟩, q := q₁, q_hom := hq, q_flat := hfl,
           q_surjective := hsu, q_quasiCompact := inferInstance, i := i₁, i_hom := hi,
           isKernel := hker }⟩

end GlobalTheory.SS
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_torusExtension_of_surjective_points' : ∀ (k : Type) [Field k] [IsAlgClosed k] (G G₁ : Over (Sp k)) [GrpObj G] [GrpObj G₁], SmConn G₁ → Nonempty (TorusExtension G) → ∀ r : G ⟶ G₁, IsMonHom r → (∀ y : (𝟙_ (Over (Sp k)) ⟶ G₁), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ≫ r = y) → Nonempty (TorusExtension G₁) := by
  atlas_forward_decl GlobalTheory.SS.nonempty_torusExtension_of_surjective_points
end
