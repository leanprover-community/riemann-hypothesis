import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwoModelsCommonCoverCompare
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LieModelTransportIsomorphism
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueEquivStatement

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TwoModels

theorem generic_fibre_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (π' : Z ⟶ Y'.X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ Z) (x x' : Sp Ω ⟶ Xo.XF c), ξ ≫ π = x ≫ Y.j → ξ ≫ π' = x' ≫ Y'.j → x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → ∃ (t t' : SAB H Z) (tΩ : SAB H (Sp Ω)) (a : SABMap t Y.t π) (a' : SABMap t' Y'.t π') (m : SABMap tΩ t ξ) (m' : SABMap (twistSAB tΩ g) t' ξ) (u : SABMap tΩ Y.oF.t x) (u' : SABMap (twistSAB tΩ g) Y'.oF.t x'), m.φ ≫ a.φ = u.φ ≫ Y.m.φ ∧ m'.φ ≫ a'.φ = u'.φ ≫ Y'.m.φ ∧ u'.φ ≫ Y'.m0.toSABMap.φ = (twistMap u g).φ ≫ (twistMap Y.m0.toSABMap g).φ ≫ n.φ :=
  @PositivityTheory.UnitarySelfGeneration.two_models_common_cover_compare

end GlobalTheory.CompanionTheory.Ar.TwoModels
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_models_common_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (π' : Z ⟶ Y'.X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ Z) (x x' : Sp Ω ⟶ Xo.XF c), ξ ≫ π = x ≫ Y.j → ξ ≫ π' = x' ≫ Y'.j → x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → ∃ (t t' : SAB H Z) (tΩ : SAB H (Sp Ω)) (a : SABMap t Y.t π) (a' : SABMap t' Y'.t π') (m : SABMap tΩ t ξ) (m' : SABMap (twistSAB tΩ g) t' ξ) (u : SABMap tΩ Y.oF.t x) (u' : SABMap (twistSAB tΩ g) Y'.oF.t x'), m.φ ≫ a.φ = u.φ ≫ Y.m.φ ∧ m'.φ ≫ a'.φ = u'.φ ≫ Y'.m.φ ∧ u'.φ ≫ Y'.m0.toSABMap.φ = (twistMap u g).φ ≫ (twistMap Y.m0.toSABMap g).φ ≫ n.φ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.TwoModels.generic_fibre_twist
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.IsoMove

theorem lieModel_isoMove : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (e : X' ≅ X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (t : SAB H X) (t' : SAB H X') (m : SABMap t' t e.hom) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V), ξ' ≫ e.hom = ξ → ∃ M' : LieModel t'.G ξ' V, (∀ v, (M'.pt v).left ≫ m.φ = (M.pt v).left) ∧ (∀ n, FullTorsion t.G ξ n → FullTorsion t'.G ξ' n) ∧ (IsCptGen ξ → IsCptGen ξ') ∧ ∀ (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1), regAt ξ' q = regAt ξ ⟨e.hom q.1, h⟩ ∧ (M'.lat q : Set V) = M.lat ⟨e.hom q.1, h⟩ ∧ ∀ n, (M'.htOm t'.PP.L n q : Set (Module.Dual Ω V)) = M.htOm t.PP.L n ⟨e.hom q.1, h⟩ :=
  @PositivityTheory.UnitarySelfGeneration.lie_model_transport_isomorphism

end GlobalTheory.CompanionTheory.Ar.IsoMove
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_iso_transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (e : X' ≅ X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (t : SAB H X) (t' : SAB H X') (m : SABMap t' t e.hom) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V), ξ' ≫ e.hom = ξ → ∃ M' : LieModel t'.G ξ' V, (∀ v, (M'.pt v).left ≫ m.φ = (M.pt v).left) ∧ (∀ n, FullTorsion t.G ξ n → FullTorsion t'.G ξ' n) ∧ (IsCptGen ξ → IsCptGen ξ') ∧ ∀ (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1), regAt ξ' q = regAt ξ ⟨e.hom q.1, h⟩ ∧ (M'.lat q : Set V) = M.lat ⟨e.hom q.1, h⟩ ∧ ∀ n, (M'.htOm t'.PP.L n q : Set (Module.Dual Ω V)) = M.htOm t.PP.L n ⟨e.hom q.1, h⟩ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.IsoMove.lieModel_isoMove
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem GlobalTheory.CompanionTheory.Ar.FrameModelsGeometry.main : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G G' : Over X) [GrpObj G] [GrpObj G'] (GΩ : Over (Sp Ω)) [GrpObj GΩ] (φ : GΩ.left ⟶ G.left) (φ' : GΩ.left ⟶ G'.left), IsGrpPullback GΩ G ξ φ → IsGrpPullback GΩ G' ξ φ' → ∀ (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V), ∃ M' : LieModel G' ξ V, ∀ e, ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ GΩ, v.left ≫ φ = (M.pt e).left ∧ v.left ≫ φ' = (M'.pt e).left := by
  intro X Ω _ ξ G G' _ _ GΩ _ φ φ' h h' V _ _ M
  obtain ⟨M₀, h₀⟩ := (GlobalTheory.CompanionTheory.Ar.LieMove.main Ω X ξ G GΩ φ V h).1 M
  obtain ⟨M', h₁⟩ := (GlobalTheory.CompanionTheory.Ar.LieMove.main Ω X ξ G' GΩ φ' V h').2 M₀
  exact ⟨M', fun e => ⟨M₀.pt e, h₀ e, h₁ e⟩⟩
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_lie_model : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G G' : Over X) [GrpObj G] [GrpObj G'] (GΩ : Over (Sp Ω)) [GrpObj GΩ] (φ : GΩ.left ⟶ G.left) (φ' : GΩ.left ⟶ G'.left), IsGrpPullback GΩ G ξ φ → IsGrpPullback GΩ G' ξ φ' → ∀ (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V), ∃ M' : LieModel G' ξ V, ∀ e, ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ GΩ, v.left ≫ φ = (M.pt e).left ∧ v.left ≫ φ' = (M'.pt e).left := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.FrameModelsGeometry.main
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.FrameRebase

def sabRebase {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f f' : S' ⟶ S} (m : SABMap t' t f) (h : f = f') : SABMap t' t f' :=
  h ▸ m

theorem sabRebase_φ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f f' : S' ⟶ S} (m : SABMap t' t f) (h : f = f') :
    (sabRebase m h).φ = m.φ := by
  subst h; rfl

theorem tied_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F)
    (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y)
    (e : A'.X ≅ A.X) (x x' : Sp Ω ⟶ Xo.XF c),
    Mono (spMap β) → Mono (spMap β') → Φ.hom ≫ Xo.s = Xo.s → A'.ξ ≫ e.hom = A.ξ → A.ξ ≫ A.f = x ≫ Y.j → A'.ξ ≫ A'.f = x' ≫ Y'.j →
    x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → x' ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ →
    A.cst = A'.cst → x ≫ pullback.snd _ _ = spMap A.cst → (∀ p ∈ S, A'.R p = A.R p) →
    ∃ (t : SAB H A'.X) (tΩ : SAB H (Sp Ω)) (k : SABMap t A.t e.hom) (m : SABMap tΩ t A'.ξ)
      (mA : SABMap tΩ A.t A.ξ) (mA' : SABMap (twistSAB tΩ g) A'.t A'.ξ) (u : SABMap tΩ Y.oF.t x)
      (u' : SABMap (twistSAB tΩ g) Y'.oF.t x') (M₁ : LieModel t.G A'.ξ A.Li) (φ : A.Li ≃ₗ[Ω] A'.Li),
      mA.φ = m.φ ≫ k.φ ∧ mA.φ ≫ A.m.φ = u.φ ≫ Y.m.φ ∧ mA'.φ ≫ A'.m.φ = u'.φ ≫ Y'.m.φ ∧
      u'.φ ≫ Y'.m0.toSABMap.φ = u.φ ≫ Y.m0.toSABMap.φ ≫ n.φ ∧
      (∀ v, (M₁.pt v).left ≫ k.φ = (A.M.pt v).left) ∧ (∀ v, ∃ w : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, w.left ≫ m.φ = (M₁.pt v).left ∧ w.left ≫ mA'.φ = (A'.M.pt (φ v)).left) ∧ (∀ N, FullTorsion A.t.G A.ξ N → FullTorsion t.G A'.ξ N) ∧ (∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1), regAt A'.ξ q = regAt A.ξ ⟨e.hom q.1, h⟩ ∧
        (M₁.lat q : Set A.Li) = A.M.lat ⟨e.hom q.1, h⟩ ∧
        ∀ N, (M₁.htOm t.PP.L N q : Set (Module.Dual Ω A.Li)) = A.M.htOm A.t.PP.L N ⟨e.hom q.1, h⟩) := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' Y Y' g Φ n S Ω _ K _ J _ y A A' e x x' _ _ _ h4 h5 h6 h7 _ _ _ _
  have hπ : A'.ξ ≫ (e.hom ≫ A.f) = x ≫ Y.j := by rw [← Category.assoc, h4, h5]
  obtain ⟨t, t', tΩ, a, a', m, m', u, u', E1, E2, E3⟩ :=
    GlobalTheory.T.twist_models_common_point E H D l Xo c O O' β β' Y Y' g Φ n A'.X (e.hom ≫ A.f) A'.f Ω A'.ξ x x' hπ h6 h7
  obtain ⟨k, hk⟩ := sabCancel pullCubCancel E H _ _ _ Y.t A.t t A.f e.hom A.m a
  obtain ⟨k', hk'⟩ := sabCancel pullCubCancel E H _ _ _ Y'.t A'.t t' A'.f (𝟙 _) A'.m
    (sabRebase a' (Category.id_comp A'.f).symm)
  obtain ⟨n₁, hn₁⟩ := sabComp pullCubComp E H _ _ _ A.t t tΩ e.hom A'.ξ k m
  obtain ⟨n₂, hn₂⟩ := sabComp pullCubComp E H _ _ _ A'.t t' (twistSAB tΩ g) (𝟙 _) A'.ξ k' m'
  let mA : SABMap tΩ A.t A.ξ := sabRebase n₁ h4
  let mA' : SABMap (twistSAB tΩ g) A'.t A'.ξ := sabRebase n₂ (Category.comp_id _)
  have hmA : mA.φ = m.φ ≫ k.φ := (sabRebase_φ n₁ h4).trans hn₁
  have hmA' : mA'.φ = m'.φ ≫ k'.φ := (sabRebase_φ n₂ _).trans hn₂
  rw [sabRebase_φ] at hk'
  obtain ⟨M₁, P1, P2, -, P4⟩ := GlobalTheory.T.lie_model_iso_transport E H A.X A'.X e Ω A.ξ A'.ξ A.t t k A.Li A.M h4
  obtain ⟨M₂, Q⟩ := GlobalTheory.T.exists_compatible_lie_model A'.X Ω A'.ξ t.G A'.t.G tΩ.G m.φ mA'.φ m.cart mA'.cart A.Li M₁
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.T.lie_model_existsUnique_equiv A'.X A'.t.G Ω A'.ξ A.Li A'.Li M₂ A'.M
  refine ⟨t, tΩ, k, m, mA, mA', u, u', M₁, φ, hmA, ?_, ?_, E3, P1, ?_, P2, P4⟩
  · rw [hmA, Category.assoc, ← hk, E1]
  · rw [hmA', Category.assoc, ← hk', E2]
  · intro v
    obtain ⟨w, hw1, hw2⟩ := Q v
    exact ⟨w, hw1, by rw [hφ v]; exact hw2⟩

end GlobalTheory.CompanionTheory.Ar.FrameRebase
end
