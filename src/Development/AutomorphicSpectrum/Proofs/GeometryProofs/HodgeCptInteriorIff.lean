import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.SubfieldClosureEqTopOfEpi
import BuildAid.ForwardExisting
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.ExtendsToFractionField
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.GermVanishesOfGenericVanishing

section
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ggeo

theorem epi_subfield_closure_range_eq_top : ∀ (O F : Type) [CommRing O] [Field F] (β : O →+* F),
    (∀ (T : Type) [CommRing T] (g₁ g₂ : F →+* T), g₁.comp β = g₂.comp β → g₁ = g₂) →
    Subfield.closure (Set.range β) = ⊤ :=
  PositivityTheory.UnitarySelfGeneration.subfield_closure_eq_top_of_epi

end GlobalTheory.CompanionTheory.Ggeo
end

open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.epi_ring_hom_field_closure : ∀ (O F : Type) [CommRing O] [Field F] (β : O →+* F), (∀ (T : Type) [CommRing T] (g₁ g₂ : F →+* T), g₁.comp β = g₂.comp β → g₁ = g₂) → Subfield.closure (Set.range β) = ⊤ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ggeo.epi_subfield_closure_range_eq_top
end

section
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ggeo

theorem extend_to_fraction_field_relay : ∀ (O F L : Type) [CommRing O] [Field F] [CommRing L] (β : O →+* F) (θ : O →+* L), Subfield.closure (Set.range β) = ⊤ → (∀ b, β b ≠ 0 → IsUnit (θ b)) → (∀ a, β a = 0 → θ a = 0) → ∃ χ : F →+* L, χ.comp β = θ :=
  PositivityTheory.UnitarySelfGeneration.extends_to_fraction_field

end GlobalTheory.CompanionTheory.Ggeo
end

open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extend_to_fraction_field : ∀ (O F L : Type) [CommRing O] [Field F] [CommRing L] (β : O →+* F) (θ : O →+* L), Subfield.closure (Set.range β) = ⊤ → (∀ b, β b ≠ 0 → IsUnit (θ b)) → (∀ a, β a = 0 → θ a = 0) → ∃ χ : F →+* L, χ.comp β = θ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ggeo.extend_to_fraction_field_relay
end

section
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ggeo

private theorem map_aeval_int' {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : A)
    (q : Polynomial ℤ) : f (Polynomial.aeval a q) = Polynomial.aeval (f a) q := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂,
    RingHom.ext_int (f.comp (algebraMap ℤ A)) (algebraMap ℤ B)]

theorem unit_of_local_hom_charZero_nf : ∀ (O F L K : Type) [CommRing O] [Field F] [NumberField F] [CommRing L] [Field K] [CharZero K] (β : O →+* F) (θ : O →+* L) (ρ : L →+* K), IsLocalHom ρ → (∀ a, β a = 0 → θ a = 0) → ∀ b, β b ≠ 0 → IsUnit (θ b) := by
  intro O F L K _ _ _ _ _ _ β θ ρ hρ hker b hb
  have halg : IsAlgebraic ℤ (β b) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic (β b))
  obtain ⟨q, hq0, hq⟩ :=
    halg.exists_nonzero_coeff_and_aeval_eq_zero (mem_nonZeroDivisors_of_ne_zero hb)
  have h1 : β (Polynomial.aeval b q) = 0 := by rw [map_aeval_int', hq]
  have h2 : ρ (θ (Polynomial.aeval b q)) = 0 := by rw [hker _ h1, map_zero]
  rw [map_aeval_int', map_aeval_int'] at h2
  have h3 : ρ (θ b) ≠ 0 := by
    intro h0
    rw [h0, ← Polynomial.coeff_zero_eq_aeval_zero'] at h2
    exact hq0 (by simpa using h2)
  exact hρ.map_nonunit _ (isUnit_iff_ne_zero.mpr h3)

end GlobalTheory.CompanionTheory.Ggeo
end

open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_hom_char_zero_units : ∀ (O F L K : Type) [CommRing O] [Field F] [NumberField F] [CommRing L] [Field K] [CharZero K] (β : O →+* F) (θ : O →+* L) (ρ : L →+* K), IsLocalHom ρ → (∀ a, β a = 0 → θ a = 0) → ∀ b, β b ≠ 0 → IsUnit (θ b) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ggeo.unit_of_local_hom_charZero_nf
end

section
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ggeo

theorem germ_vanish_of_generic_dominated : ∀ (X : Scheme.{0}) [IsReduced X] (Ω O : Type) [Field Ω] [CommRing O] (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ q : X, ξ (IsLocalRing.closedPoint Ω) ⤳ q) → ∀ (s₀ : X ⟶ Spec (CommRingCat.of O)) (gm : O →+* Ω), ξ ≫ s₀ = Spec.map (CommRingCat.ofHom gm) → ∀ (x : X) (a : O), gm a = 0 → (Spec.preimage (X.fromSpecStalk x ≫ s₀)).hom a = 0 :=
  PositivityTheory.UnitarySelfGeneration.germ_vanishes_of_generic_vanishing

end GlobalTheory.CompanionTheory.Ggeo
end

open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_vanishing_stalk_vanishing : ∀ (X : Scheme.{0}) [IsReduced X] (Ω O : Type) [Field Ω] [CommRing O] (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ q : X, ξ (IsLocalRing.closedPoint Ω) ⤳ q) → ∀ (s₀ : X ⟶ Spec (CommRingCat.of O)) (gm : O →+* Ω), ξ ≫ s₀ = Spec.map (CommRingCat.ofHom gm) → ∀ (x : X) (a : O), gm a = 0 → (Spec.preimage (X.fromSpecStalk x ≫ s₀)).hom a = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ggeo.germ_vanish_of_generic_dominated
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.IntOpen

theorem epi_of_mono_spMap {O F : Type} [CommRing O] [CommRing F] (β : O →+* F) (h : Mono (spMap β))
    {T : Type} [CommRing T] (g₁ g₂ : F →+* T) (e : g₁.comp β = g₂.comp β) : g₁ = g₂ := by
  have h1 : spMap g₁ ≫ spMap β = spMap g₂ ≫ spMap β := by
    rw [← spMap_comp, ← spMap_comp, e]
  have h2 := Spec.map_injective ((cancel_mono (spMap β)).1 h1)
  exact congrArg CommRingCat.Hom.hom h2

theorem lift_local {R : CommRingCat} [IsLocalRing R] {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
    (g : Spec R ⟶ X) (h : g (IsLocalRing.closedPoint R) ∈ Set.range j) : ∃ u, u ≫ j = g := by
  have hr : Set.range g ⊆ Set.range j := by
    rintro _ ⟨p, rfl⟩
    have hs : p ⤳ IsLocalRing.closedPoint R := IsLocalRing.specializes_closedPoint p
    exact (hs.map g.continuous).mem_open j.isOpenEmbedding.isOpen_range h
  exact ⟨IsOpenImmersion.lift j g hr, IsOpenImmersion.lift_fac _ _ _⟩

theorem interior_iff_factor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (z : Sp ℂ ⟶ A.X), Mono (spMap β) → Mono Y.j ∧ (A.Interior z ↔ ∃ u : Spec (A.X.presheaf.stalk (centre z)) ⟶ Xo.XF c, u ≫ Y.j = A.X.fromSpecStalk (centre z) ≫ A.f) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J y A z hβ
  have hab : ∀ x : A.X, A.f x ∈ abLocus Y.t.G ↔ x ∈ abLocus A.t.G :=
    abLocus_pullback abLocusOne Y.t.semi A.m.cart.1
  refine ⟨?_, ?_⟩
  · have : IsOpenImmersion Y.jQ := Y.jQ_open
    unfold Model.j; infer_instance
  constructor
  · intro hx
    have hx' : A.f (centre z) ∈ abLocus Y.t.G := (hab _).2 hx
    haveI : FiniteDimensional ℚ c.F := c.fin
    haveI : NumberField c.F := {}
    haveI : IsReduced A.X := by
      have : ∀ x : A.X, _root_.IsReduced (A.X.presheaf.stalk x) := fun x => by
        have := (A.normal x).1
        infer_instance
      exact isReduced_of_isReduced_stalk A.X
    let g : Spec (A.X.presheaf.stalk (centre z)) ⟶ Sp O := A.X.fromSpecStalk (centre z) ≫ A.f ≫ Y.s
    let θ : O →+* A.X.presheaf.stalk (centre z) := (Spec.preimage g).hom
    have hk : ∀ a, β a = 0 → θ a = 0 := fun a ha =>
      GlobalTheory.T.generic_vanishing_stalk_vanishing A.X Ω O A.ξ A.all (A.f ≫ Y.s) (A.cst.comp β) A.cst_over (centre z) a (by simp [ha])
    have hu : ∀ b, β b ≠ 0 → IsUnit (θ b) := fun b hb =>
      GlobalTheory.T.local_hom_char_zero_units O c.F _ ℂ β θ (Scheme.stalkClosedPointTo z).hom (Scheme.isLocalHom_stalkClosedPointTo' z) hk b hb
    obtain ⟨χ, hχ⟩ := GlobalTheory.T.extend_to_fraction_field O c.F _ β θ (GlobalTheory.T.epi_ring_hom_field_closure O c.F β (fun T _ g₁ g₂ e => epi_of_mono_spMap β hβ g₁ g₂ e)) hu hk
    have w : (A.X.fromSpecStalk (centre z) ≫ A.f) ≫ Y.s = spMap χ ≫ spMap β := by
      rw [← spMap_comp, hχ, Category.assoc]
      change g = _
      rw [← Spec.map_preimage g]
      rfl
    haveI : IsOpenImmersion Y.jQ := Y.jQ_open
    obtain ⟨u, hu⟩ := lift_local Y.jQ (pullback.lift _ _ w) (by
      rw [← Y.ab_gen]
      show (pullback.lift _ _ w ≫ pullback.fst _ _) _ ∈ abLocus _
      rw [pullback.lift_fst]
      have e1 : (A.X.fromSpecStalk (centre z) ≫ A.f) (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z))) = A.f (centre z) := by
        show A.f ((A.X.fromSpecStalk (centre z)) (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) = _
        rw [Scheme.fromSpecStalk_closedPoint]
      exact e1 ▸ hx')
    refine ⟨u, ?_⟩
    rw [Model.j, ← Category.assoc, hu, pullback.lift_fst]
  · rintro ⟨u, hu⟩
    show centre z ∈ abLocus A.t.G
    rw [← hab]
    have h1 : A.f (centre z) = Y.j (u (IsLocalRing.closedPoint _)) := by
      have e1 := congrArg (fun φ : Spec (A.X.presheaf.stalk (centre z)) ⟶ Y.X => φ (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) hu
      change Y.j (u (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) = A.f ((A.X.fromSpecStalk (centre z)) (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) at e1
      rw [Scheme.fromSpecStalk_closedPoint] at e1
      exact e1.symm
    rw [h1]
    have h2 : Y.jQ (u (IsLocalRing.closedPoint _)) ∈ Set.range Y.jQ := ⟨_, rfl⟩
    rw [← Y.ab_gen] at h2
    exact h2

end GlobalTheory.CompanionTheory.Ar.IntOpen
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_cpt_interior_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (z : Sp ℂ ⟶ A.X), Mono (spMap β) → Mono Y.j ∧ (A.Interior z ↔ ∃ u : Spec (A.X.presheaf.stalk (centre z)) ⟶ Xo.XF c, u ≫ Y.j = A.X.fromSpecStalk (centre z) ≫ A.f) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.IntOpen.interior_iff_factor
end
