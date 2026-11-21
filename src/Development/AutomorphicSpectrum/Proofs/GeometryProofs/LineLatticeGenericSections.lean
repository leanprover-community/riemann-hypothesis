import Mathlib
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ValuationCentreExists
import BuildAid.ForwardExisting

section
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_centre_of_isProper : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → ∀ V : ValuationSubring Ω, (∀ o : O, algebraMap O Ω o ∈ V) → ∃ p : Cpt ξ, regAt ξ p ≤ V.toSubring ∧ ∀ a ∈ regAt ξ p, a ≠ 0 → a⁻¹ ∈ V → ∃ g : X.presheaf.stalk p.1, IsUnit g ∧ genMap ξ p g = a :=
  @PositivityTheory.Xgn.valuation_centre_exists

end GlobalTheory.CompanionTheory.Ar.Flat
end

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_centre_regular_unit : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → ∀ V : ValuationSubring Ω, (∀ o : O, algebraMap O Ω o ∈ V) → ∃ p : Cpt ξ, regAt ξ p ≤ V.toSubring ∧ ∀ a ∈ regAt ξ p, a ≠ 0 → a⁻¹ ∈ V → ∃ g : X.presheaf.stalk p.1, IsUnit g ∧ genMap ξ p g = a := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.exists_centre_of_isProper
end

section
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem germ_top_stalk_closed_point {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {q : X}
    (hq : ξ (IsLocalRing.closedPoint Ω) ⤳ q) :
    X.presheaf.germ ⊤ q (show q ∈ (⊤ : X.Opens) from trivial) ≫ X.presheaf.stalkSpecializes hq ≫ Scheme.stalkClosedPointTo ξ
      = ξ.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom := by
  rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.germ_stalkClosedPointTo]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]
  have e : ∀ (f : (⊤ : (Spec (CommRingCat.of Ω)).Opens) ⟶ ξ ⁻¹ᵁ ⊤),
      (Spec (CommRingCat.of Ω)).presheaf.map f.op = 𝟙 _ := fun f => (Spec (CommRingCat.of Ω)).presheaf.map_id _
  erw [e]
  simp

theorem algebraMap_mem_regAt' {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    {O : Type} [CommRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O))
    (h : ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω))) (p : Cpt ξ) (o : O) :
    algebraMap O Ω o ∈ regAt ξ p := by
  obtain ⟨q, hq⟩ := p
  refine ⟨X.presheaf.germ ⊤ q (show q ∈ (⊤ : X.Opens) from trivial) (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)), ?_⟩
  have h1 := germ_top_stalk_closed_point ξ hq
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ s.appTop ≫ ξ.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom
      = CommRingCat.ofHom (algebraMap O Ω) := by
    have : s.appTop ≫ ξ.appTop = (ξ ≫ s).appTop := by simp
    rw [reassoc_of% this, h]
    simp
  have h3 := congrArg (fun f => f.hom o) h2
  have h4 := congrArg (fun f => f.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) h1
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3 h4
  rw [CommRingCat.hom_ofHom] at h3
  refine Eq.trans ?_ (h4.trans h3)
  rfl

theorem isIntegral_of_forall_valuationSubring' {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω]
    (hf : Function.Injective (algebraMap R Ω)) (a : Ω)
    (H : ∀ V : ValuationSubring Ω, (∀ r : R, algebraMap R Ω r ∈ V) → a ∈ V) : IsIntegral R a := by
  have hall : a ∈ ⨅ V : {V : ValuationSubring Ω // Set.range (algebraMap R Ω) ⊆ V.toSubring}, V.1.toSubring :=
    Subring.mem_iInf.mpr fun V => H V.1 fun r => V.2 ⟨r, rfl⟩
  rw [iInf_valuationSubring_superset, Subalgebra.mem_toSubring, mem_integralClosure_iff] at hall
  let g : R →+* Subring.closure (Set.range (algebraMap R Ω)) :=
    (algebraMap R Ω).codRestrict _ fun r => Subring.subset_closure ⟨r, rfl⟩
  have hg : Function.Bijective g := by
    refine ⟨fun x y hxy => hf (congrArg Subtype.val hxy), ?_⟩
    rintro ⟨y, hy⟩
    have hle : Subring.closure (Set.range (algebraMap R Ω)) ≤ (algebraMap R Ω).range :=
      Subring.closure_le.mpr fun z hz => hz
    obtain ⟨r, rfl⟩ := hle hy
    exact ⟨r, rfl⟩
  let e := RingEquiv.ofBijective g hg
  have hcomp : (algebraMap R Ω).comp (e.symm : _ →+* R) =
      (RingHom.id Ω).comp (algebraMap (Subring.closure (Set.range (algebraMap R Ω))) Ω) := by
    ext x
    have : g (e.symm x) = x := e.apply_symm_apply x
    exact congrArg Subtype.val this
  exact IsIntegral.map_of_comp_eq (e.symm : _ →+* R) (RingHom.id Ω) hcomp hall

theorem isIntegral_and_isAlgebraic_of_regular : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → IsCptGen ξ → ∀ a : Ω, ((∀ p : Cpt ξ, a ∈ regAt ξ p) → IsIntegral O a) ∧ ((∀ p ∈ genFibre O ξ, a ∈ regAt ξ p) → IsAlgebraic O a) := by
  intro X Ω _ ξ O _ _ _ s _ h hinj _ a
  refine ⟨fun ha => isIntegral_of_forall_valuationSubring' hinj a fun V hV => ?_, fun ha => ?_⟩
  · obtain ⟨p, hp, -⟩ := GlobalTheory.T.valuation_centre_regular_unit X Ω ξ O s h V hV
    exact hp (ha p)
  · haveI : FaithfulSMul O Ω := (faithfulSMul_iff_algebraMap_injective O Ω).2 hinj
    letI := FractionRing.liftAlgebra O Ω
    haveI : IsScalarTower O (FractionRing O) Ω := inferInstance
    refine (IsFractionRing.isAlgebraic_iff O (FractionRing O) Ω).2 (IsIntegral.isAlgebraic
      (isIntegral_of_forall_valuationSubring' (algebraMap (FractionRing O) Ω).injective a fun V hV => ?_))
    have hO : ∀ o : O, algebraMap O Ω o ∈ V := fun o => by
      rw [IsScalarTower.algebraMap_apply O (FractionRing O) Ω]
      exact hV _
    obtain ⟨p, hp, hu⟩ := GlobalTheory.T.valuation_centre_regular_unit X Ω ξ O s h V hO
    refine hp (ha p fun o ho => ?_)
    have hne : algebraMap O Ω o ≠ 0 := fun h0 => ho (hinj (by simpa using h0))
    have hreg := algebraMap_mem_regAt' ξ s h p o
    have hinv : (algebraMap O Ω o)⁻¹ ∈ V := by
      rw [IsScalarTower.algebraMap_apply O (FractionRing O) Ω, ← map_inv₀]
      exact hV _
    obtain ⟨g, hg, hga⟩ := hu _ hreg hne hinv
    obtain ⟨u, rfl⟩ := hg
    refine ⟨hne, hreg, ⟨(u⁻¹ : (X.presheaf.stalk p.1)ˣ).1, ?_⟩⟩
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hga, ← map_mul, Units.inv_mul, map_one]

end GlobalTheory.CompanionTheory.Ar.Flat
end

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_everywhere_isIntegral : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → IsCptGen ξ → ∀ a : Ω, ((∀ p : Cpt ξ, a ∈ regAt ξ p) → IsIntegral O a) ∧ ((∀ p ∈ genFibre O ξ, a ∈ regAt ξ p) → IsAlgebraic O a) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.isIntegral_and_isAlgebraic_of_regular
end

section
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem mem_regAt_genPt_of_isCptGen {X : Scheme.{0}} {Ω : Type} [Field Ω]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ) (a : Ω) :
    a ∈ regAt ξ ⟨genPt ξ, specializes_refl _⟩ := by
  obtain ⟨g, hg⟩ := h.bij.2 a
  refine ⟨g, ?_⟩
  rw [← hg]
  simp only [genMap, genPt, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  rfl

theorem genPt_mem_genFibre_of_isCptGen {X : Scheme.{0}} {Ω : Type} [Field Ω]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ) (O : Type) [CommRing O] [Algebra O Ω]
    (hi : Function.Injective (algebraMap O Ω)) :
    (⟨genPt ξ, specializes_refl _⟩ : Cpt ξ) ∈ genFibre O ξ := fun o ho =>
  ⟨fun h0 => ho (hi (by rw [h0, map_zero])), mem_regAt_genPt_of_isCptGen h _,
    mem_regAt_genPt_of_isCptGen h _⟩

theorem mem_lat_genFibre_iff_const_mul : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → IsCptGen ξ → ConstClosed O Ω → ∀ (L : Lat ξ Ω) (t : Ω), (∀ p ∈ genFibre O ξ, L.IsGenAt p t) → ∀ u : Ω, (∀ p ∈ genFibre O ξ, u ∈ L p) ↔ ∃ x y : O, y ≠ 0 ∧ u * algebraMap O Ω y = algebraMap O Ω x * t := by
  intro X Ω _ ξ O _ _ _ s _ hs hi hξ hc L t ht u
  have ht0 : t ≠ 0 := (ht _ (genPt_mem_genFibre_of_isCptGen hξ O hi)).1
  constructor
  · intro hu
    have hreg : ∀ p ∈ genFibre O ξ, u / t ∈ regAt ξ p := by
      intro p hp
      have h1 := hu p hp
      rw [(ht p hp).2] at h1
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h1
      replace hc : (c : Ω) * t = u := hc
      rw [← hc, mul_div_cancel_right₀ _ ht0]
      exact c.2
    obtain ⟨x, y, hy, e⟩ := hc _ ((GlobalTheory.T.regular_everywhere_isIntegral X Ω ξ O s hs hi hξ (u / t)).2 hreg)
    refine ⟨x, y, hy, ?_⟩
    rw [← e]
    field_simp
  · rintro ⟨x, y, hy, e⟩ p hp
    rw [(ht p hp).2]
    have hx : algebraMap O Ω x ∈ regAt ξ p := by
      by_cases h0 : x = 0
      · rw [h0, map_zero]; exact zero_mem _
      · exact (hp x h0).2.1
    have hyu := hp y hy
    refine Submodule.mem_span_singleton.2 ⟨⟨_, mul_mem hx hyu.2.2⟩, ?_⟩
    change algebraMap O Ω x * (algebraMap O Ω y)⁻¹ * t = u
    have := hyu.1
    rw [mul_right_comm, ← e]
    field_simp

end GlobalTheory.CompanionTheory.Ar.Flat
end

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_lattice_generic_sections : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → IsCptGen ξ → ConstClosed O Ω → ∀ (L : Lat ξ Ω) (t : Ω), (∀ p ∈ genFibre O ξ, L.IsGenAt p t) → ∀ u : Ω, (∀ p ∈ genFibre O ξ, u ∈ L p) ↔ ∃ x y : O, y ≠ 0 ∧ u * algebraMap O Ω y = algebraMap O Ω x * t := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.mem_lat_genFibre_iff_const_mul
end
