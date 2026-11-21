import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory

theorem closedImmersion_baseChange_ker_mem_map : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → ∀ W : X.Opens, IsAffineOpen W → ∀ s : Γ(X', p ⁻¹ᵁ W), (i'.app (p ⁻¹ᵁ W)).hom s = 0 → s ∈ Ideal.map (p.app W).hom (RingHom.ker (i.app W).hom) := by
  intro X X' Z Z' p i i' p' h hp hi W hW s hs
  set J : Ideal Γ(X', p ⁻¹ᵁ W) := Ideal.map (p.app W).hom (RingHom.ker (i.app W).hom) with hJ
  have hU' : IsAffineOpen (p ⁻¹ᵁ W) := hW.preimage p
  have hZ : IsAffineOpen (i ⁻¹ᵁ W) := hW.preimage i
  have hsurj : Function.Surjective (i.app W).hom := i.app_surjective W hW
  let ψ : Γ(X, W) →+* (Γ(X', p ⁻¹ᵁ W) ⧸ J) := (Ideal.Quotient.mk J).comp (p.app W).hom
  have hker : RingHom.ker (i.app W).hom ≤ RingHom.ker ψ := by
    intro a ha
    simp only [RingHom.mem_ker, ψ, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ha
  let φ : Γ(Z, i ⁻¹ᵁ W) →+* (Γ(X', p ⁻¹ᵁ W) ⧸ J) :=
    (i.app W).hom.liftOfSurjective hsurj ⟨ψ, hker⟩
  have hφ : φ.comp (i.app W).hom = ψ := (i.app W).hom.liftOfRightInverse_comp _ _ _
  let e : Spec (CommRingCat.of (Γ(X', p ⁻¹ᵁ W) ⧸ J)) ⟶ X' :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ hU'.fromSpec
  let t : Spec (CommRingCat.of (Γ(X', p ⁻¹ᵁ W) ⧸ J)) ⟶ Z :=
    Spec.map (CommRingCat.ofHom φ) ≫ hZ.fromSpec
  have hw : e ≫ p = t ≫ i := by
    have h1 := IsAffineOpen.SpecMap_appLE_fromSpec p hW hU' le_rfl
    have h2 := IsAffineOpen.SpecMap_appLE_fromSpec i hW hZ le_rfl
    simp only [e, t, Category.assoc, ← h1, ← h2, ← Spec.map_comp, ← Scheme.Hom.app_eq_appLE]
    simp only [← Spec.map_comp_assoc]
    congr 2
    ext x
    exact (RingHom.congr_fun hφ x).symm
  let l := h.lift e t hw
  have hl : l ≫ i' = e := h.lift_fst e t hw
  have hle : (⊤ : (Spec (CommRingCat.of (Γ(X', p ⁻¹ᵁ W) ⧸ J))).Opens) ≤ e ⁻¹ᵁ (p ⁻¹ᵁ W) := by
    simp [e, Scheme.Hom.comp_preimage, hU'.fromSpec_preimage_self]
  have h0 : (e.appLE (p ⁻¹ᵁ W) ⊤ hle).hom s = 0 := by
    have key : ∀ (g : Spec (CommRingCat.of (Γ(X', p ⁻¹ᵁ W) ⧸ J)) ⟶ X') (hg : g = e) (hle' : ⊤ ≤ g ⁻¹ᵁ (p ⁻¹ᵁ W)),
        g.appLE (p ⁻¹ᵁ W) ⊤ hle' = e.appLE (p ⁻¹ᵁ W) ⊤ hle := by
      rintro g rfl _; rfl
    rw [← key (l ≫ i') hl (by rw [hl]; exact hle), Scheme.Hom.comp_appLE, CommRingCat.comp_apply, hs, map_zero]
  have h1 : (e.appLE (p ⁻¹ᵁ W) ⊤ hle).hom s = (Scheme.ΓSpecIso (CommRingCat.of (Γ(X', p ⁻¹ᵁ W) ⧸ J))).inv.hom (Ideal.Quotient.mk J s) := by
    simp only [e, Scheme.Hom.comp_appLE, hU'.fromSpec_app_self]
    rw [Category.assoc]
    erw [Scheme.Hom.map_appLE]
    rw [show ∀ hh, (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appLE ⊤ ⊤ hh = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).appTop from fun _ => (Scheme.Hom.app_eq_appLE _).symm]
    rw [← Scheme.ΓSpecIso_inv_naturality]
    rfl
  rw [h1] at h0
  have h2 : Ideal.Quotient.mk J s = 0 := by
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Γ(X', p ⁻¹ᵁ W) ⧸ J))).hom.hom h0
    simpa using this
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedImmersion_baseChange_ker_mem_map_affine : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → ∀ W : X.Opens, IsAffineOpen W → ∀ s : Γ(X', p ⁻¹ᵁ W), (i'.app (p ⁻¹ᵁ W)).hom s = 0 → s ∈ Ideal.map (p.app W).hom (RingHom.ker (i.app W).hom) := by
  atlas_forward_decl GlobalTheory.closedImmersion_baseChange_ker_mem_map
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

theorem germ_app_congr {Y X : Scheme.{0}} {f g : Y ⟶ X} (e : f = g) (W : X.Opens) (y : Y) (hf : f y ∈ W)
    (hg : g y ∈ W) (s : Γ(X, W)) :
    Y.presheaf.germ (f ⁻¹ᵁ W) y hf ((f.app W).hom s) = Y.presheaf.germ (g ⁻¹ᵁ W) y hg ((g.app W).hom s) := by
  subst e; rfl

theorem affine_descent_units : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z),
    IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.Pinch.Cond p i →
    ∀ W : X.Opens, IsAffineOpen W → ∀ (u' : Γ(X', p ⁻¹ᵁ W)ˣ) (v : Γ(Z, i ⁻¹ᵁ W)ˣ),
      (∀ z : Z', p (i' z) ∈ W → gm i' z (p ⁻¹ᵁ W) u' = gm p' z (i ⁻¹ᵁ W) v) →
      ∃ u : Γ(X, W)ˣ, pullU p W u = u' := by
  intro X X' Z Z' p i i' p' h hp hi hc W hW u' v huv
  have hw : ∀ z : Z', p (i' z) = i (p' z) := fun z => by
    have := congrArg (fun f : Z' ⟶ X => f z) h.w
    simpa using this
  have claim : ∀ (s' : Γ(X', p ⁻¹ᵁ W)) (t : Γ(Z, i ⁻¹ᵁ W)),
      (∀ z : Z', ∀ hz : p (i' z) ∈ W,
        Z'.presheaf.germ (i' ⁻¹ᵁ (p ⁻¹ᵁ W)) z hz ((i'.app (p ⁻¹ᵁ W)).hom s') =
          Z'.presheaf.germ (p' ⁻¹ᵁ (i ⁻¹ᵁ W)) z (show i (p' z) ∈ W from hw z ▸ hz) ((p'.app (i ⁻¹ᵁ W)).hom t)) →
      ∃ s : Γ(X, W), (p.app W).hom s = s' := by
    intro s' t hst
    obtain ⟨s₀, rfl⟩ := Scheme.Hom.app_surjective i W hW t
    have hd : (i'.app (p ⁻¹ᵁ W)).hom (s' - (p.app W).hom s₀) = 0 := by
      apply TopCat.Presheaf.section_ext Z'.sheaf
      intro z hz
      show (Z'.presheaf.germ (i' ⁻¹ᵁ p ⁻¹ᵁ W) z hz).hom ((i'.app (p ⁻¹ᵁ W)).hom (s' - (p.app W).hom s₀)) =
        (Z'.presheaf.germ (i' ⁻¹ᵁ p ⁻¹ᵁ W) z hz).hom 0
      rw [map_sub, map_sub, map_zero, sub_eq_zero, hst z hz]
      have e1 := germ_app_congr h.w W z hz (show i (p' z) ∈ W from hw z ▸ hz) s₀
      exact e1.symm
    have hmem := GlobalTheory.T.closedImmersion_baseChange_ker_mem_map_affine X X' Z Z' p i i' p' h hp hi W hW _ hd
    have key : ∃ y, (i.app W).hom y = 0 ∧ (p.app W).hom y = s' - (p.app W).hom s₀ := by
      refine Submodule.span_induction (p := fun x _ => ∃ y, (i.app W).hom y = 0 ∧ (p.app W).hom y = x)
        ?_ ?_ ?_ ?_ hmem
      · rintro _ ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      · exact ⟨0, map_zero _, map_zero _⟩
      · rintro _ _ _ _ ⟨y₁, h₁, e₁⟩ ⟨y₂, h₂, e₂⟩
        exact ⟨y₁ + y₂, by rw [map_add, h₁, h₂, add_zero], by rw [map_add, e₁, e₂]⟩
      · rintro r _ _ ⟨y, hy, rfl⟩
        obtain ⟨y', hy', e'⟩ := (hc W hW).2 y hy r
        exact ⟨y', hy', by rw [smul_eq_mul, mul_comm]; exact e'⟩
    obtain ⟨y, -, hy⟩ := key
    exact ⟨s₀ + y, by rw [map_add, hy, add_sub_cancel]⟩
  have germs : ∀ (a : Γ(X', p ⁻¹ᵁ W)ˣ) (b : Γ(Z, i ⁻¹ᵁ W)ˣ),
      (∀ z : Z', p (i' z) ∈ W → gm i' z (p ⁻¹ᵁ W) a = gm p' z (i ⁻¹ᵁ W) b) →
      ∃ s : Γ(X, W), (p.app W).hom s = a.val := by
    intro a b hab
    refine claim a.val b.val fun z hz => ?_
    have := congrArg Units.val (hab z hz)
    rwa [gm_val i' z _ hz, gm_val p' z _ (show i (p' z) ∈ W from hw z ▸ hz)] at this
  obtain ⟨x, hx⟩ := germs u' v huv
  obtain ⟨y, hy⟩ := germs u'⁻¹ v⁻¹ fun z hz => by rw [map_inv, map_inv, huv z hz]
  have hxy : x * y = 1 := (hc W hW).1 (by
    show (p.app W).hom (x * y) = (p.app W).hom 1
    rw [map_mul, map_one, hx, hy, Units.mul_inv])
  exact ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, Units.ext hx⟩

theorem pullU_injective {X X' : Scheme.{0}} (p : X' ⟶ X)
    (hp : ∀ W : X.Opens, IsAffineOpen W → Function.Injective (p.app W)) (W : X.Opens) :
    Function.Injective (pullU p W) := by
  intro a b hab
  apply unit_ext
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
  have hle : V ≤ W := hVW
  have e : res hle a = res hle b := by
    apply Units.ext
    apply hp V hV
    have := congrArg Units.val (show pullU p V (res hle a) = pullU p V (res hle b) by
      rw [pullU_res₂, pullU_res₂, hab])
    exact this
  rw [← gm_res (𝟙 X) x hle hxV a, ← gm_res (𝟙 X) x hle hxV b, e]

theorem unitsPatch : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z),
    IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.Pinch.Cond p i →
    GlobalTheory.Pinch.UnitsPatch p i i' p' := by
  intro X X' Z Z' p i i' p' h hp hi hc W
  have hinj : ∀ V : X.Opens, Function.Injective (pullU p V) :=
    pullU_injective p (fun V hV => (hc V hV).1)
  refine ⟨hinj W, fun u' v huv => ?_⟩
  have hw : ∀ z : Z', p (i' z) = i (p' z) := fun z => by
    have := congrArg (fun f : Z' ⟶ X => f z) h.w
    simpa using this
  let J : Type := {V : X.Opens // IsAffineOpen V ∧ V ≤ W}
  have hsub : ∀ j : J, p ⁻¹ᵁ j.1 ≤ p ⁻¹ᵁ W := fun j x hx => j.2.2 hx
  have hsubZ : ∀ j : J, i ⁻¹ᵁ j.1 ≤ i ⁻¹ᵁ W := fun j x hx => j.2.2 hx
  have loc : ∀ j : J, ∃ a : Γ(X, j.1)ˣ, pullU p j.1 a = res (hsub j) u' := by
    intro j
    refine affine_descent_units X X' Z Z' p i i' p' h hp hi hc j.1 j.2.1 _ (res (hsubZ j) v) ?_
    intro z hz
    rw [gm_res i' z (hsub j) hz, gm_res p' z (hsubZ j) (show i (p' z) ∈ j.1 from hw z ▸ hz)]
    exact huv z (j.2.2 hz)
  choose a ha using loc

  have hD : ∀ j : J, ∀ y : X', ∀ hy : p y ∈ j.1, gm p y j.1 (a j) = gm (𝟙 X') y (p ⁻¹ᵁ W) u' := by
    intro j y hy
    rw [← gm_id_pull p y j.1 hy, ha j, gm_res (𝟙 X') y (hsub j) hy]
  obtain ⟨s, hs⟩ := glue_unit W (fun j : J => j.1) (fun j => j.2.2) (by
      intro x hx
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV, hVW⟩, hxV⟩) a (by
      intro j k x hx
      have hle1 : j.1 ⊓ k.1 ≤ j.1 := inf_le_left
      have hle2 : j.1 ⊓ k.1 ≤ k.1 := inf_le_right
      have e : res hle1 (a j) = res hle2 (a k) := by
        apply hinj
        apply unit_ext
        intro y hy
        rw [gm_id_pull p y _ hy, gm_id_pull p y _ hy, gm_res p y hle1 hy, gm_res p y hle2 hy,
          hD j y (hle1 hy), hD k y (hle2 hy)]
      rw [← gm_res (𝟙 X) x hle1 hx, ← gm_res (𝟙 X) x hle2 hx, e])
  refine ⟨s, unit_ext fun y hy => ?_⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (show p y ∈ W from hy) W.2
  let j : J := ⟨V, hV, hVW⟩
  rw [gm_id_pull p y W hy, ← gm_res p y j.2.2 hxV, hs j]
  exact hD j y hxV

end GlobalTheory.Pinch
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pinchingSquare_unitsPatch : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.Pinch.Cond p i → GlobalTheory.Pinch.UnitsPatch p i i' p' := by
  atlas_forward_decl GlobalTheory.Pinch.unitsPatch
end
