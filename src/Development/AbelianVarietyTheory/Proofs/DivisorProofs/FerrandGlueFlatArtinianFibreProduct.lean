import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPushoutAppLEOfIsPullbackOfIsAffine
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchlessingerFlatFibreProduct

section
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option autoImplicit false

namespace GlobalTheory.NilThicken

theorem ker_inl_le_map_ker_of_isPushout {A B C D : CommRingCat.{0}} {a : A ⟶ B} {c : A ⟶ C}
    {b : B ⟶ D} {d : C ⟶ D} (h : IsPushout a c b d) (hc : Function.Surjective c.hom) :
    RingHom.ker b.hom ≤ Ideal.map a.hom (RingHom.ker c.hom) := by
  set J : Ideal B := Ideal.map a.hom (RingHom.ker c.hom)
  let π : B ⟶ CommRingCat.of (B ⧸ J) := CommRingCat.ofHom (Ideal.Quotient.mk J)
  let e := RingHom.quotientKerEquivOfSurjective hc
  let σ : C ⟶ CommRingCat.of (B ⧸ J) := CommRingCat.ofHom
    ((Ideal.quotientMap J a.hom (Ideal.le_comap_map)).comp e.symm.toRingHom)
  have w : a ≫ π = c ≫ σ := by
    ext x
    have hx : e.symm (c.hom x) = Ideal.Quotient.mk _ x := by
      rw [RingEquiv.symm_apply_eq]; rfl
    simp [π, σ, hx]
  intro x hx
  have h1 : (b ≫ h.desc π σ w).hom x = π.hom x := by rw [h.inl_desc]
  rw [CommRingCat.comp_apply, (RingHom.mem_ker).mp hx, map_zero] at h1
  exact Ideal.Quotient.eq_zero_iff_mem.mp h1.symm

theorem isNilpotent_ker_app :
    ∀ (R₁ R₀ : CommRingCat.{0}) (g : R₁ ⟶ R₀) (Y₁ Y₀ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec R₁)
      (p₀ : Y₀ ⟶ Spec R₀) (i : Y₀ ⟶ Y₁), IsPullback i p₀ p₁ (Spec.map g) →
      Function.Surjective g → IsNilpotent (RingHom.ker g.hom) → ∀ U : Y₁.Opens, IsAffineOpen U →
      IsNilpotent (RingHom.ker (i.app U).hom) := by
  intro R₁ R₀ g Y₁ Y₀ p₁ p₀ i hpb hg hnil U hU
  have P := GlobalTheory.AffBaseChange.isPushout_appLE_of_isPullback_of_isAffine Y₁ Y₀ (Spec R₁) (Spec R₀)
    i p₀ p₁ (Spec.map g) hpb inferInstance inferInstance U hU
  have hnat := Scheme.ΓSpecIso_naturality g
  set c := (Spec.map g).appTop
  have hcker : RingHom.ker c.hom = Ideal.comap (Scheme.ΓSpecIso R₁).hom.hom (RingHom.ker g.hom) := by
    ext x
    simp only [RingHom.mem_ker, Ideal.mem_comap]
    have := congrArg (fun φ => φ.hom x) hnat
    simp only [CommRingCat.comp_apply] at this
    rw [← this]
    constructor
    · intro h0; rw [h0, map_zero]
    · intro h0
      have hinj := ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R₀).hom)).1
      exact hinj (by rw [h0, map_zero])
  have hcs : Function.Surjective c.hom := by
    intro y
    obtain ⟨r, hr⟩ := hg ((Scheme.ΓSpecIso R₀).hom y)
    obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R₁).hom).2 r
    refine ⟨x, ?_⟩
    have := congrArg (fun φ => φ.hom x) hnat
    simp only [CommRingCat.comp_apply] at this
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R₀).hom).1
    rw [this, hx, hr]
  obtain ⟨n, hn⟩ := hnil
  refine ⟨n, ?_⟩
  have hle := ker_inl_le_map_ker_of_isPushout P hcs
  have hJ : (Ideal.map (p₁.appLE ⊤ U (fun _ _ => trivial)).hom (RingHom.ker c.hom)) ^ n = ⊥ := by
    rw [← Ideal.map_pow, hcker]
    have h2 : (Ideal.comap (Scheme.ΓSpecIso R₁).hom.hom (RingHom.ker g.hom)) ^ n = ⊥ := by
      apply le_bot_iff.mp
      refine (Ideal.le_comap_pow _ n).trans ?_
      rw [show RingHom.ker g.hom ^ n = ⊥ from hn]
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      rw [Ideal.mem_bot]
      exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R₁).hom).1 (by rw [hx, map_zero])
    rw [h2, Ideal.map_bot]
  exact le_bot_iff.mp ((Ideal.pow_right_mono hle n).trans hJ.le)

end GlobalTheory.NilThicken
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNilpotent_ker_app_of_isPullback_of_nilpotent : ∀ (R₁ R₀ : CommRingCat.{0}) (g : R₁ ⟶ R₀) (Y₁ Y₀ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec R₁) (p₀ : Y₀ ⟶ Spec R₀) (i : Y₀ ⟶ Y₁), IsPullback i p₀ p₁ (Spec.map g) → Function.Surjective g → IsNilpotent (RingHom.ker g.hom) → ∀ U : Y₁.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i.app U).hom) := by
  atlas_forward_decl GlobalTheory.NilThicken.isNilpotent_ker_app
end

section
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PinchBasis

theorem isPullback_iff_elem {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (h : B ⟶ D) (i : C ⟶ D)
    (w : f ≫ h = g ≫ i) :
    IsPullback f g h i ↔ (∀ x y, f.hom x = f.hom y → g.hom x = g.hom y → x = y) ∧
      ∀ b c, h.hom b = i.hom c → ∃ a, f.hom a = b ∧ g.hom a = c := by
  constructor
  · intro H
    have H' := (Types.isPullback_iff _ _ _ _).1 (H.map (forget CommRingCat))
    exact ⟨fun x y hx hy ↦ H'.2.1 x y ⟨hx, hy⟩, fun b c hbc ↦ H'.2.2 b c hbc⟩
  · rintro ⟨h₁, h₂⟩
    refine IsPullback.of_map (forget CommRingCat) w ((Types.isPullback_iff _ _ _ _).2 ⟨?_, ?_, ?_⟩)
    · ext x
      simpa using congrArg (fun φ : A ⟶ D ↦ φ.hom x) w
    · exact fun x y hxy ↦ h₁ x y hxy.1 hxy.2
    · exact fun b c hbc ↦ h₂ b c hbc

lemma app_res {X Y : Scheme.{0}} (f : X ⟶ Y) {W V : Y.Opens} (i : W ⟶ V) (s : Γ(Y, V)) :
    (f.app W).hom ((Y.presheaf.map i.op).hom s) =
      (X.presheaf.map ((TopologicalSpace.Opens.map f.base).map i).op).hom ((f.app V).hom s) :=
  congrArg (fun φ => φ.hom s) (f.naturality i.op)

lemma appLE_res {X Y : Scheme.{0}} (g : X ⟶ Y) {U U' : Y.Opens} {V V' : X.Opens} (hU : U' ≤ U)
    (hV : V' ≤ V) (e : V ≤ g ⁻¹ᵁ U) (e' : V' ≤ g ⁻¹ᵁ U') (b : Γ(Y, U)) :
    (g.appLE U' V' e').hom ((Y.presheaf.map (homOfLE hU).op).hom b) =
      (X.presheaf.map (homOfLE hV).op).hom ((g.appLE U V e).hom b) := by
  have h1 := congrArg (fun φ => φ.hom b) (g.map_appLE e' (homOfLE hU).op)
  have h2 := congrArg (fun φ => φ.hom b) (g.appLE_map e (homOfLE hV).op)
  exact h1.trans h2.symm

lemma res_res (X : Scheme.{0}) {U V W : X.Opens} (i : V ⟶ U) (j : W ⟶ V) (k : W ⟶ U) (s : Γ(X, U)) :
    (X.presheaf.map j.op).hom ((X.presheaf.map i.op).hom s) = (X.presheaf.map k.op).hom s := by
  have := congrArg (fun φ => φ.hom s) (X.presheaf.map_comp i.op j.op)
  exact this.symm.trans rfl

theorem isPullback_app_of_isBasis : ∀ (Y₀ Y₁ Y₂ Y : Scheme.{0}) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂) (𝒱 : Set Y.Opens), TopologicalSpace.Opens.IsBasis 𝒱 → (∀ V ∈ 𝒱, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) → ∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)) := by
  intro Y₀ Y₁ Y₂ Y i₁ i₂ j₁ j₂ hw 𝒱 h𝒱 hP
  have hle : ∀ V : Y.Opens, (i₁ ≫ j₁) ⁻¹ᵁ V ≤ i₂ ⁻¹ᵁ (j₂ ⁻¹ᵁ V) := fun V => by rw [hw]; exact le_rfl
  have hcomm : ∀ V : Y.Opens, j₁.app V ≫ i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl =
      j₂.app V ≫ i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (hle V) := by
    intro V
    have key : ∀ (k k' : Y₀ ⟶ Y), k = k' → ∀ (e : (i₁ ≫ j₁) ⁻¹ᵁ V ≤ k ⁻¹ᵁ V)
        (e' : (i₁ ≫ j₁) ⁻¹ᵁ V ≤ k' ⁻¹ᵁ V), k.appLE V ((i₁ ≫ j₁) ⁻¹ᵁ V) e = k'.appLE V ((i₁ ≫ j₁) ⁻¹ᵁ V) e' := by
      rintro k _ rfl e e'; rfl
    exact (Scheme.Hom.comp_appLE i₁ j₁ V _ le_rfl).symm.trans
      ((key _ _ hw _ _).trans (Scheme.Hom.comp_appLE i₂ j₂ V _ (hle V)))
  have hcovY : ∀ U : Y.Opens, U ≤ ⨆ W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ U}, W.1 := by
    intro U y hy
    obtain ⟨W, hW, hyW, hWU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 h𝒱 hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW, hWU⟩, hyW⟩
  have hcov : ∀ {Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens),
      f ⁻¹ᵁ U ≤ ⨆ W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ U}, f ⁻¹ᵁ W.1 := by
    intro Z f U z hz
    obtain ⟨W, hW, hzW, hWU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 h𝒱 (x := f z) hz
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW, hWU⟩, hzW⟩

  have inj : ∀ (U : Y.Opens) (s t : Γ(Y, U)), (j₁.app U).hom s = (j₁.app U).hom t →
      (j₂.app U).hom s = (j₂.app U).hom t → s = t := by
    intro U s t h₁ h₂
    refine Y.sheaf.eq_of_locally_eq' (fun W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ U} => W.1) U
      (fun W => homOfLE W.2.2) (hcovY U) s t ?_
    rintro ⟨W, hW, hWU⟩
    obtain ⟨hinj, -⟩ := (isPullback_iff_elem _ _ _ _ (hcomm W)).1 (hP W hW)
    apply hinj
    · exact (app_res j₁ (homOfLE hWU) s).trans ((congrArg _ h₁).trans (app_res j₁ (homOfLE hWU) t).symm)
    · exact (app_res j₂ (homOfLE hWU) s).trans ((congrArg _ h₂).trans (app_res j₂ (homOfLE hWU) t).symm)

  have surj : ∀ (V : Y.Opens) (b : Γ(Y₁, j₁ ⁻¹ᵁ V)) (c : Γ(Y₂, j₂ ⁻¹ᵁ V)),
      (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl).hom b =
        (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (hle V)).hom c →
      ∃ a, (j₁.app V).hom a = b ∧ (j₂.app V).hom a = c := by
    intro V b c hbc
    have loc : ∀ W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ V}, ∃ a : Γ(Y, W.1),
        (j₁.app W.1).hom a = (Y₁.presheaf.map (homOfLE (j₁.preimage_mono W.2.2)).op).hom b ∧
        (j₂.app W.1).hom a = (Y₂.presheaf.map (homOfLE (j₂.preimage_mono W.2.2)).op).hom c := by
      rintro ⟨W, hW, hWV⟩
      obtain ⟨-, hex⟩ := (isPullback_iff_elem _ _ _ _ (hcomm W)).1 (hP W hW)
      apply hex
      have e1 := appLE_res i₁ (j₁.preimage_mono hWV) ((i₁ ≫ j₁).preimage_mono hWV) le_rfl le_rfl b
      have e2 := appLE_res i₂ (j₂.preimage_mono hWV) ((i₁ ≫ j₁).preimage_mono hWV) (hle V) (hle W) c
      exact e1.trans ((congrArg _ hbc).trans e2.symm)
    choose sf hsf₁ hsf₂ using loc
    have hcompat : TopCat.Presheaf.IsCompatible Y.sheaf.1 (fun W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ V} => W.1) sf := by
      intro W W'
      apply inj
      · refine (app_res j₁ _ _).trans (Eq.trans ?_ (app_res j₁ _ _).symm)
        rw [hsf₁, hsf₁]
        exact (res_res Y₁ _ _ (homOfLE (j₁.preimage_mono (inf_le_left.trans W.2.2))) b).trans
          (res_res Y₁ _ _ (homOfLE (j₁.preimage_mono (inf_le_left.trans W.2.2))) b).symm
      · refine (app_res j₂ _ _).trans (Eq.trans ?_ (app_res j₂ _ _).symm)
        rw [hsf₂, hsf₂]
        exact (res_res Y₂ _ _ (homOfLE (j₂.preimage_mono (inf_le_left.trans W.2.2))) c).trans
          (res_res Y₂ _ _ (homOfLE (j₂.preimage_mono (inf_le_left.trans W.2.2))) c).symm
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ V} => W.1) V
      (fun W => homOfLE W.2.2) (hcovY V) sf hcompat
    refine ⟨s, ?_, ?_⟩
    · refine Y₁.sheaf.eq_of_locally_eq' (fun W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ V} => j₁ ⁻¹ᵁ W.1) (j₁ ⁻¹ᵁ V)
        (fun W => homOfLE (j₁.preimage_mono W.2.2)) (hcov j₁ V) _ _ ?_
      intro W
      exact (app_res j₁ (homOfLE W.2.2) s).symm.trans ((congrArg (j₁.app W.1).hom (hs W)).trans (hsf₁ W))
    · refine Y₂.sheaf.eq_of_locally_eq' (fun W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ V} => j₂ ⁻¹ᵁ W.1) (j₂ ⁻¹ᵁ V)
        (fun W => homOfLE (j₂.preimage_mono W.2.2)) (hcov j₂ V) _ _ ?_
      intro W
      exact (app_res j₂ (homOfLE W.2.2) s).symm.trans ((congrArg (j₂.app W.1).hom (hs W)).trans (hsf₂ W))
  intro V
  exact (isPullback_iff_elem _ _ _ _ (hcomm V)).2 ⟨fun x y hx hy => inj V x y hx hy, surj V⟩

end GlobalTheory.PinchBasis
end
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullback_app_of_isBasis_opens : ∀ (Y₀ Y₁ Y₂ Y : Scheme.{0}) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂) (𝒱 : Set Y.Opens), TopologicalSpace.Opens.IsBasis 𝒱 → (∀ V ∈ 𝒱, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) → ∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)) := by
  atlas_forward_decl GlobalTheory.PinchBasis.isPullback_app_of_isBasis
end

section
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ThickPush

theorem hom_ext_appLE {Z X : Scheme.{0}} {f g : Z ⟶ X} (hb : f.base = g.base)
    (h : ∀ U e, f.appLE U (g ⁻¹ᵁ U) e = g.app U) : f = g := by
  refine Scheme.Hom.ext hb fun U => ?_
  rw [← h U (le_of_eq congr((TopologicalSpace.Opens.map $hb.symm).obj U))]
  rfl

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {f f' : X ⟶ Y} (h : f = f') (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ f' ⁻¹ᵁ U) : f.appLE U V e = f'.appLE U V e' := by
  subst h; rfl

theorem isUnit_germ_of_eq {T : Scheme.{0}} {p q : T} (hpq : p = q) (W : T.Opens) (hp : p ∈ W) (hq : q ∈ W)
    (t : Γ(T, W)) (h : IsUnit (T.presheaf.germ W p hp t)) : IsUnit (T.presheaf.germ W q hq t) := by
  subst hpq; exact h

section Desc
variable {Y₀ Y₁ Y₂ Y T : Scheme.{0}} {i₁ : Y₀ ⟶ Y₁} {i₂ : Y₀ ⟶ Y₂} {j₁ : Y₁ ⟶ Y} {j₂ : Y₂ ⟶ Y}
  (hw : i₁ ≫ j₁ = i₂ ≫ j₂) (hi₂ : Function.Surjective i₂) (hj : IsHomeomorph j₁)
  (g₁ : Y₁ ⟶ T) (g₂ : Y₂ ⟶ T) (hg : i₁ ≫ g₁ = i₂ ≫ g₂)

def bse : (Y : TopCat) ⟶ (T : TopCat) :=
  TopCat.ofHom ⟨fun y => g₁ ((hj.homeomorph _).symm y),
    g₁.base.hom.continuous.comp (hj.homeomorph _).symm.continuous⟩

theorem bse_j₁ (x : Y₁) : bse hj g₁ (j₁ x) = g₁ x := by
  show g₁ ((hj.homeomorph _).symm (hj.homeomorph _ x)) = g₁ x
  rw [Homeomorph.symm_apply_apply]

include hw hi₂ hg in
theorem bse_j₂ (x : Y₂) : bse hj g₁ (j₂ x) = g₂ x := by
  obtain ⟨y, rfl⟩ := hi₂ x
  have h1 : j₂ (i₂ y) = j₁ (i₁ y) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hw]
  have h2 : g₂ (i₂ y) = g₁ (i₁ y) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hg]
  rw [h1, h2, bse_j₁]

theorem pre₁ (W : T.Opens) : j₁ ⁻¹ᵁ ((TopologicalSpace.Opens.map (bse hj g₁)).obj W) = g₁ ⁻¹ᵁ W := by
  ext x
  show bse hj g₁ (j₁ x) ∈ W ↔ g₁ x ∈ W
  rw [bse_j₁]

include hw hi₂ hg in
theorem pre₂ (W : T.Opens) : j₂ ⁻¹ᵁ ((TopologicalSpace.Opens.map (bse hj g₁)).obj W) = g₂ ⁻¹ᵁ W := by
  ext x
  show bse hj g₁ (j₂ x) ∈ W ↔ g₂ x ∈ W
  rw [bse_j₂ hw hi₂ hj g₁ g₂ hg]

end Desc

section Lift
variable {Y₀ Y₁ Y₂ Y T : Scheme.{0}} {i₁ : Y₀ ⟶ Y₁} {i₂ : Y₀ ⟶ Y₂} {j₁ : Y₁ ⟶ Y} {j₂ : Y₂ ⟶ Y}
  (hw : i₁ ≫ j₁ = i₂ ≫ j₂) (hi₂ : Function.Surjective i₂) (hj : IsHomeomorph j₁)
  (hV : ∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl)
    (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)))
  (g₁ : Y₁ ⟶ T) (g₂ : Y₂ ⟶ T) (hg : i₁ ≫ g₁ = i₂ ≫ g₂)

def liftApp (W : T.Opens) : Γ(T, W) ⟶ Γ(Y, (TopologicalSpace.Opens.map (bse hj g₁)).obj W) :=
  (hV _).lift (g₁.appLE W _ (pre₁ hj g₁ W).le) (g₂.appLE W _ (pre₂ hw hi₂ hj g₁ g₂ hg W).le) (by
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans
      ((appLE_eq_of_eq hg _ _ _ _).trans (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm))

@[reassoc]
theorem liftApp_fst (W : T.Opens) : liftApp hw hi₂ hj hV g₁ g₂ hg W ≫ j₁.app _ = g₁.appLE W _ (pre₁ hj g₁ W).le :=
  (hV _).lift_fst _ _ _

@[reassoc]
theorem liftApp_snd (W : T.Opens) : liftApp hw hi₂ hj hV g₁ g₂ hg W ≫ j₂.app _ =
    g₂.appLE W _ (pre₂ hw hi₂ hj g₁ g₂ hg W).le :=
  (hV _).lift_snd _ _ _

def psh : Y.toPresheafedSpace ⟶ T.toPresheafedSpace where
  base := bse hj g₁
  c :=
    { app := fun W => liftApp hw hi₂ hj hV g₁ g₂ hg W.unop
      naturality := fun W W' i => by
        apply (hV _).hom_ext
        · simp only [Category.assoc]
          erw [liftApp_fst, Scheme.Hom.naturality, liftApp_fst_assoc]
          simp
        · simp only [Category.assoc]
          erw [liftApp_snd, Scheme.Hom.naturality, liftApp_snd_assoc]
          simp }

end Lift

section Hom
variable {Y₀ Y₁ Y₂ Y T : Scheme.{0}} {i₁ : Y₀ ⟶ Y₁} {i₂ : Y₀ ⟶ Y₂} {j₁ : Y₁ ⟶ Y} {j₂ : Y₂ ⟶ Y}
  (hw : i₁ ≫ j₁ = i₂ ≫ j₂) (hi₂ : Function.Surjective i₂) (hj : IsHomeomorph j₁)
  (hV : ∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl)
    (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)))
  (g₁ : Y₁ ⟶ T) (g₂ : Y₂ ⟶ T) (hg : i₁ ≫ g₁ = i₂ ≫ g₂)

def desc : Y ⟶ T :=
  ⟨⟨psh hw hi₂ hj hV g₁ g₂ hg, fun x => ⟨fun a ha => by
    obtain ⟨x₁, rfl⟩ : ∃ x₁, j₁ x₁ = x := ⟨(hj.homeomorph _).symm x, (hj.homeomorph _).apply_symm_apply x⟩
    obtain ⟨W, hW, t, rfl⟩ := T.presheaf.germ_exist (x := (psh hw hi₂ hj hV g₁ g₂ hg).base (j₁ x₁)) a
    have h1 := PresheafedSpace.stalkMap_germ_apply (psh hw hi₂ hj hV g₁ g₂ hg) W (j₁ x₁) hW t
    erw [h1] at ha
    have h2 : IsUnit ((Y₁.presheaf.germ (j₁ ⁻¹ᵁ (TopologicalSpace.Opens.map (bse hj g₁)).obj W) x₁ hW)
        ((j₁.app _).hom ((liftApp hw hi₂ hj hV g₁ g₂ hg W).hom t))) := by
      erw [← Scheme.Hom.germ_stalkMap_apply]; exact ha.map (j₁.stalkMap x₁).hom
    have h3 : (j₁.app _).hom ((liftApp hw hi₂ hj hV g₁ g₂ hg W).hom t) =
        (g₁.appLE W _ (pre₁ hj g₁ W).le).hom t := by
      rw [← CommRingCat.comp_apply, liftApp_fst]
    erw [h3] at h2
    have hx₁ : g₁ x₁ ∈ W := by rw [← bse_j₁ hj g₁ x₁]; exact hW
    have h4 : (Y₁.presheaf.germ (j₁ ⁻¹ᵁ (TopologicalSpace.Opens.map (bse hj g₁)).obj W) x₁ hW)
        ((g₁.appLE W _ (pre₁ hj g₁ W).le).hom t) = g₁.stalkMap x₁ (T.presheaf.germ W (g₁ x₁) hx₁ t) := by
      rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, CommRingCat.comp_apply]
      erw [TopCat.Presheaf.germ_res_apply]
    rw [h4] at h2
    exact isUnit_germ_of_eq (bse_j₁ hj g₁ x₁).symm W hx₁ hW t (isUnit_of_map_unit (g₁.stalkMap x₁).hom _ h2)⟩⟩⟩

theorem desc_app (W : T.Opens) : (desc hw hi₂ hj hV g₁ g₂ hg).app W = liftApp hw hi₂ hj hV g₁ g₂ hg W := rfl

end Hom

section Fac
variable {Y₀ Y₁ Y₂ Y T : Scheme.{0}} {i₁ : Y₀ ⟶ Y₁} {i₂ : Y₀ ⟶ Y₂} {j₁ : Y₁ ⟶ Y} {j₂ : Y₂ ⟶ Y}
  (hw : i₁ ≫ j₁ = i₂ ≫ j₂) (hi₂ : Function.Surjective i₂) (hj : IsHomeomorph j₁)
  (hV : ∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl)
    (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)))
  (g₁ : Y₁ ⟶ T) (g₂ : Y₂ ⟶ T) (hg : i₁ ≫ g₁ = i₂ ≫ g₂)

theorem fac₁ : j₁ ≫ desc hw hi₂ hj hV g₁ g₂ hg = g₁ := by
  refine hom_ext_appLE ?_ fun W e => ?_
  · ext x
    exact bse_j₁ hj g₁ x
  · have hh : j₁.appLE (desc hw hi₂ hj hV g₁ g₂ hg ⁻¹ᵁ W) (g₁ ⁻¹ᵁ W) e = j₁.app _ ≫ Y₁.presheaf.map (homOfLE e).op := rfl
    rw [Scheme.Hom.comp_appLE, hh, desc_app]
    erw [liftApp_fst_assoc]
    exact (Scheme.Hom.appLE_map _ _ _).trans (Scheme.Hom.appLE_eq_app _)

theorem fac₂ : j₂ ≫ desc hw hi₂ hj hV g₁ g₂ hg = g₂ := by
  refine hom_ext_appLE ?_ fun W e => ?_
  · ext x
    exact bse_j₂ hw hi₂ hj g₁ g₂ hg x
  · have hh : j₂.appLE (desc hw hi₂ hj hV g₁ g₂ hg ⁻¹ᵁ W) (g₂ ⁻¹ᵁ W) e = j₂.app _ ≫ Y₂.presheaf.map (homOfLE e).op := rfl
    rw [Scheme.Hom.comp_appLE, hh, desc_app]
    erw [liftApp_snd_assoc]
    exact (Scheme.Hom.appLE_map _ _ _).trans (Scheme.Hom.appLE_eq_app _)

theorem uniq (m : Y ⟶ T) (h₁ : j₁ ≫ m = g₁) (h₂ : j₂ ≫ m = g₂) : m = desc hw hi₂ hj hV g₁ g₂ hg := by
  refine hom_ext_appLE ?_ fun W e => ?_
  · ext x
    obtain ⟨x₁, rfl⟩ : ∃ x₁, j₁ x₁ = x := ⟨(hj.homeomorph _).symm x, (hj.homeomorph _).apply_symm_apply x⟩
    show m (j₁ x₁) = bse hj g₁ (j₁ x₁)
    rw [bse_j₁, ← h₁, Scheme.Hom.comp_apply]
  · rw [desc_app]
    apply (hV _).hom_ext
    · refine Eq.trans ?_ (liftApp_fst hw hi₂ hj hV g₁ g₂ hg W).symm
      rw [Scheme.Hom.app_eq_appLE j₁]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans (appLE_eq_of_eq h₁ _ _ _ _)
    · refine Eq.trans ?_ (liftApp_snd hw hi₂ hj hV g₁ g₂ hg W).symm
      rw [Scheme.Hom.app_eq_appLE j₂]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans (appLE_eq_of_eq h₂ _ _ _ _)

end Fac

theorem isPushout_of_isPullback_sections : ∀ (Y₀ Y₁ Y₂ : Scheme.{0}) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂),
    IsClosedImmersion i₁ → IsClosedImmersion i₂ → Surjective i₁ → Surjective i₂ →
    ∀ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂),
    IsClosedImmersion j₁ → IsClosedImmersion j₂ → Surjective j₁ → Surjective j₂ →
    (∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl)
      (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) →
    IsPushout i₁ i₂ j₁ j₂ := by
  intro Y₀ Y₁ Y₂ i₁ i₂ _ _ _ hs₂ Y j₁ j₂ hw hc₁ _ hs₁ _ hV
  have hj : IsHomeomorph j₁ :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨j₁.isClosedEmbedding.isEmbedding, hs₁.surj⟩
  refine IsPushout.of_isColimit' ⟨hw⟩ (PushoutCocone.IsColimit.mk _
    (fun s => desc hw hs₂.surj hj hV s.inl s.inr s.condition)
    (fun s => fac₁ hw hs₂.surj hj hV s.inl s.inr s.condition)
    (fun s => fac₂ hw hs₂.surj hj hV s.inl s.inr s.condition)
    (fun s m h₁ h₂ => uniq hw hs₂.surj hj hV s.inl s.inr s.condition m h₁ h₂))

end GlobalTheory.ThickPush
end
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPushout_thickenings_of_isPullback_sections : ∀ (Y₀ Y₁ Y₂ : Scheme.{0}) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsClosedImmersion i₁ → IsClosedImmersion i₂ → Surjective i₁ → Surjective i₂ → ∀ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂), IsClosedImmersion j₁ → IsClosedImmersion j₂ → Surjective j₁ → Surjective j₂ → (∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) → IsPushout i₁ i₂ j₁ j₂ := by
  atlas_forward_decl GlobalTheory.ThickPush.isPushout_of_isPullback_sections
end

section
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory

theorem exists_pushout_of_nilpotent_thickenings : ∀ (Y₀ Y₁ Y₂ : Scheme.{0}) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsClosedImmersion i₁ → IsClosedImmersion i₂ → Surjective i₁ → Surjective i₂ → (∀ U : Y₁.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i₁.app U).hom)) → (∀ U : Y₂.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i₂.app U).hom)) → ∃ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂), IsPushout i₁ i₂ j₁ j₂ ∧ IsClosedImmersion j₁ ∧ IsClosedImmersion j₂ ∧ ∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)) := by
  intro Y₀ Y₁ Y₂ i₁ i₂ h1 h2 s1 s2 n1 n2
  obtain ⟨Y, j₁, j₂, hw, c1, c2, t1, t2, 𝒱, hb, hp⟩ := GlobalTheory.T.exists_pushout_data_on_basis Y₀ Y₁ Y₂ i₁ i₂ h1 h2 s1 s2 n1 n2
  have hall := GlobalTheory.T.isPullback_app_of_isBasis_opens Y₀ Y₁ Y₂ Y i₁ i₂ j₁ j₂ hw 𝒱 hb hp
  exact ⟨Y, j₁, j₂, hw, GlobalTheory.T.isPushout_thickenings_of_isPullback_sections Y₀ Y₁ Y₂ i₁ i₂ h1 h2 s1 s2 Y j₁ j₂ hw c1 c2 t1 t2 hall,
    c1, c2, hall⟩

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pushout_of_nilpotent_thickenings' : ∀ (Y₀ Y₁ Y₂ : Scheme.{0}) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsClosedImmersion i₁ → IsClosedImmersion i₂ → Surjective i₁ → Surjective i₂ → (∀ U : Y₁.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i₁.app U).hom)) → (∀ U : Y₂.Opens, IsAffineOpen U → IsNilpotent (RingHom.ker (i₂.app U).hom)) → ∃ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂), IsPushout i₁ i₂ j₁ j₂ ∧ IsClosedImmersion j₁ ∧ IsClosedImmersion j₂ ∧ ∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)) := by
  atlas_forward_decl GlobalTheory.exists_pushout_of_nilpotent_thickenings
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option autoImplicit false

namespace GlobalTheory.PushoutSquare

theorem isPullback_of_forall_isPushout_app :
    ∀ (X Y S S' : Scheme.{0}) (j : X ⟶ Y) (p : X ⟶ S') (y : Y ⟶ S) (q : S' ⟶ S), IsAffine S → IsAffine S' → IsAffineHom j → j ≫ y = p ≫ q → (∀ V : Y.Opens, IsAffineOpen V → IsPushout (y.appLE ⊤ V (fun _ _ => trivial)) q.appTop (j.app V) (p.appLE ⊤ (j ⁻¹ᵁ V) (fun _ _ => trivial))) → IsPullback j p y q := by
  intro X Y S S' j p y q hS hS' hj w H
  let φ : X ⟶ pullback y q := pullback.lift j p w
  have hφ1 : φ ≫ pullback.fst y q = j := pullback.lift_fst _ _ _
  have hφ2 : φ ≫ pullback.snd y q = p := pullback.lift_snd _ _ _
  suffices hiso : IsIso φ by
    exact IsPullback.of_iso_pullback ⟨w⟩ (asIso φ) hφ1 hφ2
  have hPb : IsPullback (pullback.fst y q) (pullback.snd y q) y q := IsPullback.of_hasPullback y q
  haveI : IsAffineHom q := inferInstance
  haveI : IsAffineHom (pullback.fst y q) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback hPb.flip inferInstance
  let U : Y.affineOpens → (pullback y q).Opens := fun V => pullback.fst y q ⁻¹ᵁ V.1
  have hU : ⨆ V, U V = ⊤ := by
    show ⨆ V : Y.affineOpens, pullback.fst y q ⁻¹ᵁ (V : Y.Opens) = ⊤
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  show MorphismProperty.isomorphisms Scheme φ
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) U hU]
  intro V
  have hpre : φ ⁻¹ᵁ U V = j ⁻¹ᵁ V.1 := by
    show φ ⁻¹ᵁ (pullback.fst y q ⁻¹ᵁ V.1) = j ⁻¹ᵁ V.1
    rw [← Scheme.Hom.comp_preimage, hφ1]
  have hUa : IsAffineOpen (U V) := V.2.preimage _
  have hSa : IsAffineOpen (φ ⁻¹ᵁ U V) := by rw [hpre]; exact V.2.preimage j
  haveI : IsAffine (U V).toScheme := hUa
  haveI : IsAffine (φ ⁻¹ᵁ U V).toScheme := hSa

  have P1 := GlobalTheory.AffBaseChange.isPushout_appLE_of_isPullback_of_isAffine Y (pullback y q) S S'
    (pullback.fst y q) (pullback.snd y q) y q hPb hS hS' V.1 V.2
  have P2 := H V.1 V.2
  let c : Γ(pullback y q, U V) ⟶ Γ(X, j ⁻¹ᵁ V.1) := φ.appLE (U V) (j ⁻¹ᵁ V.1) hpre.ge
  have key : ∀ {T : Scheme.{0}} (g j' : X ⟶ T) (hg : g = j') (A : T.Opens) (e : j' ⁻¹ᵁ A ≤ g ⁻¹ᵁ A),
      g.appLE A (j' ⁻¹ᵁ A) e = j'.appLE A (j' ⁻¹ᵁ A) le_rfl := by
    intro T g j' hg A e; subst hg; rfl
  have hc1 : (pullback.fst y q).app V.1 ≫ c = j.app V.1 := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.app_eq_appLE]
    exact key _ _ hφ1 _ _
  have hc2 : (pullback.snd y q).appLE ⊤ (pullback.fst y q ⁻¹ᵁ V.1) (fun _ _ => trivial) ≫ c =
      p.appLE ⊤ (j ⁻¹ᵁ V.1) (fun _ _ => trivial) := by
    refine (Scheme.Hom.appLE_comp_appLE φ (pullback.snd y q) ⊤ (pullback.fst y q ⁻¹ᵁ V.1) (j ⁻¹ᵁ V.1)
      (fun _ _ => trivial) hpre.ge).trans ?_
    have e2 : ∀ (e : j ⁻¹ᵁ V.1 ≤ (φ ≫ pullback.snd y q) ⁻¹ᵁ ⊤),
        (φ ≫ pullback.snd y q).appLE ⊤ (j ⁻¹ᵁ V.1) e = p.appLE ⊤ (j ⁻¹ᵁ V.1) (fun _ _ => trivial) := by
      intro e
      have gen : ∀ (g : X ⟶ S') (hg : g = p) (e' : j ⁻¹ᵁ V.1 ≤ g ⁻¹ᵁ ⊤),
          g.appLE ⊤ (j ⁻¹ᵁ V.1) e' = p.appLE ⊤ (j ⁻¹ᵁ V.1) (fun _ _ => trivial) := by
        intro g hg e'; subst hg; rfl
      exact gen _ hφ2 e
    exact e2 _
  have hcE : c = (P1.isoIsPushout _ _ P2).hom := by
    apply P1.hom_ext
    · rw [IsPushout.inl_isoIsPushout_hom]; exact hc1
    · rw [IsPushout.inr_isoIsPushout_hom]; exact hc2
  have hcI : IsIso c := by rw [hcE]; infer_instance
  have hTop : IsIso (φ ∣_ U V).appTop := by
    rw [Scheme.Hom.appTop, morphismRestrict_app']
    refine (Scheme.Hom.appLE_congr φ _ (Scheme.Opens.ι_image_top (U V))
      ((Scheme.Opens.ι_image_top (φ ⁻¹ᵁ U V)).trans hpre) (fun f => IsIso f)).mpr ?_
    exact hcI
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms _)
    (arrowIsoSpecΓOfIsAffine (φ ∣_ U V))).mpr (inferInstanceAs (IsIso (Spec.map _)))

end GlobalTheory.PushoutSquare
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullback_of_isAffine_of_forall_isPushout_appLE : ∀ (X Y S S' : Scheme.{0}) (j : X ⟶ Y) (p : X ⟶ S') (y : Y ⟶ S) (q : S' ⟶ S), IsAffine S → IsAffine S' → IsAffineHom j → j ≫ y = p ≫ q → (∀ V : Y.Opens, IsAffineOpen V → IsPushout (y.appLE ⊤ V (fun _ _ => trivial)) q.appTop (j.app V) (p.appLE ⊤ (j ⁻¹ᵁ V) (fun _ _ => trivial))) → IsPullback j p y q := by
  atlas_forward_decl GlobalTheory.PushoutSquare.isPullback_of_forall_isPushout_app
end

section
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory.SchlessingerAffine

theorem nilKer {A B C D : CommRingCat.{0}} (e : A ≅ B) (g : B ⟶ C) (e' : C ≅ D)
    (h : IsNilpotent (RingHom.ker g.hom)) : IsNilpotent (RingHom.ker (e.hom ≫ g ≫ e'.hom).hom) := by
  have hk : RingHom.ker (e.hom ≫ g ≫ e'.hom).hom = Ideal.map e.inv.hom (RingHom.ker g.hom) := by
    ext x
    have hinj : Function.Injective e'.hom.hom := e'.commRingCatIsoToRingEquiv.injective
    constructor
    · intro hx
      rw [RingHom.mem_ker] at hx
      have hx' : g.hom (e.hom.hom x) = 0 := by
        apply hinj; simpa using hx
      have : x = e.inv.hom (e.hom.hom x) := by
        change x = (e.hom ≫ e.inv).hom x; simp
      rw [this]; exact Ideal.mem_map_of_mem _ hx'
    · intro hx
      rw [RingHom.mem_ker]
      have hle : Ideal.map e.inv.hom (RingHom.ker g.hom) ≤ RingHom.ker (e.hom ≫ g ≫ e'.hom).hom := by
        rw [Ideal.map_le_iff_le_comap]
        intro z hz
        simp only [Ideal.mem_comap, RingHom.mem_ker] at hz ⊢
        change (e'.hom.hom (g.hom ((e.inv ≫ e.hom).hom z))) = 0
        simp [hz]
      exact hle hx
  rw [hk]
  exact h.map (Ideal.mapHom e.inv.hom)

theorem appTop_eq (R S : CommRingCat.{0}) (f : R ⟶ S) :
    (Spec.map f).appTop = (Scheme.ΓSpecIso R).hom ≫ f ≫ (Scheme.ΓSpecIso S).inv := by
  rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality]; simp

theorem inv_comp_appTop (R S : CommRingCat.{0}) (f : R ⟶ S) :
    (Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop = f ≫ (Scheme.ΓSpecIso S).inv := by
  rw [appTop_eq]; simp

theorem surjTop {R S : CommRingCat.{0}} (f : R ⟶ S) (h : Function.Surjective f) :
    Function.Surjective (Spec.map f).appTop := by
  rw [appTop_eq]
  have h1 := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.surjective
  have h2 := (Scheme.ΓSpecIso S).symm.commRingCatIsoToRingEquiv.surjective
  exact (h2.comp h).comp h1

theorem nilTop {R S : CommRingCat.{0}} (f : R ⟶ S) (h : IsNilpotent (RingHom.ker f.hom)) :
    IsNilpotent (RingHom.ker (Spec.map f).appTop.hom) := by
  rw [appTop_eq]
  exact nilKer (Scheme.ΓSpecIso R) f (Scheme.ΓSpecIso S).symm h

theorem pushout_of_eq (X X' S S' : Scheme.{0}) (f : X' ⟶ X) (g : X' ⟶ S') (p : X ⟶ S) (q : S' ⟶ S)
    (h : IsPullback f g p q) [IsAffine S] [IsAffine S'] (W : X.Opens) (hW : IsAffineOpen W)
    (O : X'.Opens) (hO : f ⁻¹ᵁ W = O) :
    IsPushout (p.appLE ⊤ W (fun _ _ => trivial)) q.appTop (f.appLE W O hO.ge)
      (g.appLE ⊤ O (fun _ _ => trivial)) := by
  subst hO
  have := GlobalTheory.AffBaseChange.isPushout_appLE_of_isPullback_of_isAffine X X' S S' f g p q h
    inferInstance inferInstance W hW
  rwa [Scheme.Hom.app_eq_appLE] at this

end GlobalTheory.SchlessingerAffine

open GlobalTheory.SchlessingerAffine in

theorem GlobalTheory.SchlessingerAffine.flat_and_pushouts : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → IsNilpotent (RingHom.ker g₁.hom) → IsNilpotent (RingHom.ker g₂.hom) → ∀ (Y₁ Y₂ Y₀ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec R₁) (p₂ : Y₂ ⟶ Spec R₂) (p₀ : Y₀ ⟶ Spec R₀) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsPullback i₁ p₀ p₁ (Spec.map g₁) → IsPullback i₂ p₀ p₂ (Spec.map g₂) → Flat p₁ → Flat p₂ → ∀ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂), IsClosedImmersion j₁ → IsClosedImmersion j₂ → (∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) → ∀ (y : Y ⟶ Spec P), j₁ ≫ y = p₁ ≫ Spec.map f₁ → j₂ ≫ y = p₂ ≫ Spec.map f₂ → ∀ V : Y.Opens, IsAffineOpen V → (y.appLE ⊤ V (fun _ _ => trivial)).hom.Flat ∧ IsPushout (y.appLE ⊤ V (fun _ _ => trivial)) (Spec.map f₁).appTop (j₁.app V) (p₁.appLE ⊤ (j₁ ⁻¹ᵁ V) (fun _ _ => trivial)) ∧ IsPushout (y.appLE ⊤ V (fun _ _ => trivial)) (Spec.map f₂).appTop (j₂.app V) (p₂.appLE ⊤ (j₂ ⁻¹ᵁ V) (fun _ _ => trivial)) := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hs₁ hs₂ hn₁ hn₂ Y₁ Y₂ Y₀ p₁ p₂ p₀ i₁ i₂ h₁ h₂ hF₁ hF₂ Y j₁ j₂ hw
    hj₁ hj₂ hV y hy₁ hy₂ V hVa
  have hU₁ : IsAffineOpen (j₁ ⁻¹ᵁ V) := hVa.preimage j₁
  have hU₂ : IsAffineOpen (j₂ ⁻¹ᵁ V) := hVa.preimage j₂
  have hPT : IsPullback (Spec.map f₁).appTop (Spec.map f₂).appTop (Spec.map g₁).appTop
      (Spec.map g₂).appTop :=
    IsPullback.of_iso hP (Scheme.ΓSpecIso P).symm (Scheme.ΓSpecIso R₁).symm
      (Scheme.ΓSpecIso R₂).symm (Scheme.ΓSpecIso R₀).symm
      (inv_comp_appTop _ _ f₁).symm (inv_comp_appTop _ _ f₂).symm
      (inv_comp_appTop _ _ g₁).symm (inv_comp_appTop _ _ g₂).symm
  have q₁ := pushout_of_eq Y₁ Y₀ (Spec R₁) (Spec R₀) i₁ p₀ p₁ (Spec.map g₁) h₁ (j₁ ⁻¹ᵁ V) hU₁
    ((i₁ ≫ j₁) ⁻¹ᵁ V) rfl
  have q₂ := pushout_of_eq Y₂ Y₀ (Spec R₂) (Spec R₀) i₂ p₀ p₂ (Spec.map g₂) h₂ (j₂ ⁻¹ᵁ V) hU₂
    ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; rfl)
  have c₁ : y.appLE ⊤ V (fun _ _ => trivial) ≫ j₁.app V =
      (Spec.map f₁).appTop ≫ p₁.appLE ⊤ (j₁ ⁻¹ᵁ V) (fun _ _ => trivial) := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    refine (Scheme.Hom.appLE_comp_appLE j₁ y _ _ _ _ _).trans ?_
    refine Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE p₁ (Spec.map f₁) _ _ _ _ _).symm
    simp only [hy₁]
  have c₂ : y.appLE ⊤ V (fun _ _ => trivial) ≫ j₂.app V =
      (Spec.map f₂).appTop ≫ p₂.appLE ⊤ (j₂ ⁻¹ᵁ V) (fun _ _ => trivial) := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    refine (Scheme.Hom.appLE_comp_appLE j₂ y _ _ _ _ _).trans ?_
    refine Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE p₂ (Spec.map f₂) _ _ _ _ _).symm
    simp only [hy₂]
  exact GlobalTheory.T.schlessinger_flat_fibreProduct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hPT (surjTop g₁ hs₁) (surjTop g₂ hs₂)
    (nilTop g₁ hn₁) (nilTop g₂ hn₂) q₁ q₂
    (p₁.flat_appLE (isAffineOpen_top _) hU₁ le_top) (p₂.flat_appLE (isAffineOpen_top _) hU₂ le_top)
    (hV V) c₁ c₂
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ferrandPushout_affine_flat_and_pushouts : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → IsNilpotent (RingHom.ker g₁.hom) → IsNilpotent (RingHom.ker g₂.hom) → ∀ (Y₁ Y₂ Y₀ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec R₁) (p₂ : Y₂ ⟶ Spec R₂) (p₀ : Y₀ ⟶ Spec R₀) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsPullback i₁ p₀ p₁ (Spec.map g₁) → IsPullback i₂ p₀ p₂ (Spec.map g₂) → Flat p₁ → Flat p₂ → ∀ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂), IsClosedImmersion j₁ → IsClosedImmersion j₂ → (∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) → ∀ (y : Y ⟶ Spec P), j₁ ≫ y = p₁ ≫ Spec.map f₁ → j₂ ≫ y = p₂ ≫ Spec.map f₂ → ∀ V : Y.Opens, IsAffineOpen V → (y.appLE ⊤ V (fun _ _ => trivial)).hom.Flat ∧ IsPushout (y.appLE ⊤ V (fun _ _ => trivial)) (Spec.map f₁).appTop (j₁.app V) (p₁.appLE ⊤ (j₁ ⁻¹ᵁ V) (fun _ _ => trivial)) ∧ IsPushout (y.appLE ⊤ V (fun _ _ => trivial)) (Spec.map f₂).appTop (j₂.app V) (p₂.appLE ⊤ (j₂ ⁻¹ᵁ V) (fun _ _ => trivial)) := by
  atlas_forward_decl GlobalTheory.SchlessingerAffine.flat_and_pushouts
end

section
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option autoImplicit false

namespace GlobalTheory.FerrandFlat

theorem flat_of_appLE {Y : Scheme.{0}} {P : CommRingCat.{0}} (y : Y ⟶ Spec P) (h : ∀ V : Y.Opens, IsAffineOpen V → (y.appLE ⊤ V (fun _ _ => trivial)).hom.Flat) : Flat y :=
  HasRingHomProperty.of_iSup_eq_top (P := @Flat) (fun V : Y.affineOpens => V) (iSup_affineOpens_eq_top Y) (fun V => h V.1 V.2)

theorem flat_pushout : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → IsNilpotent (RingHom.ker g₁.hom) → IsNilpotent (RingHom.ker g₂.hom) → ∀ (Y₁ Y₂ Y₀ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec R₁) (p₂ : Y₂ ⟶ Spec R₂) (p₀ : Y₀ ⟶ Spec R₀) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsPullback i₁ p₀ p₁ (Spec.map g₁) → IsPullback i₂ p₀ p₂ (Spec.map g₂) → Flat p₁ → Flat p₂ → ∀ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂), IsClosedImmersion j₁ → IsClosedImmersion j₂ → (∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) → ∀ (y : Y ⟶ Spec P), j₁ ≫ y = p₁ ≫ Spec.map f₁ → j₂ ≫ y = p₂ ≫ Spec.map f₂ → IsPullback j₁ p₁ y (Spec.map f₁) ∧ IsPullback j₂ p₂ y (Spec.map f₂) ∧ Flat y := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hg₁ hg₂ hn₁ hn₂ Y₁ Y₂ Y₀ p₁ p₂ p₀ i₁ i₂ h₁ h₂ hf₁ hf₂ Y j₁ j₂ hw hj₁ hj₂ hV y hy₁ hy₂
  have H := GlobalTheory.T.ferrandPushout_affine_flat_and_pushouts P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hg₁ hg₂ hn₁ hn₂ Y₁ Y₂ Y₀ p₁ p₂ p₀ i₁ i₂ h₁ h₂ hf₁ hf₂ Y j₁ j₂ hw
    hj₁ hj₂ hV y hy₁ hy₂
  exact ⟨GlobalTheory.T.isPullback_of_isAffine_of_forall_isPushout_appLE _ _ _ _ j₁ p₁ y (Spec.map f₁) inferInstance inferInstance inferInstance hy₁
      (fun V hV => (H V hV).2.1),
    GlobalTheory.T.isPullback_of_isAffine_of_forall_isPushout_appLE _ _ _ _ j₂ p₂ y (Spec.map f₂) inferInstance inferInstance inferInstance hy₂
      (fun V hV => (H V hV).2.2),
    flat_of_appLE y (fun V hV => (H V hV).1)⟩

end GlobalTheory.FerrandFlat
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_ferrandPushout_over_fibreProduct : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → IsNilpotent (RingHom.ker g₁.hom) → IsNilpotent (RingHom.ker g₂.hom) → ∀ (Y₁ Y₂ Y₀ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec R₁) (p₂ : Y₂ ⟶ Spec R₂) (p₀ : Y₀ ⟶ Spec R₀) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsPullback i₁ p₀ p₁ (Spec.map g₁) → IsPullback i₂ p₀ p₂ (Spec.map g₂) → Flat p₁ → Flat p₂ → ∀ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂), IsClosedImmersion j₁ → IsClosedImmersion j₂ → (∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) → ∀ (y : Y ⟶ Spec P), j₁ ≫ y = p₁ ≫ Spec.map f₁ → j₂ ≫ y = p₂ ≫ Spec.map f₂ → IsPullback j₁ p₁ y (Spec.map f₁) ∧ IsPullback j₂ p₂ y (Spec.map f₂) ∧ Flat y := by
  atlas_forward_decl GlobalTheory.FerrandFlat.flat_pushout
end

section
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PinchDeg

theorem elem_of_isPullback {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂}
    {g₁ : R₁ ⟶ R₀} {g₂ : R₂ ⟶ R₀} (hP : IsPullback f₁ f₂ g₁ g₂) :
    (∀ x y, f₁.hom x = f₁.hom y → f₂.hom x = f₂.hom y → x = y) ∧
      ∀ a b, g₁.hom a = g₂.hom b → ∃ x, f₁.hom x = a ∧ f₂.hom x = b := by
  have H := (Types.isPullback_iff _ _ _ _).1 (hP.map (forget CommRingCat))
  exact ⟨fun x y hx hy ↦ H.2.1 x y ⟨hx, hy⟩, fun a b h ↦ H.2.2 a b h⟩

theorem subsingleton_or_subsingleton {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂}
    {g₁ : R₁ ⟶ R₀} {g₂ : R₂ ⟶ R₀} (hP : IsPullback f₁ f₂ g₁ g₂) [Subsingleton R₀]
    [IsLocalRing P] : Subsingleton R₁ ∨ Subsingleton R₂ := by
  obtain ⟨hinj, hex⟩ := elem_of_isPullback hP
  obtain ⟨e, he₁, he₂⟩ := hex 1 0 (Subsingleton.elim _ _)
  have hidem : e * e = e := hinj _ _ (by simp [he₁]) (by simp [he₂])
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
  · have h1 : e = 1 := by
      obtain ⟨u, rfl⟩ := hu
      simpa using congrArg (fun t ↦ t * (↑u⁻¹ : P)) hidem
    right
    rw [h1, map_one] at he₂
    exact subsingleton_of_zero_eq_one he₂.symm
  · have h0 : 1 - e = 1 := by
      have hid : (1 - e) * (1 - e) = 1 - e := by
        rw [sub_mul, one_mul, mul_sub, mul_one, hidem, sub_self, sub_zero]
      obtain ⟨u, hu⟩ := hu
      rw [← hu] at hid ⊢
      simpa using congrArg (fun t ↦ t * (↑u⁻¹ : P)) hid
    have he : e = 0 := by
      have := congrArg (fun t ↦ 1 - t) h0
      simpa using this
    left
    rw [he, map_zero] at he₁
    exact subsingleton_of_zero_eq_one he₁

theorem glue_of_subsingleton_right (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂)
    (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀) (hP : IsPullback f₁ f₂ g₁ g₂) [Subsingleton R₀]
    [Subsingleton R₂] (Y₁ : Over (Spec R₁)) (Y₂ : Over (Spec R₂)) (Y₀ : Over (Spec R₀))
    (i₁ : Y₀.left ⟶ Y₁.left) (i₂ : Y₀.left ⟶ Y₂.left) (hY₁ : Flat Y₁.hom) :
    ∃ (Y : Over (Spec P)) (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left),
      IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) ∧ IsPullback j₂ Y₂.hom Y.hom (Spec.map f₂) ∧
        Flat Y.hom ∧ IsPushout i₁ i₂ j₁ j₂ := by
  obtain ⟨hinj, hex⟩ := elem_of_isPullback hP
  have hbij : Function.Bijective f₁.hom :=
    ⟨fun x y h ↦ hinj x y h (Subsingleton.elim _ _),
      fun a ↦ (hex a 0 (Subsingleton.elim _ _)).imp fun x hx ↦ hx.1⟩
  haveI : IsIso f₁ := (ConcreteCategory.isIso_iff_bijective _).2 hbij
  haveI : IsEmpty (Spec R₂) := inferInstanceAs (IsEmpty (PrimeSpectrum R₂))
  haveI : IsEmpty Y₂.left := ⟨fun x ↦ isEmptyElim (Y₂.hom.base x)⟩
  haveI : IsEmpty Y₀.left := ⟨fun x ↦ isEmptyElim (i₂.base x)⟩
  let Y : Over (Spec P) := Over.mk (Y₁.hom ≫ Spec.map f₁)
  refine ⟨Y, 𝟙 _, isInitialOfIsEmpty.to _, ?_, ?_, ?_, ?_⟩
  · exact IsPullback.of_horiz_isIso ⟨by simp [Y]⟩
  · have hpb := IsPullback.of_hasPullback Y.hom (Spec.map f₂)
    haveI : IsEmpty ((pullback Y.hom (Spec.map f₂) : Scheme.{0})) :=
      ⟨fun x ↦ isEmptyElim ((pullback.snd Y.hom (Spec.map f₂)).base x)⟩
    let e : pullback Y.hom (Spec.map f₂) ≅ Y₂.left :=
      isInitialOfIsEmpty.uniqueUpToIso isInitialOfIsEmpty
    refine IsPullback.of_iso hpb e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    all_goals first
      | exact isInitialOfIsEmpty.hom_ext _ _
      | simp
  · show Flat (Y₁.hom ≫ Spec.map f₁)
    infer_instance
  · haveI : IsIso i₂ := ⟨isInitialOfIsEmpty.to _, isInitialOfIsEmpty.hom_ext _ _,
      isInitialOfIsEmpty.hom_ext _ _⟩
    exact IsPushout.of_vert_isIso ⟨isInitialOfIsEmpty.hom_ext _ _⟩

theorem glue_of_subsingleton : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → Subsingleton R₀ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y₁ : Over (Spec R₁)) (Y₂ : Over (Spec R₂)) (Y₀ : Over (Spec R₀)) (i₁ : Y₀.left ⟶ Y₁.left) (i₂ : Y₀.left ⟶ Y₂.left), IsPullback i₁ Y₀.hom Y₁.hom (Spec.map g₁) → IsPullback i₂ Y₀.hom Y₂.hom (Spec.map g₂) → Flat Y₁.hom → Flat Y₂.hom → ∃ (Y : Over (Spec P)) (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left), IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) ∧ IsPullback j₂ Y₂.hom Y.hom (Spec.map f₂) ∧ Flat Y.hom ∧ IsPushout i₁ i₂ j₁ j₂ := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP h₀ hloc _ _ _ Y₁ Y₂ Y₀ i₁ i₂ _ _ hY₁ hY₂
  rcases subsingleton_or_subsingleton hP with h₁ | h₂
  · obtain ⟨Y, j₂, j₁, hp₂, hp₁, hf, hpo⟩ :=
      glue_of_subsingleton_right P R₂ R₁ R₀ f₂ f₁ g₂ g₁ hP.flip Y₂ Y₁ Y₀ i₂ i₁ hY₂
    exact ⟨Y, j₁, j₂, hp₁, hp₂, hf, hpo.flip⟩
  · exact glue_of_subsingleton_right P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP Y₁ Y₂ Y₀ i₁ i₂ hY₁

end GlobalTheory.PinchDeg
end
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glue_flat_over_pullback_of_subsingleton : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → Subsingleton R₀ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y₁ : Over (Spec R₁)) (Y₂ : Over (Spec R₂)) (Y₀ : Over (Spec R₀)) (i₁ : Y₀.left ⟶ Y₁.left) (i₂ : Y₀.left ⟶ Y₂.left), IsPullback i₁ Y₀.hom Y₁.hom (Spec.map g₁) → IsPullback i₂ Y₀.hom Y₂.hom (Spec.map g₂) → Flat Y₁.hom → Flat Y₂.hom → ∃ (Y : Over (Spec P)) (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left), IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) ∧ IsPullback j₂ Y₂.hom Y.hom (Spec.map f₂) ∧ Flat Y.hom ∧ IsPushout i₁ i₂ j₁ j₂ := by
  atlas_forward_decl GlobalTheory.PinchDeg.glue_of_subsingleton
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

set_option autoImplicit false

namespace GlobalTheory.FerrandGlue

theorem kernel_nilpotent : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₂ → Nontrivial R₀ → IsNilpotent (RingHom.ker g₁.hom) := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hg₂ hR₀
  have hT := (Types.isPullback_iff _ _ _ _).1 (hP.map (forget CommRingCat))
  have hf₁ : Function.Surjective f₁ := by
    intro r
    obtain ⟨s, hs⟩ := hg₂ (g₁ r)
    obtain ⟨p, hp, -⟩ := hT.2.2 r s hs.symm
    exact ⟨p, hp⟩
  let J : Ideal P := (RingHom.ker g₁.hom).comap f₁.hom
  have hJ : J ≤ IsLocalRing.maximalIdeal P := IsLocalRing.le_maximalIdeal (by
    intro h
    have h1 : (1 : P) ∈ J := h ▸ Submodule.mem_top
    simp [J] at h1)
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := P)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
  refine ⟨n, ?_⟩
  have hmap : RingHom.ker g₁.hom = J.map f₁.hom := (Ideal.map_comap_of_surjective _ hf₁ _).symm
  rw [hmap, ← Ideal.map_pow, Ideal.zero_eq_bot, eq_bot_iff]
  calc (J ^ n).map f₁.hom ≤ ((IsLocalRing.maximalIdeal P) ^ n).map f₁.hom := Ideal.map_mono (Ideal.pow_right_mono hJ n)
    _ = ⊥ := by rw [hn, Ideal.zero_eq_bot, Ideal.map_bot]

theorem thickening_of_isPullback : ∀ (R₁ R₀ : CommRingCat.{0}) (g : R₁ ⟶ R₀) (Y₁ Y₀ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec R₁) (p₀ : Y₀ ⟶ Spec R₀) (i : Y₀ ⟶ Y₁), IsPullback i p₀ p₁ (Spec.map g) → Function.Surjective g → IsNilpotent (RingHom.ker g.hom) → IsClosedImmersion i ∧ Surjective i := by
  intro R₁ R₀ g Y₁ Y₀ p₁ p₀ i h hg hn
  have hc : IsClosedImmersion (Spec.map g) := IsClosedImmersion.spec_of_surjective g hg
  have hs : Surjective (Spec.map g) := by
    constructor
    intro x
    obtain ⟨n, hn⟩ := hn
    have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker g.hom : Set R₁) := fun a ha => by
      refine x.isPrime.mem_of_pow_mem n ?_
      have := Ideal.pow_mem_pow ha n
      rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this
      rw [this]
      exact zero_mem _
    rw [← range_comap_of_surjective _ g.hom hg] at hx
    exact hx
  exact ⟨MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip hc,
    MorphismProperty.of_isPullback (P := @Surjective) h.flip hs⟩

theorem ferrand_glue_artinian : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y₁ : Over (Spec R₁)) (Y₂ : Over (Spec R₂)) (Y₀ : Over (Spec R₀)) (i₁ : Y₀.left ⟶ Y₁.left) (i₂ : Y₀.left ⟶ Y₂.left), IsPullback i₁ Y₀.hom Y₁.hom (Spec.map g₁) → IsPullback i₂ Y₀.hom Y₂.hom (Spec.map g₂) → Flat Y₁.hom → Flat Y₂.hom → ∃ (Y : Over (Spec P)) (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left), IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) ∧ IsPullback j₂ Y₂.hom Y.hom (Spec.map f₂) ∧ Flat Y.hom ∧ IsPushout i₁ i₂ j₁ j₂ := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hg₁ hg₂ Y₁ Y₂ Y₀ i₁ i₂ h₁ h₂ hf₁ hf₂
  by_cases hR₀ : Subsingleton R₀
  · exact GlobalTheory.T.glue_flat_over_pullback_of_subsingleton P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hR₀ hloc hart hg₁ hg₂ Y₁ Y₂ Y₀ i₁ i₂ h₁ h₂ hf₁ hf₂
  rw [not_subsingleton_iff_nontrivial] at hR₀
  have hn₁ := kernel_nilpotent P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hg₂ hR₀
  have hn₂ := kernel_nilpotent P R₂ R₁ R₀ f₂ f₁ g₂ g₁ hP.flip hloc hart hg₁ hR₀
  obtain ⟨hc₁, hs₁⟩ := thickening_of_isPullback R₁ R₀ g₁ Y₁.left Y₀.left Y₁.hom Y₀.hom i₁ h₁ hg₁ hn₁
  obtain ⟨hc₂, hs₂⟩ := thickening_of_isPullback R₂ R₀ g₂ Y₂.left Y₀.left Y₂.hom Y₀.hom i₂ h₂ hg₂ hn₂
  obtain ⟨Y, j₁, j₂, hw, hpo, hj₁, hj₂, hV⟩ := GlobalTheory.T.exists_pushout_of_nilpotent_thickenings' Y₀.left Y₁.left Y₂.left i₁ i₂ hc₁ hc₂ hs₁ hs₂
    (GlobalTheory.T.isNilpotent_ker_app_of_isPullback_of_nilpotent R₁ R₀ g₁ Y₁.left Y₀.left Y₁.hom Y₀.hom i₁ h₁ hg₁ hn₁)
    (GlobalTheory.T.isNilpotent_ker_app_of_isPullback_of_nilpotent R₂ R₀ g₂ Y₂.left Y₀.left Y₂.hom Y₀.hom i₂ h₂ hg₂ hn₂)
  have hcomm : i₁ ≫ Y₁.hom ≫ Spec.map f₁ = i₂ ≫ Y₂.hom ≫ Spec.map f₂ := by
    rw [← Category.assoc, h₁.w, ← Category.assoc, h₂.w, Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hP.w]
  let y : Y ⟶ Spec P := hpo.desc (Y₁.hom ≫ Spec.map f₁) (Y₂.hom ≫ Spec.map f₂) hcomm
  obtain ⟨k₁, k₂, kf⟩ := GlobalTheory.T.flat_ferrandPushout_over_fibreProduct P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hg₁ hg₂ hn₁ hn₂ Y₁.left Y₂.left Y₀.left Y₁.hom Y₂.hom Y₀.hom i₁ i₂ h₁ h₂ hf₁ hf₂ Y j₁ j₂ hw hj₁ hj₂ hV y (hpo.inl_desc _ _ _) (hpo.inr_desc _ _ _)
  exact ⟨Over.mk y, j₁, j₂, k₁, k₂, kf, hpo⟩

end GlobalTheory.FerrandGlue
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ferrand_glue_flat_artinian_fibreProduct : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y₁ : Over (Spec R₁)) (Y₂ : Over (Spec R₂)) (Y₀ : Over (Spec R₀)) (i₁ : Y₀.left ⟶ Y₁.left) (i₂ : Y₀.left ⟶ Y₂.left), IsPullback i₁ Y₀.hom Y₁.hom (Spec.map g₁) → IsPullback i₂ Y₀.hom Y₂.hom (Spec.map g₂) → Flat Y₁.hom → Flat Y₂.hom → ∃ (Y : Over (Spec P)) (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left), IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) ∧ IsPullback j₂ Y₂.hom Y.hom (Spec.map f₂) ∧ Flat Y.hom ∧ IsPushout i₁ i₂ j₁ j₂ := by
  atlas_forward_decl GlobalTheory.FerrandGlue.ferrand_glue_artinian
end
