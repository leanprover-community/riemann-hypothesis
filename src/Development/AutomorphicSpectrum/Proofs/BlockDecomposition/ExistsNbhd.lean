import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import BuildAid.ForwardExisting

section
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.SectionNbhd

theorem isAffine_subscheme_ker_sq :
    ∀ (R : Type) [CommRing R] (U : Scheme.{0}) (t : U ⟶ Sp R) (e : Sp R ⟶ U)
      [IsClosedImmersion e], e ≫ t = 𝟙 _ → IsAffine (e.ker ^ 2).subscheme := by
  intro R _ U t e _ het
  have hte : ∀ q : Sp R, t (e q) = q := fun q => by
    have := congr($(het) q)
    simpa using this
  set c := (e.ker ^ 2).subschemeι with hc
  have hrange : ∀ x, ∃ q : Sp R, c x = e q := by
    intro x
    have h1 : c x ∈ Set.range c := ⟨x, rfl⟩
    rw [hc, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.support_pow _ _ two_ne_zero, Scheme.Hom.support_ker,
      e.isClosedEmbedding.isClosed_range.closure_eq] at h1
    obtain ⟨q, hq⟩ := h1
    exact ⟨q, hq.symm⟩
  have haff : IsAffineHom (c ≫ t) := by
    refine isAffineHom_of_forall_exists_isAffineOpen _ fun y => ?_
    obtain ⟨V₀, hV₀, hyV₀, -⟩ :=
      exists_isAffineOpen_mem_and_subset (x := e y) (U := ⊤) trivial
    obtain ⟨f, hfle, hyf⟩ := (isAffineOpen_top (Sp R)).exists_basicOpen_le
      (V := e ⁻¹ᵁ V₀) ⟨y, hyV₀⟩ trivial
    refine ⟨(Sp R).basicOpen f, hyf, (isAffineOpen_top (Sp R)).basicOpen f, ?_⟩
    have hV : IsAffineOpen (V₀ ⊓ t ⁻¹ᵁ (Sp R).basicOpen f) := by
      rw [Scheme.preimage_basicOpen]
      have h := Scheme.basicOpen_res U (V := V₀) (t.app ⊤ f) (homOfLE le_top).op
      rw [← h]
      exact hV₀.basicOpen _
    have heq : (c ≫ t) ⁻¹ᵁ (Sp R).basicOpen f = c ⁻¹ᵁ (V₀ ⊓ t ⁻¹ᵁ (Sp R).basicOpen f) := by
      ext x
      constructor
      · intro hx
        have hx' : t (c x) ∈ (Sp R).basicOpen f := hx
        refine ⟨?_, hx'⟩
        obtain ⟨q, hq⟩ := hrange x
        rw [hq, hte] at hx'
        have : e q ∈ V₀ := hfle hx'
        simpa [hq] using this
      · intro hx
        exact hx.2
    rw [heq]
    exact hV.preimage c
  exact isAffine_of_isAffineHom (c ≫ t)

end GlobalTheory.CompanionTheory.SectionNbhd
end

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_zero_neighbourhood_affine : ∀ (R : Type) [CommRing R] (U : Scheme.{0}) (t : U ⟶ Sp R) (e : Sp R ⟶ U) [IsClosedImmersion e], e ≫ t = 𝟙 _ → IsAffine (e.ker ^ 2).subscheme := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SectionNbhd.isAffine_subscheme_ker_sq
end

section
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.FirstOrderNbhd

theorem comp_app_eq_zero {E T U : Scheme.{0}} (c : E ⟶ U) (i' : T ⟶ E) (W : U.Opens)
    (a' : Γ(U, W)) (a : Γ(E, ⊤)) (h : c.app W a' = E.presheaf.map (homOfLE le_top).op a)
    (ha : i'.appTop a = 0) : (i' ≫ c).app W a' = 0 := by
  have ha0 : i'.app ⊤ a = 0 := ha
  have key : (i' ≫ c).app W a' = i'.app (c ⁻¹ᵁ W) (c.app W a') := by
    rw [Scheme.Hom.comp_app]
    try rfl
  have nat : i'.app (c ⁻¹ᵁ W) (E.presheaf.map (homOfLE (le_top : c ⁻¹ᵁ W ≤ ⊤)).op a)
      = T.presheaf.map (homOfLE (le_top : i' ⁻¹ᵁ c ⁻¹ᵁ W ≤ ⊤)).op (i'.app ⊤ a) := by
    rw [← CategoryTheory.comp_apply, Scheme.Hom.naturality, CategoryTheory.comp_apply]
    try rfl
  rw [key, h, nat, ha0]
  exact map_zero _

theorem exists_mem_ideal_of_lift {T U : Scheme.{0}} (e : T ⟶ U) [QuasiCompact e]
    (i' : T ⟶ (e.ker ^ 2).subscheme) (hi : i' ≫ (e.ker ^ 2).subschemeι = e)
    (W : U.affineOpens) (a : Γ((e.ker ^ 2).subscheme, ⊤)) (ha : i'.appTop a = 0) :
    ∃ a' ∈ e.ker.ideal W, (e.ker ^ 2).subschemeι.app W a' =
      (e.ker ^ 2).subscheme.presheaf.map (homOfLE le_top).op a := by
  obtain ⟨a', ha'⟩ := (e.ker ^ 2).subschemeι_app_surjective W
    ((e.ker ^ 2).subscheme.presheaf.map (homOfLE le_top).op a)
  refine ⟨a', ?_, ha'⟩
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
  have h0 := comp_app_eq_zero (e.ker ^ 2).subschemeι i' (W : U.Opens) a' a ha' ha
  rw [hi] at h0
  exact h0

theorem mul_eq_zero_of_lift {T U : Scheme.{0}} (e : T ⟶ U) [QuasiCompact e]
    (i' : T ⟶ (e.ker ^ 2).subscheme) (hi : i' ≫ (e.ker ^ 2).subschemeι = e)
    (a b : Γ((e.ker ^ 2).subscheme, ⊤)) (ha : i'.appTop a = 0) (hb : i'.appTop b = 0) :
    a * b = 0 := by
  refine TopCat.Presheaf.section_ext (e.ker ^ 2).subscheme.sheaf ⊤ (a * b) 0 ?_
  intro x hx
  obtain ⟨W, hW, hxW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := (e.ker ^ 2).subschemeι.base x) (U := ⊤) trivial
  let W' : U.affineOpens := ⟨W, hW⟩
  have hxW' : x ∈ (e.ker ^ 2).subschemeι ⁻¹ᵁ (W' : U.Opens) := hxW
  obtain ⟨a', ha'I, ha'⟩ := exists_mem_ideal_of_lift e i' hi W' a ha
  obtain ⟨b', hb'I, hb'⟩ := exists_mem_ideal_of_lift e i' hi W' b hb
  have hab : (e.ker ^ 2).subschemeι.app (W' : U.Opens) (a' * b') = 0 := by
    have hmem : a' * b' ∈ (e.ker ^ 2).ideal W' := by
      rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, sq]
      exact Ideal.mul_mem_mul ha'I hb'I
    rw [← Scheme.IdealSheafData.ker_subschemeι_app, RingHom.mem_ker] at hmem
    exact hmem
  have key : (e.ker ^ 2).subscheme.presheaf.map
      (homOfLE (le_top : (e.ker ^ 2).subschemeι ⁻¹ᵁ (W' : U.Opens) ≤ ⊤)).op (a * b) = 0 := by
    rw [map_mul, ← ha', ← hb', ← map_mul, hab]
  have h1 := TopCat.Presheaf.germ_res_apply (e.ker ^ 2).subscheme.presheaf
    (homOfLE (le_top : (e.ker ^ 2).subschemeι ⁻¹ᵁ (W' : U.Opens) ≤ ⊤)) x hxW' (a * b)
  rw [key, map_zero] at h1
  rw [map_zero]
  exact h1.symm

theorem ideal_sq_zero : ∀ (R : Type) [CommRing R] (U : Scheme.{0}) (e : Sp R ⟶ U)
    [IsClosedImmersion e] (i' : Sp R ⟶ (e.ker ^ 2).subscheme),
    i' ≫ (e.ker ^ 2).subschemeι = e → ∀ a b : Γ((e.ker ^ 2).subscheme, ⊤),
    i'.appTop a = 0 → i'.appTop b = 0 → a * b = 0 := by
  intro R _ U e _ i' hi a b ha hb
  exact mul_eq_zero_of_lift e i' hi a b ha hb

end GlobalTheory.CompanionTheory.FirstOrderNbhd
end

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_zero_neighbourhood_product_zero : ∀ (R : Type) [CommRing R] (U : Scheme.{0}) (e : Sp R ⟶ U) [IsClosedImmersion e] (i' : Sp R ⟶ (e.ker ^ 2).subscheme), i' ≫ (e.ker ^ 2).subschemeι = e → ∀ a b : Γ((e.ker ^ 2).subscheme, ⊤), i'.appTop a = 0 → i'.appTop b = 0 → a * b = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FirstOrderNbhd.ideal_sq_zero
end

section
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.CotKer

theorem mul_eq_zero_top {Q B : Type} [CommRing Q] [CommRing B] (q : Q →+* B)
    (hq : ∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) (a b : Γ(Sp Q, ⊤))
    (ha : (spMap q).appTop.hom a = 0) (hb : (spMap q).appTop.hom b = 0) : a * b = 0 := by
  have key : ∀ x : Γ(Sp Q, ⊤), (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((spMap q).appTop.hom x) =
      q ((Scheme.ΓSpecIso (CommRingCat.of Q)).hom.hom x) := fun x =>
    congrArg (fun f => CommRingCat.Hom.hom f x) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom q))
  have hφ : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of Q)).hom.hom := by
    intro x y hxy
    have h := congrArg (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom hxy
    simpa using h
  apply hφ
  rw [map_mul, map_zero]
  apply hq
  · rw [← key, ha, map_zero]
  · rw [← key, hb, map_zero]

theorem ker_sq_eq_bot {Q B : Type} [CommRing Q] [CommRing B] (q : Q →+* B)
    (hq : ∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) : (spMap q).ker ^ 2 = ⊥ := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
    Scheme.Hom.ker_apply, pow_two, eq_bot_iff, Ideal.mul_le]
  intro a ha b hb
  exact (Submodule.mem_bot _).mpr (mul_eq_zero_top q hq a b ha hb)

theorem mul_eq_zero_affine {Q B : Type} [CommRing Q] [CommRing B] (q : Q →+* B)
    (hq : ∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) (W : (Sp Q).affineOpens) (a b : Γ(Sp Q, W.1))
    (ha : ((spMap q).app W.1).hom a = 0) (hb : ((spMap q).app W.1).hom b = 0) : a * b = 0 := by
  have h := congrArg (fun I => Scheme.IdealSheafData.ideal I W) (ker_sq_eq_bot q hq)
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.IdealSheafData.ideal_bot,
    Pi.bot_apply, Scheme.Hom.ker_apply] at h
  have hab : a * b ∈ (RingHom.ker ((spMap q).app W.1).hom) ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul ha hb
  rw [h] at hab
  exact (Submodule.mem_bot _).mp hab

theorem mul_eq_zero_open {Q B : Type} [CommRing Q] [CommRing B] (q : Q →+* B)
    (hq : ∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) (O : (Sp Q).Opens) (a b : Γ(Sp Q, O))
    (ha : ((spMap q).app O).hom a = 0) (hb : ((spMap q).app O).hom b = 0) : a * b = 0 := by
  refine TopCat.Sheaf.eq_of_locally_eq' (Sp Q).sheaf
    (fun W : {W : (Sp Q).affineOpens // W.1 ≤ O} => W.1.1) O (fun W => homOfLE W.2) ?_ (a * b) 0 ?_
  · intro x hx
    obtain ⟨U', hU', hxU', hle⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens (Sp Q))) hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U', hU'⟩, hle⟩, hxU'⟩
  · intro W
    have hres : ∀ s : Γ(Sp Q, O), ((spMap q).app O).hom s = 0 →
        ((spMap q).app W.1.1).hom (((Sp Q).presheaf.map (homOfLE W.2).op).hom s) = 0 := by
      intro s hs
      have h := congrArg (fun f => CommRingCat.Hom.hom f s) ((spMap q).naturality (homOfLE W.2).op)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, hs, map_zero] at h
      exact h
    show ((Sp Q).presheaf.map (homOfLE W.2).op).hom (a * b) =
      ((Sp Q).presheaf.map (homOfLE W.2).op).hom 0
    rw [map_zero, map_mul]
    exact mul_eq_zero_affine q hq W.1 _ _ (hres a ha) (hres b hb)

theorem comp_comp_apply_eq_zero {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (a : A)
    (ha : f.hom a = 0) : ((f ≫ g) ≫ h).hom a = 0 := by
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, ha, map_zero]

theorem ker_sq_le_ker : ∀ (R Q B : Type) [CommRing R] [CommRing Q] [CommRing B] (U : Scheme.{0}) (e : Sp R ⟶ U) [IsClosedImmersion e] (q : Q →+* B) (ρ : R →+* B) (y : Sp Q ⟶ U), Function.Surjective q → (∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) → spMap q ≫ y = spMap ρ ≫ e → e.ker ^ 2 ≤ y.ker := by
  intro R Q B _ _ _ U e _ q ρ y _ hq hcomm
  show _ ≤ Scheme.IdealSheafData.ofIdeals (fun V => RingHom.ker (y.app V).hom)
  rw [Scheme.IdealSheafData.le_ofIdeals_iff]
  intro V
  rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply e V, pow_two, Ideal.mul_le]
  intro a ha b hb
  rw [RingHom.mem_ker] at ha hb ⊢
  have key : ∀ s, (e.app V).hom s = 0 → ((spMap q).app (y ⁻¹ᵁ V)).hom ((y.app V).hom s) = 0 := by
    intro s hs
    have h1 : ((spMap q).app (y ⁻¹ᵁ V)).hom ((y.app V).hom s) = ((spMap q ≫ y).app V).hom s := by
      rw [Scheme.Hom.comp_app]
      rfl
    rw [h1, Scheme.Hom.congr_app hcomm V, Scheme.Hom.comp_app]
    exact comp_comp_apply_eq_zero _ _ _ s hs
  rw [map_mul]
  exact mul_eq_zero_open q hq (y ⁻¹ᵁ V) _ _ (key a ha) (key b hb)

end GlobalTheory.CompanionTheory.CotKer
end

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_square_le_kernel_of_square_zero_map : ∀ (R Q B : Type) [CommRing R] [CommRing Q] [CommRing B] (U : Scheme.{0}) (e : Sp R ⟶ U) [IsClosedImmersion e] (q : Q →+* B) (ρ : R →+* B) (y : Sp Q ⟶ U), Function.Surjective q → (∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) → spMap q ≫ y = spMap ρ ≫ e → e.ker ^ 2 ≤ y.ker := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CotKer.ker_sq_le_ker
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.CotLift

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : A →+* B) (h : B →+* C) :
    spMap h ≫ spMap g = spMap (h.comp g) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

section Ker

variable {R P : Type} [CommRing R] [CommRing P]

def KerW (_ : R →+* P) (ε : P →+* R) : Type := RingHom.ker ε

variable (α : R →+* P) (ε : P →+* R)

instance : AddCommGroup (KerW α ε) := inferInstanceAs (AddCommGroup (RingHom.ker ε))

instance : Module P (KerW α ε) := inferInstanceAs (Module P (RingHom.ker ε))

instance : Module R (KerW α ε) := Module.compHom _ α

instance : Module Rᵐᵒᵖ (KerW α ε) :=
  Module.compHom _ (RingHom.fromOpposite (RingHom.id R) fun _ _ ↦ Commute.all _ _)

instance : IsCentralScalar R (KerW α ε) := ⟨fun _ _ ↦ rfl⟩

variable {α ε}

def KerW.val (w : KerW α ε) : P := Subtype.val (p := fun x ↦ x ∈ RingHom.ker ε) w

theorem KerW.ext' {v w : KerW α ε} (h : v.val = w.val) : v = w := Subtype.ext h

@[simp] theorem KerW.val_add (v w : KerW α ε) : (v + w).val = v.val + w.val := rfl

@[simp] theorem KerW.val_smul (r : R) (w : KerW α ε) : (r • w).val = α r * w.val := rfl

@[simp] theorem KerW.val_op_smul (r : R) (w : KerW α ε) : (MulOpposite.op r • w).val = α r * w.val := rfl

@[simp] theorem KerW.val_zero : (0 : KerW α ε).val = 0 := rfl

theorem KerW.eps_val (w : KerW α ε) : ε w.val = 0 := w.2

def pr (h : ε.comp α = RingHom.id R) (a : P) : KerW α ε :=
  ⟨a - α (ε a), by
    have e : ε (α (ε a)) = ε a := congrArg (fun f ↦ f (ε a)) h
    simp [RingHom.mem_ker, e]⟩

@[simp] theorem pr_val (h : ε.comp α = RingHom.id R) (a : P) : (pr h a).val = a - α (ε a) := rfl

theorem eps_alpha (h : ε.comp α = RingHom.id R) (r : R) : ε (α r) = r := congrArg (fun f ↦ f r) h

def theta (h : ε.comp α = RingHom.id R) (hsq : ∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0) :
    P →+* TrivSqZeroExt R (KerW α ε) where
  toFun a := TrivSqZeroExt.inl (ε a) + TrivSqZeroExt.inr (pr h a)
  map_one' := by
    apply TrivSqZeroExt.ext
    · simp
    · apply KerW.ext'; simp
  map_zero' := by
    apply TrivSqZeroExt.ext
    · simp
    · apply KerW.ext'; simp
  map_add' a b := by
    apply TrivSqZeroExt.ext
    · simp
    · apply KerW.ext'; simp; ring
  map_mul' a b := by
    have e := hsq (a - α (ε a)) (b - α (ε b)) (by simp [eps_alpha h]) (by simp [eps_alpha h])
    apply TrivSqZeroExt.ext
    · simp
    · apply KerW.ext'
      simp
      linear_combination e

@[simp] theorem theta_fst (h : ε.comp α = RingHom.id R) (hsq : ∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0) (a : P) :
    (theta h hsq a).fst = ε a := by simp [theta]

@[simp] theorem theta_snd (h : ε.comp α = RingHom.id R) (hsq : ∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0) (a : P) :
    (theta h hsq a).snd = pr h a := by simp [theta]

end Ker

section Main

variable {R P B M : Type} [CommRing R] [CommRing P] [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
  [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] {α : R →+* P} {ε : P →+* R}

theorem pr_val_self (h : ε.comp α = RingHom.id R) (w : KerW α ε) : pr h w.val = w :=
  KerW.ext' (by simp [KerW.eps_val])

def uOf (φ : P →+* TrivSqZeroExt B M) (hα : φ.comp α = (TrivSqZeroExt.inlHom B M).comp (algebraMap R B))
    (hf : ∀ a, (φ a).fst = algebraMap R B (ε a)) : KerW α ε →ₗ[R] M where
  toFun w := (φ w.val).snd
  map_add' v w := by simp
  map_smul' r w := by
    have e : φ (α r) = TrivSqZeroExt.inl (algebraMap R B r) := congrArg (fun f ↦ f r) hα
    have z : (φ w.val).fst = 0 := by rw [hf, KerW.eps_val, map_zero]
    simp only [KerW.val_smul, map_mul, e, RingHom.id_apply, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.snd_inl, smul_zero, add_zero, algebraMap_smul]

theorem tsz_theta (h : ε.comp α = RingHom.id R) (hsq : ∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0)
    (φ : P →+* TrivSqZeroExt B M) (hα : φ.comp α = (TrivSqZeroExt.inlHom B M).comp (algebraMap R B))
    (hf : ∀ a, (φ a).fst = algebraMap R B (ε a)) :
    (tsz (uOf φ hα hf)).comp (theta h hsq) = φ := by
  refine RingHom.ext fun a ↦ ?_
  have e : φ (α (ε a)) = TrivSqZeroExt.inl (algebraMap R B (ε a)) := congrArg (fun f ↦ f (ε a)) hα
  have s : (uOf φ hα hf) (pr h a) = (φ a).snd := by
    change (φ (a - α (ε a))).snd = _
    simp [e]
  apply TrivSqZeroExt.ext
  · change (TrivSqZeroExt.inl (algebraMap R B (theta h hsq a).fst) +
      TrivSqZeroExt.inr ((uOf φ hα hf) (theta h hsq a).snd) : TrivSqZeroExt B M).fst = _
    simp [hf]
  · change (TrivSqZeroExt.inl (algebraMap R B (theta h hsq a).fst) +
      TrivSqZeroExt.inr ((uOf φ hα hf) (theta h hsq a).snd) : TrivSqZeroExt B M).snd = _
    simp [s]

theorem snd_tsz_theta (h : ε.comp α = RingHom.id R) (hsq : ∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0)
    (u : KerW α ε →ₗ[R] M) (w : KerW α ε) : ((tsz (B := B) u).comp (theta h hsq) w.val).snd = u w := by
  change (TrivSqZeroExt.inl (algebraMap R B (theta h hsq w.val).fst) +
    TrivSqZeroExt.inr (u (theta h hsq w.val).snd) : TrivSqZeroExt B M).snd = _
  simp [pr_val_self]

end Main

theorem isCot_of_lifting : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (e : Sp R ⟶ X) (P : Type) [CommRing P] (α : R →+* P) (ε : P →+* R) (j : Sp P ⟶ X), ε.comp α = RingHom.id R → (∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0) → j ≫ s = spMap α → spMap ε ≫ j = e → Mono j → (∀ (Q B : Type) [CommRing Q] [CommRing B] (q : Q →+* B) (ρ : R →+* B) (y : Sp Q ⟶ X), Function.Surjective q → (∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) → spMap q ≫ y = spMap ρ ≫ e → ∃ φ : P →+* Q, spMap φ ≫ j = y) → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module R W) (_ : Module Rᵐᵒᵖ W) (_ : IsCentralScalar R W) (y₀ : Sp (TrivSqZeroExt R W) ⟶ X), IsCot s e W y₀ := by
  intro R _ X s e P _ α ε j h hsq hj hje hm hlift
  haveI := hm
  refine ⟨KerW α ε, inferInstance, inferInstance, inferInstance, inferInstance, spMap (theta h hsq) ≫ j, ?_⟩
  unfold IsCot
  refine ⟨?_, ?_, ?_⟩
  · have e1 : (theta h hsq).comp α = TrivSqZeroExt.inlHom R (KerW α ε) := by
      refine RingHom.ext fun r ↦ TrivSqZeroExt.ext ?_ (KerW.ext' ?_)
      · simp [eps_alpha h]
      · simp [eps_alpha h]
    rw [Category.assoc, hj, spMap_comp_spMap, e1]
  · have e1 : (TrivSqZeroExt.fstHom R R (KerW α ε)).toRingHom.comp (theta h hsq) = ε :=
      RingHom.ext fun a ↦ theta_fst h hsq a
    rw [← Category.assoc, spMap_comp_spMap, e1, hje]
  · intro B _ _ M _ _ _ _ _ _ y hy1 hy2
    obtain ⟨φ, hφ⟩ := hlift (TrivSqZeroExt B M) B (TrivSqZeroExt.fstHom B B M).toRingHom (algebraMap R B) y
      (fun b ↦ ⟨TrivSqZeroExt.inl b, rfl⟩)
      (fun a b ha hb ↦ by
        have ha' : a.fst = 0 := ha
        have hb' : b.fst = 0 := hb
        apply TrivSqZeroExt.ext <;> simp [ha', hb']) hy2
    have hα : φ.comp α = (TrivSqZeroExt.inlHom B M).comp (algebraMap R B) := spMap_inj (by
      rw [← spMap_comp_spMap, ← hj, ← Category.assoc, hφ, hy1])
    have hf : (TrivSqZeroExt.fstHom B B M).toRingHom.comp φ = (algebraMap R B).comp ε :=
      spMap_inj ((cancel_mono j).1 (by
        rw [← spMap_comp_spMap, Category.assoc, hφ, hy2, ← spMap_comp_spMap, Category.assoc, hje]))
    have hf' : ∀ a, (φ a).fst = algebraMap R B (ε a) := fun a ↦ congrArg (fun f ↦ f a) hf
    refine ⟨uOf φ hα hf', ?_, ?_⟩
    · change y = spMap (tsz (uOf φ hα hf')) ≫ spMap (theta h hsq) ≫ j
      rw [← Category.assoc, spMap_comp_spMap, tsz_theta, hφ]
    · intro u' hu'
      have e1 : (tsz u').comp (theta h hsq) = φ := spMap_inj ((cancel_mono j).1 (by
        rw [← spMap_comp_spMap, Category.assoc, hφ]
        exact hu'.symm))
      refine LinearMap.ext fun w ↦ ?_
      rw [← snd_tsz_theta (B := B) h hsq u' w, e1]
      rfl

end GlobalTheory.CompanionTheory.CotLift
end
end

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_immersion_universal_square_zero : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (e : Sp R ⟶ X) (P : Type) [CommRing P] (α : R →+* P) (ε : P →+* R) (j : Sp P ⟶ X), ε.comp α = RingHom.id R → (∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0) → j ≫ s = spMap α → spMap ε ≫ j = e → Mono j → (∀ (Q B : Type) [CommRing Q] [CommRing B] (q : Q →+* B) (ρ : R →+* B) (y : Sp Q ⟶ X), Function.Surjective q → (∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) → spMap q ≫ y = spMap ρ ≫ e → ∃ φ : P →+* Q, spMap φ ≫ j = y) → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module R W) (_ : Module Rᵐᵒᵖ W) (_ : IsCentralScalar R W) (y₀ : Sp (TrivSqZeroExt R W) ⟶ X), IsCot s e W y₀ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CotLift.isCot_of_lifting
end

section
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.Cot

theorem vb_of_free_on_basicOpens :
    ∀ (R W : Type) [CommRing R] [AddCommGroup W] [Module R W] (g : ℕ),
      (∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧
        Module.Free (Localization.Away r) (Localization.Away r ⊗[R] W) ∧
        Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] W) ∧
        Module.finrank (Localization.Away r) (Localization.Away r ⊗[R] W) = g) → VB R W g := by
  intro R W _ _ _ g h
  choose r hr hfree hfin hrank using h
  have hs : Ideal.span (Set.range r) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hr ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  have hfp : Module.FinitePresentation R W := by
    refine Module.FinitePresentation.of_localizationSpan' (Set.range r) hs
      (Rₚ := fun x => Localization.Away x.1) (Mₚ := fun x => Localization.Away x.1 ⊗[R] W)
      (fun x => TensorProduct.mk R (Localization.Away x.1) W 1) (fun x => ?_)
    obtain ⟨x, p, rfl⟩ := x
    have := hfree p
    have := hfin p
    exact Module.finitePresentation_of_projective (Localization.Away (r p))
      (Localization.Away (r p) ⊗[R] W)
  have hproj : Module.Projective R W := by
    rw [← Module.freeLocus_eq_univ_iff, Set.eq_univ_iff_forall]
    intro p
    have hsub : (PrimeSpectrum.basicOpen (r p) : Set (PrimeSpectrum R)) ⊆ Module.freeLocus R W := by
      rw [Module.basicOpen_subset_freeLocus_iff]
      have := hfree p
      exact Module.Projective.of_equiv
        (LocalizedModule.equivTensorProduct (Submonoid.powers (r p)) W).symm
    exact hsub (hr p)
  refine ⟨inferInstance, hproj, fun p => ?_⟩
  have hfl := hfree p
  have hfi := hfin p
  have hrange := PrimeSpectrum.localization_away_comap_range (Localization.Away (r p)) (r p)
  have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away (r p)))) := by
    rw [hrange]
    exact hr p
  obtain ⟨q', hq'⟩ := hp
  rw [← hq', ← Module.rankAtStalk_baseChange q', Module.rankAtStalk_eq_finrank_of_free]
  exact hrank p

end GlobalTheory.CompanionTheory.Cot
end

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vector_bundle_of_local_freeness : ∀ (R W : Type) [CommRing R] [AddCommGroup W] [Module R W] (g : ℕ), (∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧ Module.Free (Localization.Away r) (Localization.Away r ⊗[R] W) ∧ Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] W) ∧ Module.finrank (Localization.Away r) (Localization.Away r ⊗[R] W) = g) → VB R W g := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Cot.vb_of_free_on_basicOpens
end

section
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.CotLoc

theorem spMap_comp' {a b c : Type} [CommRing a] [CommRing b] [CommRing c] (f : a →+* b) (g : b →+* c) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_injective {a b : Type} [CommRing a] [CommRing b] {f g : a →+* b}
    (h : spMap f = spMap g) : f = g := by
  have := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  simpa using this

theorem landing {X : Scheme.{0}} {A Q R' : Type} [CommRing A] [CommRing Q] [CommRing R']
    (j : Sp A ⟶ X) [IsOpenImmersion j] (ε : A →+* R') (q : Q →+* R')
    (hq : Function.Surjective q) (hnil : ∀ x, q x = 0 → IsNilpotent x)
    (y : Sp Q ⟶ X) (hy : spMap q ≫ y = spMap ε ≫ j) :
    ∃ ψ : A →+* Q, y = spMap ψ ≫ j := by
  have hsurj : ∀ p : Sp Q, ∃ p' : Sp R', spMap q p' = p := by
    intro p
    have : (p : PrimeSpectrum Q) ∈ Set.range (PrimeSpectrum.comap q) := by
      rw [range_comap_of_surjective _ q hq]
      intro x hx
      obtain ⟨n, hn⟩ := hnil x hx
      exact p.2.mem_of_pow_mem n (hn ▸ zero_mem _)
    obtain ⟨p', hp'⟩ := this
    exact ⟨p', hp'⟩
  have hr : Set.range y ⊆ Set.range j := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨p', rfl⟩ := hsurj p
    have h1 : y (spMap q p') = (spMap q ≫ y) p' := by simp
    rw [h1, hy]
    exact ⟨spMap ε p', by simp⟩
  refine ⟨(Spec.preimage (IsOpenImmersion.lift j y hr)).hom, ?_⟩
  have : spMap (Spec.preimage (IsOpenImmersion.lift j y hr)).hom = IsOpenImmersion.lift j y hr := by
    simp [spMap]
  rw [this, IsOpenImmersion.lift_fac]

section Rel

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} {e : Sp R ⟶ X}
  {W : Type} [AddCommGroup W] [Module R W] [Module Rᵐᵒᵖ W] [IsCentralScalar R W]
  {y₀ : Sp (TrivSqZeroExt R W) ⟶ X}
  {R' : Type} [CommRing R'] [Algebra R R'] {A C : Type} [CommRing A] [CommRing C] [Algebra C A]
  [Algebra A R'] {j : Sp A ⟶ X} {k : Sp C ⟶ Sp R}

theorem base_eq (hes : e ≫ s = 𝟙 _) (hjs : j ≫ s = spMap (algebraMap C A) ≫ k)
    (hje : spMap (algebraMap A R') ≫ j = spMap (algebraMap R R') ≫ e) :
    spMap (algebraMap R R') = spMap ((algebraMap A R').comp (algebraMap C A)) ≫ k := by
  calc spMap (algebraMap R R') = (spMap (algebraMap R R') ≫ e) ≫ s := by
        rw [Category.assoc, hes, Category.comp_id]
    _ = spMap (algebraMap A R') ≫ j ≫ s := by rw [← hje, Category.assoc]
    _ = _ := by rw [hjs, spMap_comp', Category.assoc]

variable {M : Type} [AddCommGroup M] [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]
  [Module R M] [IsScalarTower R R' M]

def Good (ψ : A →+* TrivSqZeroExt R' M) : Prop :=
  (TrivSqZeroExt.fstHom R' R' M).toRingHom.comp ψ = algebraMap A R' ∧
    ψ.comp (algebraMap C A) =
      (TrivSqZeroExt.inlHom R' M).comp ((algebraMap A R').comp (algebraMap C A))

theorem fst_tsz (u : W →ₗ[R] M) :
    (TrivSqZeroExt.fstHom R' R' M).toRingHom.comp (tsz u) =
      (algebraMap R R').comp (TrivSqZeroExt.fstHom R R W).toRingHom := by
  ext x <;> simp [tsz]

theorem tsz_inl (u : W →ₗ[R] M) :
    (tsz u).comp (TrivSqZeroExt.inlHom R W) =
      (TrivSqZeroExt.inlHom R' M).comp (algebraMap R R') := by
  ext x <;> simp [tsz]

theorem exists_unique_of_good (hcot : IsCot s e W y₀) (hes : e ≫ s = 𝟙 _)
    (hjs : j ≫ s = spMap (algebraMap C A) ≫ k)
    (hje : spMap (algebraMap A R') ≫ j = spMap (algebraMap R R') ≫ e)
    (ψ : A →+* TrivSqZeroExt R' M) (hψ : Good (C := C) ψ) :
    ∃! u : W →ₗ[R] M, spMap ψ ≫ j = spMap (tsz u) ≫ y₀ := by
  refine hcot.2.2 R' M (spMap ψ ≫ j) ?_ ?_
  · rw [Category.assoc, hjs, ← Category.assoc, ← spMap_comp', hψ.2, spMap_comp', Category.assoc,
      ← base_eq hes hjs hje, ← spMap_comp']
  · rw [← Category.assoc, ← spMap_comp', hψ.1, hje]

theorem exists_good (hcot : IsCot s e W y₀) (hes : e ≫ s = 𝟙 _)
    [IsOpenImmersion j] [Mono k]
    (hjs : j ≫ s = spMap (algebraMap C A) ≫ k)
    (hje : spMap (algebraMap A R') ≫ j = spMap (algebraMap R R') ≫ e)
    (u : W →ₗ[R] M) :
    ∃ ψ : A →+* TrivSqZeroExt R' M, Good (C := C) ψ ∧ spMap ψ ≫ j = spMap (tsz u) ≫ y₀ := by
  have hy : spMap (TrivSqZeroExt.fstHom R' R' M).toRingHom ≫ spMap (tsz u) ≫ y₀ =
      spMap (algebraMap A R') ≫ j := by
    rw [← Category.assoc, ← spMap_comp', fst_tsz, spMap_comp', Category.assoc, hcot.2.1, hje]
  obtain ⟨ψ, hψ⟩ := landing j (algebraMap A R') (TrivSqZeroExt.fstHom R' R' M).toRingHom
    (fun x => ⟨TrivSqZeroExt.inl x, by simp⟩)
    (fun x hx => ⟨2, by
      have hx' : x.fst = 0 := hx
      ext <;> simp [pow_two, hx']⟩) _ hy
  refine ⟨ψ, ⟨?_, ?_⟩, hψ.symm⟩
  · apply spMap_injective
    rw [← cancel_mono j, spMap_comp', Category.assoc, ← hψ, hy]
  · apply spMap_injective
    rw [← cancel_mono k, spMap_comp', Category.assoc, ← hjs, ← Category.assoc (spMap ψ), ← hψ,
      Category.assoc, hcot.1, ← spMap_comp', tsz_inl, spMap_comp' (algebraMap R R'), base_eq hes hjs hje,
      spMap_comp' ((algebraMap A R').comp (algebraMap C A)), Category.assoc]

variable {N : Type} [AddCommGroup N] [Module R' N] [Module R'ᵐᵒᵖ N] [IsCentralScalar R' N]
  [Module R N] [IsScalarTower R R' N]

theorem tsz_comp (u : W →ₗ[R] M) (v : M →ₗ[R'] N) :
    (tsz (R := R') (B := R') v).comp (tsz u) = tsz ((v.restrictScalars R).comp u) := by
  ext x <;> simp [tsz]

theorem rel_comp {ψ : A →+* TrivSqZeroExt R' M} {u : W →ₗ[R] M} (v : M →ₗ[R'] N)
    (h : spMap ψ ≫ j = spMap (tsz u) ≫ y₀) :
    spMap ((tsz (R := R') (B := R') v).comp ψ) ≫ j =
      spMap (tsz ((v.restrictScalars R).comp u)) ≫ y₀ := by
  rw [spMap_comp', Category.assoc, h, ← tsz_comp, spMap_comp', Category.assoc]

theorem tsz_id_comp (ψ : A →+* TrivSqZeroExt R' M) :
    (tsz (R := R') (B := R') (LinearMap.id : M →ₗ[R'] M)).comp ψ = ψ := by
  ext x <;> simp [tsz]

theorem equiv_of_universal (hcot : IsCot s e W y₀) (hes : e ≫ s = 𝟙 _)
    [IsOpenImmersion j] [Mono k]
    (hjs : j ≫ s = spMap (algebraMap C A) ≫ k)
    (hje : spMap (algebraMap A R') ≫ j = spMap (algebraMap R R') ≫ e)
    (iW : W →ₗ[R] N) (ψ₁ : A →+* TrivSqZeroExt R' M) (h₁ : Good (C := C) ψ₁)
    (extW : ∀ u : W →ₗ[R] M, ∃ u' : N →ₗ[R'] M, (u'.restrictScalars R).comp iW = u)
    (extM : ∀ ψ : A →+* TrivSqZeroExt R' N, Good (C := C) ψ →
      ∃ v : M →ₗ[R'] N, (tsz (R := R') (B := R') v).comp ψ₁ = ψ)
    (uniqW : ∀ f g : N →ₗ[R'] N, (f.restrictScalars R).comp iW = (g.restrictScalars R).comp iW → f = g)
    (uniqM : ∀ f g : M →ₗ[R'] M, (tsz (R := R') (B := R') f).comp ψ₁ =
      (tsz (R := R') (B := R') g).comp ψ₁ → f = g) :
    Nonempty (N ≃ₗ[R'] M) := by
  obtain ⟨ψ₀, g₀, r₀⟩ := exists_good (M := N) hcot hes hjs hje iW
  obtain ⟨u₁, r₁, -⟩ := exists_unique_of_good (M := M) hcot hes hjs hje ψ₁ h₁
  obtain ⟨u', hu'⟩ := extW u₁
  obtain ⟨v, hv⟩ := extM ψ₀ g₀
  have ha : (v.restrictScalars R).comp u₁ = iW :=
    (exists_unique_of_good (M := N) hcot hes hjs hje ψ₀ g₀).unique
      (by rw [← hv]; exact rel_comp v r₁) r₀
  have hb : (tsz (R := R') (B := R') u').comp ψ₀ = ψ₁ := by
    apply spMap_injective
    rw [← cancel_mono j, rel_comp u' r₀, hu', r₁]
  have h1 : v.comp u' = LinearMap.id := by
    apply uniqW
    ext w
    have := congrArg (fun f => f w) ha
    have h2 := congrArg (fun f => f w) hu'
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at this h2 ⊢
    rw [h2, this]
    rfl
  have h2 : u'.comp v = LinearMap.id := by
    apply uniqM
    rw [tsz_id_comp]
    have := tsz_comp (R := R') (R' := R') v u'
    rw [LinearMap.restrictScalars_self] at this
    rw [← this, RingHom.comp_assoc, hv, hb]
  exact ⟨LinearEquiv.ofLinear u' v h2 h1⟩

def phiOf (d : A →+ M)
    (hm : ∀ a b, d (a * b) = algebraMap A R' a • d b + algebraMap A R' b • d a) :
    A →+* TrivSqZeroExt R' M where
  toFun a := TrivSqZeroExt.inl (algebraMap A R' a) + TrivSqZeroExt.inr (d a)
  map_one' := by
    have h1 : d 1 = 0 := by simpa using hm 1 1
    ext <;> simp [h1]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp [hm, add_comm]

theorem phiOf_good (d : A →+ M)
    (hm : ∀ a b, d (a * b) = algebraMap A R' a • d b + algebraMap A R' b • d a)
    (hc : ∀ c : C, d (algebraMap C A c) = 0) : Good (C := C) (phiOf d hm) := by
  constructor
  · ext a; simp [phiOf]
  · ext c <;> simp [phiOf, hc]

theorem exists_lift (ψ : A →+* TrivSqZeroExt R' M) (hψ : Good (C := C) ψ) :
    ∃ v : (R' ⊗[A] KaehlerDifferential C A) →ₗ[R'] M,
      ∀ a, v (1 ⊗ₜ KaehlerDifferential.D C A a) = (ψ a).snd := by
  letI : Module A M := Module.compHom M (algebraMap A R')
  haveI : IsScalarTower A R' M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module C M := Module.compHom M ((algebraMap A R').comp (algebraMap C A))
  haveI : IsScalarTower C A M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hfst : ∀ a, (ψ a).fst = algebraMap A R' a := fun a => congrArg (fun f => f a) hψ.1
  have hC : ∀ c, ψ (algebraMap C A c) =
      TrivSqZeroExt.inl (algebraMap A R' (algebraMap C A c)) := fun c => congrArg (fun f => f c) hψ.2
  let l : A →ₗ[C] M :=
    { toFun := fun a => (ψ a).snd
      map_add' := fun a b => by simp
      map_smul' := fun c a => by
        rw [Algebra.smul_def, map_mul, hC]
        simp }
  let d : Derivation C A M := Derivation.mk' l (fun a b => by
    show (ψ (a * b)).snd = a • (ψ b).snd + b • (ψ a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst, op_smul_eq_smul]
    rfl)
  refine ⟨d.liftKaehlerDifferential.liftBaseChange R', fun a => ?_⟩
  rw [LinearMap.liftBaseChange_tmul, one_smul, Derivation.liftKaehlerDifferential_comp_D]
  rfl

end Rel

section Final

@[reducible] def opAct (B M : Type) [CommRing B] [AddCommGroup M] [Module B M] : Module Bᵐᵒᵖ M :=
  Module.compHom M ((RingHom.id B).fromOpposite (fun x y => mul_comm x y))

theorem opAct_central (B M : Type) [CommRing B] [AddCommGroup M] [Module B M] :
    letI := opAct B M
    IsCentralScalar B M :=
  letI := opAct B M
  ⟨fun _ _ => rfl⟩

theorem compHom_tower (R R' P : Type) [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup P]
    [Module R' P] :
    letI := Module.compHom P (algebraMap R R')
    IsScalarTower R R' P :=
  letI := Module.compHom P (algebraMap R R')
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

theorem tensor_ext {R R' W N : Type} [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup W]
    [Module R W] [AddCommGroup N] [Module R' N] {f g : (R' ⊗[R] W) →ₗ[R'] N}
    (h : ∀ w, f (1 ⊗ₜ w) = g (1 ⊗ₜ w)) : f = g := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r w =>
    have : r ⊗ₜ[R] w = r • ((1 : R') ⊗ₜ[R] w) := by simp [TensorProduct.smul_tmul']
    rw [this, map_smul, map_smul, h]
  | add x y hx hy => simp [hx, hy]

theorem one_tmul_smul {R' A P : Type} [CommRing R'] [CommRing A] [Algebra A R'] [AddCommGroup P]
    [Module A P] (a : A) (x : P) :
    (1 : R') ⊗ₜ[A] (a • x) = algebraMap A R' a • ((1 : R') ⊗ₜ[A] x) := by
  rw [TensorProduct.tmul_smul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul',
    TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]

theorem kaehler_ext {R' A C N : Type} [CommRing R'] [CommRing A] [CommRing C] [Algebra C A]
    [Algebra A R'] [AddCommGroup N] [Module R' N]
    {f g : (R' ⊗[A] KaehlerDifferential C A) →ₗ[R'] N}
    (h : ∀ a, f (1 ⊗ₜ KaehlerDifferential.D C A a) = g (1 ⊗ₜ KaehlerDifferential.D C A a)) :
    f = g := by
  have key : ∀ x ∈ Submodule.span A (Set.range (KaehlerDifferential.D C A)),
      f (1 ⊗ₜ x) = g (1 ⊗ₜ x) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h a
    | zero => simp
    | add x y _ _ hx hy => simp [TensorProduct.tmul_add, hx, hy]
    | smul a x _ hx =>
      rw [one_tmul_smul, map_smul, map_smul, hx]
  refine tensor_ext fun x => key x ?_
  rw [KaehlerDifferential.span_range_derivation]
  trivial

theorem equiv_general {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} {e : Sp R ⟶ X}
    (hes : e ≫ s = 𝟙 _) {W : Type} [AddCommGroup W] [Module R W] [Module Rᵐᵒᵖ W]
    [IsCentralScalar R W] {y₀ : Sp (TrivSqZeroExt R W) ⟶ X} (hcot : IsCot s e W y₀)
    {R' : Type} [CommRing R'] [Algebra R R'] {A C : Type} [CommRing A] [CommRing C] [Algebra C A]
    [Algebra A R'] {j : Sp A ⟶ X} {k : Sp C ⟶ Sp R} [IsOpenImmersion j] [Mono k]
    (hjs : j ≫ s = spMap (algebraMap C A) ≫ k)
    (hje : spMap (algebraMap A R') ≫ j = spMap (algebraMap R R') ≫ e)
    {P : Type} [AddCommGroup P] [Module R' P] (eP : (R' ⊗[A] KaehlerDifferential C A) ≃ₗ[R'] P) :
    Nonempty ((R' ⊗[R] W) ≃ₗ[R'] P) := by
  letI := opAct R' (R' ⊗[R] W)
  haveI := opAct_central R' (R' ⊗[R] W)
  letI := opAct R' P
  haveI := opAct_central R' P
  letI : Module R P := Module.compHom _ (algebraMap R R')
  haveI : IsScalarTower R R' P := compHom_tower R R' P
  let d : A →+ P :=
    { toFun := fun a => eP ((1 : R') ⊗ₜ[A] KaehlerDifferential.D C A a)
      map_zero' := by simp
      map_add' := fun a b => by simp [TensorProduct.tmul_add] }
  have hd : ∀ a, d a = eP ((1 : R') ⊗ₜ[A] KaehlerDifferential.D C A a) := fun _ => rfl
  have hm : ∀ a b, d (a * b) = algebraMap A R' a • d b + algebraMap A R' b • d a := by
    intro a b
    simp only [hd, Derivation.leibniz, TensorProduct.tmul_add, one_tmul_smul, map_add, map_smul]
  have hc : ∀ c : C, d (algebraMap C A c) = 0 := by
    intro c
    simp [hd]
  refine equiv_of_universal hcot hes hjs hje (TensorProduct.mk R R' W 1) (phiOf d hm)
    (phiOf_good d hm hc) ?_ ?_ ?_ ?_
  · intro u
    refine ⟨u.liftBaseChange R', ?_⟩
    ext w
    simp
  · intro ψ hψ
    obtain ⟨v, hv⟩ := exists_lift ψ hψ
    refine ⟨v ∘ₗ eP.symm.toLinearMap, RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_⟩
    · have := congrArg (fun f => f a) hψ.1
      simpa [tsz, phiOf] using this.symm
    · have := hv a
      simpa [tsz, phiOf, hd] using this
  · intro f g h
    exact tensor_ext fun w => congrArg (fun f => f w) h
  · intro f g h
    have key : f ∘ₗ eP.toLinearMap = g ∘ₗ eP.toLinearMap := by
      refine kaehler_ext fun a => ?_
      have := congrArg (fun F => (F a).snd) h
      simpa [tsz, phiOf, hd] using this
    refine LinearMap.ext fun x => ?_
    have := congrArg (fun F => F (eP.symm x)) key
    simpa using this

end Final

theorem cotangent_away : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (e : Sp R ⟶ X), e ≫ s = 𝟙 _ → ∀ (W : Type) [AddCommGroup W] [Module R W] [Module Rᵐᵒᵖ W] [IsCentralScalar R W] (y₀ : Sp (TrivSqZeroExt R W) ⟶ X), IsCot s e W y₀ → ∀ (r : R) (A C : Type) [CommRing A] [CommRing C] [Algebra C A] [Algebra A (Localization.Away r)] (j : Sp A ⟶ X) (k : Sp C ⟶ Sp R) [IsOpenImmersion j] [Mono k], j ≫ s = spMap (algebraMap C A) ≫ k → spMap (algebraMap A (Localization.Away r)) ≫ j = spMap (algebraMap R (Localization.Away r)) ≫ e → Nonempty ((Localization.Away r ⊗[R] W) ≃ₗ[Localization.Away r] (Localization.Away r ⊗[A] KaehlerDifferential C A)) := by
  intro R _ X s e hes W _ _ _ _ y₀ hcot r A C _ _ _ _ j k _ _ hjs hje
  exact equiv_general hes hcot hjs hje (LinearEquiv.refl _ _)

end GlobalTheory.CompanionTheory.CotLoc
end

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cotangent_local_open_chart_exists : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (e : Sp R ⟶ X), e ≫ s = 𝟙 _ → ∀ (W : Type) [AddCommGroup W] [Module R W] [Module Rᵐᵒᵖ W] [IsCentralScalar R W] (y₀ : Sp (TrivSqZeroExt R W) ⟶ X), IsCot s e W y₀ → ∀ (r : R) (A C : Type) [CommRing A] [CommRing C] [Algebra C A] [Algebra A (Localization.Away r)] (j : Sp A ⟶ X) (k : Sp C ⟶ Sp R) [IsOpenImmersion j] [Mono k], j ≫ s = spMap (algebraMap C A) ≫ k → spMap (algebraMap A (Localization.Away r)) ≫ j = spMap (algebraMap R (Localization.Away r)) ≫ e → Nonempty ((Localization.Away r ⊗[R] W) ≃ₗ[Localization.Away r] (Localization.Away r ⊗[A] KaehlerDifferential C A)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CotLoc.cotangent_away
end

section
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.CotChart

theorem exists_smooth_chart :
  ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (e : Sp R ⟶ X) (g : ℕ), e ≫ s = 𝟙 _ → SmoothOfRelativeDimension g s → ∀ p : PrimeSpectrum R, ∃ (r : R) (A C : Type) (_ : CommRing A) (_ : CommRing C) (_ : Algebra C A) (_ : Algebra A (Localization.Away r)) (j : Sp A ⟶ X) (k : Sp C ⟶ Sp R), r ∉ p.asIdeal ∧ IsOpenImmersion j ∧ Mono k ∧ j ≫ s = spMap (algebraMap C A) ≫ k ∧ spMap (algebraMap A (Localization.Away r)) ≫ j = spMap (algebraMap R (Localization.Away r)) ≫ e ∧ Module.Free A (KaehlerDifferential C A) ∧ Module.Finite A (KaehlerDifferential C A) ∧ Module.finrank A (KaehlerDifferential C A) = g := by
  intro R _ X s e g _hes hsm p
  obtain ⟨U, hU, V, hV, hxV, hVU, hstd⟩ :=
    hsm.exists_isStandardSmoothOfRelativeDimension (e (show Sp R from p))
  have hopen : IsOpen (((e ⁻¹ᵁ V : (Sp R).Opens) : Set (Sp R)) : Set (PrimeSpectrum R)) :=
    (e ⁻¹ᵁ V).isOpen
  obtain ⟨_, ⟨r, rfl⟩, hpr, hrV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p) (show p ∈ (((e ⁻¹ᵁ V : (Sp R).Opens) : Set (Sp R)) : Set (PrimeSpectrum R)) from hxV) hopen
  have hr : r ∉ p.asIdeal := hpr
  have hrange0 : Set.range (spMap (algebraMap R (Localization.Away r))) =
      ((PrimeSpectrum.basicOpen r : TopologicalSpace.Opens (PrimeSpectrum R)) : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away r) r
  have hnt : Nontrivial (Localization.Away r) := by
    have hp : p ∈ Set.range (spMap (algebraMap R (Localization.Away r))) := by
      rw [hrange0]; exact hpr
    obtain ⟨q, -⟩ := hp
    exact (PrimeSpectrum.nonempty_iff_nontrivial).1 ⟨q⟩
  have hrange : Set.range (spMap (algebraMap R (Localization.Away r)) ≫ e) ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    have hy : (spMap (algebraMap R (Localization.Away r))) y ∈
        ((PrimeSpectrum.basicOpen r : TopologicalSpace.Opens (PrimeSpectrum R)) : Set (PrimeSpectrum R)) := by
      rw [← hrange0]; exact ⟨y, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hrV hy
  let l : Sp (Localization.Away r) ⟶ Spec Γ(X, V) :=
    IsOpenImmersion.lift hV.fromSpec (spMap (algebraMap R (Localization.Away r)) ≫ e) hrange
  have hl : l ≫ hV.fromSpec = spMap (algebraMap R (Localization.Away r)) ≫ e :=
    IsOpenImmersion.lift_fac _ _ hrange
  let ε : Γ(X, V) ⟶ CommRingCat.of (Localization.Away r) := Spec.preimage l
  have hε : Spec.map ε = l := Spec.map_preimage l
  let φ : Γ(Sp R, U) ⟶ Γ(X, V) := s.appLE U V hVU
  letI aCA : Algebra Γ(Sp R, U) Γ(X, V) := φ.hom.toAlgebra
  letI aAL : Algebra Γ(X, V) (Localization.Away r) := ε.hom.toAlgebra
  have hA : Nontrivial Γ(X, V) := ε.hom.domain_nontrivial
  have hS : Algebra.IsStandardSmoothOfRelativeDimension g Γ(Sp R, U) Γ(X, V) := hstd
  have hS' : Algebra.IsStandardSmooth Γ(Sp R, U) Γ(X, V) := hS.isStandardSmooth
  refine ⟨r, Γ(X, V), Γ(Sp R, U), inferInstance, inferInstance, aCA, aAL, hV.fromSpec, hU.fromSpec,
    hr, inferInstance, inferInstance, ?_, ?_, inferInstance, inferInstance, ?_⟩
  · exact (IsAffineOpen.SpecMap_appLE_fromSpec s hU hV hVU).symm
  · rw [← hl, ← hε]; rfl
  · exact Module.finrank_eq_of_rank_eq
      (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential g)

end GlobalTheory.CompanionTheory.CotChart
end

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_chart_at_prime : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (e : Sp R ⟶ X) (g : ℕ), e ≫ s = 𝟙 _ → SmoothOfRelativeDimension g s → ∀ p : PrimeSpectrum R, ∃ (r : R) (A C : Type) (_ : CommRing A) (_ : CommRing C) (_ : Algebra C A) (_ : Algebra A (Localization.Away r)) (j : Sp A ⟶ X) (k : Sp C ⟶ Sp R), r ∉ p.asIdeal ∧ IsOpenImmersion j ∧ Mono k ∧ j ≫ s = spMap (algebraMap C A) ≫ k ∧ spMap (algebraMap A (Localization.Away r)) ≫ j = spMap (algebraMap R (Localization.Away r)) ≫ e ∧ Module.Free A (KaehlerDifferential C A) ∧ Module.Finite A (KaehlerDifferential C A) ∧ Module.finrank A (KaehlerDifferential C A) = g := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CotChart.exists_smooth_chart
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.Cot

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_id {A : Type} [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp [spMap]

theorem exists_nbhd : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (e : Sp R ⟶ X), e ≫ s = 𝟙 _ → ∃ (P : Type) (_ : CommRing P) (α : R →+* P) (ε : P →+* R) (j : Sp P ⟶ X), ε.comp α = RingHom.id R ∧ (∀ a b : P, ε a = 0 → ε b = 0 → a * b = 0) ∧ j ≫ s = spMap α ∧ spMap ε ≫ j = e ∧ Mono j ∧ ∀ (Q B : Type) [CommRing Q] [CommRing B] (q : Q →+* B) (ρ : R →+* B) (y : Sp Q ⟶ X), Function.Surjective q → (∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) → spMap q ≫ y = spMap ρ ≫ e → ∃ φ : P →+* Q, spMap φ ≫ j = y := by
  intro R _ X s e he
  have : IsImmersion (e ≫ s) := by rw [he]; infer_instance
  have : IsImmersion e := IsImmersion.of_comp e s
  let U := e.coborderRange
  let e' : Sp R ⟶ U := e.liftCoborder
  have he' : e' ≫ U.ι = e := e.liftCoborder_ι
  let t : (U : Scheme.{0}) ⟶ Sp R := U.ι ≫ s
  have het : e' ≫ t = 𝟙 _ := by simp only [t]; rw [← Category.assoc, he', he]
  have hE : IsAffine (e'.ker ^ 2).subscheme := GlobalTheory.T.square_zero_neighbourhood_affine R U t e' het
  let c := (e'.ker ^ 2).subschemeι
  have hle : c.ker ≤ e'.ker := by
    simp only [c, Scheme.IdealSheafData.ker_subschemeι]
    exact pow_le_of_le_one zero_le le_top two_ne_zero
  let i' : Sp R ⟶ (e'.ker ^ 2).subscheme := IsClosedImmersion.lift c e' hle
  have hi' : i' ≫ c = e' := IsClosedImmersion.lift_fac _ _ _
  let E := (e'.ker ^ 2).subscheme
  let P : Type := Γ(E, ⊤)
  let iso : E ≅ Sp P := E.isoSpec
  let j : Sp P ⟶ X := iso.inv ≫ c ≫ U.ι
  let α : R →+* P := (Spec.preimage (iso.inv ≫ c ≫ t)).hom
  let ε : P →+* R := (Spec.preimage (i' ≫ iso.hom)).hom
  have hα : spMap α = iso.inv ≫ c ≫ t := Spec.map_preimage _
  have hε : spMap ε = i' ≫ iso.hom := Spec.map_preimage _
  have hjs : j ≫ s = spMap α := by simp [j, hα, t]
  have hεj : spMap ε ≫ j = e := by
    simp only [hε, j, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc i', hi', he']
  refine ⟨P, inferInstance, α, ε, j, ?_, ?_, hjs, hεj, inferInstance, ?_⟩
  · apply spMap_inj
    rw [spMap_comp, hε, hα, spMap_id]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc i', hi', het]
  · have h0 : CommRingCat.ofHom ε = i'.appTop ≫ (Scheme.ΓSpecIso (.of R)).hom := by
      have h1 : (spMap ε).appTop = (Scheme.ΓSpecIso (.of P)).hom ≫ i'.appTop := by
        rw [hε, Scheme.Hom.comp_appTop]
        simp only [iso, Scheme.isoSpec, asIso_hom]
        exact congrArg (fun f ↦ f ≫ i'.appTop) (Scheme.toSpecΓ_appTop E)
      have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ε)
      rw [h1, Category.assoc] at h2
      exact ((cancel_epi _).1 h2).symm
    have hk : ∀ a : P, ε a = 0 → i'.appTop a = 0 := fun a ha ↦ by
      have h3 : (Scheme.ΓSpecIso (.of R)).hom (i'.appTop a) = 0 := by
        have := congrArg (fun f ↦ f.hom a) h0
        simpa [ha] using this.symm
      exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom).1).1 h3
    intro a b ha hb
    exact GlobalTheory.T.square_zero_neighbourhood_product_zero R U e' i' hi' a b (hk a ha) (hk b hb)
  · intro Q B _ _ q ρ y hq hsq hy
    have hsurj : Function.Surjective (spMap q) := by
      intro x
      have hx : x ∈ Set.range (PrimeSpectrum.comap q) := by
        rw [range_comap_of_surjective _ _ hq]
        intro a ha
        have : a * a = 0 := hsq a a ha ha
        exact x.2.mem_or_mem (by simp [this] : a * a ∈ x.asIdeal) |>.elim id id
      exact hx
    have hr : Set.range y ⊆ Set.range U.ι := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨x', rfl⟩ := hsurj x
      have h1 : y (spMap q x') = e (spMap ρ x') := by
        rw [← Scheme.Hom.comp_apply, hy, Scheme.Hom.comp_apply]
      rw [h1, ← he', Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    let y' : Sp Q ⟶ U := IsOpenImmersion.lift U.ι y hr
    have hy' : y' ≫ U.ι = y := IsOpenImmersion.lift_fac _ _ _
    have hy2 : spMap q ≫ y' = spMap ρ ≫ e' := by
      rw [← cancel_mono U.ι, Category.assoc, hy', hy, Category.assoc, he']
    have hk : c.ker ≤ y'.ker := by
      simp only [c, Scheme.IdealSheafData.ker_subschemeι]
      exact GlobalTheory.T.ideal_square_le_kernel_of_square_zero_map R Q B U e' q ρ y' hq hsq hy2
    let w : Sp Q ⟶ E := IsClosedImmersion.lift c y' hk
    have hw : w ≫ c = y' := IsClosedImmersion.lift_fac _ _ _
    refine ⟨(Spec.preimage (w ≫ iso.hom)).hom, ?_⟩
    have : spMap (Spec.preimage (w ≫ iso.hom)).hom = w ≫ iso.hom := Spec.map_preimage _
    rw [this]
    simp only [j, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc w, hw, hy']

theorem cotSt : CotSt := by
  intro R _ X s e g he hs
  obtain ⟨P, _, α, ε, j, h1, h2, h3, h4, h5, h6⟩ := exists_nbhd R X s e he
  obtain ⟨W, i1, i2, i3, i4, y₀, hy⟩ := GlobalTheory.T.closed_immersion_universal_square_zero R X s e P α ε j h1 h2 h3 h4 h5 h6
  refine ⟨W, i1, i2, i3, i4, y₀, GlobalTheory.T.vector_bundle_of_local_freeness R W g fun p ↦ ?_, hy⟩
  obtain ⟨r, A, C, _, _, _, _, j, k, hr, _, _, hjs, hε, f1, f2, f3⟩ := GlobalTheory.T.exists_local_chart_at_prime R X s e g he hs p
  obtain ⟨E⟩ := GlobalTheory.T.cotangent_local_open_chart_exists R X s e he W y₀ hy r A C j k hjs hε
  have : Nontrivial (Localization.Away r) := by
    refine ⟨⟨algebraMap R _ 1, algebraMap R _ 0, fun h ↦ ?_⟩⟩
    obtain ⟨⟨_, n, rfl⟩, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers r) _).1 h
    have h0 : r ^ n ∈ p.asIdeal := by
      have : r ^ n = 0 := by simpa using hc
      rw [this]; exact zero_mem _
    exact hr (p.2.mem_of_pow_mem n h0)
  have : Nontrivial A := (algebraMap A (Localization.Away r)).domain_nontrivial
  have hf : Module.Free (Localization.Away r) (Localization.Away r ⊗[R] W) := Module.Free.of_equiv E.symm
  have hn : Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] W) := Module.Finite.equiv E.symm
  exact ⟨r, hr, hf, hn, by rw [E.finrank_eq, Module.finrank_baseChange, f3]⟩

end GlobalTheory.CompanionTheory.Cot
end
end
