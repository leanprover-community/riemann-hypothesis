import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import BuildAid.ForwardExisting

section
section
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace GlobalTheory

theorem app_injective_of_dense_range {T Z : Scheme.{0}} [IsReduced Z] (j : T ⟶ Z) [IsOpenImmersion j]
    (hj : Dense (Set.range j)) (W : Z.Opens) : Function.Injective (j.app W).hom := by
  intro a b hab
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  have h0 : j ⁻¹ᵁ Z.basicOpen (a - b) = ⊥ := by
    rw [Scheme.preimage_basicOpen, map_sub, hab, sub_self, Scheme.basicOpen_zero]
  by_contra hne
  obtain ⟨z, hz⟩ := (Opens.ne_bot_iff_nonempty _).mp hne
  obtain ⟨x, hx1, ⟨y, rfl⟩⟩ := hj.inter_open_nonempty _ (Z.basicOpen (a - b)).isOpen ⟨z, hz⟩
  have : y ∈ j ⁻¹ᵁ Z.basicOpen (a - b) := hx1
  rw [h0] at this
  exact this

theorem app_res_eq {T Z : Scheme.{0}} (j : T ⟶ Z) {V W : Z.Opens} (i : V ⟶ W)
    (i' : j ⁻¹ᵁ V ⟶ j ⁻¹ᵁ W) (a : Γ(Z, W)) :
    j.app V (Z.presheaf.map i.op a) = T.presheaf.map i'.op (j.app W a) := by
  obtain rfl : i' = (Opens.map j.base).map i := Subsingleton.elim _ _
  have := congrArg (fun f => f.hom a) (j.naturality i.op)
  simpa using this

theorem glue_of_dense_openImmersion : ∀ {T Z : Scheme.{0}} [IsReduced Z] (j : T ⟶ Z) [IsOpenImmersion j], Dense (Set.range j) →
    ∀ (U : Z.Opens) (s : Γ(T, j ⁻¹ᵁ U)), (∀ u ∈ U, ∃ (W : Z.Opens) (hWU : W ≤ U), u ∈ W ∧
      ∃ h : Γ(Z, W), j.app W h = T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) →
    ∃ h : Γ(Z, U), j.app U h = s := by
  intro T Z _ j _ hj U s hloc
  choose W hWU hmem h hh using hloc
  let Wf : U → Z.Opens := fun u => W u.1 u.2
  have hcover : U ≤ iSup Wf := fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hmem x hx⟩
  obtain ⟨g, hg, -⟩ := Z.sheaf.existsUnique_gluing' Wf U (fun u => homOfLE (hWU u.1 u.2)) hcover
    (fun u => h u.1 u.2) (by
      intro u v
      apply app_injective_of_dense_range j hj
      change j.app _ (Z.presheaf.map _ (h u.1 u.2)) = j.app _ (Z.presheaf.map _ (h v.1 v.2))
      rw [app_res_eq j _ (homOfLE (j.preimage_mono inf_le_left)),
        app_res_eq j _ (homOfLE (j.preimage_mono inf_le_right)), hh, hh]
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)
  let g' : Γ(Z, U) := g
  have hg' : ∀ u : U, Z.presheaf.map (homOfLE (hWU u.1 u.2)).op g' = h u.1 u.2 := hg
  refine ⟨g', ?_⟩
  refine T.sheaf.eq_of_locally_eq' (fun u : U => j ⁻¹ᵁ Wf u) (j ⁻¹ᵁ U)
    (fun u => homOfLE (j.preimage_mono (hWU u.1 u.2))) ?_ _ _ ?_
  · intro x hx
    exact Opens.mem_iSup.2 ⟨⟨j x, hx⟩, hmem _ hx⟩
  · intro u
    have key : T.presheaf.map (homOfLE (j.preimage_mono (hWU u.1 u.2))).op (j.app U g') =
        T.presheaf.map (homOfLE (j.preimage_mono (hWU u.1 u.2))).op s := by
      rw [← app_res_eq j (homOfLE (hWU u.1 u.2)), hg' u, hh]
    exact key

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_extending_of_dense_openImmersion : ∀ {T Z : Scheme.{0}} [IsReduced Z] (j : T ⟶ Z) [IsOpenImmersion j], Dense (Set.range j) →
    ∀ (U : Z.Opens) (s : Γ(T, j ⁻¹ᵁ U)), (∀ u ∈ U, ∃ (W : Z.Opens) (hWU : W ≤ U), u ∈ W ∧
      ∃ h : Γ(Z, W), j.app W h = T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) →
    ∃ h : Γ(Z, U), j.app U h = s := by
  atlas_forward_decl GlobalTheory.glue_of_dense_openImmersion
end

section
section
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace GlobalTheory

theorem exists_section_of_isIntegralElem_of_isOpenImmersion {T Z : Scheme.{0}}
    [GlobalTheory.IsNormalScheme Z] [IsLocallyNoetherian Z] (j : T ⟶ Z) [IsOpenImmersion j] :
    Dense (Set.range j) → ∀ (U : Z.Opens) (s : Γ(T, j ⁻¹ᵁ U)), (j.app U).hom.IsIntegralElem s →
    ∀ u ∈ U, ∃ (W : Z.Opens) (hWU : W ≤ U), u ∈ W ∧
      ∃ h : Γ(Z, W), j.app W h = T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s := by
  intro hd U s hs u hu
  let C : irreducibleComponents Z := ⟨_, irreducibleComponent_mem_irreducibleComponents u⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, huW, hWle⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (show u ∈ ((U ⊓ IsNormalScheme.component C : Z.Opens) : Set Z) from
      ⟨hu, mem_irreducibleComponent⟩)
    (U ⊓ IsNormalScheme.component C).isOpen
  have hWU : W ≤ U := fun x hx ↦ (hWle hx).1
  refine ⟨W, hWU, huW, ?_⟩
  have hWirr : IsIrreducible (W : Set Z) :=
    ⟨⟨u, huW⟩, C.2.1.2.open_subset W.isOpen fun x hx ↦ (hWle hx).2⟩
  obtain ⟨_, _⟩ := IsNormalScheme.isDomain_and_isIntegrallyClosed_of_isIrreducible hWirr
  obtain ⟨x, hxW, hfr, hgen⟩ : ∃ (x : Z) (hxW : x ∈ W),
      (letI := Z.presheaf.algebra_section_stalk (U := W) ⟨x, hxW⟩;
        IsFractionRing Γ(Z, W) (Z.presheaf.stalk x)) ∧ ∀ w ∈ W, x ⤳ w := by
    let P : Spec Γ(Z, W) := ⟨⊥, Ideal.isPrime_bot⟩
    have hxW : hW.fromSpec P ∈ W := hW.range_fromSpec.le ⟨P, rfl⟩
    refine ⟨_, hxW, ?_, ?_⟩
    · let _ := Z.presheaf.algebra_section_stalk (U := W) ⟨_, hxW⟩
      have h := hW.isLocalization_stalk' P hxW
      have e : P.asIdeal.primeCompl = nonZeroDivisors Γ(Z, W) := by
        ext a
        simp [P, Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
      unfold IsLocalization.AtPrime at h
      rw [e] at h
      exact h
    · intro w hw
      obtain ⟨q, rfl⟩ : w ∈ Set.range hW.fromSpec := hW.range_fromSpec.ge hw
      exact ((PrimeSpectrum.le_iff_specializes P q).mp bot_le).map hW.fromSpec.continuous
  obtain ⟨y, rfl⟩ : x ∈ Set.range j := by
    obtain ⟨w, hw, hwr⟩ := hd.inter_open_nonempty _ W.isOpen ⟨u, huW⟩
    exact (hgen w hw).mem_open j.isOpenEmbedding.isOpen_range hwr
  let _ := Z.presheaf.algebra_section_stalk (U := W) ⟨_, hxW⟩
  let _ : Algebra Γ(Z, W) Γ(T, j ⁻¹ᵁ W) := (j.app W).hom.toAlgebra
  have hyW : y ∈ j ⁻¹ᵁ W := hxW
  have hnat : (T.presheaf.map (homOfLE (j.preimage_mono hWU)).op).hom.comp (j.app U).hom =
      (algebraMap Γ(Z, W) Γ(T, j ⁻¹ᵁ W)).comp (Z.presheaf.map (homOfLE hWU).op).hom := by
    change _ = (j.app W).hom.comp _
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, j.naturality]
    rfl
  have hs₁ : IsIntegral Γ(Z, W) (T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) := by
    obtain ⟨p, hp, hps⟩ := hs
    refine ⟨p.map (Z.presheaf.map (homOfLE hWU).op).hom, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← hnat, ← Polynomial.hom_eval₂, hps, map_zero]
  have hgerm (a : Γ(Z, W)) : j.stalkMap y (Z.presheaf.germ W (j y) hxW a) =
      T.presheaf.germ (j ⁻¹ᵁ W) y hyW (j.app W a) :=
    j.germ_stalkMap_apply W y hxW a
  have hbij : Function.Bijective (j.stalkMap y) := ConcreteCategory.bijective_of_isIso _
  let φ : Γ(T, j ⁻¹ᵁ W) ⟶ Z.presheaf.stalk (j y) :=
    T.presheaf.germ (j ⁻¹ᵁ W) y hyW ≫ inv (j.stalkMap y)
  have hφ (c : Γ(T, j ⁻¹ᵁ W)) : j.stalkMap y (φ c) = T.presheaf.germ (j ⁻¹ᵁ W) y hyW c := by
    rw [← CommRingCat.comp_apply, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  let ψ : Γ(T, j ⁻¹ᵁ W) →ₐ[Γ(Z, W)] Z.presheaf.stalk (j y) :=
    { φ.hom with commutes' := fun a ↦ hbij.1 ((hφ _).trans (hgerm a).symm) }
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.map ψ hs₁)
  refine ⟨a, ?_⟩
  have hg : T.presheaf.germ (j ⁻¹ᵁ W) y hyW
      (j.app W a - T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) = 0 := by
    rw [map_sub, ← hgerm, ← hφ, sub_eq_zero]
    exact congr(j.stalkMap y $ha)
  have : IsReduced T := isReduced_of_isOpenImmersion j
  rw [← sub_eq_zero]
  apply eq_zero_of_basicOpen_eq_bot
  rw [eq_bot_iff]
  intro t ht
  have hyt : y ⤳ t :=
    j.isOpenEmbedding.isInducing.specializes_iff.mp (hgen _ (T.basicOpen_le _ ht))
  have hy : y ∈ T.basicOpen
      (j.app W a - T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) :=
    hyt.mem_open (T.basicOpen _).isOpen ht
  rw [Scheme.mem_basicOpen _ _ _ hyW, hg] at hy
  exact (not_isUnit_zero hy).elim

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_section_of_isIntegralElem_normal_scheme : ∀ {T Z : Scheme.{0}} [GlobalTheory.IsNormalScheme Z] [IsLocallyNoetherian Z] (j : T ⟶ Z) [IsOpenImmersion j],
    Dense (Set.range j) → ∀ (U : Z.Opens) (s : Γ(T, j ⁻¹ᵁ U)), (j.app U).hom.IsIntegralElem s →
    ∀ u ∈ U, ∃ (W : Z.Opens) (hWU : W ≤ U), u ∈ W ∧
      ∃ h : Γ(Z, W), j.app W h = T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s := by
  atlas_forward_decl GlobalTheory.exists_section_of_isIntegralElem_of_isOpenImmersion
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.GenPush

theorem app_injective_of_dense {T Z : Scheme.{0}} [IsReduced Z] (j : T ⟶ Z) [IsOpenImmersion j]
    (hj : Dense (Set.range j)) (W : Z.Opens) : Function.Injective (j.app W).hom := by
  intro a b hab
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  have h0 : j ⁻¹ᵁ Z.basicOpen (a - b) = ⊥ := by
    rw [Scheme.preimage_basicOpen, map_sub, hab, sub_self, Scheme.basicOpen_zero]
  by_contra hne
  obtain ⟨z, hz⟩ := (Opens.ne_bot_iff_nonempty _).mp hne
  obtain ⟨x, hx1, ⟨y, rfl⟩⟩ := hj.inter_open_nonempty _ (Z.basicOpen (a - b)).isOpen ⟨z, hz⟩
  have : y ∈ j ⁻¹ᵁ Z.basicOpen (a - b) := hx1
  rw [h0] at this
  exact this

theorem isIntegral_of_isIso_comp {A B C D : CommRingCat.{0}} (k : A ⟶ B) (f : B ⟶ C) (m : C ⟶ D) [IsIso k]
    [IsIso m] (h : (k ≫ f ≫ m).hom.IsIntegral) : f.hom.IsIntegral := by
  have e : f = inv k ≫ (k ≫ f ≫ m) ≫ inv m := by simp
  rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp]
  refine RingHom.IsIntegral.trans _ _ ?_ (RingHom.IsIntegral.trans _ _ h ?_)
  · exact RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso (inv k)).2
  · exact RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso (inv m)).2

theorem isIntegral_app_of_universallyClosed {Z₁ Z₂ : Scheme.{0}} (ρ : Z₁ ⟶ Z₂) [UniversallyClosed ρ]
    (U : Z₂.Opens) (hU : IsAffineOpen U) : (ρ.app U).hom.IsIntegral := by
  have : IsAffine U.toScheme := hU
  have h := isIntegral_appTop_of_universallyClosed (ρ ∣_ U)
  rw [morphismRestrict_appTop] at h
  have e : U.ι ''ᵁ ⊤ = U := by simp
  rw [ρ.app_eq e, Category.assoc, Category.assoc, ← Functor.map_comp] at h
  simp only [eqToHom_op, eqToHom_map, eqToHom_trans] at h
  have hi : ∀ {A B : CommRingCat.{0}} (p : A = B), IsIso (eqToHom p) := fun p => by
    subst p; rw [eqToHom_refl]; infer_instance
  refine @isIntegral_of_isIso_comp _ _ _ _ _ _ _ ?_ ?_ h
  · exact hi _
  · exact hi _

theorem exists_app_eq_of_isIntegralElem {T Z : Scheme.{0}} [GlobalTheory.IsNormalScheme Z] [IsLocallyNoetherian Z]
    (j : T ⟶ Z) [IsOpenImmersion j] (hj : Dense (Set.range j)) (U : Z.Opens)
    (s : Γ(T, j ⁻¹ᵁ U)) (hs : (j.app U).hom.IsIntegralElem s) : ∃ h : Γ(Z, U), j.app U h = s :=
  GlobalTheory.T.exists_section_extending_of_dense_openImmersion j hj U s fun u hu => GlobalTheory.T.exists_local_section_of_isIntegralElem_normal_scheme j hj U s hs u hu

theorem app_surjective_of_dense {T Z₁ Z₂ : Scheme.{0}} [IsReduced Z₁] [GlobalTheory.IsNormalScheme Z₂]
    [IsLocallyNoetherian Z₂] (j₁ : T ⟶ Z₁) (j₂ : T ⟶ Z₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h₁ : Dense (Set.range j₁)) (h₂ : Dense (Set.range j₂)) (ρ : Z₁ ⟶ Z₂) [UniversallyClosed ρ]
    (hρ : j₁ ≫ ρ = j₂) (U : Z₂.Opens) (hU : IsAffineOpen U) : Function.Surjective (ρ.app U).hom := by
  subst hρ
  intro t
  have ht : (ρ.app U).hom.IsIntegralElem t := isIntegral_app_of_universallyClosed ρ U hU t
  have hs : ((j₁ ≫ ρ).app U).hom.IsIntegralElem (j₁.app (ρ ⁻¹ᵁ U) t) := by
    change ((j₁.app (ρ ⁻¹ᵁ U)).hom.comp (ρ.app U).hom).IsIntegralElem _
    exact RingHom.IsIntegralElem.map ht _
  obtain ⟨h, hh⟩ := exists_app_eq_of_isIntegralElem (j₁ ≫ ρ) h₂ U _ hs
  refine ⟨h, app_injective_of_dense j₁ h₁ (ρ ⁻¹ᵁ U) ?_⟩
  rw [← hh]
  rfl

section Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem isReduced_gen_id (Y : Model Xo c (RingHom.id c.F)) : IsReduced (gen Y) := by
  haveI : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  haveI : IsIso (genι Y) := GlobalTheory.VarFlag.isIso_genι
  exact isReduced_of_isOpenImmersion (genι Y)

theorem comp_genStr (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (ρ : gen Y ⟶ gen X)
    (hρ : Y.jQ ≫ ρ = X.jQ) : ρ ≫ genStr X = genStr Y := by
  haveI := isReduced_gen_id Y
  haveI : IsDominant Y.jQ := ⟨Y.jQ_dense⟩
  refine ext_of_isDominant Y.jQ ?_
  rw [← Category.assoc, hρ, X.jQ_over, Y.jQ_over]

theorem isProper_of_jQ (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (ρ : gen Y ⟶ gen X)
    (hρ : Y.jQ ≫ ρ = X.jQ) : IsProper ρ := by
  haveI := isProper_genStr X
  haveI : IsProper (ρ ≫ genStr X) := (comp_genStr X Y ρ hρ) ▸ isProper_genStr Y
  exact IsProper.of_comp ρ (genStr X)

theorem app_surjective (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (ρ : gen Y ⟶ gen X)
    (hρ : Y.jQ ≫ ρ = X.jQ) (U : (gen X).affineOpens) : Function.Surjective (ρ.app U.1).hom := by
  obtain ⟨hN, hL⟩ := GlobalTheory.ModelRelCompare.normal_genericFibre X (GlobalTheory.ModelRelCompare.isDedFrac_in_use c).1
  haveI : GlobalTheory.IsNormalScheme (gen X) := GlobalTheory.IsNormalScheme.of_pred hN
  haveI : IsLocallyNoetherian (gen X) := hL
  haveI := isReduced_gen_id Y
  haveI := isProper_of_jQ X Y ρ hρ
  haveI := Y.jQ_open
  haveI := X.jQ_open
  exact app_surjective_of_dense Y.jQ X.jQ Y.jQ_dense X.jQ_dense ρ hρ U.1 U.2

end Models

end GlobalTheory.GenPush

theorem GlobalTheory.GenPush.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (ρ : gen Y ⟶ gen X), Y.jQ ≫ ρ = X.jQ →
    ∀ U : (gen X).affineOpens, Function.Surjective (ρ.app U.1).hom :=
  fun _ _ _ _ _ _ _ _ _ X Y ρ hρ U => GlobalTheory.GenPush.app_surjective X Y ρ hρ U
end
end
