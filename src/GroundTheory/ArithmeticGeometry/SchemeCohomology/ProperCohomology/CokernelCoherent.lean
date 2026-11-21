import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Support
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.CohFinite

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits
open scoped ZeroObject

universe w' u

noncomputable section

variable {X : Scheme.{u}}

lemma eq_zero_of_isTerminal {T : AddCommGrpCat.{u}} (hT : IsTerminal T) (s : T) : s = 0 := by
  let f : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ T :=
    AddCommGrpCat.ofHom ((zmultiplesHom T s).comp AddEquiv.ulift.toAddMonoidHom)
  have h := congrArg (fun g : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ T => g.hom (⟨1⟩ : ULift.{u} ℤ))
    (hT.hom_ext f 0)
  have h1 : (AddEquiv.ulift (⟨1⟩ : ULift.{u} ℤ) : ℤ) = 1 := rfl
  simp only [f] at h
  rwa [AddCommGrpCat.hom_ofHom, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h1, zmultiplesHom_apply, one_smul] at h

lemma eq_zero_of_bot (F : X.Modules) (s : Γ(F, ⊥)) : s = 0 :=
  eq_zero_of_isTerminal (TopCat.Sheaf.isTerminalOfEmpty (modulesAb F)) s

lemma isZero_of_forall_eq_zero (F : X.Modules) (h : ∀ (U : X.Opens) (s : Γ(F, U)), s = 0) :
    IsZero F := by
  have : IsIso (0 : F ⟶ 0) := isIso_of_bijective_app _ fun U =>
    ⟨fun a b _ => (h U a).trans (h U b).symm,
     fun t => ⟨0, (eq_zero_of_isZero (isZero_zero _) U t).symm ▸ map_zero _⟩⟩
  exact (isZero_zero _).of_iso (asIso (0 : F ⟶ 0))

namespace Scheme.Modules.SupportedIn

lemma univ (F : X.Modules) : Scheme.Modules.SupportedIn F Set.univ := by
  intro U hU s
  have hU' : U = ⊥ := by
    ext x
    simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hx => Set.disjoint_left.1 hU hx trivial
  subst hU'
  exact eq_zero_of_bot F s

lemma inter {F : X.Modules} {T₁ T₂ : Set X} (h₁ : Scheme.Modules.SupportedIn F T₁)
    (h₂ : Scheme.Modules.SupportedIn F T₂) (hT₁ : IsClosed T₁) (hT₂ : IsClosed T₂) :
    Scheme.Modules.SupportedIn F (T₁ ∩ T₂) := by
  intro U hU s
  let U₁ : X.Opens := U ⊓ ⟨T₁ᶜ, hT₁.isOpen_compl⟩
  let U₂ : X.Opens := U ⊓ ⟨T₂ᶜ, hT₂.isOpen_compl⟩
  have hcov : U ≤ U₁ ⊔ U₂ := by
    intro x hx
    by_cases hx₁ : x ∈ T₁
    · refine Or.inr ⟨hx, fun hx₂ => Set.disjoint_left.1 hU hx ⟨hx₁, hx₂⟩⟩
    · exact Or.inl ⟨hx, hx₁⟩
  refine TopCat.Sheaf.eq_of_locally_eq₂ (modulesAb F) (homOfLE inf_le_left)
    (homOfLE inf_le_left) hcov s 0 ?_ ?_
  · rw [map_zero]
    exact h₁ U₁ (Set.disjoint_left.2 fun x hx hxT => hx.2 hxT) _
  · rw [map_zero]
    exact h₂ U₂ (Set.disjoint_left.2 fun x hx hxT => hx.2 hxT) _

lemma of_mono {F G : X.Modules} (m : F ⟶ G) [Mono m] {T : Set X}
    (h : Scheme.Modules.SupportedIn G T) : Scheme.Modules.SupportedIn F T := by
  intro U hU s
  have h1 : Mono ((Scheme.Modules.toPresheaf X).map m) := Functor.map_mono _ m
  have h2 : Mono (((Scheme.Modules.toPresheaf X).map m).app (op U)) := inferInstance
  have hinj : Function.Injective (m.app U) := (AddCommGrpCat.mono_iff_injective _).1 h2
  apply hinj
  rw [map_zero]
  exact h U hU _

lemma isZero_restrict {F : X.Modules} {T : Set X} (h : Scheme.Modules.SupportedIn F T)
    (U : X.Opens) (hU : Disjoint (U : Set X) T) :
    IsZero ((Scheme.Modules.restrictFunctor U.ι).obj F) := by
  refine isZero_of_forall_eq_zero _ fun V s => h (U.ι ''ᵁ V) ?_ s
  refine hU.mono_left ?_
  exact (U.ι.image_le_opensRange V).trans (by simp)

lemma of_isZero_restrict {F : X.Modules} {T : Set X}
    (h : ∀ U : X.Opens, Disjoint (U : Set X) T →
      IsZero ((Scheme.Modules.restrictFunctor U.ι).obj F)) :
    Scheme.Modules.SupportedIn F T := by
  intro U hU s
  have hE : U.ι ''ᵁ (U.ι ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_idem U
  have h0 : F.presheaf.map (eqToHom hE).op s = 0 :=
    eq_zero_of_isZero (h U hU) (U.ι ⁻¹ᵁ U) _
  have hinv : F.presheaf.map (eqToHom hE.symm).op (F.presheaf.map (eqToHom hE).op s) = s := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl,
      op_id, CategoryTheory.Functor.map_id]
    rfl
  rw [← hinv, h0, map_zero]

lemma of_epi {F G : X.Modules} (e : F ⟶ G) [Epi e] {T : Set X}
    (h : Scheme.Modules.SupportedIn F T) : Scheme.Modules.SupportedIn G T := by
  refine of_isZero_restrict fun U hU => ?_
  have : Epi ((Scheme.Modules.restrictFunctor U.ι).map e) := Functor.map_epi _ e
  exact (isZero_restrict h U hU).of_epi ((Scheme.Modules.restrictFunctor U.ι).map e)

lemma isZero_of_empty {F : X.Modules} (h : Scheme.Modules.SupportedIn F ∅) : IsZero F :=
  isZero_of_forall_eq_zero F fun U s => h U (Set.disjoint_empty _) s

end Scheme.Modules.SupportedIn

section Cohomology

variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]

lemma H_eq_zero_of_isZero {F : X.Modules} (hF : IsZero F) {p : ℕ}
    (x : Sheaf.H.{w'} (modulesAb F) p) : x = 0 := by
  have hF' : IsZero (modulesAb F) := Functor.map_isZero _ hF
  change Abelian.Ext _ _ p at x
  rw [← Abelian.Ext.comp_mk₀_id x, hF'.eq_of_src (𝟙 _) 0, Abelian.Ext.mk₀_zero,
    Abelian.Ext.comp_zero]

theorem FiniteH.of_isZero (A : Type*) [CommRing A] [Algebra A Γ(X, ⊤)] {F : X.Modules}
    (hF : IsZero F) : FiniteH.{w'} A F := fun p =>
  have : Subsingleton (Sheaf.H.{w'} (modulesAb F) p) :=
    ⟨fun x y => (H_eq_zero_of_isZero hF x).trans (H_eq_zero_of_isZero hF y).symm⟩
  Module.Finite.of_finite

end Cohomology

end

end GroundTheory.Arith.SchemeCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

section Spec

variable {R : CommRingCat.{u}} {M N : (Spec (.of R)).Modules} (ψ : M ⟶ N)

def cokernelTildeIso (hM : IsIso M.fromTildeΓ) (hN : IsIso N.fromTildeΓ) :
    (tilde.functor R).obj (cokernel (moduleSpecΓFunctor.map ψ)) ≅ cokernel ψ :=
  let p : (moduleSpecΓFunctor ⋙ tilde.functor R).obj M ≅ M := @asIso _ _ _ _ M.fromTildeΓ hM
  let q : (moduleSpecΓFunctor ⋙ tilde.functor R).obj N ≅ N := @asIso _ _ _ _ N.fromTildeΓ hN
  PreservesCokernel.iso (tilde.functor R) (moduleSpecΓFunctor.map ψ) ≪≫
    cokernel.mapIso ((moduleSpecΓFunctor ⋙ tilde.functor R).map ψ) ψ p q
      (Scheme.Modules.fromTildeΓNatTrans.naturality ψ)

lemma cokernelTildeIso_comm (hM : IsIso M.fromTildeΓ) (hN : IsIso N.fromTildeΓ) :
    (tilde.functor R).map (cokernel.π (moduleSpecΓFunctor.map ψ)) ≫
      (cokernelTildeIso ψ hM hN).hom = N.fromTildeΓ ≫ cokernel.π ψ := by
  have h : (tilde.functor R).map (cokernel.π (moduleSpecΓFunctor.map ψ)) ≫
      (PreservesCokernel.iso (tilde.functor R) (moduleSpecΓFunctor.map ψ)).hom =
      cokernel.π ((tilde.functor R).map (moduleSpecΓFunctor.map ψ)) := by
    rw [← π_comp_cokernelComparison, ← PreservesCokernel.iso_inv, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  rw [cokernelTildeIso, Iso.trans_hom, ← Category.assoc, h]
  simp [cokernel.mapIso]
  try rfl

lemma isQuasicoherent_cokernel_spec [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (cokernel ψ).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec (.of R)).ringCatSheaf).prop_of_iso
    (cokernelTildeIso ψ inferInstance inferInstance)
    (inferInstanceAs ((tilde.functor R).obj _).IsQuasicoherent)

lemma surjective_cokernel_π_app_top [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Surjective ((cokernel.π ψ).app ⊤) := by
  have hM : IsIso M.fromTildeΓ := inferInstance
  have hN : IsIso N.fromTildeΓ := inferInstance
  set Q := cokernel (moduleSpecΓFunctor.map ψ)
  set q := cokernel.π (moduleSpecΓFunctor.map ψ)
  have hq : Function.Surjective q := (ModuleCat.epi_iff_surjective q).1 inferInstance
  have h1 : Function.Surjective (((tilde.functor R).map q).app ⊤) := by
    have e := tilde.toOpen_map_app q ⊤
    intro y
    obtain ⟨y', rfl⟩ := (ConcreteCategory.bijective_of_isIso (tilde.toOpen Q ⊤)).2 y
    obtain ⟨z, rfl⟩ := hq y'
    refine ⟨tilde.toOpen _ ⊤ z, ?_⟩
    have := congrArg (fun g => g.hom z) e
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    exact this
  have h2 : ∀ x, (cokernelTildeIso ψ hM hN).hom.app ⊤ (((tilde.functor R).map q).app ⊤ x) =
      (cokernel.π ψ).app ⊤ (N.fromTildeΓ.app ⊤ x) := fun x => by
    have := congrArg (fun g => (g.app ⊤) x) (cokernelTildeIso_comm ψ hM hN)
    exact this
  intro y
  obtain ⟨x, hx⟩ := ((ConcreteCategory.bijective_of_isIso
    ((cokernelTildeIso ψ hM hN).hom.app ⊤)).2.comp h1) y
  exact ⟨N.fromTildeΓ.app ⊤ x, (h2 x).symm.trans hx⟩

end Spec

section Scheme

variable {X : Scheme.{u}} {F G : X.Modules} (φ : F ⟶ G)

lemma bijective_app_of_iso {M N : X.Modules} (e : M ≅ N) (U : X.Opens) :
    Function.Bijective (e.hom.app U) := by
  refine Function.bijective_iff_has_inverse.2 ⟨e.inv.app U, fun x => ?_, fun y => ?_⟩
  · rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.hom_inv_id]
    rfl
  · rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id]
    rfl

lemma isQuasicoherent_restrict_cokernel [F.IsQuasicoherent] [G.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) : ((cokernel φ).restrict hU.fromSpec).IsQuasicoherent := by
  let Rf := Scheme.Modules.restrictFunctor hU.fromSpec
  have : (Rf.obj F).IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  have : (Rf.obj G).IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  have h := isQuasicoherent_cokernel_spec (R := Γ(X, U)) (Rf.map φ)
  exact (SheafOfModules.isQuasicoherent (Spec Γ(X, U)).ringCatSheaf).prop_of_iso
    (PreservesCokernel.iso Rf φ).symm h

instance isQuasicoherent_cokernel [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (cokernel φ).IsQuasicoherent :=
  isQuasicoherent_of_restrict (cokernel φ) (fun U : X.affineOpens => (U : X.Opens))
    (iSup_affineOpens_eq_top X)
    fun U => nonempty_presentation_restrict _ U.2 (isQuasicoherent_restrict_cokernel φ U.2)

lemma surjective_cokernel_π_app [F.IsQuasicoherent] [G.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) : Function.Surjective ((cokernel.π φ).app U) := by
  let Rf := Scheme.Modules.restrictFunctor hU.fromSpec
  have : (Rf.obj F).IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  have : (Rf.obj G).IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  have h1 := surjective_cokernel_π_app_top (R := Γ(X, U)) (Rf.map φ)
  have h2 : Rf.map (cokernel.π φ) = cokernel.π (Rf.map φ) ≫ (PreservesCokernel.iso Rf φ).inv := by
    rw [PreservesCokernel.iso_inv, π_comp_cokernelComparison]
  have h3 : Function.Surjective ((Rf.map (cokernel.π φ)).app ⊤) := by
    rw [h2]
    exact (bijective_app_of_iso (PreservesCokernel.iso Rf φ).symm ⊤).2.comp h1
  rw [← fromSpec_image_top hU]
  exact h3

theorem isCoherent_cokernel [F.IsQuasicoherent] (hG : IsCoherent G) :
    IsCoherent (cokernel φ) := by
  have := hG.1
  refine ⟨inferInstance, fun U hU => ?_⟩
  have := hG.2 U hU
  let π' : Γ(G, U) →ₗ[Γ(X, U)] Γ(cokernel φ, U) :=
    { toFun := (cokernel.π φ).app U
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul _ }
  exact Module.Finite.of_surjective π' (surjective_cokernel_π_app φ hU)

end Scheme

section Sequences

variable {C : Type*} [Category C] [Abelian C] {P Q : C} (α : P ⟶ Q)

def kerCoimSC : ShortComplex C :=
  ShortComplex.mk (kernel.ι α) (Abelian.coimage.π α) (cokernel.condition _)

lemma kerCoimSC_shortExact : (kerCoimSC α).ShortExact :=
  ShortComplex.ShortExact.mk' ((kerCoimSC α).exact_of_g_is_cokernel
    (cokernelIsCokernel (kernel.ι α))) (inferInstanceAs (Mono (kernel.ι α)))
    (inferInstanceAs (Epi (Abelian.coimage.π α)))

def coimCokSC : ShortComplex C :=
  ShortComplex.mk (Abelian.factorThruCoimage α) (cokernel.π α) (by
    rw [← cancel_epi (Abelian.coimage.π α), ← Category.assoc, Abelian.coimage.fac, comp_zero,
      cokernel.condition])

def coimCokIsColimit :
    IsColimit (CokernelCofork.ofπ (f := Abelian.factorThruCoimage α) (cokernel.π α)
      (coimCokSC α).zero) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun b hb => cokernel.desc α b (by
      rw [← Abelian.coimage.fac α, Category.assoc, hb, comp_zero]))
    (fun b hb => cokernel.π_desc _ _ _)
    (fun b hb m hm => by
      exact (cancel_epi (cokernel.π α)).1 (by rw [hm, cokernel.π_desc]))

lemma coimCokSC_shortExact : (coimCokSC α).ShortExact :=
  ShortComplex.ShortExact.mk' ((coimCokSC α).exact_of_g_is_cokernel (coimCokIsColimit α))
    (inferInstanceAs (Mono (Abelian.factorThruCoimage α))) (inferInstanceAs (Epi (cokernel.π α)))

end Sequences

end

end GroundTheory.Arith.SchemeCoh
end
