import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPointResidueNonzero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSmoothRelativeDimension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProjectionSurjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellColumnsFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsometryPullIdComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleOverFieldHasFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimSmoothSurjectiveTotal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePullbackBaseChange

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_projection_surjective : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → Function.Surjective π := by
  first | exact @GlobalTheory.FlagSurj.isFlagBundle_surjective | exact GlobalTheory.FlagSurj.isFlagBundle_surjective | (intros; apply GlobalTheory.FlagSurj.isFlagBundle_surjective <;> assumption)
end

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBaseChange

variable {P Y B T T' : Scheme.{0}}

theorem pullbackComp_assoc_app (f : T' ⟶ P) (g : P ⟶ Y) (h : Y ⟶ B) (M : B.Modules) :
    (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
      (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M =
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) ≫
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M ≫ eqToHom (by simp) := by
  have e := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity f g h) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at e
  rw [← e]
  simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
  simp

theorem pullbackCongr_hom_app {f f' : P ⟶ B} (H : f = f') (M : B.Modules) :
    (Scheme.Modules.pullbackCongr H).hom.app M = eqToHom (by rw [H]) := by
  subst H; simp [Scheme.Modules.pullbackCongr]

theorem pullbackComp_congr_app (v : T' ⟶ P) {k k' : P ⟶ B} (H : k = k') (M : B.Modules) :
    (Scheme.Modules.pullback v).map ((Scheme.Modules.pullbackCongr H).hom.app M) ≫
      (Scheme.Modules.pullbackComp v k').hom.app M =
    (Scheme.Modules.pullbackComp v k).hom.app M ≫ eqToHom (by rw [H]) := by
  subst H; simp [Scheme.Modules.pullbackCongr]

def baseIso (f₁ : P ⟶ Y) (p : Y ⟶ B) (f₂ : P ⟶ T) (q : T ⟶ B) (cond : f₁ ≫ p = f₂ ≫ q) (M : B.Modules) :
    (Scheme.Modules.pullback f₁).obj ((Scheme.Modules.pullback p).obj M) ≅
      (Scheme.Modules.pullback f₂).obj ((Scheme.Modules.pullback q).obj M) :=
  (Scheme.Modules.pullbackComp f₁ p).app M ≪≫ (Scheme.Modules.pullbackCongr cond).app M ≪≫
    ((Scheme.Modules.pullbackComp f₂ q).app M).symm

theorem baseIso_coherence (f₁ : P ⟶ Y) (p : Y ⟶ B) (f₂ : P ⟶ T) (q : T ⟶ B) (cond : f₁ ≫ p = f₂ ≫ q)
    (v : T' ⟶ P) (w : (v ≫ f₁) ≫ p = (v ≫ f₂) ≫ q) (M : B.Modules) :
    (Scheme.Modules.pullback v).map (baseIso f₁ p f₂ q cond M).hom ≫
        (Scheme.Modules.pullbackComp v f₂).hom.app _ ≫ (Scheme.Modules.pullbackComp (v ≫ f₂) q).hom.app M =
      (Scheme.Modules.pullbackComp v f₁).hom.app _ ≫ (Scheme.Modules.pullbackComp (v ≫ f₁) p).hom.app M ≫
        (Scheme.Modules.pullbackCongr w).hom.app M := by
  rw [pullbackComp_assoc_app, ← Category.assoc ((Scheme.Modules.pullbackComp v f₁).hom.app _),
    pullbackComp_assoc_app]
  simp only [baseIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, Functor.map_comp,
    Category.assoc]
  rw [← Functor.map_comp_assoc (Scheme.Modules.pullback v) ((Scheme.Modules.pullbackComp f₂ q).inv.app M),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp, ← Category.assoc
      ((Scheme.Modules.pullback v).map ((Scheme.Modules.pullbackCongr cond).hom.app M)),
    pullbackComp_congr_app, pullbackCongr_hom_app]
  simp

def sqFlag (f₁ : P ⟶ Y) (p : Y ⟶ B) (f₂ : P ⟶ T) (q : T ⟶ B) (cond : f₁ ≫ p = f₂ ≫ q) {M : B.Modules} {n : ℕ}
    (fl : Vert.Flag ((Scheme.Modules.pullback p).obj M) n) :
    Vert.Flag ((Scheme.Modules.pullback f₂).obj ((Scheme.Modules.pullback q).obj M)) n :=
  (fl.pull f₁).ofIso (baseIso f₁ p f₂ q cond M)

theorem sqFlag_iff (f₁ : P ⟶ Y) (p : Y ⟶ B) (f₂ : P ⟶ T) (q : T ⟶ B) (cond : f₁ ≫ p = f₂ ≫ q)
    {M : B.Modules} {n : ℕ} (fl : Vert.Flag ((Scheme.Modules.pullback p).obj M) n)
    (v : T' ⟶ P) (h : T' ⟶ T) (hv : v ≫ f₂ = h) (w : (v ≫ f₁) ≫ p = h ≫ q)
    (fl'' : Vert.Flag ((Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback q).obj M)) n) (i : Fin (n + 1)) :
    (∃ e : (Scheme.Modules.pullback v).obj ((sqFlag f₁ p f₂ q cond fl).F i) ≅ fl''.F i,
      e.hom ≫ fl''.ι i = (Scheme.Modules.pullback v).map ((sqFlag f₁ p f₂ q cond fl).ι i) ≫
        (Scheme.Modules.pullbackComp v f₂).hom.app _ ≫ (Scheme.Modules.pullbackCongr hv).hom.app _) ↔
    (∃ e : (Scheme.Modules.pullback (v ≫ f₁)).obj (fl.F i) ≅
        (fl''.ofIso ((Scheme.Modules.pullbackComp h q).app M)).F i,
      e.hom ≫ (fl''.ofIso ((Scheme.Modules.pullbackComp h q).app M)).ι i =
        (Scheme.Modules.pullback (v ≫ f₁)).map (fl.ι i) ≫
          (Scheme.Modules.pullbackComp (v ≫ f₁) p).hom.app M ≫ (Scheme.Modules.pullbackCongr w).hom.app M) := by
  subst hv
  have coh := baseIso_coherence f₁ p f₂ q cond v w M
  have nat := (Scheme.Modules.pullbackComp v f₁).hom.naturality (fl.ι i)
  simp only [Functor.comp_map] at nat
  constructor
  · rintro ⟨e, he⟩
    refine ⟨((Scheme.Modules.pullbackComp v f₁).app _).symm ≪≫ e, ?_⟩
    erw [Iso.trans_hom]
    simp only [Vert.Flag.ofIso, sqFlag, Vert.Flag.pull, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
      Category.assoc] at he ⊢
    rw [reassoc_of% he, pullbackCongr_hom_app (f := v ≫ f₂)]
    simp only [eqToHom_refl, Category.id_comp, Functor.map_comp, Category.assoc]
    rw [coh, reassoc_of% nat, Iso.inv_hom_id_app_assoc]
  · rintro ⟨e, he⟩
    refine ⟨(Scheme.Modules.pullbackComp v f₁).app _ ≪≫ e, ?_⟩
    erw [Iso.trans_hom]
    simp only [Vert.Flag.ofIso, sqFlag, Vert.Flag.pull, Iso.app_hom, Category.assoc] at he ⊢
    rw [← cancel_mono ((Scheme.Modules.pullbackComp (v ≫ f₂) q).hom.app M)]
    simp only [Category.assoc]
    rw [he, pullbackCongr_hom_app (f := v ≫ f₂)]
    simp only [eqToHom_refl, Category.id_comp, Functor.map_comp, Category.assoc]
    rw [coh, reassoc_of% nat]

theorem isFlagBundle_pullback_snd : ∀ (B Y T : Scheme.{0}) (π : Y ⟶ B) (g : T ⟶ B) (ι : Type) [Fintype ι]
    (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)),
    IsFlagBundle π E r fl → ∃ fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback (pullback.snd π g)).obj
      ((Scheme.Modules.pullback g).obj (E a))) (r a),
      IsFlagBundle (pullback.snd π g) (fun a => (Scheme.Modules.pullback g).obj (E a)) r fl' := by
  intro B Y T π g ι _ E r fl hfl
  refine ⟨fun a => sqFlag (pullback.fst π g) π (pullback.snd π g) g pullback.condition (fl a), ?_⟩
  intro T' h fl''
  obtain ⟨u, ⟨wu, hu⟩, huniq⟩ := hfl T' (h ≫ g)
    (fun a => (fl'' a).ofIso ((Scheme.Modules.pullbackComp h g).app (E a)))
  have hfst := pullback.lift_fst u h wu
  refine ⟨pullback.lift u h wu, ⟨pullback.lift_snd _ _ _, fun a i => ?_⟩, ?_⟩
  · rw [sqFlag_iff _ _ _ _ _ (fl a) _ h (pullback.lift_snd _ _ _) (by rw [hfst]; exact wu)]
    have key : ∀ (u' : T' ⟶ Y) (e : u' = u) (w' : u' ≫ π = h ≫ g),
        ∃ e : (Scheme.Modules.pullback u').obj ((fl a).F i) ≅
          ((fl'' a).ofIso ((Scheme.Modules.pullbackComp h g).app (E a))).F i,
        e.hom ≫ ((fl'' a).ofIso ((Scheme.Modules.pullbackComp h g).app (E a))).ι i =
          (Scheme.Modules.pullback u').map ((fl a).ι i) ≫
            (Scheme.Modules.pullbackComp u' π).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w').hom.app (E a) := by
      intro u' e w'
      subst e
      exact hu a i
    exact key _ hfst _
  · rintro v ⟨hv, hprop⟩
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      have w : (v ≫ pullback.fst π g) ≫ π = h ≫ g := by
        rw [Category.assoc, pullback.condition, ← Category.assoc, hv]
      exact huniq _ ⟨w, fun a i => (sqFlag_iff _ _ _ _ pullback.condition (fl a) v h hv w (fl'' a) i).1
        (hprop a i)⟩
    · rw [pullback.lift_snd]
      exact hv

end GlobalTheory.FlagBaseChange

end
end

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_exists_after_base_change : ∀ (B Y T : Scheme.{0}) (π : Y ⟶ B) (g : T ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∃ fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback (pullback.snd π g)).obj ((Scheme.Modules.pullback g).obj (E a))) (r a), IsFlagBundle (pullback.snd π g) (fun a => (Scheme.Modules.pullback g).obj (E a)) r fl' := by
  first | exact @GlobalTheory.FlagBaseChange.isFlagBundle_pullback_snd | exact GlobalTheory.FlagBaseChange.isFlagBundle_pullback_snd | (intros; apply GlobalTheory.FlagBaseChange.isFlagBundle_pullback_snd <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry GlobalTheory

namespace GlobalTheory.FlagTrans

private theorem exists_adapted_basis {K V : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V] {N : ℕ}
    (W : Fin (N + 1) → Submodule K V) (hr : ∀ i, Module.finrank K (W i) = i)
    (hle : ∀ i : Fin N, W i.castSucc ≤ W i.succ) (htop : W (Fin.last N) = ⊤) :
    ∃ b : Module.Basis (Fin N) K V, ∀ i, W i = Submodule.span K (b '' {k | (k : ℕ) < i}) := by
  have hlt (i : Fin N) : W i.castSucc < W i.succ := by
    refine lt_of_le_of_ne (hle i) fun h => ?_
    have h1 := hr i.castSucc
    rw [h, hr] at h1
    simp at h1
  choose v hv hv' using fun i => SetLike.exists_of_lt (hlt i)
  have key (i : Fin (N + 1)) : W i = Submodule.span K (v '' {k | (k : ℕ) < i}) := by
    induction i using Fin.induction with
    | zero =>
      have h0 := hr 0
      simp only [Fin.val_zero, Submodule.finrank_eq_zero] at h0
      simp [h0]
    | succ i ih =>
      have hs : {k : Fin N | (k : ℕ) < (i.succ : Fin (N + 1))} =
          insert i {k : Fin N | (k : ℕ) < (i.castSucc : Fin (N + 1))} := by
        ext k
        simp only [Fin.val_succ, Set.mem_setOf_eq, Fin.val_castSucc, Set.mem_insert_iff, Fin.ext_iff]
        omega
      rw [hs, Set.image_insert_eq, Submodule.span_insert, ← ih]
      have h1 : Submodule.span K {v i} ⊔ W i.castSucc ≤ W i.succ :=
        sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 (hv i)) (hle i)
      have h2 : W i.castSucc < Submodule.span K {v i} ⊔ W i.castSucc := by
        refine lt_of_le_of_ne le_sup_right fun h => hv' i ?_
        rw [h]
        exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
      have h3 := Submodule.finrank_lt_finrank_of_lt h2
      refine (Submodule.eq_of_le_of_finrank_le h1 ?_).symm
      rw [hr] at h3 ⊢
      simpa using h3
  have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← htop, key]
    exact Submodule.span_mono (Set.image_subset_range _ _)
  have hc : Fintype.card (Fin N) = Module.finrank K V := by
    have := hr (Fin.last N)
    rw [htop, finrank_top] at this
    simp [this]
  exact ⟨basisOfTopLeSpanOfCardEqFinrank v hsp hc, fun i => by
    rw [coe_basisOfTopLeSpanOfCardEqFinrank]; exact key i⟩

private theorem exists_equiv_of_chains {R V : Type} [CommRing R] (hR : IsField R) [AddCommGroup V] [Module R V] {N : ℕ}
    {A B : Fin (N + 1) → Type} [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, Module R (B i)] (f : ∀ i, A i →ₗ[R] V) (g : ∀ i, B i →ₗ[R] V)
    (hf : ∀ i, Function.Injective (f i)) (hg : ∀ i, Function.Injective (g i))
    (a : ∀ i : Fin (N + 1), Module.Basis (Fin i) R (A i)) (b : ∀ i : Fin (N + 1), Module.Basis (Fin i) R (B i))
    (hfle : ∀ i : Fin N, LinearMap.range (f i.castSucc) ≤ LinearMap.range (f i.succ))
    (hgle : ∀ i : Fin N, LinearMap.range (g i.castSucc) ≤ LinearMap.range (g i.succ))
    (hft : Function.Surjective (f (Fin.last N))) (hgt : Function.Surjective (g (Fin.last N))) :
    ∃ φ : V ≃ₗ[R] V, ∀ i, ∃ e : A i ≃ₗ[R] B i, ∀ s, g i (e s) = φ (f i s) := by
  letI := hR.toField
  haveI := Module.Finite.of_basis (a (Fin.last N))
  haveI : Module.Finite R V := Module.Finite.of_surjective _ hft
  obtain ⟨u, hu⟩ := exists_adapted_basis (K := R) (fun i => LinearMap.range (f i))
    (fun i => by rw [LinearMap.finrank_range_of_inj (hf i), Module.finrank_eq_card_basis (a i), Fintype.card_fin])
    hfle (LinearMap.range_eq_top.2 hft)
  obtain ⟨w, hw⟩ := exists_adapted_basis (K := R) (fun i => LinearMap.range (g i))
    (fun i => by rw [LinearMap.finrank_range_of_inj (hg i), Module.finrank_eq_card_basis (b i), Fintype.card_fin])
    hgle (LinearMap.range_eq_top.2 hgt)
  refine ⟨u.equiv w (Equiv.refl _), fun i => ?_⟩
  have hmap : (LinearMap.range (f i)).map (u.equiv w (Equiv.refl _) : V →ₗ[R] V) = LinearMap.range (g i) := by
    have h1 := hu i
    have h2 := hw i
    rw [h1, h2, Submodule.map_span, Set.image_image]
    simp
  refine ⟨(LinearEquiv.ofInjective (f i) (hf i)).trans (((u.equiv w (Equiv.refl _)).ofSubmodules _ _ hmap).trans
    (LinearEquiv.ofInjective (g i) (hg i)).symm), fun s => ?_⟩
  simp

variable {X : Scheme.{0}}

private theorem subsingleton_sections_bot (F : X.Modules) : Subsingleton Γ(F, ⊥) := by
  refine ⟨fun s t ↦ ?_⟩
  exact TopCat.Sheaf.eq_of_locally_eq' (C := Ab.{0}) ⟨F.presheaf, F.isSheaf⟩
    (fun i : PEmpty.{1} ↦ i.elim) ⊥ (fun i ↦ i.elim) (by simp) s t (fun i ↦ i.elim)

private theorem eq_bot_or_top [Subsingleton X] (U : X.Opens) : U = ⊥ ∨ U = ⊤ := by
  rcases U.1.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · exact .inl (TopologicalSpace.Opens.ext h)
  · exact .inr (eq_top_iff.2 fun y _ => Subsingleton.elim x y ▸ hx)

private theorem hom_ext_top [Subsingleton X] {F G : X.Modules} {φ ψ : F ⟶ G}
    (h : ∀ s, φ.app ⊤ s = ψ.app ⊤ s) : φ = ψ := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext s
  rcases eq_bot_or_top U with rfl | rfl
  · exact (subsingleton_sections_bot G).elim _ _
  · exact h s

private theorem exists_iso_top [Subsingleton X] {F G : X.Modules} {n : ℕ} {e : Fin n → Γ(F, ⊤)} (he : VB.IsFrame e)
    (g : Γ(F, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(G, ⊤)) : ∃ φ : F ≅ G, ∀ s, φ.hom.app ⊤ s = g s := by
  have he' : VB.IsFrame fun i => g (e i) := by
    intro V h
    rcases eq_bot_or_top V with rfl | rfl
    · haveI := subsingleton_sections_bot G
      haveI : Subsingleton Γ(X, ⊥) := CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty rfl)
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
    · have : Fintype.linearCombination Γ(X, ⊤) (fun i => Twist.resM G h (g (e i))) =
          g.toLinearMap ∘ₗ Fintype.linearCombination Γ(X, ⊤) (fun i => Twist.resM F h (e i)) := by
        refine LinearMap.ext fun a => ?_
        simp [Fintype.linearCombination_apply, Twist.resM_self]
      rw [this]
      exact g.bijective.comp (he ⊤ h)
  refine ⟨he.iso he', fun s => ?_⟩
  have : QCoh.appLinear (he.iso he').hom ⊤ = g.toLinearMap := by
    refine (he.basis le_rfl).ext fun i => ?_
    rw [VB.IsFrame.basis_apply, Twist.resM_self, QCoh.appLinear_apply]
    exact he.iso_hom_app he' i
  exact LinearMap.congr_fun this s

private theorem exists_frame_top [Subsingleton X] [Nonempty X] {F : X.Modules} {n : ℕ} (h : VB.IsVB F n) :
    ∃ e : Fin n → Γ(F, ⊤), VB.IsFrame e := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨U, e, hx, he⟩ := h x
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => Subsingleton.elim x y ▸ hx
  exact ⟨e, he⟩

private theorem range_le {M : X.Modules} {N : ℕ} (F : Vert.Flag M N) (i : Fin N) :
    LinearMap.range (QCoh.appLinear (F.ι i.castSucc) ⊤) ≤ LinearMap.range (QCoh.appLinear (F.ι i.succ) ⊤) := by
  rintro _ ⟨s, rfl⟩
  refine ⟨(F.step i).app ⊤ s, ?_⟩
  rw [← F.step_ι i]
  rfl

end GlobalTheory.FlagTrans

open GlobalTheory.FlagTrans in
theorem _root_.GlobalTheory.T.field_flags_conjugate_by_automorphism : ∀ (L : Type) [Field L] (M : (Spec (CommRingCat.of L)).Modules) (N : ℕ) (F₁ F₂ : Vert.Flag M N), ∃ φ : M ≅ M, ∀ i, ∃ e : F₁.F i ≅ F₂.F i, e.hom ≫ F₂.ι i = F₁.ι i ≫ φ.hom := by
  intro L _ M N F₁ F₂
  have hR : IsField Γ(Spec (CommRingCat.of L), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of L)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField L)
  choose a ha using fun i => exists_frame_top (F₁.isVB i)
  choose b hb using fun i => exists_frame_top (F₂.isVB i)
  obtain ⟨m, hm⟩ := exists_frame_top F₁.isVB_self
  obtain ⟨g, hg⟩ := exists_equiv_of_chains hR (fun i => QCoh.appLinear (F₁.ι i) ⊤) (fun i => QCoh.appLinear (F₂.ι i) ⊤)
    (fun i => QCoh.injective_app_of_mono _ _) (fun i => QCoh.injective_app_of_mono _ _)
    (fun i => (ha i).basis le_rfl) (fun i => (hb i).basis le_rfl) (range_le F₁) (range_le F₂)
    (ConcreteCategory.bijective_of_isIso ((F₁.ι (Fin.last N)).app ⊤)).2
    (ConcreteCategory.bijective_of_isIso ((F₂.ι (Fin.last N)).app ⊤)).2
  obtain ⟨φ, hφ⟩ := exists_iso_top hm g
  refine ⟨φ, fun i => ?_⟩
  obtain ⟨e, he⟩ := hg i
  obtain ⟨ψ, hψ⟩ := exists_iso_top (ha i) e
  refine ⟨ψ, hom_ext_top fun s => ?_⟩
  change (F₂.ι i).app ⊤ (ψ.hom.app ⊤ s) = φ.hom.app ⊤ ((F₁.ι i).app ⊤ s)
  rw [hψ, hφ]
  exact he s
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory

namespace GlobalTheory.SectionPull

theorem canonical_app_pullbackSections {X T : Scheme.{0}} (c : T ⟶ X) (t : X ⟶ T) (h : t ≫ c = 𝟙 X)
    (F : X.Modules) (s : Γ(F, ⊤)) :
    ((Scheme.Modules.pullbackComp t c).hom.app F ≫ (Scheme.Modules.pullbackCongr h).hom.app F ≫
        (Scheme.Modules.pullbackId _).hom.app F).app ⊤
      (QCoh.pullbackSections t _ (le_refl (⊤ : X.Opens))
        (QCoh.pullbackSections c F (le_refl (⊤ : T.Opens)) s)) = s := by
  have H {j j' : X ⟶ X} (w : j = j') (hj : (⊤ : X.Opens) ≤ j ⁻¹ᵁ ⊤) (hj' : (⊤ : X.Opens) ≤ j' ⁻¹ᵁ ⊤) :
      ((Scheme.Modules.pullbackCongr w).hom.app F).app ⊤ (QCoh.pullbackSections j F hj s) =
        QCoh.pullbackSections j' F hj' s := by
    subst w; rfl
  have e1 := PullPull.pullbackComp_hom_app t c F (U := ⊤) (V := ⊤) (T := ⊤) (le_refl _) (le_refl _)
    (le_refl (⊤ : X.Opens)) s
  have e2 := H h (le_refl (⊤ : X.Opens)) (le_refl (⊤ : X.Opens))
  have e3 := PullPull.pullbackId_hom_app F (U := ⊤) (V := ⊤) (le_refl _) (le_refl _) s
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [e1, e2, e3, Twist.resM_self]

theorem pullback_map_comp_canonical : ∀ (X T : Scheme.{0}) (c : T ⟶ X) (t : X ⟶ T) (h : t ≫ c = 𝟙 X) (F : X.Modules) (κ : Type) [Fintype κ] (e : κ → Γ(F, ⊤)), VB.IsFrame e → ∀ (Φ : (Scheme.Modules.pullback c).obj F ⟶ (Scheme.Modules.pullback c).obj F) (B : Matrix κ κ Γ(T, ⊤)), (∀ i, Φ.app ⊤ (QCoh.pullbackSections c F (le_refl (⊤ : T.Opens)) (e i)) = ∑ j, B j i • QCoh.pullbackSections c F (le_refl (⊤ : T.Opens)) (e j)) → ∀ (ψ : F ⟶ F), (∀ i, ψ.app ⊤ (e i) = ∑ j, t.appTop (B j i) • e j) → (Scheme.Modules.pullback t).map Φ ≫ (Scheme.Modules.pullbackComp t c).hom.app F ≫ (Scheme.Modules.pullbackCongr h).hom.app F ≫ (Scheme.Modules.pullbackId _).hom.app F = ((Scheme.Modules.pullbackComp t c).hom.app F ≫ (Scheme.Modules.pullbackCongr h).hom.app F ≫ (Scheme.Modules.pullbackId _).hom.app F) ≫ ψ := by
  intro X T c t h F κ _ e he Φ B hΦ ψ hψ
  haveI := he.isVB.isQuasicoherent
  have hc := he.pullback c
  have ht : VB.IsFrame fun i => QCoh.pullbackSections t ((Scheme.Modules.pullback c).obj F)
      (le_refl (⊤ : X.Opens)) (QCoh.pullbackSections c F (le_refl (⊤ : T.Opens)) (e i)) :=
    hc.pullback t
  refine LieVB.hom_ext_of_isFrame ht fun i => ?_
  rw [Scheme.Modules.Hom.comp_app ((Scheme.Modules.pullback t).map Φ), Scheme.Modules.Hom.comp_app _ ψ,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, canonical_app_pullbackSections, hψ]
  have e1 := QCoh.pullback_map_app_pullbackSections t Φ (U := ⊤) (V := ⊤) (le_refl _)
    (QCoh.pullbackSections c F (le_refl (⊤ : T.Opens)) (e i))
  erw [e1]
  rw [hΦ, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e2 := QCoh.pullbackSections_smul t ((Scheme.Modules.pullback c).obj F) (U := ⊤) (V := ⊤)
    (le_refl _) (B j i) (QCoh.pullbackSections c F (le_refl (⊤ : T.Opens)) (e j))
  erw [e2, Scheme.Modules.Hom.app_smul, canonical_app_pullbackSections]
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

end GlobalTheory.SectionPull
end
end

open CategoryTheory AlgebraicGeometry GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_frame_endomorphism_matrix : ∀ (X T : Scheme.{0}) (c : T ⟶ X) (t : X ⟶ T) (h : t ≫ c = 𝟙 X) (F : X.Modules) (κ : Type) [Fintype κ] (e : κ → Γ(F, ⊤)), VB.IsFrame e → ∀ (Φ : (Scheme.Modules.pullback c).obj F ⟶ (Scheme.Modules.pullback c).obj F) (B : Matrix κ κ Γ(T, ⊤)), (∀ i, Φ.app ⊤ (QCoh.pullbackSections c F (le_refl (⊤ : T.Opens)) (e i)) = ∑ j, B j i • QCoh.pullbackSections c F (le_refl (⊤ : T.Opens)) (e j)) → ∀ (ψ : F ⟶ F), (∀ i, ψ.app ⊤ (e i) = ∑ j, t.appTop (B j i) • e j) → (Scheme.Modules.pullback t).map Φ ≫ (Scheme.Modules.pullbackComp t c).hom.app F ≫ (Scheme.Modules.pullbackCongr h).hom.app F ≫ (Scheme.Modules.pullbackId _).hom.app F = ((Scheme.Modules.pullbackComp t c).hom.app F ≫ (Scheme.Modules.pullbackCongr h).hom.app F ≫ (Scheme.Modules.pullbackId _).hom.app F) ≫ ψ := by
  atlas_forward_decl GlobalTheory.SectionPull.pullback_map_comp_canonical
end

section
section
open CategoryTheory AlgebraicGeometry GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GLPath

open Polynomial

theorem appTop_spec_map {R S : CommRingCat} (g : R ⟶ S) (r : Γ(Spec R, ⊤)) :
    (Spec.map g).appTop r = (Scheme.ΓSpecIso S).inv (g ((Scheme.ΓSpecIso R).hom r)) := by
  have e := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_naturality g)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [← e]
  simp

def line {L : Type} [Field L] {m : ℕ} (A : Matrix (Fin m) (Fin m) L) : Matrix (Fin m) (Fin m) L[X] :=
  (1 - X : L[X]) • (1 : Matrix (Fin m) (Fin m) L[X]) + (X : L[X]) • A.map C

theorem eval_line_zero {L : Type} [Field L] {m : ℕ} (A : Matrix (Fin m) (Fin m) L) (i j : Fin m) :
    eval 0 (line A i j) = (1 : Matrix (Fin m) (Fin m) L) i j := by
  simp only [line, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply, smul_eq_mul]
  split_ifs <;> simp

theorem eval_line_one {L : Type} [Field L] {m : ℕ} (A : Matrix (Fin m) (Fin m) L) (i j : Fin m) :
    eval 1 (line A i j) = A i j := by
  simp only [line, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply, smul_eq_mul]
  split_ifs <;> simp

theorem mapMatrix_line_zero {L : Type} [Field L] {m : ℕ} (A : Matrix (Fin m) (Fin m) L) :
    (evalRingHom (0 : L)).mapMatrix (line A) = 1 := by
  ext i j; exact eval_line_zero A i j

theorem mapMatrix_line_one {L : Type} [Field L] {m : ℕ} (A : Matrix (Fin m) (Fin m) L) :
    (evalRingHom (1 : L)).mapMatrix (line A) = A := by
  ext i j; exact eval_line_one A i j

end GlobalTheory.GLPath

namespace GlobalTheory.GLPath
open Polynomial

theorem exists_path : ∀ (L : Type) [Field L] (ι : Type) [Fintype ι] (n : ι → ℕ)
    (A : ∀ a, Matrix (Fin (n a)) (Fin (n a)) L), (∀ a, IsUnit (A a).det) →
    ∃ (T : Scheme.{0}) (c : T ⟶ Spec (CommRingCat.of L)) (t₁ t₂ : Spec (CommRingCat.of L) ⟶ T)
      (_ : t₁ ≫ c = 𝟙 _) (_ : t₂ ≫ c = 𝟙 _) (B : ∀ a, Matrix (Fin (n a)) (Fin (n a)) Γ(T, ⊤)),
      IrreducibleSpace T ∧ (∀ a, IsUnit (B a)) ∧
      (∀ a i j, t₁.appTop (B a i j) = (Scheme.ΓSpecIso (CommRingCat.of L)).inv ((1 : Matrix (Fin (n a)) (Fin (n a)) L) i j)) ∧
      (∀ a i j, t₂.appTop (B a i j) = (Scheme.ΓSpecIso (CommRingCat.of L)).inv (A a i j)) := by
  intro L _ ι _ n A hA
  classical
  set p : L[X] := ∏ a, (line (A a)).det with hp_def
  have hev : ∀ x : L, eval x p = ∏ a, ((evalRingHom x).mapMatrix (line (A a))).det := by
    intro x
    rw [hp_def, ← coe_evalRingHom, map_prod]
    exact Finset.prod_congr rfl fun a _ => RingHom.map_det _ _
  have hu0 : IsUnit ((evalRingHom (0 : L)) p) := by
    rw [coe_evalRingHom, hev]; simp only [mapMatrix_line_zero, Matrix.det_one, Finset.prod_const_one, isUnit_one]
  have hu1 : IsUnit ((evalRingHom (1 : L)) p) := by
    rw [coe_evalRingHom, hev]; simp only [mapMatrix_line_one]
    exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun a _ => hA a
  have hp0 : p ≠ 0 := by
    intro h; rw [h, map_zero] at hu0; exact not_isUnit_zero hu0
  let R := Localization.Away p
  haveI : IsDomain R := IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hp0)
  let c : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of L) :=
    Spec.map (CommRingCat.ofHom ((algebraMap L[X] R).comp C))
  let f₁ : R →+* L := IsLocalization.Away.lift p hu0
  let f₂ : R →+* L := IsLocalization.Away.lift p hu1
  have hf : ∀ (x : L) (hx : IsUnit ((evalRingHom x) p)) (q : L[X]),
      (IsLocalization.Away.lift (S := R) p hx) (algebraMap L[X] R q) = eval x q := by
    intro x hx q
    simp [IsLocalization.Away.lift, IsLocalization.lift_eq]
  have hsec : ∀ (x : L) (hx : IsUnit ((evalRingHom x) p)),
      Spec.map (CommRingCat.ofHom (IsLocalization.Away.lift (S := R) p hx)) ≫ c = 𝟙 _ := by
    intro x hx
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext r
    simp [c, hf]
  let B : ∀ a, Matrix (Fin (n a)) (Fin (n a)) Γ(Spec (CommRingCat.of R), ⊤) := fun a =>
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp (algebraMap L[X] R)).mapMatrix (line (A a))
  have hval : ∀ (x : L) (hx : IsUnit ((evalRingHom x) p)) a i j,
      (Spec.map (CommRingCat.ofHom (IsLocalization.Away.lift (S := R) p hx))).appTop (B a i j) =
        (Scheme.ΓSpecIso (CommRingCat.of L)).inv (eval x (line (A a) i j)) := by
    intro x hx a i j
    rw [appTop_spec_map]
    simp [B, hf]
  refine ⟨Spec (CommRingCat.of R), c, _, _, hsec 0 hu0, hsec 1 hu1, B, inferInstance, ?_, ?_, ?_⟩
  · intro a
    rw [Matrix.isUnit_iff_isUnit_det]
    simp only [B]
    rw [← RingHom.map_det]
    have hdvd : (line (A a)).det ∣ p := Finset.dvd_prod_of_mem _ (Finset.mem_univ a)
    have hpu : IsUnit (algebraMap L[X] R p) := IsLocalization.Away.algebraMap_isUnit p
    rw [RingHom.comp_apply]
    exact (isUnit_of_dvd_unit (map_dvd (algebraMap L[X] R) hdvd) hpu).map _
  · intro a i j
    rw [hval 0 hu0, eval_line_zero]
  · intro a i j
    rw [hval 1 hu1, eval_line_one]

end GlobalTheory.GLPath
end
end

open CategoryTheory AlgebraicGeometry GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_matrix_units_irreducible : ∀ (L : Type) [Field L] (ι : Type) [Fintype ι] (n : ι → ℕ) (A : ∀ a, Matrix (Fin (n a)) (Fin (n a)) L), (∀ a, IsUnit (A a).det) → ∃ (T : Scheme.{0}) (c : T ⟶ Spec (CommRingCat.of L)) (t₁ t₂ : Spec (CommRingCat.of L) ⟶ T) (_ : t₁ ≫ c = 𝟙 _) (_ : t₂ ≫ c = 𝟙 _) (B : ∀ a, Matrix (Fin (n a)) (Fin (n a)) Γ(T, ⊤)), IrreducibleSpace T ∧ (∀ a, IsUnit (B a)) ∧ (∀ a i j, t₁.appTop (B a i j) = (Scheme.ΓSpecIso (CommRingCat.of L)).inv ((1 : Matrix (Fin (n a)) (Fin (n a)) L) i j)) ∧ (∀ a i j, t₂.appTop (B a i j) = (Scheme.ΓSpecIso (CommRingCat.of L)).inv (A a i j)) := by
  atlas_forward_decl GlobalTheory.GLPath.exists_path
end

section
section
open CategoryTheory AlgebraicGeometry GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPath

theorem exists_path_auto : ∀ (L : Type) [Field L] (ι : Type) [Fintype ι] (M : ι → (Spec (CommRingCat.of L)).Modules) (r : ι → ℕ), (∀ a, VB.IsVB (M a) (r a)) → ∀ φ : ∀ a, M a ≅ M a, ∃ (T : Scheme.{0}) (c : T ⟶ Spec (CommRingCat.of L)) (t₁ t₂ : Spec (CommRingCat.of L) ⟶ T) (h₁ : t₁ ≫ c = 𝟙 _) (h₂ : t₂ ≫ c = 𝟙 _) (Φ : ∀ a, (Scheme.Modules.pullback c).obj (M a) ≅ (Scheme.Modules.pullback c).obj (M a)), IrreducibleSpace T ∧ (∀ a, (Scheme.Modules.pullback t₁).map (Φ a).hom = 𝟙 _) ∧ ∀ a, (Scheme.Modules.pullback t₂).map (Φ a).hom ≫ (Scheme.Modules.pullbackComp t₂ c).hom.app (M a) ≫ (Scheme.Modules.pullbackCongr h₂).hom.app (M a) ≫ (Scheme.Modules.pullbackId _).hom.app (M a) = ((Scheme.Modules.pullbackComp t₂ c).hom.app (M a) ≫ (Scheme.Modules.pullbackCongr h₂).hom.app (M a) ≫ (Scheme.Modules.pullbackId _).hom.app (M a)) ≫ (φ a).hom := by
  intro L _ ι _ M r hM φ
  have hframe : ∀ a, ∃ e : Fin (r a) → Γ(M a, ⊤), VB.IsFrame e := fun a => by
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
    obtain ⟨U, e, hx, he⟩ := hM a x
    obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => Subsingleton.elim x y ▸ hx
    exact ⟨e, he⟩
  choose e he using hframe
  let K := Scheme.ΓSpecIso (CommRingCat.of L)
  let b : ∀ a, Module.Basis (Fin (r a)) Γ(Spec (CommRingCat.of L), ⊤) Γ(M a, ⊤) :=
    fun a => (he a).basis le_top
  have hb : ∀ a i, b a i = e a i := fun a i => by
    rw [VB.IsFrame.basis_apply, Twist.resM_self]
  let A' : ∀ a, Matrix (Fin (r a)) (Fin (r a)) Γ(Spec (CommRingCat.of L), ⊤) := fun a =>
    LinearMap.toMatrix (b a) (b a) (QCoh.appLinear (φ a).hom ⊤)
  let A : ∀ a, Matrix (Fin (r a)) (Fin (r a)) L := fun a => K.hom.hom.mapMatrix (A' a)
  have hA : ∀ a, IsUnit (A a).det := fun a => by
    have hu : IsUnit (LinearMap.det (QCoh.appLinear (φ a).hom ⊤)) :=
      LinearEquiv.isUnit_det' (LinearEquiv.ofBijective (QCoh.appLinear (φ a).hom ⊤)
        (ConcreteCategory.bijective_of_isIso ((φ a).hom.app ⊤)))
    have : (A a).det = K.hom.hom (A' a).det := (RingHom.map_det _ _).symm
    rw [this, LinearMap.det_toMatrix]
    exact hu.map _
  have hAe : ∀ a i, (φ a).hom.app ⊤ (e a i) = ∑ j, K.inv (A a j i) • e a j := fun a i => by
    have hK : ∀ j, K.inv (A a j i) = A' a j i := fun j => by
      change K.inv (K.hom (A' a j i)) = _
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
    simp only [hK, A', LinearMap.toMatrix_apply, ← hb]
    exact ((b a).sum_repr _).symm
  obtain ⟨T, c, t₁, t₂, h₁, h₂, B, hT, hB, hB₁, hB₂⟩ := GlobalTheory.T.frame_matrix_units_irreducible L ι r A hA
  have hq : ∀ a, (M a).IsQuasicoherent := fun a => (hM a).isQuasicoherent
  have hc : ∀ a, VB.IsFrame
      (fun i => QCoh.pullbackSections c (M a) (le_refl (⊤ : T.Opens)) (e a i)) :=
    fun a => (he a).pullback c
  have hm : ∀ a, VB.IsFrame (fun j => ∑ i, B a i j •
      QCoh.pullbackSections c (M a) (le_refl (⊤ : T.Opens)) (e a i)) :=
    fun a => FlagZ.Univ.isFrame_sum_smul_of_isUnit (hc a) (B a) (hB a)
  refine ⟨T, c, t₁, t₂, h₁, h₂, fun a => (hc a).iso (hm a), hT, fun a => ?_, fun a => ?_⟩
  · have H := GlobalTheory.T.pullback_frame_endomorphism_matrix _ _ c t₁ h₁ (M a) _ (e a) (he a) ((hc a).iso (hm a)).hom
      (B a) (fun i => (hc a).iso_hom_app (hm a) i) (𝟙 _) (fun i => by
        simp only [hB₁, Matrix.one_apply]
        simp [apply_ite])
    refine (cancel_mono ((Scheme.Modules.pullbackComp t₁ c).hom.app (M a) ≫
      (Scheme.Modules.pullbackCongr h₁).hom.app (M a) ≫
      (Scheme.Modules.pullbackId _).hom.app (M a))).1 ?_
    exact H.trans ((Category.comp_id _).trans (Category.id_comp _).symm)
  · exact GlobalTheory.T.pullback_frame_endomorphism_matrix _ _ c t₂ h₂ (M a) _ (e a) (he a) ((hc a).iso (hm a)).hom
      (B a) (fun i => (hc a).iso_hom_app (hm a) i) (φ a).hom (fun i => by
        simp only [hB₂]
        exact hAe a i)

end GlobalTheory.FlagPath

end
end

open CategoryTheory AlgebraicGeometry GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flags_over_field_irreducible_join : ∀ (L : Type) [Field L] (ι : Type) [Fintype ι] (M : ι → (Spec (CommRingCat.of L)).Modules) (r : ι → ℕ), (∀ a, VB.IsVB (M a) (r a)) → ∀ φ : ∀ a, M a ≅ M a, ∃ (T : Scheme.{0}) (c : T ⟶ Spec (CommRingCat.of L)) (t₁ t₂ : Spec (CommRingCat.of L) ⟶ T) (h₁ : t₁ ≫ c = 𝟙 _) (h₂ : t₂ ≫ c = 𝟙 _) (Φ : ∀ a, (Scheme.Modules.pullback c).obj (M a) ≅ (Scheme.Modules.pullback c).obj (M a)), IrreducibleSpace T ∧ (∀ a, (Scheme.Modules.pullback t₁).map (Φ a).hom = 𝟙 _) ∧ ∀ a, (Scheme.Modules.pullback t₂).map (Φ a).hom ≫ (Scheme.Modules.pullbackComp t₂ c).hom.app (M a) ≫ (Scheme.Modules.pullbackCongr h₂).hom.app (M a) ≫ (Scheme.Modules.pullbackId _).hom.app (M a) = ((Scheme.Modules.pullbackComp t₂ c).hom.app (M a) ≫ (Scheme.Modules.pullbackCongr h₂).hom.app (M a) ≫ (Scheme.Modules.pullbackId _).hom.app (M a)) ≫ (φ a).hom := by
  atlas_forward_decl GlobalTheory.FlagPath.exists_path_auto
end

section
section
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.FlagConnect

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPath

open Scheme.Modules in

theorem coh {X T B : Scheme.{0}} (t : X ⟶ T) (c : T ⟶ X) (s : X ⟶ B) (h : t ≫ c = 𝟙 _) (v : t ≫ c ≫ s = s)
    (E : B.Modules) :
    (pullbackComp t c).hom.app ((pullback s).obj E) ≫
      (pullbackCongr h).hom.app _ ≫ (pullbackId _).hom.app _ =
    (pullback t).map ((pullbackComp c s).hom.app E) ≫
      (pullbackComp t (c ≫ s)).hom.app E ≫ (pullbackCongr v).hom.app E := by
  have assoc := congr_arg (fun φ => φ.app E) (pseudofunctor_associativity t c s)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.rightUnitor_hom_app, Category.id_comp, Category.comp_id, eqToHom_app] at assoc
  have key : ∀ (u : X ⟶ X) (hu : u = 𝟙 X) (w : X ⟶ B) (hw : w = u ≫ s) (v' : w = s)
      (P : (pullback w).obj E = (pullback (u ≫ s)).obj E),
      eqToHom P ≫ (pullbackComp u s).inv.app E ≫ (pullbackCongr hu).hom.app _ ≫ (pullbackId X).hom.app _ =
        (pullbackCongr v').hom.app E := by
    intro u hu w hw v' P
    subst hu hw
    have unit := congr_arg (fun φ => φ.app E) (pseudofunctor_right_unitality s)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app, Category.comp_id, eqToHom_app] at unit
    simp only [eqToHom_refl, Category.id_comp, pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
    erw [Category.comp_id ((pullbackId X).hom.app ((pullback s).obj E))] at unit
    erw [Category.id_comp ((pullbackId X).hom.app ((pullback s).obj E))]
    erw [unit]
    simp [eqToIso.hom, eqToHom_app]
  have e1 : (pullbackComp t c).hom.app ((pullback s).obj E) =
      (pullback t).map ((pullbackComp c s).hom.app E) ≫ (pullbackComp t (c ≫ s)).hom.app E ≫
        eqToHom (by rw [Category.assoc]) ≫ (pullbackComp (t ≫ c) s).inv.app E := by
    rw [← cancel_epi ((pullbackComp t (c ≫ s)).inv.app E ≫ (pullback t).map ((pullbackComp c s).inv.app E)),
      ← cancel_mono ((pullbackComp (t ≫ c) s).hom.app E)]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [assoc]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
    simp
  rw [e1]
  simp only [Category.assoc]
  congr 2
  exact key _ h _ (Category.assoc _ _ _).symm v _

open Scheme.Modules in

theorem carries_of {X T B : Scheme.{0}} (s : X ⟶ B) (c : T ⟶ X) (t : X ⟶ T) (h : t ≫ c = 𝟙 X) {ι : Type}
    (E : ι → B.Modules) (r : ι → ℕ) (G₁ G' : ∀ a, Vert.Flag ((pullback s).obj (E a)) (r a))
    (Φ : ∀ a, (pullback c).obj ((pullback s).obj (E a)) ≅ (pullback c).obj ((pullback s).obj (E a)))
    (ψ : ∀ a, (pullback s).obj (E a) ≅ (pullback s).obj (E a))
    (hΦ : ∀ a, (pullback t).map (Φ a).hom ≫ (pullbackComp t c).hom.app _ ≫ (pullbackCongr h).hom.app _ ≫
      (pullbackId X).hom.app _ = ((pullbackComp t c).hom.app _ ≫ (pullbackCongr h).hom.app _ ≫
      (pullbackId X).hom.app _) ≫ (ψ a).hom)
    (hψ : ∀ a i, ∃ e : (G₁ a).F i ≅ (G' a).F i, e.hom ≫ (G' a).ι i = (G₁ a).ι i ≫ (ψ a).hom)
    (v : t ≫ c ≫ s = s) :
    Carries (c ≫ s) E r (fun a => ((G₁ a).pull c).ofIso (Φ a ≪≫ (pullbackComp c s).app (E a))) t s v G' := by
  intro a i
  obtain ⟨e, he⟩ := hψ a i
  refine ⟨(pullbackComp t c).app _ ≪≫ (pullbackCongr h).app _ ≪≫ (pullbackId X).app _ ≪≫ e, ?_⟩
  simp only [Iso.trans_hom, Iso.app_hom, Category.assoc, he]
  simp only [Vert.Flag.ofIso, Vert.Flag.pull, Functor.map_comp, Category.assoc, Iso.trans_hom, Iso.app_hom]
  rw [← coh t c s h v (E a)]
  simp only [Category.assoc] at hΦ
  rw [hΦ a, he]
  erw [← NatTrans.naturality_assoc, ← NatTrans.naturality_assoc, ← NatTrans.naturality_assoc]
  rfl

theorem exists_irreducible_family : ∀ (L : Type) [Field L] (B : Scheme.{0}) (s : Spec (CommRingCat.of L) ⟶ B)
    (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ)
    (G₁ G₂ : ∀ a, Vert.Flag ((Scheme.Modules.pullback s).obj (E a)) (r a)),
    ∃ (T : Scheme.{0}) (g : T ⟶ B) (t₁ t₂ : Spec (CommRingCat.of L) ⟶ T)
      (G : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (r a)) (v₁ : t₁ ≫ g = s) (v₂ : t₂ ≫ g = s),
      IrreducibleSpace T ∧ Carries g E r G t₁ s v₁ G₁ ∧ Carries g E r G t₂ s v₂ G₂ := by
  intro L _ B s ι _ E r G₁ G₂
  choose φ hφ using fun a => GlobalTheory.T.field_flags_conjugate_by_automorphism L _ (r a) (G₁ a) (G₂ a)
  obtain ⟨T, c, t₁, t₂, h₁, h₂, Φ, hT, hΦ₁, hΦ₂⟩ := GlobalTheory.T.flags_over_field_irreducible_join L ι
    (fun a => (Scheme.Modules.pullback s).obj (E a)) r (fun a => (G₁ a).isVB_self) φ
  have v₁ : t₁ ≫ c ≫ s = s := by rw [← Category.assoc, h₁, Category.id_comp]
  have v₂ : t₂ ≫ c ≫ s = s := by rw [← Category.assoc, h₂, Category.id_comp]
  refine ⟨T, c ≫ s, t₁, t₂, fun a => ((G₁ a).pull c).ofIso (Φ a ≪≫ (Scheme.Modules.pullbackComp c s).app (E a)),
    v₁, v₂, hT, ?_, ?_⟩
  · exact carries_of s c t₁ h₁ E r G₁ G₁ Φ (fun _ => Iso.refl _) (fun a => by rw [hΦ₁ a]; simp)
      (fun _ _ => ⟨Iso.refl _, by simp⟩) v₁
  · exact carries_of s c t₂ h₂ E r G₁ G₂ Φ φ hΦ₂ hφ v₂

end GlobalTheory.FlagPath

end
end

open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.FlagConnect
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flags_connected_irreducible_base : ∀ (L : Type) [Field L] (B : Scheme.{0}) (s : Spec (CommRingCat.of L) ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (G₁ G₂ : ∀ a, Vert.Flag ((Scheme.Modules.pullback s).obj (E a)) (r a)), ∃ (T : Scheme.{0}) (g : T ⟶ B) (t₁ t₂ : Spec (CommRingCat.of L) ⟶ T) (G : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (r a)) (v₁ : t₁ ≫ g = s) (v₂ : t₂ ≫ g = s), IrreducibleSpace T ∧ Carries g E r G t₁ s v₁ G₁ ∧ Carries g E r G t₂ s v₂ G₂ := by
  atlas_forward_decl GlobalTheory.FlagPath.exists_irreducible_family
end

section
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagConnect

theorem exists_irreducible_through : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → ∀ (L : Type) [Field L] (q₁ q₂ : Spec (CommRingCat.of L) ⟶ Y), q₁ ≫ π = q₂ ≫ π → ∃ (T : Scheme.{0}) (t₁ t₂ : Spec (CommRingCat.of L) ⟶ T) (f : T ⟶ Y), IrreducibleSpace T ∧ t₁ ≫ f = q₁ ∧ t₂ ≫ f = q₂ := by
  intro B Y π ι _ E r fl _ hF L _ q₁ q₂ hq
  obtain ⟨T, g, t₁, t₂, G, v₁, v₂, hT, h₁, h₂⟩ := GlobalTheory.T.flags_connected_irreducible_base L B (q₁ ≫ π) ι E r
    (carried π E r fl q₁ (q₁ ≫ π) rfl) (carried π E r fl q₂ (q₁ ≫ π) hq.symm)
  obtain ⟨f, ⟨wf, hf⟩, -⟩ := hF T g G
  have key : ∀ (q : Spec (CommRingCat.of L) ⟶ Y) (hq' : q ≫ π = q₁ ≫ π) (t : Spec (CommRingCat.of L) ⟶ T)
      (v : t ≫ g = q₁ ≫ π), Carries g E r G t (q₁ ≫ π) v (carried π E r fl q (q₁ ≫ π) hq') → t ≫ f = q := by
    intro q hq' t v ht
    obtain ⟨x, -, hx⟩ := hF _ (q₁ ≫ π) (carried π E r fl q (q₁ ≫ π) hq')
    have e₁ := hx q ⟨hq', carries_carried π E r fl q _ hq'⟩
    have e₂ := hx (t ≫ f) ⟨by rw [Category.assoc, wf, v], carries_comp π E r fl f g wf G t _ v _ _ hf ht⟩
    rw [e₁, e₂]
  exact ⟨T, t₁, t₂, f, hT, key q₁ rfl t₁ v₁ h₁, key q₂ hq.symm t₂ v₂ h₂⟩

end GlobalTheory.FlagConnect

end
end

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_points_irreducible_connected : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → ∀ (L : Type) [Field L] (q₁ q₂ : Spec (CommRingCat.of L) ⟶ Y), q₁ ≫ π = q₂ ≫ π → ∃ (T : Scheme.{0}) (t₁ t₂ : Spec (CommRingCat.of L) ⟶ T) (f : T ⟶ Y), IrreducibleSpace T ∧ t₁ ≫ f = q₁ ∧ t₂ ≫ f = q₂ := by
  atlas_forward_decl GlobalTheory.FlagConnect.exists_irreducible_through
end

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vector_bundle_over_field_has_flag : ∀ (K : Type) [Field K] (E : (Spec (CommRingCat.of K)).Modules) (n : ℕ), GlobalTheory.VB.IsVB E n → Nonempty (Vert.Flag E n) := by
  first | exact @GlobalTheory.Vert.Flag.nonempty_of_field | exact GlobalTheory.Vert.Flag.nonempty_of_field | (intros; apply GlobalTheory.Vert.Flag.nonempty_of_field <;> assumption)
end

section
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits

namespace GlobalTheory.FlagIrrFld

theorem isPreirreducible_of_connect {Y : Scheme.{0}}
    (h : ∀ y₁ y₂ : Y, ∃ (T : Scheme.{0}) (f : T ⟶ Y), IrreducibleSpace T ∧ y₁ ∈ Set.range f ∧ y₂ ∈ Set.range f) :
    IsPreirreducible (Set.univ : Set Y) := by
  rintro u v hu hv ⟨y₁, -, hy₁⟩ ⟨y₂, -, hy₂⟩
  obtain ⟨T, f, hT, ⟨t₁, rfl⟩, ⟨t₂, rfl⟩⟩ := h y₁ y₂
  obtain ⟨t, -, ht⟩ := (IrreducibleSpace.isIrreducible_univ T).isPreirreducible _ _
    (hu.preimage f.continuous) (hv.preimage f.continuous) ⟨t₁, trivial, hy₁⟩ ⟨t₂, trivial, hy₂⟩
  exact ⟨f t, trivial, ht⟩

theorem nonempty_of_field (K : Type) [Field K] (Y : Scheme.{0}) (π : Y ⟶ Spec (CommRingCat.of K)) (ι : Type)
    [Fintype ι] (E : ι → (Spec (CommRingCat.of K)).Modules) (r : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)) (hE : ∀ a, GlobalTheory.VB.IsVB (E a) (r a))
    (hF : IsFlagBundle π E r fl) : Nonempty Y := by
  have fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback (𝟙 (Spec (CommRingCat.of K)))).obj (E a)) (r a) :=
    fun a => (GlobalTheory.T.vector_bundle_over_field_has_flag K _ (r a) ((hE a).pullback _)).some
  obtain ⟨g', -, -⟩ := hF _ (𝟙 _) fl'
  obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  exact ⟨g' x⟩

theorem irreducibleSpace_of_isFlagBundle : ∀ (K : Type) [Field K] (Y : Scheme.{0}) (π : Y ⟶ Spec (CommRingCat.of K)) (ι : Type) [Fintype ι]
    (E : ι → (Spec (CommRingCat.of K)).Modules) (r : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)),
    (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → IrreducibleSpace Y := by
  intro K _ Y π ι _ E r fl hE hF
  haveI := nonempty_of_field K Y π ι E r fl hE hF
  refine { isPreirreducible_univ := isPreirreducible_of_connect fun y₁ y₂ => ?_, toNonempty := inferInstance }
  set p₁ := Y.fromSpecResidueField y₁
  set p₂ := Y.fromSpecResidueField y₂
  obtain ⟨x₁⟩ : Nonempty (Spec (Y.residueField y₁)) := inferInstance
  obtain ⟨x₂⟩ : Nonempty (Spec (Y.residueField y₂)) := inferInstance
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p₁ ≫ π) (g := p₂ ≫ π) x₁ x₂
    (Subsingleton.elim _ _)
  set P := pullback (p₁ ≫ π) (p₂ ≫ π)
  let L : Type := P.residueField z
  let u : Spec (CommRingCat.of L) ⟶ P := P.fromSpecResidueField z
  have hq : (u ≫ pullback.fst _ _ ≫ p₁) ≫ π = (u ≫ pullback.snd _ _ ≫ p₂) ≫ π := by
    simp only [Category.assoc]
    exact congrArg (u ≫ ·) pullback.condition
  obtain ⟨T, t₁, t₂, f, hT, h₁, h₂⟩ := GlobalTheory.T.flag_bundle_points_irreducible_connected _ Y π ι E r fl hE hF L _ _ hq
  obtain ⟨w⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
  have m₁ : p₁ ((pullback.fst (p₁ ≫ π) (p₂ ≫ π)) (u w)) = y₁ := by
    have := Scheme.range_fromSpecResidueField y₁ ▸ Set.mem_range_self (f := p₁) ((pullback.fst (p₁ ≫ π) (p₂ ≫ π)) (u w))
    exact this
  have m₂ : p₂ ((pullback.snd (p₁ ≫ π) (p₂ ≫ π)) (u w)) = y₂ := by
    have := Scheme.range_fromSpecResidueField y₂ ▸ Set.mem_range_self (f := p₂) ((pullback.snd (p₁ ≫ π) (p₂ ≫ π)) (u w))
    exact this
  refine ⟨T, f, hT, ⟨t₁ w, ?_⟩, ⟨t₂ w, ?_⟩⟩
  · rw [← m₁, ← Scheme.Hom.comp_apply, h₁]; rfl
  · rw [← m₂, ← Scheme.Hom.comp_apply, h₂]; rfl

end GlobalTheory.FlagIrrFld
end

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_over_field_irreducible : ∀ (K : Type) [Field K] (Y : Scheme.{0}) (π : Y ⟶ Spec (CommRingCat.of K)) (ι : Type) [Fintype ι] (E : ι → (Spec (CommRingCat.of K)).Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → IrreducibleSpace Y := by
  atlas_forward_decl GlobalTheory.FlagIrrFld.irreducibleSpace_of_isFlagBundle
end

section
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits

namespace GlobalTheory

theorem flagBundle_universallyOpen : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → UniversallyOpen π := by
  intro B Y π ι _ E r fl hE hF
  haveI := GlobalTheory.T.flag_bundle_smooth_relative_dimension B Y π ι E r fl hE hF
  haveI : Smooth π := SmoothOfRelativeDimension.smooth (∑ a, r a * (r a - 1) / 2) π
  infer_instance

end GlobalTheory
end

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_universally_open : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → UniversallyOpen π := by
  atlas_forward_decl GlobalTheory.flagBundle_universallyOpen
end

section
section
set_option autoImplicit false

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits

namespace GlobalTheory.CovTest

theorem IsFlagBundle.geometricallyIrreducible {B Y : Scheme.{0}} {π : Y ⟶ B} {ι : Type} [Fintype ι] {E : ι → B.Modules}
    {r : ι → ℕ} {fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)} (hE : ∀ a, GlobalTheory.VB.IsVB (E a) (r a))
    (hF : IsFlagBundle π E r fl) : GeometricallyIrreducible π := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  obtain ⟨fl', h'⟩ := GlobalTheory.T.flag_bundle_exists_after_base_change B Y _ π x ι E r fl hF
  exact GlobalTheory.T.flag_bundle_over_field_irreducible K _ (pullback.snd π x) ι _ r fl' (fun a => (hE a).pullback x) h'

theorem IsFlagBundle.irreducibleSpace : ∀ (B Y : Scheme.{0}) [IsIntegral B] [IsLocallyNoetherian B] (π : Y ⟶ B) (ι : Type)
    [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)),
    (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → IrreducibleSpace Y := by
  intro B Y _ _ π ι _ E r fl hE hF
  have := hF.geometricallyIrreducible hE
  have := GlobalTheory.T.flag_bundle_universally_open B Y π ι E r fl hE hF
  exact GeometricallyIrreducible.irreducibleSpace π π.isOpenMap

end GlobalTheory.CovTest
end

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_total_space_irreducible : ∀ (B Y : Scheme.{0}) [IsIntegral B] [IsLocallyNoetherian B] (π : Y ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → IrreducibleSpace Y := by
  atlas_forward_decl GlobalTheory.CovTest.IsFlagBundle.irreducibleSpace
end

section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.krull_dim_smooth_surjective_total : ∀ (B Y : Scheme.{0}) [IsLocallyNoetherian B] (π : Y ⟶ B) (n d : ℕ) [SmoothOfRelativeDimension n π], Function.Surjective π → topologicalKrullDim B = (d + 1 : ℕ) → topologicalKrullDim Y = (d + n + 1 : ℕ) := by
  first | exact @GlobalTheory.SmoothDimTotal.topologicalKrullDim_eq_of_smooth_surjective | exact GlobalTheory.SmoothDimTotal.topologicalKrullDim_eq_of_smooth_surjective | (intros; apply GlobalTheory.SmoothDimTotal.topologicalKrullDim_eq_of_smooth_surjective <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CovTest GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_pullback_base_change : ∀ (B Y B' : Scheme.{0}) (π : Y ⟶ B) (g : B' ⟶ B) (ι : Type) (E : ι → B.Modules) (n : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)), IsFlagBundle π E n fl →
    IsFlagBundle (pullback.snd π g) (fun a => (Scheme.Modules.pullback g).obj (E a)) n (fun a => bcFlag π g (fl a)) := by
  first | exact @GlobalTheory.CovTest.BCFlag.isFlagBundle_baseChange | exact GlobalTheory.CovTest.BCFlag.isFlagBundle_baseChange | (intros; apply GlobalTheory.CovTest.BCFlag.isFlagBundle_baseChange <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CovTest GlobalTheory.Published

namespace GlobalTheory.LineBundleBaseChange

theorem residueDegree_fst_ne_zero {X Y₁ Y₂ : Scheme.{0}} (f : Y₁ ⟶ X) (g : Y₂ ⟶ X) (z : ↥(pullback f g))
    (h : g.residueDegree (pullback.snd f g z) ≠ 0) : (pullback.fst f g).residueDegree z ≠ 0 := by
  let T : Scheme.Pullback.Triplet f g := Scheme.Pullback.Triplet.ofPoint z
  have hg : ((X.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom.Finite :=
    ((PullbackFinitePoint.residueDegree_ne_zero_iff_finite g _).1 h).comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (X.residueFieldCongr T.hy).inv).2)
  have hl : T.tensorInl.hom.Finite :=
    RingHom.finite_isStableUnderBaseChange.pushout_inl RingHom.finite_respectsIso _ _ hg
  let s : PrimeSpectrum T.tensor := Scheme.Pullback.SpecOfPoint z
  have hs : T.SpecTensorTo s = z := Scheme.Pullback.SpecTensorTo_SpecOfPoint z
  have hm : s.asIdeal.IsMaximal := by
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' T.tensorInl.hom hl.to_isIntegral s.asIdeal ?_
    have hp : (s.asIdeal.comap T.tensorInl.hom).IsPrime := inferInstance
    rw [Ideal.eq_bot_of_prime (s.asIdeal.comap T.tensorInl.hom)]
    exact Ideal.bot_isMaximal
  letI := Ideal.Quotient.field s.asIdeal
  let ρ : T.tensor ⟶ CommRingCat.of (T.tensor ⧸ s.asIdeal) := CommRingCat.ofHom (Ideal.Quotient.mk s.asIdeal)
  have hρ : ρ.hom.Finite := RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective
  let q : Spec (CommRingCat.of (T.tensor ⧸ s.asIdeal)) := (⊥ : PrimeSpectrum (T.tensor ⧸ s.asIdeal))
  have hq : Spec.map ρ q = s := PrimeSpectrum.ext Ideal.mk_ker
  have e : (Spec.map ρ ≫ T.SpecTensorTo) q = z := by
    rw [Scheme.Hom.comp_apply, hq, hs]
  rw [← e]
  refine PullbackFinitePoint.residueDegree_ne_zero_of_fieldPoint _ _ T.x (T.tensorInl ≫ ρ) (hρ.comp hl) ?_ q
  rw [Category.assoc, T.specTensorTo_fst, Spec.map_comp, Category.assoc]

theorem map_genericPoint_of_mem {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y) (x : X)
    (h : f x = genericPoint Y) : f (genericPoint X) = genericPoint Y :=
  ((h ▸ (genericPoint_specializes x).map f.continuous : f (genericPoint X) ⤳ genericPoint Y).antisymm
    (genericPoint_specializes _)).eq

theorem main : ∀ (k : Type) [CommRing k] (B Y B' : Scheme.{0}) [IsIntegral B] [IsIntegral Y] [IsIntegral B']
    (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ), IsArithVar q d → IsArithVar p (d + 1) → ∀ (π : Y ⟶ B) (_ : π ≫ q = p)
    (E : B.Modules), GlobalTheory.VB.IsVB E 2 → ∀ (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ g : B' ⟶ B, IsArithVar (g ≫ q) d →
    g (genericPoint B') = genericPoint B → g.residueDegree (genericPoint B') ≠ 0 →
    ∃ (_ : IsIntegral (pullback π g : Scheme.{0})), IsArithVar (pullback.fst π g ≫ p) (d + 1) ∧
      pullback.fst π g (genericPoint (pullback π g : Scheme.{0})) = genericPoint Y ∧
      (pullback.fst π g).residueDegree (genericPoint (pullback π g : Scheme.{0})) ≠ 0 := by
  intro k _ B Y B' _ _ _ q p d hq hp π w E hE fl hfl g hg hgen hdeg
  subst w
  have := hg.isLocallyNoetherian
  have hfl' := GlobalTheory.T.flag_bundle_pullback_base_change B Y B' π g Unit (fun _ => E) (fun _ => 2) (fun _ => fl) hfl
  have hE' : ∀ _ : Unit, GlobalTheory.VB.IsVB ((Scheme.Modules.pullback g).obj E) 2 := fun _ => hE.pullback g
  have hsm : SmoothOfRelativeDimension 1 (pullback.snd π g) := by
    simpa using GlobalTheory.T.flag_bundle_smooth_relative_dimension B' _ (pullback.snd π g) Unit _ _ _ hE' hfl'
  have hs' := GlobalTheory.T.flag_bundle_projection_surjective B' _ (pullback.snd π g) Unit _ _ _ hE' hfl'
  have hs := GlobalTheory.T.flag_bundle_projection_surjective B Y π Unit _ _ _ (fun _ => hE) hfl
  have := GlobalTheory.T.flag_bundle_total_space_irreducible B' _ (pullback.snd π g) Unit _ _ _ hE' hfl'
  have := SmoothOfRelativeDimension.smooth 1 (pullback.snd π g)
  have := GlobalTheory.geometricallyReduced_of_smooth (pullback.snd π g)
  have := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (pullback.snd π g)
  have hI : IsIntegral (pullback π g : Scheme.{0}) := isIntegral_of_irreducibleSpace_of_isReduced _
  have hπ : π (genericPoint Y) = genericPoint B := by
    obtain ⟨y, hy⟩ := hs (genericPoint B)
    exact map_genericPoint_of_mem π y hy
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := g) _ _ (hπ.trans hgen.symm)
  refine ⟨hI, ⟨hq.isDomain, hq.finite, hI, ?_, ?_, ?_⟩, map_genericPoint_of_mem _ z hz₁,
    residueDegree_fst_ne_zero π g _ ?_⟩
  · have : IsSeparated q := by
      obtain ⟨N, j, _, rfl⟩ := hq.isProjOver
      have := isProper_str k N
      infer_instance
    have h := ProjSpace.isProjOver_comp_of_isClosedImmersion (pullback.mapDesc π g q)
      (ProjSpace.isProjOver_pullback hp.isProjOver hg.isProjOver)
    rwa [pullback.lift_fst_assoc, Category.comp_id] at h
  · rw [← Category.assoc (pullback.fst π g), pullback.condition, Category.assoc (pullback.snd π g),
      Category.assoc (pullback.snd π g)]
    have := hg.flat
    infer_instance
  · exact GlobalTheory.T.krull_dim_smooth_surjective_total B' _ (pullback.snd π g) 1 d hs' hg.dim_eq
  · rw [map_genericPoint_of_mem _ z hz₂]
    exact hdeg

end GlobalTheory.LineBundleBaseChange

end
end
