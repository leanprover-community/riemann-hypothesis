import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleMayerVietorisChainsShortExact : Prop :=
  ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g → ∃ w, (ShortComplex.mk (biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g))) (biprod.desc ((chains R).map f) ((chains R).map g)) w).ShortExact
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleFreePresheafMayerVietorisShortExact : Prop :=
  ∀ (R : Type) [CommRing R] {P Q E : PSh} (f : P ⟶ E) (g : Q ⟶ E) [Mono f] [Mono g],
    Mono (biprod.lift ((free R).map (pullback.fst f g)) (-(free R).map (pullback.snd f g))) ∧
    ∃ w, (ShortComplex.mk (biprod.lift ((free R).map (pullback.fst f g)) (-(free R).map (pullback.snd f g)))
      (biprod.desc ((free R).map f) ((free R).map g)) w).Exact

theorem chainsXIso_nat (R : Type) [CommRing R] {E E' : Spc} (φ : E ⟶ E') (p : ℕ) :
    ((chains R).map φ).f (-(p : ℤ)) ≫ (chainsXIso R E' p).hom =
      (chainsXIso R E p).hom ≫ (free R).map (φ.app (op (SimplexCategory.mk p))) := by
  have h := HomologicalComplex.extendMap_f ((chainsN R).map φ) ComplexShape.embeddingDownNat (i := p) (i' := -(p:ℤ)) rfl
  have h2 : ((chains R).map φ).f (-(p:ℤ)) = (HomologicalComplex.extendMap ((chainsN R).map φ) ComplexShape.embeddingDownNat).f (-(p:ℤ)) := rfl
  rw [h2, h]
  simp only [chainsXIso]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem chains_isZero (R : Type) [CommRing R] (E : Spc) (n : ℤ) (hn : 0 < n) :
    IsZero (((chains R).obj E).X n) := by
  apply HomologicalComplex.isZero_extend_X
  intro i h
  change -(i:ℤ) = n at h
  omega

theorem chainsXIso_nat' (R : Type) [CommRing R] {E E' : Spc} (φ : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).inv ≫ ((chains R).map φ).f (-(p : ℤ)) =
      (free R).map (φ.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← chainsXIso_nat, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem sq1 (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (p : ℕ) :
    ((free R).map (pullbackObjIso f g (op (SimplexCategory.mk p))).inv ≫ (chainsXIso R (pullback f g) p).inv) ≫
      (biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g))).f (-(p:ℤ)) =
    biprod.lift ((free R).map (pullback.fst (f.app (op (SimplexCategory.mk p))) (g.app (op (SimplexCategory.mk p)))))
        (-(free R).map (pullback.snd (f.app (op (SimplexCategory.mk p))) (g.app (op (SimplexCategory.mk p))))) ≫
      (biprod.map (chainsXIso R U p).inv (chainsXIso R V p).inv ≫
        (HomologicalComplex.biprodXIso ((chains R).obj U) ((chains R).obj V) (-(p:ℤ))).inv) := by
  rw [← cancel_mono (HomologicalComplex.biprodXIso ((chains R).obj U) ((chains R).obj V) (-(p:ℤ))).hom]
  apply biprod.hom_ext
  · simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, HomologicalComplex.biprodXIso_hom_fst,
      biprod.map_fst, biprod.lift_fst_assoc]
    rw [← HomologicalComplex.comp_f, biprod.lift_fst, chainsXIso_nat', ← Category.assoc, ← Functor.map_comp,
      pullbackObjIso_inv_comp_fst]
  · simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, HomologicalComplex.biprodXIso_hom_snd,
      biprod.map_snd, biprod.lift_snd_assoc]
    rw [← HomologicalComplex.comp_f, biprod.lift_snd, HomologicalComplex.neg_f_apply, Preadditive.comp_neg,
      chainsXIso_nat']
    simp only [Preadditive.neg_comp, Preadditive.comp_neg]
    rw [← Category.assoc, ← Functor.map_comp, pullbackObjIso_inv_comp_snd]

theorem sq2 (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) (p : ℕ) :
    (biprod.map (chainsXIso R U p).inv (chainsXIso R V p).inv ≫
        (HomologicalComplex.biprodXIso ((chains R).obj U) ((chains R).obj V) (-(p:ℤ))).inv) ≫
      (biprod.desc ((chains R).map f) ((chains R).map g)).f (-(p:ℤ)) =
    biprod.desc ((free R).map (f.app (op (SimplexCategory.mk p)))) ((free R).map (g.app (op (SimplexCategory.mk p)))) ≫
      (chainsXIso R E p).inv := by
  apply biprod.hom_ext'
  · have h1 : biprod.inl ≫ (HomologicalComplex.biprodXIso ((chains R).obj U) ((chains R).obj V) (-(p:ℤ))).inv =
        (biprod.inl : (chains R).obj U ⟶ _).f (-(p:ℤ)) := by
      rw [Iso.comp_inv_eq]; apply biprod.hom_ext <;> simp [HomologicalComplex.biprodXIso_hom_fst,
        HomologicalComplex.biprodXIso_hom_snd, ← HomologicalComplex.comp_f]
    simp only [Category.assoc]
    rw [biprod.inl_map_assoc, reassoc_of% h1, ← HomologicalComplex.comp_f, biprod.inl_desc,
      chainsXIso_nat', biprod.inl_desc_assoc]
  · have h1 : biprod.inr ≫ (HomologicalComplex.biprodXIso ((chains R).obj U) ((chains R).obj V) (-(p:ℤ))).inv =
        (biprod.inr : (chains R).obj V ⟶ _).f (-(p:ℤ)) := by
      rw [Iso.comp_inv_eq]; apply biprod.hom_ext <;> simp [HomologicalComplex.biprodXIso_hom_fst,
        HomologicalComplex.biprodXIso_hom_snd, ← HomologicalComplex.comp_f]
    simp only [Category.assoc]
    rw [biprod.inr_map_assoc, reassoc_of% h1, ← HomologicalComplex.comp_f, biprod.inr_desc,
      chainsXIso_nat', biprod.inr_desc_assoc]

theorem etale_chains_mayer_vietoris_short_exact_of_free (hfree : EtaleFreePresheafMayerVietorisShortExact) : EtaleMayerVietorisChainsShortExact := by
  intro R _ U V E f g hc
  obtain ⟨hf, hg, hep⟩ := hc
  have w : biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g)) ≫
      biprod.desc ((chains R).map f) ((chains R).map g) = 0 := by
    rw [biprod.lift_desc, ← Functor.map_comp, Preadditive.neg_comp, ← Functor.map_comp, pullback.condition]
    simp
  refine ⟨w, ?_⟩
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  by_cases hn : 0 < n
  · have h1 := chains_isZero R (pullback f g) n hn
    have h3 := chains_isZero R E n hn
    have h2 : IsZero ((HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) n).obj
        ((chains R).obj U ⊞ (chains R).obj V)) :=
by
      have hU := chains_isZero R U n hn
      have hV := chains_isZero R V n hn
      refine IsZero.of_iso ?_ (HomologicalComplex.biprodXIso _ _ n)
      rw [IsZero.iff_id_eq_zero, ← biprod.total, hU.eq_of_tgt biprod.fst 0, hV.eq_of_tgt biprod.snd 0]
      simp
    refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_isZero_X₂ _ h2) ?_ ?_
    · exact ⟨fun a b _ => h1.eq_of_tgt a b⟩
    · exact ⟨fun a b _ => h3.eq_of_src a b⟩
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, n = -(p : ℤ) := ⟨(-n).toNat, by omega⟩
  obtain ⟨hmono, w', hex⟩ := hfree R (f.app (op (SimplexCategory.mk p))) (g.app (op (SimplexCategory.mk p)))
  have hT := ShortComplex.ShortExact.mk' hex hmono (hep _)
  refine ShortComplex.shortExact_of_iso ?_ hT
  refine ShortComplex.isoMk ?e1 ?e2 ?e3 ?c1 ?c2
  case e1 =>
    refine ?_ ≪≫ (chainsXIso R _ p).symm
    exact (free R).mapIso (pullbackObjIso f g _).symm
  case e2 => exact biprod.mapIso (chainsXIso R U p).symm (chainsXIso R V p).symm ≪≫
      (HomologicalComplex.biprodXIso _ _ _).symm
  case e3 => exact (chainsXIso R E p).symm
  case c1 => exact sq1 R f g p
  case c2 => exact sq2 R f g p

end LateralTheory.EtaleFoundations
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.MvFree

theorem finsupp_mv {T α β γ M : Type*} [AddCommGroup M] (p1 : T → α) (p2 : T → β) (f : α → γ) (g : β → γ)
    (hf : Function.Injective f) (hg : Function.Injective g) (hc : ∀ t, f (p1 t) = g (p2 t))
    (hj : ∀ t t', p1 t = p1 t' ∧ p2 t = p2 t' → t = t')
    (hs : ∀ x y, f x = g y → ∃ t, p1 t = x ∧ p2 t = y) :
    Function.Injective (Finsupp.mapDomain (M := M) p1) ∧
    ∀ (p : α →₀ M) (q : β →₀ M), Finsupp.mapDomain f p + Finsupp.mapDomain g q = 0 →
      ∃ c : T →₀ M, Finsupp.mapDomain p1 c = p ∧ Finsupp.mapDomain p2 c = -q := by
  classical
  have hp1 : Function.Injective p1 := fun t t' h =>
    hj t t' ⟨h, hg (by rw [← hc, ← hc, h])⟩
  have hh : Function.Injective (f ∘ p1) := hf.comp hp1
  refine ⟨Finsupp.mapDomain_injective hp1, fun p q hpq => ?_⟩
  set z := Finsupp.mapDomain f p with hz
  have hz' : z = Finsupp.mapDomain g (-q) := by
    have h0 : Finsupp.mapDomain g q + Finsupp.mapDomain g (-q) = 0 := by
      rw [← Finsupp.mapDomain_add, add_neg_cancel, Finsupp.mapDomain_zero]
    rw [hz]; exact (eq_neg_of_add_eq_zero_left hpq).trans (eq_neg_of_add_eq_zero_right h0).symm
  have hsupp : (z.support : Set γ) ⊆ Set.range (f ∘ p1) := by
    intro x hx
    have h1 : x ∈ Set.range f := by
      have := Finsupp.mapDomain_support (f := f) (s := p) (by rw [← hz]; exact hx)
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 this; exact ⟨a, rfl⟩
    have h2 : x ∈ Set.range g := by
      rw [hz'] at hx
      have := Finsupp.mapDomain_support (f := g) (s := -q) hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 this; exact ⟨a, rfl⟩
    obtain ⟨a, rfl⟩ := h1
    obtain ⟨b, hb⟩ := h2
    obtain ⟨t, ht, -⟩ := hs a b hb.symm
    exact ⟨t, by simp [ht]⟩
  refine ⟨Finsupp.comapDomain (f ∘ p1) z hh.injOn, ?_, ?_⟩
  · apply Finsupp.mapDomain_injective hf
    rw [← Finsupp.mapDomain_comp, Finsupp.mapDomain_comapDomain _ hh _ hsupp]
  · apply Finsupp.mapDomain_injective hg
    have : g ∘ p2 = f ∘ p1 := funext fun t => (hc t).symm
    rw [← Finsupp.mapDomain_comp, this, Finsupp.mapDomain_comapDomain _ hh _ hsupp, hz']

theorem exact_of_eval {C D : Type*} [Category C] [Category D] [Abelian D]
    (S : ShortComplex (C ⥤ D)) (h : ∀ X, (S.map ((evaluation C D).obj X)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  apply Functor.isZero
  intro X
  exact ((ShortComplex.exact_iff_isZero_homology _).1 (h X)).of_iso (S.mapHomologyIso ((evaluation C D).obj X)).symm

end LateralTheory.EtaleFoundations.MvFree

namespace LateralTheory.EtaleFoundations.MvFree

noncomputable def mvIso {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D] (G : C ⥤ D) [G.Additive] {X1 A B X3 : C}
    (a : X1 ⟶ A) (b : X1 ⟶ B) (c : A ⟶ X3) (d : B ⟶ X3)
    (w : biprod.lift a (-b) ≫ biprod.desc c d = 0)
    (w' : biprod.lift (G.map a) (-G.map b) ≫ biprod.desc (G.map c) (G.map d) = 0) :
    (ShortComplex.mk _ _ w).map G ≅ ShortComplex.mk _ _ w' := by
  haveI := preservesBinaryBiproducts_of_preservesBiproducts G
  exact ShortComplex.isoMk (Iso.refl _) (G.mapBiprod A B) (Iso.refl _)
    (by show 𝟙 _ ≫ biprod.lift (G.map a) (-G.map b) = G.map (biprod.lift a (-b)) ≫ (G.mapBiprod A B).hom
        rw [biprod.map_lift_mapBiprod, Functor.map_neg, Category.id_comp])
    (by dsimp; rw [← biprod.mapBiprod_inv_map_desc]; erw [Iso.hom_inv_id_assoc]; simp; exact (Category.comp_id _).symm)

theorem mono_f_of_iso {C : Type*} [Category C] [HasZeroMorphisms C] {S T : ShortComplex C}
    (e : S ≅ T) [Mono S.f] : Mono T.f := by
  have h : T.f = e.inv.τ₁ ≫ S.f ≫ e.hom.τ₂ := by
    rw [← e.hom.comm₁₂, ← Category.assoc, ← ShortComplex.comp_τ₁, e.inv_hom_id, ShortComplex.id_τ₁,
      Category.id_comp]
  rw [h]; infer_instance

theorem biprod_ext_el {S : Type*} [Ring S] {A B : ModuleCat.{1} S} (z z' : ↑(A ⊞ B))
    (h1 : (biprod.fst : A ⊞ B ⟶ A) z = (biprod.fst : A ⊞ B ⟶ A) z')
    (h2 : (biprod.snd : A ⊞ B ⟶ B) z = (biprod.snd : A ⊞ B ⟶ B) z') :
    z = z' := by
  have e : ∀ w : ↑(A ⊞ B), (biprod.inl : A ⟶ A ⊞ B) ((biprod.fst : A ⊞ B ⟶ A) w) + (biprod.inr : B ⟶ A ⊞ B) ((biprod.snd : A ⊞ B ⟶ B) w) = w :=
    fun w => by
      have h := ConcreteCategory.congr_hom (biprod.total (X := A) (Y := B)) w
      rw [ConcreteCategory.id_apply] at h
      conv_rhs => rw [← h]
      rfl
  rw [← e z, ← e z', h1, h2]

theorem mc_exact {S : Type*} [Ring S] {X1 A B X3 : ModuleCat.{1} S} (u : X1 ⟶ A) (v : X1 ⟶ B)
    (c : A ⟶ X3) (d : B ⟶ X3) (w : biprod.lift u (-v) ≫ biprod.desc c d = 0)
    (hu : Function.Injective u)
    (hex : ∀ p q, c p + d q = 0 → ∃ x, u x = p ∧ v x = -q) :
    Mono (biprod.lift u (-v)) ∧ (ShortComplex.mk (biprod.lift u (-v)) (biprod.desc c d) w).Exact := by
  constructor
  · have : Mono u := (ModuleCat.mono_iff_injective u).2 hu
    have : Mono (biprod.lift u (-v) ≫ biprod.fst) := by rw [biprod.lift_fst]; infer_instance
    exact mono_of_mono _ biprod.fst
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x2 hx2
    have hx2' : c ((biprod.fst : A ⊞ B ⟶ A) x2) + d ((biprod.snd : A ⊞ B ⟶ B) x2) = 0 := by
      have h : (biprod.desc c d : A ⊞ B ⟶ X3) x2 = 0 := hx2
      rw [biprod.desc_eq] at h
      simpa using h
    obtain ⟨x, h1, h2⟩ := hex _ _ hx2'
    refine ⟨x, ?_⟩
    apply biprod_ext_el
    · dsimp; rw [← ConcreteCategory.comp_apply, biprod.lift_fst, h1]
    · dsimp; rw [← ConcreteCategory.comp_apply, biprod.lift_snd]
      simp [h2]

theorem pointwise (R : Type) [CommRing R] {P Q E : PSh} (f : P ⟶ E) (g : Q ⟶ E) [Mono f] [Mono g]
    (X : Scheme.{0}ᵒᵖ) (w) :
    Mono (biprod.lift (((freeP R).map (pullback.fst f g)).app X) (-((freeP R).map (pullback.snd f g)).app X)) ∧
    (ShortComplex.mk (biprod.lift (((freeP R).map (pullback.fst f g)).app X) (-((freeP R).map (pullback.snd f g)).app X))
      (biprod.desc (((freeP R).map f).app X) (((freeP R).map g).app X)) w).Exact := by
  have hpb := (IsPullback.of_hasPullback f g).map ((evaluation _ _).obj X)
  rw [Types.isPullback_iff] at hpb
  obtain ⟨hw, hj, hs⟩ := hpb
  dsimp at hw hj hs
  have hf : Function.Injective (f.app X) := (mono_iff_injective (f.app X)).1 inferInstance
  have hg : Function.Injective (g.app X) := (mono_iff_injective (g.app X)).1 inferInstance
  obtain ⟨hinj, hex⟩ := finsupp_mv (M := ULift.{1} R)
    (fun y : ULift.{1} ((pullback f g).obj X) => ULift.up ((pullback.fst f g).app X y.down))
    (fun y : ULift.{1} ((pullback f g).obj X) => ULift.up ((pullback.snd f g).app X y.down))
    (fun y : ULift.{1} (P.obj X) => ULift.up (f.app X y.down))
    (fun y : ULift.{1} (Q.obj X) => ULift.up (g.app X y.down))
    (fun x y h => ULift.ext _ _ (hf (congrArg ULift.down h)))
    (fun x y h => ULift.ext _ _ (hg (congrArg ULift.down h)))
    (fun t => congrArg ULift.up (by simpa using ConcreteCategory.congr_hom hw t.down))
    (fun t t' h => ULift.ext _ _ (hj _ _ ⟨congrArg ULift.down h.1, congrArg ULift.down h.2⟩))
    (fun x y h => by
      obtain ⟨t, h1, h2⟩ := hs x.down y.down (congrArg ULift.down h)
      exact ⟨ULift.up t, congrArg ULift.up h1, congrArg ULift.up h2⟩)
  exact mc_exact _ _ _ _ w hinj (fun p q h => hex p q h)

end LateralTheory.EtaleFoundations.MvFree

namespace LateralTheory.EtaleFoundations

open MvFree in
theorem etale_free_presheaf_mayer_vietoris_short_exact_holds : EtaleFreePresheafMayerVietorisShortExact := by
  intro R _ P Q E f g _ _
  have w0 : biprod.lift ((freeP R).map (pullback.fst f g)) (-(freeP R).map (pullback.snd f g)) ≫
      biprod.desc ((freeP R).map f) ((freeP R).map g) = 0 := by
    rw [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp,
      pullback.condition, add_neg_cancel]
  let S := ShortComplex.mk _ _ w0
  have hev : ∀ X, Mono ((S.map ((evaluation _ _).obj X)).f) ∧ (S.map ((evaluation _ _).obj X)).Exact := by
    intro X
    have w1 : biprod.lift (((freeP R).map (pullback.fst f g)).app X) (-((freeP R).map (pullback.snd f g)).app X) ≫
        biprod.desc (((freeP R).map f).app X) (((freeP R).map g).app X) = 0 := by
      rw [biprod.lift_desc, Preadditive.neg_comp, ← NatTrans.comp_app, ← NatTrans.comp_app,
        ← Functor.map_comp, ← Functor.map_comp, pullback.condition, add_neg_cancel]
    obtain ⟨hm, hx⟩ := pointwise R f g X w1
    let e := mvIso ((evaluation _ _).obj X) _ _ _ _ w0 w1
    exact ⟨@mono_f_of_iso _ _ _ _ _ e.symm hm, ShortComplex.exact_of_iso e.symm hx⟩
  have hSm : Mono S.f := by
    have : ∀ X, Mono (S.f.app X) := fun X => (hev X).1
    exact NatTrans.mono_of_mono_app _
  have hSe : S.Exact := exact_of_eval S (fun X => (hev X).2)
  let G := presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))
  have w2 : biprod.lift (G.map ((freeP R).map (pullback.fst f g))) (-G.map ((freeP R).map (pullback.snd f g))) ≫
      biprod.desc (G.map ((freeP R).map f)) (G.map ((freeP R).map g)) = 0 := by
    rw [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp,
      ← Functor.map_comp, ← Functor.map_comp, pullback.condition, add_neg_cancel]
  let e := mvIso G _ _ _ _ w0 w2
  have hGm : Mono ((S.map G).f) := (inferInstance : Mono (G.map S.f))
  exact ⟨mono_f_of_iso e, w2, ShortComplex.exact_of_iso e (hSe.map G)⟩

end LateralTheory.EtaleFoundations
end

section
namespace LateralTheory.Fin.EtaleMayerVietorisChainsShortExact
theorem etale_mayer_vietoris_short_exact_sequence_free_of_components : LateralTheory.EtaleFoundations.EtaleFreePresheafMayerVietorisShortExact := by
  apply LateralTheory.EtaleFoundations.etale_free_presheaf_mayer_vietoris_short_exact_holds
theorem etale_mayer_vietoris_short_exact_sequence_of_components : LateralTheory.EtaleFoundations.EtaleMayerVietorisChainsShortExact := by
  apply LateralTheory.EtaleFoundations.etale_chains_mayer_vietoris_short_exact_of_free <;> first | exact etale_mayer_vietoris_short_exact_sequence_free_of_components
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleMayerVietorisChainsShortExact := etale_mayer_vietoris_short_exact_sequence_of_components
end LateralTheory.Fin.EtaleMayerVietorisChainsShortExact
end
