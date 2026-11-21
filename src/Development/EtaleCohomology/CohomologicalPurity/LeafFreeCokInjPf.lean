import Development.EtaleCohomology.CohomologicalPurity.LeafExcSheafCut

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

def pcok (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A) (b : B' ⟶ B)
    (w : i' ≫ b = a ≫ i) : cokernel ((freeP R).map i') ⟶ cokernel ((freeP R).map i) :=
  cokernel.map _ _ ((freeP R).map a) ((freeP R).map b) (by rw [← Functor.map_comp, ← Functor.map_comp, w])

theorem isIso_cokernel_map_of_etale_local_iso (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
    (b : B' ⟶ B) (w : i' ≫ b = a ≫ i) (hW : Scheme.etaleTopology.W (pcok R i' i a b w)) :
    IsIso (cokernel.map ((free R).map i') ((free R).map i) ((free R).map a) ((free R).map b)
      (by rw [← Functor.map_comp, ← Functor.map_comp, w])) := by
  rw [GrothendieckTopology.W_iff] at hW
  let G := presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))
  have w' : (freeP R).map i' ≫ (freeP R).map b = (freeP R).map a ≫ (freeP R).map i := by
    rw [← Functor.map_comp, ← Functor.map_comp, w]
  have key := cokernel_map_comp_cokernelComparison ((freeP R).map i') G ((freeP R).map i) ((freeP R).map a)
    ((freeP R).map b) w'
  have h2 : IsIso (cokernelComparison ((freeP R).map i') G ≫ G.map (pcok R i' i a b w)) := by
    have : IsIso (G.map (pcok R i' i a b w)) := hW
    infer_instance
  have h3 : IsIso (cokernel.map (G.map ((freeP R).map i')) (G.map ((freeP R).map i)) (G.map ((freeP R).map a))
      (G.map ((freeP R).map b)) (by rw [← G.map_comp, w', G.map_comp])) := by
    have h4 : IsIso (cokernel.map (G.map ((freeP R).map i')) (G.map ((freeP R).map i)) (G.map ((freeP R).map a))
      (G.map ((freeP R).map b)) (by rw [← G.map_comp, w', G.map_comp]) ≫ cokernelComparison _ G) := by
      rw [key]; exact h2
    exact IsIso.of_isIso_comp_right _ (cokernelComparison ((freeP R).map i) G)
  exact h3

def LeafFreeCokSurj : Prop := ∀ (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
  (b : B' ⟶ B) (w : i' ≫ b = a ≫ i),
  (∀ (T : Scheme.{0}) (y : B.obj (op T)), ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
    (∃ x : A.obj (op V), i.app (op V) x = B.map g.op y) ∨ ∃ y' : B'.obj (op V), b.app (op V) y' = B.map g.op y) →
  Presheaf.IsLocallySurjective Scheme.etaleTopology (pcok R i' i a b w)

def LeafFreeCokInj : Prop := ∀ (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
  (b : B' ⟶ B) (w : i' ≫ b = a ≫ i),
  (∀ (T : Scheme.{0}) (y : B'.obj (op T)) (x : A.obj (op T)), i.app (op T) x = b.app (op T) y →
    ∃ x' : A'.obj (op T), i'.app (op T) x' = y) →
  (∀ (T : Scheme.{0}) (y₁ y₂ : B'.obj (op T)), b.app (op T) y₁ = b.app (op T) y₂ →
    ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
      B'.map g.op y₁ = B'.map g.op y₂ ∨ ∃ x : A.obj (op V), i.app (op V) x = b.app (op V) (B'.map g.op y₁)) →
  Presheaf.IsLocallyInjective Scheme.etaleTopology (pcok R i' i a b w)

theorem LeafFreeCok_of (hS : LeafFreeCokSurj) (hI : LeafFreeCokInj) : LeafFreeCok := by
  intro R _ A' B' A B i' i a b w h1 h2 h3
  apply isIso_cokernel_map_of_etale_local_iso
  have := hS R i' i a b w h2
  have := hI R i' i a b w h1 h3
  exact GrothendieckTopology.W_of_isLocallyBijective _ _

end LateralTheory.CohomologicalPurity
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

variable {R : Type} [CommRing R]

theorem imageSieve_add' {F G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : F ⟶ G) {T : Scheme.{0}}
    (s₁ s₂ : G.obj (op T)) :
    Presheaf.imageSieve f s₁ ⊓ Presheaf.imageSieve f s₂ ≤ Presheaf.imageSieve f (s₁ + s₂) := by
  rintro V g ⟨⟨t₁, h₁⟩, ⟨t₂, h₂⟩⟩
  exact ⟨t₁ + t₂, by rw [map_add, map_add, h₁, h₂]⟩

theorem imageSieve_smul' {F G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : F ⟶ G) {T : Scheme.{0}}
    (r : ULift.{1} R) (s : G.obj (op T)) :
    Presheaf.imageSieve f s ≤ Presheaf.imageSieve f (r • s) := by
  rintro V g ⟨t, h⟩
  exact ⟨r • t, by rw [map_smul, map_smul, h]⟩

theorem imageSieve_zero' {F G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : F ⟶ G) {T : Scheme.{0}} :
    Presheaf.imageSieve f (0 : G.obj (op T)) = ⊤ := by
  ext V g
  simp only [Sieve.top_apply, iff_true]
  exact ⟨0, by rw [map_zero, map_zero]⟩

theorem pcok_π_apply (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
    (b : B' ⟶ B) (w : i' ≫ b = a ≫ i) (V : Scheme.{0}ᵒᵖ) (m : ((freeP R).obj B').obj V) :
    (pcok R i' i a b w).app V ((cokernel.π ((freeP R).map i')).app V m) =
      (cokernel.π ((freeP R).map i)).app V (((freeP R).map b).app V m) := by
  have e : cokernel.π ((freeP R).map i') ≫ pcok R i' i a b w = (freeP R).map b ≫ cokernel.π _ := by
    simp [pcok]
  have := ConcreteCategory.congr_hom (NatTrans.congr_app e V) m
  simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using this

theorem π_freeP_apply (R : Type) [CommRing R] {A B : PSh} (i : A ⟶ B) (V : Scheme.{0}ᵒᵖ)
    (m : ((freeP R).obj A).obj V) :
    (cokernel.π ((freeP R).map i)).app V (((freeP R).map i).app V m) = 0 := by
  have := ConcreteCategory.congr_hom (NatTrans.congr_app (cokernel.condition ((freeP R).map i)) V) m
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at this
  rw [this]; rfl

theorem freePresheaf_map_freeMk (R : Type) [CommRing R] {A B : PSh} (i : A ⟶ B) (V : Scheme.{0}ᵒᵖ) (x : A.obj V) :
    ((freeP R).map i).app V (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (i.app V x)) := by
  exact ModuleCat.free_map_apply _ _

theorem freePresheaf_obj_map_freeMk (R : Type) [CommRing R] (B : PSh) {V W : Scheme.{0}ᵒᵖ} (g : V ⟶ W) (x : B.obj V) :
    ((freeP R).obj B).map g (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (B.map g x)) := by
  exact ModuleCat.free_map_apply _ _

theorem π_app_surj (R : Type) [CommRing R] {A B : PSh} (i : A ⟶ B) (V : Scheme.{0}ᵒᵖ) :
    Function.Surjective ((cokernel.π ((freeP R).map i)).app V) := by
  have : Epi ((cokernel.π ((freeP R).map i)).app V) := inferInstance
  exact (ModuleCat.epi_iff_surjective _).1 this

theorem exists_finset_adjoin_laurent_preimage (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
    (b : B' ⟶ B) (w : i' ≫ b = a ≫ i)
    (h2 : ∀ (T : Scheme.{0}) (y : B.obj (op T)), ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
      (∃ x : A.obj (op V), i.app (op V) x = B.map g.op y) ∨ ∃ y' : B'.obj (op V), b.app (op V) y' = B.map g.op y)
    (T : Scheme.{0}) (v : ((freeP R).obj B).obj (op T)) :
    Presheaf.imageSieve (pcok R i' i a b w) ((cokernel.π ((freeP R).map i)).app (op T) v) ∈
      Scheme.etaleTopology T := by
  let J := Scheme.etaleTopology.{0}
  let N : Submodule (ULift.{1} R) (((freeP R).obj B).obj (op T)) :=
    { carrier := {v | Presheaf.imageSieve (pcok R i' i a b w) ((cokernel.π ((freeP R).map i)).app (op T) v) ∈ J T}
      zero_mem' := by
        simp only [Set.mem_setOf_eq]; rw [map_zero, imageSieve_zero']; exact J.top_mem T
      add_mem' := fun {v₁ v₂} h₁ h₂ => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_add]; exact J.superset_covering (imageSieve_add' _ _ _) (J.intersection_covering h₁ h₂)
      smul_mem' := fun r v h => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_smul]; exact J.superset_covering (imageSieve_smul' _ _ _) h }
  have gen : ∀ x, ModuleCat.freeMk x ∈ N := by
    rintro ⟨y⟩
    show Presheaf.imageSieve _ _ ∈ J T
    obtain ⟨S, hS, hS'⟩ := h2 T y
    refine J.superset_covering ?_ hS
    intro V g hg
    have nat := NatTrans.naturality_apply (cokernel.π ((freeP R).map i)) g.op (ModuleCat.freeMk (ULift.up y))
    rcases hS' g hg with ⟨x₀, hx₀⟩ | ⟨y', hy'⟩
    · refine ⟨0, ?_⟩
      rw [map_zero]; erw [← nat]
      rw [freePresheaf_obj_map_freeMk]; erw [← hx₀]; rw [← freePresheaf_map_freeMk R i (op V) x₀]; exact (π_freeP_apply R i (op V) _).symm
    · refine ⟨_, (pcok_π_apply R i' i a b w (op V) (ModuleCat.freeMk (ULift.up y'))).trans ?_⟩
      rw [freePresheaf_map_freeMk R b (op V) y']; erw [hy', ← freePresheaf_obj_map_freeMk R B g.op y]; exact nat
  show v ∈ N
  induction v using Finsupp.induction_linear with
  | zero => exact N.zero_mem
  | add v₁ v₂ h₁ h₂ => exact N.add_mem h₁ h₂
  | single x r =>
    have := N.smul_mem r (gen x)
    convert this using 1
    first
    | exact (Finsupp.smul_single_one x r).symm
    | (unfold ModuleCat.freeMk; erw [Finsupp.smul_single_one])

theorem leafFreeCokSurj : LeafFreeCokSurj := by
  intro R _ A' B' A B i' i a b w h2
  constructor
  intro T s
  obtain ⟨v, rfl⟩ := π_app_surj R i (op T) s
  exact exists_finset_adjoin_laurent_preimage R i' i a b w h2 T v

theorem LeafFreeCok_of_inj (hI : LeafFreeCokInj) : LeafFreeCok := LeafFreeCok_of leafFreeCokSurj hI

end LateralTheory.CohomologicalPurity
end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
namespace LateralTheory.CohomologicalPurity

theorem exact_app_of_π {R : Type} [CommRing R] {F G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : F ⟶ G)
    (V : Scheme.{0}ᵒᵖ) (m : G.obj V) (hm : (cokernel.π f).app V m = 0) : ∃ n, f.app V n = m := by
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.Exact := S.exact_of_g_is_cokernel (cokernelIsCokernel f)
  have h2 := hS.map ((evaluation _ _).obj V)
  rw [ShortComplex.moduleCat_exact_iff] at h2
  exact h2 m hm

theorem mapDomain_apply_eq_sum {α β M : Type*} [AddCommMonoid M] [DecidableEq β] (v : α →₀ M) (f : α → β) (t : β) :
    Finsupp.mapDomain f v t = ∑ a ∈ v.support with f a = t, v a := by
  classical
  unfold Finsupp.mapDomain
  rw [Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finsupp.single_apply]

theorem core {α β γ M : Type*} [AddCommMonoid M] (v : α →₀ M) (f : α → β) (r : α → γ)
    (Q : β → Prop) (P : γ → Prop)
    (hv : ∀ t, ¬ Q t → Finsupp.mapDomain f v t = 0)
    (hQ : ∀ a, Q (f a) → P (r a))
    (hP : ∀ a₁ a₂, f a₁ = f a₂ → P (r a₁) → P (r a₂))
    (h : ∀ a₁ ∈ v.support, ∀ a₂ ∈ v.support, f a₁ = f a₂ → r a₁ = r a₂ ∨ P (r a₁)) :
    ∀ z, ¬ P z → Finsupp.mapDomain r v z = 0 := by
  classical
  intro z hz
  rw [mapDomain_apply_eq_sum]
  set s' := v.support.filter (fun a => r a = z)
  rw [← Finset.sum_fiberwise_of_maps_to (s := s') (t := s'.image f) (g := f)
    (fun a ha => Finset.mem_image_of_mem f ha)]
  refine Finset.sum_eq_zero fun t ht => ?_
  obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.1 ht
  have ha₀' := Finset.mem_filter.1 ha₀
  have hQ0 : ¬ Q (f a₀) := fun hq => hz (ha₀'.2 ▸ hQ a₀ hq)
  have e : (s'.filter fun a => f a = f a₀) = v.support.filter (fun a => f a = f a₀) := by
    ext a
    simp only [s', Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      rcases h a h1 a₀ ha₀'.1 h3 with e | p
      · rw [e, ha₀'.2]
      · exact absurd (ha₀'.2 ▸ hP a a₀ h3 p) hz
  rw [e]
  have := mapDomain_apply_eq_sum v f (f a₀)
  rw [hv _ hQ0] at this
  convert this.symm

theorem exists_covering_finset {T : Scheme.{0}} {ι : Type*} (s : Finset ι)
    (Pr : ι → ∀ ⦃V : Scheme.{0}⦄, (V ⟶ T) → Prop)
    (hPr : ∀ p ∈ s, ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g → Pr p g) :
    ∃ S ∈ Scheme.etaleTopology T, ∀ p ∈ s, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g → Pr p g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, Scheme.etaleTopology.top_mem T, by simp⟩
  | insert q s hq ih =>
    obtain ⟨S₁, h₁, H₁⟩ := ih (fun p hp => hPr p (Finset.mem_insert_of_mem hp))
    obtain ⟨S₂, h₂, H₂⟩ := hPr q (Finset.mem_insert_self q s)
    refine ⟨S₁ ⊓ S₂, Scheme.etaleTopology.intersection_covering h₁ h₂, ?_⟩
    intro p hp V g hg
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact H₂ g hg.2
    · exact H₁ p hp g hg.1

theorem mem_range_mapDomain {α β M : Type*} [AddCommMonoid M] (u : α → β) (w : β →₀ M)
    (hw : ∀ z, (¬ ∃ x, u x = z) → w z = 0) : ∃ n : α →₀ M, Finsupp.mapDomain u n = w := by
  have hmem : w ∈ Finsupp.supported M ℕ (u '' Set.univ) := by
    rw [Finsupp.mem_supported]
    intro z hz
    by_contra hc
    exact (Finsupp.mem_support_iff.1 hz) (hw z (fun ⟨x, hx⟩ => hc ⟨x, trivial, hx⟩))
  rw [← Finsupp.lmapDomain_supported] at hmem
  obtain ⟨n, _, hn⟩ := hmem
  exact ⟨n, hn⟩

theorem leafFreeCokInj : LeafFreeCokInj := by
  intro R _ A' B' A B i' i a b w h1 h3
  have key : ∀ (T : Scheme.{0}) (z : (cokernel ((freeP R).map i')).obj (op T)),
      (pcok R i' i a b w).app (op T) z = 0 → Presheaf.equalizerSieve z 0 ∈ Scheme.etaleTopology T := by
    intro T z hz
    obtain ⟨v, rfl⟩ := π_app_surj R i' (op T) z
    rw [pcok_π_apply] at hz
    obtain ⟨n, hn⟩ := exact_app_of_π _ _ _ hz
    have hn' : Finsupp.mapDomain (fun x : ULift.{1} (A.obj (op T)) => ULift.up (i.app (op T) x.down)) n =
        Finsupp.mapDomain (fun x : ULift.{1} (B'.obj (op T)) => ULift.up (b.app (op T) x.down)) v := hn
    let Pr : (ULift.{1} (B'.obj (op T)) × ULift.{1} (B'.obj (op T))) → ∀ ⦃V : Scheme.{0}⦄, (V ⟶ T) → Prop :=
      fun p V g => b.app (op T) p.1.down = b.app (op T) p.2.down →
        B'.map g.op p.1.down = B'.map g.op p.2.down ∨
          ∃ x : A.obj (op V), i.app (op V) x = b.app (op V) (B'.map g.op p.1.down)
    obtain ⟨S, hS, HS⟩ := exists_covering_finset (v.support ×ˢ v.support) Pr (by
      intro p _
      by_cases he : b.app (op T) p.1.down = b.app (op T) p.2.down
      · obtain ⟨S, hS, H⟩ := h3 T p.1.down p.2.down he
        exact ⟨S, hS, fun V g hg _ => H g hg⟩
      · exact ⟨⊤, Scheme.etaleTopology.top_mem T, fun V g _ he' => absurd he' he⟩)
    refine Scheme.etaleTopology.superset_covering ?_ hS
    intro V g hg
    show (cokernel ((freeP R).map i')).map g.op _ = (cokernel ((freeP R).map i')).map g.op 0
    rw [map_zero, ← NatTrans.naturality_apply]
    have hcore := core v (fun x : ULift.{1} (B'.obj (op T)) => (ULift.up.{1} (b.app (op T) x.down) : ULift.{1} (B.obj (op T))))
      (fun x : ULift.{1} (B'.obj (op T)) => ULift.up (B'.map g.op x.down))
      (fun t : ULift.{1} (B.obj (op T)) => ∃ x, i.app (op T) x = t.down) (fun z => ∃ x', i'.app (op V) x' = z.down)
      (by
        intro t ht
        have := Finsupp.mapDomain_notin_range n t (by
          rintro ⟨x, hx⟩
          exact ht ⟨x.down, congrArg ULift.down hx⟩)
        exact (DFunLike.congr_fun hn' t).symm.trans this)
      (by
        rintro a₀ ⟨x, hx⟩
        obtain ⟨x', hx'⟩ := h1 T a₀.down x hx
        exact ⟨A'.map g.op x', by rw [FunctorToTypes.naturality, hx']⟩)
      (by
        rintro a₁ a₂ he ⟨x', hx'⟩
        have he' : b.app (op T) a₁.down = b.app (op T) a₂.down := congrArg ULift.down he
        refine h1 V (B'.map g.op a₂.down) (a.app (op V) x') ?_
        have := ConcreteCategory.congr_hom (NatTrans.congr_app w (op V)) x'
        simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at this
        rw [← this, hx', FunctorToTypes.naturality, FunctorToTypes.naturality, he'])
      (by
        intro a₁ ha₁ a₂ ha₂ he
        rcases HS (a₁, a₂) (Finset.mem_product.2 ⟨ha₁, ha₂⟩) g hg (congrArg ULift.down he) with e | ⟨x, hx⟩
        · left; exact congrArg ULift.up e
        · right; exact h1 V _ x hx)
    obtain ⟨n', hn''⟩ := mem_range_mapDomain (fun x : ULift.{1} (A'.obj (op V)) => ULift.up (i'.app (op V) x.down)) _
      (fun z hz => hcore z (fun ⟨x', hx'⟩ => hz ⟨ULift.up x', congrArg ULift.up hx' |>.trans rfl⟩))
    have e2 : ((freeP R).obj B').map g.op v = ((freeP R).map i').app (op V) n' := hn''.symm
    rw [e2]
    exact π_freeP_apply R i' (op V) n'
  constructor
  intro X x y hxy
  cases X with | op T =>
  refine Scheme.etaleTopology.superset_covering ?_ (key T (x - y) (by rw [map_sub, hxy, sub_self]))
  intro V g hg
  have hg' : (cokernel ((freeP R).map i')).map g.op (x - y) = (cokernel ((freeP R).map i')).map g.op 0 := hg
  rw [map_sub, map_zero, sub_eq_zero] at hg'
  exact hg'

theorem LeafFreeCokInj_of : LeafFreeCokInj := leafFreeCokInj

end LateralTheory.CohomologicalPurity
end
