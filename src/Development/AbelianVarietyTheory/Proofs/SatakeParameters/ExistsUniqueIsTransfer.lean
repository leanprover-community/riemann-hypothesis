import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FreeHomExtOfCovering
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplittingSieveMemEtaleTopology
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoveringOfForallMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains

section
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeSch_hom_ext_of_etale_covering : ∀ (R : Type) [CommRing R] {S : Scheme.{0}} (F : GlobalTheory.EtC.Shv R) (φ ψ : GlobalTheory.EtC.Tr.freeSch R S ⟶ F) (T : Sieve S), T ∈ Scheme.etaleTopology S → (∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S), T v → (GlobalTheory.EtC.free R).map (yoneda.map v) ≫ φ = (GlobalTheory.EtC.free R).map (yoneda.map v) ≫ ψ) → φ = ψ := by
  first | (exact @GlobalTheory.EtC.Tr.free_hom_ext_of_covering) | (exact GlobalTheory.EtC.Tr.free_hom_ext_of_covering) | (intros; apply GlobalTheory.EtC.Tr.free_hom_ext_of_covering  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem splitBy_baseChange : ∀ {Z X V T : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m : ℕ} {s : Fin m → (V ⟶ Z)},
    GlobalTheory.EtC.Tr.SplitBy f y s → ∀ (w : T ⟶ V), GlobalTheory.EtC.Tr.SplitBy f (w ≫ y) (fun j => w ≫ s j) := by
  intro Z X V T f y m s ⟨hs, hiso⟩ w
  have hs' : ∀ j, (w ≫ s j) ≫ f = w ≫ y := fun j => by rw [Category.assoc, hs j]
  refine ⟨hs', ?_⟩

  let c : Cofan (fun _ : Fin m => V) :=
    Cofan.mk (pullback f y) (fun j => pullback.lift (s j) (𝟙 V) (by rw [hs j, Category.id_comp]))
  have hc : IsColimit c := by
    haveI : IsIso ((coproductIsCoproduct (fun _ : Fin m => V)).desc c) := hiso
    exact IsColimit.ofPointIso (coproductIsCoproduct (fun _ : Fin m => V))
  let c' : Cofan (fun _ : Fin m => T) :=
    Cofan.mk (pullback f (w ≫ y)) (fun j => pullback.lift (w ≫ s j) (𝟙 T) (by rw [hs' j, Category.id_comp]))
  let g : pullback f (w ≫ y) ⟶ pullback f y :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ w) (by rw [pullback.condition, Category.assoc])
  have hg1 : g ≫ pullback.fst f y = pullback.fst f (w ≫ y) := pullback.lift_fst _ _ _
  have hg2 : g ≫ pullback.snd f y = pullback.snd f (w ≫ y) ≫ w := pullback.lift_snd _ _ _

  have hA : IsPullback (pullback.snd f (w ≫ y)) g w (pullback.snd f y) := by
    refine IsPullback.of_bot (v₂₁ := pullback.fst f y) (v₂₂ := y) (h₃₁ := f) ?_ hg2.symm
      (IsPullback.of_hasPullback f y).flip
    rw [hg1]
    exact (IsPullback.of_hasPullback f (w ≫ y)).flip
  let α : Discrete.functor (fun _ : Fin m => T) ⟶ Discrete.functor (fun _ : Fin m => V) :=
    Discrete.natTrans (fun _ => w)
  have hsq : ∀ j, w ≫ c.ι.app ⟨j⟩ = c'.ι.app ⟨j⟩ ≫ g := by
    intro j
    show w ≫ pullback.lift (s j) (𝟙 V) _ = pullback.lift (w ≫ s j) (𝟙 T) _ ≫ g
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, hg1, pullback.lift_fst]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, hg2, ← Category.assoc, pullback.lift_snd,
        Category.comp_id, Category.id_comp]
  have hcc : α ≫ c.ι = c'.ι ≫ (Functor.const _).map g := by
    ext ⟨j⟩
    exact hsq j
  have hpb : ∀ j, IsPullback (c'.ι.app j) (α.app j) g (c.ι.app j) := by
    rintro ⟨j⟩
    refine IsPullback.of_right (h₁₂ := pullback.snd f (w ≫ y)) (v₁₃ := w) (h₂₂ := pullback.snd f y) ?_ (hsq j).symm hA
    have e1 : c'.ι.app ⟨j⟩ ≫ pullback.snd f (w ≫ y) = 𝟙 T := pullback.lift_snd _ _ _
    have e2 : c.ι.app ⟨j⟩ ≫ pullback.snd f y = 𝟙 V := pullback.lift_snd _ _ _
    rw [e1, e2]
    show IsPullback (𝟙 T) w w (𝟙 V)
    exact IsPullback.id_horiz w
  obtain ⟨hc'⟩ := FinitaryPreExtensive.isUniversal_finiteCoproducts hc c' α g hcc
    (NatTrans.Equifibered.of_discrete _) hpb
  have : Sigma.desc (fun j => pullback.lift (w ≫ s j) (𝟙 T) (by rw [hs' j, Category.id_comp])) =
      ((coproductIsCoproduct (fun _ : Fin m => T)).coconePointUniqueUpToIso hc').hom := by
    apply Sigma.hom_ext; intro j
    rw [Sigma.ι_desc]
    exact ((coproductIsCoproduct (fun _ : Fin m => T)).comp_coconePointUniqueUpToIso_hom hc' ⟨j⟩).symm
  rw [this]
  infer_instance

end GlobalTheory.EtC.Tr
end

section
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitBy_baseChange' : ∀ {Z X V T : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m : ℕ} {s : Fin m → (V ⟶ Z)}, GlobalTheory.EtC.Tr.SplitBy f y s → ∀ (w : T ⟶ V), GlobalTheory.EtC.Tr.SplitBy f (w ≫ y) (fun j => w ≫ s j) := by
  first | (exact @GlobalTheory.EtC.Tr.splitBy_baseChange) | (exact GlobalTheory.EtC.Tr.splitBy_baseChange) | (intros; apply GlobalTheory.EtC.Tr.splitBy_baseChange  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite

noncomputable section

namespace GlobalTheory.EtC.Tr

open GlobalTheory.EtC.CupSpec

theorem free_hom_glue_of_covering (R : Type) [CommRing R] {S : Scheme.{0}} (F : GlobalTheory.EtC.Shv R) (T : Sieve S)
    (hT : T ∈ Scheme.etaleTopology S)
    (σ : ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S), T v → (GlobalTheory.EtC.Tr.freeSch R V ⟶ F))
    (hσ : ∀ ⦃V W : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v) (g : W ⟶ V),
      (GlobalTheory.EtC.free R).map (yoneda.map g) ≫ σ v hv = σ (g ≫ v) (T.downward_closed hv g)) :
    ∃ t : GlobalTheory.EtC.Tr.freeSch R S ⟶ F, ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v),
      (GlobalTheory.EtC.free R).map (yoneda.map v) ≫ t = σ v hv := by

  let x : Presieve.FamilyOfElements (F.obj ⋙ forget _) T.arrows := fun V v hv =>
    Sec.map (σ v hv) (freeGen R (yoneda.obj V) V (𝟙 V))

  have hres : ∀ ⦃V W : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v) (g : W ⟶ V),
      Sec.res g (Sec.map (σ v hv) (freeGen R (yoneda.obj V) V (𝟙 V))) =
        Sec.map (σ v hv) (freeGen R (yoneda.obj V) W g) := by
    intro V W v hv g
    rw [map_res, freeGen_res]
    congr 2
  have hcomp : ∀ ⦃V W : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v) (g : W ⟶ V),
      Sec.map (σ (g ≫ v) (T.downward_closed hv g)) (freeGen R (yoneda.obj W) W (𝟙 W)) =
        Sec.map (σ v hv) (freeGen R (yoneda.obj V) W g) := by
    intro V W v hv g
    rw [← hσ v hv g]
    change Sec.map (σ v hv) (Sec.map ((GlobalTheory.EtC.free R).map (yoneda.map g)) (freeGen R (yoneda.obj W) W (𝟙 W))) = _
    rw [freeGen_map]
    congr 2
  have hx : x.SieveCompatible := by
    intro V W v g hv
    exact (hcomp v hv g).trans (hres v hv g).symm
  have hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 F.cond)
  obtain ⟨s, hs, -⟩ := hF T hT x ((Presieve.compatible_iff_sieveCompatible x).2 hx)
  obtain ⟨t, ht⟩ := free_exists (R := R) (yoneda.obj S) F (fun U g => Sec.res g (show Sec F S from s))
    (fun V U g h => by
      change Sec.res g (Sec.res h _) = Sec.res (g ≫ h) _
      simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply])
  refine ⟨t, fun V v hv => ?_⟩
  apply free_ext
  intro U w
  change Sec.map t (Sec.map ((GlobalTheory.EtC.free R).map (yoneda.map v)) (freeGen R (yoneda.obj V) U w)) = _
  rw [freeGen_map, ht, ← hres v hv w]
  have hsv : Sec.res v (show Sec F S from s) = Sec.map (σ v hv) (freeGen R (yoneda.obj V) V (𝟙 V)) := hs v hv
  rw [← hsv]
  change Sec.res (w ≫ v) _ = Sec.res w (Sec.res v _)
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

end GlobalTheory.EtC.Tr

example : ∀ (R : Type) [CommRing R] {S : Scheme.{0}} (F : GlobalTheory.EtC.Shv R) (T : Sieve S), T ∈ Scheme.etaleTopology S → ∀ (σ : ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S), T v → (GlobalTheory.EtC.Tr.freeSch R V ⟶ F)), (∀ ⦃V W : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v) (g : W ⟶ V), (GlobalTheory.EtC.free R).map (yoneda.map g) ≫ σ v hv = σ (g ≫ v) (T.downward_closed hv g)) → ∃ t : GlobalTheory.EtC.Tr.freeSch R S ⟶ F, ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v), (GlobalTheory.EtC.free R).map (yoneda.map v) ≫ t = σ v hv :=
  @GlobalTheory.EtC.Tr.free_hom_glue_of_covering
end
end

section
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_freeSch_hom_glue_of_etale_covering : ∀ (R : Type) [CommRing R] {S : Scheme.{0}} (F : GlobalTheory.EtC.Shv R) (T : Sieve S), T ∈ Scheme.etaleTopology S → ∀ (σ : ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S), T v → (GlobalTheory.EtC.Tr.freeSch R V ⟶ F)), (∀ ⦃V W : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v) (g : W ⟶ V), (GlobalTheory.EtC.free R).map (yoneda.map g) ≫ σ v hv = σ (g ≫ v) (T.downward_closed hv g)) → ∃ t : GlobalTheory.EtC.Tr.freeSch R S ⟶ F, ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ S) (hv : T v), (GlobalTheory.EtC.free R).map (yoneda.map v) ≫ t = σ v hv := by
  first | (exact @GlobalTheory.EtC.Tr.free_hom_glue_of_covering) | (exact GlobalTheory.EtC.Tr.free_hom_glue_of_covering) | (intros; apply GlobalTheory.EtC.Tr.free_hom_glue_of_covering  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr.SumEq

end GlobalTheory.EtC.Tr.SumEq

namespace GlobalTheory.EtC.Tr

open CategoryTheory Limits AlgebraicGeometry in
private lemma exists_sigma_ι_apply_eq_of_finite_coprod {σ : Type} [Finite σ] (g : σ → Scheme.{0}) (q : ↥(∐ g)) :
    ∃ k a, (Sigma.ι g k) a = q :=
  (sigmaOpenCover g).exists_eq q

open CategoryTheory Limits AlgebraicGeometry in
private lemma exists_pullback_lift_apply_eq_of_isIso_sigmaDesc {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m : ℕ}
    {s : Fin m → (V ⟶ Z)} (hc : ∀ j, s j ≫ f = y)
    [IsIso (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y)]
    (p : ↥(pullback f y)) : ∃ k a, pullback.lift (s k) (𝟙 V) (by simp [hc k]) a = p := by
  obtain ⟨q, rfl⟩ := Scheme.Hom.surjective
    (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y) p
  obtain ⟨k, a, rfl⟩ := exists_sigma_ι_apply_eq_of_finite_coprod _ q
  exact ⟨k, a, by rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]⟩

open CategoryTheory Limits AlgebraicGeometry in
private lemma isOpenImmersion_pullback_lift_of_isIso_sigmaDesc {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m : ℕ}
    {s : Fin m → (V ⟶ Z)} (hc : ∀ j, s j ≫ f = y)
    [IsIso (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y)] (k : Fin m) :
    IsOpenImmersion (pullback.lift (s k) (𝟙 V) (by simp [hc k]) : V ⟶ pullback f y) := by
  rw [← Sigma.ι_desc (fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
    (j : Fin m) → V ⟶ pullback f y) k]
  infer_instance

open CategoryTheory Limits AlgebraicGeometry in
private lemma pullback_snd_lift_id_apply {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} (t : V ⟶ Z)
    (h : t ≫ f = 𝟙 V ≫ y) (a : ↥V) : pullback.snd f y (pullback.lift t (𝟙 V) h a) = a := by
  rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
  rfl

open CategoryTheory Limits AlgebraicGeometry in
private lemma index_eq_of_pullback_lift_apply_eq {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m : ℕ}
    {s : Fin m → (V ⟶ Z)} (hc : ∀ j, s j ≫ f = y)
    [IsIso (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y)]
    {j j' : Fin m} (a b : ↥V)
    (h : (pullback.lift (s j) (𝟙 V) (by simp [hc j]) : V ⟶ pullback f y) a =
      (pullback.lift (s j') (𝟙 V) (by simp [hc j']) : V ⟶ pullback f y) b) :
    j = j' := by
  have h1 : (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y) (Sigma.ι (fun _ : Fin m => V) j a) =
      (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y) (Sigma.ι (fun _ : Fin m => V) j' b) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Sigma.ι_desc, Sigma.ι_desc]
    exact h
  have h2 : (Sigma.ι (fun _ : Fin m => V) j) a = (Sigma.ι (fun _ : Fin m => V) j') b :=
    Scheme.Hom.injective _ h1
  exact congrArg Sigma.fst ((sigmaι_eq_iff (fun _ : Fin m => V) j j' a b).mp (by convert h2))

open CategoryTheory Limits AlgebraicGeometry in
private lemma injective_of_pullback_lift_apply_eq_of_isIso {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m m' : ℕ}
    {s : Fin m → (V ⟶ Z)} {s' : Fin m' → (V ⟶ Z)} (hc : ∀ j, s j ≫ f = y) (hc' : ∀ j, s' j ≫ f = y)
    [IsIso (Sigma.desc fun j => pullback.lift (s j) (𝟙 V) (by simp [hc j]) :
      (∐ fun _ : Fin m => V) ⟶ pullback f y)]
    (x : ↥V) (K : Fin m → Fin m') (A : Fin m → ↥V)
    (hKA : ∀ j, (pullback.lift (s' (K j)) (𝟙 V) (by simp [hc' (K j)]) : V ⟶ pullback f y) (A j) =
      (pullback.lift (s j) (𝟙 V) (by simp [hc j]) : V ⟶ pullback f y) x) : Function.Injective K := by
  intro j j' hjj
  have hA : ∀ i, A i = x := fun i => by
    have := congrArg (pullback.snd f y) (hKA i)
    rwa [pullback_snd_lift_id_apply, pullback_snd_lift_id_apply] at this
  refine index_eq_of_pullback_lift_apply_eq hc x x ?_
  rw [← hKA j, ← hKA j', hA, hA]
  have key : ∀ k k' : Fin m', k = k' →
      (pullback.lift (s' k) (𝟙 V) (by simp [hc' k]) : V ⟶ pullback f y) x =
      (pullback.lift (s' k') (𝟙 V) (by simp [hc' k']) : V ⟶ pullback f y) x := by
    rintro k _ rfl
    rfl
  exact key _ _ hjj

open CategoryTheory Limits AlgebraicGeometry in

theorem _root_.GlobalTheory.EtC.Tr.sum_sections_eq_of_two_splittings : ∀ (R : Type) [CommRing R] {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X}
    {m m' : ℕ} {s : Fin m → (V ⟶ Z)} {s' : Fin m' → (V ⟶ Z)}, _root_.GlobalTheory.EtC.Tr.SplitBy f y s → _root_.GlobalTheory.EtC.Tr.SplitBy f y s' →
    ∑ j, (_root_.GlobalTheory.EtC.free R).map (yoneda.map (s j)) = ∑ j, (_root_.GlobalTheory.EtC.free R).map (yoneda.map (s' j)) := by
  intro R _ Z X V f y m m' s s' hs hs'
  obtain ⟨hc, hi⟩ := hs
  obtain ⟨hc', hi'⟩ := hs'
  let T : Sieve V :=
    { arrows := fun W v => (_root_.GlobalTheory.EtC.free R).map (yoneda.map v) ≫
          ∑ j, (_root_.GlobalTheory.EtC.free R).map (yoneda.map (s j)) =
        (_root_.GlobalTheory.EtC.free R).map (yoneda.map v) ≫
          ∑ j, (_root_.GlobalTheory.EtC.free R).map (yoneda.map (s' j))
      downward_closed := by
        intro W W' v hv g
        rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hv] }
  refine _root_.GlobalTheory.EtC.Tr.free_hom_ext_of_covering R (_root_.GlobalTheory.EtC.Tr.freeSch R Z) _ _ T ?_ (fun W v hv => hv)
  apply Scheme.zariskiTopology_le_etaleTopology
  choose K A hKA using fun (x : ↥V) (j : Fin m) =>
    exists_pullback_lift_apply_eq_of_isIso_sigmaDesc hc' ((pullback.lift (s j) (𝟙 V) (by simp [hc j]) : V ⟶ pullback f y) x)
  choose K' A' hKA' using fun (x : ↥V) (k : Fin m') =>
    exists_pullback_lift_apply_eq_of_isIso_sigmaDesc hc ((pullback.lift (s' k) (𝟙 V) (by simp [hc' k]) : V ⟶ pullback f y) x)
  have hopen := isOpenImmersion_pullback_lift_of_isIso_sigmaDesc hc'
  let U : ↥V → V.Opens := fun x =>
    ⟨⋂ j, (pullback.lift (s j) (𝟙 V) (by simp [hc j]) : V ⟶ pullback f y) ⁻¹'
        Set.range (pullback.lift (s' (K x j)) (𝟙 V) (by simp [hc' (K x j)]) : V ⟶ pullback f y),
      isOpen_iInter_of_finite fun j =>
        (Scheme.Hom.isOpenEmbedding _).isOpen_range.preimage (Scheme.Hom.continuous _)⟩
  have hxU : ∀ x, x ∈ U x := fun x => Set.mem_iInter.mpr fun j => ⟨A x j, hKA x j⟩
  have hagree : ∀ x, T ((U x).ι) := by
    intro x
    have hinj := injective_of_pullback_lift_apply_eq_of_isIso hc hc' x (K x) (A x) (hKA x)
    have hinj' := injective_of_pullback_lift_apply_eq_of_isIso hc' hc x (K' x) (A' x) (hKA' x)
    have hbij : Function.Bijective (K x) := (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨hinj, le_antisymm (Fintype.card_le_of_injective _ hinj) (Fintype.card_le_of_injective _ hinj')⟩
    have hsec : ∀ j, (U x).ι ≫ s j = (U x).ι ≫ s' (K x j) := by
      intro j
      have hr : Set.range ⇑((U x).ι ≫ (pullback.lift (s j) (𝟙 V) (by simp [hc j]) : V ⟶ pullback f y)) ⊆
          Set.range (pullback.lift (s' (K x j)) (𝟙 V) (by simp [hc' (K x j)]) : V ⟶ pullback f y) := by
        rintro _ ⟨w, rfl⟩
        have hw : (U x).ι w ∈ U x := by
          have hw' : (U x).ι w ∈ Set.range (U x).ι := ⟨w, rfl⟩
          rwa [Scheme.Opens.range_ι] at hw'
        rw [Scheme.Hom.comp_apply]
        exact Set.mem_iInter.mp hw j
      have hg := IsOpenImmersion.lift_fac _ _ hr
      have hgι : IsOpenImmersion.lift _ _ hr = (U x).ι := by
        have := congrArg (· ≫ pullback.snd f y) hg
        simp only [Category.assoc, pullback.lift_snd, Category.comp_id] at this
        exact this
      rw [hgι] at hg
      have := congrArg (· ≫ pullback.fst f y) hg
      simp only [Category.assoc, pullback.lift_fst] at this
      exact this.symm
    show (_root_.GlobalTheory.EtC.free R).map (yoneda.map (U x).ι) ≫ _ =
      (_root_.GlobalTheory.EtC.free R).map (yoneda.map (U x).ι) ≫ _
    rw [Preadditive.comp_sum, Preadditive.comp_sum]
    refine Fintype.sum_equiv (Equiv.ofBijective _ hbij) _ _ fun j => ?_
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
      Equiv.ofBijective_apply, hsec j]
  rw [show Scheme.zariskiTopology = Scheme.grothendieckTopology @IsOpenImmersion from rfl,
    Scheme.mem_grothendieckTopology_iff]
  refine ⟨Scheme.Cover.mkOfCovers V (fun x => (U x : Scheme.{0})) (fun x => (U x).ι)
    (fun x => ⟨x, ⟨x, hxU x⟩, rfl⟩), ?_⟩
  rintro W _ ⟨x⟩
  exact hagree x

end GlobalTheory.EtC.Tr
end

section
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeSheaf_sum_sections_eq_of_two_splittings : ∀ (R : Type) [CommRing R] {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m m' : ℕ} {s : Fin m → (V ⟶ Z)} {s' : Fin m' → (V ⟶ Z)}, GlobalTheory.EtC.Tr.SplitBy f y s → GlobalTheory.EtC.Tr.SplitBy f y s' → ∑ j, (GlobalTheory.EtC.free R).map (yoneda.map (s j)) = ∑ j, (GlobalTheory.EtC.free R).map (yoneda.map (s' j)) := by
  first | (exact @GlobalTheory.EtC.Tr.sum_sections_eq_of_two_splittings) | (exact GlobalTheory.EtC.Tr.sum_sections_eq_of_two_splittings) | (intros; apply GlobalTheory.EtC.Tr.sum_sections_eq_of_two_splittings  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace GlobalTheory.EtC.Tr

variable (R : Type) [CommRing R]

theorem splits_of_splitSieve {Z X S V : Scheme.{0}} {f : Z ⟶ X} {x : S ⟶ X} {v : V ⟶ S} (hv : splitSieve f x v) :
    Splits f (v ≫ x) := by
  obtain ⟨W, w, u, ⟨m, s, hs⟩, rfl⟩ := hv
  refine ⟨m, fun j => w ≫ s j, ?_⟩
  have := GlobalTheory.T.splitBy_baseChange' hs w
  rwa [Category.assoc]

def splitSum {Z X V : Scheme.{0}} (f : Z ⟶ X) (y : V ⟶ X) (h : Splits f y) : freeSch R V ⟶ freeSch R Z :=
  ∑ j, (free R).map (yoneda.map (h.choose_spec.choose j))

theorem splitSum_eq {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} (h : Splits f y) {m : ℕ} {s : Fin m → (V ⟶ Z)}
    (hs : SplitBy f y s) : splitSum R f y h = ∑ j, (free R).map (yoneda.map (s j)) :=
  GlobalTheory.T.freeSheaf_sum_sections_eq_of_two_splittings R h.choose_spec.choose_spec hs

theorem existsUnique_isTransfer {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] :
    ∃! t, IsTransfer R f t := by
  have hT := GlobalTheory.T.splittingSieve_mem_etaleTopology f (𝟙 X)

  let σ : ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ X), splitSieve f (𝟙 X) v → (freeSch R V ⟶ freeSch R Z) :=
    fun V v hv => splitSum R f (v ≫ 𝟙 X) (splits_of_splitSieve hv)
  have hσ : ∀ ⦃V W : Scheme.{0}⦄ (v : V ⟶ X) (hv : splitSieve f (𝟙 X) v) (g : W ⟶ V),
      (free R).map (yoneda.map g) ≫ σ v hv = σ (g ≫ v) ((splitSieve f (𝟙 X)).downward_closed hv g) := by
    intro V W v hv g
    obtain ⟨m, s, hs⟩ := splits_of_splitSieve hv
    have hg := GlobalTheory.T.splitBy_baseChange' hs g
    rw [← Category.assoc] at hg
    simp only [σ, splitSum_eq R _ hs, splitSum_eq R _ hg, Preadditive.comp_sum, ← Functor.map_comp]
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_freeSch_hom_glue_of_etale_covering R (freeSch R Z) _ hT σ hσ
  have key : ∀ t', IsTransfer R f t' → ∀ ⦃V : Scheme.{0}⦄ (v : V ⟶ X) (hv : splitSieve f (𝟙 X) v),
      (free R).map (yoneda.map v) ≫ t' = σ v hv := by
    intro t' ht' V v hv
    obtain ⟨m, s, hs⟩ := splits_of_splitSieve hv
    simp only [σ, splitSum_eq R _ hs]
    have := ht'.apply_of_splitBy R hs
    rwa [Category.comp_id] at this
  refine ⟨t, ?_, fun t' ht' => ?_⟩
  · intro S x m s hs hiso
    refine GlobalTheory.T.freeSch_hom_ext_of_etale_covering R (freeSch R Z) _ _ _ (GlobalTheory.T.splittingSieve_mem_etaleTopology f x) (fun V v hv => ?_)
    obtain ⟨m', s', hs'⟩ := splits_of_splitSieve hv
    have hvx : splitSieve f (𝟙 X) (v ≫ x) := ⟨V, 𝟙 V, v ≫ x, (show Splits f ((v ≫ x) ≫ 𝟙 X) by rw [Category.comp_id]; exact ⟨m', s', hs'⟩), Category.id_comp _⟩
    have h1 := GlobalTheory.T.splitBy_baseChange' ⟨hs, hiso⟩ v
    rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, ht _ hvx, Preadditive.comp_sum]
    simp only [σ, ← Functor.map_comp]
    rw [splitSum_eq R _ (show SplitBy f ((v ≫ x) ≫ 𝟙 X) (fun j => v ≫ s j) by rw [Category.comp_id]; exact h1)]
  · exact GlobalTheory.T.freeSch_hom_ext_of_etale_covering R (freeSch R Z) _ _ _ hT fun V v hv => by rw [key t' ht' v hv, ht v hv]

end GlobalTheory.EtC.Tr

end
end
