import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LeafKillCut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMayerVietorisConnectingExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCechNerveAugmentationIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.CupSpec

namespace UpperTheory.CoverSieveFree

private def coverSieve {Y A B T : Scheme.{0}} (a : A ⟶ Y) (b : B ⟶ Y) (x : T ⟶ Y) : Sieve T where
  arrows V g := (∃ u : V ⟶ A, u ≫ a = g ≫ x) ∨ ∃ v : V ⟶ B, v ≫ b = g ≫ x
  downward_closed := by
    rintro V W g (⟨u, hu⟩ | ⟨v, hv⟩) h
    · exact Or.inl ⟨h ≫ u, by simp [hu]⟩
    · exact Or.inr ⟨h ≫ v, by simp [hv]⟩

private theorem coverSieve_mem {Y A B T : Scheme.{0}} (a : A ⟶ Y) (b : B ⟶ Y) [IsOpenImmersion a]
    [IsOpenImmersion b] (hc : ∀ y : Y, y ∈ Set.range a ∨ y ∈ Set.range b) (x : T ⟶ Y) :
    coverSieve a b x ∈ Scheme.etaleTopology.{0} T := by
  let Xs : Bool → Scheme.{0} := fun i => Bool.casesOn i B A
  let fs : ∀ i, Xs i ⟶ Y := fun i => Bool.casesOn (motive := fun i => Xs i ⟶ Y) i b a
  have hmem : Presieve.ofArrows Xs fs ∈ Scheme.precoverage @Etale Y := by
    refine (Scheme.ofArrows_mem_precoverage_iff @Etale).2 ⟨fun y => ?_, fun i => ?_⟩
    · rcases hc y with h | h
      · exact ⟨true, h⟩
      · exact ⟨false, h⟩
    · cases i <;> dsimp [fs] <;> infer_instance
  have hS := Precoverage.generate_mem_toGrothendieck hmem
  refine Scheme.etaleTopology.superset_covering ?_ (Scheme.etaleTopology.pullback_stable x hS)
  rintro V g ⟨W, h, k, hk, e⟩
  rcases hk with ⟨i⟩
  cases i
  · exact Or.inr ⟨h, e⟩
  · exact Or.inl ⟨h, e⟩

private theorem free_hom_ext (R : Type) [CommRing R] {Y A B : Scheme.{0}} (a : A ⟶ Y) (b : B ⟶ Y)
    [IsOpenImmersion a] [IsOpenImmersion b] (hc : ∀ y : Y, y ∈ Set.range a ∨ y ∈ Set.range b)
    {G : Shv R} (φ ψ : (free R).obj (yoneda.obj Y) ⟶ G)
    (ha : (free R).map (yoneda.map a) ≫ φ = (free R).map (yoneda.map a) ≫ ψ)
    (hb : (free R).map (yoneda.map b) ≫ φ = (free R).map (yoneda.map b) ≫ ψ) : φ = ψ := by
  apply free_ext
  intro U x
  refine G.isSeparated _ (coverSieve a b x) (coverSieve_mem a b hc x) _ _ ?_
  intro V g hg
  change Sec.res g (Sec.map φ _) = Sec.res g (Sec.map ψ _)
  rw [map_res, map_res, freeGen_res]
  rcases hg with ⟨u, hu⟩ | ⟨v, hv⟩
  · have e : (ConcreteCategory.hom ((yoneda.obj Y).map g.op)) x =
        (ConcreteCategory.hom ((yoneda.map a).app (op V))) u := hu.symm
    rw [e, ← freeGen_map]
    change Sec.map ((free R).map (yoneda.map a) ≫ φ) _ = Sec.map ((free R).map (yoneda.map a) ≫ ψ) _
    rw [ha]
  · have e : (ConcreteCategory.hom ((yoneda.obj Y).map g.op)) x =
        (ConcreteCategory.hom ((yoneda.map b).app (op V))) v := hv.symm
    rw [e, ← freeGen_map]
    change Sec.map ((free R).map (yoneda.map b) ≫ φ) _ = Sec.map ((free R).map (yoneda.map b) ≫ ψ) _
    rw [hb]

end UpperTheory.CoverSieveFree

open UpperTheory.CoverSieveFree in
theorem UpperTheory.isCovering_pair_of_isOpenImmersion_of_jointly_surjective :
    ∀ (R : Type) [CommRing R] {Y A B : Scheme.{0}} (a : A ⟶ Y) (b : B ⟶ Y), IsOpenImmersion a → IsOpenImmersion b →
       (∀ y : Y, y ∈ Set.range a ∨ y ∈ Set.range b) → Cover2 R (sch.map a) (sch.map b) := by
  intro R _ Y A B a b ha hb hc
  have hy : ∀ {Z : Scheme.{0}} (f : Z ⟶ Y) [Mono f], Mono (sch.map f) := by
    intro Z f _
    have h1 : ∀ X, Mono ((yoneda.map f).app X) := fun X =>
      (mono_iff_injective _).2 (fun g h e => (cancel_mono f).1 (by simpa using e))
    have h2 : Mono (yoneda.map f) := NatTrans.mono_of_mono_app _
    have h3 : ∀ n, Mono ((sch.map f).app n) := fun n => h2
    exact NatTrans.mono_of_mono_app _
  refine ⟨hy a, hy b, fun n => ⟨fun {G} φ ψ h => ?_⟩⟩
  apply free_hom_ext R a b hc φ ψ
  · have e := congrArg (fun k => biprod.inl ≫ k) h
    simp only [biprod.inl_desc_assoc] at e
    exact e
  · have e := congrArg (fun k => biprod.inr ≫ k) h
    simp only [biprod.inr_desc_assoc] at e
    exact e
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace UpperTheory.SchemePresentationCover

private theorem sch_pres : PreservesLimitsOfShape WalkingCospan sch := by
  unfold sch; infer_instance

private theorem pb {Y : Scheme.{0}} {A B C D : Y.Opens} (hC : C = A ⊓ B) (hCA : C ≤ A) (hCB : C ≤ B)
    (hA : A ≤ D) (hB : B ≤ D) :
    IsPullback (Y.homOfLE hCA) (Y.homOfLE hCB) (Y.homOfLE hA) (Y.homOfLE hB) := by
  subst hC
  exact isPullback_opens_inf_le hA hB

private theorem cov (R : Type) [CommRing R] {Y : Scheme.{0}} {A B D : Y.Opens} (hD : D = A ⊔ B)
    (hA : A ≤ D) (hB : B ≤ D) :
    Cover2 R (sch.map (Y.homOfLE hA)) (sch.map (Y.homOfLE hB)) := by
  subst hD
  apply UpperTheory.isCovering_pair_of_isOpenImmersion_of_jointly_surjective
  · infer_instance
  · infer_instance
  · intro y
    have hy : (y.1 : Y) ∈ A ⊔ B := y.2
    rcases (by simpa using hy : (y.1 : Y) ∈ A ∨ (y.1 : Y) ∈ B) with h | h
    · exact Or.inl ⟨⟨y.1, h⟩, by rw [Scheme.homOfLE_apply']; rfl⟩
    · exact Or.inr ⟨⟨y.1, h⟩, by rw [Scheme.homOfLE_apply']; rfl⟩

end UpperTheory.SchemePresentationCover

private theorem sq_lemma' {T S : Scheme.{0}} (f : T ⟶ S) {P Q : S.Opens} (h : P ≤ Q) (h' : f ⁻¹ᵁ P ≤ f ⁻¹ᵁ Q) :
    T.homOfLE h' ≫ f ∣_ Q = f ∣_ P ≫ S.homOfLE h := by
  rw [← cancel_mono Q.ι]
  simp [morphismRestrict_ι]

open UpperTheory.SchemePresentationCover in
theorem UpperTheory.exists_mayerVietoris_preimage_of_restrictions_vanish :
    ∀ (R : Type) [CommRing R] (F : Shv R) {S : Scheme.{0}} (U V : S.Opens) (n : ℤ)
        (x : H R (sch.obj (U ⊔ V).toScheme) F (n + 1)),
        pull R (sch.map (S.homOfLE (le_sup_left : U ≤ U ⊔ V))) F (n + 1) x = 0 →
        pull R (sch.map (S.homOfLE (le_sup_right : V ≤ U ⊔ V))) F (n + 1) x = 0 →
        ∃ y : H R (sch.obj (U ⊓ V).toScheme) F n,
          ∀ {T : Scheme.{0}} (f : T ⟶ S) (a : H R (sch.obj (f ⁻¹ᵁ U).toScheme) F n)
            (b : H R (sch.obj (f ⁻¹ᵁ V).toScheme) F n),
            pull R (sch.map (f ∣_ (U ⊓ V))) F n y =
              pull R (sch.map (T.homOfLE (f.preimage_mono inf_le_left))) F n a -
                pull R (sch.map (T.homOfLE (f.preimage_mono inf_le_right))) F n b →
            pull R (sch.map (f ∣_ (U ⊔ V))) F (n + 1) x = 0 := by
  intro R _ F S U V n x hx1 hx2
  obtain ⟨d, hd, hnat⟩ := mayerVietoris R F
  haveI := sch_pres
  have hc := cov R (rfl : U ⊔ V = U ⊔ V) le_sup_left le_sup_right
  obtain ⟨c, hc'⟩ := ((hd _ _ hc n).2.2 x).1 ⟨hx1, hx2⟩
  have P := (pb (rfl : U ⊓ V = U ⊓ V) inf_le_left inf_le_right
    (le_sup_left : U ≤ U ⊔ V) (le_sup_right : V ≤ U ⊔ V)).map sch
  refine ⟨pull R P.isoPullback.hom F n c, ?_⟩
  intro T f a b hab
  have hD : f ⁻¹ᵁ (U ⊔ V) = f ⁻¹ᵁ U ⊔ f ⁻¹ᵁ V := by
    ext; simp
  have hC : f ⁻¹ᵁ (U ⊓ V) = f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V := by
    ext; simp
  have hcT := cov R hD (f.preimage_mono le_sup_left) (f.preimage_mono le_sup_right)
  have PT := (pb hC (f.preimage_mono inf_le_left) (f.preimage_mono inf_le_right)
    (f.preimage_mono le_sup_left) (f.preimage_mono le_sup_right)).map sch
  have hu : sch.map (T.homOfLE (f.preimage_mono (le_sup_left : U ≤ U ⊔ V))) ≫ sch.map (f ∣_ (U ⊔ V)) =
      sch.map (f ∣_ U) ≫ sch.map (S.homOfLE (le_sup_left : U ≤ U ⊔ V)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, sq_lemma']
  have hv : sch.map (T.homOfLE (f.preimage_mono (le_sup_right : V ≤ U ⊔ V))) ≫ sch.map (f ∣_ (U ⊔ V)) =
      sch.map (f ∣_ V) ≫ sch.map (S.homOfLE (le_sup_right : V ≤ U ⊔ V)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, sq_lemma']
  have key := hnat (sch.map (T.homOfLE (f.preimage_mono (le_sup_left : U ≤ U ⊔ V))))
    (sch.map (T.homOfLE (f.preimage_mono (le_sup_right : V ≤ U ⊔ V))))
    (sch.map (S.homOfLE (le_sup_left : U ≤ U ⊔ V))) (sch.map (S.homOfLE (le_sup_right : V ≤ U ⊔ V)))
    (sch.map (f ∣_ (U ⊔ V))) (sch.map (f ∣_ U)) (sch.map (f ∣_ V)) hu hv hcT hc n c
  rw [← hc', key, ((hd (sch.map (T.homOfLE (f.preimage_mono (le_sup_left : U ≤ U ⊔ V))))
    (sch.map (T.homOfLE (f.preimage_mono (le_sup_right : V ≤ U ⊔ V)))) hcT n).2.1)]
  refine ⟨a, b, ?_⟩
  have inj : Function.Injective (pull R PT.isoPullback.hom F n) := by
    intro z w h
    have h2 := congrArg (pull R PT.isoPullback.inv F n) h
    rwa [← pull_comp, ← pull_comp, Iso.inv_hom_id, pull_id, pull_id] at h2
  apply inj
  rw [map_sub, ← pull_comp, ← pull_comp, ← pull_comp, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd, ← hab, ← pull_comp]
  refine congrArg (fun φ => pull R φ F n c) ?_
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullback.map, pullback.lift_fst, IsPullback.isoPullback_hom_fst_assoc,
      IsPullback.isoPullback_hom_fst, ← Functor.map_comp, ← Functor.map_comp, sq_lemma']
  · rw [Category.assoc, Category.assoc, pullback.map, pullback.lift_snd, IsPullback.isoPullback_hom_snd_assoc,
      IsPullback.isoPullback_hom_snd, ← Functor.map_comp, ← Functor.map_comp, sq_lemma']
end
