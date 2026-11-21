import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFgIsSeparated
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperOfPowerSeriesArcsOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGrpSchemeDescendsToFgSubring
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetAbelianLocusOfGoodReduction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfIsPullbackIsDominant
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteMulByNatAbelianVarietyAlgClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuasiCompactIffLocallyOfFinitePresentation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsClosedImageOfIsClosedSubgroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenConnectedComponentOfNoetherianSpace

section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.ProperLimit

def GoodAt {Y P : Scheme.{0}} (q : Y ⟶ P) (y : Y) : Prop :=
  ∃ W : P.Opens, q y ∈ W ∧ UniversallyClosed (q ∣_ W)

theorem universallyClosed_of_factor {Y P V U V' U' : Scheme.{0}} {q : Y ⟶ P} {v : V ⟶ Y} {r : V ⟶ U}
    {j : U ⟶ P} (h : IsPullback v r q j) [UniversallyClosed r] {v' : V' ⟶ Y} {r' : V' ⟶ U'} (m : U' ⟶ U)
    (h' : IsPullback v' r' q (m ≫ j)) : UniversallyClosed r' := by
  have H : IsPullback (h.lift v' (r' ≫ m) (by rw [Category.assoc, h'.w])) r' r m :=
    IsPullback.of_right (by rwa [h.lift_fst]) (h.lift_snd _ _ _) h
  exact MorphismProperty.of_isPullback H ‹_›

theorem GoodAt.baseChange {Y P Y' P' : Scheme.{0}} {q : Y ⟶ P} {q' : Y' ⟶ P'} {a : Y' ⟶ Y} {g : P' ⟶ P}
    (h : IsPullback a q' q g) {y : Y'} (H : GoodAt q (a y)) : GoodAt q' y := by
  obtain ⟨W, hW, _⟩ := H
  refine ⟨g ⁻¹ᵁ W, ?_, ?_⟩
  · change g (q' y) ∈ W
    rwa [← Scheme.Hom.comp_apply, ← h.w, Scheme.Hom.comp_apply]
  · refine universallyClosed_of_factor (isPullback_morphismRestrict q W).flip (g ∣_ W)
      (v' := (q' ⁻¹ᵁ g ⁻¹ᵁ W).ι ≫ a) ?_
    rw [morphismRestrict_ι]
    exact (isPullback_morphismRestrict q' (g ⁻¹ᵁ W)).flip.paste_horiz h

theorem GoodAt.of_comp {Y P Y' P' : Scheme.{0}} {q : Y ⟶ P} {q' : Y' ⟶ P'} {a : Y' ⟶ Y} {g : P' ⟶ P}
    [UniversallyClosed a] [IsSeparated g] (h : a ≫ q = q' ≫ g) {y : Y'} (H : GoodAt q (a y)) : GoodAt q' y := by
  obtain ⟨W, hW, _⟩ := H
  refine ⟨g ⁻¹ᵁ W, ?_, ?_⟩
  · change g (q' y) ∈ W
    rwa [← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply]
  · have h₁ : UniversallyClosed ((a ≫ q) ∣_ W) := by
      rw [morphismRestrict_comp]
      infer_instance
    rw [h, morphismRestrict_comp] at h₁
    exact UniversallyClosed.of_comp_of_isSeparated _ (g ∣_ W)

theorem range_eq_of_isPullback {Y P Y' P' : Scheme.{0}} {q : Y ⟶ P} {q' : Y' ⟶ P'} {a : Y' ⟶ Y} {g : P' ⟶ P}
    (h : IsPullback a q' q g) : Set.range q' = g ⁻¹' Set.range q := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨a y, by rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]⟩
  · rintro ⟨y, hy⟩
    obtain ⟨w, -, hw⟩ := Scheme.exists_preimage_of_isPullback h y z hy
    exact ⟨w, hw⟩

theorem isLocallyClosed_range {Y P : Scheme.{0}} {q : Y ⟶ P} (H : ∀ y, GoodAt q y) :
    IsLocallyClosed (Set.range q) := by
  refine ((isLocallyClosed_tfae (Set.range q)).out 0 2).2 ?_
  rintro _ ⟨y, rfl⟩
  obtain ⟨W, hW, _⟩ := H y
  refine ⟨W, W.2.mem_nhds hW, ?_⟩
  have := (q ∣_ W).isClosedMap.isClosed_range
  rw [range_eq_of_isPullback (isPullback_morphismRestrict q W).flip] at this
  exact this

theorem universallyClosed_of_isClosed_range {Y P : Scheme.{0}} {q : Y ⟶ P} (H : ∀ y, GoodAt q y)
    (h : IsClosed (Set.range q)) : UniversallyClosed q := by
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @UniversallyClosed) fun z => ?_
  by_cases hz : z ∈ Set.range q
  · obtain ⟨y, rfl⟩ := hz
    exact H y
  · let W : P.Opens := ⟨(Set.range q)ᶜ, h.isOpen_compl⟩
    refine ⟨W, hz, ?_⟩
    have : IsEmpty (q ⁻¹ᵁ W : Y.Opens) := ⟨fun y => y.2 ⟨y.1, rfl⟩⟩
    infer_instance

theorem universallyClosed_snd_iff {X Y P S T : Scheme.{0}} {p : X ⟶ S} {π : Y ⟶ X} {q : Y ⟶ P} {t : P ⟶ S}
    [UniversallyClosed π] [Surjective π] [IsProper t] (w : π ≫ p = q ≫ t) (H : ∀ y, GoodAt q y) (g : T ⟶ S) :
    UniversallyClosed (pullback.snd p g) ↔ IsClosed (pullback.fst t g ⁻¹' Set.range q) := by
  have hq := IsPullback.of_hasPullback q (pullback.fst t g)
  let π' : pullback q (pullback.fst t g) ⟶ pullback p g :=
    pullback.lift (pullback.fst _ _ ≫ π) (pullback.snd _ _ ≫ pullback.snd _ _) (by
      rw [Category.assoc, w, hq.w_assoc, pullback.condition, Category.assoc])
  have e : π' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullback.snd _ _ := pullback.lift_snd _ _ _
  have hπ : IsPullback (pullback.fst _ _) π' π (pullback.fst p g) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (.of_hasPullback p g)
    rw [e, w]
    exact hq.paste_vert (.of_hasPullback t g)
  have : UniversallyClosed π' := MorphismProperty.of_isPullback hπ ‹_›
  have : Surjective π' := MorphismProperty.of_isPullback hπ ‹_›
  rw [← range_eq_of_isPullback hq]
  constructor
  · intro _
    have : UniversallyClosed (pullback.snd q (pullback.fst t g) ≫ pullback.snd t g) := by
      rw [← e]
      infer_instance
    have := UniversallyClosed.of_comp_of_isSeparated (pullback.snd q (pullback.fst t g)) (pullback.snd t g)
    exact (pullback.snd q (pullback.fst t g)).isClosedMap.isClosed_range
  · intro h
    have := universallyClosed_of_isClosed_range (fun y => (H _).baseChange hq (y := y)) h
    have : UniversallyClosed (π' ≫ pullback.snd p g) := by
      rw [e]
      infer_instance
    exact UniversallyClosed.of_comp_surjective π' _

def HasCover {X S : Scheme.{0}} (p : X ⟶ S) (V : Set X) : Prop :=
  ∃ (Y P : Scheme.{0}) (π : Y ⟶ X) (q : Y ⟶ P) (t : P ⟶ S), UniversallyClosed π ∧ Surjective π ∧ IsProper t ∧
    π ≫ p = q ≫ t ∧ ∀ y, π y ∈ V → GoodAt q y

theorem HasCover.union {X S : Scheme.{0}} {p : X ⟶ S} {V V' : Set X} (h : HasCover p V) (h' : HasCover p V') :
    HasCover p (V ∪ V') := by
  obtain ⟨Y, P, π, q, t, _, _, _, w, H⟩ := h
  obtain ⟨Y', P', π', q', t', _, _, _, w', H'⟩ := h'
  let Q : pullback π π' ⟶ pullback t t' :=
    pullback.lift (pullback.fst _ _ ≫ q) (pullback.snd _ _ ≫ q') (by
      rw [Category.assoc, Category.assoc, ← w, ← w', pullback.condition_assoc])
  have e₁ : Q ≫ pullback.fst _ _ = pullback.fst _ _ ≫ q := pullback.lift_fst _ _ _
  have e₂ : Q ≫ pullback.snd _ _ = pullback.snd _ _ ≫ q' := pullback.lift_snd _ _ _
  refine ⟨_, _, pullback.fst π π' ≫ π, Q, pullback.fst t t' ≫ t, inferInstance, inferInstance, inferInstance,
    by rw [reassoc_of% e₁, Category.assoc, w], ?_⟩
  rintro y (hy | hy)
  · exact GoodAt.of_comp e₁.symm (H _ hy)
  · rw [pullback.condition] at hy
    exact GoodAt.of_comp e₂.symm (H' _ hy)

theorem isOpen_diff_range {X U P S Z : Scheme.{0}} {p : X ⟶ S} {t : P ⟶ S} [IsSeparated t] {a : Z ⟶ X} {b : Z ⟶ P}
    (h : IsPullback a b p t) (i : U ⟶ X) [IsOpenImmersion i] (δ : U ⟶ Z) (hδ : δ ≫ a = i) :
    IsOpen (a ⁻¹' Set.range i \ Set.range δ) := by
  have : IsSeparated a := MorphismProperty.of_isPullback h.flip ‹_›
  let γ : U ⟶ pullback a i := pullback.lift δ (𝟙 _) (by simpa)
  have e : γ ≫ pullback.snd a i = 𝟙 _ := pullback.lift_snd _ _ _
  have e' : γ ≫ pullback.fst a i = δ := pullback.lift_fst _ _ _
  have : IsClosedImmersion (γ ≫ pullback.snd a i) := by rw [e]; infer_instance
  have : IsClosedImmersion γ := IsClosedImmersion.of_comp γ (pullback.snd a i)
  have ho := (pullback.fst a i).isOpenEmbedding.isOpenMap _ γ.isClosedEmbedding.isClosed_range.isOpen_compl
  convert ho using 1
  rw [← Scheme.Pullback.range_fst, Set.compl_eq_univ_diff,
    Set.image_diff (pullback.fst a i).isOpenEmbedding.injective, Set.image_univ, ← Set.range_comp, ← e']
  rfl

theorem hasCover_of_section {X U P S : Scheme.{0}} (p : X ⟶ S) [IsSeparated p] (i : U ⟶ X) [IsOpenImmersion i]
    (t : P ⟶ S) [IsProper t] (j : U ⟶ P) [IsOpenImmersion j] (w : i ≫ p = j ≫ t) (σ : S ⟶ P) (hσ : σ ≫ t = 𝟙 _)
    (hd : ∀ s, σ s ∉ Set.range j) : HasCover p (Set.range i) := by
  let a := pullback.fst p t
  let b := pullback.snd p t
  let δ : U ⟶ pullback p t := pullback.lift i j w
  have e₁ : δ ≫ a = i := pullback.lift_fst _ _ _
  have e₂ : δ ≫ b = j := pullback.lift_snd _ _ _
  have e₁' (u : U) : a (δ u) = i u := by rw [← Scheme.Hom.comp_apply, e₁]
  have e₂' (u : U) : b (δ u) = j u := by rw [← Scheme.Hom.comp_apply, e₂]
  have o₁ := isOpen_diff_range (.of_hasPullback p t) i δ e₁
  have o₂ := isOpen_diff_range (IsPullback.of_hasPullback p t).flip j δ e₂
  let Γ : TopologicalSpace.Closeds ↥(pullback p t) := ⟨_, (o₁.union o₂).isClosed_compl⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Γ
  have hI : Set.range I.subschemeι = Γ := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have mem (z : ↥(pullback p t)) : z ∈ Set.range I.subschemeι ↔
      (a z ∈ Set.range i → z ∈ Set.range δ) ∧ (b z ∈ Set.range j → z ∈ Set.range δ) := by
    rw [hI]
    change ¬ ((a z ∈ Set.range i ∧ z ∉ Set.range δ) ∨ (b z ∈ Set.range j ∧ z ∉ Set.range δ)) ↔ _
    tauto
  refine ⟨_, _, I.subschemeι ≫ a, I.subschemeι ≫ b, t, inferInstance, ⟨fun x => ?_⟩, ‹_›,
    by rw [Category.assoc, Category.assoc, pullback.condition], fun y hy => ?_⟩
  · by_cases hx : x ∈ Set.range i
    · obtain ⟨u, rfl⟩ := hx
      obtain ⟨y, hy⟩ := (mem (δ u)).2 ⟨fun _ => ⟨u, rfl⟩, fun _ => ⟨u, rfl⟩⟩
      exact ⟨y, by rw [Scheme.Hom.comp_apply, hy, e₁']⟩
    · let s : X ⟶ pullback p t := pullback.lift (𝟙 _) (p ≫ σ) (by simp [hσ])
      have f₁ : a (s x) = x := by
        rw [← Scheme.Hom.comp_apply, show s ≫ a = 𝟙 _ from pullback.lift_fst _ _ _]
        rfl
      have f₂ : b (s x) = σ (p x) := by
        rw [← Scheme.Hom.comp_apply, show s ≫ b = p ≫ σ from pullback.lift_snd _ _ _, Scheme.Hom.comp_apply]
      obtain ⟨y, hy⟩ := (mem (s x)).2 ⟨fun h => (hx (f₁ ▸ h)).elim, fun h => (hd _ (f₂ ▸ h)).elim⟩
      exact ⟨y, by rw [Scheme.Hom.comp_apply, hy, f₁]⟩
  · obtain ⟨u, hu⟩ := ((mem _).1 ⟨y, rfl⟩).1 hy
    refine ⟨j.opensRange, ⟨u, by rw [Scheme.Hom.comp_apply, ← hu, e₂']⟩, ?_⟩
    let c : pullback I.subschemeι δ ⟶ pullback (I.subschemeι ≫ b) j :=
      pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by rw [pullback.condition_assoc, e₂])
    have g₁ : c ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
    have g₂ : c ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
    have : Surjective c := ⟨fun z => by
      obtain ⟨u, hu⟩ := ((mem _).1 ⟨pullback.fst (I.subschemeι ≫ b) j z, rfl⟩).2
        ⟨pullback.snd (I.subschemeι ≫ b) j z, by
          rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]⟩
      obtain ⟨v, hv, -⟩ := Scheme.exists_preimage_of_isPullback (.of_hasPullback I.subschemeι δ) _ _ hu.symm
      refine ⟨v, (pullback.fst (I.subschemeι ≫ b) j).isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, g₁, hv]⟩
    have : UniversallyClosed (c ≫ pullback.snd (I.subschemeι ≫ b) j) := by
      rw [g₂]
      infer_instance
    have := UniversallyClosed.of_comp_surjective c (pullback.snd (I.subschemeι ≫ b) j)
    refine universallyClosed_of_factor (.of_hasPullback (I.subschemeι ≫ b) j) j.isoOpensRange.inv
      (v' := ((I.subschemeι ≫ b) ⁻¹ᵁ j.opensRange).ι) ?_
    rw [Scheme.Hom.isoOpensRange_inv_comp]
    exact (isPullback_morphismRestrict _ _).flip

theorem hasCover_affine {R : Type} [CommRing R] {X U : Scheme.{0}} (p : X ⟶ Sp R) [IsSeparated p]
    [LocallyOfFiniteType p] (i : U ⟶ X) [IsOpenImmersion i] [IsAffine U] : HasCover p (Set.range i) := by
  have : LocallyOfFiniteType (coprod.desc (i ≫ p) (𝟙 (Sp R))) := by
    refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType) (coprodOpenCover.{0, 0} U (Sp R)) ?_
    rintro ⟨_ | _⟩
    · change LocallyOfFiniteType (coprod.inl ≫ _)
      rw [coprod.inl_desc]
      infer_instance
    · change LocallyOfFiniteType (coprod.inr ≫ _)
      rw [coprod.inr_desc]
      exact MorphismProperty.id_mem (W := @LocallyOfFiniteType) _
  obtain ⟨P, t, j, _, _, e⟩ := ArcProper.exists_isOpenImmersion_isProper (coprod.desc (i ≫ p) (𝟙 (Sp R)))
  refine hasCover_of_section p i t (coprod.inl ≫ j) (by simp [e]) (coprod.inr ≫ j) (by simp [e]) ?_
  rintro s ⟨u, hu⟩
  exact inl_ne_inr U (Sp R) u s (j.isOpenEmbedding.injective hu)

theorem hasCover_univ {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) [IsSeparated p]
    [LocallyOfFiniteType p] [QuasiCompact p] : HasCover p Set.univ := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  refine compact_open_induction_on (P := fun S : X.Opens => HasCover p S) ⊤ isCompact_univ ?_ ?_
  · exact ⟨X, _, 𝟙 _, p, 𝟙 _, inferInstance, inferInstance, inferInstance, by simp, fun _ h => h.elim⟩
  · intro S _ W h
    have : IsAffine W.1 := W.2
    have := h.union (hasCover_affine p W.1.ι)
    rwa [Scheme.Opens.range_ι] at this

open GlobalTheory.Spread GlobalTheory.SpreadSep in

theorem exists_finset_isProper (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V]
    [Algebra k V] {X : Scheme.{0}} (p : X ⟶ Sp k) [LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p]
    [UniversallyClosed (pullback.snd p (spMap (algebraMap k V)))] :
    ∃ s : Finset V, IsProper (pullback.snd p (spMap (algebraMap k (Algebra.adjoin k (s : Set V))))) := by
  classical
  obtain ⟨Y, P, π₀, q₀, q, _, _, _, w, H⟩ := hasCover_univ p
  replace H := fun y => H y trivial
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian P := {}
  obtain ⟨U, Z, hU, hZ, eΔ⟩ := isLocallyClosed_range H
  let s : (Finset V)ᵒᵖ := .op ∅
  let π : (bcDiagram q V).obj s ⟶ P := pullback.fst q _
  have : QuasiCompact π := inferInstanceAs (QuasiCompact (pullback.fst q _))
  let O : P.Opens := ⟨U, hU⟩
  let O' : P.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  have key : ((π ⁻¹ᵁ O : Set _) \ (π ⁻¹ᵁ O' : Set _)) = π ⁻¹' Set.range q₀ := by
    rw [eΔ]
    ext x
    change π x ∈ U ∧ ¬ π x ∉ Z ↔ π x ∈ U ∧ π x ∈ Z
    rw [not_not]
  obtain ⟨j, f, hj⟩ := exists_isClosed_preimage_diff (bcDiagram q V) (bcCone q V) (isLimitBcCone q V)
    (π ⁻¹ᵁ O) (π ⁻¹ᵁ O')
    (QuasiCompact.isCompact_preimage (f := π) _ O.2 (TopologicalSpace.NoetherianSpace.isCompact _))
    (QuasiCompact.isCompact_preimage (f := π) _ O'.2 (TopologicalSpace.NoetherianSpace.isCompact _))
    (by
      have e : (bcCone q V).π.app s ≫ π = pullback.fst q _ := bcMap_fst _ _
      rw [key, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, e]
      exact (universallyClosed_snd_iff w H _).mp ‹_›)
  have e : (bcDiagram q V).map f ≫ π = pullback.fst q _ := bcMap_fst _ _
  rw [key, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, e] at hj
  have := (universallyClosed_snd_iff w H _).mpr hj
  exact ⟨j.unop, { }⟩

end GlobalTheory.ProperLimit
end

section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.AbelianLimit

open RationalPoint in

theorem connectedSpace_of_surjective_pow {k : Type} [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G]
    [IsCommMonObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (h : ∀ n : ℕ, 1 ≤ n → Surjective ((𝟙 G) ^ n : G ⟶ G).left) : ConnectedSpace G.left := by
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : IsNoetherian G.left := {}
  have key (f : G ⟶ G) {x y : 𝟙_ (Over (Sp k)) ⟶ G} (hx : pt x ∈ connectedComponent (pt y)) :
      pt (x ≫ f) ∈ connectedComponent (pt (y ≫ f)) :=
    f.left.continuous.image_connectedComponent_subset (pt y) ⟨_, hx, rfl⟩
  have tr (x z : 𝟙_ (Over (Sp k)) ⟶ G) : x ≫ (𝟙 G * (toUnit G ≫ z)) = x * z := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit G) (𝟙 _), Category.id_comp]
  have key' (z : 𝟙_ (Over (Sp k)) ⟶ G) {x y : 𝟙_ (Over (Sp k)) ⟶ G} (hx : pt x ∈ connectedComponent (pt y)) :
      pt (x * z) ∈ connectedComponent (pt (y * z)) := by
    simpa only [tr] using key (𝟙 G * (toUnit G ≫ z)) hx
  let H : Subgroup (𝟙_ (Over (Sp k)) ⟶ G) :=
    { carrier := {x | pt x ∈ connectedComponent (pt (1 : 𝟙_ (Over (Sp k)) ⟶ G))}
      one_mem' := mem_connectedComponent
      mul_mem' := fun {x y} hx hy => by
        have := key' y hx
        rw [_root_.one_mul, ← connectedComponent_eq hy] at this
        exact this
      inv_mem' := fun {x} hx => by
        have := key (𝟙 G)⁻¹ hx
        rwa [GrpObj.comp_inv, GrpObj.comp_inv, Category.comp_id, Category.comp_id, inv_one] at this }
  have : H.Normal := ⟨fun x hx g => by rwa [_root_.mul_comm g x, mul_inv_cancel_right]⟩
  have : DiscreteTopology (_root_.ConnectedComponents G.left) :=
    ConnectedComponents.discreteTopology_iff.2 isOpen_connectedComponent_of_noetherianSpace
  have : Finite (_root_.ConnectedComponents G.left) := finite_of_compact_of_discrete
  have : Finite ((𝟙_ (Over (Sp k)) ⟶ G) ⧸ H) := by
    refine Finite.of_injective (fun q => ConnectedComponents.mk (pt q.out)) fun q q' e => ?_
    rw [← q.out_eq, ← q'.out_eq]
    refine QuotientGroup.eq.2 ?_
    have := key' q.out⁻¹ (ConnectedComponents.coe_eq_coe'.1 e.symm)
    rwa [mul_inv_cancel, _root_.mul_comm] at this
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have all (x : 𝟙_ (Over (Sp k)) ⟶ G) : x ∈ H := by
    have := h H.index (Nat.one_le_iff_ne_zero.2 Subgroup.FiniteIndex.index_ne_zero)
    obtain ⟨z, hz⟩ := ((𝟙 G) ^ H.index : G ⟶ G).left.surjective (pt x)
    obtain ⟨y, -, rfl⟩ := (pt_mem_image_iff ((𝟙 G) ^ H.index) isClosed_univ x).1 ⟨z, trivial, hz⟩
    rw [MonObj.comp_pow, Category.comp_id]
    exact H.pow_index_mem y
  have hu : connectedComponent (pt (1 : 𝟙_ (Over (Sp k)) ⟶ G)) = Set.univ := by
    by_contra hne
    obtain ⟨x, hx⟩ := exists_pt_mem (isOpen_connectedComponent_of_noetherianSpace _).isClosed_compl
      (Set.nonempty_compl.2 hne)
    exact hx (all x)
  exact connectedSpace_iff_connectedComponent.2 ⟨_, hu⟩

theorem pow_comm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (n : ℕ) :
    ((𝟙 G') ^ n : G' ⟶ G').left ≫ φ = φ ≫ ((𝟙 G) ^ n : G ⟶ G).left := by
  have e := congrArg (fun q => q.left) (map_pow (pushHom h G') (𝟙 G') n)
  have e' (x : Over.mk (G'.hom ≫ f) ⟶ G) : x ^ n = x ≫ (𝟙 G) ^ n := by
    rw [MonObj.comp_pow, Category.comp_id]
  rw [e'] at e
  refine Eq.trans e ?_
  change (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem isPullback_pow {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (n : ℕ) :
    IsPullback φ ((𝟙 G') ^ n : G' ⟶ G').left ((𝟙 G) ^ n : G ⟶ G).left φ := by
  refine IsPullback.of_bot ?_ (pow_comm h n).symm h.1
  rw [Over.w, Over.w]
  exact h.1

theorem surjective_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) (n : ℕ) (hn : 1 ≤ n) :
    Surjective ((𝟙 A) ^ n : A ⟶ A).left := by
  refine ⟨fun x => ?_⟩
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  let K := AlgebraicClosure (S.residueField (A.hom x))
  let t : Sp K ⟶ S := spMap (algebraMap (S.residueField (A.hom x)) K) ≫ S.fromSpecResidueField (A.hom x)
  have ht : A.hom x = t (IsLocalRing.closedPoint K) := by
    exact (Scheme.fromSpecResidueField_apply _ _).symm
  let B := (Over.pullback t).obj A
  have hB : IsAbelianScheme B :=
    { comm := inferInstance
      smooth := inferInstanceAs (Smooth (pullback.snd A.hom t))
      proper := inferInstanceAs (IsProper (pullback.snd A.hom t))
      geomConnected := inferInstanceAs (GeometricallyConnected (pullback.snd A.hom t)) }
  have hm : IsMonHom ((𝟙 B) ^ n : B ⟶ B) := by
    have := hB.comm
    clear hn
    induction n with
    | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (toUnit B ≫ η[B]))
    | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift ((𝟙 B) ^ n) (𝟙 B) ≫ μ[B]))
  have hs := (flat_and_surjective_of_isFinite_abelianEnd
    (fun _ _ f _ _ => (geometricallyIntegral_of_smooth_of_geometricallyConnected.1 f).1) K B hB ((𝟙 B) ^ n)
    hm (MulFiniteAny.isFinite_mulA K B hB n hn)).2
  obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback (.of_hasPullback A.hom t) x _ ht
  obtain ⟨z, rfl⟩ := ((𝟙 B) ^ n : B ⟶ B).left.surjective y
  exact ⟨pullback.fst A.hom t z, (congrArg (fun g => g z) (pow_comm (isGrpPullback_pullback A t) n)).symm.trans hy⟩

theorem isAbelianScheme_of_isDominant {S S' : Scheme.{0}} {B : Over S} {A : Over S'} [GrpObj B] [GrpObj A]
    [IsCommMonObj B] [Smooth B.hom] [IsProper B.hom] {f : S' ⟶ S} [IsDominant f] {φ : A.left ⟶ B.left}
    (h : IsGrpPullback A B f φ) (hA : IsAbelianScheme A) : IsAbelianScheme B := by
  have hd : DenseRange φ := by
    rw [DenseRange, ProperLimit.range_eq_of_isPullback h.1.flip]
    exact f.denseRange.preimage B.hom.isOpenMap
  have hs (n : ℕ) (hn : 1 ≤ n) : Surjective ((𝟙 B) ^ n : B ⟶ B).left := by
    have := surjective_pow A hA n hn
    have : IsProper (((𝟙 B) ^ n : B ⟶ B).left ≫ B.hom) := by rw [Over.w]; infer_instance
    have : IsProper ((𝟙 B) ^ n : B ⟶ B).left := IsProper.of_comp _ B.hom
    refine ⟨Set.range_eq_univ.1 ?_⟩
    rw [← ((𝟙 B) ^ n : B ⟶ B).left.isClosedMap.isClosed_range.closure_eq]
    refine (Dense.mono ?_ hd).closure_eq
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := ((𝟙 A) ^ n : A ⟶ A).left.surjective y
    exact ⟨φ z, (congrArg (fun g => g z) (pow_comm h n)).symm⟩
  refine ⟨‹_›, ‹_›, ‹_›, SemiAbelianCompare.geometricallyConnected_of_isAlgClosed _ fun k _ _ s => ?_⟩
  have : LocallyOfFiniteType ((Over.pullback s).obj B).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd B.hom s))
  have : QuasiCompact ((Over.pullback s).obj B).hom := inferInstanceAs (QuasiCompact (pullback.snd B.hom s))
  exact connectedSpace_of_surjective_pow ((Over.pullback s).obj B) fun n hn =>
    MorphismProperty.of_isPullback (isPullback_pow (isGrpPullback_pullback B s) n) (hs n hn)

theorem abelianScheme_descends_to_fg_subring :
    ∀ (R : Type) [CommRing R] (g : ℕ) (A : Over (Sp R)) [GrpObj A] (F : Finset R), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (φ : A.left ⟶ B.left), (F : Set R) ⊆ S ∧ Algebra.FiniteType ℤ S ∧
      IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧ IsGrpPullback A B (spMap S.subtype) φ := by
  intro R _ g A _ F hA hg
  have := hA.comm
  have := hA.proper
  obtain ⟨k, A₀, _, _, φ₀, hF, hk, _, _, _, h₀⟩ :=
    smooth_grpScheme_descends_to_fg_subring R A F hA.smooth inferInstance inferInstance
  have : IsNoetherianRing k := Algebra.FiniteType.isNoetherianRing ℤ k
  have h₁ : IsPullback φ₀ A.hom A₀.hom (spMap (algebraMap k R)) := h₀.1
  have : UniversallyClosed (pullback.snd A₀.hom (spMap (algebraMap k R))) := by
    rw [← h₁.isoPullback_inv_snd]
    infer_instance
  obtain ⟨s, hs⟩ := ProperLimit.exists_finset_isProper k R A₀.hom
  let S : Subalgebra k R := Algebra.adjoin k (s : Set R)
  let t : Sp S.toSubring ⟶ Sp k := spMap (algebraMap k S)
  have e : spMap S.toSubring.subtype ≫ t = spMap k.subtype := Spread.spMap_algHom_comp S.val
  obtain ⟨φ, hφ⟩ := GoodVal.exists_isGrpPullback_of_comp A₀ t (spMap S.toSubring.subtype) (e ▸ h₀)
  have hsm : Smooth ((Over.pullback t).obj A₀).hom := inferInstanceAs (Smooth (pullback.snd A₀.hom t))
  have : IsProper ((Over.pullback t).obj A₀).hom := hs
  have hd : IsDominant (spMap S.toSubring.subtype) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical S.toSubring.subtype).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]
      exact bot_le)⟩
  exact ⟨S.toSubring, (Over.pullback t).obj A₀, inferInstance, φ, fun x hx => S.algebraMap_mem ⟨x, hF hx⟩,
    SpreadGroup.finiteType_of_fg hk (Subalgebra.fg_adjoin_finset s), isAbelianScheme_of_isDominant hφ hA,
    smoothOfRelativeDimension_of_isPullback_isDominant _ _ _ _ _ _ _ _ g hφ.1 hd hsm hg, hφ⟩

end GlobalTheory.AbelianLimit
end
