import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionFlatLocallyQuasiFinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniversalTorsionPairPolAV
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitTorsAlgClosedFractionField
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.IsFractionRingIntO

section
open AlgebraicGeometry CategoryTheory Limits TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SplitFinitePart

theorem exists_section_of_isIntegralHom {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K]
    [Algebra R K] [IsFractionRing R K] {N : Scheme.{0}} (g : N ⟶ Sp R) [IsIntegralHom g] (γ : Sp K ⟶ N)
    (hγ : γ ≫ g = spMap (algebraMap R K)) : ∃ s : Sp R ⟶ N, s ≫ g = 𝟙 _ ∧ spMap (algebraMap R K) ≫ s = γ := by
  have : IsAffine N := isAffine_of_isAffineHom g
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (N.isoSpec.inv ≫ g)
  obtain ⟨c, hc⟩ := Spec.map_surjective (γ ≫ N.isoSpec.hom)
  have h1 : IsIntegralHom (Spec.map ψ) := by rw [hψ]; infer_instance
  have hint : ψ.hom.IsIntegral := IsIntegralHom.SpecMap_iff.mp h1
  have h2 : ψ ≫ c = CommRingCat.ofHom (algebraMap R K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hc, hψ, Category.assoc, Iso.hom_inv_id_assoc, hγ]
  have h3 : c.hom.comp ψ.hom = algebraMap R K := congrArg CommRingCat.Hom.hom h2
  have h4 : ∀ b, ∃ a : R, algebraMap R K a = c.hom b := fun b => by
    refine IsIntegrallyClosed.isIntegral_iff.mp ?_
    have := (hint b).map c.hom
    rwa [h3] at this
  choose σ hσ using h4
  have hi := IsFractionRing.injective R K
  let σ' : Γ(N, ⊤) →+* R :=
    { toFun := σ
      map_one' := hi (by simp [hσ])
      map_mul' := fun a b => hi (by simp [hσ])
      map_zero' := hi (by simp [hσ])
      map_add' := fun a b => hi (by simp [hσ]) }
  refine ⟨spMap σ' ≫ N.isoSpec.inv, ?_, ?_⟩
  · rw [Category.assoc, ← hψ, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext a
    exact hi ((hσ _).trans (congrArg (fun φ : R →+* K => φ a) h3))
  · rw [← Category.assoc, Iso.comp_inv_eq, ← hc, ← Spec.map_comp]
    congr 1
    ext a
    exact hσ a

theorem exists_finite_open {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K]
    [Algebra R K] [IsFractionRing R K] {Z : Scheme.{0}} (π : Z ⟶ Sp R) [Flat π] [LocallyQuasiFinite π]
    [IsSeparated π] [QuasiCompact π] [LocallyOfFiniteType π]
    (hs : ∀ z : Z, π z = genericPoint (Sp R) →
      ∃ γ : Sp K ⟶ Z, γ ≫ π = spMap (algebraMap R K) ∧ z ∈ Set.range γ) (p : Sp R) :
    ∃ (W : (Sp R).Opens) (H : Z.Opens) (ρ : H.toScheme ⟶ W.toScheme), p ∈ W ∧ ρ ≫ W.ι = H.ι ≫ π ∧ IsFinite ρ ∧
      (∀ z : Z, π z = p → z ∈ H) ∧
      ∀ z ∈ H, ∃ s : W.toScheme ⟶ Z, s ≫ π = W.ι ∧ (∀ w, s w ∈ H) ∧ z ∈ Set.range s := by
  let j := π.toNormalization
  let g := π.fromNormalization
  have hjg : j ≫ g = π := π.toNormalization_fromNormalization
  have hjg' : ∀ z, g (j z) = π z := fun z => by rw [← Scheme.Hom.comp_apply, hjg]
  let I : Type := π ⁻¹' {genericPoint (Sp R)}
  have : Finite I := π.finite_preimage_singleton _
  choose γ hγ hγ' using fun i : I => hs i.1 i.2
  choose s hs1 hs2 using fun i : I => exists_section_of_isIntegralHom g (γ i ≫ j) (by rw [Category.assoc, hjg, hγ])
  have hgs : ∀ i y, g (s i y) = y := fun i y => by rw [← Scheme.Hom.comp_apply, hs1]; rfl
  have hcl : ∀ i, IsClosed (Set.range (s i)) := fun i => by
    have : IsClosedImmersion (s i ≫ g) := by rw [hs1]; infer_instance
    have : IsClosedImmersion (s i) := IsClosedImmersion.of_comp _ g
    exact (s i).isClosedEmbedding.isClosed_range
  have hcov : ∀ z : Z, ∃ i, s i (π z) = j z := fun z => by
    obtain ⟨z', hz', e⟩ := Flat.generalizingMap π (genericPoint_specializes (π z))
    obtain ⟨a, ha⟩ := hγ' ⟨z', e⟩
    have h1 : j z' ∈ Set.range (s ⟨z', e⟩) :=
      ⟨spMap (algebraMap R K) a, by rw [← Scheme.Hom.comp_apply, hs2, Scheme.Hom.comp_apply, ha]⟩
    obtain ⟨y, hy⟩ := (hz'.map j.continuous).mem_closed (hcl _) h1
    refine ⟨⟨z', e⟩, ?_⟩
    rw [← hjg', ← hy, hgs]
  let good : I → Prop := fun i => s i p ∈ Set.range j
  let U : π.normalization.Opens := ⟨Set.range j \ ⋃ i : {i // ¬ good i}, Set.range (s i.1),
    j.isOpenEmbedding.isOpen_range.sdiff (isClosed_iUnion_of_finite fun i => hcl i.1)⟩
  let W : (Sp R).Opens := ⟨⋂ i : {i // good i}, s i.1 ⁻¹' U,
    isOpen_iInter_of_finite fun i => U.isOpen.preimage (s i.1).continuous⟩
  have hU : ∀ n, n ∈ Set.range j → g n = p → n ∈ U := fun n hn hp => ⟨hn, fun h => by
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp h
    apply i.2
    have : y = p := by rw [← hp, ← hy, hgs]
    subst this
    change s i.1 y ∈ Set.range j
    rw [hy]; exact hn⟩
  have hpW : p ∈ W := Set.mem_iInter.mpr fun i => hU _ i.2 (hgs _ _)
  have hgood : ∀ i y, s i y ∈ U → good i := fun i y h => by
    by_contra hn
    exact h.2 (Set.mem_iUnion.mpr ⟨⟨i, hn⟩, y, rfl⟩)
  have hWU : ∀ i, good i → ∀ y ∈ W, s i y ∈ U := fun i hi y hy => Set.mem_iInter.mp hy ⟨i, hi⟩
  let H : Z.Opens := j ⁻¹ᵁ U ⊓ π ⁻¹ᵁ W
  have hle : H ≤ j ⁻¹ᵁ (g ⁻¹ᵁ W) := fun z hz => by
    change g (j z) ∈ W
    rw [hjg']; exact hz.2
  let a := j.resLE _ H hle
  have ha : a ≫ (g ⁻¹ᵁ W).ι = H.ι ≫ j := j.resLE_comp_ι hle
  have ha' : ∀ z, (a z).1 = j z.1 := fun z => by
    have := congrArg (fun φ : H.toScheme ⟶ _ => φ z) ha
    exact this
  have : IsOpenImmersion (a ≫ (g ⁻¹ᵁ W).ι) := by rw [ha]; infer_instance
  have : IsOpenImmersion a := IsOpenImmersion.of_comp _ (g ⁻¹ᵁ W).ι
  have hr : Set.range a = (g ⁻¹ᵁ W).ι ⁻¹' ⋃ i : {i // good i}, Set.range (s i.1) := by
    ext n
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨i, hi⟩ := hcov z.1
      exact Set.mem_iUnion.mpr ⟨⟨i, hgood i _ (by rw [hi]; exact z.2.1)⟩, π z.1, hi.trans (ha' z).symm⟩
    · intro hn
      obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hn
      have hy' : s i y = n.1 := hy
      have hyW : y ∈ W := by
        rw [← hgs i y, hy']; exact n.2
      have h1 := hWU i.1 i.2 y hyW
      obtain ⟨z, hz⟩ := h1.1
      refine ⟨⟨z, show j z ∈ U from hz ▸ h1, show π z ∈ W by rw [← hjg', hz, hgs]; exact hyW⟩, Subtype.ext ?_⟩
      exact (ha' _).trans (hz.trans hy')
  have : IsClosedImmersion a := IsClosedImmersion.of_isPreimmersion _ (by
    rw [hr]
    exact (isClosed_iUnion_of_finite fun i : {i // good i} => hcl i.1).preimage (g ⁻¹ᵁ W).ι.continuous)
  have hρ : (a ≫ g ∣_ W) ≫ W.ι = H.ι ≫ π := by
    rw [Category.assoc, morphismRestrict_ι, reassoc_of% ha, hjg]
  refine ⟨W, H, a ≫ g ∣_ W, hpW, hρ, ?_, fun z hz => ⟨hU _ ⟨z, rfl⟩ ((hjg' z).trans hz), show π z ∈ W from hz ▸ hpW⟩,
    fun z hz => ?_⟩
  · have : LocallyOfFiniteType ((a ≫ g ∣_ W) ≫ W.ι) := by rw [hρ]; infer_instance
    have : LocallyOfFiniteType (a ≫ g ∣_ W) := locallyOfFiniteType_of_comp _ W.ι
    exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨inferInstance, this⟩
  · obtain ⟨i, hi⟩ := hcov z
    have hg := hgood i (π z) (by rw [hi]; exact hz.1)
    have hsub : Set.range (W.ι ≫ s i) ⊆ Set.range j := by
      rintro _ ⟨w, rfl⟩
      exact (hWU i hg w.1 w.2).1
    have hl := IsOpenImmersion.lift_fac j (W.ι ≫ s i) hsub
    have hl' : ∀ w : W.toScheme, j (IsOpenImmersion.lift j (W.ι ≫ s i) hsub w) = s i w.1 := fun w => by
      rw [← Scheme.Hom.comp_apply, hl]; rfl
    refine ⟨IsOpenImmersion.lift j (W.ι ≫ s i) hsub, ?_, fun w => ⟨?_, ?_⟩, ⟨π z, hz.2⟩, ?_⟩
    · refine (congrArg (_ ≫ ·) hjg.symm).trans ?_
      simp only [reassoc_of% hl, hs1, Category.comp_id]
    · change j _ ∈ U
      rw [hl']; exact hWU i hg w.1 w.2
    · change π _ ∈ W
      rw [← hjg', hl', hgs]; exact w.2
    · apply j.isOpenEmbedding.injective
      exact (hl' _).trans hi

theorem range_of_isPullback {P X Y S : Scheme.{0}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (h : IsPullback a b f g) : Set.range a = f ⁻¹' Set.range g := by
  rw [← Scheme.Pullback.range_fst, ← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, h.isoPullback.hom.surjective.range_eq, Set.image_univ]

theorem exists_free_away {R : Type} [CommRing R] (f₀ : R) (p : PrimeSpectrum R) (hp : f₀ ∉ p.asIdeal) (B : Type)
    [CommRing B] [Algebra (Localization.Away f₀) B] [Module.Finite (Localization.Away f₀) B]
    [Module.Flat (Localization.Away f₀) B] [Algebra.FinitePresentation (Localization.Away f₀) B] :
    ∃ (f : R) (_ : Algebra (Localization.Away f₀) (Localization.Away f)), f ∉ p.asIdeal ∧
      IsScalarTower R (Localization.Away f₀) (Localization.Away f) ∧
      Module.Free (Localization.Away f) (Localization.Away f ⊗[Localization.Away f₀] B) := by
  set A := Localization.Away f₀
  have := Module.FinitePresentation.of_finite_of_finitePresentation A B
  obtain ⟨q, rfl⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R A)) := by
    rw [PrimeSpectrum.localization_away_comap_range A f₀]; exact hp
  have : Module.Free (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl B) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hf, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    q.asIdeal.primeCompl (LocalizedModule.mkLinearMap q.asIdeal.primeCompl B) (Localization.AtPrime q.asIdeal)
  obtain ⟨⟨r', u⟩, hu⟩ := IsLocalization.surj (Submonoid.powers f₀) r
  have hu' : IsUnit (algebraMap R A u) := IsLocalization.map_units A u
  have hass : Associated r (algebraMap R A r') := ⟨hu'.unit, hu⟩
  have hr' : r' ∉ (PrimeSpectrum.comap (algebraMap R A) q).asIdeal := fun h => by
    have h' : algebraMap R A r' ∈ q.asIdeal := h
    rw [← show r * algebraMap R A u = algebraMap R A r' from hu] at h'
    exact (q.isPrime.mem_or_mem h').elim hr fun h'' => q.isPrime.ne_top (q.asIdeal.eq_top_of_isUnit_mem h'' hu')
  let T := Localization.Away r
  have : IsLocalization.Away (algebraMap R A r') T := IsLocalization.Away.of_associated hass
  have : IsLocalization.Away (f₀ * r') T := IsLocalization.Away.mul' A T f₀ r'
  let e : T ≃ₐ[R] Localization.Away (f₀ * r') := IsLocalization.algEquiv (Submonoid.powers (f₀ * r')) _ _
  letI : Algebra T (Localization.Away (f₀ * r')) := e.toRingHom.toAlgebra
  letI : Algebra A (Localization.Away (f₀ * r')) := (e.toRingHom.comp (algebraMap A T)).toAlgebra
  have : IsScalarTower A T (Localization.Away (f₀ * r')) := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Free T (T ⊗[A] B) := Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers r) B)
  refine ⟨f₀ * r', inferInstance, fun h => ((PrimeSpectrum.comap (algebraMap R A) q).isPrime.mem_or_mem h).elim hp hr',
    IsScalarTower.of_algebraMap_eq fun x => ?_, Module.Free.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange A T
      (Localization.Away (f₀ * r')) (Localization.Away (f₀ * r')) B)⟩
  change _ = e (algebraMap A T (algebraMap R A x))
  rw [← IsScalarTower.algebraMap_apply, e.commutes]

theorem exists_free_chart {R : Type} [CommRing R] {Z : Scheme.{0}} (π : Z ⟶ Sp R) [Flat π]
    [LocallyOfFinitePresentation π] (p : PrimeSpectrum R) (W W' : (Sp R).Opens) (H : Z.Opens)
    (ρ : H.toScheme ⟶ W.toScheme) (hW : p ∈ W) (hW' : p ∈ W') (hρ : ρ ≫ W.ι = H.ι ≫ π) [IsFinite ρ] :
    ∃ (f : R) (B : Type) (_ : CommRing B) (_ : Algebra (Localization.Away f) B) (j : Sp B ⟶ Z), f ∉ p.asIdeal ∧
      Module.Finite (Localization.Away f) B ∧ Module.Free (Localization.Away f) B ∧ IsOpenImmersion j ∧
      j ≫ π = spMap (algebraMap (Localization.Away f) B) ≫ spMap (algebraMap R (Localization.Away f)) ∧
      Set.range (spMap (algebraMap R (Localization.Away f))) ⊆ (W : Set (Sp R)) ∩ W' ∧
      Set.range j = (H : Set Z) ∩ π ⁻¹' Set.range (spMap (algebraMap R (Localization.Away f))) := by
  obtain ⟨_, ⟨f₀, rfl⟩, hp, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show p ∈ (W ⊓ W').1 from ⟨hW, hW'⟩) (W ⊓ W').isOpen
  let A := Localization.Away f₀
  have hA : Set.range (spMap (algebraMap R A)) ⊆ (W : Set (Sp R)) ∩ W' :=
    (PrimeSpectrum.localization_away_comap_range A f₀).subset.trans hsub
  have hA' : Set.range (spMap (algebraMap R A)) ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]; exact fun x hx => (hA hx).1
  let a := IsOpenImmersion.lift W.ι (spMap (algebraMap R A)) hA'
  have ha : a ≫ W.ι = spMap (algebraMap R A) := IsOpenImmersion.lift_fac _ _ _
  have P₀ : IsPullback (𝟙 _) ρ (H.ι ≫ π) W.ι := IsPullback.of_horiz_isIso_mono ⟨by rw [hρ, Category.id_comp]⟩
  have : Flat ρ := MorphismProperty.of_isPullback (P := @Flat) P₀ inferInstance
  have : LocallyOfFinitePresentation ρ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) P₀ inferInstance
  have : IsAffine (pullback ρ a) := isAffine_of_isAffineHom (pullback.snd ρ a)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective ((pullback ρ a).isoSpec.inv ≫ pullback.snd ρ a)
  let B₀ : Type := Γ(pullback ρ a, ⊤)
  letI : Algebra A B₀ := ψ.hom.toAlgebra
  have : Module.Finite A B₀ := (IsFinite.SpecMap_iff ψ).mp (by rw [hψ]; infer_instance)
  have : Module.Flat A B₀ := Flat.SpecMap_iff.mp (show Flat (Spec.map ψ) by rw [hψ]; infer_instance)
  have : Algebra.FinitePresentation A B₀ := (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp
    (show LocallyOfFinitePresentation (Spec.map ψ) by rw [hψ]; infer_instance)
  obtain ⟨f, _, hf, hT, hfree⟩ := exists_free_away f₀ p hp B₀
  let A' := Localization.Away f
  have e : spMap (algebraMap A A') ≫ spMap (algebraMap R A) = spMap (algebraMap R A') := by
    rw [← Spec.map_comp, IsScalarTower.algebraMap_eq R A A']; rfl
  have P₁ := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A A' B₀)
  have P₂ : IsPullback ((pullback ρ a).isoSpec.inv ≫ pullback.fst ρ a) (spMap (algebraMap A B₀)) ρ a := by
    have h : spMap (algebraMap A B₀) = (pullback ρ a).isoSpec.inv ≫ pullback.snd ρ a := hψ
    rw [h]
    exact IsPullback.of_iso (IsPullback.of_hasPullback ρ a) (pullback ρ a).isoSpec (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  have P₃ := P₁.flip.paste_horiz P₂
  have e' : (spMap (algebraMap A A') ≫ a) ≫ W.ι = spMap (algebraMap R A') := by rw [Category.assoc, ha, e]
  have : IsOpenImmersion (spMap (algebraMap R A')) := IsOpenImmersion.of_isLocalization f
  have : IsOpenImmersion ((spMap (algebraMap A A') ≫ a) ≫ W.ι) := by rw [e']; infer_instance
  have ho : IsOpenImmersion (spMap (algebraMap A A') ≫ a) := IsOpenImmersion.of_comp _ W.ι
  have ho' := MorphismProperty.of_isPullback (P := @IsOpenImmersion) P₃.flip ho
  have hr := range_of_isPullback P₃
  have hw := P₃.w
  generalize (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := A') (B := B₀)).toRingHom) ≫
    (pullback ρ a).isoSpec.inv ≫ pullback.fst ρ a) = j at ho' hr hw
  have hρ' : ∀ z, (ρ z).1 = π z.1 := fun z => congrArg (fun φ : H.toScheme ⟶ _ => φ z) hρ
  refine ⟨f, A' ⊗[A] B₀, inferInstance, inferInstance, j ≫ H.ι, hf, inferInstance, hfree, inferInstance, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← hρ, reassoc_of% hw, ← e']
    rfl
  · rintro _ ⟨y, rfl⟩
    exact hA ⟨spMap (algebraMap A A') y, by rw [← Scheme.Hom.comp_apply, e]⟩
  · ext z
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨w, hw'⟩ := hr.subset ⟨y, rfl⟩
      refine ⟨(j y).2, w, ?_⟩
      rw [← e', Scheme.Hom.comp_apply, hw']
      exact hρ' _
    · rintro ⟨hz, w, hw'⟩
      obtain ⟨y, hy⟩ := hr.superset (show (⟨z, hz⟩ : H.toScheme) ∈ ρ ⁻¹' Set.range (spMap (algebraMap A A') ≫ a) from
        ⟨w, Subtype.ext (by
          refine Eq.trans ?_ (hρ' ⟨z, hz⟩).symm
          refine Eq.trans ?_ hw'
          rw [← e']; rfl)⟩)
      exact ⟨y, by rw [Scheme.Hom.comp_apply, hy]; rfl⟩

theorem exists_open_fibres_subset {P S : Scheme.{0}} (W : S.Opens) (ρ : P ⟶ W.toScheme) [UniversallyClosed ρ]
    (U : P.Opens) (p : S) (hp : p ∈ W) (hU : ∀ y : P, (ρ y).1 = p → y ∈ U) :
    ∃ W' : S.Opens, p ∈ W' ∧ ∀ y : P, (ρ y).1 ∈ W' → y ∈ U := by
  have hc : IsClosed (ρ '' (U : Set P)ᶜ) := ρ.isClosedMap _ U.isOpen.isClosed_compl
  refine ⟨⟨W.ι '' (ρ '' (U : Set P)ᶜ)ᶜ, W.ι.isOpenEmbedding.isOpenMap _ hc.isOpen_compl⟩, ⟨⟨p, hp⟩, ?_, rfl⟩, ?_⟩
  · rintro ⟨y, hy, e⟩
    exact hy (hU y (congrArg Subtype.val e))
  · rintro y ⟨w, hw, e⟩
    by_contra hy
    exact hw ⟨y, hy, Subtype.ext e.symm⟩

theorem eq_comp_section {A B k : Type} [CommRing A] [CommRing B] [Algebra A B] [Field k] (β : B →+* k)
    (σ : B →ₐ[A] A) (y : Sp k) (h : spMap β y ∈ Set.range (spMap σ.toRingHom)) :
    β = (β.comp (algebraMap A B)).comp σ.toRingHom := by
  obtain ⟨Q, hQ⟩ := h
  ext b
  have h1 : b - algebraMap A B (σ b) ∈ (spMap σ.toRingHom Q).asIdeal := by
    change σ (b - algebraMap A B (σ b)) ∈ Q.asIdeal
    simp
  rw [hQ] at h1
  have h2 : β (b - algebraMap A B (σ b)) ∈ y.asIdeal := h1
  rw [(Ideal.eq_bot_of_prime y.asIdeal (h := y.isPrime)), Ideal.mem_bot, map_sub, sub_eq_zero] at h2
  exact h2

theorem isReduced_of_generic {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {Z : Scheme.{0}} (π : Z ⟶ Sp R) [Flat π] [IsReduced (pullback π (spMap (algebraMap R K)))] : IsReduced Z := by
  have : IsDominant (spMap (algebraMap R K)) := by
    rw [isDominant_iff]
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R K)).mpr ?_
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R K)]
    exact bot_le
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap R K))
  exact IsSchemeTheoreticallyDominant.isReduced (pullback.fst π (spMap (algebraMap R K)))

theorem mem_of_forall_maximal {S : Type} [CommRing S] (U : (Sp S).Opens)
    (h : ∀ 𝔪 : Ideal S, 𝔪.IsMaximal → ∀ y, spMap (Ideal.Quotient.mk 𝔪) y ∈ U) (s : Sp S) : s ∈ U := by
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal s.asIdeal s.isPrime.ne_top
  have := h𝔪.isPrime
  have h1 := h 𝔪 h𝔪 ⟨⊥, Ideal.isPrime_bot⟩
  refine Specializes.mem_open ((PrimeSpectrum.le_iff_specializes _ _).mp ?_) U.isOpen h1
  intro a ha
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hle ha)

theorem epi_spMap {K L : Type} [Field K] [Field L] (σ : K →+* L) : Epi (spMap σ) := by
  have : Flat (spMap σ) := inferInstance
  have : Surjective (spMap σ) := ⟨fun u => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

end GlobalTheory.SplitFinitePart
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SplitFinitePart

structure IsTorsionOver {X S Z : Scheme.{0}} (G : Over X) [GrpObj G] (x : S ⟶ X) (q : ℕ) (π : Z ⟶ S)
    (κ : Over.mk (π ≫ x) ⟶ G) : Prop where
  pow : κ ^ q = 1
  lift : ∀ (T : Over X) (w : T ⟶ G) (c : T.left ⟶ S), c ≫ x = T.hom → w ^ q = 1 →
    ∃ z : T.left ⟶ Z, z ≫ π = c ∧ z ≫ κ.left = w.left
  ext : ∀ (T : Scheme.{0}) (z z' : T ⟶ Z), z ≫ π = z' ≫ π → z ≫ κ.left = z' ≫ κ.left → z = z'

theorem isTorsionOver {X S : Scheme.{0}} (G : Over X) [GrpObj G] (x : S ⟶ X) (q : ℕ) :
    IsTorsionOver G x q (pullback.snd (torsion G q).hom x)
      (Over.homMk (pullback.fst (torsion G q).hom x) pullback.condition ≫ torsion.ι G q) where
  pow := by rw [← MonObj.comp_pow, (LamF.torsion_universal G q).1, MonObj.comp_one]
  lift T w c hc hw := by
    obtain ⟨w', rfl⟩ := (LamF.torsion_universal G q).2 T w hw
    refine ⟨pullback.lift w'.left c ((Over.w w').trans hc.symm), pullback.lift_snd _ _ _, ?_⟩
    exact pullback.lift_fst_assoc _ _ _ _
  ext T z z' h h' := by
    have : Mono (torsion.ι G q) := inferInstanceAs (Mono (pullback.fst _ _))
    have : Mono (torsion.ι G q).left := inferInstanceAs (Mono ((Over.forget X).map (torsion.ι G q)))
    refine pullback.hom_ext ?_ h
    rw [← cancel_mono (torsion.ι G q).left]
    simpa using h'

variable {X S Z : Scheme.{0}} {G : Over X} [GrpObj G] {x : S ⟶ X} {q : ℕ} {π : Z ⟶ S} {κ : Over.mk (π ≫ x) ⟶ G}

theorem IsTorsionOver.pow_eq_one (h : IsTorsionOver G x q π κ) {T : Over X} (w : T ⟶ G) (z : T.left ⟶ Z)
    (hz : z ≫ κ.left = w.left) : w ^ q = 1 := by
  have h1 : z ≫ π ≫ x = T.hom := by
    rw [← Over.w w, ← hz, Category.assoc, Over.w κ]; rfl
  have h2 : w = (Over.homMk z h1 : T ⟶ Over.mk (π ≫ x)) ≫ κ := Over.OverMorphism.ext hz.symm
  rw [h2, ← MonObj.comp_pow, h.pow, MonObj.comp_one]

theorem IsTorsionOver.exists_open_one (h : IsTorsionOver G x q π κ) (p : S) (H : Z.Opens)
    (hH : ∀ z : Z, π z = p → z ∈ H) : ∃ W : S.Opens, p ∈ W ∧ ∀ (T : Over X) (z : T.left ⟶ Z),
      z ≫ κ.left = (1 : T ⟶ G).left → ∀ s, π (z s) ∈ W → z s ∈ H := by
  obtain ⟨e, he, he'⟩ := h.lift (Over.mk x) 1 (𝟙 S) (Category.id_comp _) (one_pow _)
  refine ⟨e ⁻¹ᵁ H, hH _ (by rw [← Scheme.Hom.comp_apply, he]; rfl), fun T z hz s hs => ?_⟩
  have h1 : (z ≫ π) ≫ x = T.hom := by
    rw [← Over.w (1 : T ⟶ G), ← hz, Category.assoc, Category.assoc, Over.w κ]; rfl
  have h2 : z = (z ≫ π) ≫ e := by
    refine h.ext _ _ _ (by rw [Category.assoc (z ≫ π), he]; exact (Category.comp_id _).symm) ?_
    rw [Category.assoc (z ≫ π), he', hz, ← MonObj.comp_one (Over.homMk (z ≫ π) h1 : T ⟶ Over.mk x)]
    rfl
  rw [h2]
  exact hs

theorem IsTorsionOver.exists_open_mul [IsCommMonObj G] (h : IsTorsionOver G x q π κ) (p : S) (W : S.Opens)
    (H : Z.Opens) (ρ : H.toScheme ⟶ W.toScheme) (hp : p ∈ W) (hρ : ρ ≫ W.ι = H.ι ≫ π) [IsFinite ρ]
    (hH : ∀ z : Z, π z = p → z ∈ H) : ∃ W' : S.Opens, p ∈ W' ∧ ∀ (T : Over X) (w w' : T ⟶ G)
      (z z' z'' : T.left ⟶ Z), z ≫ κ.left = w.left → z' ≫ κ.left = w'.left → z'' ≫ κ.left = (w * w').left →
      z' ≫ π = z ≫ π → z'' ≫ π = z ≫ π → (∀ s, z s ∈ H) → (∀ s, z' s ∈ H) → ∀ s, π (z s) ∈ W' → z'' s ∈ H := by
  let c : pullback ρ ρ ⟶ S := (pullback.fst ρ ρ ≫ ρ) ≫ W.ι
  let P : Over X := Over.mk (c ≫ x)
  let a : P ⟶ G := (Over.homMk (pullback.fst ρ ρ ≫ H.ι) (by
    simp only [P, c, Over.mk_hom, Category.assoc, reassoc_of% hρ]) : P ⟶ Over.mk (π ≫ x)) ≫ κ
  let b : P ⟶ G := (Over.homMk (pullback.snd ρ ρ ≫ H.ι) (by
    simp only [P, c, Over.mk_hom, Category.assoc, pullback.condition_assoc, reassoc_of% hρ]) :
      P ⟶ Over.mk (π ≫ x)) ≫ κ
  have hab : (a * b) ^ q = 1 := by
    rw [mul_pow, h.pow_eq_one a (pullback.fst ρ ρ ≫ H.ι) rfl, h.pow_eq_one b (pullback.snd ρ ρ ≫ H.ι) rfl, _root_.mul_one]
  obtain ⟨m, hm, hm'⟩ := h.lift P (a * b) c rfl hab
  have hc : ∀ y : ↥(pullback ρ ρ), ((pullback.fst ρ ρ ≫ ρ) y).1 = π (m y) := fun y =>
    (congrArg (fun φ : pullback ρ ρ ⟶ S => φ y) hm).symm
  obtain ⟨W', hW', hm''⟩ := exists_open_fibres_subset W (pullback.fst ρ ρ ≫ ρ) (m ⁻¹ᵁ H) p hp
    fun y hy => hH _ ((hc y).symm.trans hy)
  refine ⟨W', hW', fun T w w' z z' z'' hz hz' hz'' e' e'' hzH hzH' s hs => ?_⟩
  have r : Set.range z ⊆ Set.range H.ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨s, rfl⟩; exact hzH s
  have r' : Set.range z' ⊆ Set.range H.ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨s, rfl⟩; exact hzH' s
  have f := IsOpenImmersion.lift_fac H.ι z r
  have f' := IsOpenImmersion.lift_fac H.ι z' r'
  let l : T.left ⟶ pullback ρ ρ := pullback.lift (IsOpenImmersion.lift H.ι z r) (IsOpenImmersion.lift H.ι z' r') (by
    rw [← cancel_mono W.ι, Category.assoc, Category.assoc, hρ, reassoc_of% f, reassoc_of% f', e'])
  have l1 : l ≫ pullback.fst ρ ρ ≫ H.ι = z := by rw [pullback.lift_fst_assoc, f]
  have l2 : l ≫ pullback.snd ρ ρ ≫ H.ι = z' := by rw [pullback.lift_snd_assoc, f']
  have lc : l ≫ c = z ≫ π := by
    rw [← l1]; simp only [c, Category.assoc, hρ]
  have lx : l ≫ c ≫ x = T.hom := by
    rw [reassoc_of% lc, ← Over.w w, ← hz, Category.assoc, Over.w κ]; rfl
  let L : T ⟶ P := Over.homMk l lx
  have La : L ≫ a = w := Over.OverMorphism.ext (by
    rw [← hz, ← l1]; simp [L, a])
  have Lb : L ≫ b = w' := Over.OverMorphism.ext (by
    rw [← hz', ← l2]; simp [L, b])
  have key : z'' = l ≫ m := by
    refine h.ext _ _ _ (by rw [e'', ← lc, ← hm]; exact (Category.assoc _ _ _).symm) ?_
    rw [hz'', ← La, ← Lb, ← MonObj.comp_mul, Category.assoc]
    exact congrArg (l ≫ ·) hm'.symm
  rw [key]
  refine hm'' (l s) ?_
  rw [hc]
  change ((l ≫ m) ≫ π) s ∈ W'
  rw [← key, e'']
  exact hs

theorem IsTorsionOver.exists_rational {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (t : SAB H X) {R : Type} [CommRing R] [IsDomain R] {x : Sp R ⟶ X}
    {π : Z ⟶ Sp R} {κ : Over.mk (π ≫ x) ⟶ t.G} (h : IsTorsionOver t.G x q π κ) (hs : SplitTors t x q) (z : Z)
    (hz : π z = genericPoint (Sp R)) :
    ∃ g₀ : Sp (FractionRing R) ⟶ Z, g₀ ≫ π = spMap (algebraMap R (FractionRing R)) ∧ z ∈ Set.range g₀ := by
  obtain ⟨Ω, _, y, o, hy⟩ : ∃ (Ω : Type) (_ : Field Ω) (y : Sp Ω ⟶ Z) (o : Sp Ω), y o = z :=
    ⟨Z.residueField z, inferInstance, Z.fromSpecResidueField z, IsLocalRing.closedPoint _,
      Scheme.fromSpecResidueField_apply z _⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (y ≫ π)
  have hinj : Function.Injective φ.hom := by
    rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
    intro a ha
    have h1 : Spec.map φ o = genericPoint (Sp R) := by rw [hφ, Scheme.Hom.comp_apply, hy, hz]
    rw [genericPoint_eq_bot_of_affine] at h1
    have h2 : a ∈ (Spec.map φ o).asIdeal := by
      change φ.hom a ∈ o.asIdeal
      rw [RingHom.mem_ker.mp ha]; exact zero_mem _
    rw [h1] at h2
    exact h2
  let io : FractionRing R →+* Ω := IsFractionRing.lift hinj
  have hio : spMap (io.comp (algebraMap R (FractionRing R))) = y ≫ π := by
    rw [← hφ, show io.comp (algebraMap R (FractionRing R)) = φ.hom from
      RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a]
    rfl
  have hio' : spMap io ≫ spMap (algebraMap R (FractionRing R)) = y ≫ π := by
    rw [← hio, ← Spec.map_comp]; rfl
  let w : Over.mk (spMap (io.comp (algebraMap R (FractionRing R))) ≫ x) ⟶ t.G :=
    (Over.homMk y (by rw [hio]; simp) : _ ⟶ Over.mk (π ≫ x)) ≫ κ
  have hw : w ^ q = 1 := h.pow_eq_one w y rfl
  obtain ⟨w₀, hw₀⟩ := hs Ω io w hw
  have := epi_spMap io
  have h0 : w₀ ≫ t.G.hom = spMap (algebraMap R (FractionRing R)) ≫ x := by
    rw [← cancel_epi (spMap io), reassoc_of% hw₀, reassoc_of% hio', Over.w w, ← Category.assoc, ← hio]; rfl
  let w₁ : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ x) ⟶ t.G := Over.homMk w₀ h0
  let i : Over.mk (spMap (io.comp (algebraMap R (FractionRing R))) ≫ x) ⟶
      Over.mk (spMap (algebraMap R (FractionRing R)) ≫ x) := Over.homMk (spMap io) (by
    rw [hio]; simp [reassoc_of% hio'])
  have hi : i ≫ w₁ = w := Over.OverMorphism.ext hw₀
  have hw₁ : w₁ ^ q = 1 := by
    have : i ≫ w₁ ^ q = i ≫ 1 := by rw [MonObj.comp_pow, hi, hw, MonObj.comp_one]
    exact Over.OverMorphism.ext ((cancel_epi (spMap io)).mp (congrArg Over.Hom.left this))
  obtain ⟨g₀, hg₀, hg₀'⟩ := h.lift _ w₁ (spMap (algebraMap R (FractionRing R))) rfl hw₁
  have e : spMap io ≫ g₀ = y := h.ext _ _ _ ((Category.assoc _ _ _).trans ((congrArg (spMap io ≫ ·) hg₀).trans hio'))
    ((Category.assoc _ _ _).trans ((congrArg (spMap io ≫ ·) hg₀').trans hw₀))
  exact ⟨g₀, hg₀, spMap io o, (congrArg (fun g : Sp Ω ⟶ Z => g o) e).trans hy⟩

theorem IsTorsionOver.thru_iff {E : Type} [Field E] [NumberField E] [IsCMField E]
    {Ho : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (t : SAB Ho X) {κ : Over.mk (π ≫ x) ⟶ t.G} (h : IsTorsionOver t.G x q π κ)
    {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (a : Sp A ⟶ S) [Mono a] (j : Sp B ⟶ Z) [IsOpenImmersion j]
    (hj : j ≫ π = spMap (algebraMap A B) ≫ a) (H : Z.Opens) (hr : Set.range j = (H : Set Z) ∩ π ⁻¹' Set.range a)
    {T : Type} [CommRing T] (φ : A →+* T) (z : Sp T ⟶ Z) (hz : z ≫ π = spMap φ ≫ a) :
    Thru t (j ≫ κ.left) φ (z ≫ κ.left) ↔ ∀ s, z s ∈ H := by
  constructor
  · rintro ⟨β, rfl, hβ⟩ s
    have e : spMap β ≫ j = z := h.ext _ _ _ (by
      rw [Category.assoc, hj, hz, ← Spec.map_comp_assoc]; rfl) ((Category.assoc _ _ _).trans hβ)
    exact (hr.subset ⟨spMap β s, congrArg (fun g : Sp T ⟶ Z => g s) e⟩).1
  · intro hs
    have r : Set.range z ⊆ Set.range j := by
      rintro _ ⟨s, rfl⟩
      exact hr.superset ⟨hs s, spMap φ s, (congrArg (fun g : Sp T ⟶ S => g s) hz).symm⟩
    obtain ⟨β, hβ⟩ := Spec.map_surjective (IsOpenImmersion.lift j z r)
    have e : Spec.map β ≫ j = z := by rw [hβ, IsOpenImmersion.lift_fac]
    refine ⟨β.hom, ?_, (Category.assoc _ _ _).symm.trans (congrArg (· ≫ κ.left) e)⟩
    have e' : Spec.map β ≫ spMap (algebraMap A B) = spMap φ := by
      rw [← cancel_mono a, Category.assoc, ← hj, reassoc_of% e, hz]
    rw [← Spec.map_comp] at e'
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e')

theorem IsTorsionOver.isFinPart {E : Type} [Field E] [NumberField E] [IsCMField E]
    {Ho : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (t : SAB Ho X) {κ : Over.mk (π ≫ x) ⟶ t.G} (h : IsTorsionOver t.G x q π κ)
    [AlgebraicGeometry.IsReduced Z] {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    [Module.Free A B] (a : Sp A ⟶ S) [Mono a] (j : Sp B ⟶ Z) [IsOpenImmersion j]
    (hj : j ≫ π = spMap (algebraMap A B) ≫ a) (H : Z.Opens) (hr : Set.range j = (H : Set Z) ∩ π ⁻¹' Set.range a)
    (W W₁ W₂ : S.Opens) (hW : ∀ y, a y ∈ W) (hW₁ : ∀ y, a y ∈ W₁) (hW₂ : ∀ y, a y ∈ W₂)
    (hsec : ∀ z ∈ H, ∃ s : W.toScheme ⟶ Z, s ≫ π = W.ι ∧ (∀ w, s w ∈ H) ∧ z ∈ Set.range s)
    (hone : ∀ (T : Over X) (z : T.left ⟶ Z), z ≫ κ.left = (1 : T ⟶ t.G).left → ∀ s, π (z s) ∈ W₁ → z s ∈ H)
    (hmul : ∀ (T : Over X) (w w' : T ⟶ t.G)
      (z z' z'' : T.left ⟶ Z), z ≫ κ.left = w.left → z' ≫ κ.left = w'.left → z'' ≫ κ.left = (w * w').left →
      z' ≫ π = z ≫ π → z'' ≫ π = z ≫ π → (∀ s, z s ∈ H) → (∀ s, z' s ∈ H) → ∀ s, π (z s) ∈ W₂ → z'' s ∈ H)
    (u : Over.mk (spMap (algebraMap A B) ≫ a ≫ x) ⟶ t.G) (hu : u.left = j ≫ κ.left) :
    IsFinPart t (a ≫ x) q u := by
  have hin : ∀ {T : Type} [CommRing T] (φ : A →+* T) (z : Sp T ⟶ Z), z ≫ π = spMap φ ≫ a → ∀ s,
      π (z s) = a (spMap φ s) := fun φ z hz s => congrArg (fun g : _ ⟶ S => g s) hz
  have hsect : ∀ (k : Type) [Field k] (β : B →+* k),
      ∃ σ : B →ₐ[A] A, β = (β.comp (algebraMap A B)).comp σ.toRingHom := fun k _ β => by
    let o : Sp k := IsLocalRing.closedPoint k
    obtain ⟨hz, y, hy⟩ := hr.subset ⟨spMap β o, rfl⟩
    obtain ⟨s, hs, hsH, w, hw⟩ := hsec _ hz
    have r : Set.range a ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]; rintro _ ⟨y, rfl⟩; exact hW y
    have f := IsOpenImmersion.lift_fac W.ι a r
    have hz' : (IsOpenImmersion.lift W.ι a r ≫ s) ≫ π = spMap (RingHom.id A) ≫ a := by
      rw [Category.assoc, hs, f]
      exact (Category.id_comp a).symm.trans (congrArg (· ≫ a) (Spec.map_id _).symm)
    obtain ⟨σ, hσ, hσ'⟩ := (h.thru_iff t a j hj H hr _ _ hz').mpr fun y => hsH _
    have e : spMap σ ≫ j = IsOpenImmersion.lift W.ι a r ≫ s := h.ext _ _ _ (by
      rw [Category.assoc, hj, hz', ← hσ, ← Spec.map_comp_assoc]; rfl) ((Category.assoc _ _ _).trans hσ')
    refine ⟨{ σ with commutes' := fun c => congrArg (fun g : A →+* A => g c) hσ }, eq_comp_section β _ o ⟨y, ?_⟩⟩
    apply j.isOpenEmbedding.injective
    refine (congrArg (fun g : Sp A ⟶ Z => g y) e).trans ?_
    rw [← hw, Scheme.Hom.comp_apply]
    congr 1
    apply W.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, f, hy, ← hw, ← Scheme.Hom.comp_apply, hs]
  refine ⟨‹_›, ‹_›, h.pow_eq_one u j hu.symm, fun T _ β β' e e' => ?_, fun T _ φ w hw hm => ?_, fun T _ φ => ?_,
    fun T _ φ w w' hw hw' => ?_, hsect, fun b hb => ?_⟩
  · have e₁ : spMap β ≫ j = spMap β' ≫ j := h.ext _ _ _ (by
      rw [Category.assoc, Category.assoc, hj, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
      exact congrArg (fun g => spMap g ≫ a) e) (by
        rw [Category.assoc, Category.assoc, ← hu]; exact e')
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono j).mp e₁))
  · obtain ⟨z, hz, hz'⟩ := h.lift _ w (spMap φ ≫ a) (Category.assoc _ _ _) hw
    rw [hu, ← hz']
    refine (h.thru_iff t a j hj H hr φ z hz).mpr (mem_of_forall_maximal (z ⁻¹ᵁ H) fun 𝔪 h𝔪 => ?_)
    have h1 := hm 𝔪 h𝔪
    rw [hu, ← hz'] at h1
    exact (h.thru_iff t a j hj H hr ((Ideal.Quotient.mk 𝔪).comp φ) (spMap (Ideal.Quotient.mk 𝔪) ≫ z) (by
      rw [Category.assoc]
      refine (congrArg (spMap (Ideal.Quotient.mk 𝔪) ≫ ·) hz).trans ?_
      rw [← Spec.map_comp_assoc]; rfl)).mp h1
  · obtain ⟨z, hz, hz'⟩ := h.lift (Over.mk (spMap φ ≫ a ≫ x)) 1 (spMap φ ≫ a) (Category.assoc _ _ _) (one_pow _)
    rw [hu, ← hz']
    exact (h.thru_iff t a j hj H hr φ z hz).mpr fun s => hone _ z hz' s ((hin φ z hz s).symm ▸ hW₁ _)
  · have hq : ∀ v : Over.mk (spMap φ ≫ a ≫ x) ⟶ t.G, Thru t u.left φ v.left → v ^ q = 1 := by
      rintro v ⟨β, -, hβ⟩
      exact h.pow_eq_one v (spMap β ≫ j) (by rw [← hβ, hu]; exact Category.assoc _ _ _)
    obtain ⟨z, hz, hz₁⟩ := h.lift _ w (spMap φ ≫ a) (Category.assoc _ _ _) (hq w hw)
    obtain ⟨z', hz', hz₂⟩ := h.lift _ w' (spMap φ ≫ a) (Category.assoc _ _ _) (hq w' hw')
    obtain ⟨z'', hz'', hz₃⟩ := h.lift _ (w * w') (spMap φ ≫ a) (Category.assoc _ _ _)
      (by rw [mul_pow, hq w hw, hq w' hw', _root_.mul_one])
    rw [hu, ← hz₁] at hw
    rw [hu, ← hz₂] at hw'
    rw [hu, ← hz₃]
    exact (h.thru_iff t a j hj H hr φ z'' hz'').mpr fun s => hmul _ w w' z z' z'' hz₁ hz₂ hz₃ (hz'.trans hz.symm)
      (hz''.trans hz.symm) ((h.thru_iff t a j hj H hr φ z hz).mp hw) ((h.thru_iff t a j hj H hr φ z' hz').mp hw') s
      ((hin φ z hz s).symm ▸ hW₂ _)
  · have : _root_.IsReduced B := (affine_isReduced_iff (CommRingCat.of B)).mp (isReduced_of_isOpenImmersion j)
    refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.mpr fun J hJ => ?_)
    obtain ⟨σ, hσ⟩ := hsect J.ResidueField (algebraMap B J.ResidueField)
    rw [← Ideal.algebraMap_residueField_eq_zero, hσ]
    simp [hb σ]

theorem exists_finite_part : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CharZero R] (x : Sp R ⟶ X) (q : ℕ), q ≠ 0 → SplitTors t x q → ∀ 𝔭 : Ideal R, 𝔭.IsPrime → ∃ (f : R) (B : Type) (_ : CommRing B) (_ : Algebra (Localization.Away f) B) (u : Over.mk (spMap (algebraMap (Localization.Away f) B) ≫ spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ t.G), f ∉ 𝔭 ∧ IsFinPart t (spMap (algebraMap R (Localization.Away f)) ≫ x) q u ∧ ∀ (k : Type) [Field k] (φ : Localization.Away f →+* k), RingHom.ker (φ.comp (algebraMap R (Localization.Away f))) = 𝔭 → ∀ w : Over.mk (spMap φ ≫ spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ t.G, w ^ q = 1 → Thru t u.left φ w.left := by
  intro E _ _ _ Ho X _ t R _ _ _ _ x q hq hs 𝔭 h𝔭
  have := t.semi.smooth
  have := t.semi.separated
  have := t.semi.quasiCompact
  obtain ⟨_, _⟩ := GlobalTheory.T.torsion_flat_locallyQuasiFinite X t.G t.semi q hq
  have hcl : IsClosedImmersion η[t.G].left := by
    have : IsClosedImmersion (η[t.G].left ≫ t.G.hom) := by
      rw [Over.w]; exact inferInstanceAs (IsClosedImmersion (𝟙 X))
    exact IsClosedImmersion.of_comp _ t.G.hom
  have : IsClosedImmersion (torsion.ι t.G q).left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (GrpTangent.isPullback_torsion t.G q).flip hcl
  have : IsSeparated (torsion t.G q).hom := by rw [← Over.w (torsion.ι t.G q)]; infer_instance
  have : QuasiCompact (torsion t.G q).hom := by rw [← Over.w (torsion.ι t.G q)]; infer_instance
  have : LocallyOfFiniteType (torsion t.G q).hom := by rw [← Over.w (torsion.ι t.G q)]; infer_instance
  have : LocallyOfFinitePresentation (torsion t.G q).hom := inferInstance
  have hred : IsReduced (pullback (torsion t.G q).hom x) := by
    have hu : IsUnit (q : Γ(Sp (FractionRing R), ⊤)) := by
      have h0 : (q : FractionRing R) ≠ 0 := by
        rw [← map_natCast (algebraMap R (FractionRing R))]
        exact fun h => Nat.cast_ne_zero.mpr hq ((map_eq_zero_iff _ (IsFractionRing.injective R _)).mp h)
      simpa using h0.isUnit.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
    have : Etale (pullback.snd (torsion t.G q).hom (spMap (algebraMap R (FractionRing R)) ≫ x)) :=
      LamF.etale_pullback_torsion _ t.G hu
    have := GlobalTheory.isReduced_of_smooth_of_isReduced
      (pullback.snd (torsion t.G q).hom (spMap (algebraMap R (FractionRing R)) ≫ x))
    have := isReduced_of_isOpenImmersion
      (pullbackLeftPullbackSndIso (torsion t.G q).hom x (spMap (algebraMap R (FractionRing R)))).hom
    exact isReduced_of_generic (K := FractionRing R) (pullback.snd (torsion t.G q).hom x)
  have h := isTorsionOver t.G x q
  let p : PrimeSpectrum R := ⟨𝔭, h𝔭⟩
  obtain ⟨W, H, ρ, hpW, hρ, _, hH, hsec⟩ := exists_finite_open (K := FractionRing R)
    (pullback.snd (torsion t.G q).hom x) (h.exists_rational t hs) p
  obtain ⟨W₁, hW₁, hone⟩ := h.exists_open_one p H hH
  obtain ⟨W₂, hW₂, hmul⟩ := h.exists_open_mul p W H ρ hpW hρ hH
  obtain ⟨f, B, _, _, j, hf, hfin, hfree, _, hj, hsub, hr⟩ :=
    exists_free_chart (pullback.snd (torsion t.G q).hom x) p W (W₁ ⊓ W₂) H ρ hpW ⟨hW₁, hW₂⟩ hρ
  have : IsOpenImmersion (spMap (algebraMap R (Localization.Away f))) := IsOpenImmersion.of_isLocalization f
  let u₀ : Over.mk (spMap (algebraMap (Localization.Away f) B) ≫ spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶
      Over.mk (pullback.snd (torsion t.G q).hom x ≫ x) := Over.homMk j (by simp [reassoc_of% hj])
  refine ⟨f, B, inferInstance, inferInstance, u₀ ≫ _, hf, h.isFinPart t _ j hj H hr W W₁ W₂
    (fun y => (hsub ⟨y, rfl⟩).1) (fun y => (hsub ⟨y, rfl⟩).2.1) (fun y => (hsub ⟨y, rfl⟩).2.2) hsec hone hmul _ rfl,
    fun k _ φ hφ w hw => ?_⟩
  obtain ⟨z, hz, hz'⟩ := h.lift _ w (spMap φ ≫ spMap (algebraMap R (Localization.Away f))) (Category.assoc _ _ _) hw
  rw [← hz']
  refine (h.thru_iff t _ j hj H hr φ z hz).mpr fun s => hH _ ?_
  refine (congrArg (fun g : Sp k ⟶ Sp R => g s) hz).trans (PrimeSpectrum.ext ?_)
  change Ideal.comap (algebraMap R (Localization.Away f)) (Ideal.comap φ s.asIdeal) = 𝔭
  rw [Ideal.eq_bot_of_prime s.asIdeal (h := s.isPrime), Ideal.comap_comap, ← hφ]
  rfl

end GlobalTheory.SplitFinitePart
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_finite_torsion_splitting : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CharZero R] (x : Sp R ⟶ X) (q : ℕ), q ≠ 0 → SplitTors t x q → ∀ 𝔭 : Ideal R, 𝔭.IsPrime → ∃ (f : R) (B : Type) (_ : CommRing B) (_ : Algebra (Localization.Away f) B) (u : Over.mk (spMap (algebraMap (Localization.Away f) B) ≫ spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ t.G), f ∉ 𝔭 ∧ IsFinPart t (spMap (algebraMap R (Localization.Away f)) ≫ x) q u ∧ ∀ (k : Type) [Field k] (φ : Localization.Away f →+* k), RingHom.ker (φ.comp (algebraMap R (Localization.Away f))) = 𝔭 → ∀ w : Over.mk (spMap φ ≫ spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ t.G, w ^ q = 1 → Thru t u.left φ w.left := by
  atlas_forward_decl GlobalTheory.SplitFinitePart.exists_finite_part
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitTors_algClosed_fraction_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (R : Type) [CommRing R] [IsDomain R] [IsAlgClosed (FractionRing R)] (x : Sp R ⟶ X) (q : ℕ), q ≠ 0 → SplitTors t x q := by
  first | exact @GlobalTheory.LineNorm.splitTors_of_isAlgClosed | exact GlobalTheory.LineNorm.splitTors_of_isAlgClosed | (intros; apply GlobalTheory.LineNorm.splitTors_of_isAlgClosed <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj

namespace GlobalTheory.CharUniq

attribute [local instance] Over.cartesianMonoidalCategory

theorem spc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

theorem exists_restr {T T' : Scheme.{0}} (g : T' ⟶ T) (p : T ⟶ X) (p' : T' ⟶ X) (h : g ≫ p = p') :
    ∃ r : (Over.mk p ⟶ t.G) →* (Over.mk p' ⟶ t.G), ∀ w, (r w).left = g ≫ w.left := by
  let δ : Over.mk p' ⟶ Over.mk p := Over.homMk g h
  exact ⟨{ toFun := fun w => δ ≫ w, map_one' := by simp, map_mul' := fun a b => comp_mul _ _ _ }, fun w => rfl⟩

theorem isFinPart_of_equiv {R L B : Type} [CommRing R] [CommRing L] [CommRing B] [Algebra R B] [Algebra L B]
    (e : R ≃+* L) (he : (algebraMap L B).comp e.toRingHom = algebraMap R B) (x : Sp R ⟶ X) (q : ℕ)
    (u : Over.mk (spMap (algebraMap L B) ≫ spMap e.toRingHom ≫ x) ⟶ t.G)
    (u' : Over.mk (spMap (algebraMap R B) ≫ x) ⟶ t.G) (hu : u'.left = u.left)
    (h : IsFinPart t (spMap e.toRingHom ≫ x) q u) : IsFinPart t x q u' := by
  have he' : (algebraMap R B).comp e.symm.toRingHom = algebraMap L B := by
    rw [← he]; ext a; simp
  have th : ∀ (S : Type) [CommRing S] (φ : R →+* S) (w : Sp S ⟶ t.G.left),
      Thru t u'.left φ w ↔ Thru t u.left (φ.comp e.symm.toRingHom) w := by
    intro S _ φ w
    rw [hu]
    refine exists_congr fun β => and_congr_left fun _ => ⟨fun a => ?_, fun a => ?_⟩
    · rw [← a, RingHom.comp_assoc, he']
    · rw [← he, ← RingHom.comp_assoc, a]; ext b; simp
  have tr : ∀ (S : Type) [CommRing S] (φ : R →+* S),
      ∃ r : (Over.mk (spMap φ ≫ x) ⟶ t.G) →* (Over.mk (spMap (φ.comp e.symm.toRingHom) ≫ spMap e.toRingHom ≫ x) ⟶ t.G),
        ∀ w, (r w).left = w.left := by
    intro S _ φ
    obtain ⟨r, hr⟩ := exists_restr t (𝟙 _) (spMap φ ≫ x)
      (spMap (φ.comp e.symm.toRingHom) ≫ spMap e.toRingHom ≫ x) (by
        rw [Category.id_comp, ← Category.assoc, spc]
        congr 2; ext b; simp)
    exact ⟨r, fun w => (hr w).trans (Category.id_comp _)⟩
  letI : Algebra R L := e.toRingHom.toAlgebra
  haveI : IsScalarTower R L B := IsScalarTower.of_algebraMap_eq' he.symm
  let e' : R ≃ₐ[R] L := AlgEquiv.ofRingEquiv (f := e) fun _ => rfl
  haveI := h.finite
  haveI := h.free
  haveI : Module.Finite R L := Module.Finite.equiv e'.toLinearEquiv
  haveI : Module.Free R L := Module.Free.of_equiv e'.toLinearEquiv
  refine ⟨Module.Finite.trans L B, Module.Free.trans (S := L), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨r, hr⟩ := exists_restr t (𝟙 _) (spMap (algebraMap L B) ≫ spMap e.toRingHom ≫ x)
      (spMap (algebraMap R B) ≫ x) (by rw [Category.id_comp, ← Category.assoc, spc, he])
    have : u' = r u := Over.OverMorphism.ext (by rw [hr, hu]; exact (Category.id_comp _).symm)
    rw [this, ← map_pow, h.tors, map_one]
  · intro S _ β β' h1 h2
    refine h.mono S β β' (by rw [← he', ← RingHom.comp_assoc, h1, RingHom.comp_assoc]) (by rw [← hu]; exact h2)
  · intro S _ φ w hw hm
    obtain ⟨r, hr⟩ := tr S φ
    rw [th, ← hr]
    refine h.isOpen S _ (r w) (by rw [← map_pow, hw, map_one]) fun 𝔪 h𝔪 => ?_
    rw [hr]
    exact (th _ _ _).1 (hm 𝔪 h𝔪)
  · intro S _ φ
    obtain ⟨r, hr⟩ := tr S φ
    rw [th, ← hr, map_one]
    exact h.one S _
  · intro S _ φ w w' h1 h2
    obtain ⟨r, hr⟩ := tr S φ
    rw [th, ← hr] at h1 h2 ⊢
    rw [map_mul]
    exact h.mul S _ _ _ h1 h2
  · intro k _ β
    obtain ⟨σ, hσ⟩ := h.sect k β
    refine ⟨e'.symm.toAlgHom.comp (σ.restrictScalars R), hσ.trans ?_⟩
    rw [← he']
    rfl
  · intro b hb
    refine h.inj b fun σ => ?_
    have := hb (e'.symm.toAlgHom.comp (σ.restrictScalars R))
    exact e'.symm.injective (this.trans (map_zero _).symm)

theorem exists_finPart_local [IsLocallyNoetherian X] (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CharZero R] [IsLocalRing R] (x : Sp R ⟶ X) (q : ℕ) (hq : q ≠ 0) (hs : SplitTors t x q) :
    ∃ (B₀ : Type) (_ : CommRing B₀) (_ : Algebra R B₀) (u : Over.mk (spMap (algebraMap R B₀) ≫ x) ⟶ t.G),
      IsFinPart t x q u ∧ ∀ (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B]
        (w : Over.mk (spMap (algebraMap R B) ≫ x) ⟶ t.G), w ^ q = 1 → Thru t u.left (algebraMap R B) w.left := by
  obtain ⟨f, B₀, _, _, u, hf, hu, hk⟩ := GlobalTheory.T.exists_local_finite_torsion_splitting E H X t R x q hq hs (IsLocalRing.maximalIdeal R) inferInstance
  have hfu : IsUnit f := by
    by_contra hn
    exact hf hn
  let e : R ≃+* Localization.Away f :=
    (IsLocalization.atUnits R (Submonoid.powers f) (S := Localization.Away f)
      ((Submonoid.powers_le).2 hfu)).toRingEquiv
  have hee : e.toRingHom = algebraMap R (Localization.Away f) := by
    ext a
    exact (IsLocalization.atUnits R (Submonoid.powers f) (S := Localization.Away f)
      ((Submonoid.powers_le).2 hfu)).commutes a
  letI : Algebra R B₀ := ((algebraMap (Localization.Away f) B₀).comp e.toRingHom).toAlgebra
  revert u
  rw [← hee]
  intro u hu hk
  obtain ⟨r, hr⟩ := exists_restr t (𝟙 _) (spMap (algebraMap (Localization.Away f) B₀) ≫ spMap e.toRingHom ≫ x)
    (spMap (algebraMap R B₀) ≫ x) (by rw [Category.id_comp, ← Category.assoc, spc])
  have hr' : (r u).left = u.left := (hr u).trans (Category.id_comp _)
  have hu' := isFinPart_of_equiv t e rfl x q u (r u) hr' hu
  refine ⟨B₀, inferInstance, inferInstance, r u, hu', fun B _ _ _ w hw => hu'.isOpen B _ w hw fun 𝔪 h𝔪 => ?_⟩
  letI := Ideal.Quotient.field 𝔪
  let φ : R →+* B ⧸ 𝔪 := (Ideal.Quotient.mk 𝔪).comp (algebraMap R B)
  have hφ : (φ.comp e.symm.toRingHom).comp e.toRingHom = φ := by ext a; simp
  obtain ⟨s, hs⟩ := exists_restr t (spMap (Ideal.Quotient.mk 𝔪)) (spMap (algebraMap R B) ≫ x)
    (spMap (φ.comp e.symm.toRingHom) ≫ spMap e.toRingHom ≫ x) (by
      rw [← Category.assoc, ← Category.assoc, spc, spc, hφ])
  obtain ⟨β, h1, h2⟩ := hk (B ⧸ 𝔪) (φ.comp e.symm.toRingHom) (by
    rw [hφ]
    have : (𝔪.comap (algebraMap R B)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔪
    rw [← IsLocalRing.eq_maximalIdeal this, ← RingHom.comap_ker, Ideal.mk_ker]) (s w)
    (by rw [← map_pow, hw, map_one])
  refine ⟨β, ?_, by rw [hr', h2, hs]⟩
  exact (congrArg (fun z => z.comp e.toRingHom) h1).trans hφ

theorem exists_finPart_int [IsLocallyNoetherian X] (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]
    [IsAlgClosed C] [CharZero C] (x : Sp ↥(intO C) ⟶ X) (q : ℕ) (hq : q ≠ 0) :
    ∃ (B₀ : Type) (_ : CommRing B₀) (_ : Algebra ↥(intO C) B₀)
      (u : Over.mk (spMap (algebraMap ↥(intO C) B₀) ≫ x) ⟶ t.G),
      IsFinPart t x q u ∧ ∀ (B : Type) [CommRing B] [Algebra ↥(intO C) B] [Module.Finite ↥(intO C) B]
        (w : Over.mk (spMap (algebraMap ↥(intO C) B) ≫ x) ⟶ t.G), w ^ q = 1 →
          Thru t u.left (algebraMap ↥(intO C) B) w.left := by
  haveI := GlobalTheory.IntegralPointCheck.valuationRing_intO C
  haveI := GlobalTheory.IntegralPointCheck.isFractionRing_intO C
  haveI : IsAlgClosed (FractionRing ↥(intO C)) :=
    IsAlgClosed.of_ringEquiv C _ (FractionRing.algEquiv ↥(intO C) C).symm.toRingEquiv
  exact exists_finPart_local t _ x q hq (GlobalTheory.T.splitTors_algClosed_fraction_field E H X t _ x q hq)

theorem char_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (x : Sp ↥(intO C) ⟶ X) (q : ℕ), q ≠ 0 → ∀ c c' : TorsChar t x q, (∀ w : Over.mk (spMap (algebraMap ↥(intO C) ↥(intO C)) ≫ x) ⟶ t.G, w ^ q = 1 → c.χ ↥(intO C) w = c'.χ ↥(intO C) w) → ∀ (B : Type) [CommRing B] [Algebra ↥(intO C) B] [Module.Finite ↥(intO C) B] (w : Over.mk (spMap (algebraMap ↥(intO C) B) ≫ x) ⟶ t.G), w ^ q = 1 → c.χ B w = c'.χ B w := by
  intro E _ _ _ H X _ t C _ _ _ _ x q hq c c' h B _ _ _ w hw
  obtain ⟨B₀, _, _, u, hu, hth⟩ := exists_finPart_int t C x q hq
  haveI := hu.finite
  have key : (c.χ B₀ u : B₀) = c'.χ B₀ u := by
    refine sub_eq_zero.1 (hu.inj _ fun σ => ?_)
    obtain ⟨r, hr⟩ := exists_restr t (spMap σ.toRingHom) (spMap (algebraMap ↥(intO C) B₀) ≫ x)
      (spMap (algebraMap ↥(intO C) ↥(intO C)) ≫ x) (by
        rw [← Category.assoc, spc]
        congr 2
        exact RingHom.ext fun a => σ.commutes a)
    rw [map_sub, ← c.nat B₀ _ σ u (r u) hu.tors (hr u), ← c'.nat B₀ _ σ u (r u) hu.tors (hr u),
      h (r u) (by rw [← map_pow, hu.tors, map_one]), sub_self]
  obtain ⟨β, h1, h2⟩ := hth B w hw
  let β' : B₀ →ₐ[↥(intO C)] B := { β with commutes' := fun a => RingHom.congr_fun h1 a }
  refine Units.ext ?_
  rw [c.nat B₀ B β' u w hu.tors h2.symm, c'.nat B₀ B β' u w hu.tors h2.symm, key]

end GlobalTheory.CharUniq
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionChar_eq_of_eq_on_torsion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (x : Sp ↥(intO C) ⟶ X) (q : ℕ), q ≠ 0 → ∀ c c' : TorsChar t x q, (∀ w : Over.mk (spMap (algebraMap ↥(intO C) ↥(intO C)) ≫ x) ⟶ t.G, w ^ q = 1 → c.χ ↥(intO C) w = c'.χ ↥(intO C) w) → ∀ (B : Type) [CommRing B] [Algebra ↥(intO C) B] [Module.Finite ↥(intO C) B] (w : Over.mk (spMap (algebraMap ↥(intO C) B) ≫ x) ⟶ t.G), w ^ q = 1 → c.χ B w = c'.χ B w := by
  first | exact @GlobalTheory.CharUniq.char_unique | exact GlobalTheory.CharUniq.char_unique | (intros; apply GlobalTheory.CharUniq.char_unique <;> assumption)
end
