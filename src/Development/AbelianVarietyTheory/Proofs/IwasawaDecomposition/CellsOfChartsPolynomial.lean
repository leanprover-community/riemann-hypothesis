import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineChartOfLeftInverseMatrix
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsClosedSubschemeOpenPieces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteNormalFlatClosure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNormalMvPolynomialOfIsNormal

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

noncomputable section

namespace GlobalTheory.GrCl

section CellsInP

open MvPolynomial
open GlobalTheory.ProjSpace (grading spMap_pt pt_str_assoc pt_baseChange pt_eq_pt_iff span_range_comp_eq_top exists_mem_chart
  pt_preimage_basicOpen isPullback_baseChange baseChange mem_spOpen)
open GlobalTheory.SplitCells (lin lin_hom)

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R S : Type} [CommRing R] [CommRing S] {N : ℕ} {ρ : R →+* S} {J : Type} {ξ : J → Fin (N + 1) → S}
  {ℓ : J → Fin (N + 1) → R}

theorem eval₂_lin' (a : Fin (N + 1) → R) (w : Fin (N + 1) → S) : eval₂ ρ w (lin a) = ∑ q, ρ (a q) * w q := by
  simp [lin, eval₂_sum]

theorem cell_immersion (hc : Cells ρ ξ ℓ) (j : J) (hv) :
    IsImmersion (pt ρ (ξ j) hv) ∧ ∃ T : Set (PSpace R N), IsClosed T ∧
      Set.range (pt ρ (ξ j) hv) = T ∩ (Proj.basicOpen (grading R N) (lin (ℓ j)) : Set (PSpace R N)) := by
  have h1 : eval₂Hom ρ (ξ j) (lin (ℓ j)) = 1 := by rw [coe_eval₂Hom, eval₂_lin', hc.one]
  have hu : IsUnit (eval₂Hom ρ (ξ j) (lin (ℓ j))) := h1 ▸ isUnit_one
  have hm : lin (ℓ j) ∈ grading R N 1 := lin_hom _
  have e : pt ρ (ξ j) hv = _ := ProjPoint.ofHom_eq_awayι _ _ _ one_pos hm hu
  have hs : Function.Surjective (ProjPoint.awayLift (grading R N) (eval₂Hom ρ (ξ j)) _ hu) := by
    intro p
    obtain ⟨F, rfl⟩ := hc.gen j p
    change _ ∈ (ProjPoint.awayLift (grading R N) (eval₂Hom ρ (ξ j)) _ hu).range
    induction F using MvPolynomial.induction_on with
    | C a =>
      have := ProjPoint.awayLift_mk_mul (grading R N) _ hu hm 0 (C a) (isHomogeneous_C _ a)
      rw [pow_zero, mul_one] at this
      exact ⟨_, this⟩
    | add F G hF hG => rw [map_add]; exact add_mem hF hG
    | mul_X F k hF =>
      rw [map_mul]
      refine mul_mem hF ?_
      have := ProjPoint.awayLift_mk_mul (grading R N) _ hu hm 1 (X k) (isHomogeneous_X R k)
      rw [h1, one_pow, mul_one] at this
      exact ⟨_, this⟩
  have hcl : IsClosedImmersion (Spec.map (CommRingCat.ofHom (ProjPoint.awayLift (grading R N) _ _ hu))) :=
    IsClosedImmersion.spec_of_surjective _ hs
  refine ⟨by rw [e]; infer_instance, ?_⟩
  obtain ⟨T, hT, hT'⟩ := (Proj.awayι (grading R N) _ hm one_pos).isOpenEmbedding.isInducing.isClosed_iff.1
    (Spec.map (CommRingCat.ofHom (ProjPoint.awayLift (grading R N) _ _ hu))).isClosedEmbedding.isClosed_range
  refine ⟨T, hT, ?_⟩
  have hr : Set.range (Proj.awayι (grading R N) _ hm one_pos) = Proj.basicOpen (grading R N) (lin (ℓ j)) :=
    congrArg (fun U : (PSpace R N).Opens => (U : Set (PSpace R N))) (Proj.opensRange_awayι _ _ hm one_pos)
  rw [e, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ← hT', Set.image_preimage_eq_inter_range, hr]

theorem cell_overlap (hc : Cells ρ ξ ℓ) (hv : ∀ j, Ideal.span (Set.range (ξ j)) = ⊤) {j j' : J} {x : PSpace R N}
    (hx : x ∈ Set.range (pt ρ (ξ j') (hv j'))) (h : x ∈ Proj.basicOpen (grading R N) (lin (ℓ j))) :
    x ∈ Set.range (pt ρ (ξ j) (hv j)) := by
  obtain ⟨y, rfl⟩ := hx
  have hy : y.asIdeal.IsPrime := y.isPrime
  let K : Type := y.asIdeal.ResidueField
  let ψ' : S →+* K := algebraMap S K
  have h2 : eval₂ ρ (ξ j') (lin (ℓ j)) ∉ y.asIdeal := by
    rw [← mem_spOpen, ← pt_preimage_basicOpen ρ (ξ j') (hv j') one_pos (lin_hom _)]
    exact h
  have h3 : ∑ q, ψ' (ρ (ℓ j q)) * ψ' (ξ j' q) ≠ 0 := by
    intro h0
    apply h2
    rw [eval₂_lin', ← Ideal.algebraMap_residueField_eq_zero, map_sum]
    simpa only [map_mul] using h0
  obtain ⟨ψ, u, hb, hu⟩ := hc.ovl K j j' ψ' h3
  let z : Sp K := IsLocalRing.closedPoint K
  have hz : spMap ψ' z = y := by
    refine PrimeSpectrum.ext ?_
    change Ideal.comap ψ' (IsLocalRing.maximalIdeal K) = y.asIdeal
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
    exact Ideal.ker_algebraMap_residueField _
  have e : spMap ψ ≫ pt ρ (ξ j) (hv j) = spMap ψ' ≫ pt ρ (ξ j') (hv j') := by
    rw [spMap_pt, spMap_pt, hb]
    exact (pt_eq_pt_iff _ _ _).2 ⟨u, hu⟩
  refine ⟨spMap ψ z, ?_⟩
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, hz]

theorem isClosed_iUnion_cell (hc : Cells ρ ξ ℓ) (hv : ∀ j, Ideal.span (Set.range (ξ j)) = ⊤) :
    IsClosed (⋃ j, Set.range (pt ρ (ξ j) (hv j))) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  by_cases h : ∃ j, y ∈ Proj.basicOpen (grading R N) (lin (ℓ j))
  · obtain ⟨j, hj⟩ := h
    obtain ⟨T, hT, e⟩ := (cell_immersion hc j (hv j)).2
    have hyT : y ∉ T := fun h' => hy (Set.mem_iUnion.2 ⟨j, e ▸ ⟨h', hj⟩⟩)
    refine Filter.mem_of_superset
      ((hT.isOpen_compl.inter (Proj.basicOpen (grading R N) (lin (ℓ j))).isOpen).mem_nhds ⟨hyT, hj⟩) ?_
    rintro z ⟨h1, h2⟩ hz
    obtain ⟨j', hz⟩ := Set.mem_iUnion.1 hz
    have := cell_overlap hc hv hz h2
    rw [e] at this
    exact h1 this.1
  · push_neg at h
    obtain ⟨q, hq⟩ := exists_mem_chart R N y
    obtain ⟨T, _, jj, a, ha⟩ := hc.lin q
    let F : MvPolynomial (Fin (N + 1)) R := X q - ∑ t, C (a t) * lin (ℓ (jj t))
    have hF : F.IsHomogeneous 1 := by
      refine (isHomogeneous_X R q).sub (IsHomogeneous.sum _ _ _ fun t _ => ?_)
      simpa using (isHomogeneous_C _ (a t)).mul (lin_hom (ℓ (jj t)))
    have hyF : y ∈ Proj.basicOpen (grading R N) F := by
      intro hmem
      refine hq ?_
      have h4 : ∑ t, C (a t) * lin (ℓ (jj t)) ∈ y.asHomogeneousIdeal :=
        sum_mem fun t _ => Ideal.mul_mem_left _ _ (not_not.1 (h (jj t)))
      have := add_mem hmem h4
      simpa [F] using this
    refine Filter.mem_of_superset ((Proj.basicOpen (grading R N) F).isOpen.mem_nhds hyF) ?_
    intro z hz hz'
    obtain ⟨j', w, rfl⟩ := Set.mem_iUnion.1 hz'
    have h5 : w ∈ pt ρ (ξ j') (hv j') ⁻¹ᵁ Proj.basicOpen (grading R N) F := hz
    rw [pt_preimage_basicOpen ρ (ξ j') (hv j') one_pos hF, mem_spOpen] at h5
    refine h5 ?_
    have h6 : eval₂ ρ (ξ j') F = 0 := by
      simp only [F, eval₂_sub, eval₂_X, eval₂_sum, eval₂_mul, eval₂_C, eval₂_lin']
      rw [ha j']
      simp
    rw [h6]
    exact zero_mem _

theorem cells_immersed : ∀ (O : Type) [CommRing O] (Z P : Scheme.{0}) (s : Z ⟶ Sp O) (N : ℕ) (p₁ : P ⟶ Z) (p₂ : P ⟶ PSpace O N), IsPullback p₁ p₂ s (PSpace.str O N) → ∀ (R S : Type) [CommRing R] [CommRing S] (χ : Sp R ⟶ Z) (g : O →+* R) (ρ : R →+* S) (J : Type) (ξ : J → Fin (N + 1) → S) (ℓ : J → Fin (N + 1) → R) (i : J → (Sp S ⟶ P)), IsOpenImmersion χ → χ ≫ s = spMap g → Cells ρ ξ ℓ → (∀ j, i j ≫ p₁ = spMap ρ ≫ χ) → (∀ j, ∃ hv, i j ≫ p₂ = pt (ρ.comp g) (ξ j) hv) → (∀ j, IsImmersion (i j)) ∧ (∀ j, ∃ U : P.Opens, Set.range (i j) = (⋃ j', Set.range (i j')) ∩ (U : Set P)) ∧ ∃ T : Set P, IsClosed T ∧ ⋃ j, Set.range (i j) = T ∩ p₁ ⁻¹' Set.range χ := by
  intro O _ Z P s N p₁ p₂ hP R S _ _ χ g ρ J ξ ℓ i hχ hg hc hi₁ hi₂
  have hb := isPullback_baseChange N g
  rw [← hg] at hb
  let e : PSpace R N ⟶ P := hP.flip.lift (baseChange N g) (PSpace.str R N ≫ χ) (by rw [hb.w, Category.assoc])
  have he : IsPullback e (PSpace.str R N) p₁ χ := hb.of_right' hP.flip
  have he₂ : e ≫ p₂ = baseChange N g := hP.flip.lift_fst _ _ _
  have heo : IsOpenImmersion e := MorphismProperty.of_isPullback he.flip hχ
  have hr : Set.range e = p₁ ⁻¹' Set.range χ := by
    rw [← Scheme.Pullback.range_fst, ← he.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact he.isoPullback.hom.surjective.range_comp _
  choose hv hi₂ using hi₂
  have hj : ∀ j, i j = pt ρ (ξ j) (hv j) ≫ e := fun j =>
    hP.hom_ext (by rw [hi₁, Category.assoc, he.w, pt_str_assoc]) (by rw [hi₂, Category.assoc, he₂, pt_baseChange])
  have hm : ∀ j, Set.range (i j) = e '' Set.range (pt ρ (ξ j) (hv j)) := fun j => by
    rw [hj, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have hinj := e.isOpenEmbedding.injective
  refine ⟨fun j => ?_, fun j => ⟨e ''ᵁ Proj.basicOpen (grading R N) (lin (ℓ j)), Set.ext fun x => ?_⟩,
    (e '' (⋃ j, Set.range (pt ρ (ξ j) (hv j)))ᶜ)ᶜ,
    (e.isOpenEmbedding.isOpenMap _ (isClosed_iUnion_cell hc hv).isOpen_compl).isClosed_compl,
    Set.ext fun x => ?_⟩
  · have := (cell_immersion hc j (hv j)).1
    rw [hj]
    infer_instance
  · simp only [Set.mem_inter_iff, Set.mem_iUnion, hm]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨T, -, eT⟩ := (cell_immersion hc j (hv j)).2
      have hy₂ := hy
      rw [eT] at hy₂
      exact ⟨⟨j, y, hy, rfl⟩, y, hy₂.2, rfl⟩
    · rintro ⟨⟨j', y, hy, rfl⟩, y', hy', e'⟩
      obtain rfl := hinj e'
      exact ⟨y', cell_overlap hc hv hy hy', rfl⟩
  · simp only [Set.mem_inter_iff, Set.mem_iUnion, hm, ← hr]
    constructor
    · rintro ⟨j, y, hy, rfl⟩
      refine ⟨?_, y, rfl⟩
      rintro ⟨y', hy', e'⟩
      obtain rfl := hinj e'
      exact hy' (Set.mem_iUnion.2 ⟨j, hy⟩)
    · rintro ⟨hx, y, rfl⟩
      by_contra hn
      refine hx ⟨y, fun hy => hn ?_, rfl⟩
      obtain ⟨j, hy⟩ := Set.mem_iUnion.1 hy
      exact ⟨j, y, hy, rfl⟩

end CellsInP

end GlobalTheory.GrCl
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl

theorem spMap_comp_spMap_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem normal_stalk_iff {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    (IsDomain (Y.presheaf.stalk (f x)) ∧ IsIntegrallyClosed (Y.presheaf.stalk (f x))) ↔
      (IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)) := by
  let e := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  exact ⟨fun ⟨_, _⟩ => ⟨e.symm.toMulEquiv.isDomain _, .of_equiv e⟩,
    fun ⟨_, _⟩ => ⟨e.toMulEquiv.isDomain _, .of_equiv e.symm⟩⟩

theorem normal_sp_mvPolynomial {Z : Scheme.{0}} (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z) {R : Type} [CommRing R]
    (χ : Sp R ⟶ Z) [IsOpenImmersion χ] (V : Type) [Finite V] :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp (MvPolynomial V R)) := by
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin V
  have h := GlobalTheory.isNormalScheme_sp_mvPolynomial R r fun x => (normal_stalk_iff χ x).1 (hn _)
  let φ : CommRingCat.of (MvPolynomial (Fin r) R) ≅ CommRingCat.of (MvPolynomial V R) :=
    (MvPolynomial.renameEquiv R e.symm).toRingEquiv.toCommRingCatIso
  exact fun x => (normal_stalk_iff (Spec.map φ.hom) x).1 (h _)

theorem flat_spMap_C (R V : Type) [CommRing R] : Flat (spMap (MvPolynomial.C : R →+* MvPolynomial V R)) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact RingHom.flat_algebraMap_iff.2 (inferInstance : Module.Flat R (MvPolynomial V R))

theorem exists_spMap_fac {X : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S] (χ : Sp R ⟶ X) [IsOpenImmersion χ]
    (w : Sp S ⟶ X) (h : Set.range w ⊆ Set.range χ) : ∃ φ : R →+* S, spMap φ ≫ χ = w := by
  refine ⟨(Spec.preimage (IsOpenImmersion.lift χ w h)).hom, ?_⟩
  show Spec.map (Spec.preimage _) ≫ _ = _
  rw [Spec.map_preimage]
  exact IsOpenImmersion.lift_fac _ _ _

theorem iUnion_inter_chart {O : Type} [CommRing O] {Z P : Scheme.{0}} {s : Z ⟶ Sp O} {N : ℕ} {p₁ : P ⟶ Z}
    {p₂ : P ⟶ PSpace O N} (hP : IsPullback p₁ p₂ s (PSpace.str O N)) (ch : Charts Z) (g : ∀ a, O →+* ch.R a)
    {V J : Type} (ξ : ∀ a, J → Fin (N + 1) → MvPolynomial V (ch.R a)) (hg : ∀ a, ch.χ a ≫ s = spMap (g a))
    (hglue : ∀ (K : Type) [Field K] (a a' : ch.ι) (φ : ch.R a →+* K) (j' : J) (ψ' : MvPolynomial V (ch.R a') →+* K),
      spMap φ ≫ ch.χ a = spMap (ψ'.comp MvPolynomial.C) ≫ ch.χ a' →
        ∃ (j : J) (ψ : MvPolynomial V (ch.R a) →+* K) (u : Kˣ), ψ.comp MvPolynomial.C = φ ∧
          ψ' ∘ ξ a' j' = (u : K) • (ψ ∘ ξ a j))
    (i : ∀ k : ch.ι × J, Sp (MvPolynomial V (ch.R k.1)) ⟶ P)
    (h₁ : ∀ k, i k ≫ p₁ = spMap MvPolynomial.C ≫ ch.χ k.1)
    (h₂ : ∀ k, ∃ hv, i k ≫ p₂ = pt (MvPolynomial.C.comp (g k.1)) (ξ k.1 k.2) hv) (a : ch.ι) :
    (⋃ k, Set.range (i k)) ∩ p₁ ⁻¹' Set.range (ch.χ a) = ⋃ j, Set.range (i (a, j)) := by
  refine Set.Subset.antisymm ?_ (Set.iUnion_subset fun j => ?_)
  · rintro x ⟨hx, hxa⟩
    obtain ⟨⟨a', j'⟩, y, rfl⟩ := Set.mem_iUnion.1 hx
    have := y.isPrime
    let K := y.asIdeal.ResidueField
    let ψ' : MvPolynomial V (ch.R a') →+* K := algebraMap _ _
    have hy : ∀ t, spMap ψ' t = y := fun t => by
      refine PrimeSpectrum.ext ?_
      have ht : t.asIdeal = ⊥ := (Ideal.eq_bot_or_top _).resolve_right t.isPrime.ne_top
      change t.asIdeal.comap ψ' = _
      rw [ht]
      exact Ideal.ker_algebraMap_residueField _
    have e₁ : spMap (ψ'.comp MvPolynomial.C) ≫ ch.χ a' = (spMap ψ' ≫ i (a', j')) ≫ p₁ := by
      rw [Category.assoc, h₁, ← Category.assoc, spMap_comp_spMap_eq]
    obtain ⟨φ, hφ⟩ := exists_spMap_fac (ch.χ a) (spMap (ψ'.comp MvPolynomial.C) ≫ ch.χ a') (by
      rintro _ ⟨t, rfl⟩
      rw [e₁, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy]
      exact hxa)
    obtain ⟨j, ψ, u, hψ, hu⟩ := hglue K a a' φ j' ψ' hφ
    have hc : ψ.comp (MvPolynomial.C.comp (g a)) = ψ'.comp (MvPolynomial.C.comp (g a')) := by
      have := congrArg (· ≫ s) hφ
      simp only [Category.assoc, hg, spMap_comp_spMap_eq] at this
      rw [← RingHom.comp_assoc, hψ]
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
    have e : spMap ψ ≫ i (a, j) = spMap ψ' ≫ i (a', j') := by
      refine hP.hom_ext ?_ ?_
      · rw [← e₁, ← hφ, Category.assoc, h₁, ← Category.assoc, spMap_comp_spMap_eq, hψ]
      · obtain ⟨hv, e₂⟩ := h₂ (a, j)
        obtain ⟨hv', e₂'⟩ := h₂ (a', j')
        rw [Category.assoc, Category.assoc, e₂, e₂', ProjSpace.spMap_pt, ProjSpace.spMap_pt, hc]
        exact (ProjSpace.pt_eq_pt_iff _ _ _).2 ⟨u, hu⟩
    have t : Sp K := IsLocalRing.closedPoint K
    refine Set.mem_iUnion.2 ⟨j, spMap ψ t, ?_⟩
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, hy]
  · rintro _ ⟨y, rfl⟩
    refine ⟨Set.mem_iUnion.2 ⟨_, y, rfl⟩, spMap MvPolynomial.C y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h₁]

theorem exists_cellCl : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] (Z : Scheme.{0}) (s : Z ⟶ Sp O), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → Flat s → ∀ (ch : Charts Z) (g : ∀ a, O →+* ch.R a) (V J : Type) [Finite V] [Finite J] (N : ℕ) (ξ : ∀ a, J → Fin (N + 1) → MvPolynomial V (ch.R a)) (ℓ : ∀ a, J → Fin (N + 1) → ch.R a), (∀ a, ch.χ a ≫ s = spMap (g a)) → (∀ a, Cells (MvPolynomial.C : ch.R a →+* MvPolynomial V (ch.R a)) (ξ a) (ℓ a)) → (∀ (K : Type) [Field K] (a a' : ch.ι) (φ : ch.R a →+* K) (j' : J) (ψ' : MvPolynomial V (ch.R a') →+* K), spMap φ ≫ ch.χ a = spMap (ψ'.comp MvPolynomial.C) ≫ ch.χ a' → ∃ (j : J) (ψ : MvPolynomial V (ch.R a) →+* K) (u : Kˣ), ψ.comp MvPolynomial.C = φ ∧ ψ' ∘ ξ a' j' = (u : K) • (ψ ∘ ξ a j)) → ∃ (Z' : Scheme.{0}) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O N) (κ : ∀ a, J → (Sp (MvPolynomial V (ch.R a)) ⟶ Z')), CellCl s ch g ξ f q κ := by
  intro O _ _ _ Z s hproj hn hfl ch g V J _ _ N ξ ℓ hg hc hglue
  have hPp : IsProjOver (pullback.fst s (PSpace.str O N) ≫ s) :=
    ProjSpace.isProjOver_pullback hproj ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  have hP := IsPullback.of_hasPullback s (PSpace.str O N)
  generalize pullback.snd s (PSpace.str O N) = p₂ at hP
  generalize pullback.fst s (PSpace.str O N) = p₁ at hP hPp
  generalize pullback s (PSpace.str O N) = P at p₁ p₂ hP hPp
  have hv : ∀ a j, Ideal.span (Set.range (ξ a j)) = ⊤ := fun a j => by
    rw [Ideal.eq_top_iff_one, ← (hc a).one j]
    exact Ideal.sum_mem _ fun q _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨q, rfl⟩)
  let i : ∀ k : ch.ι × J, Sp (MvPolynomial V (ch.R k.1)) ⟶ P := fun k =>
    hP.lift (spMap MvPolynomial.C ≫ ch.χ k.1) (pt (MvPolynomial.C.comp (g k.1)) (ξ k.1 k.2) (hv _ _))
      (by rw [Category.assoc, hg, ProjSpace.pt_str, spMap_comp_spMap_eq])
  have h₁ : ∀ k, i k ≫ p₁ = spMap MvPolynomial.C ≫ ch.χ k.1 := fun k => hP.lift_fst _ _ _
  have h₂ : ∀ k, ∃ hv, i k ≫ p₂ = pt (MvPolynomial.C.comp (g k.1)) (ξ k.1 k.2) hv := fun k => ⟨_, hP.lift_snd _ _ _⟩
  have hmeet := iUnion_inter_chart hP ch g ξ hg hglue i h₁ h₂
  have hcell := fun a => GlobalTheory.GrCl.cells_immersed O Z P s N p₁ p₂ hP _ _ (ch.χ a) (g a) MvPolynomial.C J (ξ a) (ℓ a)
    (fun j => i (a, j)) inferInstance (hg a) (hc a) (fun j => h₁ (a, j)) (fun j => h₂ (a, j))
  have hnT := fun a => normal_sp_mvPolynomial hn (ch.χ a) V
  have hcar : IsOpen ch.carrier := isOpen_iUnion fun a => (ch.χ a).isOpenEmbedding.isOpen_range
  let Ω : P.Opens := ⟨p₁ ⁻¹' ch.carrier, hcar.preimage p₁.continuous⟩
  obtain ⟨U, j, e, hj, he, hej, hcov⟩ := GlobalTheory.ReducedUnion.exists_closed_union P (ch.ι × J)
    (fun k => Sp (MvPolynomial V (ch.R k.1))) i Ω (fun k => (hcell k.1).1 k.2)
    (fun k => by
      have := fun x => (hnT k.1 x).1
      exact isReduced_of_isReduced_stalk _)
    (fun k => by
      obtain ⟨W, hW⟩ := (hcell k.1).2.1 k.2
      refine ⟨p₁ ⁻¹ᵁ (ch.χ k.1).opensRange ⊓ W, ?_⟩
      rw [hW, ← hmeet, Set.inter_assoc]
      rfl)
    ⟨closure (⋃ k, Set.range (i k)), isClosed_closure, by
      refine Set.Subset.antisymm (Set.subset_inter subset_closure (Set.iUnion_subset fun k => ?_)) ?_
      · have : Set.range (i k) ⊆ ⋃ j, Set.range (i (k.1, j)) := Set.subset_iUnion (fun j => Set.range (i (k.1, j))) k.2
        rw [← hmeet] at this
        exact fun x hx => Set.mem_iUnion.2 ⟨k.1, (this hx).2⟩
      · rintro x ⟨hx, hxΩ⟩
        obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hxΩ
        obtain ⟨T, hT, eT⟩ := (hcell a).2.2
        have ho : IsOpen (p₁ ⁻¹' Set.range (ch.χ a)) := (ch.χ a).isOpenEmbedding.isOpen_range.preimage p₁.continuous
        have h3 := ho.closure_inter ⟨hx, ha⟩
        rw [hmeet, eT] at h3
        have h4 : x ∈ T ∩ p₁ ⁻¹' Set.range (ch.χ a) := ⟨closure_minimal Set.inter_subset_left hT h3, ha⟩
        rw [← eT, ← hmeet] at h4
        exact h4.1⟩
  have hcov' : ∀ x : U, ∃ k y, e k y = x := fun x => Set.mem_iUnion.1 (hcov.ge (Set.mem_univ x))
  have hnU : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme U := fun x => by
    obtain ⟨k, y, rfl⟩ := hcov' x
    exact (normal_stalk_iff (e k) y).2 (hnT k.1 y)
  have hfU : Flat (j ≫ Ω.ι ≫ p₁ ≫ s) := by
    have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat.{0})
    refine IsZariskiLocalAtSource.of_openCover (P := @Flat) (Scheme.Cover.mkOfCovers _ _ e hcov' he) fun k => ?_
    have := flat_spMap_C (ch.R k.1) V
    have e1 : e k ≫ j ≫ Ω.ι ≫ p₁ ≫ s = spMap MvPolynomial.C ≫ ch.χ k.1 ≫ s := by
      rw [← reassoc_of% h₁ k, ← hej k]
      simp only [Category.assoc]
    change Flat (e k ≫ j ≫ Ω.ι ≫ p₁ ≫ s)
    rw [e1]
    infer_instance
  obtain ⟨Z', ν, ε, hν, hnZ, hpZ, hfZ, hpb, hd⟩ :=
    GlobalTheory.GraphClosure.exists_normalisation_of_locallyClosed O P U (p₁ ≫ s) Ω j hPp hj hnU hfU
  have hε : IsOpenImmersion ε := MorphismProperty.of_isPullback hpb.flip inferInstance
  have hκ : ∀ k, (e k ≫ ε) ≫ ν = i k := fun k => by rw [Category.assoc, hpb.w, hej]
  have hr : Set.range ε = (ν ≫ p₁) ⁻¹' ch.carrier := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      have : ν (ε y) = Ω.ι (j y) := by rw [← Scheme.Hom.comp_apply, hpb.w, Scheme.Hom.comp_apply]
      change p₁ (ν (ε y)) ∈ ch.carrier
      rw [this]
      exact (j y).2
    · intro hx
      obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback hpb x ⟨ν x, hx⟩ rfl
      exact ⟨y, hy⟩
  refine ⟨Z', ν ≫ p₁, ν ≫ p₂, fun a l => e (a, l) ≫ ε, ?_, hnZ, ?_, ?_, fun a l => inferInstance, fun a l => ?_,
    fun a l => ?_, ?_, hr ▸ hd, fun K _ w w' hw e₁ e₂ => ?_, fun R K _ _ _ _ _ _ z y₀ y e₀ e₁ e₂ => ?_⟩
  · rwa [Category.assoc]
  · rwa [Category.assoc]
  · rw [Category.assoc, Category.assoc, hP.w]
  · rw [← Category.assoc, hκ, h₁]
  · rw [← Category.assoc, hκ]
    exact h₂ (a, l)
  · rw [← hr]
    refine Set.Subset.antisymm (Set.iUnion₂_subset ?_) ?_
    · rintro a l _ ⟨y, rfl⟩
      exact ⟨e (a, l) y, rfl⟩
    · rintro _ ⟨x, rfl⟩
      obtain ⟨⟨a, l⟩, y, rfl⟩ := hcov' x
      exact Set.mem_iUnion₂.2 ⟨a, l, y, rfl⟩
  · have key : ∀ v : Sp K ⟶ Z', Set.range (v ≫ ν ≫ p₁) ⊆ ch.carrier → ∃ v₀, v₀ ≫ ε = v := fun v hv =>
      ⟨IsOpenImmersion.lift ε v (by
        rintro _ ⟨t, rfl⟩
        rw [hr]
        exact hv ⟨t, rfl⟩), IsOpenImmersion.lift_fac _ _ _⟩
    have e₃ : w ≫ ν = w' ≫ ν := hP.hom_ext (by simpa only [Category.assoc] using e₁)
      (by simpa only [Category.assoc] using e₂)
    obtain ⟨v', rfl⟩ := key w' (e₁ ▸ hw)
    obtain ⟨v, rfl⟩ := key w hw
    rw [Category.assoc, Category.assoc, hpb.w] at e₃
    rw [(cancel_mono _).1 e₃]
  · obtain ⟨c, hc, -⟩ := (GlobalTheory.existsUnique_lift_spec_of_isLocalization (R' := K) (nonZeroDivisors R) le_rfl ν y
      (hP.lift z y₀ e₀.symm) (hP.hom_ext (by rw [Category.assoc, Category.assoc, hP.lift_fst, e₁])
        (by rw [Category.assoc, Category.assoc, hP.lift_snd, e₂]))).exists
    exact ⟨c, hc⟩

end GlobalTheory.GrCl
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cells_of_charts_polynomial : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] (Z : Scheme.{0}) (s : Z ⟶ Sp O), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → Flat s → ∀ (ch : Charts Z) (g : ∀ a, O →+* ch.R a) (V J : Type) [Finite V] [Finite J] (N : ℕ) (ξ : ∀ a, J → Fin (N + 1) → MvPolynomial V (ch.R a)) (ℓ : ∀ a, J → Fin (N + 1) → ch.R a), (∀ a, ch.χ a ≫ s = spMap (g a)) → (∀ a, Cells (MvPolynomial.C : ch.R a →+* MvPolynomial V (ch.R a)) (ξ a) (ℓ a)) → (∀ (K : Type) [Field K] (a a' : ch.ι) (φ : ch.R a →+* K) (j' : J) (ψ' : MvPolynomial V (ch.R a') →+* K), spMap φ ≫ ch.χ a = spMap (ψ'.comp MvPolynomial.C) ≫ ch.χ a' → ∃ (j : J) (ψ : MvPolynomial V (ch.R a) →+* K) (u : Kˣ), ψ.comp MvPolynomial.C = φ ∧ ψ' ∘ ξ a' j' = (u : K) • (ψ ∘ ξ a j)) → ∃ (Z' : Scheme.{0}) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O N) (κ : ∀ a, J → (Sp (MvPolynomial V (ch.R a)) ⟶ Z')), CellCl s ch g ξ f q κ := by
  atlas_forward_decl GlobalTheory.GrCl.exists_cellCl
end
