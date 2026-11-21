import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelMapGenericallyOpenImmersionCalculusStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGrpObjOfStrictBirationalLaw
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeakNeronModelBirationalGroupLaw
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyIntegralOfIsIntegralOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ProdIrrAndWeakNeronStatement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmoothFlatAlgebraFiniteCoverDecomp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GlueModelsOverSubfield
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo

section
open CategoryTheory AlgebraicGeometry Limits

namespace GlobalTheory.EqualityOnPoints

theorem eq_on_points {W X Y Z : Scheme.{0}} {a b : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s]
    (h : a ≫ s = b ≫ s) (i : W ⟶ X) [IsDominant i] (hi : i ≫ a = i ≫ b) (x : X) :
    (a x : Y) = b x := by

  set l := pullback.lift a b h with hl
  have hcl : IsClosed (l ⁻¹' Set.range (pullback.diagonal s)) :=
    (pullback.diagonal s).isClosedEmbedding.isClosed_range.preimage l.continuous

  have he : i ≫ l = (i ≫ a) ≫ pullback.diagonal s := by
    apply pullback.hom_ext
    · rw [hl, Category.assoc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst,
        Category.comp_id]
    · rw [hl, Category.assoc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd,
        Category.comp_id, hi]
  have hsub : Set.range i ⊆ l ⁻¹' Set.range (pullback.diagonal s) := by
    rintro _ ⟨w, rfl⟩
    refine ⟨(i ≫ a) w, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← he, Scheme.Hom.comp_apply]

  have hall : l x ∈ Set.range (pullback.diagonal s) := by
    have hcl' := hcl.closure_subset_iff.2 hsub
    rw [i.denseRange.closure_range] at hcl'
    exact hcl' (Set.mem_univ x)
  obtain ⟨y, hy⟩ := hall
  have ha : a x = y := by
    have e : (pullback.diagonal s ≫ pullback.fst s s) y = (l ≫ pullback.fst s s) x := by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy]
    rw [pullback.diagonal_fst, hl, pullback.lift_fst] at e
    simpa using e.symm
  have hb : b x = y := by
    have e : (pullback.diagonal s ≫ pullback.snd s s) y = (l ≫ pullback.snd s s) x := by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy]
    rw [pullback.diagonal_snd, hl, pullback.lift_snd] at e
    simpa using e.symm
  rw [ha, hb]

end GlobalTheory.EqualityOnPoints
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.StrictLaw

theorem fibre_preirr {P X Y S : Scheme.{0}} {p : P ⟶ X} {q : P ⟶ Y} {g : X ⟶ S} {f : Y ⟶ S}
    (h : IsPullback p q g f) (x : X)
    [hg : GeometricallyIrreducible (f.fiberToSpecResidueField (g x))] :
    IsPreirreducible (p ⁻¹' {x}) := by
  have h1 : IsPullback (p.fiberι x) (p.fiberToSpecResidueField x) p (X.fromSpecResidueField x) :=
    IsPullback.of_hasPullback _ _
  have h2 : IsPullback (f.fiberι (g x)) (f.fiberToSpecResidueField (g x)) f
      (S.fromSpecResidueField (g x)) := IsPullback.of_hasPullback _ _
  have h3 := h1.paste_horiz h.flip
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField] at h3
  have h4 := IsPullback.of_right' h3 h2
  have h5 : IrreducibleSpace (p.fiber x) :=
    hg.geometrically_irreducibleSpace _ _ _ h4
  rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
  exact (PreirreducibleSpace.isPreirreducible_univ).image _ (p.fiberι x).continuous.continuousOn

theorem apply_eq_of_dominant {W X Y Z : Scheme.{0}} {a b : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s]
    (hs : a ≫ s = b ≫ s) (i : W ⟶ X) [IsDominant i] (hi : i ≫ a = i ≫ b) (x : X) : a x = b x := by
  first
  | (rename_i h_7 h_10; revert W X Y Z a b s h_7 hs i h_10 hi x; exact @_root_.GlobalTheory.EqualityOnPoints.eq_on_points)
  | exact @_root_.GlobalTheory.EqualityOnPoints.eq_on_points
  | exact _root_.GlobalTheory.EqualityOnPoints.eq_on_points
  | (apply _root_.GlobalTheory.EqualityOnPoints.eq_on_points <;> assumption)
  | (intros; apply _root_.GlobalTheory.EqualityOnPoints.eq_on_points <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EqualityOnPoints.eq_on_points <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EqualityOnPoints.eq_on_points ..)

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}

theorem extends_comp {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {U : M.Y.left.Opens}
    {g : U.toScheme ⟶ N.Y.left} (h : Extends M N f U g) {T : Scheme.{0}} (t : T ⟶ A.left)
    (u : T ⟶ U.toScheme) (e : t ≫ M.j = u ≫ U.ι) : u ≫ g = t ≫ f.left ≫ N.j := by
  have hp := isPullback_morphismRestrict M.j U
  rw [← hp.lift_fst u t e.symm, Category.assoc, h.2, ← Category.assoc, hp.lift_snd]

theorem pullback_map_fst {X Y : Over (Sp R)} (g : X ⟶ Y) :
    ((Over.pullback (spMap (algebraMap R K))).map g).left ≫ pullback.fst Y.hom (spMap (algebraMap R K))
      = pullback.fst X.hom (spMap (algebraMap R K)) ≫ g.left := by
  exact pullback.lift_fst _ _ _

def pr₁ (M : Model R A) (N : Model R A') : (M.prod N).Y ⟶ M.Y := fst M.Y N.Y

def pr₂ (M : Model R A) (N : Model R A') : (M.prod N).Y ⟶ N.Y := snd M.Y N.Y

theorem prod_j_fst (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (pr₁ M N).left = (fst A A').left ≫ M.j := by
  have : (M.prod N).e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map (fst M.Y N.Y) = fst A A' ≫ M.e.inv := by
    simp [Model.prod]
  have h := congrArg (fun t => t.left ≫ pullback.fst M.Y.hom (spMap (algebraMap R K))) this
  simp only [Over.comp_left, Category.assoc] at h
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback_map_fst _).symm).trans h)

theorem prod_j_snd (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (pr₂ M N).left = (snd A A').left ≫ N.j := by
  have : (M.prod N).e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map (snd M.Y N.Y) = snd A A' ≫ N.e.inv := by
    simp [Model.prod]
  have h := congrArg (fun t => t.left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))) this
  simp only [Over.comp_left, Category.assoc] at h
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback_map_fst _).symm).trans h)

theorem isPullback_j (M : Model R A) :
    IsPullback M.j A.hom M.Y.hom (spMap (algebraMap R K)) := by
  refine (IsPullback.of_hasPullback M.Y.hom (spMap (algebraMap R K))).of_iso
    ((Over.forget _).mapIso M.e) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · have : M.e.hom.left ≫ M.e.inv.left = 𝟙 _ := by rw [← Over.comp_left]; simp
    show _ ≫ 𝟙 _ = M.e.hom.left ≫ M.e.inv.left ≫ _
    rw [← Category.assoc, this]; simp
  · exact (Category.comp_id _).trans (Over.w M.e.hom).symm

theorem isDominant_j [IsDomain R] [IsFractionRing R K] (M : Model R A) : IsDominant M.j := by
  have := M.smooth
  have hd : DenseRange (spMap (algebraMap R K)) := by
    show DenseRange (PrimeSpectrum.comap (algebraMap R K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)]
    exact bot_le
  refine ⟨(hd.preimage M.Y.hom.isOpenMap).mono ?_⟩
  rintro y ⟨s, hs⟩
  obtain ⟨a, ha, -⟩ := Scheme.exists_preimage_of_isPullback (isPullback_j M) y s hs.symm
  exact ⟨a, ha⟩

theorem j_notMem_sp [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] (M : Model R A)
    (a : A.left) : M.j a ∉ M.sp := by
  intro h
  have h1 : M.Y.hom (M.j a) = spMap (algebraMap R K) (A.hom a) := by
    rw [← Scheme.Hom.comp_apply, M.j_hom, Scheme.Hom.comp_apply]
  have h2 : spMap (algebraMap R K) (A.hom a) = IsLocalRing.closedPoint R := h1.symm.trans h
  have h3 := congrArg PrimeSpectrum.asIdeal h2
  apply IsDiscreteValuationRing.not_a_field R
  refine h3.symm.trans ?_
  show Ideal.comap (algebraMap R K) (PrimeSpectrum.asIdeal (A.hom a)) = ⊥
  rw [@Ideal.eq_bot_of_prime K _ (PrimeSpectrum.asIdeal (R := K) (A.hom a))
    (PrimeSpectrum.isPrime (R := K) (A.hom a))]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)

theorem exists_restrict [IsNoetherianRing R] (M : Model R A) (V : M.Y.left.Opens)
    (hV : Set.range M.j ⊆ V) :
    ∃ (N : Model R A) (g : N.Y ⟶ M.Y), IsOpenImmersion g.left ∧ N.j ≫ g.left = M.j ∧
      Set.range g.left = V := by
  have := M.smooth
  have := M.sep
  have := M.qc
  have : IsLocallyNoetherian M.Y.left := LocallyOfFiniteType.isLocallyNoetherian M.Y.hom
  let j' : A.left ⟶ V.toScheme := IsOpenImmersion.lift V.ι M.j (by simpa using hV)
  have hj : j' ≫ V.ι = M.j := IsOpenImmersion.lift_fac _ _ _
  have h1 : IsPullback j' (𝟙 _) V.ι M.j := IsPullback.of_vert_isIso_mono ⟨by simp [hj]⟩
  have h2 := (h1.flip.paste_horiz (isPullback_j M).flip).flip
  rw [Category.id_comp] at h2
  refine ⟨⟨Over.mk (V.ι ≫ M.Y.hom), (Over.isoMk h2.isoPullback h2.isoPullback_hom_snd).symm,
    inferInstanceAs (Smooth (V.ι ≫ M.Y.hom)), inferInstanceAs (IsSeparated (V.ι ≫ M.Y.hom)),
    inferInstanceAs (QuasiCompact (V.ι ≫ M.Y.hom))⟩, Over.homMk V.ι rfl,
    (inferInstance : IsOpenImmersion V.ι), ?_, Scheme.Opens.range_ι V⟩
  exact (congrArg (· ≫ V.ι) h2.isoPullback_hom_fst).trans hj

theorem isoAt_of_open {M N : Model R A} {M' N' : Model R A'} {f : A ⟶ A'}
    (i : N.Y.left ⟶ M.Y.left) (i' : N'.Y.left ⟶ M'.Y.left) [IsOpenImmersion i] [IsOpenImmersion i']
    (hi : i ≫ M.Y.hom = N.Y.hom) (hi' : i' ≫ M'.Y.hom = N'.Y.hom)
    (hj : N.j ≫ i = M.j) (hj' : N'.j ≫ i' = M'.j)
    {U : M.Y.left.Opens} {g : U.toScheme ⟶ M'.Y.left} [IsOpenImmersion g] (h : Extends M M' f U g)
    (z : N.Y.left) (u : U.toScheme) (hu : U.ι u = i z) (hg : g u ∈ Set.range i') :
    IsoAt N N' f z := by
  let W : N.Y.left.Opens := i ⁻¹ᵁ (U.ι ''ᵁ (g ⁻¹ᵁ i'.opensRange))
  have h1 : Set.range (W.ι ≫ i) ⊆ Set.range U.ι := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨v, -, hv⟩ := w.2
    exact ⟨v, hv⟩
  let l := IsOpenImmersion.lift U.ι (W.ι ≫ i) h1
  have hl : l ≫ U.ι = W.ι ≫ i := IsOpenImmersion.lift_fac _ _ _
  have h2 : Set.range (l ≫ g) ⊆ Set.range i' := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨v, hv', hv⟩ := w.2
    have : U.ι (l w) = U.ι v := by
      rw [← Scheme.Hom.comp_apply, hl]; exact hv.symm
    rw [Scheme.Hom.comp_apply, U.ι.isOpenEmbedding.injective this]
    exact hv'
  let m := IsOpenImmersion.lift i' (l ≫ g) h2
  have hm : m ≫ i' = l ≫ g := IsOpenImmersion.lift_fac _ _ _
  refine ⟨W, m, ⟨u, hg, hu⟩, ⟨?_, ?_⟩, inferInstance⟩
  · rw [← hi', ← hi, ← Category.assoc, hm, Category.assoc, h.1, ← Category.assoc, hl, Category.assoc]
  · rw [← cancel_mono i', Category.assoc, hm, ← Category.assoc,
      extends_comp h (N.j ⁻¹ᵁ W).ι _ (by rw [Category.assoc, hl, ← hj, morphismRestrict_ι_assoc])]
    simp only [Category.assoc, hj']

theorem geomIrr [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)] (M : Model R A)
    (hM : M.Irr) (s : Sp R) (hs : s = IsLocalRing.closedPoint R) :
    GeometricallyIrreducible (M.Y.hom.fiberToSpecResidueField s) := by
  have := M.smooth
  have h0 : s.asIdeal = IsLocalRing.maximalIdeal R := by rw [hs]; rfl
  have h0' : s.asIdeal.IsMaximal := h0 ▸ IsLocalRing.maximalIdeal.isMaximal R
  have h1 : IsAlgClosed s.asIdeal.ResidueField :=
    IsAlgClosed.of_ringEquiv (IsLocalRing.ResidueField R) _
      ((Ideal.quotEquivOfEq h0.symm).trans
        (RingEquiv.ofBijective _ (Ideal.bijective_algebraMap_quotient_residueField _)))
  have h2 : IsAlgClosed ((Sp R).residueField s) :=
    IsAlgClosed.of_ringEquiv s.asIdeal.ResidueField _
      (Scheme.Spec.residueFieldIso (CommRingCat.of R) s).commRingCatIsoToRingEquiv.symm
  have h3 : IrreducibleSpace (M.Y.hom.fiber s) := by
    have : IrreducibleSpace (M.Y.hom ⁻¹' {s} : Set _) :=
      Subtype.irreducibleSpace (hs ▸ hM)
    exact (M.Y.hom.fiberHomeo _).irreducibleSpace_iff.2 this
  have h4 : LocallyOfFiniteType (M.Y.hom.fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  exact @geometricallyIrreducible_of_isAlgClosed _ _ h2 _ _ h4 h3

theorem exists_pt {P U Y : Type*} [TopologicalSpace P] [TopologicalSpace U] (p : P → Y) (x : Y)
    (hF : IsPreirreducible (p ⁻¹' {x})) (i g : U → P) (hi : Continuous i) (hg : IsOpenMap g)
    (h : ∀ u, p (g u) = p (i u)) (W O : Set P) (hW : IsOpen W) (hO : IsOpen O)
    (hWi : W ⊆ Set.range i) (h1 : (p ⁻¹' {x} ∩ W).Nonempty) (h2 : (p ⁻¹' {x} ∩ O).Nonempty) :
    ∃ u, i u ∈ W ∧ p (i u) = x ∧ g u ∈ O := by
  obtain ⟨w, hw, hwW⟩ := h1
  obtain ⟨u, rfl⟩ := hWi hwW
  obtain ⟨_, hz, ⟨v, hv, rfl⟩, hzO⟩ := hF _ _ (hg _ (hW.preimage hi)) hO
    ⟨g u, (h u).trans hw, u, hwW, rfl⟩ h2
  exact ⟨v, hv, (h v).symm.trans hz, hzO⟩

theorem ext_pt [IsDomain R] [IsFractionRing R K] {B B' : Over (Sp K)} {M : Model R A}
    {N : Model R B} {N' : Model R B'} {Q : Model R A'} {f : A ⟶ B} {f' : A ⟶ B'}
    {U U' : M.Y.left.Opens} {g : U.toScheme ⟶ N.Y.left} {g' : U'.toScheme ⟶ N'.Y.left}
    (h : Extends M N f U g) (h' : Extends M N' f' U' g') (p : N.Y ⟶ Q.Y) (p' : N'.Y ⟶ Q.Y)
    (e : f.left ≫ N.j ≫ p.left = f'.left ≫ N'.j ≫ p'.left)
    (u : U.toScheme) (u' : U'.toScheme) (hu : U.ι u = U'.ι u') :
    p.left (g u) = p'.left (g' u') := by
  have := Q.sep
  have := isDominant_j M
  let W := U ⊓ U'
  let a : W.toScheme ⟶ U.toScheme := M.Y.left.homOfLE inf_le_left
  let a' : W.toScheme ⟶ U'.toScheme := M.Y.left.homOfLE inf_le_right
  have ha : a ≫ U.ι = W.ι := Scheme.homOfLE_ι _ _
  have ha' : a' ≫ U'.ι = W.ι := Scheme.homOfLE_ι _ _
  have hd : IsDominant (M.j ∣_ W) := IsZariskiLocalAtTarget.restrict this W
  have hw : U.ι u ∈ W := ⟨u.2, hu ▸ u'.2⟩
  obtain ⟨w, hw⟩ : ∃ w : W.toScheme, W.ι w = U.ι u := ⟨⟨_, hw⟩, rfl⟩
  have key := apply_eq_of_dominant (a := a ≫ g ≫ p.left) (b := a' ≫ g' ≫ p'.left) Q.Y.hom
    (by simp only [Category.assoc, Over.w, h.1, h'.1, reassoc_of% ha, reassoc_of% ha'])
    (M.j ∣_ W) (by
      have e1 := extends_comp h (M.j ⁻¹ᵁ W).ι (M.j ∣_ W ≫ a)
        (by rw [Category.assoc, ha, morphismRestrict_ι])
      have e2 := extends_comp h' (M.j ⁻¹ᵁ W).ι (M.j ∣_ W ≫ a')
        (by rw [Category.assoc, ha', morphismRestrict_ι])
      rw [Category.assoc] at e1 e2
      rw [reassoc_of% e1, reassoc_of% e2, e]) w
  have b1 : a w = u := U.ι.isOpenEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, ha, hw])
  have b2 : a' w = u' := U'.ι.isOpenEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, ha', ← hu, hw])
  simpa only [Scheme.Hom.comp_apply, b1, b2] using key

def Good (M : Model R A) (f : A ⊗ A ⟶ A ⊗ A) (V : Set M.Y.left) (z : (M.prod M).Y.left) : Prop :=
  ∃ (U : (M.prod M).Y.left.Opens) (g : U.toScheme ⟶ (M.prod M).Y.left) (u : U.toScheme),
    Extends (M.prod M) (M.prod M) f U g ∧ IsOpenImmersion g ∧ U.ι u = z ∧
    (pr₁ M M).left z ∈ V ∧ (pr₂ M M).left z ∈ V ∧
    (pr₁ M M).left (g u) ∈ V ∧ (pr₂ M M).left (g u) ∈ V

theorem isPullback_prod (M : Model R A) (N : Model R A') :
    IsPullback (pr₁ M N).left (pr₂ M N).left M.Y.hom N.Y.hom := IsPullback.of_hasPullback _ _

section
variable [IsDomain R] [IsLocalRing R] [IsFractionRing R K]
  [IsAlgClosed (IsLocalRing.ResidueField R)]

theorem fst_case (M : Model R A) (hM : M.Irr) (f : A ⊗ A ⟶ A ⊗ A) (hf : f ≫ fst A A = fst A A)
    (h : GenIso (M.prod M) (M.prod M) f) :
    ∃ T : Set M.Y.left, IsOpen T ∧ (M.sp ∩ T).Nonempty ∧ ∀ V : Set M.Y.left, IsOpen V →
      ∀ x ∈ M.sp, x ∈ T → x ∈ V → ∃ z, (pr₁ M M).left z = x ∧ Good M f V z := by
  obtain ⟨y, hy, U, g, hyU, he, hg⟩ := h
  have := M.smooth
  have hp := isPullback_prod M M
  have ho : UniversallyOpen (pr₁ M M).left :=
    MorphismProperty.of_isPullback hp.flip inferInstance
  refine ⟨(pr₁ M M).left '' U, (pr₁ M M).left.isOpenMap _ U.2, ⟨_, hy, y, hyU, rfl⟩, ?_⟩
  rintro V hV x hx ⟨w, hwU, hw⟩ hxV
  have := geomIrr M hM (M.Y.hom x) hx
  have hF := fibre_preirr hp x
  have hc : ∀ u, (pr₁ M M).left (g u) = (pr₁ M M).left (U.ι u) := fun u =>
    ext_pt (Q := M) he (extends_id _ U) (pr₁ M M) (pr₁ M M) (by
      rw [prod_j_fst, ← Category.assoc, ← Over.comp_left, hf]; simp) u u rfl
  have hO : IsOpen ((pr₂ M M).left ⁻¹' V) := hV.preimage (pr₂ M M).left.continuous
  obtain ⟨d, hd, hd'⟩ := Scheme.exists_preimage_of_isPullback hp x x rfl
  have hd2 : ((pr₁ M M).left ⁻¹' {x} ∩ (pr₂ M M).left ⁻¹' V).Nonempty :=
    ⟨d, hd, show (pr₂ M M).left d ∈ V from hd' ▸ hxV⟩
  obtain ⟨u, hu, hux, hgu⟩ := exists_pt (pr₁ M M).left x hF U.ι g U.ι.continuous
    g.isOpenEmbedding.isOpenMap hc (U ∩ (pr₂ M M).left ⁻¹' V) _ (U.2.inter hO) hO
    (fun z hz => ⟨⟨z, hz.1⟩, rfl⟩) (hF _ _ U.2 hO ⟨w, hw, hwU⟩ hd2) hd2
  exact ⟨_, hux, U, g, u, he, hg, rfl, hux ▸ hxV, hu.2, ((hc u).trans hux) ▸ hxV, hgu⟩

theorem snd_case (M : Model R A) (hM : M.Irr) (hMM : (M.prod M).Irr) (f f' : A ⊗ A ⟶ A ⊗ A)
    (hf : f ≫ fst A A = fst A A) (hf' : f' ≫ snd A A = snd A A)
    (hff : f ≫ snd A A = f' ≫ fst A A)
    (h : GenIso (M.prod M) (M.prod M) f) (h' : GenIso (M.prod M) (M.prod M) f') :
    ∃ T : Set M.Y.left, IsOpen T ∧ (M.sp ∩ T).Nonempty ∧ ∀ V : Set M.Y.left, IsOpen V →
      ∀ x ∈ M.sp, x ∈ T → x ∈ V → ∃ z, (pr₂ M M).left z = x ∧ Good M f V z := by
  obtain ⟨y, hy, U, g, hyU, he, hg⟩ := h
  obtain ⟨y', hy', U', g', hyU', he', hg'⟩ := h'
  have := M.smooth
  have hp := (isPullback_prod M M).flip
  have ho : UniversallyOpen (pr₂ M M).left :=
    MorphismProperty.of_isPullback hp.flip inferInstance
  obtain ⟨y₀, hy₀, hy₀U⟩ := hMM.2 _ _ U.2 U'.2 ⟨y, hy, hyU⟩ ⟨y', hy', hyU'⟩
  have hUU : IsOpen ((U : Set (M.prod M).Y.left) ∩ U') := U.2.inter U'.2
  refine ⟨(pr₂ M M).left '' (U ∩ U'), (pr₂ M M).left.isOpenMap _ hUU,
    ⟨_, ?_, y₀, hy₀U, rfl⟩, ?_⟩
  · show M.Y.hom _ = _
    rw [← Scheme.Hom.comp_apply, Over.w]
    exact hy₀
  rintro V hV x hx ⟨w, hwU, hw⟩ hxV
  have := geomIrr M hM (M.Y.hom x) hx
  have hF := fibre_preirr hp x
  have hc : ∀ u, (pr₁ M M).left (g u) = (pr₁ M M).left (U.ι u) := fun u =>
    ext_pt (Q := M) he (extends_id _ U) (pr₁ M M) (pr₁ M M) (by
      rw [prod_j_fst, ← Category.assoc, ← Over.comp_left, hf]; simp) u u rfl
  have hc' : ∀ u, (pr₂ M M).left (g' u) = (pr₂ M M).left (U'.ι u) := fun u =>
    ext_pt (Q := M) he' (extends_id _ U') (pr₂ M M) (pr₂ M M) (by
      rw [prod_j_snd, ← Category.assoc, ← Over.comp_left, hf']; simp) u u rfl
  have hO : IsOpen ((pr₁ M M).left ⁻¹' V) := hV.preimage (pr₁ M M).left.continuous
  obtain ⟨d, hd, hd'⟩ := Scheme.exists_preimage_of_isPullback hp x x rfl
  have hd2 : ((pr₂ M M).left ⁻¹' {x} ∩ (pr₁ M M).left ⁻¹' V).Nonempty :=
    ⟨d, hd, show (pr₁ M M).left d ∈ V from hd' ▸ hxV⟩
  obtain ⟨u', hu, hux, hgu⟩ := exists_pt (pr₂ M M).left x hF U'.ι g' U'.ι.continuous
    g'.isOpenEmbedding.isOpenMap hc' ((U ∩ U') ∩ (pr₁ M M).left ⁻¹' V) _ (hUU.inter hO) hO
    (fun z hz => ⟨⟨z, hz.1.2⟩, rfl⟩) (hF _ _ hUU hO ⟨w, hw, hwU⟩ hd2) hd2
  let u : U.toScheme := ⟨U'.ι u', hu.1.1⟩
  have huu : U.ι u = U'.ι u' := rfl
  have hc'' : (pr₂ M M).left (g u) = (pr₁ M M).left (g' u') :=
    ext_pt (Q := M) he he' (pr₂ M M) (pr₁ M M) (by
      rw [prod_j_fst, prod_j_snd, ← Category.assoc, ← Over.comp_left, hff, Over.comp_left,
        Category.assoc]) u u' huu
  exact ⟨_, hux, U, g, u, he, hg, huu, hu.2, hux ▸ hxV, (hc u) ▸ hu.2, hc'' ▸ hgu⟩
end

theorem good_isoAt {M N : Model R A} (i : N.Y ⟶ M.Y) [IsOpenImmersion i.left]
    (hj : N.j ≫ i.left = M.j) {f : A ⊗ A ⟶ A ⊗ A} {z : (M.prod M).Y.left}
    (h : Good M f (Set.range i.left) z) :
    ∃ w : (N.prod N).Y.left, i.left ((pr₁ N N).left w) = (pr₁ M M).left z ∧
      i.left ((pr₂ N N).left w) = (pr₂ M M).left z ∧
      IsoAt (N.prod N) (N.prod N) f w := by
  obtain ⟨U, g, u, he, hg, hu, h1, h2, h3, h4⟩ := h
  let ii : (N.prod N).Y ⟶ (M.prod M).Y := i ⊗ₘ i
  have e1 : ii.left ≫ (pr₁ M M).left = (pr₁ N N).left ≫ i.left := by
    exact congrArg (fun t => t.left) (tensorHom_fst i i)
  have e2 : ii.left ≫ (pr₂ M M).left = (pr₂ N N).left ≫ i.left := by
    exact congrArg (fun t => t.left) (tensorHom_snd i i)
  have e : ii.left = pullback.map N.Y.hom N.Y.hom M.Y.hom M.Y.hom i.left i.left (𝟙 _)
      (by simp) (by simp) := by
    apply pullback.hom_ext
    · exact e1.trans (pullback.lift_fst _ _ _).symm
    · exact e2.trans (pullback.lift_snd _ _ _).symm
  have ho : IsOpenImmersion ii.left := by
    rw [e]
    exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) ‹_› ‹_› (Over.w i).symm (Over.w i).symm
  have hr : ∀ t, (pr₁ M M).left t ∈ Set.range i.left → (pr₂ M M).left t ∈ Set.range i.left →
      t ∈ Set.range ii.left := by
    intro t ht ht'
    rw [e]
    exact (Scheme.Pullback.range_map _ _ _ _ _ _ _ _ _).ge ⟨ht, ht'⟩
  have hj' : (N.prod N).j ≫ ii.left = (M.prod M).j := by
    apply (isPullback_prod M M).hom_ext
    · rw [prod_j_fst, ← hj, ← Category.assoc, ← prod_j_fst N N, Category.assoc, Category.assoc]
      exact congrArg (_ ≫ ·) e1
    · rw [prod_j_snd, ← hj, ← Category.assoc, ← prod_j_snd N N, Category.assoc, Category.assoc]
      exact congrArg (_ ≫ ·) e2
  obtain ⟨w, hw⟩ := hr z h1 h2
  refine ⟨w, ?_, ?_, @isoAt_of_open R _ K _ _ _ _ (M.prod M) (N.prod N) (M.prod M) (N.prod N) f
    ii.left ii.left ho ho (Over.w _) (Over.w _) hj' hj' U g hg he w u
    (hu.trans hw.symm) (hr _ h3 h4)⟩
  · rw [← hw, ← Scheme.Hom.comp_apply, ← e1, Scheme.Hom.comp_apply]
  · rw [← hw, ← Scheme.Hom.comp_apply, ← e2, Scheme.Hom.comp_apply]

theorem shear_fst [GrpObj A] (b : Bool) : shear A b ≫ fst A A = fst A A := by
  cases b <;> simp [shear]

def coshear (A : Over (Sp K)) [GrpObj A] : Bool → (A ⊗ A ⟶ A ⊗ A)
  | true => (β_ A A).hom ≫ shear A true ≫ (β_ A A).hom
  | false => (ι[A] ⊗ₘ 𝟙 A) ≫ (β_ A A).hom ≫ shear A true ≫ (β_ A A).hom

theorem coshear_snd [GrpObj A] (b : Bool) : coshear A b ≫ snd A A = snd A A := by
  cases b <;> simp [coshear, shear]

theorem shear_snd [GrpObj A] [IsCommMonObj A] (b : Bool) :
    shear A b ≫ snd A A = coshear A b ≫ fst A A := by
  cases b
  · simp only [coshear, shear, Category.assoc, braiding_hom_fst, lift_snd, MonObj.comp_mul,
      braiding_hom_snd, tensorHom_fst, tensorHom_snd, Category.comp_id]
    rw [mul_comm]; rfl
  · simp only [coshear, shear, Category.assoc, braiding_hom_fst, lift_snd, MonObj.comp_mul,
      braiding_hom_snd]
    rw [mul_comm]

end GlobalTheory.SS.StrictLaw

namespace GlobalTheory.SS
open StrictLaw

theorem exists_strict_le : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, BirLaw M → ∃ N : Model R A, Strict N ∧ N.Le M := by
  intro R K _ _ _ _ _ hSH A _ _ _ M ⟨hM, hs, hι⟩
  obtain ⟨gLe, gComp, gIso, gProd, gBr⟩ := GlobalTheory.T.modelMapGenericallyOpenImmersion_calculus R K hSH
  have hMM := (GlobalTheory.T.prod_irr_and_weakNeron' R K hSH A A).1 M M hM hM
  obtain ⟨hdvr, -, hac, hfr⟩ := hSH
  have hβ := (gBr A A A M M M hM hM hM).2
  have ht : GenIso (M.prod M) (M.prod M) (coshear A true) :=
    gComp _ _ _ _ _ _ _ _ hMM hβ (gComp _ _ _ _ _ _ _ _ hMM (hs true) hβ)
  have hco : ∀ b, GenIso (M.prod M) (M.prod M) (coshear A b) := by
    intro b
    cases b
    · exact gComp _ _ _ _ _ _ _ _ hMM
        (gProd _ _ _ _ _ _ _ _ _ _ hι (gLe A M M hM M.le_refl)) ht
    · exact ht
  choose T hT hTne hTx using fun b => fst_case M hM (shear A b) (shear_fst b) (hs b)
  choose T' hT' hTne' hTx' using fun b => snd_case M hM hMM (shear A b) (coshear A b)
    (shear_fst b) (coshear_snd b) (shear_snd b) (hs b) (hco b)
  have hcl : IsClosed M.sp :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal (IsLocalRing.closedPoint R)).2
      (IsLocalRing.maximalIdeal.isMaximal R) |>.preimage M.Y.hom.continuous
  let W : Set M.Y.left := (T true ∩ T false) ∩ (T' true ∩ T' false)
  have hW : IsOpen W := ((hT _).inter (hT _)).inter ((hT' _).inter (hT' _))
  have hWne : (M.sp ∩ W).Nonempty :=
    hM.2 _ _ ((hT _).inter (hT _)) ((hT' _).inter (hT' _))
      (hM.2 _ _ (hT _) (hT _) (hTne _) (hTne _)) (hM.2 _ _ (hT' _) (hT' _) (hTne' _) (hTne' _))
  let V : M.Y.left.Opens := ⟨M.spᶜ ∪ W, hcl.isOpen_compl.union hW⟩
  obtain ⟨N, i, hi, hj, hr⟩ := exists_restrict M V (by
    rintro _ ⟨a, rfl⟩; exact Or.inl (j_notMem_sp M a))
  have hsp : N.sp = i.left ⁻¹' M.sp := by
    ext x
    show N.Y.hom x = _ ↔ M.Y.hom (i.left x) = _
    rw [← Scheme.Hom.comp_apply, Over.w]
  have hinj := i.left.isOpenEmbedding.injective
  have hN : N.Irr := by
    obtain ⟨x, hx, hxW⟩ := hWne
    obtain ⟨x, rfl⟩ : x ∈ Set.range i.left := hr ▸ Or.inr hxW
    unfold Model.Irr
    rw [hsp]
    exact ⟨⟨x, hx⟩, hM.2.preimage i.left.isOpenEmbedding⟩
  have hLe : N.Le M := ⟨i, hi, hj⟩
  have key : ∀ b, ∀ x ∈ N.sp,
      (∃ z, (pr₁ N N).left z = x ∧ IsoAt (N.prod N) (N.prod N) (shear A b) z) ∧
      ∃ z, (pr₂ N N).left z = x ∧ IsoAt (N.prod N) (N.prod N) (shear A b) z := by
    intro b x hx
    rw [hsp] at hx
    have hxV : i.left x ∈ (V : Set M.Y.left) := hr ▸ ⟨x, rfl⟩
    have hxW : i.left x ∈ W := hxV.resolve_left (fun h => h hx)
    have h1 : i.left x ∈ T b := by cases b; exacts [hxW.1.2, hxW.1.1]
    have h2 : i.left x ∈ T' b := by cases b; exacts [hxW.2.2, hxW.2.1]
    obtain ⟨z, hz, hg⟩ := hTx b _ i.left.isOpenEmbedding.isOpen_range _ hx h1 ⟨x, rfl⟩
    obtain ⟨z', hz', hg'⟩ := hTx' b _ i.left.isOpenEmbedding.isOpen_range _ hx h2 ⟨x, rfl⟩
    obtain ⟨w, hw, -, hw2⟩ := good_isoAt i hj hg
    obtain ⟨w', -, hw', hw2'⟩ := good_isoAt i hj hg'
    exact ⟨⟨w, hinj (hw.trans hz), hw2⟩, w', hinj (hw'.trans hz'), hw2'⟩
  refine ⟨N, ⟨⟨hN, fun b => ?_, ?_⟩, key⟩, hLe⟩
  · obtain ⟨x, hx⟩ := hN.1
    obtain ⟨z, hz, hz'⟩ := (key b x hx).1
    refine ⟨z, ?_, hz'⟩
    show (N.prod N).Y.hom z = _
    rw [← Over.w (pr₁ N N), Scheme.Hom.comp_apply, hz]
    exact hx
  · have h1 := gLe A N M hN hLe
    have h2 := (gIso A A N M (Iso.refl A)).1 h1
    have h3 := gComp _ _ _ _ _ _ _ _ hM h1 (gComp _ _ _ _ _ _ _ _ hM hι h2)
    simpa using h3

end GlobalTheory.SS
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_strict_model_of_birational : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, BirLaw M → ∃ N : Model R A, Strict N ∧ N.Le M := by
  atlas_forward_decl GlobalTheory.SS.exists_strict_le
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.ChartModel

set_option backward.isDefEq.respectTransparency false

noncomputable def twoCover {X U V : Scheme.{0}} (u : U ⟶ X) (v : V ⟶ X) [IsOpenImmersion u] [IsOpenImmersion v]
    (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v) : X.OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun i => Bool.rec U V i)
    (fun i => Bool.rec (motive := fun i => (Bool.rec U V i : Scheme.{0}) ⟶ X) u v i) (fun x => by
    rcases hc x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩) (fun i => by cases i <;> assumption)

theorem isClosedImmersion_snd_diagonal {U Y S : Scheme.{0}} (g : U ⟶ Y) (f : Y ⟶ S) [Mono g]
    [IsSeparated (g ≫ f)] :
    IsClosedImmersion (pullback.snd (pullback.diagonal f)
      (pullback.map (g ≫ f) (g ≫ f) f f g g (𝟙 _) (Category.comp_id _) (Category.comp_id _))) := by
  have H := pullback_map_diagonal_isPullback g g f
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion H.isoPullback.hom,
    H.isoPullback_hom_snd, ← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion (pullback.diagonal g)]
  convert (inferInstance : IsClosedImmersion (pullback.diagonal (g ≫ f)))
  ext : 1 <;> simp

theorem isSeparated_of_two {U V Y S : Scheme.{0}} (u : U ⟶ Y) (v : V ⟶ Y) (f : Y ⟶ S) [IsOpenImmersion u]
    [IsOpenImmersion v] [IsSeparated (u ≫ f)] [IsSeparated (v ≫ f)]
    (h : ∀ x y : Y, f x = f y → (x ∈ Set.range u ∧ y ∈ Set.range u) ∨ (x ∈ Set.range v ∧ y ∈ Set.range v)) :
    IsSeparated f := by
  constructor
  refine IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) (twoCover
    (pullback.map (u ≫ f) (u ≫ f) f f u u (𝟙 _) (Category.comp_id _) (Category.comp_id _))
    (pullback.map (v ≫ f) (v ≫ f) f f v v (𝟙 _) (Category.comp_id _) (Category.comp_id _)) ?_) ?_
  · intro z
    rw [Scheme.Pullback.range_map, Scheme.Pullback.range_map]
    exact h _ _ (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition])
  · rintro (_ | _)
    · exact isClosedImmersion_snd_diagonal u f
    · exact isClosedImmersion_snd_diagonal v f

theorem exists_glue_chart {S T A X W : Scheme.{0}} (i : T ⟶ S) [IsOpenImmersion i] (a : A ⟶ T) (c : X ⟶ S)
    {p : W ⟶ X} {w : W ⟶ T} (hW : IsPullback p w c i) (u : W ⟶ A) [IsOpenImmersion u] (hu : u ≫ a = w)
    [Smooth a] [IsSeparated a] [Smooth c] [IsSeparated c] [CompactSpace A] [CompactSpace X] :
    ∃ (Y : Scheme.{0}) (f : Y ⟶ S) (g : X ⟶ Y) (j : A ⟶ Y), IsOpenImmersion g ∧ IsPullback j a f i ∧ g ≫ f = c ∧
      p ≫ g = u ≫ j ∧ Smooth f ∧ IsSeparated f ∧ CompactSpace Y ∧ ∀ y, f y ∉ Set.range i → y ∈ Set.range g := by
  have : IsOpenImmersion p := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hW.flip ‹_›
  have := GlueModels.isOpenImmersion_inl p u
  have := GlueModels.isOpenImmersion_inr p u
  have hc := GlueModels.pushout_cover p u
  let f : pushout p u ⟶ S := pushout.desc c (a ≫ i) (by rw [hW.w, ← Category.assoc, hu])
  have h1 : pushout.inl p u ≫ f = c := pushout.inl_desc _ _ _
  have h2 : pushout.inr p u ≫ f = a ≫ i := pushout.inr_desc _ _ _
  have e1 (x : X) : f (pushout.inl p u x) = c x := congrArg (fun g => g x) h1
  have e2 (x : A) : f (pushout.inr p u x) = i (a x) := congrArg (fun g => g x) h2
  have e3 (x : W) : pushout.inl p u (p x) = pushout.inr p u (u x) :=
    congrArg (fun g => g x) (pushout.condition (f := p) (g := u))
  have hin (y) (hy : f y ∈ Set.range i) : y ∈ Set.range (pushout.inr p u) := by
    rcases hc y with ⟨x, rfl⟩ | hy
    · obtain ⟨t, ht⟩ := hy
      obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hW x t ((e1 x).symm.trans ht.symm)
      exact ⟨u z, (e3 z).symm⟩
    · exact hy
  have hout (y) (hy : f y ∉ Set.range i) : y ∈ Set.range (pushout.inl p u) := by
    rcases hc y with h | ⟨x, rfl⟩
    · exact h
    · exact absurd ⟨a x, (e2 x).symm⟩ hy
  refine ⟨_, f, pushout.inl p u, pushout.inr p u, inferInstance, ?_, h1, pushout.condition, ?_, ?_, ?_, hout⟩
  · refine (IsOpenImmersion.isPullback _ _ _ _ h2 ?_).flip
    ext y
    constructor
    · exact hin y
    · rintro ⟨x, rfl⟩
      exact ⟨a x, (e2 x).symm⟩
  · refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) (twoCover _ _ hc) ?_
    rintro (_ | _)
    · change Smooth (pushout.inl p u ≫ f)
      rw [h1]; infer_instance
    · change Smooth (pushout.inr p u ≫ f)
      rw [h2]; infer_instance
  · have : IsSeparated (pushout.inl p u ≫ f) := by rw [h1]; infer_instance
    have : IsSeparated (pushout.inr p u ≫ f) := by rw [h2]; infer_instance
    refine isSeparated_of_two (pushout.inl p u) (pushout.inr p u) f fun x y hxy => ?_
    by_cases hx : f x ∈ Set.range i
    · exact Or.inr ⟨hin x hx, hin y (hxy ▸ hx)⟩
    · exact Or.inl ⟨hout x hx, hout y (hxy ▸ hx)⟩
  · refine ⟨?_⟩
    rw [← Set.eq_univ_of_forall (s := Set.range (pushout.inl p u) ∪ Set.range (pushout.inr p u)) hc]
    exact (isCompact_range (pushout.inl p u).continuous).union (isCompact_range (pushout.inr p u).continuous)

theorem exists_model_of_chart : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)), Smooth A.hom → IsSeparated A.hom → QuasiCompact A.hom → ∀ (C : Type) [CommRing C] [Algebra R C], Algebra.Smooth R C → ∀ u : Sp (TensorProduct R K C) ⟶ A.left, IsOpenImmersion u → u ≫ A.hom = spMap (algebraMap K (TensorProduct R K C)) → ∃ (M : Model R A) (g : Sp C ⟶ M.Y.left), IsOpenImmersion g ∧ g ≫ M.Y.hom = spMap (algebraMap R C) ∧ spMap (Algebra.TensorProduct.includeRight : C →ₐ[R] TensorProduct R K C).toRingHom ≫ g = u ≫ M.j ∧ M.sp ⊆ Set.range g := by
  intro R K _ _ _ _ _ _ A hA hs hq C _ _ hC u hu hua
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hloc : IsLocalization.Away π K := by
    refine (IsLocalization.iff_of_le_of_exists_dvd (S := K) (M := Submonoid.powers π) (nonZeroDivisors R)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero) fun r hr => ?_).2 inferInstance
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero hr) hπ
    exact ⟨π ^ n, ⟨n, rfl⟩, hn.dvd⟩
  have hi : IsOpenImmersion (spMap (algebraMap R K)) := IsOpenImmersion.of_isLocalization π
  have hW : IsPullback (spMap (Algebra.TensorProduct.includeRight : C →ₐ[R] TensorProduct R K C).toRingHom)
      (spMap (algebraMap K (TensorProduct R K C))) (spMap (algebraMap R C)) (spMap (algebraMap R K)) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R K C)).flip
  have : Smooth (spMap (algebraMap R C)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr hC
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨Y, f, g, j, hg, hj, hgf, hp, h1, h2, h3, h4⟩ :=
    exists_glue_chart (spMap (algebraMap R K)) A.hom (spMap (algebraMap R C)) hW u hua
  refine ⟨⟨Over.mk f, Over.isoMk hj.isoPullback.symm hj.isoPullback_inv_snd, h1, h2,
    (inferInstance : QuasiCompact f)⟩, g, hg, hgf, ?_, fun y hy => h4 y ?_⟩
  · exact hp.trans (congrArg (u ≫ ·) hj.isoPullback_hom_fst.symm)
  · rintro ⟨t, ht⟩
    have ht' : spMap (algebraMap R K) t = IsLocalRing.closedPoint R := ht.trans hy
    have h5 : π ∈ (spMap (algebraMap R K) t).asIdeal := by
      rw [ht']; exact hπ.not_isUnit
    exact t.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (show algebraMap R K π ∈ t.asIdeal from h5)
      (IsLocalization.Away.algebraMap_isUnit π))

end GlobalTheory.ChartModel
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scheme_model_of_affine_smooth_chart : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)), Smooth A.hom → IsSeparated A.hom → QuasiCompact A.hom → ∀ (C : Type) [CommRing C] [Algebra R C], Algebra.Smooth R C → ∀ u : Sp (TensorProduct R K C) ⟶ A.left, IsOpenImmersion u → u ≫ A.hom = spMap (algebraMap K (TensorProduct R K C)) → ∃ (M : Model R A) (g : Sp C ⟶ M.Y.left), IsOpenImmersion g ∧ g ≫ M.Y.hom = spMap (algebraMap R C) ∧ spMap (Algebra.TensorProduct.includeRight : C →ₐ[R] TensorProduct R K C).toRingHom ≫ g = u ≫ M.j ∧ M.sp ⊆ Set.range g := by
  atlas_forward_decl GlobalTheory.ChartModel.exists_model_of_chart
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.IrrSplit

section
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}

theorem isPullback_lift (M : Model R A) (U : M.Y.left.Opens)
    (hU : Set.range (pullback.fst M.Y.hom (spMap (algebraMap R K))) ⊆ Set.range U.ι) :
    IsPullback (IsOpenImmersion.lift U.ι (pullback.fst M.Y.hom (spMap (algebraMap R K))) hU)
      (pullback.snd M.Y.hom (spMap (algebraMap R K))) (U.ι ≫ M.Y.hom) (spMap (algebraMap R K)) := by
  refine ⟨⟨by rw [IsOpenImmersion.lift_fac_assoc, pullback.condition]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c => pullback.lift (c.fst ≫ U.ι) c.snd (by simpa using c.condition)) ?_ ?_ ?_⟩⟩
  · intro c
    rw [← cancel_mono U.ι, Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
  · intro c
    rw [pullback.lift_snd]
  · intro c m h₁ h₂
    apply pullback.hom_ext
    · rw [pullback.lift_fst, ← h₁, Category.assoc, IsOpenImmersion.lift_fac]
    · rw [pullback.lift_snd, h₂]

def restrictModel (M : Model R A) (U : M.Y.left.Opens) [QuasiCompact U.ι]
    (hU : Set.range (pullback.fst M.Y.hom (spMap (algebraMap R K))) ⊆ Set.range U.ι) : Model R A where
  Y := Over.mk (U.ι ≫ M.Y.hom)
  e := Over.isoMk (g := (Over.pullback (spMap (algebraMap R K))).obj M.Y) (isPullback_lift M U hU).isoPullback.symm
    ((isPullback_lift M U hU).isoPullback_inv_snd) ≪≫ M.e
  smooth := by have := M.smooth; show Smooth (U.ι ≫ M.Y.hom); infer_instance
  sep := by have := M.sep; show IsSeparated (U.ι ≫ M.Y.hom); infer_instance
  qc := by have := M.qc; show QuasiCompact (U.ι ≫ M.Y.hom); infer_instance

theorem restrictModel_j (M : Model R A) (U : M.Y.left.Opens) [QuasiCompact U.ι]
    (hU : Set.range (pullback.fst M.Y.hom (spMap (algebraMap R K))) ⊆ Set.range U.ι) :
    (restrictModel M U hU).j ≫ U.ι = M.j := by
  have h := (isPullback_lift M U hU).isoPullback_hom_fst
  show ((M.e.inv.left ≫ (isPullback_lift M U hU).isoPullback.hom) ≫
    pullback.fst (U.ι ≫ M.Y.hom) (spMap (algebraMap R K))) ≫ U.ι = _
  rw [Category.assoc, Category.assoc, reassoc_of% h, IsOpenImmersion.lift_fac]
  rfl

end

theorem exists_cover_irr : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) (M : Model R A), ∃ (n : ℕ) (N : Fin n → Model R A) (g : ∀ i, (N i).Y ⟶ M.Y), (∀ i, (N i).Irr ∧ IsOpenImmersion (g i).left ∧ (N i).j ≫ (g i).left = M.j) ∧ ∀ y ∈ M.sp, ∃ i, y ∈ Set.range (g i).left := by
  intro R K _ _ _ _ _ _ A M
  have := M.smooth
  have := M.qc
  let f : M.Y.left ⟶ Sp R := M.Y.hom
  let c : Sp R := IsLocalRing.closedPoint R
  have : IsLocallyNoetherian M.Y.left := LocallyOfFiniteType.isLocallyNoetherian f
  have hf : Smooth f := M.smooth
  have hf' : QuasiCompact f := M.qc
  have hs : Smooth (f.fiberToSpecResidueField c) :=
    inferInstanceAs (Smooth (pullback.snd f ((Sp R).fromSpecResidueField c)))
  obtain ⟨-, hn, hl⟩ := GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field
    ((Sp R).residueField c) (f.fiber c) (f.fiberToSpecResidueField c) hs
  have hn' : GlobalTheory.IsNormalScheme (f.fiber c) := GlobalTheory.IsNormalScheme.of_pred hn
  have : CompactSpace (f.fiber c) := inferInstance
  have : IsNoetherian (f.fiber c) := {}
  have hfin : (irreducibleComponents (f.fiber c)).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hr : Set.range (f.fiberι c) = M.sp := f.range_fiberι c
  have hcl : Topology.IsClosedEmbedding (f.fiberι c) := by
    refine ⟨(f.fiberι c).isEmbedding, ?_⟩
    rw [f.range_fiberι]
    exact (IsLocalRing.isClosed_singleton_closedPoint R).preimage f.continuous
  have : Finite (irreducibleComponents (f.fiber c)) := hfin
  obtain ⟨n, ⟨σ⟩⟩ := Finite.exists_equiv_fin (irreducibleComponents (f.fiber c))
  let U : Fin n → M.Y.left.Opens := fun i => ⟨(f.fiberι c '' (σ.symm i).1ᶜ)ᶜ,
    (hcl.isClosedMap _ (GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents
      (σ.symm i).2).isClosed_compl).isOpen_compl⟩
  have hU : ∀ i, Set.range (pullback.fst M.Y.hom (spMap (algebraMap R K))) ⊆ Set.range (U i).ι := by
    rintro i _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    rintro ⟨z, -, hz⟩
    have h1 : pullback.fst M.Y.hom (spMap (algebraMap R K)) x ∈ M.sp := hr ▸ ⟨z, hz⟩
    have h2 : M.Y.hom (pullback.fst M.Y.hom (spMap (algebraMap R K)) x) =
        spMap (algebraMap R K) (pullback.snd M.Y.hom (spMap (algebraMap R K)) x) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    have h3 := h2.symm.trans h1
    generalize pullback.snd M.Y.hom (spMap (algebraMap R K)) x = p at h3
    have h4 : Ideal.comap (algebraMap R K) p.asIdeal = IsLocalRing.maximalIdeal R :=
      congrArg PrimeSpectrum.asIdeal h3
    have h5 : p.asIdeal = ⊥ := (Ideal.eq_bot_or_top (K := K) p.asIdeal).resolve_right p.isPrime.ne_top
    rw [h5, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)] at h4
    exact IsDiscreteValuationRing.not_a_field R h4.symm
  have hmem : ∀ i z, f.fiberι c z ∈ U i ↔ z ∈ (σ.symm i).1 := by
    intro i z
    show f.fiberι c z ∉ f.fiberι c '' (σ.symm i).1ᶜ ↔ _
    rw [hcl.injective.mem_set_image]
    simp
  refine ⟨n, fun i => restrictModel M (U i) (hU i), fun i => Over.homMk (U i).ι rfl,
    fun i => ⟨?_, inferInstanceAs (IsOpenImmersion (U i).ι), restrictModel_j M (U i) (hU i)⟩, ?_⟩
  · have hi : IsIrreducible (f.fiberι c '' (σ.symm i).1) :=
      (σ.symm i).2.1.image _ (f.fiberι c).continuous.continuousOn
    have he : (restrictModel M (U i) (hU i)).sp = (U i).ι ⁻¹' (f.fiberι c '' (σ.symm i).1) := by
      ext y
      constructor
      · intro hy
        have : (U i).ι y ∈ M.sp := hy
        rw [← hr] at this
        obtain ⟨z, hz⟩ := this
        refine ⟨z, (hmem i z).1 ?_, hz⟩
        rw [hz]; exact y.2
      · rintro ⟨z, -, hz⟩
        have : (U i).ι y ∈ M.sp := hr ▸ ⟨z, hz⟩
        exact this
    show IsIrreducible _
    rw [he]
    refine ⟨?_, hi.2.preimage (U i).ι.isOpenEmbedding⟩
    obtain ⟨z, hz⟩ := (σ.symm i).2.1.1
    exact ⟨⟨_, (hmem i z).2 hz⟩, z, hz, rfl⟩
  · intro y hy
    rw [← hr] at hy
    obtain ⟨z, rfl⟩ := hy
    refine ⟨σ ⟨_, irreducibleComponent_mem_irreducibleComponents z⟩, ⟨_, (hmem _ z).2 ?_⟩, rfl⟩
    rw [Equiv.symm_apply_apply]
    exact mem_irreducibleComponent

end GlobalTheory.SS.IrrSplit
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cover_model_irreducible_specialFibre : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) (M : Model R A), ∃ (n : ℕ) (N : Fin n → Model R A) (g : ∀ i, (N i).Y ⟶ M.Y), (∀ i, (N i).Irr ∧ IsOpenImmersion (g i).left ∧ (N i).j ≫ (g i).left = M.j) ∧ ∀ y ∈ M.sp, ∃ i, y ∈ Set.range (g i).left := by
  atlas_forward_decl GlobalTheory.SS.IrrSplit.exists_cover_irr
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GlobalTheory.SS.WeakNeronEx
open GlobalTheory.AbLaw ReciprocityTheory.ChartRestriction.G.Out

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem sp_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (e : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem away_of_irreducible (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K]
    {π : V} (hπ : Irreducible π) : IsLocalization.Away π K := by
  refine (IsLocalization.iff_of_le_of_exists_dvd (M := Submonoid.powers π) (S := K)
    (nonZeroDivisors V) (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero) ?_).mpr
    inferInstance
  intro a ha
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    (nonZeroDivisors.ne_zero ha) hπ
  exact ⟨π ^ n, ⟨n, rfl⟩, hn.dvd⟩

section Ev
variable {X : Scheme.{0}} {L : Type} [Field L] (a : Sp L ⟶ X)

def ev (W : X.Opens) (h : ⊤ ≤ a ⁻¹ᵁ W) : Γ(X, W) →+* L :=
  (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom.comp (a.appLE W ⊤ h).hom

theorem ev_rs {W W' : X.Opens} (e : W' ≤ W) (h : ⊤ ≤ a ⁻¹ᵁ W) (h' : ⊤ ≤ a ⁻¹ᵁ W') (f : Γ(X, W)) :
    ev a W' h' (rs X e f) = ev a W h f := by
  have := congrArg (fun q => q.hom f) (Scheme.Hom.map_appLE a h' (homOfLE e).op)
  exact congrArg (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom this

theorem ev_ne_zero {W : X.Opens} (h : ⊤ ≤ a ⁻¹ᵁ W) (f : Γ(X, W)) :
    ev a W h f ≠ 0 ↔ ⊤ ≤ a ⁻¹ᵁ X.basicOpen f := by
  have e := Scheme.basicOpen_appLE a ⊤ W h f
  rw [top_inf_eq] at e
  rw [← e, ← isUnit_iff_ne_zero]
  constructor
  · intro hu
    have : IsUnit ((a.appLE W ⊤ h).hom f) := by
      have := hu.map (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom
      simpa [ev] using this
    exact (Scheme.basicOpen_of_isUnit _ this).ge
  · intro hu
    have : IsUnit ((a.appLE W ⊤ h).hom f) :=
      RingedSpace.isUnit_of_isUnit_germ (Sp L).toRingedSpace ⊤ _ fun x hx =>
        (Scheme.mem_basicOpen _ _ x hx).1 (hu hx)
    exact this.map (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom

theorem spMap_ev {W : X.Opens} (hW : IsAffineOpen W) (h : ⊤ ≤ a ⁻¹ᵁ W) :
    spMap (ev a W h) ≫ hW.fromSpec = a := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec a hW (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  have : spMap (ev a W h) = Spec.map (Scheme.ΓSpecIso (CommRingCat.of L)).hom ≫ Spec.map (a.appLE W ⊤ h) :=
    Spec.map_comp (a.appLE W ⊤ h) _
  rw [this, Category.assoc, e, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]
end Ev

theorem fromSpec_hom {X : Scheme.{0}} {K : Type} [CommRing K] (f : X ⟶ Sp K) {W : X.Opens} (hW : IsAffineOpen W) :
    hW.fromSpec ≫ f = spMap (cst f W) := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hW (le_top : W ≤ f ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at e
  rw [← e]
  rfl

theorem exists_min {V L : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field L] [Algebra V L]
    [IsFractionRing V L] {I : Type} [Finite I] [Nonempty I] (c : I → L) :
    ∃ i, ∀ j, ∃ t : V, c j = algebraMap V L t * c i := by
  obtain ⟨i, hi⟩ := Finite.exists_max (fun j => ValuationRing.valuation V L (c j))
  refine ⟨i, fun j => ?_⟩
  by_cases h0 : c i = 0
  · have := hi j
    simp only [h0, map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact ⟨0, by simp [this]⟩
  · have : c j / c i ∈ (ValuationRing.valuation V L).integer := by
      rw [Valuation.mem_integer_iff, map_div₀]
      exact div_le_one_of_le₀ (hi j) zero_le'
    obtain ⟨t, ht⟩ := (ValuationRing.mem_integer_iff V L _).1 this
    exact ⟨t, by rw [ht, div_mul_cancel₀ _ h0]⟩

theorem exists_chart {X : Scheme.{0}} {H : LB X} {m : ℕ} (s : Fin (m + 1) → LB.Sec H)
    (hc : ⨆ i, nonzeroLocus (s i) = ⊤) (r : ∀ i, Fin (m + 1) → Γ(X, nonzeroLocus (s i)))
    (hr : ∀ i j k, rs X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) =
        rs X (inf_le_left : nonzeroLocus (s i) ⊓ H.U k ≤ nonzeroLocus (s i)) (r i j) *
          rs X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s i).f k))
    {V L : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field L] [Algebra V L]
    [IsFractionRing V L] (a : Sp L ⟶ X) :
    ∃ (i : Fin (m + 1)) (h : ⊤ ≤ a ⁻¹ᵁ nonzeroLocus (s i)), ∀ j, ev a _ h (r i j) ∈ (algebraMap V L).range := by
  have hpt : ∀ W : X.Opens, a (IsLocalRing.closedPoint L) ∈ W → ⊤ ≤ a ⁻¹ᵁ W := fun W hW y _ => by
    have : y = IsLocalRing.closedPoint L := Subsingleton.elim (α := PrimeSpectrum L) _ _
    subst this
    exact hW
  have hx : a (IsLocalRing.closedPoint L) ∈ ⨆ i, nonzeroLocus (s i) := by rw [hc]; trivial
  obtain ⟨i₀, h₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h₀
  have hU : ⊤ ≤ a ⁻¹ᵁ H.U k := hpt _ (X.basicOpen_le _ hk)
  have hne : ev a _ hU ((s i₀).f k) ≠ 0 := (ev_ne_zero a hU _).2 (hpt _ hk)
  obtain ⟨i, hi⟩ := exists_min (V := V) (fun j => ev a _ hU ((s j).f k))
  have hne' : ev a _ hU ((s i).f k) ≠ 0 := by
    intro h
    obtain ⟨t, ht⟩ := hi i₀
    exact hne (by simpa [h] using ht)
  have hD : ⊤ ≤ a ⁻¹ᵁ nonzeroLocus (s i) :=
    hpt _ (TopologicalSpace.Opens.mem_iSup.2 ⟨k, (ev_ne_zero a hU _).1 hne' (x := IsLocalRing.closedPoint L) trivial⟩)
  have hI : ⊤ ≤ a ⁻¹ᵁ (nonzeroLocus (s i) ⊓ H.U k) := fun y hy => ⟨hD hy, hU hy⟩
  refine ⟨i, hD, fun j => ?_⟩
  obtain ⟨t, ht⟩ := hi j
  have e := congrArg (ev a _ hI) (hr i j k)
  rw [map_mul, ev_rs a _ hU, ev_rs a _ hU, ev_rs a _ hD, ht] at e
  exact ⟨t, mul_right_cancel₀ hne' e⟩

section Alg
variable (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  {D : Type} [CommRing D] [Algebra K D] [Algebra R D] [IsScalarTower R K D]

include K in

theorem flat_sub (B : Subalgebra R D) : Module.Flat R B := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, Submodule.eq_bot_iff]
  rintro x ⟨c, hc⟩
  have hu : IsUnit (algebraMap R D c) := by
    rw [IsScalarTower.algebraMap_apply R K D]
    exact (IsLocalization.map_units K c).map _
  have : algebraMap R D c * (x : D) = 0 := by
    rw [← Algebra.smul_def]
    exact congrArg Subtype.val hc
  exact Subtype.ext (hu.mul_right_eq_zero.1 this)

def gen (B : Subalgebra R D) : TensorProduct R K B →ₐ[K] D :=
  Algebra.TensorProduct.lift (Algebra.ofId K D) B.val (fun _ _ => Commute.all _ _)

omit [IsDomain R] [IsDiscreteValuationRing R] in

theorem gen_injective (B : Subalgebra R D) : Function.Injective (gen R K B) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  letI : Algebra B (TensorProduct R K B) := Algebra.TensorProduct.rightAlgebra
  have hl : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) (TensorProduct R K B) :=
    IsLocalization.tensorRight K (nonZeroDivisors R)
  obtain ⟨⟨b, c⟩, e⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) x
  have e' := congrArg (gen R K B) e
  rw [map_mul, hx, zero_mul] at e'
  have hb : b = 0 := by
    apply Subtype.ext
    have : gen R K B (algebraMap B _ b) = (b : D) := by
      show gen R K B (1 ⊗ₜ b) = _
      simp [gen]
    rw [← this, ← e']; rfl
  rw [hb, map_zero] at e
  exact (IsLocalization.map_units (TensorProduct R K B) c).mul_left_eq_zero.1 e

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem gen_surjective {I : Type} (r : I → D)
    (h : Function.Surjective (MvPolynomial.eval₂Hom (algebraMap K D) r)) :
    Function.Surjective (gen R K (Algebra.adjoin R (Set.range r))) := by
  intro d
  obtain ⟨p, rfl⟩ := h d
  refine ⟨MvPolynomial.aeval (fun i => (1 : K) ⊗ₜ (⟨r i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ :
    Algebra.adjoin R (Set.range r))) p, ?_⟩
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  simp [gen, MvPolynomial.aeval_def]

theorem smooth_away {π : R} (hπ : Irreducible π) (B : Type) [CommRing B] [Algebra R B]
    [Algebra.Smooth K (TensorProduct R K B)] : Algebra.Smooth R (Localization.Away (algebraMap R B π)) := by
  have := away_of_irreducible R K hπ
  have h₁ : Algebra.Smooth R K := Algebra.Smooth.of_isLocalization_Away π
  have h₂ : Algebra.Smooth R (TensorProduct R K B) := Algebra.Smooth.comp R K _
  letI : Algebra B (TensorProduct R K B) := Algebra.TensorProduct.rightAlgebra
  have hl : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers π)) (TensorProduct R K B) :=
    IsLocalization.tensorRight K (Submonoid.powers π)
  rw [Algebra.algebraMapSubmonoid_powers] at hl
  haveI : IsScalarTower R B (TensorProduct R K B) := Algebra.TensorProduct.right_isScalarTower
  exact Algebra.Smooth.of_equiv ((IsLocalization.algEquiv (Submonoid.powers (algebraMap R B π))
    (TensorProduct R K B) (Localization.Away (algebraMap R B π))).restrictScalars R)
end Alg

theorem exists_affine (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {X : Scheme.{0}} (f : X ⟶ Sp K) (hf : IsProjBy f) :
    ∃ (m : ℕ) (B : Fin m → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra R (B i))
      (u : ∀ i, Sp (TensorProduct R K (B i)) ⟶ X),
      (∀ i, Algebra.FiniteType R (B i) ∧ Module.Flat R (B i) ∧ IsOpenImmersion (u i) ∧
        u i ≫ f = spMap (algebraMap K _)) ∧
      ∀ (V L : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra R V] [Field L] [Algebra V L]
        [IsFractionRing V L] (a : Sp L ⟶ X),
        a ≫ f ≫ spMap (algebraMap R K) = spMap ((algebraMap V L).comp (algebraMap R V)) →
        ∃ (i : Fin m) (b : B i →ₐ[R] V) (ψ : TensorProduct R K (B i) →+* L), spMap ψ ≫ u i = a ∧
          ∀ x, ψ (1 ⊗ₜ x) = algebraMap V L (b x) := by
  obtain ⟨H, -, m, s, hc, hs⟩ := hf
  choose haff r hr hsurj using hs
  letI : ∀ i, Algebra K Γ(X, nonzeroLocus (s i)) := fun i => (cst f _).toAlgebra
  letI : ∀ i, Algebra R Γ(X, nonzeroLocus (s i)) := fun i => ((cst f _).comp (algebraMap R K)).toAlgebra
  haveI : ∀ i, IsScalarTower R K Γ(X, nonzeroLocus (s i)) := fun i => IsScalarTower.of_algebraMap_eq fun _ => rfl
  let e : ∀ i, TensorProduct R K (Algebra.adjoin R (Set.range (r i))) ≃ₐ[K] Γ(X, nonzeroLocus (s i)) := fun i =>
    AlgEquiv.ofBijective (gen R K _) ⟨gen_injective R K _, gen_surjective R K _ (hsurj i)⟩
  refine ⟨m + 1, fun i => Algebra.adjoin R (Set.range (r i)), inferInstance, inferInstance,
    fun i => spMap (e i).symm.toAlgHom.toRingHom ≫ (haff i).fromSpec, fun i => ⟨?_, flat_sub R K _, ?_, ?_⟩, ?_⟩
  · exact Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)
  · haveI : IsIso (spMap (e i).symm.toAlgHom.toRingHom) :=
      inferInstanceAs (IsIso (Spec.map (e i).symm.toRingEquiv.toCommRingCatIso.hom))
    infer_instance
  · rw [Category.assoc, fromSpec_hom, sp_comp]
    exact congrArg spMap ((e i).symm.toAlgHom.comp_algebraMap)
  · intro V L _ _ _ _ _ _ _ a ha
    obtain ⟨i, h, hi⟩ := exists_chart s hc r hr (V := V) a
    have h₁ := spMap_ev a (haff i) h
    have h₂ : (ev a _ h).comp (algebraMap R _) = (algebraMap V L).comp (algebraMap R V) := by
      apply sp_inj
      have h₀ : a ≫ f = spMap ((ev a _ h).comp (cst f _)) := by
        rw [← sp_comp, ← fromSpec_hom f (haff i), reassoc_of% h₁]
      rw [← ha, reassoc_of% h₀, sp_comp]
      rfl
    letI : Algebra R L := ((algebraMap V L).comp (algebraMap R V)).toAlgebra
    haveI : IsScalarTower R V L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let φ : Γ(X, nonzeroLocus (s i)) →ₐ[R] L := ⟨ev a _ h, fun c => congrArg (fun q => q c) h₂⟩
    have hle : Algebra.adjoin R (Set.range (r i)) ≤ (IsScalarTower.toAlgHom R V L).range.comap φ := by
      rw [Algebra.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩
      exact hi j
    let κ := AlgEquiv.ofInjective (IsScalarTower.toAlgHom R V L) (IsFractionRing.injective V L)
    refine ⟨i, κ.symm.toAlgHom.comp ((φ.comp (Subalgebra.val _)).codRestrict _ fun x => hle x.2),
      (ev a _ h).comp (e i).toAlgHom.toRingHom, ?_, fun x => ?_⟩
    · rw [← Category.assoc, sp_comp]
      refine Eq.trans ?_ h₁
      congr 2
      ext y
      simp
    · have h₃ : ∀ y, algebraMap V L (κ.symm y) = y := fun y =>
        congrArg Subtype.val (κ.apply_symm_apply y)
      refine Eq.trans ?_ (h₃ _).symm
      have h₄ : gen R K (Algebra.adjoin R (Set.range (r i))) (1 ⊗ₜ x) = x.1 := by simp [gen]
      exact congrArg (ev a _ h) h₄

theorem range_subset {V : Type} [CommRing V] [IsLocalRing V] {Y Z : Scheme.{0}} (b : Sp V ⟶ Y) (g : Z ⟶ Y)
    [IsOpenImmersion g] (h : b (IsLocalRing.closedPoint V) ∈ Set.range g) : Set.range b ⊆ Set.range g := by
  rintro _ ⟨y, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint y).map b.continuous).mem_open g.isOpenEmbedding.isOpen_range h

theorem exists_weakNeron : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K], PerfectField (IsLocalRing.ResidueField R) → ∀ (A : Over (Sp K)), Smooth A.hom → IsProper A.hom → GlobalTheory.AbLaw.IsProjBy A.hom → ∃ (n : ℕ) (M : Fin n → Model R A), (∀ i, (M i).Irr) ∧ WeakNeron M := by
  intro R K _ _ _ _ _ _ hperf A hsm hpr hproj
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, B, _, _, u, hB, hpt⟩ := exists_affine R K A.hom hproj
  have hs : ∀ i, Algebra.Smooth R (Localization.Away (algebraMap R (B i) π)) := fun i => by
    obtain ⟨-, -, h₃, h₄⟩ := hB i
    have h₅ : Smooth (spMap (algebraMap K (TensorProduct R K (B i)))) := by rw [← h₄]; infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at h₅
    haveI := RingHom.smooth_algebraMap.mp h₅
    exact smooth_away R K hπ (B i)
  have h₁ := fun i => by
    haveI := (hB i).1
    haveI := (hB i).2.1
    exact GlobalTheory.T.smooth_flat_algebra_finite_cover_decomp R K π hπ hperf (B i) (hs i)
  choose n C instR instA φ hC hlift using h₁
  have h₂ := fun i k => GlobalTheory.T.exists_scheme_model_of_affine_smooth_chart R K A hsm inferInstance inferInstance (C i k) (hC i k).1
    (spMap (Algebra.TensorProduct.map (AlgHom.id K K) (φ i k)).toRingHom ≫ u i)
    (by haveI := (hC i k).2; haveI := (hB i).2.2.1; infer_instance)
    (by
      rw [Category.assoc, (hB i).2.2.2, sp_comp]
      exact congrArg spMap (AlgHom.comp_algebraMap (Algebra.TensorProduct.map (AlgHom.id K K) (φ i k))))
  choose M g hg₁ hg₂ hg₃ hg₄ using h₂
  choose p N q hN hcov using fun i k => GlobalTheory.T.exists_cover_model_irreducible_specialFibre R K A (M i k)
  let e := Fintype.equivFin (Σ (i : Fin m) (k : Fin (n i)), Fin (p i k))
  refine ⟨_, fun t => N (e.symm t).1 (e.symm t).2.1 (e.symm t).2.2, fun t => (hN _ _ _).1, ?_⟩
  intro V L _ _ _ _ _ _ _ hmax a ha
  suffices h : ∃ i k l, ∃ b : Sp V ⟶ (N i k l).Y.left, b ≫ (N i k l).Y.hom = spMap (algebraMap R V) ∧
      spMap (algebraMap V L) ≫ b = a ≫ (N i k l).j by
    obtain ⟨i, k, l, h⟩ := h
    refine ⟨e ⟨i, k, l⟩, ?_⟩
    beta_reduce
    rw [e.symm_apply_apply]
    exact h
  have hunr : Unr π V := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hmax, hπ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton]
  obtain ⟨i, b, ψ, hψ, hb⟩ := hpt V L a ha
  obtain ⟨k, c, hc⟩ := hlift i V b hunr
  have hb₀ : (spMap c.toRingHom ≫ g i k) ≫ (M i k).Y.hom = spMap (algebraMap R V) := by
    rw [Category.assoc, hg₂, sp_comp]
    exact congrArg spMap (AlgHom.comp_algebraMap c)
  have hgen : spMap (algebraMap V L) ≫ spMap c.toRingHom ≫ g i k = a ≫ (M i k).j := by
    letI : Algebra R L := ((algebraMap V L).comp (algebraMap R V)).toAlgebra
    haveI : IsScalarTower R V L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let ψ₀ : TensorProduct R K (B i) →ₐ[R] L := ⟨ψ, fun x => by
      have := hb (algebraMap R _ x)
      rw [AlgHom.commutes] at this
      refine Eq.trans (congrArg ψ ?_) this
      exact ((Algebra.TensorProduct.includeRight : B i →ₐ[R] TensorProduct R K (B i)).commutes x).symm⟩
    let ψ' : TensorProduct R K (C i k) →ₐ[R] L := Algebra.TensorProduct.lift
      (ψ₀.comp Algebra.TensorProduct.includeLeft) ((IsScalarTower.toAlgHom R V L).comp c) fun _ _ => Commute.all _ _
    have e₁ : ψ'.toRingHom.comp (Algebra.TensorProduct.map (AlgHom.id K K) (φ i k)).toRingHom = ψ := by
      refine RingHom.ext fun x => ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x y =>
        have h₅ : c (φ i k y) = b y := congrArg (fun q => q y) hc
        show ψ' (x ⊗ₜ φ i k y) = _
        rw [Algebra.TensorProduct.lift_tmul]
        show ψ (x ⊗ₜ 1) * algebraMap V L (c (φ i k y)) = _
        rw [h₅, ← hb, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
    have e₂ : ψ'.toRingHom.comp (Algebra.TensorProduct.includeRight : C i k →ₐ[R] TensorProduct R K (C i k)).toRingHom =
        (algebraMap V L).comp c.toRingHom := by
      refine RingHom.ext fun x => ?_
      show ψ' (1 ⊗ₜ x) = _
      rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
      rfl
    rw [← Category.assoc, sp_comp, ← e₂, ← sp_comp, Category.assoc, hg₃, ← Category.assoc, ← Category.assoc,
      sp_comp, e₁, hψ]
  have hsp : (spMap c.toRingHom ≫ g i k) (IsLocalRing.closedPoint V) ∈ (M i k).sp := by
    show (M i k).Y.hom ((spMap c.toRingHom ≫ g i k) _) = _
    rw [← Scheme.Hom.comp_apply, hb₀]
    haveI : IsLocalHom (algebraMap R V) := by
      apply ((IsLocalRing.local_hom_TFAE (algebraMap R V)).out 0 2).2
      exact hmax.le
    exact IsLocalRing.comap_closedPoint (algebraMap R V)
  obtain ⟨l, hl⟩ := hcov i k _ hsp
  obtain ⟨-, hq, hj⟩ := hN i k l
  have hfac := IsOpenImmersion.lift_fac (q i k l).left _ (range_subset _ _ hl)
  refine ⟨i, k, l, IsOpenImmersion.lift (q i k l).left _ (range_subset _ _ hl), ?_, ?_⟩
  · rw [← Over.w (q i k l), ← Category.assoc, hfac, hb₀]
  · rw [← cancel_mono (q i k l).left, Category.assoc, hfac, Category.assoc, hj, hgen]

end GlobalTheory.SS.WeakNeronEx
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weak_neron_model : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K], PerfectField (IsLocalRing.ResidueField R) → ∀ (A : Over (Sp K)), Smooth A.hom → IsProper A.hom → GlobalTheory.AbLaw.IsProjBy A.hom → ∃ (n : ℕ) (M : Fin n → Model R A), (∀ i, (M i).Irr) ∧ WeakNeron M := by
  atlas_forward_decl GlobalTheory.SS.WeakNeronEx.exists_weakNeron
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
namespace GlobalTheory.SS

theorem exists_neutral_group_model : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → GlobalTheory.AbLaw.IsProjBy A.hom → ∃ (G : Model R A) (_ : GrpObj G.Y), SmConn G.Y ∧ IsMonHom G.e.hom ∧ ∃ c : ℕ, 1 ≤ c ∧ ∀ a : (𝟙_ (Over (Sp K)) ⟶ A), ∃ s : 𝟙_ (Over (Sp R)) ⟶ G.Y, spMap (algebraMap R K) ≫ s.left = (a ^ c).left ≫ G.j := by
  intro R K _ _ _ _ _ hS A _ _ hA hP
  have h1 := hS.1
  have h3 := hS.2.2.1
  have h4 := hS.2.2.2
  obtain ⟨n, M, hI, hW⟩ := GlobalTheory.T.exists_weak_neron_model R K inferInstance A hA.smooth hA.proper hP
  obtain ⟨N, hN, c, hc, hT⟩ := GlobalTheory.T.exists_weakNeronModel_birational_groupLaw R K hS A hA n M hI hW
  obtain ⟨N', hN', hle⟩ := GlobalTheory.T.exists_strict_model_of_birational R K hS A hA N hN
  obtain ⟨G, inst, hG, he, hs⟩ := GlobalTheory.T.exists_grpObj_of_strictBirationalLaw R K hS A hA N' hN'
  obtain ⟨b1, b2, b3, -, -⟩ := GlobalTheory.T.modelMapGenericallyOpenImmersion_calculus R K hS
  refine ⟨G, inst, hG, he, c, hc, fun a => hs (a ^ c) ?_⟩
  have e1 : GenIso N' N (𝟙 A) := b1 A N' N hN'.1.1 hle
  have e2 : GenIso N N' (𝟙 A) := (b3 A A N' N (Iso.refl A)).1 e1
  have e3 := b2 A A A N' N N _ _ hN.1 e1 (hT a)
  have e4 := b2 A A A N' N N' _ _ hN.1 e3 e2
  simpa only [Category.id_comp, Category.comp_id] using e4

end GlobalTheory.SS
end
