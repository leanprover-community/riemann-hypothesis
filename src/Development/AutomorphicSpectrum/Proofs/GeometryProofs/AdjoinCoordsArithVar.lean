import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ZarhinBundleKernelFirstCoordEquations
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartOfSmoothCoords
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStandardSmoothLocalization
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomogeneousFormNonvanishingPoint

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

namespace GlobalTheory.CompanionTheory.Ar.SncRes

theorem isReduced_image_of_quasiCompact {X Y : Scheme.{0}} [IsReduced X] (f : X ⟶ Y) [QuasiCompact f] :
    IsReduced f.image := by
  have : ∀ x : f.image, _root_.IsReduced (f.image.presheaf.stalk x) := fun x => by
    obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := ⊤) (x := f.imageι x) trivial
    have hV : IsAffineOpen (f.imageι ⁻¹ᵁ U) := hU.preimage f.imageι
    have hx' : x ∈ f.imageι ⁻¹ᵁ U := hx
    have : _root_.IsReduced Γ(f.image, f.imageι ⁻¹ᵁ U) :=
      isReduced_of_injective (f.toImage.app (f.imageι ⁻¹ᵁ U)).hom
        (f.toImage_app_injective ⟨U, hU⟩)
    letI := f.image.presheaf.algebra_section_stalk (⟨x, hx'⟩ : f.imageι ⁻¹ᵁ U)
    have := hV.isLocalization_stalk ⟨x, hx'⟩
    exact isReduced_localizationPreserves (hV.primeIdealOf ⟨x, hx'⟩).asIdeal.primeCompl _ ‹_›
  exact isReduced_of_isReduced_stalk f.image

theorem quasiCompact_point {Ω : Type} [Field Ω] [CharZero Ω] {N : ℕ} (x : Fin (N + 1) → Ω) (hx : x ≠ 0) :
    QuasiCompact (point ℚ x hx) := by
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str ℚ N
  have h : QuasiCompact (point ℚ x hx ≫ PSpace.str ℚ N) := by
    rw [point_str]
    infer_instance
  exact .of_comp _ (PSpace.str ℚ N)

theorem closure_reduced_dominant : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (hx : x ≠ 0),
    IsReduced (point ℚ x hx).image ∧ IsDominant (point ℚ x hx).toImage := by
  intro Ω _ _ N x hx
  have := quasiCompact_point x hx
  exact ⟨isReduced_image_of_quasiCompact _, inferInstance⟩

end GlobalTheory.CompanionTheory.Ar.SncRes
end
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_point_image_reduced : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (hx : x ≠ 0), IsReduced (point ℚ x hx).image ∧ IsDominant (point ℚ x hx).toImage := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.SncRes.closure_reduced_dominant
end

section
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncRes

theorem hom_to_spQ_ext {X : Scheme.{0}} (a b : X ⟶ Sp ℚ) : a = b := by
  haveI : IsAffine (Sp ℚ) := inferInstanceAs (IsAffine (Spec (CommRingCat.of ℚ)))
  apply ext_of_isAffine
  apply (cancel_epi (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv).mp
  apply CommRingCat.hom_ext
  exact RingHom.ext_rat _ _

theorem smoothOfRelativeDimension_spMap (B : Type) [CommRing B] [Algebra ℚ B] (e : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension e ℚ B] :
    SmoothOfRelativeDimension e (spMap (algebraMap ℚ B)) := by
  show SmoothOfRelativeDimension e (Spec.map (CommRingCat.ofHom (algebraMap ℚ B)))
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension e)]
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap e).mpr inferInstance)

def valEquiv {Ω : Type} [Field Ω] [CharZero Ω] {Z : Scheme.{0}} (ζ : Sp Ω ⟶ Z) [IsDominant ζ] [IsReduced Z]
    (W : Z.Opens) (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ζ W h).hom = A) :
    Γ(Z, W) ≃+* A :=
  RingEquiv.ofBijective
    ((valMap ζ W h).hom.codRestrict A.toSubring (fun x => by
      have : (valMap ζ W h).hom x ∈ (A : Set Ω) := hA ▸ Set.mem_range_self x
      exact this))
    ⟨fun x y hxy => valMap_injective ζ h (congrArg Subtype.val hxy), fun y => by
      have : (y : Ω) ∈ Set.range (valMap ζ W h).hom := hA ▸ y.2
      obtain ⟨x, hx⟩ := this
      exact ⟨x, Subtype.ext hx⟩⟩

theorem smoothOfRelativeDimension_basicOpen_of_away : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (Z : Scheme.{0}) (ζ : Sp Ω ⟶ Z) [IsDominant ζ] [IsReduced Z] (g : Z ⟶ Sp ℚ) (e : ℕ) (W : Z.Opens) (hW : IsAffineOpen W) (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ζ W h).hom = A) (σ : Γ(Z, W)) (g₀ : A) (hg : (g₀ : Ω) = valR ζ W σ) [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away g₀)], SmoothOfRelativeDimension e ((Z.basicOpen σ).ι ≫ g) := by
  intro Ω _ _ Z ζ _ _ g e W hW h A hA σ g₀ hg _
  haveI := hW.isLocalization_basicOpen σ
  have hE : valEquiv ζ W h A hA σ = g₀ := by
    apply Subtype.ext
    rw [hg]
    show (valMap ζ W h).hom σ = valR ζ W σ
    simp only [valR, valMap, dif_pos h]
    rfl
  let ψ : Γ(Z, Z.basicOpen σ) ≃+* Localization.Away g₀ :=
    IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers σ) (T := Submonoid.powers g₀) _ _ (valEquiv ζ W h A hA)
      (by rw [Submonoid.map_powers]; exact congrArg Submonoid.powers hE)
  have hiso : IsIso (CommRingCat.ofHom (ψ.symm : Localization.Away g₀ →+* Γ(Z, Z.basicOpen σ))) :=
    ⟨⟨CommRingCat.ofHom (ψ : Γ(Z, Z.basicOpen σ) →+* Localization.Away g₀),
      by ext x; simp, by ext x; simp⟩⟩
  let f2 : Spec Γ(Z, Z.basicOpen σ) ⟶ Sp (Localization.Away g₀) :=
    Spec.map (CommRingCat.ofHom (ψ.symm : Localization.Away g₀ →+* Γ(Z, Z.basicOpen σ)))
  haveI : IsIso f2 := by dsimp only [f2]; infer_instance
  have key : (Z.basicOpen σ).ι ≫ g =
      ((hW.basicOpen σ).isoSpec.hom ≫ f2) ≫ spMap (algebraMap ℚ (Localization.Away g₀)) :=
    hom_to_spQ_ext _ _
  rw [key]
  haveI := smoothOfRelativeDimension_spMap (Localization.Away g₀) e
  have := smoothOfRelativeDimension_comp 0 e ((hW.basicOpen σ).isoSpec.hom ≫ f2)
    (spMap (algebraMap ℚ (Localization.Away g₀)))
  rwa [zero_add] at this

end GlobalTheory.CompanionTheory.Ar.SncRes
end
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_smooth_basic_open : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (Z : Scheme.{0}) (ζ : Sp Ω ⟶ Z) [IsDominant ζ] [IsReduced Z] (g : Z ⟶ Sp ℚ) (e : ℕ) (W : Z.Opens) (hW : IsAffineOpen W) (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ζ W h).hom = A) (σ : Γ(Z, W)) (g₀ : A) (hg : (g₀ : Ω) = valR ζ W σ) [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away g₀)], SmoothOfRelativeDimension e ((Z.basicOpen σ).ι ≫ g) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.SncRes.smoothOfRelativeDimension_basicOpen_of_away
end

section
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

namespace GlobalTheory.CompanionTheory.Ar.Coords

theorem dense_point_lift (Ω : Type) [Field Ω] [CharZero Ω] (X X' : Scheme.{0}) (ξ : Sp Ω ⟶ X)
    [IsDominant ξ] (f : X' ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)]
    (hd : Dense ((f ⁻¹ᵁ U : X'.Opens) : Set X')) (hU : ⊤ ≤ ξ ⁻¹ᵁ U) :
    ∃ ζ : Sp Ω ⟶ X', ζ ≫ f = ξ ∧ IsDominant ζ ∧ ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U) := by
  have hr : Set.range ξ ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hU (show x ∈ (⊤ : (Sp Ω).Opens) from trivial)

  let ζ₀ : Sp Ω ⟶ (f ⁻¹ᵁ U).toScheme := IsOpenImmersion.lift U.ι ξ hr ≫ inv (f ∣_ U)
  have hζ₀ : ζ₀ ≫ (f ∣_ U ≫ U.ι) = ξ := by
    simp only [ζ₀, Category.assoc, IsIso.inv_hom_id_assoc, IsOpenImmersion.lift_fac]
  have hT : f ∣_ U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f := morphismRestrict_ι f U
  have hfac : (ζ₀ ≫ (f ⁻¹ᵁ U).ι) ≫ f = ξ := by
    rw [Category.assoc, ← hT, hζ₀]
  refine ⟨ζ₀ ≫ (f ⁻¹ᵁ U).ι, hfac, ⟨?_⟩, ?_⟩
  ·
    rw [DenseRange, dense_iff_inter_open]
    intro W hW hne
    obtain ⟨v, hvW, hvU⟩ := hd.inter_open_nonempty W hW hne
    let T : (f ⁻¹ᵁ U).toScheme ⟶ X := f ∣_ U ≫ U.ι
    have hTo : IsOpenImmersion T := inferInstance
    let W' : Set (f ⁻¹ᵁ U).toScheme := (f ⁻¹ᵁ U).ι ⁻¹' W
    have hW' : IsOpen W' := hW.preimage (f ⁻¹ᵁ U).ι.continuous
    have himg : IsOpen (T '' W') := T.isOpenEmbedding.isOpenMap _ hW'
    have hne' : (T '' W').Nonempty :=
      ⟨T ⟨v, hvU⟩, ⟨v, hvU⟩, by
        change (f ⁻¹ᵁ U).ι ⟨v, hvU⟩ ∈ W
        exact hvW, rfl⟩
    obtain ⟨y, hyT, p, rfl⟩ := (ξ.denseRange).inter_open_nonempty _ himg hne'
    obtain ⟨w, hwW, hw⟩ := hyT
    have hp : T (ζ₀ p) = ξ p := by
      rw [← hζ₀]; simp [T]
    have hwp : w = ζ₀ p := T.isOpenEmbedding.injective (hw.trans hp.symm)
    refine ⟨(ζ₀ ≫ (f ⁻¹ᵁ U).ι) p, ?_, p, rfl⟩
    subst hwp
    simpa [W'] using hwW
  · intro x _
    have hx : ξ x ∈ U := hU (show x ∈ (⊤ : (Sp Ω).Opens) from trivial)
    rw [← hfac] at hx
    exact hx

end GlobalTheory.CompanionTheory.Ar.Coords
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_generic_point_over_iso_open : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X X' : Scheme.{0}) (ξ : Sp Ω ⟶ X) [IsDominant ξ] (f : X' ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)] (hd : Dense ((f ⁻¹ᵁ U : X'.Opens) : Set X')) (hU : ⊤ ≤ ξ ⁻¹ᵁ U), ∃ ζ : Sp Ω ⟶ X', ζ ≫ f = ξ ∧ IsDominant ζ ∧ ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Coords.dense_point_lift
end

section
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

namespace GlobalTheory.CompanionTheory.Ar.TupleCoords

private theorem valR_eq_valMap {A : Type} [CommRing A] {X : Scheme} (x : Sp A ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ (TopologicalSpace.Opens.map x.base).obj U) (f : X.presheaf.obj (op U)) :
    valR x U f = (GlobalTheory.Points.valMap x U h).hom f := by
  simp only [valR, dif_pos h, GlobalTheory.Points.valMap, CommRingCat.hom_comp, RingHom.comp_apply]

theorem exists_tuple_eq_point : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (r : ℕ) (p : Sp Ω ⟶ PSpace ℚ r),
    ∃ (x' : Fin (r + 1) → Ω) (hx' : x' ≠ 0), p = point ℚ x' hx' := by
  intro Ω _ _ r p
  let y0 : Sp Ω := (default : PrimeSpectrum Ω)
  obtain ⟨i, hi0⟩ := GlobalTheory.ProjSpace.exists_mem_chart ℚ r (p.base y0)
  have hi : ⊤ ≤ (TopologicalSpace.Opens.map p.base).obj (GlobalTheory.ProjSpace.chart ℚ r i) := by
    intro y _
    have hy : y = y0 := Subsingleton.elim (α := PrimeSpectrum Ω) y y0
    subst hy
    exact hi0
  set t : Fin (r + 1) → Ω := fun j => valR p (GlobalTheory.ProjSpace.chart ℚ r i) (GlobalTheory.ProjSpace.ratio ℚ r i j)
    with ht_def
  have hti : t i = 1 := by
    simp only [ht_def, valR_eq_valMap p _ hi]
    rw [show GlobalTheory.ProjSpace.ratio ℚ r i i = 1 from GlobalTheory.ProjSpace.ratioOn_self]
    exact map_one _
  have hti0 : t i ≠ 0 := by rw [hti]; exact one_ne_zero
  have htne : t ≠ 0 := fun h => hti0 (congr_fun h i)
  refine ⟨t, htne, ?_⟩
  have hq : ⊤ ≤ (TopologicalSpace.Opens.map (point ℚ t htne).base).obj (GlobalTheory.ProjSpace.chart ℚ r i) :=
    (GlobalTheory.TuplePoint.le_point_preimage_iff i).2 hti0
  refine GlobalTheory.Points.ext_of_valR (GlobalTheory.ProjSpace.isAffineOpen_chart ℚ r i) hi hq ?_
  intro f
  obtain ⟨P, rfl⟩ := GlobalTheory.ProjSpace.aeval_ratio_surjective ℚ r i f
  rw [valR_eq_valMap p _ hi, valR_eq_valMap _ _ hq]
  have key : (GlobalTheory.Points.valMap p _ hi).hom.comp (MvPolynomial.aeval (R := ℚ) (GlobalTheory.ProjSpace.ratio ℚ r i)).toRingHom
      = (GlobalTheory.Points.valMap (point ℚ t htne) _ hq).hom.comp
          (MvPolynomial.aeval (R := ℚ) (GlobalTheory.ProjSpace.ratio ℚ r i)).toRingHom := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext_rat _ _) ?_
    intro j
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
    rw [← valR_eq_valMap p _ hi, ← valR_eq_valMap _ _ hq,
      GlobalTheory.TuplePoint.valR_point_ratio hti0 j, hti, div_one]
  exact RingHom.congr_fun key P

end GlobalTheory.CompanionTheory.Ar.TupleCoords
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_point_coords_exist : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (r : ℕ) (p : Sp Ω ⟶ PSpace ℚ r), ∃ (x' : Fin (r + 1) → Ω) (hx' : x' ≠ 0), p = point ℚ x' hx' := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.TupleCoords.exists_tuple_eq_point
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncRes

theorem valR_mem_adjoin_of_affine {Ω : Type} [Field Ω] [CharZero Ω] {X : Scheme.{0}} (ξ : Sp Ω ⟶ X)
    {W₀ : X.Opens} (hW₀ : IsAffineOpen W₀) (h₀ : ⊤ ≤ ξ ⁻¹ᵁ W₀) (A : Subalgebra ℚ Ω)
    (hA : Set.range (valMap ξ W₀ h₀).hom = A) {O : X.Opens} (hO : ⊤ ≤ ξ ⁻¹ᵁ O) (t : Γ(X, O)) :
    valR ξ O t ∈ IntermediateField.adjoin ℚ (A : Set Ω) := by
  have hmem : ∀ a : Γ(X, W₀), valR ξ W₀ a ∈ IntermediateField.adjoin ℚ (A : Set Ω) := fun a => by
    apply IntermediateField.subset_adjoin
    rw [valR_eq ξ W₀ h₀, ← hA]
    exact ⟨a, rfl⟩
  let z : Sp Ω := IsLocalRing.closedPoint Ω
  obtain ⟨b, hbO, hxb⟩ := hW₀.exists_basicOpen_le (V := O) ⟨ξ z, hO trivial⟩ (h₀ trivial)
  have hD : ⊤ ≤ ξ ⁻¹ᵁ X.basicOpen b := fun y _ => by
    rw [Subsingleton.elim y z]
    exact hxb
  have hloc := hW₀.isLocalization_basicOpen b
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers b)
    ((X.presheaf.map (homOfLE hbO).op).hom t)
  have hres : ∀ c : Γ(X, W₀), valR ξ (X.basicOpen b) (algebraMap Γ(X, W₀) Γ(X, X.basicOpen b) c) =
      valR ξ W₀ c := fun c => valR_res ξ (X.basicOpen_le b) hD c
  have hv := congrArg (valR ξ (X.basicOpen b)) h
  simp only at hv
  rw [valR_mul ξ _ hD, valR_res ξ hbO hD, hres, hres, valR_pow ξ _ h₀] at hv
  have hunit : valR ξ W₀ b ≠ 0 := ((le_preimage_basicOpen_iff ξ h₀ b).1 hD).ne_zero
  have e : valR ξ O t = valR ξ W₀ a / valR ξ W₀ b ^ n := by
    rw [eq_div_iff (pow_ne_zero n hunit)]
    exact hv
  rw [e]
  exact div_mem (hmem a) (pow_mem (hmem b) n)

theorem valR_appIso_inv {C : Type} [CommRing C] {X Y : Scheme.{0}} (r : Y ⟶ X) [IsOpenImmersion r] (y : Sp C ⟶ Y)
    (V : Y.Opens) (h : ⊤ ≤ y ⁻¹ᵁ V) (t : Γ(Y, V)) :
    valR (y ≫ r) (r ''ᵁ V) ((r.appIso V).inv.hom t) = valR y V t := by
  rw [← valR_appLE y r (r.preimage_image_eq V).ge h, ← Scheme.Hom.appIso_hom']
  congr 1
  exact congrArg (fun φ => φ.hom t) (r.appIso V).inv_hom_id

theorem valR_mem_adjoin_of_modification : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X X' : Scheme.{0}) (ξ : Sp Ω ⟶ X) [IsDominant ξ] [IsReduced X] (f : X' ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)] (ζ : Sp Ω ⟶ X') (hζ : ζ ≫ f = ξ) (hU : ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U)) (W₀ : X.Opens) (hW₀ : IsAffineOpen W₀) (h₀ : ⊤ ≤ ξ ⁻¹ᵁ W₀) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ξ W₀ h₀).hom = A) (W' : X'.Opens) (h' : ⊤ ≤ ζ ⁻¹ᵁ W') (s : Γ(X', W')), valR ζ W' s ∈ IntermediateField.adjoin ℚ (A : Set Ω) := by
  intro Ω _ _ X X' ξ _ _ f U _ ζ hζ hU W₀ hW₀ h₀ A hA W' h' s
  haveI : IsOpenImmersion ((f ⁻¹ᵁ U).ι ≫ f) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have hr : Set.range ζ ⊆ Set.range (f ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact hU (Set.mem_univ y)
  let y : Sp Ω ⟶ (f ⁻¹ᵁ U).toScheme := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι ζ hr
  have hy : y ≫ (f ⁻¹ᵁ U).ι = ζ := IsOpenImmersion.lift_fac _ _ _
  have hyr : y ≫ ((f ⁻¹ᵁ U).ι ≫ f) = ξ := by rw [← Category.assoc, hy, hζ]
  have hV : ⊤ ≤ y ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ⁻¹ᵁ W') := fun z hz => by
    have : z ∈ ζ ⁻¹ᵁ W' := h' hz
    rw [← hy] at this
    exact this
  have e1 : valR ζ W' s = valR y _ (((f ⁻¹ᵁ U).ι.app W').hom s) := by
    conv_lhs => rw [← hy]
    exact valR_comp y _ W' s
  rw [e1, ← valR_appIso_inv ((f ⁻¹ᵁ U).ι ≫ f) y _ hV]
  subst hyr
  exact valR_mem_adjoin_of_affine _ hW₀ h₀ A hA (fun z hz => ((( (f ⁻¹ᵁ U).ι ≫ f).preimage_image_eq _).ge (hV hz) : _)) _

end GlobalTheory.CompanionTheory.Ar.SncRes
end
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_values_in_adjoined_field : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X X' : Scheme.{0}) (ξ : Sp Ω ⟶ X) [IsDominant ξ] [IsReduced X] (f : X' ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)] (ζ : Sp Ω ⟶ X') (hζ : ζ ≫ f = ξ) (hU : ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U)) (W₀ : X.Opens) (hW₀ : IsAffineOpen W₀) (h₀ : ⊤ ≤ ξ ⁻¹ᵁ W₀) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ξ W₀ h₀).hom = A) (W' : X'.Opens) (h' : ⊤ ≤ ζ ⁻¹ᵁ W') (s : Γ(X', W')), valR ζ W' s ∈ IntermediateField.adjoin ℚ (A : Set Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncRes.valR_mem_adjoin_of_modification | exact GlobalTheory.CompanionTheory.Ar.SncRes.valR_mem_adjoin_of_modification | (intros; apply GlobalTheory.CompanionTheory.Ar.SncRes.valR_mem_adjoin_of_modification <;> assumption)
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.Ar.SncRes.ProdChart

theorem isAffineOpen_fst_inf_snd {S X Y : Scheme.{0}} [IsAffine S] (f : X ⟶ S) (g : Y ⟶ S) {U : X.Opens}
    {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := by
  haveI : IsAffine U.toScheme := hU
  haveI : IsAffine V.toScheme := hV
  let m := pullback.map (U.ι ≫ f) (V.ι ≫ g) f g U.ι V.ι (𝟙 S) (by simp) (by simp)
  haveI : IsOpenImmersion m :=
    MorphismProperty.pullback_map (P := @IsOpenImmersion) inferInstance inferInstance rfl rfl
  have e : m.opensRange = pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V := by
    ext1
    refine (Scheme.Pullback.range_map _ _ _ _ _ _ _ _ _).trans ?_
    simp
  rw [← e]
  exact isAffineOpen_opensRange m

theorem spec_rat_ext {C : Type} [CommRing C] (u v : Sp C ⟶ Sp ℚ) : u = v := by
  rw [← Spec.map_preimage u, ← Spec.map_preimage v]
  congr 1
  ext1
  exact Subsingleton.elim _ _

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {X Y : Scheme.{0}} (f : X ⟶ Sp ℚ) (g : Y ⟶ Sp ℚ)
  {U : X.Opens} {V : Y.Opens}

theorem val_mem_of_components (hU : IsAffineOpen U) (hV : IsAffineOpen V) (C : Subalgebra ℚ Ω)
    (p : Sp Ω ⟶ pullback f g) (hA : ⊤ ≤ (p ≫ pullback.fst f g) ⁻¹ᵁ U) (hB : ⊤ ≤ (p ≫ pullback.snd f g) ⁻¹ᵁ V)
    (mA : ∀ s, (valMap (p ≫ pullback.fst f g) U hA).hom s ∈ C)
    (mB : ∀ s, (valMap (p ≫ pullback.snd f g) V hB).hom s ∈ C)
    (h : ⊤ ≤ p ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V))
    (t : Γ(pullback f g, pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)) :
    (valMap p _ h).hom t ∈ C := by
  let ι : CommRingCat.of C ⟶ CommRingCat.of Ω := CommRingCat.ofHom C.val.toRingHom
  let φA : Γ(X, U) ⟶ CommRingCat.of C := CommRingCat.ofHom ((valMap _ U hA).hom.codRestrict C mA)
  let φB : Γ(Y, V) ⟶ CommRingCat.of C := CommRingCat.ofHom ((valMap _ V hB).hom.codRestrict C mB)
  have eA : φA ≫ ι = valMap _ U hA := rfl
  have eB : φB ≫ ι = valMap _ V hB := rfl
  have hfg : (Spec.map φA ≫ hU.fromSpec) ≫ f = (Spec.map φB ≫ hV.fromSpec) ≫ g := spec_rat_ext _ _
  let q : Sp C ⟶ pullback f g := pullback.lift _ _ hfg
  have hq : Spec.map ι ≫ q = p := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, ← Spec.map_comp, eA,
        specMap_valMap_fromSpec hU]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, ← Spec.map_comp, eB,
        specMap_valMap_fromSpec hV]
  have h₃ : ⊤ ≤ (q ≫ pullback.fst f g) ⁻¹ᵁ U := by
    rw [pullback.lift_fst]
    exact le_preimage_specMap_fromSpec hU φA
  have h₄ : ⊤ ≤ (q ≫ pullback.snd f g) ⁻¹ᵁ V := by
    rw [pullback.lift_snd]
    exact le_preimage_specMap_fromSpec hV φB
  have hqW : ⊤ ≤ q ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) :=
    fun y hy => ⟨h₃ hy, h₄ hy⟩
  have key : ∀ h' : ⊤ ≤ (Spec.map ι ≫ q) ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V),
      valMap (Spec.map ι ≫ q) _ h' = valMap q _ hqW ≫ ι := fun h' => by
    rw [← appLE_valMap (Spec.map ι) q hqW (le_preimage_top _) h', valMap_specMap]
    simp only [valMap, Category.assoc]
  have h' : ⊤ ≤ (Spec.map ι ≫ q) ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := by
    rw [hq]
    exact h
  have e : (valMap p _ h).hom t = (valMap (Spec.map ι ≫ q) _ h').hom t := by
    rw [← valR_eq, ← valR_eq, hq]
  rw [e, key]
  exact ((valMap q _ hqW).hom t).2

theorem closed_prod_chart {Z : Scheme.{0}} (j : Z ⟶ pullback f g) [IsClosedImmersion j] (ζ : Sp Ω ⟶ Z)
    (pX : Sp Ω ⟶ X) (pY : Sp Ω ⟶ Y) (h₁ : ζ ≫ j ≫ pullback.fst f g = pX) (h₂ : ζ ≫ j ≫ pullback.snd f g = pY)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hA : ⊤ ≤ pX ⁻¹ᵁ U) (hB : ⊤ ≤ pY ⁻¹ᵁ V) (R₁ R₂ : Set Ω)
    (e₁ : Set.range (valMap pX U hA).hom = Algebra.adjoin ℚ R₁)
    (e₂ : Set.range (valMap pY V hB).hom = Algebra.adjoin ℚ R₂) :
    IsAffineOpen ((j ≫ pullback.fst f g) ⁻¹ᵁ U ⊓ (j ≫ pullback.snd f g) ⁻¹ᵁ V) ∧
      ∃ h : ⊤ ≤ ζ ⁻¹ᵁ ((j ≫ pullback.fst f g) ⁻¹ᵁ U ⊓ (j ≫ pullback.snd f g) ⁻¹ᵁ V),
        Set.range (valMap ζ _ h).hom = Algebra.adjoin ℚ (R₁ ∪ R₂) := by
  subst h₁ h₂
  have hW := isAffineOpen_fst_inf_snd f g hU hV
  have hZ : ⊤ ≤ ζ ⁻¹ᵁ ((j ≫ pullback.fst f g) ⁻¹ᵁ U ⊓ (j ≫ pullback.snd f g) ⁻¹ᵁ V) :=
    fun y hy => ⟨hA hy, hB hy⟩
  have hp : ⊤ ≤ (ζ ≫ j) ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := hZ
  have hA' : ⊤ ≤ ((ζ ≫ j) ≫ pullback.fst f g) ⁻¹ᵁ U := by rwa [Category.assoc]
  have hB' : ⊤ ≤ ((ζ ≫ j) ≫ pullback.snd f g) ⁻¹ᵁ V := by rwa [Category.assoc]
  have vA : ∀ s, (valMap ((ζ ≫ j) ≫ pullback.fst f g) U hA').hom s = (valMap (ζ ≫ j ≫ pullback.fst f g) U hA).hom s := by
    intro s
    rw [← valR_eq, ← valR_eq, Category.assoc]
  have vB : ∀ s, (valMap ((ζ ≫ j) ≫ pullback.snd f g) V hB').hom s = (valMap (ζ ≫ j ≫ pullback.snd f g) V hB).hom s := by
    intro s
    rw [← valR_eq, ← valR_eq, Category.assoc]
  refine ⟨hW.preimage j, hZ, Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨s, rfl⟩
    obtain ⟨t, rfl⟩ := j.app_surjective _ hW s
    have e : (valMap (ζ ≫ j) _ hp).hom t = (valMap ζ _ hZ).hom ((j.app _).hom t) :=
      (valR_eq _ _ hp t).symm.trans ((valR_comp ζ j _ t).trans (valR_eq ζ (j ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)) hZ _))
    rw [← e]
    refine val_mem_of_components f g hU hV _ (ζ ≫ j) hA' hB' (fun s => ?_) (fun s => ?_) hp t
    · rw [vA]
      have m : (valMap (ζ ≫ j ≫ pullback.fst f g) U hA).hom s ∈ (Algebra.adjoin ℚ R₁ : Set Ω) := by
        rw [← e₁]
        exact Set.mem_range_self s
      exact Algebra.adjoin_mono Set.subset_union_left m
    · rw [vB]
      have m : (valMap (ζ ≫ j ≫ pullback.snd f g) V hB).hom s ∈ (Algebra.adjoin ℚ R₂ : Set Ω) := by
        rw [← e₂]
        exact Set.mem_range_self s
      exact Algebra.adjoin_mono Set.subset_union_right m
  · let F : Z ⟶ Sp ℚ := j ≫ pullback.fst f g ≫ f
    let S : Subalgebra ℚ Ω :=
      { (valMap ζ _ hZ).hom.range with
        algebraMap_mem' := fun c => ⟨(GlobalTheory.QCoh.Qcqs.baseRingHom F _).hom c,
          RingHom.congr_fun (Subsingleton.elim
            ((valMap ζ _ hZ).hom.comp (GlobalTheory.QCoh.Qcqs.baseRingHom F _).hom) (algebraMap ℚ Ω)) c⟩ }
    have hS : Algebra.adjoin ℚ (R₁ ∪ R₂) ≤ S := by
      refine Algebra.adjoin_le (Set.union_subset ?_ ?_)
      · intro w hw
        obtain ⟨s, rfl⟩ : w ∈ Set.range (valMap (ζ ≫ j ≫ pullback.fst f g) U hA).hom :=
          e₁.symm ▸ (Algebra.subset_adjoin hw : w ∈ (Algebra.adjoin ℚ R₁ : Set Ω))
        exact ⟨((j ≫ pullback.fst f g).appLE U _ inf_le_left).hom s,
          congrArg (fun φ => φ.hom s) (appLE_valMap ζ (j ≫ pullback.fst f g) inf_le_left hZ hA)⟩
      · intro w hw
        obtain ⟨s, rfl⟩ : w ∈ Set.range (valMap (ζ ≫ j ≫ pullback.snd f g) V hB).hom :=
          e₂.symm ▸ (Algebra.subset_adjoin hw : w ∈ (Algebra.adjoin ℚ R₂ : Set Ω))
        exact ⟨((j ≫ pullback.snd f g).appLE V _ inf_le_right).hom s,
          congrArg (fun φ => φ.hom s) (appLE_valMap ζ (j ≫ pullback.snd f g) inf_le_right hZ hB)⟩
    exact hS

theorem prod_chart (Ω : Type) [Field Ω] [CharZero Ω] (N r : ℕ) (Z : Scheme.{0})
    (j : Z ⟶ pullback (PSpace.str ℚ N) (PSpace.str ℚ r)) [IsClosedImmersion j] (ζ : Sp Ω ⟶ Z)
    (x : Fin (N + 1) → Ω) (hx : x ≠ 0) (x' : Fin (r + 1) → Ω) (hx' : x' ≠ 0)
    (h₁ : ζ ≫ j ≫ pullback.fst _ _ = point ℚ x hx) (h₂ : ζ ≫ j ≫ pullback.snd _ _ = point ℚ x' hx')
    (a : Fin (N + 1)) (l : Fin (r + 1)) (ha : x a ≠ 0) (hl : x' l ≠ 0) :
    IsAffineOpen ((j ≫ pullback.fst _ _) ⁻¹ᵁ chart ℚ N a ⊓ (j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l) ∧
      ∃ h : ⊤ ≤ ζ ⁻¹ᵁ ((j ≫ pullback.fst _ _) ⁻¹ᵁ chart ℚ N a ⊓ (j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l),
        Set.range (valMap ζ _ h).hom =
          Algebra.adjoin ℚ (Set.range (fun k => x k / x a) ∪ Set.range (fun k => x' k / x' l)) :=
  closed_prod_chart _ _ j ζ _ _ h₁ h₂ (isAffineOpen_chart ℚ N a) (isAffineOpen_chart ℚ r l)
    ((le_point_preimage_iff a).2 ha) ((le_point_preimage_iff l).2 hl) _ _
    (range_valMap_point _) (range_valMap_point _)

end GlobalTheory.CompanionTheory.Ar.SncRes.ProdChart
end
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segre_product_affine_chart : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (N r : ℕ) (Z : Scheme.{0}) (j : Z ⟶ pullback (PSpace.str ℚ N) (PSpace.str ℚ r)) [IsClosedImmersion j] (ζ : Sp Ω ⟶ Z) (x : Fin (N + 1) → Ω) (hx : x ≠ 0) (x' : Fin (r + 1) → Ω) (hx' : x' ≠ 0) (h₁ : ζ ≫ j ≫ pullback.fst _ _ = point ℚ x hx) (h₂ : ζ ≫ j ≫ pullback.snd _ _ = point ℚ x' hx') (a : Fin (N + 1)) (l : Fin (r + 1)) (ha : x a ≠ 0) (hl : x' l ≠ 0), IsAffineOpen ((j ≫ pullback.fst _ _) ⁻¹ᵁ chart ℚ N a ⊓ (j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l) ∧ ∃ h : ⊤ ≤ ζ ⁻¹ᵁ ((j ≫ pullback.fst _ _) ⁻¹ᵁ chart ℚ N a ⊓ (j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l), Set.range (valMap ζ _ h).hom = Algebra.adjoin ℚ (Set.range (fun k => x k / x a) ∪ Set.range (fun k => x' k / x' l)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.SncRes.ProdChart.prod_chart
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_chart_of_smooth_coords : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (Z : Scheme.{0}) (ζ : Sp Ω ⟶ Z) [IsDominant ζ] [IsReduced Z] (g : Z ⟶ Sp ℚ) (e : ℕ) (T : Set Z) (hsm : SmoothOfRelativeDimension e g) (hc : HasSncCoords g e T) (W : Z.Opens) (hW : IsAffineOpen W) (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ζ W h).hom = A) (σ : Γ(Z, W)) (hσ : ∀ t ∈ W, t ∈ T ↔ t ∉ Z.basicOpen σ), SncChart A e (valR ζ W σ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncRes.sncChart_of_coords | exact GlobalTheory.CompanionTheory.Ar.SncRes.sncChart_of_coords | (intros; apply GlobalTheory.CompanionTheory.Ar.SncRes.sncChart_of_coords <;> assumption)
end

section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standard_smooth_localization : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ) (hA : IsArithVar (mCoordIdeal y) (e + 1)) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1)) (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0), ∃ s : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩), s ≠ 0 ∧ Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SegreChart.exists_away_standardSmooth | exact GlobalTheory.CompanionTheory.Ar.SegreChart.exists_away_standardSmooth | (intros; apply GlobalTheory.CompanionTheory.Ar.SegreChart.exists_away_standardSmooth <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

theorem aeval_const_mul {σ R : Type} [Fintype σ] [CommRing R] [Algebra ℤ R] {G : MvPolynomial σ ℤ} {n : ℕ}
    (hG : G.IsHomogeneous n) (κ : R) (a : σ → R) :
    aeval (fun j => κ * a j) G = κ ^ n * aeval a G := by
  simp only [aeval_def, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = n := by
    have h := hG (mem_support_iff.1 hm)
    have e : Finsupp.weight (1 : σ → ℕ) m = ∑ i, m i := by
      simp [Finsupp.weight_apply, Finsupp.sum_fintype]
    rw [← e]
    exact h
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem exists_homog {σ Ω : Type} [Field Ω] [CharZero Ω] (r : σ → Ω) (c₀ : σ) (h1 : r c₀ = 1)
    (t : Algebra.adjoin ℚ (Set.range r)) :
    ∃ (m : ℤ) (n : ℕ) (G : MvPolynomial σ ℤ), m ≠ 0 ∧ G.IsHomogeneous n ∧
      aeval r G = (m : Ω) * (t : Ω) := by
  obtain ⟨t, ht⟩ := t
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨1, 1, X j, one_ne_zero, isHomogeneous_X _ _, by simp⟩
  | algebraMap q =>
    refine ⟨q.den, 0, C q.num, by exact_mod_cast q.den_nz, isHomogeneous_C _ _, ?_⟩
    have hd : (q.den : Ω) ≠ 0 := by exact_mod_cast q.den_nz
    simp only [map_intCast, eq_intCast, eq_ratCast, Int.cast_natCast]
    rw [Rat.cast_def]
    field_simp
  | add x y hx hy ihx ihy =>
    obtain ⟨m₁, n₁, G₁, hm₁, hG₁, e₁⟩ := ihx
    obtain ⟨m₂, n₂, G₂, hm₂, hG₂, e₂⟩ := ihy
    refine ⟨m₁ * m₂, n₁ + n₂, C m₂ * X c₀ ^ n₂ * G₁ + C m₁ * X c₀ ^ n₁ * G₂, mul_ne_zero hm₁ hm₂, ?_, ?_⟩
    · refine MvPolynomial.IsHomogeneous.add ?_ ?_
      · have := ((isHomogeneous_C σ m₂).mul ((isHomogeneous_X ℤ c₀).pow n₂)).mul hG₁
        convert this using 1
        ring
      · have := ((isHomogeneous_C σ m₁).mul ((isHomogeneous_X ℤ c₀).pow n₁)).mul hG₂
        convert this using 1
        ring
    · simp only [map_add, map_mul, map_pow, aeval_X, h1, one_pow, mul_one, eq_intCast, map_intCast, e₁, e₂]
      push_cast
      ring
  | mul x y hx hy ihx ihy =>
    obtain ⟨m₁, n₁, G₁, hm₁, hG₁, e₁⟩ := ihx
    obtain ⟨m₂, n₂, G₂, hm₂, hG₂, e₂⟩ := ihy
    refine ⟨m₁ * m₂, n₁ + n₂, G₁ * G₂, mul_ne_zero hm₁ hm₂, hG₁.mul hG₂, ?_⟩
    simp only [map_mul, e₁, e₂]
    push_cast
    ring

theorem smooth_away_mul {B : Type} [CommRing B] [Algebra ℚ B] (s u : B) (e : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s)] :
    Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away (s * u)) := by
  let S := Localization.Away s
  let T := Localization.Away (algebraMap B S u)
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 S T :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away (algebraMap B S u)
  have h := Algebra.IsStandardSmoothOfRelativeDimension.trans e 0 ℚ S T
  rw [zero_add] at h
  haveI : IsLocalization.Away (s * u) T := IsLocalization.Away.mul' S T s u
  let f : T ≃ₐ[B] Localization.Away (s * u) :=
    IsLocalization.algEquiv (Submonoid.powers (s * u)) T (Localization.Away (s * u))
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv e (f.restrictScalars ℚ)

theorem eval_map_int {σ : Type} (w : σ → ℂ) (f : MvPolynomial σ ℤ) :
    eval w (map (Int.castRingHom ℂ) f) = aeval w f := by
  rw [aeval_def, eval₂_eq_eval_map, algebraMap_int_eq]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {N : ℕ} (y : (Σ k, ι k) → Ω) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1))

theorem blockRatio_eq (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) (p : Σ k, ι k) [DecidableEq K] :
    y p / y ⟨p.1, E c₀ p.1⟩ =
      (∏ k, y ⟨k, E (E.symm (Function.update (E c₀) p.1 p.2)) k⟩) / ∏ k, y ⟨k, E c₀ k⟩ := by
  obtain ⟨k₀, i⟩ := p
  simp only [Equiv.apply_symm_apply]
  have h0 : (∏ k, y ⟨k, E c₀ k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  rw [div_eq_div_iff (hc k₀) h0,
    ← Finset.mul_prod_erase Finset.univ (fun k => y ⟨k, E c₀ k⟩) (Finset.mem_univ k₀),
    ← Finset.mul_prod_erase Finset.univ (fun k => y ⟨k, Function.update (E c₀) k₀ i k⟩) (Finset.mem_univ k₀)]
  have e : ∏ k ∈ Finset.univ.erase k₀, y ⟨k, Function.update (E c₀) k₀ i k⟩ =
      ∏ k ∈ Finset.univ.erase k₀, y ⟨k, E c₀ k⟩ :=
    Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [e, Function.update_self]
  ring

theorem aeval_blockRatio_mem [CharZero Ω] (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) (β : MRing ι) :
    aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β ∈
      Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) := by
  classical
  induction β using MvPolynomial.induction_on with
  | C n => simpa using intCast_mem _ n
  | add p q hp hq => simpa using add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul, aeval_X]
    refine mul_mem hp (Algebra.subset_adjoin ⟨E.symm (Function.update (E c₀) i.1 i.2), ?_⟩)
    exact (blockRatio_eq y E c₀ hc i).symm

theorem aeval_eq_prod_mul (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) {β : MRing ι} {b : K → ℕ} (hb : IsMultiHomog β b) :
    aeval y β = (∏ k, y ⟨k, E c₀ k⟩ ^ b k) *
      aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β := by
  have h := GlobalTheory.CompanionTheory.Ar.aeval_blockScale hb (fun k => y ⟨k, E c₀ k⟩) (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩)
  have e : (fun p : Σ k, ι k => y ⟨p.1, E c₀ p.1⟩ * (y p / y ⟨p.1, E c₀ p.1⟩)) = y :=
    funext fun p => mul_div_cancel₀ _ (hc p.1)
  rwa [e] at h

theorem mConeMap_segre (j : Fin (N + 1)) :
    mConeMap y (∏ k, (X ⟨k, E j k⟩ : MRing ι)) =
      (∏ k, (X k : MvPolynomial K Ω)) * C (∏ k, y ⟨k, E j k⟩) := by
  simp only [map_prod, mConeMap, aeval_X, Finset.prod_mul_distrib]
  rw [mul_comm]

theorem vanish_of_value (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) {β : MRing ι} {b : K → ℕ} (hb : IsMultiHomog β b)
    {n : ℕ} {m : ℤ} {G : MvPolynomial (Fin (N + 1)) ℤ} (hG : G.IsHomogeneous n)
    (hval : aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) G =
      (m : Ω) * aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) (hβ : evC z β = 0) :
    (∏ k, z ⟨k, E c₀ k⟩) = 0 ∨ aeval (fun j => ∏ k, z ⟨k, E j k⟩) G = 0 := by
  have h0 : (∏ k, y ⟨k, E c₀ k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  have hx : aeval (fun j => ∏ k, y ⟨k, E j k⟩) G * ∏ k, y ⟨k, E c₀ k⟩ ^ b k =
      (m : Ω) * aeval y β * (∏ k, y ⟨k, E c₀ k⟩) ^ n := by
    have e : (fun j => ∏ k, y ⟨k, E j k⟩) = fun j => (∏ k, y ⟨k, E c₀ k⟩) *
        ((∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) :=
      funext fun j => (mul_div_cancel₀ _ h0).symm
    rw [e, aeval_const_mul hG, hval, aeval_eq_prod_mul y E c₀ hc hb]
    ring
  let P₁ : MRing ι := aeval (fun j => ∏ k, (X ⟨k, E j k⟩ : MRing ι)) G * ∏ k, (X ⟨k, E c₀ k⟩ : MRing ι) ^ b k
  let P₂ : MRing ι := C m * β * (∏ k, (X ⟨k, E c₀ k⟩ : MRing ι)) ^ n
  have hmem : P₁ - P₂ ∈ mCoordIdeal y := by
    refine RingHom.mem_ker.2 ?_
    have hG' : mConeMap y (aeval (fun j => ∏ k, (X ⟨k, E j k⟩ : MRing ι)) G) =
        (∏ k, (X k : MvPolynomial K Ω)) ^ n * C (aeval (fun j => ∏ k, y ⟨k, E j k⟩) G) := by
      rw [comp_aeval_apply]
      simp only [mConeMap_segre]
      rw [aeval_const_mul hG]
      congr 1
      exact (comp_aeval_apply _ (IsScalarTower.toAlgHom ℤ Ω (MvPolynomial K Ω)) G).symm
    have hX : mConeMap y (∏ k, (X ⟨k, E c₀ k⟩ : MRing ι) ^ b k) =
        (∏ k, (X k : MvPolynomial K Ω) ^ b k) * C (∏ k, y ⟨k, E c₀ k⟩ ^ b k) := by
      simp only [map_prod, map_pow, mConeMap, aeval_X, mul_pow, Finset.prod_mul_distrib]
      rw [mul_comm]
    have hC : mConeMap y (C m) = C (m : Ω) := by
      simp [mConeMap]
    have hS := mConeMap_segre y E c₀
    simp only [P₁, P₂, map_sub, map_mul, map_pow, hG', hX, hC, hS,
      GroundTheory.Heights₂.Heights.LowerBoundFree.mConeMap_of_isMultiHomog y hb]
    rw [sub_eq_zero]
    have := congrArg (C : Ω →+* MvPolynomial K Ω) hx
    simp only [map_mul, map_pow] at this
    calc _ = (∏ k, (X k : MvPolynomial K Ω)) ^ n * (∏ k, (X k : MvPolynomial K Ω) ^ b k) *
          (C (aeval (fun j => ∏ k, y ⟨k, E j k⟩) G) * C (∏ k, y ⟨k, E c₀ k⟩ ^ b k)) := by ring
      _ = _ := by rw [this]; ring
  have hzero := hz.2 _ hmem
  have hev : aeval z (P₁ - P₂) = 0 := by rw [← eval_map_int]; exact hzero
  have hβ' : aeval z β = 0 := by rw [← eval_map_int]; exact hβ
  have hP : aeval (fun j => ∏ k, z ⟨k, E j k⟩) G * ∏ k, z ⟨k, E c₀ k⟩ ^ b k = 0 := by
    simp only [P₁, P₂, map_sub, map_mul, map_pow, map_prod, aeval_X, hβ', comp_aeval_apply] at hev
    simpa using hev
  rcases mul_eq_zero.1 hP with h | h
  · exact Or.inr h
  · obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h
    refine Or.inl (Finset.prod_eq_zero_iff.2 ⟨k, Finset.mem_univ _, ?_⟩)
    by_contra h'
    exact pow_ne_zero _ h' hk

end GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes in

theorem GlobalTheory.CompanionTheory.Ar.SncRes.exists_segre_form : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (b : K → ℕ) (hb : IsMultiHomog β b) (hβ : β ∉ mCoordIdeal y) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1)) (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) (s : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩)) (hs : s ≠ 0) [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s)], ∃ (d : ℕ) (Gz : MvPolynomial (Fin (N + 1)) ℤ) (g₀ : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩)), Gz.IsHomogeneous (d + 1) ∧ (X c₀ : MvPolynomial _ ℤ) ∣ Gz ∧ (g₀ : Ω) = aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) Gz ∧ g₀ ≠ 0 ∧ Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away g₀) ∧ ∀ z ∈ mcPts (mCoordIdeal y), evC z β = 0 → eval (fun j => ∏ k, z ⟨k, E j k⟩) (map (Int.castRingHom ℂ) Gz) = 0 := by
  intro Ω _ _ K _ ι _ y e β b hb hβ N E c₀ hc s hs _
  have h0 : (∏ k, y ⟨k, E c₀ k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  have h1 : (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) c₀ = 1 := div_self h0
  obtain ⟨m₁, n₁, G₁, hm₁, hG₁, e₁⟩ := SegreForm.exists_homog _ c₀ h1 s
  obtain ⟨m₂, n₂, G₂, hm₂, hG₂, e₂⟩ := SegreForm.exists_homog _ c₀ h1
    ⟨_, SegreForm.aeval_blockRatio_mem y E c₀ hc β⟩
  have hbt : aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β ≠ 0 := by
    intro h
    apply hβ
    rw [form_mem_mCoordIdeal_iff y hb, SegreForm.aeval_eq_prod_mul y E c₀ hc hb, h, mul_zero]
  have hm₁' : (m₁ : Ω) ≠ 0 := by exact_mod_cast hm₁
  have hm₂' : (m₂ : Ω) ≠ 0 := by exact_mod_cast hm₂
  have hs' : (s : Ω) ≠ 0 := fun h => hs (Subtype.ext h)
  refine ⟨n₁ + n₂, X c₀ * G₁ * G₂,
    s * (((m₁ * m₂ : ℤ) : Algebra.adjoin ℚ _) * ⟨_, SegreForm.aeval_blockRatio_mem y E c₀ hc β⟩),
    ?_, ?_, ?_, ?_, SegreForm.smooth_away_mul s _ e, ?_⟩
  · have := ((isHomogeneous_X ℤ c₀).mul hG₁).mul hG₂
    convert this using 1
    ring
  · rw [mul_assoc]
    exact dvd_mul_right _ _
  · have e₂' : aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) G₂ =
        (m₂ : Ω) * aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β := e₂
    rw [map_mul, map_mul, aeval_X, e₁, e₂', div_self h0]
    push_cast
    ring
  · intro h
    have h' := congrArg (Subtype.val) h
    have h'' : (s : Ω) * (((m₁ : Ω) * m₂) * aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β) = 0 := by
      simpa using h'
    exact mul_ne_zero hs' (mul_ne_zero (mul_ne_zero hm₁' hm₂') hbt) h''
  · intro z hz hzβ
    rw [SegreForm.eval_map_int, map_mul, map_mul, aeval_X]
    rcases SegreForm.vanish_of_value y E c₀ hc hb hG₂ e₂ hz hzβ with h | h
    · simp only [h, zero_mul]
    · simp only [h, mul_zero]
end
end

section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_smooth_chart_of_nonzero : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (b : K → ℕ) (hb : IsMultiHomog β b) (hβ : β ∉ mCoordIdeal y) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1)) (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) (s : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩)) (hs : s ≠ 0) [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s)], ∃ (d : ℕ) (Gz : MvPolynomial (Fin (N + 1)) ℤ) (g₀ : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩)), Gz.IsHomogeneous (d + 1) ∧ (X c₀ : MvPolynomial _ ℤ) ∣ Gz ∧ (g₀ : Ω) = aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) Gz ∧ g₀ ≠ 0 ∧ Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away g₀) ∧ ∀ z ∈ mcPts (mCoordIdeal y), evC z β = 0 → eval (fun j => ∏ k, z ⟨k, E j k⟩) (map (Int.castRingHom ℂ) Gz) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncRes.exists_segre_form | exact GlobalTheory.CompanionTheory.Ar.SncRes.exists_segre_form | (intros; apply GlobalTheory.CompanionTheory.Ar.SncRes.exists_segre_form <;> assumption)
end

section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_form_nonvanishing_point : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (d : ℕ) (Gz : MvPolynomial (Fin (N + 1)) ℤ) (r : ℕ) (x' : Fin (r + 1) → Ω) (hG : Gz.IsHomogeneous (d + 1)) (h0 : aeval (fun j => ∏ k, y ⟨k, E j k⟩) Gz ≠ 0) (hβ : ∀ z ∈ mcPts (mCoordIdeal y), evC z β = 0 → eval (fun j => ∏ k, z ⟨k, E j k⟩) (map (Int.castRingHom ℂ) Gz) = 0) (hx' : x' ≠ 0) (hF : ∀ i l, x' l ≠ 0 → x' i / x' l ∈ blockFnField y) (hch : ∀ a l, (∏ k, y ⟨k, E a k⟩) ≠ 0 → x' l ≠ 0 → SncChart (Algebra.adjoin ℚ (Set.range (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) ∪ Set.range (fun k => x' k / x' l))) e (aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) (map (algebraMap ℤ ℚ) Gz))), ∃ (y' : (Σ _ : Unit, Fin (r + 1)) → Ω) (J : Ideal (MRing (joinIdx ι fun _ : Unit => Fin (r + 1)))), (∃ i, y' ⟨(), i⟩ ≠ 0) ∧ blockFnField (joinVec y y') = blockFnField y ∧ IsMultiHomogIdeal J ∧ ¬ J ≤ mCoordIdeal (joinVec y y') ∧ IsSncModel (joinVec y y') e J ∧ ∀ z ∈ mcPts (mCoordIdeal (joinVec y y')), evC z (rename (joinInl ι fun _ : Unit => Fin (r + 1)) β) = 0 → z ∈ mcPts J := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SegreChart.final_data_main | exact GlobalTheory.CompanionTheory.Ar.SegreChart.final_data_main | (intros; apply GlobalTheory.CompanionTheory.Ar.SegreChart.final_data_main <;> assumption)
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory.CompanionTheory.Ar.SncRes
variable {Ω : Type} [Field Ω] [CharZero Ω]

theorem closure_facts {N : ℕ} (x : Fin (N + 1) → Ω) (hx : x ≠ 0) :
    IsReduced (point ℚ x hx).image ∧ IsDominant (point ℚ x hx).toImage :=
  GlobalTheory.T.projective_point_image_reduced Ω N x hx

theorem smooth_basicOpen {Z : Scheme.{0}} (ζ : Sp Ω ⟶ Z) [IsDominant ζ] [IsReduced Z] (g : Z ⟶ Sp ℚ)
    (e : ℕ) {W : Z.Opens} (hW : IsAffineOpen W) (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω)
    (hA : Set.range (valMap ζ W h).hom = A) (σ : Γ(Z, W)) (g₀ : A) (hg : (g₀ : Ω) = valR ζ W σ)
    [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away g₀)] :
    SmoothOfRelativeDimension e ((Z.basicOpen σ).ι ≫ g) :=
  GlobalTheory.T.standard_smooth_basic_open Ω Z ζ g e W hW h A hA σ g₀ hg

theorem lift_generic {X X' : Scheme.{0}} (ξ : Sp Ω ⟶ X) [IsDominant ξ] (f : X' ⟶ X) (U : X.Opens)
    [IsIso (f ∣_ U)] (hd : Dense ((f ⁻¹ᵁ U : X'.Opens) : Set X')) (hU : ⊤ ≤ ξ ⁻¹ᵁ U) :
    ∃ ζ : Sp Ω ⟶ X', ζ ≫ f = ξ ∧ IsDominant ζ ∧ ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U) :=
  GlobalTheory.T.lift_generic_point_over_iso_open Ω X X' ξ f U hd hU

theorem exists_coords {r : ℕ} (p : Sp Ω ⟶ PSpace ℚ r) : ∃ (x' : Fin (r + 1) → Ω) (hx' : x' ≠ 0), p = point ℚ x' hx' :=
  GlobalTheory.T.projective_point_coords_exist Ω r p

theorem val_mem_field {X X' : Scheme.{0}} (ξ : Sp Ω ⟶ X) [IsDominant ξ] [IsReduced X] (f : X' ⟶ X) (U : X.Opens)
    [IsIso (f ∣_ U)] (ζ : Sp Ω ⟶ X') (hζ : ζ ≫ f = ξ) (hU : ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U)) {W₀ : X.Opens}
    (hW₀ : IsAffineOpen W₀) (h₀ : ⊤ ≤ ξ ⁻¹ᵁ W₀) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ξ W₀ h₀).hom = A)
    (W' : X'.Opens) (h' : ⊤ ≤ ζ ⁻¹ᵁ W') (s : Γ(X', W')) :
    valR ζ W' s ∈ IntermediateField.adjoin ℚ (A : Set Ω) :=
  GlobalTheory.T.regular_values_in_adjoined_field Ω X X' ξ f U ζ hζ hU W₀ hW₀ h₀ A hA W' h' s

theorem prod_chart {N r : ℕ} {Z : Scheme.{0}} (j : Z ⟶ pullback (PSpace.str ℚ N) (PSpace.str ℚ r))
    [IsClosedImmersion j] (ζ : Sp Ω ⟶ Z) (x : Fin (N + 1) → Ω) (hx : x ≠ 0) (x' : Fin (r + 1) → Ω) (hx' : x' ≠ 0)
    (h₁ : ζ ≫ j ≫ pullback.fst _ _ = point ℚ x hx) (h₂ : ζ ≫ j ≫ pullback.snd _ _ = point ℚ x' hx')
    (a : Fin (N + 1)) (l : Fin (r + 1)) (ha : x a ≠ 0) (hl : x' l ≠ 0) :
    IsAffineOpen ((j ≫ pullback.fst _ _) ⁻¹ᵁ chart ℚ N a ⊓ (j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l) ∧
      ∃ h : ⊤ ≤ ζ ⁻¹ᵁ ((j ≫ pullback.fst _ _) ⁻¹ᵁ chart ℚ N a ⊓ (j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l),
        Set.range (valMap ζ _ h).hom =
          Algebra.adjoin ℚ (Set.range (fun k => x k / x a) ∪ Set.range (fun k => x' k / x' l)) :=
  GlobalTheory.T.segre_product_affine_chart Ω N r Z j ζ x hx x' hx' h₁ h₂ a l ha hl

theorem snc_transfer {Z : Scheme.{0}} (ζ : Sp Ω ⟶ Z) [IsDominant ζ] [IsReduced Z] (g : Z ⟶ Sp ℚ) (e : ℕ) (T : Set Z)
    (hsm : SmoothOfRelativeDimension e g) (hc : HasSncCoords g e T) {W : Z.Opens} (hW : IsAffineOpen W)
    (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ζ W h).hom = A) (σ : Γ(Z, W))
    (hσ : ∀ t ∈ W, t ∈ T ↔ t ∉ Z.basicOpen σ) : SncChart A e (valR ζ W σ) :=
  GlobalTheory.T.snc_chart_of_smooth_coords Ω Z ζ g e T hsm hc W hW h A hA σ hσ

theorem form_section {N : ℕ} {Z : Scheme.{0}} (u : Z ⟶ PSpace ℚ N) (η : Sp Ω ⟶ Z) (x : Fin (N + 1) → Ω) (hx : x ≠ 0)
    (hu : η ≫ u = point ℚ x hx) {W : Z.Opens} (hW : ⊤ ≤ η ⁻¹ᵁ W) {a : Fin (N + 1)} (hi : W ≤ u ⁻¹ᵁ chart ℚ N a)
    {n : ℕ} {G : MvPolynomial (Fin (N + 1)) ℚ} (hG : G.IsHomogeneous n) :
    ∃ σ : Γ(Z, W), valR η W σ = aeval (fun j => x j / x a) G ∧
      Z.basicOpen σ = W ⊓ u ⁻¹ᵁ Proj.basicOpen (grading ℚ N) G := by
  refine ⟨(u.appLE _ W hi).hom (formOn (chart ℚ N a) a le_rfl n G hG), ?_, ?_⟩
  · have ha : x a ≠ 0 := ne_zero_of_le hu hW hi
    have h : ⊤ ≤ point ℚ x hx ⁻¹ᵁ chart ℚ N a := (le_point_preimage_iff a).2 ha
    rw [valR_appLE η u hi hW, hu, formOn_eq_aeval, valR_eq _ _ h]
    exact (valMap_eval₂Hom point_str h _ G).trans (by simp only [valR_point_ratio ha])
  · rw [Scheme.basicOpen_appLE, basicOpen_formOn]
    refine le_antisymm (le_inf inf_le_left (inf_le_right.trans (u.preimage_mono inf_le_right)))
      (le_inf inf_le_left ?_)
    rintro t ⟨h1, h2⟩
    exact ⟨hi h1, h2⟩

theorem chart_single {N : ℕ} {Z : Scheme.{0}} (i : Z ⟶ PSpace ℚ N) [IsClosedImmersion i] (ζ : Sp Ω ⟶ Z)
    (x : Fin (N + 1) → Ω) (hx : x ≠ 0) (hi : ζ ≫ i = point ℚ x hx) (a : Fin (N + 1)) (ha : x a ≠ 0) :
    IsAffineOpen (i ⁻¹ᵁ chart ℚ N a) ∧ ∃ h : ⊤ ≤ ζ ⁻¹ᵁ (i ⁻¹ᵁ chart ℚ N a),
      Set.range (valMap ζ _ h).hom = Algebra.adjoin ℚ (Set.range fun k => x k / x a) := by
  have hc := (isAffineOpen_chart ℚ N a)
  refine ⟨hc.preimage i, le_preimage_chart hi ha, ?_⟩
  have h₁ : ⊤ ≤ point ℚ x hx ⁻¹ᵁ chart ℚ N a := (le_point_preimage_iff a).2 ha
  rw [← range_valMap_point h₁, ← (i.app_surjective _ hc).range_comp]
  congr 1
  funext s
  have := valR_comp ζ i (chart ℚ N a) s
  rw [hi, valR_eq _ _ h₁, valR_eq _ _ (le_preimage_chart hi ha)] at this
  exact this.symm

theorem snc_of_res (hR : ResKStatement) (N e d : ℕ) (x : Fin (N + 1) → Ω) (c₀ : Fin (N + 1)) (hc₀ : x c₀ ≠ 0)
    (G : MvPolynomial (Fin (N + 1)) ℚ) (hG : G.IsHomogeneous (d + 1)) (hdiv : (X c₀ : MvPolynomial _ ℚ) ∣ G)
    (g₀ : Algebra.adjoin ℚ (Set.range fun j => x j / x c₀))
    (hg₀ : (g₀ : Ω) = aeval (fun j => x j / x c₀) G) (h0 : g₀ ≠ 0)
    [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away g₀)] :
    ∃ (r : ℕ) (x' : Fin (r + 1) → Ω), x' ≠ 0 ∧
      (∀ i l, x' l ≠ 0 → x' i / x' l ∈
        IntermediateField.adjoin ℚ ((Algebra.adjoin ℚ (Set.range fun j => x j / x c₀) : Subalgebra ℚ Ω) : Set Ω)) ∧
      ∀ a l, x a ≠ 0 → x' l ≠ 0 →
        SncChart (Algebra.adjoin ℚ (Set.range (fun k => x k / x a) ∪ Set.range (fun k => x' k / x' l))) e
          (aeval (fun j => x j / x a) G) := by
  have hx : x ≠ 0 := fun h => hc₀ (by simp [h])
  obtain ⟨hred, hdom⟩ := closure_facts x hx
  set p := point ℚ x hx with hp
  have hπ : p.toImage ≫ p.imageι = point ℚ x hx := Scheme.Hom.toImage_imageι p
  obtain ⟨hW₀, h₀, hA₀⟩ := chart_single p.imageι p.toImage x hx hπ c₀ hc₀
  obtain ⟨σ₀, hσ₀, hb₀⟩ := form_section p.imageι p.toImage x hx hπ h₀ le_rfl hG
  have hsub : Proj.basicOpen (grading ℚ N) G ≤ chart ℚ N c₀ := by
    obtain ⟨G', rfl⟩ := hdiv
    rw [Proj.basicOpen_mul]
    exact inf_le_left
  set U : (p.image).Opens := p.imageι ⁻¹ᵁ Proj.basicOpen (grading ℚ N) G with hUdef
  have hUb : p.image.basicOpen σ₀ = U := by
    rw [hb₀]
    exact inf_eq_right.2 (p.imageι.preimage_mono hsub)
  have hval : valR p.toImage _ σ₀ = g₀ := by rw [hσ₀, hg₀]
  have hUtop : ⊤ ≤ p.toImage ⁻¹ᵁ U := by
    rw [← hUb, le_preimage_basicOpen_iff _ h₀, hval]
    exact isUnit_iff_ne_zero.2 (by simpa using h0)
  have hsmU : SmoothOfRelativeDimension e (U.ι ≫ p.imageι ≫ PSpace.str ℚ N) := by
    have := smooth_basicOpen p.toImage (p.imageι ≫ PSpace.str ℚ N) e hW₀ h₀ _ hA₀ σ₀ g₀ hval.symm
    rwa [hUb] at this
  have hdense : Dense (U : Set p.image) := by
    refine p.toImage.denseRange.mono ?_
    rintro _ ⟨y, rfl⟩
    exact hUtop (Set.mem_univ y)
  obtain ⟨r, X', j, f, hj, hf, hsm, hiso, hd, hco⟩ := hR ℚ N e p.image p.imageι U ⟨inferInstance, hred, hdense, hsmU⟩
  obtain ⟨ζ, hζ, hdomζ, hζU⟩ := lift_generic p.toImage f U hd hUtop
  obtain ⟨x', hx', hp₂⟩ := exists_coords (ζ ≫ j ≫ pullback.snd _ _)
  have hp₁ : ζ ≫ j ≫ pullback.fst _ _ = point ℚ x hx := by
    rw [← hf, reassoc_of% hζ, hπ]
  have : Smooth (f ≫ p.imageι ≫ PSpace.str ℚ N) := hsm.smooth
  have hredX' : IsReduced X' := GlobalTheory.isReduced_of_smooth_of_isReduced (f ≫ p.imageι ≫ PSpace.str ℚ N)
  refine ⟨r, x', hx', fun i l hl => ?_, fun a l ha hl => ?_⟩
  · have hW : ⊤ ≤ ζ ⁻¹ᵁ ((j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l) := le_preimage_chart (by simpa using hp₂) hl
    have := val_mem_field p.toImage f U ζ hζ hζU hW₀ h₀ _ hA₀ _ hW
      (pullRatio (j ≫ pullback.snd _ _) _ l le_rfl i)
    rwa [valR_pullRatio (by simpa using hp₂) hW] at this
  · obtain ⟨hWa, hW, hAW⟩ := prod_chart j ζ x hx x' hx' hp₁ hp₂ a l ha hl
    obtain ⟨σ, hσ, hb⟩ := form_section (j ≫ pullback.fst _ _) ζ x hx (by simpa using hp₁) hW inf_le_left hG
    rw [← hσ]
    refine snc_transfer ζ (f ≫ p.imageι ≫ PSpace.str ℚ N) e _ hsm hco hWa hW _ hAW σ fun t ht => ?_
    rw [hb]
    have e₁ : (j ≫ pullback.fst _ _) t = p.imageι (f t) := by
      rw [← hf]
      rfl
    constructor
    · rintro h ⟨-, h2⟩
      exact h (show p.imageι (f t) ∈ Proj.basicOpen (grading ℚ N) G from e₁ ▸ h2)
    · intro h h2
      exact h ⟨ht, show (j ≫ pullback.fst _ _) t ∈ Proj.basicOpen (grading ℚ N) G from e₁ ▸ h2⟩

section Top
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_smooth (y : (Σ k, ι k) → Ω) (e : ℕ) (hA : IsArithVar (mCoordIdeal y) (e + 1)) (N : ℕ)
    (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1)) (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) :
    ∃ s : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩), s ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s) :=
  GlobalTheory.T.exists_standard_smooth_localization Ω K ι y e hA N E c₀ hc

theorem exists_form (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (b : K → ℕ) (hb : IsMultiHomog β b)
    (hβ : β ∉ mCoordIdeal y) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1))
    (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0)
    (s : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩)) (hs : s ≠ 0)
    [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s)] :
    ∃ (d : ℕ) (Gz : MvPolynomial (Fin (N + 1)) ℤ)
      (g₀ : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩)),
      Gz.IsHomogeneous (d + 1) ∧ (X c₀ : MvPolynomial _ ℤ) ∣ Gz ∧
      (g₀ : Ω) = aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) Gz ∧ g₀ ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away g₀) ∧
      ∀ z ∈ mcPts (mCoordIdeal y), evC z β = 0 →
        eval (fun j => ∏ k, z ⟨k, E j k⟩) (map (Int.castRingHom ℂ) Gz) = 0 :=
  GlobalTheory.T.standard_smooth_chart_of_nonzero Ω K ι y e β b hb hβ N E c₀ hc s hs

theorem final_data (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k))
    (d : ℕ) (Gz : MvPolynomial (Fin (N + 1)) ℤ) (r : ℕ) (x' : Fin (r + 1) → Ω)
    (hG : Gz.IsHomogeneous (d + 1)) (h0 : aeval (fun j => ∏ k, y ⟨k, E j k⟩) Gz ≠ 0)
    (hβ : ∀ z ∈ mcPts (mCoordIdeal y), evC z β = 0 →
      eval (fun j => ∏ k, z ⟨k, E j k⟩) (map (Int.castRingHom ℂ) Gz) = 0)
    (hx' : x' ≠ 0) (hF : ∀ i l, x' l ≠ 0 → x' i / x' l ∈ blockFnField y)
    (hch : ∀ a l, (∏ k, y ⟨k, E a k⟩) ≠ 0 → x' l ≠ 0 →
      SncChart (Algebra.adjoin ℚ (Set.range (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) ∪
        Set.range (fun k => x' k / x' l))) e
        (aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) (map (algebraMap ℤ ℚ) Gz))) :
    ∃ (y' : (Σ _ : Unit, Fin (r + 1)) → Ω) (J : Ideal (MRing (joinIdx ι fun _ : Unit => Fin (r + 1)))),
      (∃ i, y' ⟨(), i⟩ ≠ 0) ∧ blockFnField (joinVec y y') = blockFnField y ∧ IsMultiHomogIdeal J ∧
      ¬ J ≤ mCoordIdeal (joinVec y y') ∧ IsSncModel (joinVec y y') e J ∧
      ∀ z ∈ mcPts (mCoordIdeal (joinVec y y')),
        evC z (rename (joinInl ι fun _ : Unit => Fin (r + 1)) β) = 0 → z ∈ mcPts J :=
  GlobalTheory.T.homogeneous_form_nonvanishing_point Ω K ι y e β N E d Gz r x' hG h0 hβ hx' hF hch

theorem adjoin_seg_le (y : (Σ k, ι k) → Ω) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1))
    (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) :
    IntermediateField.adjoin ℚ ((Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) :
      Subalgebra ℚ Ω) : Set Ω) ≤ blockFnField y := by
  rw [IntermediateField.adjoin_le_iff]
  have h1 : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) ≤
      (blockFnField y).toSubalgebra := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    change (∏ k, y ⟨k, E j k⟩) / (∏ k, y ⟨k, E c₀ k⟩) ∈ blockFnField y
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => IntermediateField.subset_adjoin _ _ ⟨⟨k, E j k⟩, ⟨k, E c₀ k⟩, rfl, rfl⟩
  exact h1

theorem exists_snc_model : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (b : K → ℕ), IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomog β b → β ∉ mCoordIdeal y → ∃ (M : ℕ) (y' : (Σ _ : Unit, Fin M) → Ω) (J : Ideal (MRing (joinIdx ι fun _ : Unit => Fin M))), (∃ i, y' ⟨(), i⟩ ≠ 0) ∧ blockFnField (joinVec y y') = blockFnField y ∧ IsMultiHomogIdeal J ∧ ¬ J ≤ mCoordIdeal (joinVec y y') ∧ IsSncModel (joinVec y y') e J ∧ ∀ z ∈ mcPts (mCoordIdeal (joinVec y y')), evC z (rename (joinInl ι fun _ : Unit => Fin M) β) = 0 → z ∈ mcPts J := by
  intro hR K _ ι _ Ω _ _ y e β b hA hb hβ
  classical
  obtain ⟨-, ⟨-, -, hrel⟩, -, -⟩ := id hA
  choose c hc using hrel
  have hc' : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hc k (by
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul])
  have : Nonempty ((k : K) → ι k) := ⟨c⟩
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card ((k : K) → ι k) = N + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  let E : Fin (N + 1) ≃ ((k : K) → ι k) := (Fintype.equivFinOfCardEq hN).symm
  let c₀ := E.symm c
  have hE : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0 := fun k => by simpa [c₀] using hc' k
  obtain ⟨s, hs, hsm⟩ := exists_smooth y e hA N E c₀ hE
  obtain ⟨d, Gz, g₀, hG, hdiv, hg₀, hg0, hsm₀, hz⟩ := exists_form y e β b hb hβ N E c₀ hE s hs
  let x : Fin (N + 1) → Ω := fun j => ∏ k, y ⟨k, E j k⟩
  have hx₀ : x c₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hE k
  let G := map (algebraMap ℤ ℚ) Gz
  obtain ⟨r, x', hx', hF, hch⟩ := snc_of_res hR N e d x c₀ hx₀ G (hG.map _)
    (by simpa [G] using map_dvd (MvPolynomial.map (algebraMap ℤ ℚ)) hdiv) g₀
    (by rw [hg₀]; exact (aeval_map_algebraMap ℚ _ _).symm) hg0
  obtain ⟨y', J, h⟩ := final_data y e β N E d Gz r x' hG (by
      intro h
      have h1 : aeval (fun j => x j / x c₀) Gz = 0 := by
        simp only [div_eq_inv_mul]
        rw [GlobalTheory.CompanionTheory.Ar.ProjCoord.aeval_mul_of_isHomogeneous x _ hG]
        exact mul_eq_zero_of_right _ h
      exact hg0 (Subtype.ext (hg₀.trans h1))) hz hx'
    (fun i l hl => adjoin_seg_le y N E c₀ hE (hF i l hl)) (fun a l ha hl => hch a l ha hl)
  exact ⟨r + 1, y', J, h⟩
end Top

end GlobalTheory.CompanionTheory.Ar.SncRes
end
end
