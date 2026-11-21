import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedCompatibleMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrameOfFreeSec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SabExtNormalStOfHomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProperOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SvalUpSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import BuildAid.ForwardExisting

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Spread

theorem gs_fromSpecStalk (X : Scheme.{0}) (x : X) (U : X.Opens) (hx : x ∈ U) (c : Γ(X, U))
    (q : PrimeSpectrum (X.presheaf.stalk x)) :
    gs (X.fromSpecStalk x) q U c =
      @algebraMap (X.presheaf.stalk x) ((Spec.structureSheaf (X.presheaf.stalk x)).presheaf.stalk q) _ _
        (StructureSheaf.stalkAlgebra _ q) (gs (𝟙 X) x U c) := by
  have hq : X.fromSpecStalk x q ∈ U := by
    have : X.fromSpecStalk x q ⤳ x := (Scheme.range_fromSpecStalk (x := x)).le ⟨q, rfl⟩
    exact this.mem_open U.2 hx
  rw [gs_eq _ _ _ hq, gs_eq _ _ _ hx]
  rw [Scheme.fromSpecStalk_app hx]
  simp only [CommRingCat.comp_apply, Scheme.ΓSpecIso_inv]
  erw [TopCat.Presheaf.germ_res_apply]
  rfl

variable {V : Type} [CommRing V]

theorem stalkMap_cst {Y Z : Scheme.{0}} (g : Z ⟶ Y) (p : Y ⟶ Sp V) (z : Z) (v : V) :
    (g.stalkMap z).hom (cst p (g z) v) = cst (g ≫ p) z v := by
  have h : g z ∈ p ⁻¹ᵁ (⊤ : (Sp V).Opens) := trivial
  rw [cst, cst, ← gs_pull g p z ⊤ trivial, gs_stalkMap g z (p ⁻¹ᵁ ⊤) h, gs_pull (𝟙 Y) p (g z) ⊤ trivial,
    Category.id_comp]

theorem isUnit_cst_iff {Z : Scheme.{0}} (p : Z ⟶ Sp V) (z : Z) (v : V) :
    IsUnit (cst p z v) ↔ v ∉ (p z).asIdeal := by
  rw [cst, gs_stalkMap p z ⊤ trivial, isUnit_map_iff]
  let P : PrimeSpectrum V := p z
  have e : gs (𝟙 (Sp V)) (p z) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom v) =
      algebraMap V ((Spec.structureSheaf V).presheaf.stalk P) v := by
    rw [gs_eq _ _ (⊤ : (Sp V).Opens) (show (𝟙 (Sp V) : Sp V ⟶ Sp V) (p z) ∈ (⊤ : (Sp V).Opens) from trivial)]
    rfl
  rw [e]
  exact IsLocalization.AtPrime.isUnit_to_map_iff ((Spec.structureSheaf V).presheaf.stalk P) P.asIdeal v

theorem isNormalScheme_sp (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] :
    IsNormalScheme (Sp R) := by
  refine (isNormalScheme_iff _).2 fun P => ?_
  let P' : PrimeSpectrum R := P
  change IsDomain ((Spec.structureSheaf R).presheaf.stalk P') ∧
    IsIntegrallyClosed ((Spec.structureSheaf R).presheaf.stalk P')
  have hle := P'.asIdeal.primeCompl_le_nonZeroDivisors
  exact ⟨IsLocalization.isDomain_of_le_nonZeroDivisors ((Spec.structureSheaf R).presheaf.stalk P') hle,
    isIntegrallyClosed_of_isLocalization _ _ hle⟩

end GlobalTheory.Spread

namespace GlobalTheory.Spread

variable {V : Type} [CommRing V]

theorem cst_fromSpecStalk (X : Scheme.{0}) (x : X) (p : X ⟶ Sp V) (q : PrimeSpectrum (X.presheaf.stalk x))
    (v : V) :
    cst (X.fromSpecStalk x ≫ p) q v =
      @algebraMap (X.presheaf.stalk x) ((Spec.structureSheaf (X.presheaf.stalk x)).presheaf.stalk q) _ _
        (StructureSheaf.stalkAlgebra _ q) (cst p x v) := by
  unfold cst
  refine (gs_pull (X.fromSpecStalk x) p q ⊤ trivial _).symm.trans
    ((gs_fromSpecStalk X x (p ⁻¹ᵁ ⊤) trivial _ q).trans ?_)
  congr 1

theorem exists_closedFibre_of_generic (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R))
    [GrpObj G] [GeometricallyIntegral G.hom] (y : G.left)
    (hy : ∀ w : G.left, w ⤳ y → G.hom w = G.hom y → w = y) :
    ∃ z : G.left, G.hom z = closedPoint R ∧ y ⤳ z := by
  set P := G.hom y
  have hI : IsIntegral (G.hom.fiber P) :=
    GeometricallyIntegral.geometrically_isIntegral (f := G.hom) ((Sp R).fromSpecResidueField P)
      (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  let η := G.hom.fiberι P (genericPoint (G.hom.fiber P))
  have hη : ∀ w : G.left, G.hom w = P → η ⤳ w := by
    intro w hw
    obtain ⟨w', rfl⟩ : w ∈ Set.range (G.hom.fiberι P) := by rw [Scheme.Hom.range_fiberι]; exact hw
    exact (genericPoint_specializes w').map (G.hom.fiberι P).continuous
  have hηP : G.hom η = P := by
    have : η ∈ Set.range (G.hom.fiberι P) := ⟨_, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  have hηy : η = y := hy η (hη y rfl) hηP
  let e := (MonObj.one : 𝟙_ (Over (Sp R)) ⟶ G).left
  have he : ∀ u, G.hom (e u) = u := fun u => by
    change (e ≫ G.hom) u = u
    rw [Over.w]
    rfl
  refine ⟨e (closedPoint R), he _, ?_⟩
  rw [← hηy]
  exact (hη (e P) (he P)).trans ((IsLocalRing.specializes_closedPoint P).map e.continuous)

end GlobalTheory.Spread

namespace GlobalTheory.Spread

theorem dvd_of_dvd_near_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsNoetherianRing R → IsIntegrallyClosed R →
    ∀ (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ (r : R), r ≠ 0 → ∀ (W : G.left.Opens) (a : Γ(G.left, W))
    (x : G.left), x ∈ W → (∀ y ∈ W, (∃ z : G.left, G.hom z = closedPoint R ∧ y ⤳ z) → cst G.hom y r ∣ gs (𝟙 G.left) y W a) →
    cst G.hom x r ∣ gs (𝟙 G.left) x W a := by
  intro R _ _ _ hN hIC G _ hG r hr W a x hxW H
  have : Smooth G.hom := hG.smooth
  have : GeometricallyConnected G.hom := hG.geomConnected
  have : GeometricallyIntegral G.hom := GlobalTheory.geometricallyIntegral_of_smooth G.hom
  have : IsNormalScheme (Sp R) := isNormalScheme_sp R
  have : IsNormalScheme G.left := GlobalTheory.isNormalScheme_of_smooth G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  obtain ⟨_, _⟩ := (isNormalScheme_iff G.left).1 ‹_› x
  have ha : cst G.hom x r ≠ 0 := by
    intro h0
    have hreg := cst_regular G.hom x hr
    rw [h0] at hreg
    exact one_ne_zero (hreg (by simp : (0 : G.left.presheaf.stalk x) * 1 = 0 * 0))
  refine GlobalTheory.dvd_of_forall_height_eq_one ha fun q _ hq1 haq => ?_
  let f := G.left.fromSpecStalk x
  let Q : PrimeSpectrum (G.left.presheaf.stalk x) := ⟨q, inferInstance⟩
  have hmem : ∀ Q' : PrimeSpectrum (G.left.presheaf.stalk x),
      r ∈ (G.hom (f Q')).asIdeal ↔ cst G.hom x r ∈ Q'.asIdeal := by
    intro Q'
    letI := StructureSheaf.stalkAlgebra (G.left.presheaf.stalk x) Q'
    have e1 := isUnit_cst_iff (f ≫ G.hom) Q' r
    rw [cst_fromSpecStalk] at e1
    have e2 := IsLocalization.AtPrime.isUnit_to_map_iff
      ((Spec.structureSheaf (G.left.presheaf.stalk x)).presheaf.stalk Q') Q'.asIdeal (cst G.hom x r)
    have e := e1.symm.trans e2
    constructor
    · intro h
      by_contra h'
      exact (e.2 h') h
    · intro h
      by_contra h'
      exact (e.1 h') h
  have hyx : f Q ⤳ x := (Scheme.range_fromSpecStalk (x := x)).le ⟨Q, rfl⟩
  have hyW : f Q ∈ W := hyx.mem_open W.2 hxW
  have key : ∃ z : G.left, G.hom z = closedPoint R ∧ f Q ⤳ z := by
    apply exists_closedFibre_of_generic R G (f Q)
    intro w hwy hw
    obtain ⟨Q'', rfl⟩ : w ∈ Set.range f := by
      rw [Scheme.range_fromSpecStalk]; exact hwy.trans hyx
    let Q' : PrimeSpectrum (G.left.presheaf.stalk x) := Q''
    have hsp : Q' ⤳ Q := (f.isEmbedding.isInducing.specializes_iff).1 hwy
    have hle : Q'.asIdeal ≤ q := (PrimeSpectrum.le_iff_specializes Q' Q).2 hsp
    have haQ' : cst G.hom x r ∈ Q'.asIdeal := (hmem Q').1 (by change r ∈ (G.hom (f Q'')).asIdeal; rw [hw]; exact (hmem Q).2 haq)
    have hQ : Q'' = Q := by
      by_contra hne
      have hlt : Q'.asIdeal < q := lt_of_le_of_ne hle (fun h => hne (PrimeSpectrum.ext h))
      have h1 := Ideal.height_strict_mono_of_isPrime hlt
      rw [hq1, ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot] at h1
      rw [h1] at haQ'
      exact ha haQ'
    rw [hQ]
  obtain ⟨t, ht⟩ := H (f Q) hyW key
  have hd := map_dvd (f.stalkMap Q).hom ⟨t, ht⟩
  replace hd : cst (f ≫ G.hom) Q r ∣ gs f Q W a := by
    have e1 := stalkMap_cst f G.hom Q r
    have e2 := gs_stalkMap f Q W hyW a
    rw [← e1, e2]
    exact hd
  rw [cst_fromSpecStalk, gs_fromSpecStalk _ x W hxW] at hd
  letI := StructureSheaf.stalkAlgebra (G.left.presheaf.stalk x) Q
  haveI : IsLocalization Q.asIdeal.primeCompl
      ((Spec.structureSheaf (G.left.presheaf.stalk x)).presheaf.stalk Q) :=
    StructureSheaf.IsLocalization.to_stalk _ Q
  obtain ⟨w, hw⟩ := hd
  obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective (S := (Spec.structureSheaf (G.left.presheaf.stalk x)).presheaf.stalk Q)
    Q.asIdeal.primeCompl w
  dsimp only at hw
  have e : algebraMap (G.left.presheaf.stalk x) ((Spec.structureSheaf (G.left.presheaf.stalk x)).presheaf.stalk Q)
      (gs (𝟙 G.left) x W a * s) =
      algebraMap (G.left.presheaf.stalk x) ((Spec.structureSheaf (G.left.presheaf.stalk x)).presheaf.stalk Q)
      (cst G.hom x r * c) := by
    rw [map_mul, hw]
    erw [mul_assoc, IsLocalization.mk'_spec]
    rw [map_mul]
  obtain ⟨u, hu⟩ := (IsLocalization.eq_iff_exists Q.asIdeal.primeCompl _).1 e
  refine ⟨u * s, Q.asIdeal.primeCompl.mul_mem u.2 s.2, ⟨u * c, ?_⟩⟩
  linear_combination hu

end GlobalTheory.Spread
end

section
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GenericFibreOpen

theorem range_spMap_algebraMap_eq (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] :
    Set.range (spMap (algebraMap O K)) = {x : Sp O | (x : PrimeSpectrum O).asIdeal = ⊥} := by
  have key : ∀ y : Sp K, ((spMap (algebraMap O K)).base y : PrimeSpectrum O).asIdeal = ⊥ := fun y => by
    change Ideal.comap (algebraMap O K) (y : PrimeSpectrum K).asIdeal = ⊥
    rw [(Ideal.eq_bot_or_top (y : PrimeSpectrum K).asIdeal).resolve_right (y : PrimeSpectrum K).isPrime.ne_top]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact key y
  · intro hx
    refine ⟨(show Sp K from (default : PrimeSpectrum K)), ?_⟩
    apply PrimeSpectrum.ext
    exact (key _).trans hx.symm

end GlobalTheory.GenericFibreOpen

open GlobalTheory.GenericFibreOpen in

theorem GlobalTheory.GenericFibreOpen.isOpen_preimage_range_spMap_fraction :
    ∀ (O K R : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] [CommRing R]
      [IsLocalRing R] (g : Sp R ⟶ Sp O), IsOpen (g ⁻¹' Set.range (spMap (algebraMap O K))) := by
  intro O K R _ _ _ _ _ _ _ g
  rw [range_spMap_algebraMap_eq O K]
  have hc : Continuous g.base := g.base.hom.continuous
  set c : Sp R := (IsLocalRing.closedPoint R : PrimeSpectrum R)
  have hle : ∀ x : Sp R, ((g.base x : Sp O) : PrimeSpectrum O).asIdeal ≤ ((g.base c : Sp O) : PrimeSpectrum O).asIdeal := by
    intro x
    have hs : (x : PrimeSpectrum R) ⤳ IsLocalRing.closedPoint R := IsLocalRing.specializes_closedPoint _
    exact (PrimeSpectrum.le_iff_specializes _ _).2 (hs.map hc)
  by_cases hp : ((g.base c : Sp O) : PrimeSpectrum O).asIdeal = ⊥
  · have : (fun x : Sp R => g.base x) ⁻¹' {x : Sp O | (x : PrimeSpectrum O).asIdeal = ⊥} = Set.univ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact le_bot_iff.1 (hp ▸ hle x)
    exact this ▸ isOpen_univ
  · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
    have hmax : ((g.base c : Sp O) : PrimeSpectrum O).asIdeal.IsMaximal :=
      ((g.base c : Sp O) : PrimeSpectrum O).isPrime.isMaximal hp
    have : (fun x : Sp R => g.base x) ⁻¹' {x : Sp O | (x : PrimeSpectrum O).asIdeal = ⊥} =
        (fun x : Sp R => g.base x) ⁻¹' (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum O)) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · intro h hx
        rw [h, Ideal.mem_bot] at hx
        exact ha0 hx
      · intro hx
        by_contra hne
        have hq : ((g.base x : Sp O) : PrimeSpectrum O).asIdeal.IsMaximal :=
          ((g.base x : Sp O) : PrimeSpectrum O).isPrime.isMaximal hne
        have heq := hq.eq_of_le hmax.ne_top (hle x)
        exact hx (heq ▸ ha)
    rw [this]
    exact (PrimeSpectrum.basicOpen a).isOpen.preimage hc
end

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preimage_generic_fiber_isOpen : ∀ (O K R : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] [CommRing R] [IsLocalRing R] (g : Sp R ⟶ Sp O), IsOpen (g ⁻¹' Set.range (spMap (algebraMap O K))) := by
  atlas_forward_decl GlobalTheory.GenericFibreOpen.isOpen_preimage_range_spMap_fraction
end

section
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem factor_through_fractionField_of_range :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (T : Scheme.{0})
      (g : T ⟶ Sp O), Set.range g ⊆ Set.range (spMap (algebraMap O K)) →
        ∃ f : T ⟶ Sp K, f ≫ spMap (algebraMap O K) = g := by
  intro O K _ _ _ _ _ T g hg
  let φ : O →+* Γ(T, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ g.appTop).hom
  have hgφ : g = T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) := by
    have h := Scheme.toSpecΓ_naturality g
    have e : g = g ≫ (Sp O).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of O)).inv := by simp
    rw [e, ← Category.assoc, h, Category.assoc, ← Spec.map_comp]
    simp [φ]
  have hunit : ∀ b : nonZeroDivisors O, IsUnit (φ b) := by
    rintro ⟨b, hb⟩
    refine T.toRingedSpace.isUnit_of_isUnit_germ ⊤ (φ b) fun x hx => ?_
    have hmem : x ∈ T.basicOpen (φ b) := by
      have e : T.basicOpen (φ b) = g ⁻¹ᵁ (Sp O).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of O)).inv b) := by
        rw [Scheme.preimage_basicOpen_top]; rfl
      rw [e]
      show g x ∈ (Sp O).basicOpen _
      rw [basicOpen_eq_of_affine (R := CommRingCat.of O) b]
      obtain ⟨y, hy⟩ := hg ⟨x, rfl⟩
      show b ∉ (g x).asIdeal
      rw [← hy]
      intro hbm
      have hbm' : algebraMap O K b ∈ y.asIdeal := hbm
      have hu : IsUnit (algebraMap O K b) :=
        (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb).isUnit
      exact y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hbm' hu)
    exact (T.mem_basicOpen (φ b) x hx).1 hmem
  let ψ : K →+* Γ(T, ⊤) := IsLocalization.lift (M := nonZeroDivisors O) hunit
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ), ?_⟩
  rw [hgφ, Category.assoc, ← Spec.map_comp]
  congr 2
  ext b
  simp [ψ]

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factor_through_generic_fiber : ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (T : Scheme.{0}) (g : T ⟶ Sp O), Set.range g ⊆ Set.range (spMap (algebraMap O K)) → ∃ f : T ⟶ Sp K, f ≫ spMap (algebraMap O K) = g := by
  atlas_forward_decl GlobalTheory.factor_through_fractionField_of_range
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TorRef.TriplePull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem range_j {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Set.range Y.j = abLocus Y.t.G ∩ Y.s ⁻¹' Set.range (spMap β) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    have hy : Y.jQ y ∈ Set.range Y.jQ := ⟨y, rfl⟩
    rw [← Y.ab_gen] at hy
    refine ⟨hy, ?_⟩
    rw [Set.mem_preimage, ← Set.mem_preimage, ← Scheme.Pullback.range_fst]
    exact ⟨Y.jQ y, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [Set.mem_preimage, ← Set.mem_preimage, ← Scheme.Pullback.range_fst] at h2
    obtain ⟨p, rfl⟩ := h2
    have hp : p ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := h1
    rw [Y.ab_gen] at hp
    obtain ⟨y, rfl⟩ := hp
    exact ⟨y, rfl⟩

theorem factor_j {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {T : Scheme.{0}} (f : T ⟶ Y.X)
    (hf : Set.range f ⊆ Set.range Y.j) (h : T ⟶ Sp c.F) (hh : h ≫ spMap β = f ≫ Y.s) :
    ∃ u : T ⟶ Xo.XF c, u ≫ Y.j = f := by
  haveI := Y.jQ_open
  let p : T ⟶ pullback Y.s (spMap β) := pullback.lift f h hh.symm
  have hp : Set.range p ⊆ Set.range Y.jQ := by
    rintro _ ⟨x, rfl⟩
    rw [← Y.ab_gen]
    show (p ≫ pullback.fst _ _) x ∈ abLocus _
    rw [pullback.lift_fst]
    exact ((range_j Y).le (hf ⟨x, rfl⟩)).1
  refine ⟨IsOpenImmersion.lift Y.jQ p hp, ?_⟩
  rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]

end GlobalTheory.TorRef.TriplePull

namespace GlobalTheory.TorRef.TriplePull

theorem sab_of_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), Z.j ≫ π = X.j → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ξ' : Sp R' ⟶ Z.X) (t' : SAB H (Sp R')), IsCN R' → Dense (ξ' ⁻¹' Set.range Z.j) → SABMap t' X.t (ξ' ≫ π) → Nonempty (SABMap t' Z.t ξ') := by
  intro E _ _ _ H D l Xo c X Z π hπ R' _ _ _ ξ' t' hR hd m
  obtain ⟨hN, hIC, -, -⟩ := hR
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := ⟨⟩
  obtain ⟨t'', ⟨n''⟩⟩ := exists_sabPull ξ' Z.t
  have hU : IsOpen (ξ' ⁻¹' Set.range Z.j) := by
    have e : ξ' ⁻¹' Set.range Z.j =
        abLocus t''.G ∩ (ξ' ≫ Z.s) ⁻¹' Set.range (spMap (algebraMap (𝓞 c.F) c.F)) := by
      rw [range_j, Set.preimage_inter]
      congr 1
      ext x
      exact abLocus_pullback abLocusOne Z.t.semi n''.cart.1 x
    rw [e]
    exact (GlobalTheory.AbLocusOpen.isOpen_abLocus_local t''.G t''.semi).inter (GlobalTheory.T.preimage_generic_fiber_isOpen _ _ _ _)
  let U : (Sp R').Opens := ⟨_, hU⟩
  have hUr : Set.range (U.ι ≫ ξ') ⊆ Set.range Z.j := by
    rintro _ ⟨x, rfl⟩
    have hx : U.ι x ∈ (U : Set (Sp R')) := by rw [← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩
    exact hx
  obtain ⟨h, hh⟩ := GlobalTheory.T.factor_through_generic_fiber (𝓞 c.F) c.F U.toScheme ((U.ι ≫ ξ') ≫ Z.s) (by
    rintro _ ⟨x, rfl⟩
    exact ((range_j Z).le (hUr ⟨x, rfl⟩)).2)
  obtain ⟨u, hu⟩ := factor_j Z (U.ι ≫ ξ') hUr h hh
  obtain ⟨t₀, ⟨n₀⟩⟩ := exists_sabPull u Z.oF.t
  have hp0 : IsProper t₀.G.hom := MorphismProperty.of_isPullback (P := @IsProper) n₀.cart.1 Z.oF.proper
  obtain ⟨a1, -⟩ := ObjMaps.exists_sab_comp Z.m n₀
  obtain ⟨a, -⟩ := ObjMaps.exists_sab_cancel n'' (hu ▸ a1 : SABMap t₀ Z.t (U.ι ≫ ξ'))
  obtain ⟨zx, -⟩ := ObjMaps.exists_sab_cancel X.m0.toSABMap
    (by rw [Category.id_comp]; exact Z.m0.toSABMap : SABMap Z.oF.t Xo.univ.t (𝟙 _ ≫ pullback.fst _ _))
  obtain ⟨c1, -⟩ := ObjMaps.exists_sab_comp zx n₀
  obtain ⟨c2, -⟩ := ObjMaps.exists_sab_comp X.m c1
  have hux : (u ≫ 𝟙 _) ≫ X.jQ ≫ pullback.fst _ _ = U.ι ≫ ξ' ≫ π := by
    rw [Category.comp_id]
    change u ≫ X.j = _
    rw [← hπ, ← Category.assoc, hu, Category.assoc]
  obtain ⟨a', -⟩ := ObjMaps.exists_sab_cancel m (hux ▸ c2 : SABMap t₀ X.t (U.ι ≫ ξ' ≫ π))
  haveI : IsNoetherianRing R' := hN
  haveI : IsIntegrallyClosed R' := hIC
  have hNorm : Geo.Tor.IsNormalScheme (Sp R') := GlobalTheory.IsNormalScheme.pred _
  have hDom : IsDominant U.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact hd⟩
  obtain ⟨b, -⟩ := sabExtNormalSt_of_homExtNormalSt GlobalTheory.homExtNormal E H (Sp R') U.toScheme U.ι hNorm
    inferInstance hDom t₀ t' t'' a' a hp0
  obtain ⟨n, -⟩ := ObjMaps.exists_sab_comp n'' b
  exact ⟨(Category.id_comp ξ') ▸ n⟩

end GlobalTheory.TorRef.TriplePull
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sabMap_extends_dense : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), Z.j ≫ π = X.j → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ξ' : Sp R' ⟶ Z.X) (t' : SAB H (Sp R')), IsCN R' → Dense (ξ' ⁻¹' Set.range Z.j) → SABMap t' X.t (ξ' ≫ π) → Nonempty (SABMap t' Z.t ξ') := by
  atlas_forward_decl GlobalTheory.TorRef.TriplePull.sab_of_chart
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TorRef

theorem psiCoord_associated {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {χ : D.X} {r r' : R}
    (h : PsiCoord D χ r) (h' : PsiCoord D χ r') : Associated r r' := by
  obtain ⟨x, hx, ex⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D χ r).1 h
  obtain ⟨x', hx', ex'⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D χ r').1 h'
  obtain ⟨u, hu⟩ := hx.unique hx'
  have e1 : algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) (u * r') := by
    rw [← ex, hu, map_mul, ← ex']
    rfl
  have e2 : r = u * r' := IsFractionRing.injective R (FractionRing R) e1
  exact ⟨u⁻¹, by rw [e2, mul_comm, ← mul_assoc, Units.inv_mul, one_mul]⟩

theorem inConePull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [CommRing R'] [IsDomain R'] [IsLocalRing R'] (φ : R →+* R') (t : SAB H (Sp R)) (t' : SAB H (Sp R'))
    (P : PELUnif (maximalIdeal R) t) (P' : PELUnif (maximalIdeal R') t') (e : P'.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X) (m : ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X),
    (∀ y r, PsiCoord P.D.toPre (e y) r → ∃ u : R'ˣ, PsiCoord P'.D.toPre y (u * φ r)) → InCone P.D.toPre γ →
    InCone P'.D.toPre (fun i => pull e.toLinearMap (γ i)) := by
  intro E _ _ _ H R R' _ _ _ _ _ _ φ t t' P P' e m γ hpsi hin
  intro W _ _ _ hW ϖ hϖ f be hsym hF
  have hF0 : FormAt P.D.toPre (f.comp φ) ϖ (pull e.symm.toLinearMap be) := by
    intro y0
    obtain ⟨r, hr⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff P.D.toPre y0).2
      (GlobalTheory.PeriodFormCompare.psiIn_top P.D y0)
    obtain ⟨u, hu⟩ := hpsi (e.symm y0) r (by rwa [e.apply_symm_apply])
    obtain ⟨r', n, hr', hbe, hass⟩ := hF (e.symm y0)
    refine ⟨r, n, hr, by simpa [pull_apply] using hbe, ?_⟩
    have h1 : Associated (u * φ r) r' := psiCoord_associated hu hr'
    have h2 : Associated (f (φ r)) (f (u * φ r)) := by
      rw [map_mul]
      exact ⟨(Units.map f.toMonoidHom u), by simp [mul_comm]⟩
    exact h2.trans ((h1.map f).trans hass)
  obtain ⟨cf, hc, heq⟩ := hin W hW ϖ hϖ (f.comp φ) (pull e.symm.toLinearMap be)
    (fun a b => by simp [pull_apply, hsym]) hF0
  refine ⟨cf, hc, ?_⟩
  refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
  have := congrArg (fun F => F (e a) (e b)) heq
  simpa [toReal, pull_apply, LinearMap.sum_apply] using this

theorem hasCones_of_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X) (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ), (Fin m → LinearMap.BilinForm ℤ X) → Prop), (∀ (X₁ X₂ : Type) [AddCommGroup X₁] [Module (𝓞 E) X₁] [Module.Finite (𝓞 E) X₁] [AddCommGroup X₂] [Module (𝓞 E) X₂] [Module.Finite (𝓞 E) X₂] (f : X₁ ≃ₗ[𝓞 E] X₂) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X₂), Cn X₂ m γ → Cn X₁ m (fun i => pull f.toLinearMap (γ i))) → Z.j ≫ π = X.j → π ≫ X.s = Z.s → HasCones Cn X → HasCones Cn Z := by
  intro E _ _ _ H D l Xo c X Z π Cn hCn hj hs hX z
  obtain ⟨R, _, _, _, ξ, t, a, P, m, γ, hcn, hpt, het, hfu, htor, hcone, hin⟩ := hX (π z)
  obtain ⟨R', _, _, _, ξ', φ, hcn', hpt', het', hfu', hinj, hloc, hsq, hdense⟩ :=
    GlobalTheory.T.formally_unramified_compatible_map E H D l Xo c X Z π hj hs R ξ z hcn het hfu hpt
  obtain ⟨t', a', P', e, htor', hpsi⟩ := pullSt E H R R' φ t P hcn hcn' hinj hloc htor
  obtain ⟨a'', -⟩ := GlobalTheory.ObjMaps.exists_sab_comp a a'
  rw [← hsq] at a''
  obtain ⟨b⟩ := GlobalTheory.T.sabMap_extends_dense E H D l Xo c X Z π hj R' ξ' t' hcn' hdense a''
  exact ⟨R', inferInstance, inferInstance, inferInstance, ξ', t', b, P', m, fun i => pull e.toLinearMap (γ i),
    hcn', hpt', het', hfu', htor', hCn _ _ e m γ hcone, inConePull E H R R' φ t t' P P' e m γ hpsi hin⟩

end GlobalTheory.TorRef
end
end
