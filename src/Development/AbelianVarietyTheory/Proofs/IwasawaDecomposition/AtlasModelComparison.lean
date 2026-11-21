import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasLocalRingPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import BuildAid.ForwardExisting

section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GlueStalk

theorem isDominant_fromSpecStalk_of_isIntegral (X : Scheme.{0}) [IsIntegral X] (x : X) :
    IsDominant (X.fromSpecStalk x) := by
  refine ⟨?_⟩
  have h : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact (genericPoint_spec X).specializes trivial
  have h2 : Dense ({genericPoint X} : Set X) := by
    rw [dense_iff_closure_eq]; exact genericPoint_spec X
  exact h2.mono (Set.singleton_subset_iff.2 h)

theorem fromSpecStalk_generic {T S P : Scheme.{0}} (h : ∀ x : T, Spec (T.presheaf.stalk x) ⟶ S)
    (H : ∀ (x ξ : T) (e : ξ ⤳ x), (∀ y, y ⤳ ξ → y = ξ) → Spec.map (T.presheaf.stalkSpecializes e) ≫ h x = h ξ)
    (V : T.Opens) [IsIntegral V] {x : T} (hx : x ∈ V) (f : V.toScheme ⟶ S)
    (hf : V.fromSpecStalkOfMem x hx ≫ f = h x) [IsIntegral P] (j : P ⟶ V) (k : P ⟶ T) [IsOpenImmersion k]
    (hk : j ≫ V.ι = k) :
    P.fromSpecStalk (genericPoint P) ≫ j ≫ f =
      Spec.map (k.stalkMap (genericPoint P)) ≫ h (k (genericPoint P)) := by
  have hmax : ∀ y, y ⤳ k (genericPoint P) → y = k (genericPoint P) := fun y hy => by
    obtain ⟨p, rfl⟩ : y ∈ Set.range k := hy.mem_open k.isOpenEmbedding.isOpen_range ⟨_, rfl⟩
    exact (hy.antisymm (((genericPoint_spec P).specializes trivial).map k.continuous)).eq
  have e₀ : V.ι (genericPoint V) = k (genericPoint P) := hmax _ (by
    rw [← hk, Scheme.Hom.comp_apply]
    exact ((genericPoint_spec V).specializes trivial).map V.ι.continuous)
  have e : k (genericPoint P) ⤳ x := by
    rw [← e₀]
    exact ((genericPoint_spec V).specializes (y := (⟨x, hx⟩ : V)) trivial).map V.ι.continuous
  rw [← H x _ e hmax, ← hf, ← Category.assoc, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono V.ι, Category.assoc, hk, Category.assoc, Category.assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem exists_glue_of_stalks : ∀ (B T S : Scheme.{0}) (t : T ⟶ B) (s : S ⟶ B) (h : ∀ x : T, Spec (T.presheaf.stalk x) ⟶ S), LocallyOfFiniteType s → IsSeparated s → IsLocallyNoetherian T → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → (∀ x, h x ≫ s = T.fromSpecStalk x ≫ t) → (∀ (x ξ : T) (e : ξ ⤳ x), (∀ y, y ⤳ ξ → y = ξ) → Spec.map (T.presheaf.stalkSpecializes e) ≫ h x = h ξ) → ∃ g : T ⟶ S, ∀ x, T.fromSpecStalk x ≫ g = h x := by
  intro B T S t s h _ _ _ hn hs H
  have : GlobalTheory.IsNormalScheme T := GlobalTheory.IsNormalScheme.of_pred hn
  have loc : ∀ x : T, ∃ (V : T.Opens) (hx : x ∈ V) (f : V.toScheme ⟶ S), IsIntegral V ∧
      V.fromSpecStalkOfMem x hx ≫ f = h x ∧ f ≫ s = V.ι ≫ t := fun x => by
    obtain ⟨U, hU, f, h₁, h₂⟩ := spread_out_of_isGermInjective' t s (h x) (hs x)
    let Z : irreducibleComponents T := ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩
    have hx : x ∈ U ⊓ GlobalTheory.IsNormalScheme.component Z := ⟨hU, mem_irreducibleComponent⟩
    have : Nonempty (U ⊓ GlobalTheory.IsNormalScheme.component Z).toScheme := ⟨⟨x, hx⟩⟩
    refine ⟨_, hx, T.homOfLE inf_le_left ≫ f, isIntegral_of_isOpenImmersion (T.homOfLE inf_le_right), ?_, ?_⟩
    · rw [h₁, ← Category.assoc]
      congr 1
      rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι,
        Scheme.Opens.fromSpecStalkOfMem_ι]
    · rw [Category.assoc, h₂, Scheme.homOfLE_ι_assoc]
  choose V hx f hi h₁ h₂ using loc
  have hc : ⨆ x, V x = ⊤ := top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hx x⟩
  have key : ∀ x y, pullback.fst (V x).ι (V y).ι ≫ f x = pullback.snd (V x).ι (V y).ι ≫ f y := fun x y => by
    have := hi x
    have := hi y
    cases isEmpty_or_nonempty ↥(pullback (V x).ι (V y).ι) with
    | inl _ => exact (isInitialOfIsEmpty (X := pullback (V x).ι (V y).ι)).hom_ext _ _
    | inr _ =>
      have : IsIntegral (pullback (V x).ι (V y).ι) := isIntegral_of_isOpenImmersion (pullback.fst (V x).ι (V y).ι)
      have := isDominant_fromSpecStalk_of_isIntegral _ (genericPoint ↥(pullback (V x).ι (V y).ι))
      refine ext_of_isDominant_of_isSeparated s ?_
        ((pullback (V x).ι (V y).ι).fromSpecStalk (genericPoint _)) ?_
      · rw [Category.assoc, Category.assoc, h₂, h₂, pullback.condition_assoc]
      · exact (fromSpecStalk_generic h H (V x) (hx x) (f x) (h₁ x) _ _ rfl).trans
          (fromSpecStalk_generic h H (V y) (hx y) (f y) (h₁ y) _ _ pullback.condition.symm).symm
  refine ⟨(T.openCoverOfIsOpenCover V hc).glueMorphisms f key, fun x => ?_⟩
  rw [← Scheme.Opens.fromSpecStalkOfMem_ι (V x) x (hx x), Category.assoc, ← h₁ x]
  exact congrArg (_ ≫ ·) (Scheme.Cover.ι_glueMorphisms (T.openCoverOfIsOpenCover V hc) f key x)

end GlobalTheory.GlueStalk
end

section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_morphism_of_stalk_maps : ∀ (B T S : Scheme.{0}) (t : T ⟶ B) (s : S ⟶ B) (h : ∀ x : T, Spec (T.presheaf.stalk x) ⟶ S), LocallyOfFiniteType s → IsSeparated s → IsLocallyNoetherian T → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → (∀ x, h x ≫ s = T.fromSpecStalk x ≫ t) → (∀ (x ξ : T) (e : ξ ⤳ x), (∀ y, y ⤳ ξ → y = ξ) → Spec.map (T.presheaf.stalkSpecializes e) ≫ h x = h ξ) → ∃ g : T ⟶ S, ∀ x, T.fromSpecStalk x ≫ g = h x := by
  first | exact @GlobalTheory.GlueStalk.exists_glue_of_stalks | exact GlobalTheory.GlueStalk.exists_glue_of_stalks | (intros; apply GlobalTheory.GlueStalk.exists_glue_of_stalks <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atlas_local_ring_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (i : Idx H p) (X : Scheme.{0}) (π : X ⟶ (Y i).X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas (Y i) π ty) (Z : Mdl Y i₀) (R K k : Type) [CommRing R] [IsLocalRing R] [Field K] [Field k] (φ : R →+* K) (ψ : R →+* k) (z : Sp R ⟶ Z.X) (z' : Sp R ⟶ X), i.c.F ≤ Z.i.c.F → (∀ σ, ty σ ⊆ Z.ty σ) → Function.Injective φ → z (IsLocalRing.closedPoint R) ∈ Z.opn → NatTo Z A (spMap φ ≫ z) (spMap φ ≫ z') → NatTo Z A (spMap ψ ≫ z) (spMap ψ ≫ z') := by
  first | exact @GlobalTheory.DRFlag.Spez.natTo_specialise | exact GlobalTheory.DRFlag.Spez.natTo_specialise | (intros; apply GlobalTheory.DRFlag.Spez.natTo_specialise <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem residueField_isFractionRing_of_generic : ∀ (X : Scheme.{0}) (x ξ : X) (e : ξ ⤳ x),
    IsDomain (X.presheaf.stalk x) → (∀ y, y ⤳ ξ → y = ξ) →
    @IsFractionRing (X.presheaf.stalk x) _ (X.residueField ξ) _
      (RingHom.toAlgebra (X.presheaf.stalkSpecializes e ≫ X.residue ξ).hom) := by
  intro X x ξ e hd hgen

  have hnil : ∀ s : X.presheaf.stalk ξ, X.residue ξ s = 0 → IsNilpotent s := by
    intro s hs
    have hs' : s ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.residue_eq_zero_iff s).mp hs
    rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
    intro J hJ
    let q : PrimeSpectrum (X.presheaf.stalk ξ) := ⟨J, hJ⟩
    have h1 : X.fromSpecStalk ξ q ⤳ ξ := by
      have : X.fromSpecStalk ξ q ∈ Set.range (X.fromSpecStalk ξ) := ⟨q, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have h2 : q = IsLocalRing.closedPoint _ :=
      (X.fromSpecStalk ξ).isEmbedding.injective
        ((hgen _ h1).trans Scheme.fromSpecStalk_closedPoint.symm)
    have h3 : J = IsLocalRing.maximalIdeal _ := congrArg PrimeSpectrum.asIdeal h2
    rw [h3]; exact hs'
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hξU : ξ ∈ U := e.mem_open U.2 hxU
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨ξ, hξU⟩ : U)
  haveI hLx := hU.isLocalization_stalk ⟨x, hxU⟩
  haveI hLξ := hU.isLocalization_stalk ⟨ξ, hξU⟩
  have hsp : ∀ a : Γ(X, U), X.presheaf.stalkSpecializes e (X.presheaf.germ U x hxU a) =
      X.presheaf.germ U ξ hξU a :=
    fun a => X.presheaf.germ_stalkSpecializes_apply hxU e a
  have hunitξ : ∀ b ∈ (hU.primeIdealOf ⟨ξ, hξU⟩).asIdeal.primeCompl,
      IsUnit (X.presheaf.germ U ξ hξU b) :=
    fun b hb => IsLocalization.map_units (X.presheaf.stalk (⟨ξ, hξU⟩ : U))
      (⟨b, hb⟩ : (hU.primeIdealOf ⟨ξ, hξU⟩).asIdeal.primeCompl)
  have hne : ∀ b ∈ (hU.primeIdealOf ⟨ξ, hξU⟩).asIdeal.primeCompl,
      X.presheaf.germ U x hxU b ≠ 0 := by
    intro b hb h0
    have h' := congrArg (X.presheaf.stalkSpecializes e) h0
    rw [hsp, map_zero] at h'
    exact (hunitξ b hb).ne_zero h'
  have hinj : ∀ r : X.presheaf.stalk x,
      X.residue ξ (X.presheaf.stalkSpecializes e r) = 0 → r = 0 := by
    intro r hr
    obtain ⟨⟨a, d⟩, hrad⟩ := IsLocalization.surj (S := X.presheaf.stalk (⟨x, hxU⟩ : U))
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl r
    change r * X.presheaf.germ U x hxU d = X.presheaf.germ U x hxU a at hrad
    have hres : X.residue ξ (X.presheaf.germ U ξ hξU a) = 0 := by
      rw [← hsp, ← hrad, map_mul, map_mul, hr, zero_mul]
    obtain ⟨n, hn⟩ := hnil _ hres
    have hn' : algebraMap Γ(X, U) (X.presheaf.stalk (⟨ξ, hξU⟩ : U)) (a ^ n) = 0 := by
      rw [map_pow]; exact hn
    obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff
      (hU.primeIdealOf ⟨ξ, hξU⟩).asIdeal.primeCompl _ _).mp hn'
    have hc' : X.presheaf.germ U x hxU c * (X.presheaf.germ U x hxU a) ^ n = 0 := by
      rw [← map_pow, ← map_mul, hc, map_zero]
    have ha0 : X.presheaf.germ U x hxU a = 0 :=
      IsNilpotent.eq_zero ⟨n, (mul_eq_zero.mp hc').resolve_left (hne c c.2)⟩
    rw [ha0] at hrad
    exact (IsUnit.mul_left_eq_zero (IsLocalization.map_units
      (X.presheaf.stalk (⟨x, hxU⟩ : U)) d)).mp hrad
  letI alg := RingHom.toAlgebra (X.presheaf.stalkSpecializes e ≫ X.residue ξ).hom
  have halg : ∀ r, algebraMap (X.presheaf.stalk x) (X.residueField ξ) r =
      X.residue ξ (X.presheaf.stalkSpecializes e r) := fun _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro y
    rw [isUnit_iff_ne_zero, halg]
    exact fun h => nonZeroDivisors.ne_zero y.2 (hinj _ h)
  · intro z
    obtain ⟨s, rfl⟩ := X.residue_surjective ξ z
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (S := X.presheaf.stalk (⟨ξ, hξU⟩ : U))
      (hU.primeIdealOf ⟨ξ, hξU⟩).asIdeal.primeCompl s
    change s * X.presheaf.germ U ξ hξU b = X.presheaf.germ U ξ hξU a at hab
    refine ⟨⟨X.presheaf.germ U x hxU a,
      ⟨X.presheaf.germ U x hxU b, mem_nonZeroDivisors_of_ne_zero (hne b b.2)⟩⟩, ?_⟩
    change X.residue ξ s * algebraMap _ _ (X.presheaf.germ U x hxU b) =
      algebraMap _ _ (X.presheaf.germ U x hxU a)
    rw [halg, halg, hsp, hsp, ← map_mul, hab]
  · intro r t h
    refine ⟨1, ?_⟩
    have h0 := hinj (r - t) (by rw [map_sub, map_sub, ← halg, ← halg, h, sub_self])
    rw [sub_eq_zero.mp h0]

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFractionRing_stalk_generic : ∀ (X : Scheme.{0}) (x ξ : X) (e : ξ ⤳ x), IsDomain (X.presheaf.stalk x) → (∀ y, y ⤳ ξ → y = ξ) → @IsFractionRing (X.presheaf.stalk x) _ (X.residueField ξ) _ (RingHom.toAlgebra (X.presheaf.stalkSpecializes e ≫ X.residue ξ).hom) := by
  atlas_forward_decl GlobalTheory.residueField_isFractionRing_of_generic
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

set_option autoImplicit false

namespace GlobalTheory.MapLoc

theorem exists_gen (X : Scheme.{0}) (x : X) (hd : IsDomain (X.presheaf.stalk x)) :
    ∃ ξ : X, ξ ⤳ x ∧ ∀ y, y ⤳ x → ξ ⤳ y := by
  let η : PrimeSpectrum (X.presheaf.stalk x) := ⟨⊥, Ideal.isPrime_bot⟩
  refine ⟨X.fromSpecStalk x η, ?_, ?_⟩
  · have h1 : η ⤳ IsLocalRing.closedPoint (X.presheaf.stalk x) :=
      (PrimeSpectrum.le_iff_specializes _ _).1 (show (⊥ : Ideal _) ≤ _ from bot_le)
    have := h1.map (X.fromSpecStalk x).continuous
    rwa [Scheme.fromSpecStalk_closedPoint] at this
  · intro y hy
    have : y ∈ Set.range (X.fromSpecStalk x) := by rw [Scheme.range_fromSpecStalk]; exact hy
    obtain ⟨q, rfl⟩ := this
    exact ((PrimeSpectrum.le_iff_specializes η q).1 (show (⊥ : Ideal _) ≤ _ from bot_le)).map
      (X.fromSpecStalk x).continuous

theorem isFractionRing_residue : ∀ (X : Scheme.{0}) (x ξ : X) (e : ξ ⤳ x), IsDomain (X.presheaf.stalk x) →
    (∀ y, y ⤳ ξ → y = ξ) →
    @IsFractionRing (X.presheaf.stalk x) _ (X.residueField ξ) _
      (RingHom.toAlgebra (X.presheaf.stalkSpecializes e ≫ X.residue ξ).hom) :=
  GlobalTheory.T.isFractionRing_stalk_generic

theorem spMap_cancel {R K A : Type} [CommRing R] [CommRing K] [CommRing A] (f : R →+* K) (hf : Function.Injective f)
    (u v : Sp R ⟶ Sp A) (h : spMap f ≫ u = spMap f ≫ v) : u = v := by
  rw [← Spec.map_preimage u, ← Spec.map_preimage v] at h ⊢
  congr 1
  have e := Spec.map_injective ((Spec.map_comp _ _).trans (h.trans (Spec.map_comp _ _).symm))
  ext a
  exact hf (congrArg (fun φ => φ.hom a) e)

end GlobalTheory.MapLoc

open GlobalTheory.MapLoc in
theorem GlobalTheory.DRFlag.exists_mapsTo : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (i : Idx H p) (X : Scheme.{0}) (π : X ⟶ (Y i).X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas (Y i) π ty) (Z : Mdl Y i₀), p.Prime → (p : ℂ) ∈ W.nonunits → Geo (Y i) π → i.c.F ≤ Z.i.c.F → (∀ σ, ty σ ⊆ Z.ty σ) → LocMaps Z A → ∃ h, MapsTo Z A h := by
  intro E _ _ _ H Dw Xo p W Y i₀ i X π ty A Z hp hW hgeo hF hty hloc

  have hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z.X := (geoOf Z).normal
  have : IsDiscreteValuationRing (Z.i.c.V W) := isDiscreteValuationRing_V _ W hp hW
  have hZp : IsProper Z.s := by
    have := projProper _ _ _ (geoOf Z).proj
    rwa [Z.π_s] at this
  have : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  have : CompactSpace Z.X := QuasiCompact.compactSpace_of_compactSpace Z.s
  have : IsNoetherian Z.X := {}
  have hXp : IsProper (π ≫ (Y i).s) := projProper _ _ _ hgeo.proj
  have hopen : IsOpen Z.opn := by
    rw [← Z.cover]
    exact isOpen_iUnion fun a => (Z.U a).1.isOpen
  have hdom : ∀ x : Z.X, IsDomain (Z.X.presheaf.stalk x) := fun x => (hn x).1

  choose g hgx hgmin using fun x : Z.X => exists_gen Z.X x (hdom x)
  have hgo : ∀ x, g x ∈ Z.opn := fun x => by
    obtain ⟨g', hg', hg'x⟩ := GlobalTheory.ShFam.EigLoc.exists_generisation hopen Z.dense x
    exact (hgmin x g' hg'x).mem_open hopen hg'
  have hgen : ∀ x y, y ⤳ g x → y = g x := fun x y hy =>
    (hy.antisymm (hgmin x y (hy.trans (hgx x)))).eq

  let f : ∀ x : Z.X, Z.X.presheaf.stalk x →+* Z.X.residueField (g x) := fun x =>
    (Z.X.presheaf.stalkSpecializes (hgx x) ≫ Z.X.residue (g x)).hom
  have hfr : ∀ x, @IsFractionRing (Z.X.presheaf.stalk x) _ (Z.X.residueField (g x)) _ (f x).toAlgebra := fun x =>
    isFractionRing_residue Z.X x (g x) (hgx x) (hdom x) (hgen x)
  have hinj : ∀ x, Function.Injective (f x) := fun x => by
    letI := (f x).toAlgebra
    haveI := hfr x
    exact IsFractionRing.injective (Z.X.presheaf.stalk x) (Z.X.residueField (g x))
  have key : ∀ x, spMap (f x) ≫ Z.X.fromSpecStalk x = Z.X.fromSpecResidueField (g x) := fun x => by
    show Spec.map (_ ≫ _) ≫ _ = _
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    rfl

  have Hy : ∀ ξ : Z.opn, ∃ y : Sp (Z.X.residueField ξ.1) ⟶ X, NatTo Z A (Z.X.fromSpecResidueField ξ.1) y ∧
      ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R] [Algebra R (Z.X.residueField ξ.1)]
        [IsFractionRing R (Z.X.residueField ξ.1)] (z : Sp R ⟶ Z.X),
        spMap (algebraMap R (Z.X.residueField ξ.1)) ≫ z = Z.X.fromSpecResidueField ξ.1 →
        ∃ z' : Sp R ⟶ X, spMap (algebraMap R (Z.X.residueField ξ.1)) ≫ z' = y := fun ξ =>
    hloc _ _ (by
      rintro _ ⟨q, rfl⟩
      exact Set.mem_of_eq_of_mem (Scheme.fromSpecResidueField_apply ξ.1 _) ξ.2)
  choose y hyN hyE using Hy

  have Hh : ∀ x : Z.X, ∃ z' : Sp (Z.X.presheaf.stalk x) ⟶ X, spMap (f x) ≫ z' = y ⟨g x, hgo x⟩ := fun x => by
    letI := (f x).toAlgebra
    haveI := hfr x
    haveI := hdom x
    haveI := (hn x).2
    exact hyE ⟨g x, hgo x⟩ (Z.X.presheaf.stalk x) (Z.X.fromSpecStalk x) (key x)
  choose h hh using Hh
  have hh' : ∀ x ξ (e : ξ ⤳ x), g x = ξ → ∀ hξ : ξ ∈ Z.opn,
      Spec.map (Z.X.presheaf.stalkSpecializes e ≫ Z.X.residue ξ) ≫ h x = y ⟨ξ, hξ⟩ := by
    rintro x ξ e rfl hξ
    exact hh x

  let b : i.c.V W →+* Z.i.c.V W :=
    ((IntermediateField.inclusion hF).toRingHom.comp (i.c.V W).subtype).codRestrict (Z.i.c.V W) fun x => x.2
  have hovr : ∀ {K : Type} [Field K] (w : Sp K ⟶ Z.X) (y' : Sp K ⟶ X), NatTo Z A w y' →
      y' ≫ π ≫ (Y i).s = w ≫ Z.s ≫ spMap b := by
    rintro K _ w y' ⟨τ, mu, u, ⟨b', π', r, hb', h1, h2, -⟩, he, -, -⟩
    have eb : b' = b := RingHom.ext fun v => Subtype.ext (Subtype.ext (hb' v))
    subst eb
    rw [← Category.assoc, he, ← h1, ← Z.π_s]
    simp only [Category.assoc]
    rw [pullback.condition, reassoc_of% h2]
  have hover : ∀ x, h x ≫ π ≫ (Y i).s = Z.X.fromSpecStalk x ≫ Z.s ≫ spMap b := fun x => by
    apply spMap_cancel (f x) (hinj x)
    rw [← Category.assoc, hh x]
    exact (hovr (Z.X.fromSpecResidueField (g x)) (y ⟨g x, hgo x⟩) (hyN ⟨g x, hgo x⟩)).trans (by rw [← key x]; exact Category.assoc _ _ _)

  obtain ⟨gg, hgg⟩ := GlobalTheory.T.exists_morphism_of_stalk_maps (Sp (i.c.V W)) Z.X X (Z.s ≫ spMap b) (π ≫ (Y i).s) h inferInstance inferInstance
    inferInstance hn hover (by
      intro x ξ e hξ
      have hxg : g x = ξ := hξ _ (hgmin x ξ e)
      have hξg : g ξ = ξ := hξ _ (hgx ξ)
      have hξo : ξ ∈ Z.opn := hxg ▸ hgo x
      have hi : Function.Injective (Z.X.residue ξ).hom := by
        letI := (Z.X.presheaf.stalkSpecializes (specializes_refl ξ) ≫ Z.X.residue ξ).hom.toAlgebra
        haveI := isFractionRing_residue Z.X ξ ξ (specializes_refl ξ) (hdom ξ) hξ
        have := IsFractionRing.injective (Z.X.presheaf.stalk ξ) (Z.X.residueField ξ)
        rwa [RingHom.algebraMap_toAlgebra, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] at this
      haveI : IsIso (Z.X.residue ξ) := (ConcreteCategory.isIso_iff_bijective _).2 ⟨hi, Scheme.residue_surjective _ _⟩
      rw [← cancel_epi (Spec.map (Z.X.residue ξ)), ← Category.assoc, ← Spec.map_comp, hh' x ξ e hxg hξo]
      have := hh' ξ ξ (specializes_refl ξ) hξg hξo
      rw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] at this
      exact this.symm)

  refine ⟨gg, fun k _ w hw => ?_⟩
  obtain ⟨x, hx⟩ : ∃ x, w (IsLocalRing.closedPoint k) = x := ⟨_, rfl⟩
  obtain ⟨ψ, hψ⟩ := GlobalTheory.ShFam.EigLoc.exists_stalk_factor w x (hx ▸ specializes_rfl)
  have hxo : x ∈ Z.opn := hx ▸ hw ⟨_, rfl⟩
  have e1 : w ≫ gg = spMap ψ ≫ h x := by rw [← hψ, Category.assoc, hgg]
  rw [e1, ← hψ]
  refine GlobalTheory.T.atlas_local_ring_points E H Dw Xo p W Y i₀ i X π ty A Z (Z.X.presheaf.stalk x) (Z.X.residueField (g x)) k (f x) ψ
    (Z.X.fromSpecStalk x) (h x) hF hty (hinj x) (by rw [Scheme.fromSpecStalk_closedPoint]; exact hxo) ?_
  rw [key x, hh x]
  exact hyN ⟨g x, hgo x⟩
end

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atlas_model_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (i : Idx H p) (X : Scheme.{0}) (π : X ⟶ (Y i).X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas (Y i) π ty) (Z : Mdl Y i₀), p.Prime → (p : ℂ) ∈ W.nonunits → Geo (Y i) π → i.c.F ≤ Z.i.c.F → (∀ σ, ty σ ⊆ Z.ty σ) → LocMaps Z A → ∃ h, MapsTo Z A h := by
  atlas_forward_decl GlobalTheory.DRFlag.exists_mapsTo
end
