import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KernelTrivialOfEveryPointCovered
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitPointEqOfIso
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DegenerationDataCoordsNeZeroLatticesIsomorphic
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsGrpPullbackPtC
import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.HomExtendsOverDVRHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperOfAbelianEverywhereStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsAffineOpenPreimageBasicOpen

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam GlobalTheory.LocM
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.PolFibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {S : Scheme.{0}}
  {t : SAB H S} {K : Type} [Field K] {x : Sp K ⟶ S} {u : SAB H (Sp K)}

theorem exists_to_fibre (m : SABMap u t x) :
    ∃ φ : u.G.left ⟶ ((Over.pullback x).obj t.G).left, IsGrpPullback u.G ((Over.pullback x).obj t.G) (𝟙 _) φ ∧
      LBIso u.PP.L ((t.PP.L.pull (pullback.fst t.G.hom x)).pull φ) := by
  have hM := pull_isLB t.PP.isLB (pullback.fst t.G.hom x)
  obtain ⟨φ, hφ, e, -⟩ := GlobalTheory.Ex.UnifModel.exists_cancel (g := 𝟙 _) (f := x) (m.cart.congr (Category.id_comp _).symm rfl)
    (isGrpPullback_pullback t.G x) t.PP.isLB hM u.PP.isLB (GlobalTheory.Ex.UnifModel.iso_of_map m)
    ⟨Out.CubePf.idIsoL _, Out.CubePf.idIsoL_isGen hM⟩
  exact ⟨φ, hφ, e⟩

theorem exists_of_fibre (m : SABMap u t x) :
    ∃ φ : ((Over.pullback x).obj t.G).left ⟶ u.G.left, IsGrpPullback ((Over.pullback x).obj t.G) u.G (𝟙 _) φ ∧
      LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (u.PP.L.pull φ) := by
  have hM := pull_isLB t.PP.isLB (pullback.fst t.G.hom x)
  obtain ⟨φ, hφ, e, -⟩ := GlobalTheory.Ex.UnifModel.exists_cancel (g := 𝟙 _) (f := x)
    ((isGrpPullback_pullback t.G x).congr (Category.id_comp _).symm rfl) m.cart t.PP.isLB u.PP.isLB hM
    ⟨Out.CubePf.idIsoL _, Out.CubePf.idIsoL_isGen hM⟩ (GlobalTheory.Ex.UnifModel.iso_of_map m)
  exact ⟨φ, hφ, e⟩

theorem ample_kTriv_of_polAt (m : SABMap u t x) (hp : GlobalTheory.LN.PolAt t x) :
    RelAmple u.G u.PP.L ∧ KTriv u.G u.PP.L := by
  obtain ⟨φ, hφ, e⟩ := exists_to_fibre m
  exact amplePt _ _ (𝟙 _) _ _ φ hφ _ _ (pull_isLB t.PP.isLB _) u.PP.isLB e hp.2.1 hp.2.2

theorem polAt_of_map (m : SABMap u t x) (hp : IsProper (pullback.snd t.G.hom x)) (hA : RelAmple u.G u.PP.L)
    (hK : KTriv u.G u.PP.L) : GlobalTheory.LN.PolAt t x := by
  obtain ⟨φ, hφ, e⟩ := exists_of_fibre m
  have h := amplePt _ _ (𝟙 _) _ _ φ hφ _ _ u.PP.isLB (pull_isLB t.PP.isLB _) e hA hK
  exact ⟨hp, h.1, h.2⟩

end GlobalTheory.LocM.PolFibre
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PolNearAmple

theorem relAmple_near_of_polAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] (t : SAB H (Sp R)), IsProper t.G.hom → ∀ (C : Type) [Field C] (g : R →+* C), GlobalTheory.LN.PolAt t (spMap g) → ∃ s : R, g s ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (h : R →+* R'), IsUnit (h s) → ∀ (t' : SAB H (Sp R')), SABMap t' t (spMap h) → RelAmple t'.G t'.PP.L := by
  intro E _ _ _ H R _ _ t hprop C _ g hpol
  have : Smooth t.G.hom := t.semi.smooth
  have : Flat t.G.hom := inferInstance
  have hL := t.PP.isLB
  let p : Ideal R := RingHom.ker g
  haveI : p.IsPrime := RingHom.ker_isPrime g
  let g₀ := algebraMap R p.ResidueField
  have hf₂ : p.primeCompl ≤ (IsUnit.submonoid C).comap g := fun x hx =>
    show IsUnit (g x) from isUnit_iff_ne_zero.2 fun h0 => hx (RingHom.mem_ker.2 h0)
  let i : p.ResidueField →+* C := Ideal.ResidueField.lift p g le_rfl hf₂
  have hcomp : i.comp g₀ = g := RingHom.ext fun r => Ideal.ResidueField.lift_algebraMap p g le_rfl hf₂ r
  have hsp : spMap i ≫ spMap g₀ = spMap g := by
    rw [← hcomp]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have h₂ : IsPullback (pullback.fst t.G.hom (spMap g)) (pullback.snd t.G.hom (spMap g)) t.G.hom
      (spMap i ≫ spMap g₀) := by
    rw [hsp]; exact IsPullback.of_hasPullback _ _
  have hA₁ : RelAmple ((Over.pullback (spMap g₀)).obj t.G) (t.PP.L.pull (pullback.fst t.G.hom (spMap g₀))) :=
    FibreAmple.relAmple_of_fieldExtension (f := t.G.hom) hL i (IsPullback.of_hasPullback t.G.hom (spMap g₀)) h₂
      (pull_isLB hL _) (GlobalTheory.lbIso_refl (pull_isLB hL _)) hpol.2.1
  obtain ⟨s, hs, hAs⟩ := ProperFinite.relAmple_near_fibre t.G hL g₀ (FibreAmple.residueField_fraction p) hA₁
  refine ⟨s, fun h0 => hs (Ideal.algebraMap_residueField_eq_zero.2 (RingHom.mem_ker.2 h0)), ?_⟩
  intro R' _ h hu t' m
  let D : (Sp R).Opens := PrimeSpectrum.basicOpen s
  have : IsAffine D.toScheme := IsAffineOpen.Spec_basicOpen (R := CommRingCat.of R) s
  have hrange : Set.range (spMap h) ⊆ Set.range D.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    show s ∉ Ideal.comap h y.asIdeal
    exact fun hy => y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hy hu)
  let u : Sp R' ⟶ D.toScheme := IsOpenImmersion.lift D.ι (spMap h) hrange
  have hu' : u ≫ D.ι = spMap h := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ, hφ, Hp⟩ := FibreAmple.exists_isPullback (IsPullback.of_hasPullback t.G.hom D.ι) m.cart.1 u hu'
  have e₀ : LBIso t'.PP.L (t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := (isPullCubical_iff m.cm t.cub t'.cub).1 m.lin
    exact ⟨w, (isGen_iff w).2 hw⟩
  obtain ⟨w, hw⟩ : LBIso t'.PP.L ((t.PP.L.pull (pullback.fst t.G.hom D.ι)).pull φ) :=
    LBIso.trans t'.PP.isLB (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) e₀
      (FibreAmple.lbIso_pull_comp hφ (GlobalTheory.lbIso_refl (pull_isLB hL _)))
  exact relAmple_pull (A := (Over.pullback D.ι).obj t.G) (A' := t'.G) Hp (pull_isLB hL _) t'.PP.isLB
    ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) hAs

end GlobalTheory.PolNearAmple
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relative_ample_spread_of_polarized_fiber : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] (t : SAB H (Sp R)), IsProper t.G.hom → ∀ (C : Type) [Field C] (g : R →+* C), GlobalTheory.LN.PolAt t (spMap g) → ∃ s : R, g s ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (h : R →+* R'), IsUnit (h s) → ∀ (t' : SAB H (Sp R')), SABMap t' t (spMap h) → RelAmple t'.G t'.PP.L := by
  first | exact @GlobalTheory.PolNearAmple.relAmple_near_of_polAt | exact GlobalTheory.PolNearAmple.relAmple_near_of_polAt | (intros; apply GlobalTheory.PolNearAmple.relAmple_near_of_polAt <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.KTrivSpread

namespace GlobalTheory.KTrivGenericPt

theorem spMap_eq_lift_comp_jK {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] (ψ : R →+* F)
    (hψ : Function.Injective ψ) :
    spMap ψ = spMap (IsFractionRing.lift (K := FractionRing R) hψ) ≫ Out.jK R := by
  rw [Out.jK, spMap, spMap, ← Spec.map_comp]
  congr 1
  ext r
  simp

theorem trivAlong_field {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {R : Type} [CommRing R] [IsDomain R]
    {g : Sp R ⟶ S} (h : TrivAlong A L (Out.jK R ≫ g)) {F : Type} [Field F] (ψ : R →+* F)
    (hψ : Function.Injective ψ) : TrivAlong A L (spMap ψ ≫ g) := by
  rw [spMap_eq_lift_comp_jK ψ hψ, Category.assoc]
  exact h.comp _

end GlobalTheory.KTrivGenericPt

open GlobalTheory.KTrivGenericPt in

theorem GlobalTheory.KTrivGenericPt.kTriv_of_polAt_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (t : SAB H (Sp R)), IsProper t.G.hom → RelAmple t.G t.PP.L → GlobalTheory.LN.PolAt t (jK R) → KTriv t.G t.PP.L := by
  intro E _ _ _ H R _ _ _ _ t hP ha hpol
  haveI : IsProper t.G.hom := hP
  have hA : IsAbelianScheme t.G := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  have hgen : TrivAlong t.G t.PP.L (Out.jK R) :=
    trivAlong_of_kTriv (isGrpPullback_pullback t.G (Out.jK R)) t.PP.isLB hpol.2.2
  have hgen' : TrivAlong t.G t.PP.L (Out.jK R ≫ 𝟙 (Sp R)) := by rw [Category.comp_id]; exact hgen
  refine kTriv_of_primes hG R t.G hA t.PP.L t.PP.isLB ha fun p => ?_
  let O := Localization.AtPrime p.asIdeal
  have hO : Function.Injective (algebraMap R O) := IsLocalization.injective O p.asIdeal.primeCompl_le_nonZeroDivisors
  have hp : PrimeSpectrum.comap (algebraMap R O) (IsLocalRing.closedPoint O) = p :=
    PrimeSpectrum.ext Localization.AtPrime.under_maximalIdeal
  by_cases hf : IsField O
  · refine ⟨O, inferInstance, algebraMap R O, ⟨_, hp⟩, ?_⟩
    letI := hf.toField
    have := trivAlong_field hgen' (algebraMap R O) hO
    rwa [Category.comp_id] at this
  · obtain ⟨V, _, _, _, ρ, h1, h2⟩ := exists_dvr O hf
    have hρ : Function.Injective (ρ.comp (algebraMap R O)) := h1.comp hO
    have : CharZero V := charZero_of_injective_ringHom hρ
    refine ⟨V, inferInstance, ρ.comp (algebraMap R O), ⟨IsLocalRing.closedPoint V, ?_⟩, ?_⟩
    · rw [PrimeSpectrum.comap_comp_apply, IsLocalRing.comap_closedPoint, hp]
    · have key := trivAlong_dvr hG (𝟙 (Sp R)) hA t.PP t.cub ha V (spMap (ρ.comp (algebraMap R O))) ?_
      · rwa [Category.comp_id] at key
      · let F := AlgebraicClosure (FractionRing V)
        have H' := trivAlong_field hgen'
          ((algebraMap (FractionRing V) F).comp ((algebraMap V (FractionRing V)).comp (ρ.comp (algebraMap R O))))
          ((algebraMap (FractionRing V) F).injective.comp ((IsFractionRing.injective V (FractionRing V)).comp hρ))
        have e : (Out.TF (R := V) F).hom ≫ spMap (ρ.comp (algebraMap R O)) = spMap ((algebraMap (FractionRing V) F).comp
            ((algebraMap V (FractionRing V)).comp (ρ.comp (algebraMap R O)))) :=
          (congrArg (· ≫ _) (Spec.map_comp _ _).symm).trans (Spec.map_comp _ _).symm
        rw [← e, Category.assoc] at H'
        exact H'
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_trivial_of_relative_ample : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (t : SAB H (Sp R)), IsProper t.G.hom → RelAmple t.G t.PP.L → GlobalTheory.LN.PolAt t (jK R) → KTriv t.G t.PP.L := by
  first | exact @GlobalTheory.KTrivGenericPt.kTriv_of_polAt_generic | exact GlobalTheory.KTrivGenericPt.kTriv_of_polAt_generic | (intros; apply GlobalTheory.KTrivGenericPt.kTriv_of_polAt_generic <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PolNear

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem polAt_generic {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R R' : Type} [CommRing R]
    [IsDomain R] [CommRing R'] [IsDomain R'] (b : R →+* R') (hb : Function.Injective b) {t : SAB H (Sp R)}
    {t' : SAB H (Sp R')} (m : SABMap t' t (spMap b)) (hp : GlobalTheory.LN.PolAt t (jK R)) : GlobalTheory.LN.PolAt t' (jK R') := by
  have hi : Function.Injective ((algebraMap R' (FractionRing R')).comp b) :=
    (IsFractionRing.injective R' (FractionRing R')).comp hb
  refine GlobalTheory.DatUniq.polAt_pull m hp (jK R') (spMap (IsFractionRing.lift (K := FractionRing R) hi)) ?_
  have e : (IsFractionRing.lift (K := FractionRing R) hi).comp (algebraMap R (FractionRing R)) =
      (algebraMap R' (FractionRing R')).comp b :=
    RingHom.ext fun x => IsFractionRing.lift_algebraMap (K := FractionRing R) hi x
  have e' := congrArg spMap e
  rw [spMap_comp' (algebraMap R (FractionRing R)) (IsFractionRing.lift (K := FractionRing R) hi),
    spMap_comp' b (algebraMap R' (FractionRing R'))] at e'
  exact e'

theorem exists_near : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R], IsIntegrallyClosed R → ∀ (t : SAB H (Sp R)), GlobalTheory.LN.PolAt t (jK R) → ∀ (C : Type) [Field C] (g : R →+* C), GlobalTheory.LN.PolAt t (spMap g) → ∃ r : R, g r ≠ 0 ∧ ∃ (t' : SAB H (Sp (Localization.Away r))) (_ : SABMap t' t (spMap (algebraMap R (Localization.Away r)))), IsProper t'.G.hom ∧ RelAmple t'.G t'.PP.L ∧ KTriv t'.G t'.PP.L := by
  intro E _ _ _ H R _ _ _ _ _ _ t hgen C _ g hp

  have hsub : Set.range (spMap g) ⊆ abLocus t.G := abLocusOne _ t.G t.semi C (spMap g) hp.1
  have hop : IsOpen (abLocus t.G) := GlobalTheory.AbLocusOpen.isOpen_abLocus_local t.G t.semi
  obtain ⟨y⟩ : Nonempty (PrimeSpectrum C) := inferInstance
  obtain ⟨_, ⟨r₁, rfl⟩, hq, hsub₁⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open (hsub ⟨y, rfl⟩) hop
  have hg₁ : g r₁ ≠ 0 := by
    intro h0
    refine (PrimeSpectrum.mem_basicOpen _ _).1 hq ?_
    show g r₁ ∈ y.asIdeal
    rw [h0]; exact zero_mem _
  have hr₁ : r₁ ≠ 0 := fun h => hg₁ (by rw [h, map_zero])
  let R₁ := Localization.Away r₁
  have hM₁ : Submonoid.powers r₁ ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hr₁
  haveI : IsDomain R₁ := IsLocalization.isDomain_localization hM₁
  haveI : IsNoetherianRing R₁ := IsLocalization.isNoetherianRing (Submonoid.powers r₁) R₁ inferInstance
  have hinj₁ : Function.Injective (algebraMap R R₁) := IsLocalization.injective R₁ hM₁

  obtain ⟨t₁, ⟨m₁⟩⟩ := exists_sab (spMap (algebraMap R R₁)) t
  have hab : abLocus t₁.G = Set.univ := Set.eq_univ_of_forall fun x =>
    (abLocus_pullback abLocusOne t.semi m₁.cart.1 x).1 (hsub₁ (by
      have hx : spMap (algebraMap R R₁) x ∈ Set.range (PrimeSpectrum.comap (algebraMap R R₁)) := ⟨x, rfl⟩
      rwa [PrimeSpectrum.localization_away_comap_range R₁ r₁] at hx))
  have hgen₁ : GlobalTheory.LN.PolAt t₁ (jK R₁) := polAt_generic _ hinj₁ m₁ hgen
  haveI : CharZero R₁ := charZero_of_injective_ringHom hinj₁
  have hP₁ : IsProper t₁.G.hom := GlobalTheory.T.proper_of_abelian_everywhere E H R₁ t₁ hgen₁ hab

  let g₁ : R₁ →+* C := IsLocalization.Away.lift r₁ (Ne.isUnit hg₁)
  have hgg : g₁.comp (algebraMap R R₁) = g := IsLocalization.lift_comp _
  have hp₁ : GlobalTheory.LN.PolAt t₁ (spMap g₁) :=
    GlobalTheory.DatUniq.polAt_pull m₁ hp (spMap g₁) (𝟙 _) (by rw [Category.id_comp, ← spMap_comp', hgg])

  obtain ⟨s, hs, hamp⟩ := GlobalTheory.T.relative_ample_spread_of_polarized_fiber E H R₁ t₁ hP₁ C g₁ hp₁
  obtain ⟨⟨a, _, ⟨n, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers r₁) s
  simp only at ha

  have hga : g a ≠ 0 := by
    have e : g a = g₁ s * g (r₁ ^ n) := by rw [← hgg, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, ha]
    rw [e, map_pow]
    exact mul_ne_zero hs (pow_ne_zero _ hg₁)
  have hgr : g (r₁ * a) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hg₁ hga
  have hr : r₁ * a ≠ 0 := fun h0 => hgr (by rw [h0, map_zero])
  refine ⟨r₁ * a, hgr, ?_⟩

  let R' := Localization.Away (r₁ * a)
  have hM : Submonoid.powers (r₁ * a) ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hr
  haveI : IsDomain R' := IsLocalization.isDomain_localization hM
  haveI : IsNoetherianRing R' := IsLocalization.isNoetherianRing (Submonoid.powers (r₁ * a)) R' inferInstance
  have hinj : Function.Injective (algebraMap R R') := IsLocalization.injective R' hM
  haveI : CharZero R' := charZero_of_injective_ringHom hinj
  have hu : IsUnit (algebraMap R R' (r₁ * a)) := IsLocalization.Away.algebraMap_isUnit (r₁ * a)
  rw [map_mul] at hu
  let h : R₁ →+* R' := IsLocalization.Away.lift r₁ (isUnit_of_mul_isUnit_left hu)
  have hh : h.comp (algebraMap R R₁) = algebraMap R R' := IsLocalization.lift_comp _
  have hhs : IsUnit (h s) := by
    have e : h s * algebraMap R R' (r₁ ^ n) = algebraMap R R' a := by
      rw [← hh, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, ha]
    exact isUnit_of_mul_isUnit_left (e ▸ isUnit_of_mul_isUnit_right hu)

  obtain ⟨t', ⟨m'⟩⟩ := exists_sab (spMap h) t₁
  obtain ⟨n', -⟩ := sabComp pullCubComp E H _ _ _ t t₁ t' _ _ m₁ m'
  have ee : spMap h ≫ spMap (algebraMap R R₁) = spMap (algebraMap R R') := by rw [← spMap_comp', hh]
  have hP' : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m'.cart.1 hP₁
  have hA' : RelAmple t'.G t'.PP.L := hamp R' h hhs t' m'
  exact ⟨t', ee ▸ n', hP', hA', GlobalTheory.T.canonical_trivial_of_relative_ample E H R' t' hP' hA' (polAt_generic _ hinj (ee ▸ n') hgen)⟩

end GlobalTheory.PolNear
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_after_localization : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R], IsIntegrallyClosed R → ∀ (t : SAB H (Sp R)), GlobalTheory.LN.PolAt t (jK R) → ∀ (C : Type) [Field C] (g : R →+* C), GlobalTheory.LN.PolAt t (spMap g) → ∃ r : R, g r ≠ 0 ∧ ∃ (t' : SAB H (Sp (Localization.Away r))) (_ : SABMap t' t (spMap (algebraMap R (Localization.Away r)))), IsProper t'.G.hom ∧ RelAmple t'.G t'.PP.L ∧ KTriv t'.G t'.PP.L := by
  atlas_forward_decl GlobalTheory.PolNear.exists_near
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolLocal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem pull_ample_kTriv {S S' : Scheme.{0}} [IsAffine S] {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S}
    (m : SABMap t' t f) (hA : Out.RelAmple t.G t.PP.L) (hK : Out.KTriv t.G t.PP.L) :
    Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨relAmple_pull m.cart.1 t.PP.isLB t'.PP.isLB ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top S)
    (fun _ => trivial) hA, kTriv_pull m.cart t.PP.isLB t'.PP.isLB ((isGen_iff w).1 hw) hK⟩

theorem ample_kTriv_of_iso {S S' : Scheme.{0}} [IsAffine S'] {t : SAB H S} {u : SAB H S'} {j : S' ⟶ S} [IsIso j]
    (m : SABMap u t j) (hA : Out.RelAmple u.G u.PP.L) (hK : Out.KTriv u.G u.PP.L) :
    Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  obtain ⟨n, -⟩ := GlobalTheory.ObjMaps.exists_sab_id t
  obtain ⟨m', -⟩ := GlobalTheory.ArcObj.exists_sab_fac m n (g := inv j) (by simp)
  exact pull_ample_kTriv m' hA hK

theorem isIso_spMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (hf : Function.Bijective f) :
    IsIso (spMap f) := by
  have : IsIso (CommRingCat.ofHom f) := (RingEquiv.ofBijective f hf).toCommRingCatIso.isIso_hom
  unfold spMap
  infer_instance

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

theorem isProper_of_map {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    (hp : IsProper t.G.hom) : IsProper t'.G.hom :=
  MorphismProperty.of_isPullback m.cart.1 hp

end GlobalTheory.PolLocal

namespace GlobalTheory.PolLocal

theorem algebraMap_fractionRing_bijective (O : Type) [CommRing O] [IsDomain O] (hf : IsField O) :
    Function.Bijective (algebraMap O (FractionRing O)) := by
  refine ⟨IsFractionRing.injective O (FractionRing O), fun z => ?_⟩
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.surj (nonZeroDivisors O) z
  obtain ⟨b, hb⟩ := hf.mul_inv_cancel (nonZeroDivisors.ne_zero y.2)
  refine ⟨x * b, ?_⟩
  calc algebraMap O (FractionRing O) (x * b) = z * algebraMap O (FractionRing O) (y * b) := by
        rw [map_mul, map_mul, ← mul_assoc, ← hxy]
    _ = z := by rw [hb, map_one, mul_one]

theorem algebraMap_away_bijective {O : Type} [CommRing O] (r : O) (hr : IsUnit r) :
    Function.Bijective (algebraMap O (Localization.Away r)) := by
  have e := IsLocalization.atUnit O (Localization.Away r) r hr
  have h : ⇑(algebraMap O (Localization.Away r)) = ⇑e := funext fun x => by
    simpa using (e.commutes x).symm
  rw [h]
  exact e.bijective

theorem relAmple_kTriv_of_polAt_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (O : Type)
    [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [CharZero O], IsIntegrallyClosed O →
    ∀ (t : SAB H (Sp O)), IsProper t.G.hom → GlobalTheory.LN.PolAt t (Out.jK O) →
      Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  intro E _ _ _ H O _ _ _ _ _ hIC t hprop hpol
  by_cases hf : IsField O
  · obtain ⟨u, ⟨mu⟩⟩ := exists_pull (Out.jK O) t
    obtain ⟨hA, hK⟩ := GlobalTheory.LocM.PolFibre.ample_kTriv_of_polAt mu hpol
    haveI : IsIso (Out.jK O) := isIso_spMap _ (algebraMap_fractionRing_bijective O hf)
    exact ample_kTriv_of_iso mu hA hK
  obtain ⟨V, _, _, _, ρ, hρ, hloc⟩ := GlobalTheory.KTrivSpread.exists_dvr O hf
  obtain ⟨tV, ⟨mV⟩⟩ := exists_pull (spMap ρ) t
  obtain ⟨tK, ⟨mK⟩⟩ := exists_pull (spMap (algebraMap V (FractionRing V))) tV
  let ψ : FractionRing O →+* FractionRing V := IsLocalization.map (M := nonZeroDivisors O) (T := nonZeroDivisors V)
    (FractionRing V) ρ (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective ρ hρ)
  have heq : spMap ψ ≫ Out.jK O = Out.jK V ≫ spMap ρ := by
    show spMap ψ ≫ spMap (algebraMap O (FractionRing O)) = spMap (algebraMap V (FractionRing V)) ≫ spMap ρ
    rw [← spMap_comp, ← spMap_comp, IsLocalization.map_comp]
  have hpV : GlobalTheory.LN.PolAt tV (Out.jK V) := GlobalTheory.DatUniq.polAt_pull mV hpol (Out.jK V) (spMap ψ) heq
  obtain ⟨hAK, hKK⟩ := GlobalTheory.LocM.PolFibre.ample_kTriv_of_polAt mK hpV
  obtain ⟨hAV, hKV⟩ := GlobalTheory.PolDvr.relAmple_kTriv_of_generic_fibre GlobalTheory.HomExtExamples.homExtSt_holds GlobalTheory.allSixLaws.1
    GlobalTheory.allSixLaws.2.1 E H V (FractionRing V) tV tK mK (isProper_of_map mV hprop) hAK hKK
  obtain ⟨uk, ⟨mk⟩⟩ := exists_pull (spMap (IsLocalRing.residue V)) tV
  obtain ⟨hAk, hKk⟩ := pull_ample_kTriv mk hAV hKV
  obtain ⟨n, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp mV mk
  let β : O →+* IsLocalRing.ResidueField V := (IsLocalRing.residue V).comp ρ
  have hpβ : GlobalTheory.LN.PolAt t (spMap β) := by
    rw [spMap_comp]
    exact GlobalTheory.LocM.PolFibre.polAt_of_map n (by haveI := hprop; infer_instance) hAk hKk
  obtain ⟨r, hr, t', m', -, hA', hK'⟩ := GlobalTheory.T.proper_after_localization E H O hIC t hpol (IsLocalRing.ResidueField V) β hpβ
  have hu : IsUnit r := isUnit_of_map_unit ρ r ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 hr)
  haveI := isIso_spMap _ (algebraMap_away_bijective r hu)
  exact ample_kTriv_of_iso m' hA' hK'

end GlobalTheory.PolLocal
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relative_ample_canonical_trivial_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [CharZero O], IsIntegrallyClosed O → ∀ (t : SAB H (Sp O)), IsProper t.G.hom → GlobalTheory.LN.PolAt t (Out.jK O) → Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  first | exact @GlobalTheory.PolLocal.relAmple_kTriv_of_polAt_generic | exact GlobalTheory.PolLocal.relAmple_kTriv_of_polAt_generic | (intros; apply GlobalTheory.PolLocal.relAmple_kTriv_of_polAt_generic <;> assumption)
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open TopologicalSpace

namespace GlobalTheory.AmpleSpreadAt

open GlobalTheory.SecSpread GlobalTheory.LBGerm

variable {R : Type} [CommRing R] {q : PrimeSpectrum R}
  {X X' : Scheme.{0}} {p : X ⟶ Sp R} {φ : X' ⟶ X} {π : X' ⟶ Sp (Localization.AtPrime q.asIdeal)}

theorem exists_denom (H : IsPullback φ π p (spMap (algebraMap R (Localization.AtPrime q.asIdeal)))) {U : X.Opens}
    (hU : IsAffineOpen U) (t : Γ(X', φ ⁻¹ᵁ U)) :
    ∃ d ∈ q.asIdeal.primeCompl, ∃ a : Γ(X, U), (φ.app U).hom (constFn p U d) * t = (φ.app U).hom a := by
  let _ := (φ.app U).hom.toAlgebra
  have hl := GlobalTheory.QCoh.Qcqs.isLocalization_app (R := .of R) (L := .of (Localization.AtPrime q.asIdeal))
    q.asIdeal.primeCompl H hU
  obtain ⟨⟨a, ⟨_, d, hd, rfl⟩⟩, e⟩ := @IsLocalization.surj _ _ _ _ _ _ hl t
  exact ⟨d, hd, a, (mul_comm _ _).trans e⟩

theorem exists_const_mul_eq_zero (H : IsPullback φ π p (spMap (algebraMap R (Localization.AtPrime q.asIdeal))))
    {U : X.Opens} (hU : IsAffineOpen U) (a : Γ(X, U)) (h : ∀ z, φ z ∈ U → gs φ z U a = 0) :
    ∃ d ∈ q.asIdeal.primeCompl, ∀ y ∈ U, cst p y d * gs (𝟙 X) y U a = 0 := by
  have e : (φ.app U).hom a = 0 := fn_ext fun z hz => by
    have hz' : φ z ∈ U := hz
    refine (gs_pull (𝟙 X') φ z U hz' _).trans ?_
    rw [Category.id_comp, h z hz', gs_zero (𝟙 X') z _ hz]
  let _ := (φ.app U).hom.toAlgebra
  have hl := GlobalTheory.QCoh.Qcqs.isLocalization_app (R := .of R) (L := .of (Localization.AtPrime q.asIdeal))
    q.asIdeal.primeCompl H hU
  obtain ⟨⟨_, d, hd, rfl⟩, hm⟩ := (@IsLocalization.map_eq_zero_iff _ _ _ _ _ _ hl a).1 e
  refine ⟨d, hd, fun y hy => ?_⟩
  have e' := congrArg (gs (𝟙 X) y U) (show constFn p U d * a = 0 from hm)
  rwa [gs_mul _ y _ hy, gs_constFn p U _ y hy, Category.id_comp, gs_zero _ y _ hy] at e'

theorem isUnit_cst (hw : φ ≫ p = π ≫ spMap (algebraMap R (Localization.AtPrime q.asIdeal))) (z : X') {d : R}
    (hd : d ∈ q.asIdeal.primeCompl) : IsUnit (cst (φ ≫ p) z d) := by
  have hu : IsUnit (algebraMap R (Localization.AtPrime q.asIdeal) d) :=
    IsLocalization.map_units (Localization.AtPrime q.asIdeal) (⟨d, hd⟩ : q.asIdeal.primeCompl)
  rw [hw, cst, ← gs_pull π _ z ⊤ trivial]
  have e := congrArg (gs π z ⊤) (spMap_appTop (algebraMap R (Localization.AtPrime q.asIdeal)) d)
  refine (congrArg IsUnit e).mpr ?_
  rw [gs_eq π z ⊤ trivial]
  exact ((hu.map _).map _).map _

theorem exists_sec_preimage_nonzeroLocus_eq
    (H : IsPullback φ π p (spMap (algebraMap R (Localization.AtPrime q.asIdeal)))) [CompactSpace X]
    [X.IsSeparated] {L : LB X} (hL : L.IsLB) (s : (L.pull φ).Sec) :
    ∃ θ : L.Sec, φ ⁻¹ᵁ Out.nonzeroLocus θ = Out.nonzeroLocus s := by
  classical
  obtain ⟨α, _, V, c, hV, hle, hc⟩ := exists_finite_affine_refinement hL
  have loc : ∀ x : α, ∃ (d : R) (_ : d ∈ q.asIdeal.primeCompl) (a : Γ(X, V x)), ∀ z, φ z ∈ V x → gs φ z (V x) a =
      cst (φ ≫ p) z d * gs (𝟙 X') z ((L.pull φ).U (fun _ => c x)) (s.f (fun _ => c x)) := by
    intro x
    have hle' : φ ⁻¹ᵁ V x ≤ (L.pull φ).U (fun _ => c x) := fun z hz => mem_pull.2 (hle x hz)
    obtain ⟨d, hd, a, ha⟩ := exists_denom H (hV x) (resG X' hle' (s.f (fun _ => c x)))
    refine ⟨d, hd, a, fun z hz => ?_⟩
    have e := congrArg (gs (𝟙 X') z _) ha
    have hz' : (𝟙 X' : X' ⟶ X') z ∈ φ ⁻¹ᵁ V x := hz
    rw [gs_mul _ z _ hz', gs_res _ z hle' hz', gs_pull (𝟙 X') φ z _ hz, gs_pull (𝟙 X') φ z _ hz,
      Category.id_comp, gs_constFn p _ φ z hz] at e
    exact e.symm
  choose d hd a ha using loc
  obtain ⟨b, hb⟩ : ∃ b : ∀ x, Γ(X, V x), ∀ x z, φ z ∈ V x → gs φ z (V x) (b x) =
      cst (φ ≫ p) z (∏ x, d x) * gs (𝟙 X') z ((L.pull φ).U (fun _ => c x)) (s.f (fun _ => c x)) :=
    ⟨fun x => constFn p _ (∏ w ∈ Finset.univ.erase x, d w) * a x, fun x z hz => by
      rw [gs_mul φ z _ hz, gs_constFn p _ φ z hz, ha x z hz, ← Finset.mul_prod_erase _ d (Finset.mem_univ x), cst_mul]
      ring⟩
  have kill : ∀ xw : α × α, ∃ e : R, e ∈ q.asIdeal.primeCompl ∧ ∀ y ∈ V xw.1 ⊓ V xw.2, cst p y e * (gs (𝟙 X) y _ (b xw.1) -
      (gm (𝟙 X) y (L.U (c xw.1) ⊓ L.U (c xw.2)) (L.g (c xw.1) (c xw.2))).val * gs (𝟙 X) y _ (b xw.2)) = 0 := by
    rintro ⟨x, w⟩
    have l : V x ⊓ V w ≤ L.U (c x) ⊓ L.U (c w) := inf_le_inf (hle x) (hle w)
    have hx : ∀ {Z : Scheme.{0}} (r : Z ⟶ X) (y : Z), r y ∈ V x ⊓ V w → gs r y (V x ⊓ V w) (resG X inf_le_left (b x) -
        resG X l (L.g (c x) (c w)).val * resG X inf_le_right (b w)) =
        gs r y _ (b x) - (gm r y (L.U (c x) ⊓ L.U (c w)) (L.g (c x) (c w))).val * gs r y _ (b w) := fun r y hy => by
      rw [gs_sub _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy, gs_unit r y _ (l hy)]
    obtain ⟨e, he, h⟩ := exists_const_mul_eq_zero H ((hV x).inf (hV w)) _ fun z hz => (hx φ z hz).trans (by
      rw [hb x z hz.1, hb w z hz.2, pull_sec_trans s z (l hz).1 (l hz).2]
      ring)
    exact ⟨e, he, fun y hy => (congrArg _ (hx (𝟙 X) y hy)).symm.trans (h y hy)⟩
  choose e he hk using kill
  obtain ⟨θ, hθ⟩ := exists_sec_of_refinement hL V c hle hc (fun x => constFn p _ (∏ xw, e xw) * b x)
    fun y x w hx hw => by
      have h := hk (x, w) y ⟨hx, hw⟩
      rw [gs_mul _ y _ hx, gs_mul _ y _ hw, gs_constFn p _ _ y hx, gs_constFn p _ _ y hw, Category.id_comp,
        ← Finset.mul_prod_erase _ e (Finset.mem_univ (x, w)), cst_mul]
      linear_combination cst p y (∏ xw ∈ Finset.univ.erase (x, w), e xw) * h
  refine ⟨θ, Opens.ext (Set.ext fun z => ?_)⟩
  obtain ⟨x, hx⟩ := hc (φ z)
  have h₁ := congrArg (φ.stalkMap z).hom (hθ (φ z) (c x) x (hle x hx) hx)
  rw [map_mul, ← gs_stalkMap φ z _ (hle x hx), ← gs_stalkMap φ z _ hx, gs_mul φ z _ hx, gs_constFn p _ φ z hx,
    hb x z hx] at h₁
  refine (mem_nonzeroLocus_iff_pull θ φ z (hle x hx)).trans (Iff.trans ?_
    (mem_nonzeroLocus_iff_isUnit s (k := fun _ => c x) (mem_pull.2 (hle x hx))).symm)
  rw [h₁, IsUnit.mul_iff, IsUnit.mul_iff, IsUnit.mul_iff]
  exact ⟨fun h => h.2.2.2, fun h => ⟨(Units.isUnit _).map _,
    isUnit_cst H.w z (Submonoid.prod_mem _ fun xw _ => he xw),
    isUnit_cst H.w z (Submonoid.prod_mem _ fun x _ => hd x), h⟩⟩

theorem exists_basicOpen_le' {x : Sp R} {V : (Sp R).Opens} (hV : x ∈ V) :
    ∃ f : R, x ∈ (PrimeSpectrum.basicOpen f : (Sp R).Opens) ∧ (PrimeSpectrum.basicOpen f : (Sp R).Opens) ≤ V := by
  obtain ⟨_, ⟨f, rfl⟩, hf, hle⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hV V.isOpen
  exact ⟨f, hf, hle⟩

theorem exists_basicOpen_le {V : (Sp R).Opens} (hV : (q : Sp R) ∈ V) :
    ∃ f : R, f ∉ q.asIdeal ∧ PrimeSpectrum.basicOpen f ≤ V := by
  obtain ⟨f, hf, hle⟩ := exists_basicOpen_le' hV
  exact ⟨f, hf, hle⟩

set_option backward.isDefEq.respectTransparency false in

theorem spMap_eq_fromSpecStalk (q : PrimeSpectrum R) :
    Spec.map (Spec.stalkIso (CommRingCat.of R) (q : Sp R)).hom ≫ (Sp R).fromSpecStalk (q : Sp R) =
      spMap (algebraMap R (Localization.AtPrime q.asIdeal)) := by
  have e : (Sp R).fromSpecStalk (q : Sp R) = Spec.map (Spec.stalkIso (CommRingCat.of R) (q : Sp R)).inv ≫
      spMap (algebraMap R (Localization.AtPrime q.asIdeal)) := by
    refine (Spec.fromSpecStalk_eq (CommRingCat.of R) (q : Sp R)).trans ?_
    rw [spMap, ← Spec.map_comp]
    exact congrArg Spec.map (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of R) (x := q)).symm
  refine (congrArg (Spec.map (Spec.stalkIso (CommRingCat.of R) (q : Sp R)).hom ≫ ·) e).trans ?_
  rw [← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in

theorem exists_isAffineOpen_preimage_basicOpen_of_stalk {x : Sp R} {p' : X' ⟶ Spec ((Sp R).presheaf.stalk x)}
    (H' : IsPullback φ p' p ((Sp R).fromSpecStalk x)) [QuasiCompact p] [QuasiSeparated p] [IsAffine X'] :
    ∃ f : R, x ∈ (PrimeSpectrum.basicOpen f : (Sp R).Opens) ∧ IsAffineOpen (p ⁻¹ᵁ PrimeSpectrum.basicOpen f) := by
  obtain ⟨hc⟩ := StalkLimit.nonempty_isLimit H'
  have (V : StalkLimit.AffNhd x) : CompactSpace ((StalkLimit.diagram _ p).obj V) := by
    have : IsAffine V.1.toScheme := V.2.2
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd p V.1.ι)
  have (V : StalkLimit.AffNhd x) : QuasiSeparatedSpace ((StalkLimit.diagram _ p).obj V) := by
    have : IsAffine V.1.toScheme := V.2.2
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd p V.1.ι)
  have : IsAffine (StalkLimit.cone H').pt := ‹IsAffine X'›
  obtain ⟨V, hV⟩ := Scheme.exists_isAffine_of_isLimit _ _ hc
  have : IsAffine (pullback p V.1.ι) := hV
  have h₁ : IsAffineOpen (p ⁻¹ᵁ V.1) := IsAffine.of_isIso (pullbackRestrictIsoRestrict p V.1).inv
  obtain ⟨f, hf, hle⟩ := exists_basicOpen_le' V.2.1
  refine ⟨f, hf, ?_⟩
  have h₂ := GlobalTheory.AmpleSpread.isAffineOpen_inf_preimage_basicOpen p h₁ f
  rwa [inf_eq_right.2 (p.preimage_mono hle)] at h₂

theorem exists_isAffineOpen_preimage_basicOpen
    (H : IsPullback φ π p (spMap (algebraMap R (Localization.AtPrime q.asIdeal)))) [QuasiCompact p]
    [QuasiSeparated p] [IsAffine X'] : ∃ f : R, f ∉ q.asIdeal ∧ IsAffineOpen (p ⁻¹ᵁ PrimeSpectrum.basicOpen f) := by
  have h₀ : IsPullback (spMap (algebraMap R (Localization.AtPrime q.asIdeal)))
      (Spec.map (Spec.stalkIso (CommRingCat.of R) (q : Sp R)).hom) (𝟙 _) ((Sp R).fromSpecStalk (q : Sp R)) :=
    IsPullback.of_vert_isIso ⟨(Category.comp_id _).trans (spMap_eq_fromSpecStalk q).symm⟩
  have H' := H.paste_vert h₀
  rw [Category.comp_id] at H'
  obtain ⟨f, hf, h⟩ := exists_isAffineOpen_preimage_basicOpen_of_stalk H'
  exact ⟨f, hf, h⟩

theorem exists_preimage_basicOpen_le
    (H : IsPullback φ π p (spMap (algebraMap R (Localization.AtPrime q.asIdeal)))) [UniversallyClosed p]
    {U : X.Opens} (hU : φ ⁻¹ᵁ U = ⊤) : ∃ f : R, f ∉ q.asIdeal ∧ p ⁻¹ᵁ PrimeSpectrum.basicOpen f ≤ U := by
  have hc : IsClosed (p '' (U : Set X)ᶜ) := p.isClosedMap _ U.isOpen.isClosed_compl
  obtain ⟨f, hf, hle⟩ := exists_basicOpen_le (q := q) (V := ⟨_, hc.isOpen_compl⟩) (by
    rintro ⟨x, hx, e⟩
    have hy : spMap (algebraMap R (Localization.AtPrime q.asIdeal))
        (IsLocalRing.closedPoint (Localization.AtPrime q.asIdeal)) = q :=
      PrimeSpectrum.ext (Localization.AtPrime.under_maximalIdeal (I := q.asIdeal))
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback H x _ (e.trans hy.symm)
    exact hx (hU.ge (Set.mem_univ z)))
  exact ⟨f, hf, fun x hx => by_contra fun h => hle hx ⟨x, h, rfl⟩⟩

theorem exists_cover (H : IsPullback φ π p (spMap (algebraMap R (Localization.AtPrime q.asIdeal)))) [IsProper p]
    {L : LB X} (hL : L.IsLB) (h : IsAmpleLB (L.pull φ)) :
    ∃ f : R, f ∉ q.asIdeal ∧ ∃ n, 1 ≤ n ∧ ∃ (N : ℕ) (θ : Fin (N + 1) → (lbPow L n).Sec),
      p ⁻¹ᵁ PrimeSpectrum.basicOpen f ≤ ⨆ i, Out.nonzeroLocus (θ i) ∧
      ∀ i, IsAffineOpen (Out.nonzeroLocus (θ i) ⊓ p ⁻¹ᵁ PrimeSpectrum.basicOpen f) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  obtain ⟨n, hn, N, s, hs, ha⟩ := h.exists_cover
  have hP := isLB_lbPow hL n
  choose t ht using fun i => exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_pull hP φ) (isLB_lbPow h.isLB n)
    (lbIso_lbPow_pull hL φ n).symm (s i)
  choose θ hθ using fun i => exists_sec_preimage_nonzeroLocus_eq H hP (t i)
  obtain ⟨f₀, hf₀, h₀⟩ := exists_preimage_basicOpen_le H (U := ⨆ i, Out.nonzeroLocus (θ i)) (by
    rw [Scheme.Hom.preimage_iSup, ← hs]
    exact iSup_congr fun i => (hθ i).trans (ht i))
  have aff : ∀ i, ∃ g : R, g ∉ q.asIdeal ∧
      IsAffineOpen (Out.nonzeroLocus (θ i) ⊓ p ⁻¹ᵁ PrimeSpectrum.basicOpen g) := fun i => by
    have := isAffineHom_nonzeroLocus_ι hP (θ i)
    have : IsAffine (φ ⁻¹ᵁ Out.nonzeroLocus (θ i)) := by
      rw [hθ, ht]; exact ha i
    obtain ⟨g, hg, h₁⟩ := exists_isAffineOpen_preimage_basicOpen
      ((isPullback_morphismRestrict φ (Out.nonzeroLocus (θ i))).paste_vert H)
    refine ⟨g, hg, ?_⟩
    have h₂ : IsAffineOpen ((Out.nonzeroLocus (θ i)).ι ''ᵁ (Out.nonzeroLocus (θ i)).ι ⁻¹ᵁ
        p ⁻¹ᵁ PrimeSpectrum.basicOpen g) := h₁.image_of_isOpenImmersion (Out.nonzeroLocus (θ i)).ι
    rwa [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι] at h₂
  choose g hg hga using aff
  have hm : f₀ * ∏ i, g i ∈ q.asIdeal.primeCompl :=
    q.asIdeal.primeCompl.mul_mem hf₀ (Submonoid.prod_mem _ fun i _ => hg i)
  refine ⟨f₀ * ∏ i, g i, hm, n, hn, N, θ,
    (p.preimage_mono (PrimeSpectrum.basicOpen_mul_le_left _ _)).trans h₀, fun i => ?_⟩
  have h₁ := GlobalTheory.AmpleSpread.isAffineOpen_inf_preimage_basicOpen p (hga i) (f₀ * ∏ i, g i)
  have hle : PrimeSpectrum.basicOpen (f₀ * ∏ i, g i) ≤ PrimeSpectrum.basicOpen (g i) := by
    rw [← Finset.mul_prod_erase _ g (Finset.mem_univ i), mul_left_comm]
    exact PrimeSpectrum.basicOpen_mul_le_left _ _
  rwa [inf_assoc, inf_eq_right.2 (p.preimage_mono hle)] at h₁

end GlobalTheory.AmpleSpreadAt

namespace GlobalTheory.AmpleSpreadAt

theorem relAmple_spread_at : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (q : PrimeSpectrum R) (A : Over (Sp R)) (M : LB A.left), IsProper A.hom → M.IsLB → ∀ (B : Over (Sp (Localization.AtPrime q.asIdeal))) (φ : B.left ⟶ A.left) (N : LB B.left), IsPullback φ B.hom A.hom (spMap (algebraMap R (Localization.AtPrime q.asIdeal))) → N.IsLB → LBIso N (M.pull φ) → Out.RelAmple B N → ∃ (U : (Sp R).Opens) (_ : q ∈ U), Out.RelAmple (Over.mk (A.hom ∣_ U)) (M.pull (A.hom ⁻¹ᵁ U).ι) := by
  intro R _ _ q A M _ hM B φ N H hN hNM h
  have h₁ : IsAmpleLB (M.pull φ) :=
    (isAmpleLB_of_relAmple_of_isAffine B hN h).of_lbIso (LB.isLB_pull hM φ) hNM.symm
  obtain ⟨f, hf, n, hn, N', θ, hc, ha⟩ := exists_cover H hM h₁
  let U : (Sp R).Opens := PrimeSpectrum.basicOpen f
  refine ⟨U, hf, ?_⟩
  have hb : (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom f) = U :=
    basicOpen_eq_of_affine (R := CommRingCat.of R) f
  have hU : IsAffineOpen U :=
    by have := (isAffineOpen_top (Sp R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom f); rwa [hb] at this
  have : IsAffine U.toScheme := hU
  have : IsProper (Over.mk (A.hom ∣_ U)).hom :=
    inferInstanceAs (IsProper (A.hom ∣_ _))
  let ψ := (A.hom ⁻¹ᵁ U).ι
  have : IsAffineHom ψ := MorphismProperty.of_isPullback (P := @IsAffineHom)
    (isPullback_morphismRestrict A.hom U) inferInstance
  refine (relAmple_iff_isAmpleLB_of_isAffine _ (LB.isLB_pull hM _)).2
    (isAmpleLB_of_cover (LB.isLB_pull hM _) hn (fun i => secPowPull (θ i) ψ) (top_le_iff.1 fun z _ => ?_) fun i => ?_)
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hc z.2)
    exact Opens.mem_iSup.2 ⟨i, (nonzeroLocus_secPowPull (θ i) ψ).ge hi⟩
  · have e : ψ ⁻¹ᵁ (Out.nonzeroLocus (θ i) ⊓ A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen f) =
        Out.nonzeroLocus (secPowPull (θ i) ψ) :=
      (le_antisymm (fun z hz => hz.1) fun z hz => ⟨hz, z.2⟩).trans (nonzeroLocus_secPowPull (θ i) ψ).symm
    exact e ▸ (ha i).preimage ψ

end GlobalTheory.AmpleSpreadAt
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relative_ample_spread_from_localization : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (q : PrimeSpectrum R) (A : Over (Sp R)) (M : LB A.left), IsProper A.hom → M.IsLB → ∀ (B : Over (Sp (Localization.AtPrime q.asIdeal))) (φ : B.left ⟶ A.left) (N : LB B.left), IsPullback φ B.hom A.hom (spMap (algebraMap R (Localization.AtPrime q.asIdeal))) → N.IsLB → LBIso N (M.pull φ) → Out.RelAmple B N → ∃ (U : (Sp R).Opens) (_ : q ∈ U), Out.RelAmple (Over.mk (A.hom ∣_ U)) (M.pull (A.hom ⁻¹ᵁ U).ι) := by
  first | exact @GlobalTheory.AmpleSpreadAt.relAmple_spread_at | exact GlobalTheory.AmpleSpreadAt.relAmple_spread_at | (intros; apply GlobalTheory.AmpleSpreadAt.relAmple_spread_at <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PolNormal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem polAt_generic_pull {S T : Type} [CommRing S] [IsDomain S] [CommRing T] [IsDomain T] (i : S →+* T)
    (hi : Function.Injective i) {t : SAB H (Sp S)} {t' : SAB H (Sp T)} (m : SABMap t' t (spMap i))
    (hg : GlobalTheory.LN.PolAt t (Out.jK S)) : GlobalTheory.LN.PolAt t' (Out.jK T) := by
  let ι : FractionRing S →+* FractionRing T :=
    IsLocalization.map (FractionRing T) i (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective i hi)
  refine GlobalTheory.DatUniq.polAt_pull m hg (Out.jK T) (spMap ι) ?_
  simp only [spMap, Out.jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact IsLocalization.map_comp _

end GlobalTheory.PolNormal

namespace GlobalTheory.PolNormal

end GlobalTheory.PolNormal

namespace GlobalTheory.PolNormal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem relAmple_kTriv_of_normal {S : Type} [CommRing S] [IsDomain S] [CharZero S] [IsNoetherianRing S]
    (hS : IsIntegrallyClosed S) (t : SAB H (Sp S)) (hp : IsProper t.G.hom) (hg : GlobalTheory.LN.PolAt t (Out.jK S)) :
    Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  have key : ∀ q : PrimeSpectrum S, ∃ (tO : SAB H (Sp (Localization.AtPrime q.asIdeal)))
      (_ : SABMap tO t (spMap (algebraMap S (Localization.AtPrime q.asIdeal)))),
      Out.RelAmple tO.G tO.PP.L ∧ Out.KTriv tO.G tO.PP.L := by
    intro q
    let O := Localization.AtPrime q.asIdeal
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap (algebraMap S O)) t
    refine ⟨_, m, ?_⟩
    have hi : Function.Injective (algebraMap S O) :=
      IsLocalization.injective O q.asIdeal.primeCompl_le_nonZeroDivisors
    have : CharZero O := charZero_of_injective_algebraMap hi
    have hO : IsIntegrallyClosed O :=
      isIntegrallyClosed_of_isLocalization O q.asIdeal.primeCompl q.asIdeal.primeCompl_le_nonZeroDivisors
    exact GlobalTheory.T.relative_ample_canonical_trivial_local E H O hO _ (MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hp)
      (polAt_generic_pull _ hi m hg)
  have hA : Out.RelAmple t.G t.PP.L := by
    have := t.semi.quasiCompact
    have := t.semi.separated
    refine GlobalTheory.AmpleLocal.relAmple_of_locally (Sp S) t.G t.PP.L t.PP.isLB inferInstance inferInstance fun s => ?_
    obtain ⟨tO, m, hA, -⟩ := key s
    obtain ⟨w, hw, -⟩ := m.lin
    exact GlobalTheory.T.relative_ample_spread_from_localization S s t.G t.PP.L hp t.PP.isLB tO.G m.φ tO.PP.L m.cart.1 tO.PP.isLB ⟨w, hw⟩ hA
  refine ⟨hA, GlobalTheory.KTrivGlob.kTriv_of_forall_point GlobalTheory.allSixLaws.1 E H (Sp S) t hp hA fun q => ?_⟩
  obtain ⟨tO, m, -, hK⟩ := key q
  have : q.asIdeal.IsPrime := q.isPrime
  exact ⟨_, _, tO, m, ⟨IsLocalRing.closedPoint _, PrimeSpectrum.ext Localization.AtPrime.under_maximalIdeal⟩, hK⟩

end GlobalTheory.PolNormal

namespace GlobalTheory.PolNormal

end GlobalTheory.PolNormal
end
