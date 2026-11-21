import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSymmetricIffExistsGen
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolAVPullbackOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaGroupKTrivialOfPrincipalGenericFibreDvr
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RelAmpleOfGenericIsogenousDedekindStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarizedCMExtensionDvrStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverBaseChangeAndFiniteRestrict
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KernelTrivialOfEveryPointCovered
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingFieldExtensionIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionPointsFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUnitOfPowEqOne
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionExtendsAbLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoNearNormalPointOfFiniteBirational
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullObjectOfGenericFibreDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelObjectPullbackExistsAndFull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteOfAmpleDeterminantFramesPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AmpleDeterminantFramesPullbackOfIsAffineHomStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperOfCompleteDVRLiftGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfCommonGenericFibre

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGroupK_trivial_of_principal_genericFibre_dvr : Laws → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → RelAmple B M.L.L → KTriv B M.L.L := by
  first | exact @GlobalTheory.KTrivSpread.kTriv_of_generic_fibre | exact GlobalTheory.KTrivSpread.kTriv_of_generic_fibre | (intros; apply GlobalTheory.KTrivSpread.kTriv_of_generic_fibre <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.PolDvr

theorem exists_polAV {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R]
    [IsLocalRing R] (t : SAB H (Sp R)) (hp : IsProper t.G.hom) (hA : Out.RelAmple t.G t.PP.L)
    (hK : Out.KTriv t.G t.PP.L) :
    ∃ (P : Out.PolAV (Sp R)) (e : P.A ≅ t.G), (∀ {S : Scheme.{0}} (B : Over S) [GrpObj B] (f : Sp R ⟶ S)
      (φ : t.G.left ⟶ B.left) (M : LB B.left), IsGrpPullback t.G B f φ → LBIso t.PP.L (M.pull φ) →
        IsGrpPullback P.A B f (e.hom.left ≫ φ) ∧ LBIso P.L (M.pull (e.hom.left ≫ φ))) := by
  have hab : IsAbelianScheme t.G := ⟨t.comm, t.semi.smooth, hp, t.semi.geomConnected⟩
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim R t.G hab
  let P : Out.PolAV (Sp R) :=
    { A := t.G
      isAb := hab
      g := g
      smoothDim := hg
      L := t.PP.L
      isLB := t.PP.isLB
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩
      sym := GlobalTheory.CechPic.sym_of_isSymmetric t.PP t.sym
      ample := hA
      ktriv := hK }
  refine ⟨P, Iso.refl _, ?_⟩
  intro S B _ f φ M h₁ h₂
  simp only [Iso.refl_hom, Over.id_left, Category.id_comp]
  exact ⟨h₁, h₂⟩

theorem relAmple_kTriv_of_generic_fibre : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (t : SAB H (Sp V)) (tK : SAB H (Sp K)) (_ : SABMap tK t (spMap (algebraMap V K))), IsProper t.G.hom → Out.RelAmple tK.G tK.PP.L → Out.KTriv tK.G tK.PP.L → Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  intro hH hL hL2 E _ _ _ H V K _ _ _ _ _ _ t tK m hp hA hK
  have hab : IsAbelianScheme t.G := ⟨t.comm, t.semi.smooth, hp, t.semi.geomConnected⟩
  have hiso : LBIso tK.PP.L (t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨t', -, e, -, -, hA', hK'⟩ := GlobalTheory.T.exists_principallyPolarizedCM_extension_dvr hH hL hL2 E H V K t.G tK m.cm.F hab m.cart hA hK
  have hp' : IsProper t'.G.hom := by
    have := hp
    have : IsIso e.hom.left := ((Over.forget _).mapIso e).isIso_hom
    rw [← Over.w e.hom]
    infer_instance
  obtain ⟨P, e', -⟩ := exists_polAV t' hp' hA' hK'
  have : IsIso (e'.hom ≫ e.hom).left := ((Over.forget _).mapIso (e' ≪≫ e)).isIso_hom
  have hAmp : Out.RelAmple t.G t.PP.L :=
    GlobalTheory.T.relAmple_of_generic_isogenous_dedekind hL hL2 V K P t.G (e'.hom ≫ e.hom) t.PP.L tK.G m.cm.F tK.PP.L hab t.PP.isLB tK.PP.isLB
      inferInstance inferInstance inferInstance m.cart hiso hA
  refine ⟨hAmp, ?_⟩
  have hpK : IsProper tK.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hp
  obtain ⟨P₀, e₀, hu⟩ := exists_polAV tK hpK hA hK
  obtain ⟨hpb, hlb⟩ := hu t.G (spMap (algebraMap V K)) m.cm.F t.PP.L m.cart hiso
  have hsym : ∃ s : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![(ι[t.G]).left, 𝟙 t.G.left] ![1, -1]), s.IsGen := by
    obtain ⟨s, hs, -⟩ := GlobalTheory.SymmetricBundle.gen_of_isSymmetric t.PP t.sym
    exact ⟨s, hs⟩
  obtain ⟨M, hM⟩ := (GlobalTheory.T.abelianScheme_cubical_bundle_exists_and_maps hL.globalFns (Sp V) t.G hab).1 t.PP ⟨t.cub.t, t.cub.isGen⟩ hsym
  have key := GlobalTheory.T.thetaGroupK_trivial_of_principal_genericFibre_dvr hL V K P₀ t.G M (e₀.hom.left ≫ m.cm.F) hab hpb (by rw [hM]; exact hlb)
    (by rw [hM]; exact hAmp)
  rw [hM] at key
  exact key

end GlobalTheory.PolDvr
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_principal_of_genericFibre_dvr : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (t : SAB H (Sp V)) (tK : SAB H (Sp K)) (_ : SABMap tK t (spMap (algebraMap V K))), IsProper t.G.hom → Out.RelAmple tK.G tK.PP.L → Out.KTriv tK.G tK.PP.L → Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  first | exact @GlobalTheory.PolDvr.relAmple_kTriv_of_generic_fibre | exact GlobalTheory.PolDvr.relAmple_kTriv_of_generic_fibre | (intros; apply GlobalTheory.PolDvr.relAmple_kTriv_of_generic_fibre <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits in

theorem _root_.GlobalTheory.isProjOver_of_isProper_of_isImmersion {A : Type} [CommRing A]
    {B X : Scheme.{0}} (e : B ⟶ X)
    [IsImmersion e] {x : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A} (hx : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver x) [IsProper (e ≫ x)] :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (e ≫ x) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver at hx
  obtain ⟨N, i, hi, -, rfl⟩ := hx
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver
  haveI : IsProper (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str A N) := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str A N
  haveI : IsProper ((e ≫ i) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str A N) := by rw [Category.assoc]; infer_instance
  haveI : IsProper (e ≫ i) := IsProper.of_comp (e ≫ i) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str A N)
  exact ⟨N, e ≫ i, .of_isPreimmersion _ (e ≫ i).isClosedMap.isClosed_range, by simp⟩

open AlgebraicGeometry CategoryTheory Limits in
private theorem isPullback_fst_comp_map {X Y Z W : Scheme.{0}} (f : X ⟶ Y) (s : Y ⟶ Z)
    (t : W ⟶ Z) :
    IsPullback (pullback.fst (f ≫ s) t)
      (pullback.map (f ≫ s) t s t f (𝟙 _) (𝟙 _) (by simp) (by simp)) f (pullback.fst s t) := by
  have h₁ : pullback.map (f ≫ s) t s t f (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ pullback.fst s t =
      pullback.fst (f ≫ s) t ≫ f := pullback.lift_fst _ _ _
  have h₂ : pullback.map (f ≫ s) t s t f (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ pullback.snd s t =
      pullback.snd (f ≫ s) t := (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  refine IsPullback.of_bot ?_ h₁.symm (IsPullback.of_hasPullback s t)
  rw [h₂]
  exact IsPullback.of_hasPullback (f ≫ s) t

open AlgebraicGeometry CategoryTheory Limits in
private theorem isImmersion_pullback_lift_of_isPullback {X Y Z W P : Scheme.{0}} (f : X ⟶ Y)
    (s : Y ⟶ Z) (t : W ⟶ Z) (y : W ⟶ Y) (hy : y ≫ s = t) (φ : P ⟶ X) (b : P ⟶ W)
    (h : IsPullback φ b f y) :
    IsImmersion (pullback.lift (f := f ≫ s) (g := t) φ b
      (by rw [← hy, ← Category.assoc, h.w, Category.assoc])) := by
  set Γ : W ⟶ pullback s t := pullback.lift y (𝟙 W) (by rw [hy, Category.id_comp]) with hΓdef
  have hΓs : Γ ≫ pullback.snd s t = 𝟙 W := pullback.lift_snd _ _ _
  have hΓf : Γ ≫ pullback.fst s t = y := pullback.lift_fst _ _ _
  haveI : IsImmersion (Γ ≫ pullback.snd s t) := by rw [hΓs]; infer_instance
  haveI : IsImmersion Γ := IsImmersion.of_comp Γ (pullback.snd s t)
  set e : P ⟶ pullback (f ≫ s) t := pullback.lift (f := f ≫ s) (g := t) φ b
    (by rw [← hy, ← Category.assoc, h.w, Category.assoc]) with hedef
  have hef : e ≫ pullback.fst (f ≫ s) t = φ := pullback.lift_fst _ _ _
  have hes : e ≫ pullback.snd (f ≫ s) t = b := pullback.lift_snd _ _ _
  set g := pullback.map (f ≫ s) t s t f (𝟙 _) (𝟙 _) (by simp) (by simp) with hgdef
  have hg₁ : g ≫ pullback.fst s t = pullback.fst (f ≫ s) t ≫ f := pullback.lift_fst _ _ _
  have hg₂ : g ≫ pullback.snd s t = pullback.snd (f ≫ s) t :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hsq : e ≫ g = b ≫ Γ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hg₁, hΓf, ← Category.assoc, hef, h.w]
    · rw [Category.assoc, Category.assoc, hg₂, hΓs, hes, Category.comp_id]
  have hleft : IsPullback e b g Γ := by
    refine IsPullback.of_right ?_ hsq (isPullback_fst_comp_map f s t)
    rw [hef, hΓf]
    exact h
  exact MorphismProperty.of_isPullback (P := @IsImmersion) hleft.flip ‹IsImmersion Γ›

open AlgebraicGeometry CategoryTheory Limits in

theorem _root_.GlobalTheory.isProjOver_of_isPullback_of_isProper_of_isQProjOver :
    ∀ (R A : Type) [CommRing R] [CommRing A] (S : Scheme.{0}) (s : S ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (G : Over S)
      (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A ⟶ S) (B : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A)) (φ : B.left ⟶ G.left), IsProper G.hom →
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver (G.hom ≫ s) → IsPullback φ B.hom G.hom y → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver B.hom := by
  intro R A _ _ S s G y B φ hG hq hpb
  let j : R →+* A :=
    (Spec.preimage (y ≫ s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))).hom
  have hj : y ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
    simp only [j, CommRingCat.ofHom_hom]
    exact (Spec.map_preimage _).symm
  haveI := isImmersion_pullback_lift_of_isPullback G.hom s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j) y hj φ B.hom hpb
  haveI : IsProper B.hom := MorphismProperty.of_isPullback (P := @IsProper) hpb hG
  have hqQ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver (pullback.snd (G.hom ≫ s) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j)) :=
    (_root_.GlobalTheory.isQProjOver_baseChange_and_finite_restrict R A j _ _).1 hq
  have he : pullback.lift (f := G.hom ≫ s) (g := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j) φ B.hom
      (by rw [← hj, ← Category.assoc, hpb.w, Category.assoc]) ≫
        pullback.snd (G.hom ≫ s) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j) = B.hom := pullback.lift_snd _ _ _
  haveI : IsProper (pullback.lift (f := G.hom ≫ s) (g := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j) φ B.hom
      (by rw [← hj, ← Category.assoc, hpb.w, Category.assoc]) ≫
        pullback.snd (G.hom ≫ s) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j)) := by rw [he]; infer_instance
  rw [← he]
  exact _root_.GlobalTheory.isProjOver_of_isProper_of_isImmersion _ hqQ

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProjOver_baseChange_of_proper_quasiProjective : ∀ (R A : Type) [CommRing R] [CommRing A] (S : Scheme.{0}) (s : S ⟶ Sp R) (G : Over S) (y : Sp A ⟶ S) (B : Over (Sp A)) (φ : B.left ⟶ G.left), IsProper G.hom → IsQProjOver (G.hom ≫ s) → IsPullback φ B.hom G.hom y → IsProjOver B.hom := by
  first | exact @GlobalTheory.isProjOver_of_isPullback_of_isProper_of_isQProjOver | exact GlobalTheory.isProjOver_of_isPullback_of_isProper_of_isQProjOver | (intros; apply GlobalTheory.isProjOver_of_isPullback_of_isProper_of_isQProjOver <;> assumption)
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.AmpleGlobal

theorem exists_lift_fieldExtension {S S' : Scheme.{0}} (f : S' ⟶ S) {K₀ : Type} [Field K₀] (x : Sp K₀ ⟶ S)
    (a : Sp K₀) (q : S') (h : f q = x a) :
    ∃ (K : Type) (_ : Field K) (i : K₀ →+* K) (u : Sp K ⟶ S'), u ≫ f = spMap i ≫ x := by
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback q a h
  refine ⟨(pullback f x).residueField z, inferInstance,
    (Spec.preimage ((pullback f x).fromSpecResidueField z ≫ pullback.snd f x)).hom,
    (pullback f x).fromSpecResidueField z ≫ pullback.fst f x, ?_⟩
  change _ = Spec.map (CommRingCat.ofHom _) ≫ x
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, Category.assoc, Category.assoc, pullback.condition]

theorem relAmple_of_pointwise {S : Scheme.{0}} [IsLocallyNoetherian S] (G : Over S) [IsProper G.hom] [Flat G.hom]
    (M : LB G.left) (hM : M.IsLB)
    (hproj : ∀ (A : Type) [CommRing A] (y : Sp A ⟶ S) (B : Over (Sp A)) (φ : B.left ⟶ G.left),
      IsPullback φ B.hom G.hom y → IsProjOver B.hom)
    (hpt : ∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (G' : Over S') (φ : G'.left ⟶ G.left) (L' : LB G'.left),
      IsPullback φ G'.hom G.hom f ∧ L'.IsLB ∧ LBIso L' (M.pull φ) ∧ p ∈ Set.range f ∧ Out.RelAmple G' L') :
    Out.RelAmple G M := by
  refine GlobalTheory.AmpleLocal.relAmple_of_locally S G M hM inferInstance inferInstance (fun s => ?_)
  obtain ⟨V, hV, hsV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (by first | exact AlgebraicGeometry.isBasis_affine_open S | exact S.isBasis_affineOpens | exact AlgebraicGeometry.Scheme.isBasis_affineOpens S | exact isBasis_affineOpens S)) (show s ∈ (⊤ : S.Opens) from trivial)
  have hV' : IsAffineOpen V := hV
  have : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV'⟩
  let y : Spec (CommRingCat.of Γ(S, V)) ⟶ S := hV'.fromSpec
  let q := hV'.primeIdealOf ⟨s, hsV⟩
  have hq : hV'.fromSpec q = s := hV'.fromSpec_primeIdealOf ⟨s, hsV⟩
  let g : Γ(S, V) →+* q.asIdeal.ResidueField := algebraMap _ _
  let B : Over (Spec (CommRingCat.of Γ(S, V))) := Over.mk (pullback.snd G.hom y)
  have hB : IsPullback (pullback.fst G.hom y) B.hom G.hom y := IsPullback.of_hasPullback _ _
  have hLB : (M.pull (pullback.fst G.hom y)).IsLB := pull_isLB hM _
  have hflat : Flat B.hom := by
    first | (show Flat (pullback.snd G.hom y); infer_instance) | exact MorphismProperty.pullback_snd _ _ inferInstance
  have hprojB := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver _).2 (hproj _ y B _ hB)
  have hfib : Out.RelAmple ((Over.pullback (Spec.map (CommRingCat.ofHom g))).obj B)
      ((M.pull (pullback.fst G.hom y)).pull (pullback.fst B.hom (Spec.map (CommRingCat.ofHom g)))) := by
    obtain ⟨S', f, G', φ, L', hφ, hL', e, ⟨s', hs'⟩, hA'⟩ := hpt s
    let x : Sp q.asIdeal.ResidueField ⟶ S := Spec.map (CommRingCat.ofHom g) ≫ y
    let a : Sp q.asIdeal.ResidueField := IsLocalRing.closedPoint _
    have ha : x a = s := by
      have hpt' : (Spec.map (CommRingCat.ofHom g)) a = q := by
        apply PrimeSpectrum.ext
        change Ideal.comap g (IsLocalRing.maximalIdeal _) = q.asIdeal
        rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
      first
        | (show y ((Spec.map (CommRingCat.ofHom g)) a) = s
           rw [hpt']
           exact hq)
        | exact (Scheme.comp_base_apply _ _ _).trans (by rw [hpt']; exact hq)
    obtain ⟨K, _, i, u, hu⟩ := exists_lift_fieldExtension f x a s' (hs'.trans ha.symm)
    have h₂ : IsPullback (pullback.fst G.hom (spMap i ≫ x)) (pullback.snd G.hom (spMap i ≫ x)) G.hom
        (spMap i ≫ x) := IsPullback.of_hasPullback _ _
    have hA₂ := GlobalTheory.FibreAmple.relAmple_of_factor hM hφ h₂ u hu hL' e hA'
    exact GlobalTheory.FibreAmple.relAmple_of_fieldExtension hM i
      ((IsPullback.of_hasPullback B.hom (Spec.map (CommRingCat.ofHom g))).paste_horiz hB) h₂
      (pull_isLB hLB _) (GlobalTheory.FibreAmple.lbIso_pull_pull hM _ _) hA₂
  obtain ⟨r, hr, hA⟩ := GlobalTheory.AmpleNear.relAmple_near_fibre Γ(S, V) B (M.pull (pullback.fst G.hom y)) hflat hprojB hLB
    q.asIdeal.ResidueField g (GlobalTheory.FibreAmple.residueField_fraction q.asIdeal) hfib
  let U₀ : (Spec (CommRingCat.of Γ(S, V))).Opens := PrimeSpectrum.basicOpen r
  let j := U₀.ι
  have : IsOpenImmersion y := by dsimp only [y]; infer_instance
  have : IsOpenImmersion j := by dsimp only [j]; exact inferInstance
  have hqr : q ∈ PrimeSpectrum.basicOpen r :=
    (PrimeSpectrum.mem_basicOpen _ _).2 fun h => hr ((Ideal.algebraMap_residueField_eq_zero).2 h)
  refine ⟨(j ≫ y).opensRange, ⟨⟨q, hqr⟩, ?_⟩, ?_⟩
  · rw [← hq]
    rfl
  · have hu : (j ≫ y).isoOpensRange.inv ≫ (j ≫ y) = (j ≫ y).opensRange.ι := by
      rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
    exact GlobalTheory.FibreAmple.relAmple_of_factor hM ((IsPullback.of_hasPullback B.hom j).paste_horiz hB)
      (isPullback_morphismRestrict G.hom _).flip _ hu (pull_isLB hLB _) (GlobalTheory.FibreAmple.lbIso_pull_pull hM _ _) hA

theorem relAmple_of_polarised_at_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S), IsProper t.G.hom → (∀ (A : Type) [CommRing A] (y : Sp A ⟶ S) (B : Over (Sp A)) (φ : B.left ⟶ t.G.left), IsPullback φ B.hom t.G.hom y → IsProjOver B.hom) → (∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (_ : SABMap t' t f), p ∈ Set.range f ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L) → Out.RelAmple t.G t.PP.L := by
  intro E _ _ _ H S _ t hP hproj hpt
  have hflat : Flat t.G.hom := by
    first
      | exact inferInstance
      | (haveI := t.semi.smooth; infer_instance)
  refine relAmple_of_pointwise t.G t.PP.L t.PP.isLB hproj (fun p => ?_)
  obtain ⟨S', f, t', m, hp, hA, -⟩ := hpt p
  refine ⟨S', f, t'.G, m.cm.F, t'.PP.L, m.cart.1, t'.PP.isLB, ?_, hp, hA⟩
  first
    | (obtain ⟨w, hw, -⟩ := m.lin; exact ⟨w, hw⟩)
    | (obtain ⟨w, hw⟩ := m.lin; exact ⟨w, hw⟩)
    | (obtain ⟨w, hw, -⟩ := m.lin; exact ⟨w, hw.1⟩)
    | (obtain ⟨w, -, hw, -⟩ := m.lin; exact ⟨w, hw⟩)
    | (obtain ⟨w, hw, -⟩ := m.lin; exact (hw : False))

end GlobalTheory.AmpleGlobal
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_of_polarised_at_every_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S), IsProper t.G.hom → (∀ (A : Type) [CommRing A] (y : Sp A ⟶ S) (B : Over (Sp A)) (φ : B.left ⟶ t.G.left), IsPullback φ B.hom t.G.hom y → IsProjOver B.hom) → (∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (_ : SABMap t' t f), p ∈ Set.range f ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L) → Out.RelAmple t.G t.PP.L := by
  atlas_forward_decl GlobalTheory.AmpleGlobal.relAmple_of_polarised_at_points
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelTrivial_of_every_point_covered : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → (∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (_ : SABMap t' t f), p ∈ Set.range f ∧ Out.KTriv t'.G t'.PP.L) → Out.KTriv t.G t.PP.L := by
  first | exact @GlobalTheory.KTrivGlob.kTriv_of_forall_point | exact GlobalTheory.KTrivGlob.kTriv_of_forall_point | (intros; apply GlobalTheory.KTrivGlob.kTriv_of_forall_point <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.FullDescent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {n N : ℕ}

theorem exists_lift {S S' : Scheme.{0}} (f : S' ⟶ S) {k : Type} [Field k] (x : Sp k ⟶ S) (p : Sp k)
    (hp : x p ∈ Set.range f) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (i : k →+* Ω) (y : Sp Ω ⟶ S'), spMap i ≫ x = y ≫ f := by
  obtain ⟨q, hq⟩ := hp
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := x) (g := f) p q hq.symm
  let Ω : Type := AlgebraicClosure ((pullback x f).residueField z)
  let u : Sp Ω ⟶ pullback x f :=
    Spec.map (CommRingCat.ofHom (algebraMap ((pullback x f).residueField z) Ω)) ≫ (pullback x f).fromSpecResidueField z
  refine ⟨Ω, inferInstance, inferInstance, (Spec.preimage (u ≫ pullback.fst x f)).hom, u ≫ pullback.snd x f, ?_⟩
  have e : spMap (Spec.preimage (u ≫ pullback.fst x f)).hom = u ≫ pullback.fst x f := Spec.map_preimage _
  rw [e]
  exact (Category.assoc _ _ _).trans ((congrArg (u ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)

theorem tate_push {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (ν : SABMap t' t f)
    {k : Type} [Field k] {y : Sp k ⟶ S'} {x : Sp k ⟶ S} (hx : x = y ≫ f)
    (I : TateIso D k (Over.mk y ⟶ t'.G) (fun a g => g ≫ t'.act.act a)
        (fun m g g' c => Out.WeilIs t'.G t'.PP.L m g g' (unitOn c))) :
    ∃ J : TateIso D k (Over.mk x ⟶ t.G) (fun a g => g ≫ t.act.act a)
        (fun m g g' c => Out.WeilIs t.G t.PP.L m g g' (unitOn c)),
      J.ζ = I.ζ ∧ ∀ m a, (J.ev m a).left = (I.ev m a).left ≫ ν.φ := by
  subst hx
  have hL : LBIso t'.PP.L (t.PP.L.pull ν.cm.F) := by
    obtain ⟨w, hw, -⟩ := ν.lin
    exact ⟨w, hw⟩
  refine ⟨ObjPull.tateMove (ObjPull.pushEquiv ν.cart (Over.mk y)).symm (fun c g => ?_) (fun m g g' c hc => ?_) I,
    rfl, fun _ _ => rfl⟩
  · obtain ⟨g, rfl⟩ := (ObjPull.pushEquiv ν.cart (Over.mk y)).surjective g
    rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_eq]
    apply Over.OverMorphism.ext
    show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
    rw [Category.assoc, ← ν.act, Category.assoc]
  · exact (weilIs_iff_of_isGrpPullback_comm S S' t.G t'.G f ν.cm.F t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB ν.cart hL
      (Over.mk y) m _ _ g g' _ (ObjPull.pushEquiv_symm_left ν.cart (Over.mk y) g).symm
      (ObjPull.pushEquiv_symm_left ν.cart (Over.mk y) g').symm).1 hc

theorem torsion_ext (hL : Out.Laws) {S : Scheme.{0}} (t : SAB H S) (hp : IsProper t.G.hom)
    (ha : Out.RelAmple t.G t.PP.L) (hk : Out.KTriv t.G t.PP.L) {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed K]
    [CharZero K] (i : K →+* Ω) (x : Sp K ⟶ S) :
    Function.Injective (TateIsoFieldExt.precomp
        (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) t.G) ∧
      ∀ m, 0 < m → ∀ z : Over.mk (spMap i ≫ x) ⟶ t.G, z ^ m = 1 → ∃ y : Over.mk x ⟶ t.G, y ^ m = 1 ∧
        TateIsoFieldExt.precomp (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) t.G y = z := by
  obtain ⟨P, φ, -, hφ, -⟩ := exists_polAV_pullback_of_isLocalRing E H S t hp ha hk K x
  obtain ⟨hinj, honto⟩ := torsion_points_field_extension hL (Sp K) P K Ω i (𝟙 _)
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hφ (𝟙 _) x (Category.id_comp _).symm
  obtain ⟨e', he'⟩ := exists_mulEquiv_of_isGrpPullback hφ (spMap i ≫ 𝟙 _) (spMap i ≫ x) (by simp)
  have key : ∀ y, TateIsoFieldExt.precomp (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) t.G (e y) =
      e' ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ 𝟙 (Sp K)) ⟶ Over.mk (𝟙 (Sp K))) ≫ y) := fun y => by
    apply Over.OverMorphism.ext
    rw [he']
    show spMap i ≫ (e y).left = (spMap i ≫ y.left) ≫ φ
    rw [he]
    exact (Category.assoc _ _ _).symm
  refine ⟨fun y y' h => ?_, fun m hm z hz => ?_⟩
  · obtain ⟨y, rfl⟩ := e.surjective y
    obtain ⟨y', rfl⟩ := e.surjective y'
    rw [key, key] at h
    exact congrArg e (hinj (e'.injective h))
  · obtain ⟨z, rfl⟩ := e'.surjective z
    rw [← map_pow, map_eq_one_iff _ e'.injective] at hz
    obtain ⟨y, hy, rfl⟩ := honto m z (Nat.cast_ne_zero.2 hm.ne') hz
    exact ⟨e y, by rw [← map_pow, hy, map_one], key y⟩

theorem fullObj_of_cover : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lv : D.La → (𝟙_ (Over S) ⟶ t.G)), 0 < N → IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ a c, lv (a + c) = lv a * lv c) → (∀ a, lv (N • a) = 1) → (∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (ν : SABMap t' t f) (lv' : D.La → (𝟙_ (Over S') ⟶ t'.G)), p ∈ Set.range f ∧ (∀ a, (lv' a).left ≫ ν.φ = f ≫ (lv a).left) ∧ FullObj D (f ≫ s) t' lv') → FullObj D s t lv := by
  intro hL E _ _ _ H D n N S s t lv hN hp ha hk hadd hker hcov
  refine ⟨hp, ha, hk, hadd, hker, fun k _ _ _ x β hx => ?_⟩
  obtain ⟨S', f, t', ν, lv', hq, hl, o⟩ := hcov (x (default : PrimeSpectrum k))
  obtain ⟨Ω, _, _, i, y, hy⟩ := exists_lift f x _ hq
  have : CharZero Ω := (i.charZero_iff i.injective).1 inferInstance
  have hy' : y ≫ f ≫ s = spMap (i.comp β) := by
    rw [← Category.assoc, ← hy, Category.assoc, hx]
    exact (Spec.map_comp _ _).symm
  obtain ⟨hdet, I', hI', hA'⟩ := o.geom Ω y (i.comp β) hy'
  refine ⟨?_, ?_⟩
  · refine (detCond_iff_of_field_extension E H D S t.G k Ω i x t.act _ t.semi.smooth).1 ?_
    rw [hy]
    exact (detCond_iff_of_sabMap E H D S S' t t' f ⟨ν⟩ Ω y _).1 hdet
  obtain ⟨J, hJ, hJ'⟩ := tate_push ν hy I'
  obtain ⟨hinj, honto⟩ := torsion_ext hL t hp ha hk i x
  let g : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  obtain ⟨I, hI⟩ := TateIsoFieldExt.down D i (TateIsoFieldExt.precomp g t.G)
    (act := fun a z => z ≫ t.act.act a) (act' := fun a z => z ≫ t.act.act a)
    (e' := fun m z z' c => Out.WeilIs t.G t.PP.L m z z' (unitOn c))
    (e := fun m z z' c => Out.WeilIs t.G t.PP.L m z z' (unitOn c)) hinj honto
    (fun c z => (Category.assoc g z (t.act.act c)).symm)
    (fun c => by
      haveI := t.act.hom c
      exact MonObj.one_comp (t.act.act c))
    (fun m z z' c => weilIs_fieldExt_iff S t.G k Ω i x t.PP.L m z z' c
      ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩ t.PP.isLB) J
  obtain ⟨h₁, h₂⟩ := hI N hN
  refine ⟨I, i.injective ?_, fun a => hinj ?_⟩
  · rw [← h₁, hJ, hI']
    rfl
  · rw [← h₂]
    apply Over.OverMorphism.ext
    rw [hJ', ← hA', Over.comp_left, ObjPull.toUnit_left', Category.assoc, hl]
    show spMap i ≫ (toUnit (Over.mk x) ≫ lv a).left = y ≫ f ≫ (lv a).left
    rw [Over.comp_left, ObjPull.toUnit_left', ← Category.assoc y, ← hy]
    exact (Category.assoc _ _ _).symm

end GlobalTheory.FullDescent
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullLevelObject_of_covering_pullbacks : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lv : D.La → (𝟙_ (Over S) ⟶ t.G)), 0 < N → IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ a c, lv (a + c) = lv a * lv c) → (∀ a, lv (N • a) = 1) → (∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (ν : SABMap t' t f) (lv' : D.La → (𝟙_ (Over S') ⟶ t'.G)), p ∈ Set.range f ∧ (∀ a, (lv' a).left ≫ ν.φ = f ≫ (lv a).left) ∧ FullObj D (f ≫ s) t' lv') → FullObj D s t lv := by
  atlas_forward_decl GlobalTheory.FullDescent.fullObj_of_cover
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem GlobalTheory.exists_torsion_level_extend : ∀ (Λ : Type) [AddCommGroup Λ] (N : ℕ) (S W : Scheme.{0}) [IsLocallyNoetherian S] (j : W ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over W) [GrpObj G'] (φ : G'.left ⟶ G.left) (lv' : Λ → (𝟙_ (Over W) ⟶ G')), Geo.Tor.IsNormalScheme S → IsOpenImmersion j → IsDominant j → IsProper G.hom → IsUnit (N : Γ(S, ⊤)) → IsGrpPullback G' G j φ → (∀ a c, lv' (a + c) = lv' a * lv' c) → (∀ a, lv' (N • a) = 1) → ∃ lv : Λ → (𝟙_ (Over S) ⟶ G), (∀ a c, lv (a + c) = lv a * lv c) ∧ (∀ a, lv (N • a) = 1) ∧ ∀ a, (lv' a).left ≫ φ = j ≫ (lv a).left := by
  intro Λ _ N S W _ j G _ _ G' _ φ lv' hS _ _ _ hN gp hadd hker
  have hred : IsReduced S := by
    have : ∀ x : S, _root_.IsReduced (S.presheaf.stalk x) := fun x => by
      obtain ⟨_, _⟩ := hS x
      infer_instance
    exact isReduced_of_isReduced_stalk _
  have hqc : QuasiCompact j := inferInstance
  let P : Over S := Over.mk ((𝟙_ (Over W)).hom ≫ j)
  let ρ : (𝟙_ (Over W) ⟶ G') →* (P ⟶ G) := pushHom gp _
  have hρ : ∀ x, (ρ x).left = x.left ≫ φ := fun _ => rfl
  have h0 : lv' 0 = 1 := by simpa using hker 0
  have hpow : ∀ (n : ℕ) a, lv' (n • a) = lv' a ^ n := fun n a => by
    induction n with
    | zero => simpa using h0
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hex : ∀ a, ∃ σ : S ⟶ G.left, σ ≫ G.hom = 𝟙 S ∧ j ≫ σ = (lv' a).left ≫ φ := fun a => by
    obtain ⟨s, h₁, h₂⟩ := GlobalTheory.exists_section_of_pow_eq_one hS j G N hN P (ρ (lv' a))
      (by rw [← map_pow, ← hpow, hker, map_one]) (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
    exact ⟨s, h₁, h₂.trans (Category.id_comp _)⟩
  choose σ hσ₁ hσ₂ using hex
  let lv : Λ → (𝟙_ (Over S) ⟶ G) := fun a => Over.homMk (σ a) (hσ₁ a)
  let u : P ⟶ 𝟙_ (Over S) := Over.homMk j ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hu : ∀ a, u ≫ lv a = ρ (lv' a) := fun a => Over.OverMorphism.ext (hσ₂ a)
  have inj : ∀ s t : 𝟙_ (Over S) ⟶ G, u ≫ s = u ≫ t → s = t := fun s t h =>
    Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := S) G.hom ((Over.w s).trans (Over.w t).symm) j
      (congrArg (fun z => z.left) h))
  refine ⟨lv, fun a c => inj _ _ ?_, fun a => inj _ _ ?_, fun a => (hσ₂ a).symm⟩
  · rw [MonObj.comp_mul, hu, hu, hu, hadd, map_mul]
  · rw [hu, hker, map_one, MonObj.comp_one]
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionLevel_extends_from_dense_open_normal : ∀ (Λ : Type) [AddCommGroup Λ] (N : ℕ) (S W : Scheme.{0}) [IsLocallyNoetherian S] (j : W ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over W) [GrpObj G'] (φ : G'.left ⟶ G.left) (lv' : Λ → (𝟙_ (Over W) ⟶ G')), IsNormalScheme S → IsOpenImmersion j → IsDominant j → IsProper G.hom → IsUnit (N : Γ(S, ⊤)) → IsGrpPullback G' G j φ → (∀ a c, lv' (a + c) = lv' a * lv' c) → (∀ a, lv' (N • a) = 1) → ∃ lv : Λ → (𝟙_ (Over S) ⟶ G), (∀ a c, lv (a + c) = lv a * lv c) ∧ (∀ a, lv (N • a) = 1) ∧ ∀ a, (lv' a).left ≫ φ = j ≫ (lv a).left := by
  atlas_forward_decl GlobalTheory.exists_torsion_level_extend
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_near_normal_point_of_finite_birational : ∀ (U M : Scheme.{0}) [IsLocallyNoetherian M] (u : U ⟶ M) (W : M.Opens), IsFinite u → IsReduced U → IsIso (u ∣_ W) → Dense (W : Set M) → Dense ((u ⁻¹ᵁ W : U.Opens) : Set U) → ∀ x : M, IsDomain (M.presheaf.stalk x) → IsIntegrallyClosed (M.presheaf.stalk x) → ∃ V : M.Opens, x ∈ V ∧ IsIso (u ∣_ V) := by
  first | exact @GlobalTheory.FiniteBirationalNear.main | exact GlobalTheory.FiniteBirationalNear.main | (intros; apply GlobalTheory.FiniteBirationalNear.main <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullObject_of_genericFibre_dvr : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (s : Sp V ⟶ Sp (RZ H n N)) (t : SAB H (Sp V)) (lv : D.La → (𝟙_ (Over (Sp V)) ⟶ t.G)) (tK : SAB H (Sp K)) (ν : SABMap tK t (spMap (algebraMap V K))) (lvK : D.La → (𝟙_ (Over (Sp K)) ⟶ tK.G)), 0 < N → IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ a c, lv (a + c) = lv a * lv c) → (∀ a, lv (N • a) = 1) → (∀ a, (lvK a).left ≫ ν.φ = spMap (algebraMap V K) ≫ (lv a).left) → FullObj D (spMap (algebraMap V K) ≫ s) tK lvK → FullObj D s t lv := by
  first | exact @GlobalTheory.FullSpread.fullObj_of_genericFibre | exact GlobalTheory.FullSpread.fullObj_of_genericFibre | (intros; apply GlobalTheory.FullSpread.fullObj_of_genericFibre <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullLevelObject_pullback_exists_and_full : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lev : D.La → (𝟙_ (Over S) ⟶ t.G)) (f : S' ⟶ S), (∃ (t' : SAB H S') (ν : SABMap t' t f) (lv : D.La → (𝟙_ (Over S') ⟶ t'.G)), ∀ a, (lv a).left ≫ ν.φ = f ≫ (lev a).left) ∧ ∀ (t' : SAB H S') (ν : SABMap t' t f) (lv : D.La → (𝟙_ (Over S') ⟶ t'.G)), (∀ a, (lv a).left ≫ ν.φ = f ≫ (lev a).left) → FullObj D s t lev → FullObj D (f ≫ s) t' lv := by
  first | exact @GlobalTheory.fullObj_pull | exact GlobalTheory.fullObj_pull | (intros; apply GlobalTheory.fullObj_pull <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_completeDVR_lift_generic : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y : Scheme.{0}) [IsLocallyNoetherian Y] (f : X ⟶ Y) (s : Y ⟶ Sp R), IsSeparated s → IsQProjOver (f ≫ s) → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [Algebra V K] [IsFractionRing V K] (x : Sp K ⟶ X) (y : Sp V ⟶ Y), Set.range x ⊆ genericPoints X → x ≫ f = spMap (algebraMap V K) ≫ y → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x) → IsProper f := by
  first | exact @GlobalTheory.ValuativeGeneric.isProper_of_lift_generic | exact GlobalTheory.ValuativeGeneric.isProper_of_lift_generic | (intros; apply GlobalTheory.ValuativeGeneric.isProper_of_lift_generic <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.AbelianLocusNormalisation

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

theorem exists_comp {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} (m' : SABMap t'' t' g) (m : SABMap t' t f) {h : S'' ⟶ S} (e : g ≫ f = h) :
    ∃ n : SABMap t'' t h, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact ObjMaps.exists_sab_comp m m'

theorem exists_cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {h : S'' ⟶ S} (m : SABMap t' t f) (n : SABMap t'' t h) {g : S'' ⟶ S'} (e : g ≫ f = h) :
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact ObjMaps.exists_sab_cancel m n

theorem isProper_pull {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    (h : IsProper t.G.hom) : IsProper t'.G.hom :=
  MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 h

theorem isAbelianScheme_of_isProper {S : Scheme.{0}} (t : SAB H S) (h : IsProper t.G.hom) : IsAbelianScheme t.G :=
  ⟨inferInstance, t.semi.smooth, h, t.semi.geomConnected⟩

theorem pol_of_map {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    (h : IsProper t.G.hom) : (Out.RelAmple t.G t.PP.L → Out.RelAmple t'.G t'.PP.L) ∧
      (Out.KTriv t.G t.PP.L → Out.KTriv t'.G t'.PP.L) := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact (pol_pull S S' t.G t'.G f m.φ t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB (isAbelianScheme_of_isProper t h) m.cart
    ⟨w, hw⟩).2

theorem isNormalScheme_of_open {X Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f] (h : Geo.Tor.IsNormalScheme X) :
    Geo.Tor.IsNormalScheme Y := fun x => by
  obtain ⟨_, _⟩ := h (f x)
  let e := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

theorem isReduced_of_normal {X : Scheme.{0}} (h : Geo.Tor.IsNormalScheme X) : IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    obtain ⟨_, _⟩ := h x
    infer_instance
  exact isReduced_of_isReduced_stalk X

theorem exists_full_through (hE : GlobalTheory.LN.HomExtSt) (h1 : Out.Laws) (h2 : Out.Laws2) {D : Datum H} {n N : ℕ}
    (hN : 0 < N) {S W : Scheme.{0}} [IsLocallyNoetherian S] (s : S ⟶ Sp (RZ H n N)) (t : SAB H S)
    (lv : D.La → (𝟙_ (Over S) ⟶ t.G)) (hp : IsProper t.G.hom) (add : ∀ a c, lv (a + c) = lv a * lv c)
    (ker : ∀ a, lv (N • a) = 1) (j : W ⟶ S) [IsOpenImmersion j] [IsDominant j] (tW : SAB H W) (ν : SABMap tW t j)
    (lW : D.La → (𝟙_ (Over W) ⟶ tW.G)) (hl : ∀ a, (lW a).left ≫ ν.φ = j ≫ (lv a).left)
    (o : FullObj D (j ≫ s) tW lW) (p : S) :
    ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (ν : SABMap t' t f) (lv' : D.La → (𝟙_ (Over S') ⟶ t'.G)),
      p ∈ Set.range f ∧ (∀ a, (lv' a).left ≫ ν.φ = f ≫ (lv a).left) ∧ FullObj D (f ≫ s) t' lv' := by
  obtain ⟨ξ, hξ, hs⟩ := exists_mem_genericPoints_specializes p
  have hξj := genericPoints_subset_range_of_isDominant j hξ
  by_cases hne : ξ = p
  · exact ⟨W, j, tW, ν, lW, hne ▸ hξj, hl, o⟩
  obtain ⟨V, _, _, -, f, hf₀, hf₁⟩ := exists_complete_discreteValuationRing_of_specializes hs hne
  let K := FractionRing V
  let g : Sp K ⟶ Sp V := spMap (algebraMap V K)
  have hr : Set.range (g ≫ f) ⊆ Set.range j := by
    rintro _ ⟨q, rfl⟩
    have : g q = (⊥ : PrimeSpectrum V) := by
      apply PrimeSpectrum.ext
      show Ideal.comap (algebraMap V K) q.asIdeal = ⊥
      rw [Subsingleton.elim (α := PrimeSpectrum K) q ⊥]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V K)
    rw [Scheme.Hom.comp_apply, this, hf₀]
    exact hξj
  let x : Sp K ⟶ W := IsOpenImmersion.lift j (g ≫ f) hr
  have hx : x ≫ j = g ≫ f := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨tV, ⟨νV⟩⟩ := exists_pull (S' := Sp V) f t
  obtain ⟨tK, ⟨νK⟩⟩ := exists_pull g tV
  obtain ⟨κ, hκ⟩ := exists_comp νK νV rfl
  obtain ⟨κ', hκ'⟩ := exists_cancel ν κ hx
  let lV := fun a => ObjPull.secPull νV.cart (lv a)
  let lK := fun a => ObjPull.secPull κ'.cart (lW a)
  have oK : FullObj D (x ≫ j ≫ s) tK lK :=
    (GlobalTheory.T.fullLevelObject_pullback_exists_and_full E H D n N W _ (j ≫ s) tW lW x).2 tK κ' lK (fun a => ObjPull.secPull_left _ _) o
  have hpV := isProper_pull νV hp
  obtain ⟨am, kt⟩ := GlobalTheory.T.relAmple_principal_of_genericFibre_dvr hE h1 h2 E H V K tV tK νK hpV oK.ample oK.ktriv
  refine ⟨Sp V, f, tV, νV, lV, ⟨_, hf₁⟩, fun a => ObjPull.secPull_left _ _, ?_⟩
  refine GlobalTheory.T.fullObject_of_genericFibre_dvr h1 h2 E H D n N V K (f ≫ s) tV lV tK νK lK hN hpV am kt (fun a c => ?_) (fun a => ?_)
    (fun a => ?_) ?_
  · simp only [lV, add, map_mul]
  · simp only [lV, ker, map_one]
  · apply νV.cart.1.hom_ext
    · have e₁ : (lK a).left ≫ κ'.φ = x ≫ (lW a).left := ObjPull.secPull_left _ _
      have e₂ : (lV a).left ≫ νV.φ = f ≫ (lv a).left := ObjPull.secPull_left _ _
      change ((lK a).left ≫ νK.φ) ≫ νV.φ = (g ≫ (lV a).left) ≫ νV.φ
      rw [Category.assoc, ← hκ, hκ', ← Category.assoc, e₁, Category.assoc, hl, ← Category.assoc, hx, Category.assoc,
        Category.assoc, e₂]
    · rw [Category.assoc, νK.cart.1.w, ← Category.assoc, Over.w (lK a), Category.assoc, Over.w (lV a)]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  · rwa [← Category.assoc, hx, Category.assoc] at oK

theorem exists_full (hE : GlobalTheory.LN.HomExtSt) (h1 : Out.Laws) (h2 : Out.Laws2) {D : Datum H} {n N : ℕ}
    (hN : 0 < N) (hu : IsUnit (N : RZ H n N)) {S W : Scheme.{0}} [IsLocallyNoetherian S]
    (hS : Geo.Tor.IsNormalScheme S) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (hp : IsProper t.G.hom)
    (hq : IsQProjOver (t.G.hom ≫ s)) (j : W ⟶ S) [IsOpenImmersion j] [IsDominant j] (tW : SAB H W)
    (ν : SABMap tW t j) (lW : D.La → (𝟙_ (Over W) ⟶ tW.G)) (o : FullObj D (j ≫ s) tW lW) :
    ∃ lv : D.La → (𝟙_ (Over S) ⟶ t.G), FullObj D s t lv ∧ ∀ a, (lW a).left ≫ ν.φ = j ≫ (lv a).left := by
  have hu' : IsUnit (N : Γ(S, ⊤)) := by
    simpa using hu.map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (RZ H n N))).inv.hom)
  obtain ⟨lv, add, ker, hl⟩ := GlobalTheory.T.torsionLevel_extends_from_dense_open_normal D.La N S W j t.G tW.G ν.φ lW hS ‹_› ‹_› hp hu' ν.cart o.add o.ker
  have th := exists_full_through hE h1 h2 hN s t lv hp add ker j tW ν lW hl o
  have am : Out.RelAmple t.G t.PP.L := GlobalTheory.T.relAmple_of_polarised_at_every_point E H S t hp
    (fun A _ y B φ h => GlobalTheory.T.isProjOver_baseChange_of_proper_quasiProjective _ A S s t.G y B φ hp hq h) fun p => by
      obtain ⟨S', f, t', ν', _, a, -, b⟩ := th p
      exact ⟨S', f, t', ν', a, b.ample, b.ktriv⟩
  have kt : Out.KTriv t.G t.PP.L := GlobalTheory.T.kernelTrivial_of_every_point_covered h1 E H S t hp am fun p => by
    obtain ⟨S', f, t', ν', _, a, -, b⟩ := th p
    exact ⟨S', f, t', ν', a, b.ktriv⟩
  exact ⟨lv, GlobalTheory.T.fullLevelObject_of_covering_pullbacks h1 E H D n N S s t lv hN hp am kt add ker th, hl⟩

theorem isProper_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (h : IsProjOver s) :
    IsProper s := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have := isProper_str R N
  infer_instance

theorem separated_finiteType_of_isQProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}
    (h : IsQProjOver s) : IsSeparated s ∧ LocallyOfFiniteType s := by
  obtain ⟨N, i, hi, -, rfl⟩ := h
  have := isProper_str R N
  exact ⟨inferInstance, inferInstance⟩

theorem isProper_of_abLocus (hE : GlobalTheory.LN.HomExtSt) {R : Type} [CommRing R] [IsNoetherianRing R] {Z M : Scheme.{0}}
    {sZ : Z ⟶ Sp R} {sM : M ⟶ Sp R} (hZ : IsProjOver sZ) (hM : IsQProjOver sM) {t : SAB H Z} {tM : SAB H M}
    (hp : IsProper tM.G.hom) {U : Z.Opens} (hU : abLocus t.G ⊆ U) {u : U.toScheme ⟶ M} (hu : u ≫ sM = U.ι ≫ sZ)
    {tU : SAB H U.toScheme} (mU : SABMap tU t U.ι) (mM : SABMap tU tM u) : IsProper u := by
  have := isProper_of_isProjOver hZ
  obtain ⟨_, _⟩ := separated_finiteType_of_isQProjOver hM
  have : IsLocallyNoetherian M := LocallyOfFiniteType.isLocallyNoetherian sM
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  refine GlobalTheory.T.isProper_of_completeDVR_lift_generic R _ M u sM ‹_› ?_ fun V K _ _ _ _ _ _ _ x y _ hxy => ?_
  · obtain ⟨N, i, hi, e⟩ := hZ
    exact ⟨N, U.ι ≫ i, inferInstance, inferInstance, by rw [hu, Category.assoc, e]⟩
  obtain ⟨z, hz, -⟩ := valuative_lift_of_isProper sZ (x ≫ U.ι) (y ≫ sM)
    (by rw [Category.assoc, ← hu, reassoc_of% hxy])
  obtain ⟨tz, ⟨mz⟩⟩ := exists_pull z t
  obtain ⟨ty, ⟨my⟩⟩ := exists_pull y tM
  obtain ⟨tx, ⟨mx⟩⟩ := exists_pull x tU
  obtain ⟨a, -⟩ := exists_comp mx mU rfl
  obtain ⟨b, -⟩ := exists_comp mx mM rfl
  obtain ⟨a', -⟩ := exists_cancel mz a hz
  obtain ⟨b', -⟩ := exists_cancel my b hxy.symm
  have hA : IsAbelianScheme tz.G := isAbelianScheme_of_common_generic_fibre ty.G tz.G
    (isAbelianScheme_of_isProper ty (isProper_pull my hp)) tz.semi (fun f hf => by
      obtain ⟨F, hF, -⟩ := hE V K ty.G tz.G ty.semi tz.semi f hf
      exact ⟨F, hF.2⟩) tx.G b'.cart a'.cart
  have := hA.proper
  have hr : Set.range z ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact (range_subset_abLocus_of_isProper t.semi mz.cart.1).trans hU
  exact ⟨IsOpenImmersion.lift U.ι z hr, by rw [← cancel_mono U.ι, Category.assoc, IsOpenImmersion.lift_fac, hz]⟩

theorem isAffineHom_of_isProper {R : Type} [CommRing R] {X Z V : Scheme.{0}} [IsAffine V] (g : X ⟶ Z) [IsImmersion g]
    (u : X ⟶ V) [IsProper u] (sZ : Z ⟶ Sp R) [IsSeparated sZ] (sV : V ⟶ Sp R) (h : u ≫ sV = g ≫ sZ) :
    IsAffineHom g := by
  let l : X ⟶ pullback sV sZ := pullback.lift u g h
  have e₁ : l ≫ pullback.fst sV sZ = u := pullback.lift_fst _ _ _
  have e₂ : l ≫ pullback.snd sV sZ = g := pullback.lift_snd _ _ _
  have : IsProper (l ≫ pullback.fst sV sZ) := by rwa [e₁]
  have : IsProper l := IsProper.of_comp l (pullback.fst sV sZ)
  have : IsImmersion (l ≫ pullback.snd sV sZ) := by rwa [e₂]
  have : IsImmersion l := IsImmersion.of_comp l (pullback.snd sV sZ)
  have : IsClosedImmersion l := IsClosedImmersion.of_isPreimmersion l l.isClosedMap.isClosed_range
  have : IsAffineHom sV := inferInstance
  have : IsAffineHom (pullback.snd sV sZ) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback sV sZ) ‹_›
  rw [← e₂]
  infer_instance

theorem isFinite_of_isProper (h1 : Out.Laws) (h2 : Out.Laws2) {R : Type} [CommRing R] {Z M : Scheme.{0}}
    [IsLocallyNoetherian Z] (sZ : Z ⟶ Sp R) [IsSeparated sZ] (sM : M ⟶ Sp R) (z : Z ⟶ Sp ℤ) [Flat z]
    (hn : Geo.Tor.IsNormalScheme Z) {t : SAB H Z} {tM : SAB H M} (hp : IsProper tM.G.hom)
    (am : Out.RelAmple tM.G tM.PP.L) (kt : Out.KTriv tM.G tM.PP.L) {N : ℕ} (hN : 0 < N)
    (A : GlobalTheory.LN.AmpFrames t.G t.PP.L N) {U : Z.Opens} {u : U.toScheme ⟶ M} [IsProper u] (hu : u ≫ sM = U.ι ≫ sZ)
    {tU : SAB H U.toScheme} (mU : SABMap tU t U.ι) (mM : SABMap tU tM u) : IsFinite u := by
  suffices h : ∀ V : M.affineOpens, IsFinite (u ∣_ V.1) by
    refine IsFinite.iff_isProper_and_isAffineHom.2 ⟨‹_›, ⟨fun V hV => ?_⟩⟩
    have := h ⟨V, hV⟩
    have : IsAffine V.toScheme := hV
    exact isAffine_of_isAffineHom (u ∣_ V)
  intro V
  have : IsAffine V.1.toScheme := V.2
  have ha := isAffineHom_of_isProper ((u ⁻¹ᵁ V.1).ι ≫ U.ι) (u ∣_ V.1) sZ (V.1.ι ≫ sM)
    (by rw [morphismRestrict_ι_assoc, hu, Category.assoc])
  obtain ⟨t', ⟨m'⟩⟩ := exists_pull (u ⁻¹ᵁ V.1).ι tU
  obtain ⟨tV, ⟨mV⟩⟩ := exists_pull V.1.ι tM
  obtain ⟨a, -⟩ := exists_comp m' mU rfl
  obtain ⟨b, -⟩ := exists_comp m' mM rfl
  obtain ⟨b', -⟩ := exists_cancel mV b (morphismRestrict_ι u V.1)
  obtain ⟨A', -⟩ := GlobalTheory.T.ampleDeterminantFrames_pullback_of_isAffineHom E H Z _ t t' _ a N A ha
  exact GlobalTheory.T.isFinite_of_ampleDeterminantFrames_pullback h1 h2 E H _ _ (((u ⁻¹ᵁ V.1).ι ≫ U.ι) ≫ z) t' tV (u ∣_ V.1) b' N A' hN
    (isNormalScheme_of_open ((u ⁻¹ᵁ V.1).ι ≫ U.ι) hn) inferInstance (isProper_pull b hp) ((pol_of_map b hp).1 am)
    ((pol_of_map b hp).2 kt) inferInstance

theorem isIso_restrict_of_section {U M : Scheme.{0}} [IsReduced U] (u : U ⟶ M) [IsSeparated u] (W : M.Opens)
    (j : W.toScheme ⟶ U) [IsDominant j] (h : j ≫ u = W.ι) :
    IsIso (u ∣_ W) ∧ Dense ((u ⁻¹ᵁ W : U.Opens) : Set U) := by
  have hr : Set.range j ⊆ Set.range (u ⁻¹ᵁ W).ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    show u (j w) ∈ W
    rw [← Scheme.Hom.comp_apply, h]
    exact w.2
  refine ⟨?_, j.denseRange.mono (hr.trans (Scheme.Opens.range_ι _).le)⟩
  let σ := IsOpenImmersion.lift (u ⁻¹ᵁ W).ι j hr
  have hσ : σ ≫ (u ⁻¹ᵁ W).ι = j := IsOpenImmersion.lift_fac _ _ _
  have h₁ : σ ≫ u ∣_ W = 𝟙 _ := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, reassoc_of% hσ, h, Category.id_comp]
  have : IsDominant σ := by
    constructor
    have hd := Dense.preimage j.denseRange (u ⁻¹ᵁ W).ι.isOpenEmbedding.isOpenMap
    refine hd.mono ?_
    rintro y ⟨x, hx⟩
    refine ⟨x, (u ⁻¹ᵁ W).ι.isOpenEmbedding.injective ?_⟩
    rw [← hx, ← hσ]; rfl
  refine ⟨σ, ?_, h₁⟩
  refine ext_of_isDominant_of_isSeparated (u ∣_ W) ?_ σ ?_
  · rw [Category.assoc, h₁, Category.comp_id, Category.id_comp]
  · rw [reassoc_of% h₁, Category.comp_id]

theorem normal_stalk_of_generic {O : Type} [CommRing O] [IsDomain O] {M : Scheme.{0}} (s : M ⟶ Sp O)
    (h : Smooth (pullback.snd s (spMap (algebraMap O (FractionRing O))))) (x : M) (hx : (s x).asIdeal = ⊥) :
    IsDomain (M.presheaf.stalk x) ∧ IsIntegrallyClosed (M.presheaf.stalk x) := by
  have hb : IsPreimmersion (spMap (algebraMap O (FractionRing O))) :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of O) (S := FractionRing O) (nonZeroDivisors O)
  have hbf : Flat (spMap (algebraMap O (FractionRing O))) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (nonZeroDivisors O))
  have h1 : IsPreimmersion (pullback.fst s (spMap (algebraMap O (FractionRing O)))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hb
  have hx' : x ∈ Set.range (pullback.fst s (spMap (algebraMap O (FractionRing O)))) := by
    rw [Scheme.Pullback.range_fst]
    refine ⟨(⊥ : PrimeSpectrum (FractionRing O)), PrimeSpectrum.ext ?_⟩
    rw [hx]
    exact Ideal.comap_bot_of_injective (algebraMap O (FractionRing O)) (IsFractionRing.injective O _)
  obtain ⟨y, rfl⟩ := hx'
  obtain ⟨_, _⟩ := (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ h).2.1 y
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks (pullback.fst s (spMap (algebraMap O (FractionRing O)))) y
  let e := (asIso ((pullback.fst s (spMap (algebraMap O (FractionRing O)))).stalkMap y)).commRingCatIsoToRingEquiv
  exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩

theorem exists_isIso_restrict {U M : Scheme.{0}} (u : U ⟶ M) (T : M → Prop)
    (h : ∀ x, T x → ∃ V : M.Opens, x ∈ V ∧ IsIso (u ∣_ V)) : ∃ W : M.Opens, (∀ x, T x → x ∈ W) ∧ IsIso (u ∣_ W) := by
  let W : M.Opens := ⨆ V : {V : M.Opens // IsIso (u ∣_ V)}, V.1
  refine ⟨W, fun x hx => ?_, ?_⟩
  · obtain ⟨V, a, b⟩ := h x hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, b⟩, a⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun V : {V : M.Opens // IsIso (u ∣_ V)} => W.ι ⁻¹ᵁ V.1) ?_ fun V => ?_
  · rw [← Scheme.Hom.preimage_iSup]
    exact W.ι_preimage_self
  · have e : W.ι ''ᵁ (W.ι ⁻¹ᵁ V.1) = V.1 := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.2 (le_iSup (fun V : {V : M.Opens // IsIso (u ∣_ V)} => V.1) V)
    refine ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict u W (W.ι ⁻¹ᵁ V.1))).2 ?_
    rw [e]
    exact V.2

theorem exists_finite_map : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)) (m : ℕ) (C : ZOn sM tM m) (U : C.Z.Opens), n.Prime → (∃ j, N = n ^ j) → 0 < m → FamCore D sM tM lev → (U : Set C.Z) = abLocus C.t.G → ∃ (u : U.toScheme ⟶ MM) (tU : SAB H U.toScheme) (mU : SABMap tU C.t U.ι) (mM : SABMap tU tM u), u ≫ sM = U.ι ≫ C.s ∧ IsFinite u ∧ Surjective u ∧ (∃ W : MM.Opens, (∀ x : MM, (sM x).asIdeal = ⊥ → x ∈ W) ∧ IsIso (u ∣_ W)) ∧ ∀ j' : C.W.toScheme ⟶ U.toScheme, j' ≫ U.ι = C.j → j' ≫ u = C.W.ι := by
  intro hE h1 h2 E _ _ _ H D n N MM sM tM lev m C U hn ⟨e, he⟩ hm F hU
  have := BaseRing.finiteType_RZ H n N
  have : IsNoetherianRing (RZ H n N) := Algebra.FiniteType.isNoetherianRing ℤ _
  have hn₀ : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne_zero
  have hun : IsUnit (n : RZ H n N) := IsUnit.of_mul_eq_one
    ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr (Or.inl rfl))⟩ (Subtype.ext (by simp [hn₀]))
  have huN : IsUnit (N : RZ H n N) := by simpa only [he, Nat.cast_pow] using hun.pow e
  have hN : 0 < N := he ▸ pow_pos hn.pos e
  have := isProper_of_isProjOver C.proj
  obtain ⟨_, _⟩ := separated_finiteType_of_isQProjOver F.qproj
  have : IsLocallyNoetherian MM := LocallyOfFiniteType.isLocallyNoetherian sM
  have : IsLocallyNoetherian C.Z := LocallyOfFiniteType.isLocallyNoetherian C.s
  have := C.flat
  have := F.flat
  have := F.red
  have := C.j_open
  have := C.j_dom
  have hnU := isNormalScheme_of_open U.ι C.normal
  have := isReduced_of_normal hnU
  obtain ⟨tU, ⟨mU⟩⟩ := exists_pull U.ι C.t
  have hpU : IsProper tU.G.hom := by
    obtain ⟨U', hU', hP⟩ := C.good.1
    obtain rfl : U' = U := TopologicalSpace.Opens.ext (hU'.trans hU.symm)
    have i := mU.cart.1.isoIsPullback_hom_snd _ _ (isPullback_morphismRestrict C.t.G.hom U').flip
    rw [← i]
    infer_instance
  have hqU : IsQProjOver (tU.G.hom ≫ U.ι ≫ C.s) := by
    obtain ⟨k, i, _, _, hi⟩ := C.qproj
    have : IsOpenImmersion mU.φ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) mU.cart.1.flip inferInstance
    have : QuasiCompact mU.φ := MorphismProperty.of_isPullback (P := @QuasiCompact) mU.cart.1.flip inferInstance
    exact ⟨k, mU.φ ≫ i, inferInstance, inferInstance, by rw [Category.assoc, hi, mU.cart.1.w_assoc]⟩
  have hpW := isProper_pull C.m₁ F.obj.proper
  have hr : Set.range C.j ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι, hU]
    exact range_subset_abLocus_of_isProper C.t.semi C.m₂.cart.1
  let j : C.W.toScheme ⟶ U.toScheme := IsOpenImmersion.lift U.ι C.j hr
  have hj : j ≫ U.ι = C.j := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (j ≫ U.ι) := by rwa [hj]
  have : IsOpenImmersion j := IsOpenImmersion.of_comp j U.ι
  have : IsDominant j := by
    constructor
    have hd := Dense.preimage C.j.denseRange U.ι.isOpenEmbedding.isOpenMap
    refine hd.mono ?_
    rintro y ⟨x, hx⟩
    refine ⟨x, U.ι.isOpenEmbedding.injective ?_⟩
    rw [← hx, ← hj]; rfl
  obtain ⟨ν, -⟩ := exists_cancel mU C.m₂ hj
  let lW := fun a => ObjPull.secPull C.m₁.cart (lev a)
  have hlW : ∀ a, (lW a).left ≫ C.m₁.φ = C.W.ι ≫ (lev a).left := fun a => ObjPull.secPull_left _ _
  have oW : FullObj D (C.W.ι ≫ sM) C.tW lW := (GlobalTheory.T.fullLevelObject_pullback_exists_and_full E H D n N MM _ sM tM lev C.W.ι).2 C.tW C.m₁ lW hlW F.obj
  have hjs : j ≫ U.ι ≫ C.s = C.W.ι ≫ sM := by rw [reassoc_of% hj, C.j_over]
  obtain ⟨lv, o, hl⟩ := exists_full hE h1 h2 hN huN hnU (U.ι ≫ C.s) tU hpU hqU j C.tW ν lW (by rwa [hjs])
  obtain ⟨u, ⟨hu, mM, hM⟩, -⟩ := F.rep _ (U.ι ≫ C.s) tU lv inferInstance inferInstance inferInstance o
  have hju : j ≫ u = C.W.ι := by
    obtain ⟨k, hk⟩ := exists_comp ν mM rfl
    refine (F.rep _ (C.W.ι ≫ sM) C.tW lW inferInstance inferInstance inferInstance oW).unique
      ⟨by rw [Category.assoc, hu, hjs], k, fun a => ?_⟩ ⟨rfl, C.m₁, hlW⟩
    rw [hk, ← Category.assoc, hl, Category.assoc, hM, Category.assoc]
  have := isProper_of_abLocus hE C.proj F.qproj F.obj.proper hU.ge hu mU mM
  have : Flat (spMap (algebraMap ℤ (RZ H n N))) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have hf : IsFinite u := isFinite_of_isProper h1 h2 C.s sM (C.s ≫ spMap (algebraMap ℤ (RZ H n N))) C.normal
    F.obj.proper F.obj.ample F.obj.ktriv (pow_pos hm 2) C.amp hu mU mM
  obtain ⟨hi, hd⟩ := isIso_restrict_of_section u C.W j hju
  refine ⟨u, tU, mU, mM, hu, hf, ⟨?_⟩, exists_isIso_restrict u _ fun x hx => ?_, fun j' hj' => ?_⟩
  · have hd' : Dense (Set.range u) := C.dense.mono fun w hw =>
      ⟨j ⟨w, hw⟩, congrArg (fun f => f (⟨w, hw⟩ : C.W.toScheme)) hju⟩
    rw [← Set.range_eq_univ, ← u.isClosedMap.isClosed_range.closure_eq]
    exact hd'.closure_eq
  · obtain ⟨a, b⟩ := normal_stalk_of_generic sM F.gen x hx
    exact GlobalTheory.T.isIso_near_normal_point_of_finite_birational _ MM u C.W hf inferInstance hi C.dense hd x a b
  · obtain rfl : j' = j := by rw [← cancel_mono U.ι, hj, hj']
    exact hju

end GlobalTheory.AbelianLocusNormalisation
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_locus_open_family_over_level : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)) (m : ℕ) (C : ZOn sM tM m) (U : C.Z.Opens), n.Prime → (∃ j, N = n ^ j) → 0 < m → FamCore D sM tM lev → (U : Set C.Z) = abLocus C.t.G → ∃ (u : U.toScheme ⟶ MM) (tU : SAB H U.toScheme) (mU : SABMap tU C.t U.ι) (mM : SABMap tU tM u), u ≫ sM = U.ι ≫ C.s ∧ IsFinite u ∧ Surjective u ∧ (∃ W : MM.Opens, (∀ x : MM, (sM x).asIdeal = ⊥ → x ∈ W) ∧ IsIso (u ∣_ W)) ∧ ∀ j' : C.W.toScheme ⟶ U.toScheme, j' ≫ U.ι = C.j → j' ≫ u = C.W.ι := by
  first | exact @GlobalTheory.AbelianLocusNormalisation.exists_finite_map | exact GlobalTheory.AbelianLocusNormalisation.exists_finite_map | (intros; apply GlobalTheory.AbelianLocusNormalisation.exists_finite_map <;> assumption)
end
