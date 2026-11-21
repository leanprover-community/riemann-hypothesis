import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalBasisAlong
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExtendedArcUAdicUniformisationOfArcData
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicBaseEmbedsValuationAlgebraicClosure
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniversalBasisMoveBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecUnitClosedFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoreOfIsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionPointsFieldExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsAtUniformisedTraitStatement

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam

noncomputable section
namespace GlobalTheory.Ex.OneGen

theorem existsUnique_smul_of_basis {R M κ : Type} [CommRing R] [AddCommGroup M] [Module R M] [Subsingleton κ]
    (c : Module.Basis κ R M) (k : κ) (s : M) : ∃! r : R, s = r • c k := by
  have := uniqueOfSubsingleton k
  obtain rfl : k = default := Subsingleton.elim _ _
  refine ⟨c.repr s default, ?_, fun r hr => ?_⟩
  · have e := c.sum_repr s
    rw [Fintype.sum_unique] at e
    exact e.symm
  · rw [hr]; simp

theorem exists_univBasis_field (hS : SecBaseChangeAnySt) {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K]
    (y : Sp K ⟶ S) : ∃ b : SecM P.A P.L ((1 : ℕ) : ℤ) (Over.mk y), ∀ (T : Over S) [IsAffine T.left] (h : T ⟶ Over.mk y)
      (s : SecM P.A P.L ((1 : ℕ) : ℤ) T), ∃! c : Γ(T.left, ⊤), s = c • VVRank.pullM P.A P.L _ h b := by
  obtain ⟨V, hV, b, hb⟩ := ThetaReal.exists_univBasis hS P 1 le_rfl (y (closedPoint K))
  have hr : Set.range y ⊆ Set.range V.ι := by
    rintro _ ⟨q, rfl⟩
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    rw [Subsingleton.elim q (closedPoint K)]
    exact ⟨⟨_, hV⟩, rfl⟩
  let u : Over.mk y ⟶ overRes (T := baseOver S) V := Over.homMk (IsOpenImmersion.lift V.ι y hr)
    ((congrArg (_ ≫ ·) (Category.comp_id V.ι)).trans (IsOpenImmersion.lift_fac V.ι y hr))
  have h1 : 1 ^ P.g = 1 := one_pow _
  let k₀ : Fin (1 ^ P.g) := Fin.cast h1.symm 0
  have : Subsingleton (Fin (1 ^ P.g)) := ⟨fun a a' => Fin.ext (by have := a.2; have := a'.2; omega)⟩
  refine ⟨VVRank.pullM P.A P.L _ u (b k₀), fun T _ h s => ?_⟩
  obtain ⟨c, hc⟩ := hb T (h ≫ u)
  rw [VVRank.pullM_comp _ P.isLB, ← hc]
  exact existsUnique_smul_of_basis c k₀ s

theorem exists_univBasis_of_fibre : Laws2 → ∀ (S S' : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB →
    ∀ (P : PolAV S') (f : S' ⟶ S) (φ : P.A.left ⟶ G.left), IsGrpPullback P.A G f φ → LBIso P.L (L.pull φ) →
    ∀ (K : Type) [Field K] (y : Sp K ⟶ S') (x : Sp K ⟶ S), y ≫ f = x → ∃ e, UnivBasis G L x e := by
  intro hL S S' G _ L hL₀ P f φ hp hw K _ y x hx
  obtain ⟨w, hw⟩ := hw
  obtain ⟨b, hb⟩ := exists_univBasis_field hL.secBaseChangeAny P y
  have hτ : (𝟙 (Sp K) : (Over.mk y).left ⟶ (Over.mk x).left) ≫ (Over.mk x).hom = (Over.mk y).hom ≫ f :=
    (Category.id_comp _).trans hx.symm
  have : IsIso (C := Scheme.{0}) (X := (Over.mk y).left) (Y := (Over.mk x).left) (𝟙 (Sp K)) := IsIso.id _
  obtain ⟨e, he⟩ := UnivBasisMove.exists_rel_up hp (T := Over.mk y) (T₀ := Over.mk x) (𝟙 (Sp K)) hτ hw hL₀ P.isLB b
  refine ⟨SecM.toSec G e, fun K' _ i x' h s => ?_⟩
  obtain rfl : (spMap i ≫ y) ≫ f = x' := by rw [Category.assoc, hx, h]
  let T : Over S' := Over.mk (spMap i ≫ y)
  have : IsAffine T.left := inferInstanceAs (IsAffine (Spec _))
  obtain ⟨E, hE⟩ := UnivBasisMove.exists_linearEquiv hp hw hL₀ P.isLB ((1 : ℕ) : ℤ) T
  let u : T ⟶ Over.mk y := Over.homMk (spMap i) rfl
  let u₀ : Over.mk (T.hom ≫ f) ⟶ Over.mk x := Over.homMk (spMap i) h
  have key : E (VVRank.pullM G L _ u₀ e) = VVRank.pullM P.A P.L _ u b :=
    (hE _).unique_down hL₀ P.isLB (he.pull _ _ u u₀ ((Category.id_comp _).trans (Category.comp_id _).symm))
  obtain ⟨c, hc, hu⟩ := hb T u (E s)
  refine ⟨c, E.injective (hc.trans ?_), fun r hr => hu r ?_⟩
  · rw [← key]
    exact (E.map_smul c _).symm
  · rw [← key]
    exact (congrArg E hr).trans (E.map_smul r _)

end GlobalTheory.Ex.OneGen
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universal_section_basis_polarised_fibre : Laws2 → ∀ (S S' : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → ∀ (P : PolAV S') (f : S' ⟶ S) (φ : P.A.left ⟶ G.left), IsGrpPullback P.A G f φ → LBIso P.L (L.pull φ) → ∀ (K : Type) [Field K] (y : Sp K ⟶ S') (x : Sp K ⟶ S), y ≫ f = x → ∃ e, UnivBasis G L x e := by
  first | exact @GlobalTheory.Ex.OneGen.exists_univBasis_of_fibre | exact GlobalTheory.Ex.OneGen.exists_univBasis_of_fibre | (intros; apply GlobalTheory.Ex.OneGen.exists_univBasis_of_fibre <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

namespace GlobalTheory.Ex.OneGen

open ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic in

theorem exists_sec_pull_locus {X Y : Scheme.{0}} {L : LB X} (s : LB.Sec L) (φ : Y ⟶ X) :
    ∃ s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)),
      nonzeroLocus s' = φ ⁻¹ᵁ nonzeroLocus s := by
  have l : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => φ) j ≤ φ ⁻¹ᵁ L.U (j 0) :=
    fun j => LB.wchart_le L _ j 0
  have v : ∀ (j : Fin 1 → L.ι) (z : Y), z ∈ LB.wchart L (fun _ : Fin 1 => φ) j →
      gs (𝟙 Y) z _ ((Y.presheaf.map (homOfLE (l j)).op).hom ((φ.app _).hom (s.f (j 0)))) =
        gs (𝟙 Y ≫ φ) z (L.U (j 0)) (s.f (j 0)) := fun j z hj =>
    (gs_res _ z _ hj _).trans (gs_pull _ φ z _ (l j hj) _)
  let s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)) :=
    { f := fun j => (Y.presheaf.map (homOfLE (l j)).op).hom ((φ.app _).hom (s.f (j 0)))
      compat := fun j j' => fn_ext fun z hz => by
        have hm : (𝟙 Y ≫ φ) z ∈ L.U (j 0) ⊓ L.U (j' 0) := ⟨l j hz.1, l j' hz.2⟩
        have g : (trF (L := L) (fun _ : Fin 1 => φ) (fun _ => 1) (𝟙 Y) z j j').val =
            gs (𝟙 Y ≫ φ) z (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)).val := by
          refine Eq.trans ?_ (gs_unit _ z _ hm _).symm
          exact congrArg Units.val ((Fin.prod_univ_one _).trans (zpow_one _))
        refine ((gs_res (𝟙 Y) z _ hz _).trans (v j z hz.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) z _ hz _ _).trans
          (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) z _ hz _).trans
            ((congrArg Units.val (gm_linComb L _ _ (𝟙 Y) z j j' hz.1 hz.2)).trans g))
              ((gs_res (𝟙 Y) z _ hz _).trans (v j' z hz.2)))).symm)
        exact (gs_res _ z _ hm _).symm.trans ((congrArg (gs _ z _) (s.compat (j 0) (j' 0))).trans
          ((gs_mul _ z _ hm _ _).trans (congrArg _ (gs_res _ z _ hm _)))) }
  have b : ∀ (j : Fin 1 → L.ι) (y : Y), y ∈ Y.basicOpen (s'.f j) ↔
      y ∈ LB.wchart L (fun _ : Fin 1 => φ) j ∧ φ y ∈ X.basicOpen (s.f (j 0)) := fun j y => by
    change y ∈ Y.basicOpen ((Y.presheaf.map (homOfLE (l j)).op).hom ((φ.app _).hom (s.f (j 0)))) ↔ _
    rw [Scheme.basicOpen_res]
    exact and_congr_right fun _ => (SetLike.ext_iff.1 (Scheme.preimage_basicOpen φ (s.f (j 0))) y).symm
  refine ⟨s', SetLike.ext fun y => ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j 0, ((b j y).1 hj).2⟩
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show φ y ∈ nonzeroLocus s from h)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, (b _ y).2
      ⟨Set.mem_iInter.2 fun _ => X.basicOpen_le _ hi, hi⟩⟩

theorem isUnit_sval_iff {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    IsUnit (sval s r z J) ↔ r z ∈ nonzeroLocus s := by
  have key : ∀ (U : Y.Opens) (_ : r z ∈ U) (f : Γ(Y, U)), IsUnit (gs r z U f) ↔ IsUnit (gs (𝟙 Y) (r z) U f) :=
    fun U h f => by rw [gs_stalkMap r z U h, isUnit_map_iff]
  refine ⟨fun h => (mem_nonzeroLocus s _).2 ⟨_, hJ.mem φ r, (key _ (hJ.mem φ r) _).1 h⟩, fun h => ?_⟩
  obtain ⟨j, hj, hu⟩ := (mem_nonzeroLocus s _).1 h
  rw [sval, sec_trans s r z (hJ.mem φ r) hj]
  exact (Units.isUnit _).mul ((key _ hj _).2 hu)

theorem nz_pullS {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) {T : Over S}
    (σ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)) (hσ : ∀ y : T.left, ∃ g, (fst T G).left g = y ∧ g ∈ nonzeroLocus σ)
    {V : Type} [CommRing V] [IsLocalRing V] (χ : Sp V ⟶ S) (h : Over.mk χ ⟶ T) :
    NZ G L χ (VVRank.pullS G _ h σ) := by
  obtain ⟨g, hg, hn⟩ := hσ (h.left (closedPoint V))
  have P : IsPullback (h ▷ G).left (fst (Over.mk χ) G).left (fst T G).left h.left := by
    refine IsPullback.of_right (h₁₂ := (snd T G).left) (v₁₃ := G.hom) (h₂₂ := T.hom) ?_ ?_
      (IsPullback.of_hasPullback T.hom G.hom).flip
    · rw [VVRank.whisker_snd_left, Over.w h]
      exact (IsPullback.of_hasPullback χ G.hom).flip
    · rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
  obtain ⟨g', h₁, h₂⟩ := Scheme.exists_preimage_of_isPullback P g (closedPoint V) hg
  refine ⟨g', h₂, ?_⟩
  obtain ⟨J, hJ⟩ := exists_good' hL g'
  have u := (isUnit_sval_iff (φ := fun _ : Fin 1 => (snd T G).left) σ (𝟙 _ ≫ (h ▷ G).left) g' hJ).2
    (by rw [Category.id_comp, h₁]; exact hn)
  exact (isUnit_sval_iff (φ := fun _ : Fin 1 => (snd (Over.mk χ) G).left) _ (𝟙 _) g' hJ).1
    ((congrArg IsUnit (VVRank.sv_pullS G _ h σ (𝟙 _) g' hJ)).mpr u)

theorem exists_sec_nz_up {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
    {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ) {L₀ : LB G.left} {L₁ : LB A.left}
    {w : LB.Iso L₁ (L₀.pull φ)} (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (h : GlobalTheory.LN.ThetaNZ A L₁) :
    ∃ σ : LB.Sec (LPow G L₀ ((1 : ℕ) : ℤ) (Over.mk f)),
      ∀ y : (Over.mk f).left, ∃ g, (fst (Over.mk f) G).left g = y ∧ g ∈ nonzeroLocus σ := by
  obtain ⟨θ, hθ⟩ := h
  let T : Over S' := Over.mk (𝟙 S')
  obtain ⟨s, hs⟩ := exists_sec_pull_locus θ (snd T A).left
  have hτ : (𝟙 S' : T.left ⟶ (Over.mk f).left) ≫ (Over.mk f).hom = T.hom ≫ f := rfl
  have : IsIso (𝟙 S' : T.left ⟶ (Over.mk f).left) := IsIso.id S'
  obtain ⟨σ, hσ⟩ := exists_secRel_up (T := T) (T₀ := Over.mk f) hp (𝟙 S') hτ hw hL₀ hL₁ (a := ((1 : ℕ) : ℤ)) s
  refine ⟨σ, fun y => ?_⟩
  obtain ⟨g, i, hg, hi⟩ := hθ y
  obtain ⟨z, h₁, h₂⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback T.hom A.hom) y g hg.symm
  have hz : z ∈ nonzeroLocus s := by
    rw [hs]
    change pullback.snd T.hom A.hom z ∈ nonzeroLocus θ
    rw [h₂]
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  obtain ⟨J, hJ⟩ := exists_good' hL₀ z
  obtain ⟨J', hJ'⟩ := exists_good' hL₁ z
  have e₁ := psi_fst' (T := T) (T₀ := Over.mk f) hp (𝟙 S') hτ
  refine ⟨psi (T := T) (T₀ := Over.mk f) hp (𝟙 S') hτ z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, e₁]
    exact h₁
  have u := (isUnit_sval_iff (φ := fun _ : Fin 1 => (snd T A).left) s (𝟙 _) z hJ').2 hz
  have e := hσ _ (𝟙 _) z J J' hJ hJ'
  rw [Category.id_comp] at e
  exact (isUnit_sval_iff (φ := fun _ : Fin 1 => (snd (Over.mk f) G).left) σ _ z hJ).1
    ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))

theorem exists_nz_of_polAt : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (χ : Sp W ⟶ S) (t' : SAB H (Sp W)) (_ : SABMap t' t χ), GlobalTheory.LN.PolAt t' (jK W) → ∃ σ : LB.Sec (LPow t.G t.PP.L ((1 : ℕ) : ℤ) (Over.mk χ)), ∀ (W' : Type) [CommRing W'] [IsLocalRing W'] (i : W →+* W') (χ' : Sp W' ⟶ S) (h : spMap i ≫ χ = χ'), NZ t.G t.PP.L χ' (VVRank.pullS t.G _ (Over.homMk (spMap i) h : Over.mk χ' ⟶ Over.mk χ) σ) := by
  intro h₁ h₂ E _ _ _ H S t W _ _ _ χ t' m hp
  obtain ⟨w, hw, -⟩ := m.lin
  obtain ⟨σ, hσ⟩ := exists_sec_nz_up m.cart hw t.PP.isLB t'.PP.isLB
    (GlobalTheory.ThetaDvr.thetaNZ_of_polAt h₁ h₂ E H W t' hp)
  exact ⟨σ, fun W' _ _ i χ' h => nz_pullS t.G t.PP.isLB σ hσ χ' _⟩

end GlobalTheory.Ex.OneGen
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nz_of_polAt' : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (χ : Sp W ⟶ S) (t' : SAB H (Sp W)) (_ : SABMap t' t χ), GlobalTheory.LN.PolAt t' (jK W) → ∃ σ : LB.Sec (LPow t.G t.PP.L ((1 : ℕ) : ℤ) (Over.mk χ)), ∀ (W' : Type) [CommRing W'] [IsLocalRing W'] (i : W →+* W') (χ' : Sp W' ⟶ S) (h : spMap i ≫ χ = χ'), NZ t.G t.PP.L χ' (VVRank.pullS t.G _ (Over.homMk (spMap i) h : Over.mk χ' ⟶ Over.mk χ) σ) := by
  first | exact @GlobalTheory.Ex.OneGen.exists_nz_of_polAt | exact GlobalTheory.Ex.OneGen.exists_nz_of_polAt | (intros; apply GlobalTheory.Ex.OneGen.exists_nz_of_polAt <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

namespace GlobalTheory.AbelianTrait

theorem isProper_snd_of_mem_abLocus {S : Scheme.{0}} (G : Over S) [IsSeparated G.hom] [LocallyOfFiniteType G.hom]
    {K : Type} [Field K] (t : Sp K ⟶ S) (p : Sp K) (hp : t p ∈ abLocus G) : IsProper (pullback.snd G.hom t) := by
  let K' := AlgebraicClosure K
  let u : Sp K' ⟶ Sp K := spMap (algebraMap K K')
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have q : Sp K' := (default : PrimeSpectrum K')
  have e : (u ≫ t) q = t p := congrArg (fun z => t z) (Subsingleton.elim (u q) p)
  have h₁ := hp K' (u ≫ t) ⟨q, e⟩
  have P := (IsPullback.of_hasPullback (pullback.snd G.hom t) u).paste_horiz (IsPullback.of_hasPullback G.hom t)
  have h₃ : UniversallyClosed (pullback.snd (pullback.snd G.hom t) u) := by
    rw [← P.isoPullback_hom_snd]
    infer_instance
  have : Nonempty (Sp K') := ⟨q⟩
  have hu : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) u :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have : UniversallyClosed (pullback.snd G.hom t) :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @UniversallyClosed) hu h₃
  exact ⟨⟩

theorem nonempty_pelUnif_of_abLocus : GlobalTheory.LN.UDvrSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (χ : Sp W ⟶ S) (t' : SAB H (Sp W)) (_ : SABMap t' t χ), GlobalTheory.LN.PolAt t' (jK W) → Set.range χ ⊆ abLocus t.G → Nonempty (PELUnif (maximalIdeal W) t') := by
  intro hU E _ _ _ H S t W _ _ _ hW χ t' m hpol hr
  have hG := t'.semi
  have := hG.smooth
  have := hG.separated
  let r : Sp (W ⧸ maximalIdeal W) ⟶ Sp W := spMap (Ideal.Quotient.mk (maximalIdeal W))
  have p : Sp (W ⧸ maximalIdeal W) := (default : PrimeSpectrum (ResidueField W))
  have h₀ : r p ∈ abLocus t'.G := (abLocus_pullback abLocusOne t.semi m.cart.1 (r p)).1 (hr ⟨_, rfl⟩)
  have h₁ : IsProper (pullback.snd t'.G.hom r) := isProper_snd_of_mem_abLocus t'.G (K := ResidueField W) r p h₀
  have h₂ := IsSemiAbelian.pullback r t'.G hG
  obtain ⟨P, -⟩ := hU E H W hW t' hpol
    ⟨_, ZJ.isGt_splitExtOfAbelian _ ⟨h₂.comm, h₂.smooth, h₁, h₂.geomConnected⟩⟩
  exact ⟨P⟩

end GlobalTheory.AbelianTrait
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_uniformisation_trait_in_abelianLocus : GlobalTheory.LN.UDvrSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (χ : Sp W ⟶ S) (t' : SAB H (Sp W)) (_ : SABMap t' t χ), GlobalTheory.LN.PolAt t' (jK W) → Set.range χ ⊆ abLocus t.G → Nonempty (PELUnif (maximalIdeal W) t') := by
  first | exact @GlobalTheory.AbelianTrait.nonempty_pelUnif_of_abLocus | exact GlobalTheory.AbelianTrait.nonempty_pelUnif_of_abLocus | (intros; apply GlobalTheory.AbelianTrait.nonempty_pelUnif_of_abLocus <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.OneGenBasis

theorem pullTo_injective {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K → (Y' ⟶ X)} (p : Y' ⟶ Y) (e : ∀ k, p ≫ φ k = φ' k) [IsSchemeTheoreticallyDominant p] [QuasiCompact p]
    {s t : LB.Sec (LB.LinComb L φ ε)} (h : ∀ j, (VVRank.pullTo s p e).f j = (VVRank.pullTo t p e).f j) (j) :
    s.f j = t.f j := by
  obtain rfl : (fun k => p ≫ φ k) = φ' := funext e
  refine p.app_injective _ (fn_ext fun y hy => ?_)
  have hy' : (𝟙 Y' : _ ⟶ _) y ∈ LB.wchart L (fun k => p ≫ φ k) j :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  exact (gs_res _ y _ hy' _).symm.trans ((congrArg (gs (𝟙 _) y _) (h j)).trans (gs_res _ y _ hy' _))

theorem pullM_injective {S : Scheme.{0}} (G : Over S) [GrpObj G] [Flat G.hom] (L : LB G.left) (a : ℤ) {T T' : Over S}
    (h : T' ⟶ T) [IsSchemeTheoreticallyDominant h.left] [QuasiCompact h.left] :
    Function.Injective (VVRank.pullM G L a h) := by
  have hp : IsPullback (h ▷ G).left (fst T' G).left (fst T G).left h.left := by
    refine IsPullback.of_right (h₁₂ := (snd T G).left) (v₁₃ := G.hom) (h₂₂ := T.hom) ?_ ?_
      (IsPullback.of_hasPullback T.hom G.hom).flip
    · rw [VVRank.whisker_snd_left, Over.w]
      exact (IsPullback.of_hasPullback T'.hom G.hom).flip
    · rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
  have : Flat (fst T G).left :=
    MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback T.hom G.hom).flip inferInstance
  have : IsSchemeTheoreticallyDominant (h ▷ G).left := .of_isPullback hp.flip
  have : QuasiCompact (h ▷ G).left := MorphismProperty.of_isPullback (P := @QuasiCompact) hp.flip inferInstance
  intro s t e
  exact Subtype.ext (funext (pullTo_injective (s := SecM.toSec G s) (t := SecM.toSec G t) (h ▷ G).left
    (fun _ => VVRank.whisker_snd_left G h) fun j => congrFun (congrArg Subtype.val e) j))

theorem exists_eq_mul {W W' : Type} [CommRing W] [IsDomain W] [IsIntegrallyClosed W] [CommRing W'] [IsDomain W']
    (i : W →+* W') (hf : i.Finite) (i' : FractionRing W →+* FractionRing W')
    (hi : i'.comp (algebraMap W _) = (algebraMap W' _).comp i) {a b : FractionRing W} (ha : a ≠ 0) {r : W'}
    (h : i' b = algebraMap W' _ r * i' a) : ∃ r₀ : W, b = algebraMap W _ r₀ * a := by
  have h₁ : i' (b / a) = algebraMap W' _ r := by
    rw [map_div₀, h, mul_div_cancel_right₀ _ ((map_ne_zero i').2 ha)]
  obtain ⟨p, hp, h₂⟩ := hf.to_isIntegral r
  have h₃ : IsIntegral W (b / a) := ⟨p, hp, i'.injective (by
    rw [Polynomial.hom_eval₂, hi, h₁, ← Polynomial.hom_eval₂, h₂, map_zero, map_zero])⟩
  obtain ⟨r₀, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h₃
  exact ⟨r₀, by rw [hr, div_mul_cancel₀ _ ha]⟩

theorem exists_fractionMap {W W' : Type} [CommRing W] [IsDomain W] [CommRing W'] [IsDomain W'] (i : W →+* W')
    (hi : Function.Injective i) : ∃ i' : FractionRing W →+* FractionRing W',
      i'.comp (algebraMap W _) = (algebraMap W' _).comp i := by
  have hg : Function.Injective ((algebraMap W' (FractionRing W')).comp i) := by
    rw [RingHom.coe_comp]
    exact (IsFractionRing.injective W' (FractionRing W')).comp hi
  refine ⟨IsFractionRing.lift (K := FractionRing W) hg, RingHom.ext fun x => ?_⟩
  rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]

theorem appTop_inv {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (x : R) :
    (spMap f).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) =
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (f x) :=
  (congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

theorem inv_bijective (R : Type) [CommRing R] :
    Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
  ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv

theorem exists_eq_mul_fn {W W' : Type} [CommRing W] [IsDomain W] [IsIntegrallyClosed W] [CommRing W'] [IsDomain W']
    (i : W →+* W') (hf : i.Finite) (i' : FractionRing W →+* FractionRing W')
    (hi : i'.comp (algebraMap W _) = (algebraMap W' _).comp i) {a b : Γ(Sp (FractionRing W), ⊤)} (ha : a ≠ 0)
    {r : Γ(Sp W', ⊤)} (h : (spMap i').appTop.hom b = (jK W').appTop.hom r * (spMap i').appTop.hom a) :
    ∃ r₀ : Γ(Sp W, ⊤), b = (jK W).appTop.hom r₀ * a := by
  obtain ⟨a, rfl⟩ := (inv_bijective _).2 a
  obtain ⟨b, rfl⟩ := (inv_bijective _).2 b
  obtain ⟨r, rfl⟩ := (inv_bijective _).2 r
  rw [appTop_inv, appTop_inv, appTop_inv, ← map_mul] at h
  obtain ⟨r₀, hr⟩ := exists_eq_mul i hf i' hi (a := a) (fun e => ha (by rw [e, map_zero]))
    ((inv_bijective (FractionRing W')).1 h)
  exact ⟨(Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom r₀, by
    rw [appTop_inv (algebraMap W (FractionRing W)), ← map_mul, ← hr]⟩

theorem basis_of_square {A A' K K' M M' N N' : Type} [CommRing A] [CommRing A'] [CommRing K] [CommRing K'] [IsDomain K]
    [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N] [AddCommGroup N'] [Module A M] [Module A' M'] [Module K N]
    [Module K' N'] {f : A →+* K} {g : A →+* A'} {f' : A' →+* K'} {g' : K →+* K'} (p : M →ₛₗ[f] N) (q : M →ₛₗ[g] M')
    (p' : M' →ₛₗ[f'] N') (q' : N →ₛₗ[g'] N') (hsq : ∀ x, q' (p x) = p' (q x)) (hp : Function.Injective p)
    (hf : Function.Injective f) (e : N) (h₀ : ∀ s, ∃! c : K, s = c • e) (h₁ : ∀ s, ∃! c : K', s = c • q' e) (σ : M)
    (hne : p σ ≠ 0) (hgen : ∀ s, ∃ r : A', q s = r • q σ)
    (hint : ∀ a b r, a ≠ 0 → g' b = f' r * g' a → ∃ r₀, b = f r₀ * a) :
    LinearIndependent A (fun _ : Fin 1 => σ) ∧ Submodule.span A (Set.range fun _ : Fin 1 => σ) = ⊤ := by
  obtain ⟨a, ha, -⟩ := h₀ (p σ)
  have ha0 : a ≠ 0 := fun h => hne (ha.trans (by rw [h, zero_smul]))
  refine ⟨Fintype.linearIndependent_iff.2 fun c hc k => ?_, eq_top_iff.2 fun s _ => ?_⟩
  · rw [Fin.sum_univ_one] at hc
    rw [Subsingleton.elim k 0]
    have t := congrArg p hc
    rw [map_smulₛₗ, ha, smul_smul, map_zero] at t
    have t' := (h₀ 0).unique t.symm (zero_smul _ _).symm
    exact hf (((mul_eq_zero.1 t').resolve_right ha0).trans (map_zero _).symm)
  · obtain ⟨b, hb, -⟩ := h₀ (p s)
    obtain ⟨r, hr⟩ := hgen s
    have t := congrArg p' hr
    rw [map_smulₛₗ, ← hsq, ← hsq, ha, hb, map_smulₛₗ, map_smulₛₗ, smul_smul] at t
    obtain ⟨r₀, hr₀⟩ := hint a b r ha0 ((h₁ _).unique rfl t)
    have : s = r₀ • σ := hp (by rw [map_smulₛₗ, ha, hb, smul_smul, hr₀])
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)

theorem basisAlong_of_isGenSec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Flat G.hom] (L : LB G.left), L.IsLB → ∀ (W W' : Type) [CommRing W] [IsDomain W] [IsIntegrallyClosed W] [CommRing W'] [IsDomain W'] (i : W →+* W'), Function.Injective i → i.Finite → ∀ (χ : Sp W ⟶ S) (σ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ))), IsGenSec G L ((1 : ℕ) : ℤ) (VVRank.pullS G _ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ χ) ⟶ Over.mk χ) σ) → (∃ e, UnivBasis G L (jK W ≫ χ) e) → SecM.ofSec G (VVRank.pullS G _ (Over.homMk (jK W) rfl : Over.mk (jK W ≫ χ) ⟶ Over.mk χ) σ) ≠ 0 → GlobalTheory.LN.BasisAlong G L 1 (𝟙 (Over.mk χ)) (fun _ : Fin 1 => σ) := by
  intro S G _ _ L hL W W' _ _ _ _ _ i hinj hf χ σ hgen ⟨e, he⟩ hne
  obtain ⟨i', hi⟩ := exists_fractionMap i hinj
  have hsq : spMap i' ≫ jK W = jK W' ≫ spMap i := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hi]
  let hK : Over.mk (jK W ≫ χ) ⟶ Over.mk χ := Over.homMk (jK W) rfl
  let hI : Over.mk (spMap i ≫ χ) ⟶ Over.mk χ := Over.homMk (spMap i) rfl
  let hI' : Over.mk (spMap i' ≫ jK W ≫ χ) ⟶ Over.mk (jK W ≫ χ) := Over.homMk (spMap i') rfl
  let hK' : Over.mk (spMap i' ≫ jK W ≫ χ) ⟶ Over.mk (spMap i ≫ χ) := Over.homMk (jK W') (by
    change jK W' ≫ spMap i ≫ χ = spMap i' ≫ jK W ≫ χ
    rw [← Category.assoc, ← hsq, Category.assoc])
  have hsq' : hI' ≫ hK = hK' ≫ hI := Over.OverMorphism.ext hsq
  have : IsSchemeTheoreticallyDominant hK.left := (ExtUnique.spec_fractionRing W (FractionRing W)).2
  have : QuasiCompact hK.left := (ExtUnique.spec_fractionRing W (FractionRing W)).1
  have hρ := pullM_injective G L ((1 : ℕ) : ℤ) hK
  have hid : spMap (RingHom.id (FractionRing W)) = 𝟙 _ := Spec.map_id _
  have h₀ : ∀ s : SecM G L ((1 : ℕ) : ℤ) (Over.mk (jK W ≫ χ)), ∃! c : Γ((Over.mk (jK W ≫ χ)).left, ⊤),
      s = c • SecM.ofSec G e := fun s => by
    have q := he _ (RingHom.id _) _ (by rw [hid, Category.id_comp]) s
    rwa [← VVRank.pullM_ofSec, show (Over.homMk (spMap (RingHom.id (FractionRing W))) _ :
      Over.mk (jK W ≫ χ) ⟶ Over.mk (jK W ≫ χ)) = 𝟙 _ from Over.OverMorphism.ext hid, VVRank.pullM_id G hL] at q
  have h₁ : ∀ s, ∃! c : Γ((Over.mk (spMap i' ≫ jK W ≫ χ)).left, ⊤),
      s = c • VVRank.pullM G L ((1 : ℕ) : ℤ) hI' (SecM.ofSec G e) := he _ i' _ rfl
  have hdom : IsDomain Γ((Over.mk (jK W ≫ χ)).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing W))).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  have key := basis_of_square (VVRank.pullM G L ((1 : ℕ) : ℤ) hK) (VVRank.pullM G L _ hI) (VVRank.pullM G L _ hK')
    (VVRank.pullM G L _ hI') (fun x => by rw [VVRank.pullM_comp G hL, VVRank.pullM_comp G hL, hsq']) hρ
    (hK.left.app_injective ⊤) _ h₀ h₁ (SecM.ofSec G σ) hne
    (fun s => (hgen (SecM.toSec G (VVRank.pullM G L _ hI s))).imp fun _ hr => Subtype.ext (funext hr))
    fun a b r ha h => exists_eq_mul_fn i hf i' hi ha h
  rw [← VVRank.pullM_id G hL _ (SecM.ofSec G σ)] at key
  exact (GlobalTheory.LN.PolFrames.basisAlong_iff G L 1 (𝟙 _) hL
    (b' := fun _ => VVRank.pullS G _ (𝟙 _) σ) fun _ => VVRank.isPullSec_pullS G _ _ σ).2 key

end GlobalTheory.Ex.OneGenBasis
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generatingSection_finite_ext_normal_domain_isBasis : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Flat G.hom] (L : LB G.left), L.IsLB → ∀ (W W' : Type) [CommRing W] [IsDomain W] [IsIntegrallyClosed W] [CommRing W'] [IsDomain W'] (i : W →+* W'), Function.Injective i → i.Finite → ∀ (χ : Sp W ⟶ S) (σ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ))), IsGenSec G L ((1 : ℕ) : ℤ) (VVRank.pullS G _ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ χ) ⟶ Over.mk χ) σ) → (∃ e, UnivBasis G L (jK W ≫ χ) e) → SecM.ofSec G (VVRank.pullS G _ (Over.homMk (jK W) rfl : Over.mk (jK W ≫ χ) ⟶ Over.mk χ) σ) ≠ 0 → GlobalTheory.LN.BasisAlong G L 1 (𝟙 (Over.mk χ)) (fun _ : Fin 1 => σ) := by
  atlas_forward_decl GlobalTheory.Ex.OneGenBasis.basisAlong_of_isGenSec
end

section
namespace GlobalTheory

theorem exists_extend_of_ringEquiv_of_isAlgebraic {K L M F : Type} [Field K] [Field L] [Field M] [Field F]
    [IsAlgClosed F] [Algebra L M] [Algebra.IsAlgebraic L M] (φ : K ≃+* L) (g : K →+* F) :
    ∃ g' : M →+* F, g'.comp ((algebraMap L M).comp φ.toRingHom) = g := by
  letI : Algebra L F := (g.comp φ.symm.toRingHom).toAlgebra
  let g' : M →ₐ[L] F := IsAlgClosed.lift
  refine ⟨g'.toRingHom, RingHom.ext fun x => ?_⟩
  change g' (algebraMap L _ (φ x)) = g x
  rw [g'.commutes]
  change g (φ.symm (φ x)) = g x
  rw [φ.symm_apply_apply]

theorem exists_finite_normal_adjoin_algebraic :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R]
      (s : AlgebraicClosure (FractionRing R)),
      ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (h : R →+* R₂)
        (h' : FractionRing R →+* FractionRing R₂)
        (e : FractionRing R₂ →+* AlgebraicClosure (FractionRing R)),
        Function.Injective h ∧ h.Finite ∧ IsIntegrallyClosed R₂ ∧
        (∀ r, h' (algebraMap R _ r) = algebraMap R₂ _ (h r)) ∧ e.comp h' = algebraMap _ _ ∧
        (∃ s₂, e s₂ = s) ∧
        ∀ (F : Type) [Field F] [IsAlgClosed F] (g : FractionRing R₂ →+* F),
          ∃ g' : AlgebraicClosure (FractionRing R) →+* F, g'.comp e = g := by
  intro R _ _ _ _ _ s
  have : CharZero (FractionRing R) := IsFractionRing.charZero_of_isFractionRing R
  let L : IntermediateField (FractionRing R) (AlgebraicClosure (FractionRing R)) :=
    IntermediateField.adjoin (FractionRing R) {s}
  have : FiniteDimensional (FractionRing R) L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral s)
  have : Algebra.IsSeparable (FractionRing R) L := inferInstance
  have hfin : Module.Finite R (integralClosure R L) :=
    IsIntegralClosure.finite R (FractionRing R) L (integralClosure R L)
  have hfr : IsFractionRing (integralClosure R L) L :=
    integralClosure.isFractionRing_of_finite_extension (FractionRing R) L
  let φ : FractionRing (integralClosure R L) ≃+* L :=
    (FractionRing.algEquiv (integralClosure R L) L).toRingEquiv
  have hφ : ∀ x : integralClosure R L,
      φ (algebraMap (integralClosure R L) _ x) = algebraMap (integralClosure R L) L x :=
    fun x => (FractionRing.algEquiv (integralClosure R L) L).commutes x
  refine ⟨integralClosure R L, inferInstance, inferInstance, algebraMap R _,
    φ.symm.toRingHom.comp (algebraMap (FractionRing R) L),
    (algebraMap L (AlgebraicClosure (FractionRing R))).comp φ.toRingHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have h1 : algebraMap R L a = algebraMap R L b := by
      rw [IsScalarTower.algebraMap_apply R (integralClosure R L) L,
        IsScalarTower.algebraMap_apply R (integralClosure R L) L b, hab]
    rw [IsScalarTower.algebraMap_apply R (FractionRing R) L,
      IsScalarTower.algebraMap_apply R (FractionRing R) L b] at h1
    exact IsFractionRing.injective R (FractionRing R) ((algebraMap (FractionRing R) L).injective h1)
  · exact RingHom.finite_algebraMap.2 hfin
  · exact (isIntegrallyClosed_iff_isIntegrallyClosedIn L).2 inferInstance
  · intro r
    apply φ.injective
    rw [hφ, ← IsScalarTower.algebraMap_apply R (integralClosure R L) L,
      IsScalarTower.algebraMap_apply R (FractionRing R) L]
    exact φ.apply_symm_apply _
  · refine RingHom.ext fun x => ?_
    change algebraMap L _ (φ (φ.symm (algebraMap (FractionRing R) L x))) = _
    rw [φ.apply_symm_apply, ← IsScalarTower.algebraMap_apply]
  · refine ⟨φ.symm ⟨s, IntermediateField.mem_adjoin_simple_self _ s⟩, ?_⟩
    change algebraMap L _ (φ (φ.symm _)) = _
    rw [φ.apply_symm_apply]
    rfl
  · intro F _ _ g
    have : Algebra.IsAlgebraic L (AlgebraicClosure (FractionRing R)) :=
      Algebra.IsAlgebraic.tower_top (K := FractionRing R) L
    exact exists_extend_of_ringEquiv_of_isAlgebraic φ g

end GlobalTheory
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integrally_closed_extension_of_adjoin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (s : AlgebraicClosure (FractionRing R)), ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (h : R →+* R₂) (h' : FractionRing R →+* FractionRing R₂) (e : FractionRing R₂ →+* AlgebraicClosure (FractionRing R)), Function.Injective h ∧ h.Finite ∧ IsIntegrallyClosed R₂ ∧ (∀ r, h' (algebraMap R _ r) = algebraMap R₂ _ (h r)) ∧ e.comp h' = algebraMap _ _ ∧ (∃ s₂, e s₂ = s) ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] (g : FractionRing R₂ →+* F), ∃ g' : AlgebraicClosure (FractionRing R) →+* F, g'.comp e = g := by
  atlas_forward_decl GlobalTheory.exists_finite_normal_adjoin_algebraic
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

namespace GlobalTheory.FiniteDVRValuation

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} in

theorem _root_.GlobalTheory.FiniteDVRValuation.exists_nat_val (hϖ : Irreducible ϖ) (hv : _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ F v) {c : V}
    (hc : c ≠ 0) :
    ∃ n : ℕ, v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) c)) =
        ((n : ℚ) : WithTop ℚ) ∧ (n = 0 → IsUnit c) := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  refine ⟨n, ?_, fun hn => by subst hn; simp⟩
  rw [hv _ n ⟨u, by rw [zpow_natCast, map_mul, map_pow, mul_comm]⟩]
  norm_cast

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} in
theorem _root_.GlobalTheory.FiniteDVRValuation.val_nonneg (hϖ : Irreducible ϖ) (hv : _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ F v) (c : V) :
    0 ≤ v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) c)) := by
  by_cases hc : c = 0
  · subst hc
    simp
  · obtain ⟨n, hn, -⟩ := _root_.GlobalTheory.FiniteDVRValuation.exists_nat_val hϖ hv hc
    rw [hn]
    exact_mod_cast n.cast_nonneg

end

def nonnegSubring {F K : Type} [Field F] [Field K] (v : AddValuation F (WithTop ℚ)) (e : K →+* F) :
    ValuationSubring K where
  carrier := {x | 0 ≤ v (e x)}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_mul, AddValuation.map_mul] at *
    exact add_nonneg ha hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at *
    exact v.map_le_add ha hb
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, map_neg, AddValuation.map_neg] at *
    exact ha
  mem_or_inv_mem' := by
    intro x
    simp only [Set.mem_setOf_eq]
    by_cases hx : x = 0
    · left; simp [hx]
    by_contra hcon
    push_neg at hcon
    have h1 : v (e x) + v (e x⁻¹) = 0 := by
      rw [← AddValuation.map_mul, ← map_mul, mul_inv_cancel₀ hx, map_one, AddValuation.map_one]
    have h2 : v (e x) + v (e x⁻¹) < 0 := by
      calc v (e x) + v (e x⁻¹) ≤ 0 + v (e x⁻¹) := by gcongr; exact hcon.1.le
        _ = v (e x⁻¹) := zero_add _
        _ < 0 := hcon.2
    exact h2.ne h1

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing in
open scoped CategoryTheory.Obj BigOperators in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.FiniteDVRValuation.main :
    ∀ (W W' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing W']
      [IsDomain W'] [IsDiscreteValuationRing W'] (i : W →+* W'), Function.Injective i →
      i.Finite → ∀ (ϖ : W'), Irreducible ϖ → ∀ (F : Type) [Field F]
      [Algebra (FractionRing W') F] (v : AddValuation F (WithTop ℚ)), _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ F v →
      (∀ r : W', 0 ≤ v (algebraMap (FractionRing W') F (algebraMap W' _ r))) ∧
      (∃ i' : FractionRing W →+* FractionRing W',
        (∀ r, i' (algebraMap W _ r) = algebraMap W' _ (i r)) ∧
        ∀ a : FractionRing W, v (algebraMap (FractionRing W') F (i' a)) = 0 →
          ∃ u : Wˣ, algebraMap W (FractionRing W) u = a) ∧
      ∀ (K : Type) [Field K] (e : K →+* F), ∃ S : ValuationSubring K,
        ∀ x, (x ∈ S ↔ 0 ≤ v (e x)) ∧ (S.valuation x = 1 → v (e x) = 0) := by
  intro W W' _ _ _ _ _ _ i hi hfin ϖ hϖ F _ _ v hv
  refine ⟨fun r => _root_.GlobalTheory.FiniteDVRValuation.val_nonneg hϖ hv r, ?_,
    fun K _ e => ⟨_root_.GlobalTheory.FiniteDVRValuation.nonnegSubring v e, fun x => ⟨Iff.rfl, fun h => ?_⟩⟩⟩
  · have hinj : Function.Injective ((algebraMap W' (FractionRing W')).comp i) :=
      (IsFractionRing.injective W' (FractionRing W')).comp hi
    have hunit : ∀ x : W,
        v (algebraMap (FractionRing W') F (algebraMap W' _ (i x))) = 0 → IsUnit x := by
      intro x hx
      by_contra hxu
      have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' i hfin.to_isIntegral
        (IsLocalRing.maximalIdeal W')
      have hcomap : (IsLocalRing.maximalIdeal W').comap i = IsLocalRing.maximalIdeal W :=
        IsLocalRing.eq_maximalIdeal hmax
      have hmem : x ∈ (IsLocalRing.maximalIdeal W').comap i := by
        rw [hcomap]
        exact (IsLocalRing.mem_maximalIdeal x).2 hxu
      have hix : ¬IsUnit (i x) := (IsLocalRing.mem_maximalIdeal _).1 (Ideal.mem_comap.1 hmem)
      have hle := (_root_.ReciprocityTheory.ChartRestriction.G.DVR.TWO.v_of_V v hϖ hv (i x)).2 hix ((map_ne_zero_iff i hi).2 hx0)
      have hle' : (1 : WithTop ℚ) ≤ 0 := by
        rw [← hx]
        exact hle
      exact absurd hle' (by norm_num)
    refine ⟨IsFractionRing.lift hinj, fun r => IsFractionRing.lift_algebraMap hinj r,
      fun a ha => ?_⟩
    by_cases ha0 : a = 0
    · subst ha0
      simp at ha
    rcases ValuationRing.isInteger_or_isInteger W a with ⟨x, hx⟩ | ⟨x, hx⟩
    · subst hx
      rw [IsFractionRing.lift_algebraMap, RingHom.comp_apply] at ha
      exact ⟨(hunit x ha).unit, rfl⟩
    · have hinv : v (algebraMap (FractionRing W') F (IsFractionRing.lift hinj a⁻¹)) = 0 := by
        have hsum : v (algebraMap (FractionRing W') F (IsFractionRing.lift hinj a)) +
            v (algebraMap (FractionRing W') F (IsFractionRing.lift hinj a⁻¹)) = 0 := by
          rw [← AddValuation.map_mul, ← map_mul, ← map_mul, mul_inv_cancel₀ ha0, map_one, map_one,
            AddValuation.map_one]
        rwa [ha, zero_add] at hsum
      rw [← hx, IsFractionRing.lift_algebraMap, RingHom.comp_apply] at hinv
      refine ⟨(hunit x hinv).unit⁻¹, ?_⟩
      rw [← inv_inv a, ← hx, map_units_inv, IsUnit.unit_spec]
  · have hx0 : x ≠ 0 := by
      rintro rfl
      simp at h
    have h1 : x ∈ _root_.GlobalTheory.FiniteDVRValuation.nonnegSubring v e := (ValuationSubring.valuation_le_one_iff _ _).1 h.le
    have h2 : x⁻¹ ∈ _root_.GlobalTheory.FiniteDVRValuation.nonnegSubring v e :=
      (ValuationSubring.valuation_le_one_iff _ _).1 (by rw [map_inv₀, h, inv_one])
    change 0 ≤ v (e x) at h1
    change 0 ≤ v (e x⁻¹) at h2
    have hsum : v (e x) + v (e x⁻¹) = 0 := by
      rw [← AddValuation.map_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, AddValuation.map_one]
    exact le_antisymm (le_add_of_nonneg_right h2 |>.trans_eq hsum) h1

end GlobalTheory.FiniteDVRValuation
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_over_finite_dvr_extension : ∀ (W W' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing W'] [IsDomain W'] [IsDiscreteValuationRing W'] (i : W →+* W'), Function.Injective i → i.Finite → ∀ (ϖ : W'), Irreducible ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing W') F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → (∀ r : W', 0 ≤ v (algebraMap (FractionRing W') F (algebraMap W' _ r))) ∧ (∃ i' : FractionRing W →+* FractionRing W', (∀ r, i' (algebraMap W _ r) = algebraMap W' _ (i r)) ∧ ∀ a : FractionRing W, v (algebraMap (FractionRing W') F (i' a)) = 0 → ∃ u : Wˣ, algebraMap W (FractionRing W) u = a) ∧ ∀ (K : Type) [Field K] (e : K →+* F), ∃ S : ValuationSubring K, ∀ x, (x ∈ S ↔ 0 ≤ v (e x)) ∧ (S.valuation x = 1 → v (e x) = 0) := by
  first | exact @GlobalTheory.FiniteDVRValuation.main | exact GlobalTheory.FiniteDVRValuation.main | (intros; apply GlobalTheory.FiniteDVRValuation.main <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.OneGen

section
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem exists_normalised_unit (hL : L.IsLB) {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (m : ℕ) (a b c : ℤ)
    (hc : c = a - b)
    (α₀ : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -b])) (h₀ : α₀.IsGen) :
    ∃ (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -b])) (d : Γ(T.left, ⊤)ˣ),
      α.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ α (ptSecT A 1).left) (rigT A L ρ T c) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
        val α r z J = gm (r ≫ (fst T A).left) z ⊤ d * val α₀ r z J := by
  have hγ := DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ h₀ (ptSecT A 1).left)) (NormTheta.rigT_isGen (T := T) hρ c)
  obtain ⟨d, hd⟩ := SymLiftOdd.exists_const hL (𝟙 T.left) (𝟙 T.left) (Category.comp_id _) (fun v => ⟨v, rfl⟩)
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, NormTheta.ptSec_snd, NormTheta.ptSec_snd_pow, hc]
      rw [← zpow_add, ← zpow_add, show -a + - -b + (a - b) = 0 by ring, zpow_zero]) hγ
  obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ^ m).left]) (ε' := ![a, -b])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, NormTheta.ptSec_snd, NormTheta.ptSec_snd_pow, hc]
      rw [← zpow_add, ← zpow_add, show -a + - -b + (a - b) = 0 by ring, zpow_zero, _root_.mul_one])
    (LB.mulGen L _ _ _ _ α₀ (LB.pullGen L _ _ (LB.mulGen L _ _ _ _
      (LB.invGen L _ _ (LB.pullGen L _ _ α₀ (ptSecT A 1).left)) (rigT A L ρ T c)) (fst T A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ h₀ (DVR.pullGen_isGen _ _ _ _ hγ _))
  refine ⟨α, d, hα, corr_of_val hL fun y J hJ => ?_, fun Z r z J hJ => ?_⟩
  · rw [val_pull hJ, hv _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, NormTheta.ptSec_fst, Category.comp_id,
      val_mul hJ, val_inv, val_pull hJ, mul_inv_cancel_left]
  · rw [hv _ _ z J hJ, val_mul hJ, val_pull hJ, hd _ _ z J hJ, Category.comp_id, mul_comm]

theorem isGenSec_smul {k : ℤ} {th : LB.Sec (LPow A L k T)} (H : IsGenSec A L k th) (e : Γ(T.left, ⊤)ˣ) :
    IsGenSec A L k (SecM.toSec A ((e : Γ(T.left, ⊤)) • SecM.ofSec A th)) := fun s => by
  obtain ⟨r, hr⟩ := H s
  have e₁ : SecM.ofSec A s = r • SecM.ofSec A th := Subtype.ext (funext hr)
  have e₂ : SecM.ofSec A s = (r * (e⁻¹ : Γ(T.left, ⊤)ˣ)) • ((e : Γ(T.left, ⊤)) • SecM.ofSec A th) := by
    rw [← mul_smul, _root_.mul_assoc, Units.inv_mul, _root_.mul_one, e₁]
  exact ⟨_, fun j => congrArg (fun q => q.1 j) e₂⟩

theorem exists_thG (hL : L.IsLB) {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (m : ℕ) (a : ℤ)
    (ha : a = ((m ^ 2 : ℕ) : ℤ)) {I : Type} {x : I → (T ⟶ A)} (hx : ∀ i, x i ^ (m ^ 2) = 1)
    {th : LB.Sec (LPow A L ((1 : ℕ) : ℤ) T)} {s₁ : LB.Sec (LPow A L a T)}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -((1 : ℕ) : ℤ)])}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => (1 : T ⟶ A).left) (fun _ => a))}
    {U : I → ThetaGrp A L a T} {s₂ : I → LB.Sec (LPow A L a T)} {w : I → Γ(T.left, ⊤)}
    (hα : α.IsGen) (hτ : τ.IsGen)
    (h₁ : IsTwistPull A L (mulT A T m) (snd T A ^ m) (lift_snd _ _) a ((1 : ℕ) : ℤ) α th s₁)
    (hU : ∀ i, SymLift A L a (m ^ 2) (x i) (U i)) (h₂ : ∀ i, IsActOf A L a (U i) s₁ (s₂ i))
    (hw : ∀ i, IsValueAt A L a (s₂ i) 1 τ (w i)) :
    ∃ e : Γ(T.left, ⊤)ˣ, ∀ i, ThG A L ρ m th (x i) (e * w i) := by
  subst ha
  obtain ⟨α', d, hα', hn, hv⟩ := exists_normalised_unit hL hρ m _ _ (((m ^ 2 : ℕ) : ℤ) - 1) rfl α hα
  obtain ⟨b, hb⟩ := SymLiftOdd.exists_const hL (𝟙 T.left) (𝟙 T.left) (Category.comp_id _) (fun v => ⟨v, rfl⟩)
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr, NormTheta.one_left, zpow_neg,
        mul_inv_cancel])
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hτ (DVR.invGen_isGen _ _ _ _ (NormTheta.rigT_isGen (T := T) hρ ((m ^ 2 : ℕ) : ℤ))))
  refine ⟨d * b, fun i => ⟨hx i, SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A (s₂ i)), α',
    SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A s₁), U i, hα', hn, ?_, hU i, ?_, fun y J hJ => ?_⟩⟩
  · refine VVRank.isTwistPull_of_sv A hL hα' fun y J hJ => ?_
    rw [sv_of_eq_mul (s := SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A s₁)) (t := s₁) (c := d) (fun j => rfl) _ y hJ,
      VVRank.sv_of_isTwistPull A h₁ (𝟙 _) y hJ, hv _ _ y J hJ, gs_unit _ _ ⊤ trivial, Units.val_mul, _root_.mul_assoc]
  · refine VVRank.isTwistPull_of_sv A hL (U i).isGen fun y J hJ => ?_
    rw [sv_of_eq_mul (s := SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A s₁)) (t := s₁) (c := d) (fun j => rfl) _ y hJ,
      sv_of_eq_mul (s := SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A (s₂ i))) (t := s₂ i) (c := d) (fun j => rfl) _ y hJ,
      VVRank.sv_of_isTwistPull A (h₂ i) (𝟙 _) y hJ, Category.assoc, ← Over.comp_left, translT, lift_fst, mul_left_comm]
  · have q := ThetaPtMove.sv_of_isValueAt (hw i) (𝟙 _) y hJ
    have q' := hb _ (𝟙 _) y J hJ
    rw [val_mul hJ, val_inv, Category.comp_id, mul_inv_eq_iff_eq_mul] at q'
    rw [Category.id_comp, q', Units.val_mul, ← gs_unit _ _ ⊤ trivial] at q
    rw [sv_of_eq_mul (s := SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A (s₂ i))) (t := s₂ i) (c := d) (fun j => rfl) _ y hJ,
      q, ptSecT_fst, Units.val_mul, gs_mul _ y ⊤ trivial, gs_mul _ y ⊤ trivial]
    ring

end

theorem exists_gen_thG_of_isThetaPt : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (ρ : LB.Gen (P.L.pull (eSec P.A))), ρ.IsGen → ∀ (m : ℕ) (Ix : Type) (x : Ix → (baseOver (Sp K) ⟶ P.A)) (v : Ix → K), (∀ i, x i ^ (m ^ 2) = 1) → IsThetaPt P m x (fun i => fnOf (v i)) → ∃ th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver (Sp K))), IsGenSec P.A P.L ((1 : ℕ) : ℤ) th ∧ ∀ i, ThG P.A P.L ρ m th (x i) (fnOf (v i)) := by
  intro K _ P ρ hρ m Ix x v hx H
  have : Subsingleton (baseOver (Sp K)).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (baseOver (Sp K)).left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨th, s₁, α, τ, U, s₂, w, u, hth, hα, hτ, h₁, hU, h₂, hw, hv⟩ := ThetaCoord.isThetaPtOver_of_subsingleton P H
  obtain ⟨e, he⟩ := exists_thG P.isLB hρ m ((m : ℤ) ^ 2) (Nat.cast_pow m 2).symm hx (th := th) (α := α) hα hτ h₁ hU h₂ hw
  refine ⟨_, isGenSec_smul hth (u * e⁻¹), fun i => ?_⟩
  have q := ThG.smul P.isLB (a := ((u * e⁻¹ : Γ((baseOver (Sp K)).left, ⊤)ˣ) : Γ((baseOver (Sp K)).left, ⊤)))
    (th' := SecM.toSec P.A (((u * e⁻¹ : Γ((baseOver (Sp K)).left, ⊤)ˣ) : Γ((baseOver (Sp K)).left, ⊤)) • SecM.ofSec P.A th))
    rfl (he i)
  rw [Units.val_mul, _root_.mul_assoc, Units.inv_mul_cancel_left, ← hv i] at q
  exact q

end GlobalTheory.Ex.OneGen
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_thetaPoint_normalised_thetaConstants : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (ρ : LB.Gen (P.L.pull (eSec P.A))), ρ.IsGen → ∀ (m : ℕ) (Ix : Type) (x : Ix → (baseOver (Sp K) ⟶ P.A)) (v : Ix → K), (∀ i, x i ^ (m ^ 2) = 1) → IsThetaPt P m x (fun i => fnOf (v i)) → ∃ th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver (Sp K))), IsGenSec P.A P.L ((1 : ℕ) : ℤ) th ∧ ∀ i, ThG P.A P.L ρ m th (x i) (fnOf (v i)) := by
  first | exact @GlobalTheory.Ex.OneGen.exists_gen_thG_of_isThetaPt | exact GlobalTheory.Ex.OneGen.exists_gen_thG_of_isThetaPt | (intros; apply GlobalTheory.Ex.OneGen.exists_gen_thG_of_isThetaPt <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.OneGen

section Pts
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
include hp hτ

theorem exists_torsion_up [IsIso τ] {n : ℕ} (x : T ⟶ A) (hx : x ^ n = 1) :
    ∃ x₀ : T₀ ⟶ G, τ ≫ x₀.left = x.left ≫ φ ∧ x₀ ^ n = 1 := by
  let x₀ : T₀ ⟶ G := Over.homMk (inv τ ≫ x.left ≫ φ) (by
    rw [Category.assoc, Category.assoc, hp.1.w, IsIso.inv_comp_eq, hτ, ← Category.assoc, Over.w])
  have e : τ ≫ x₀.left = x.left ≫ φ := IsIso.hom_inv_id_assoc _ _
  refine ⟨x₀, e, Over.OverMorphism.ext ((cancel_epi τ).1 ?_)⟩
  rw [over_pow hp τ hτ e, hx, over_one hp τ hτ]

theorem exists_torsion_down {n : ℕ} (x₀ : T₀ ⟶ G) (hx : x₀ ^ n = 1) :
    ∃ x : T ⟶ A, τ ≫ x₀.left = x.left ≫ φ ∧ x ^ n = 1 := by
  have w : (τ ≫ x₀.left) ≫ G.hom = T.hom ≫ f := by rw [Category.assoc, Over.w, hτ]
  let x : T ⟶ A := Over.homMk (hp.1.lift _ _ w) (hp.1.lift_snd _ _ _)
  have e : τ ≫ x₀.left = x.left ≫ φ := (hp.1.lift_fst _ _ _).symm
  refine ⟨x, e, Over.OverMorphism.ext (hp.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩
  rw [← over_pow hp τ hτ e, hx, over_one hp τ hτ]

theorem secRel_smul {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)} {a : ℤ} {B : Over S}
    (σ : T.left ⟶ B.left) (hσ : σ ≫ B.hom = T.hom ≫ f) (β : B ⟶ T₀) (hβ : σ ≫ β.left = τ)
    {th : LB.Sec (LPow A L₁ a T)} {th₀ : LB.Sec (LPow G L₀ a T₀)} (h : SecRel hp τ hτ w th th₀)
    {th' : LB.Sec (LPow G L₀ a B)} {c : Γ(B.left, ⊤)}
    (hc : SecM.ofSec G th' = c • SecM.ofSec G (VVRank.pullS G a β th₀)) :
    SecRel hp σ hσ w (SecM.toSec A (σ.appTop.hom c • SecM.ofSec A th)) th' := by
  intro Z r z J J' hJ hJ'
  have e : psi hp σ hσ ≫ (β ▷ G).left = psi hp τ hτ := by
    refine psi_ext ?_ ?_
    · rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, ← Category.assoc, psi_fst', psi_fst',
        Category.assoc, hβ]
    · rw [Category.assoc, VVRank.whisker_snd_left, psi_snd', psi_snd']
  rw [sv_of_eq_mul (s := th') (t := VVRank.pullS G a β th₀) (c := c) (fun j => congrArg (fun q => q.1 j) hc) _ z hJ,
    sv_of_eq_mul (s := SecM.toSec A (σ.appTop.hom c • SecM.ofSec A th)) (t := th) (c := σ.appTop.hom c)
      (fun j => rfl) _ z hJ',
    VVRank.sv_pullS _ _ _ _ _ _ hJ, Category.assoc r _ (β ▷ G).left, e, h _ _ _ _ _ hJ hJ', mul_left_comm,
    Category.assoc r _ (fst B G).left, psi_fst', ← Category.assoc]
  exact congrArg (fun q => _ * (q * _)) (gs_pull _ σ z ⊤ trivial c).symm

end Pts

theorem exists_gen_thG_generic : Laws → Laws2 → ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x₀ : Sp K ⟶ S) (P : PolAV (Sp K)) (φ : P.A.left ⟶ G.left), IsGrpPullback P.A G x₀ φ → LBIso P.L (L.pull φ) → ∀ (m : ℕ), Odd m → ∀ (Ix : Type) (x : Ix → (baseOver (Sp K) ⟶ P.A)) (v : Ix → K), (∀ y, y ^ (m ^ 2) = 1 ↔ ∃ i, x i = y) → IsThetaPt P m x (fun i => fnOf (v i)) → ∃ th : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x₀)), IsGenSec G L ((1 : ℕ) : ℤ) th ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] (e : K →+* F) (x' : Sp F ⟶ S) (h : spMap e ≫ x₀ = x') (a : F) (th' : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x'))), SecM.ofSec G th' = @id Γ((Over.mk x').left, ⊤) (fnOf a) • SecM.ofSec G (VVRank.pullS G _ (Over.homMk (spMap e) h : Over.mk x' ⟶ Over.mk x₀) th) → (∀ i, ∃ z, ThG G L ρ m th' z (fnOf (a * e (v i)))) ∧ ∀ z (c : F), ThG G L ρ m th' z (fnOf c) → ∃ i, c = a * e (v i) := by
  intro hLaw _ S G _ L ρ hL hρ K _ _ _ x₀ P φ hp ⟨w, hw⟩ m hm Ix x v hx hv
  have hL₁ := P.isLB
  have := P.isAb.comm
  obtain ⟨ρ', hρ', hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw hL hL₁ hρ
  have hx' : ∀ i, x i ^ (m ^ 2) = 1 := fun i => (hx _).2 ⟨i, rfl⟩
  obtain ⟨thP, hg, hth⟩ := GlobalTheory.T.exists_generator_thetaPoint_normalised_thetaConstants K P ρ' hρ' m Ix x v hx' hv
  let τ : (baseOver (Sp K)).left ⟶ (Over.mk x₀).left := 𝟙 (Sp K)
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp K)))
  have hτ : τ ≫ (Over.mk x₀).hom = (baseOver (Sp K)).hom ≫ x₀ := rfl
  have hi : inv τ = 𝟙 (Sp K) := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
  obtain ⟨th, hrel⟩ := exists_secRel_up hp τ hτ hw hL hL₁ thP
  refine ⟨th, ThetaPtUp.isGenSec_up hp τ hτ hw hL hL₁ hrel hg, fun F _ _ e x' h a th' hth' => ?_⟩
  choose y hy hy' using fun i => exists_torsion_up hp τ hτ (x i) (hx' i)
  have up : ∀ i, ThG G L ρ m th (y i) (fnOf (v i)) := fun i => by
    have q := ThG.up hp τ hτ hw hL hL₁ hr (hy i) (hy' i) hrel (hth i)
    rw [hi] at q
    exact q
  let T' : Over (Sp K) := Over.mk (spMap e)
  let u : T' ⟶ baseOver (Sp K) := Over.homMk (spMap e) (Category.comp_id _)
  let τ' : T'.left ⟶ (Over.mk x₀).left := spMap e
  have hτ' : τ' ≫ (Over.mk x₀).hom = T'.hom ≫ x₀ := rfl
  let σ : T'.left ⟶ (Over.mk x').left := 𝟙 (Sp F)
  haveI : IsIso σ := inferInstanceAs (IsIso (𝟙 (Sp F)))
  have hσ : σ ≫ (Over.mk x').hom = T'.hom ≫ x₀ := (Category.id_comp _).trans h.symm
  have hj : inv σ = 𝟙 (Sp F) := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
  obtain ⟨t, ht⟩ := exists_secRel hp τ' hτ' hw hL hL₁ th
  have hrel' := secRel_smul hp τ' hτ' σ hσ (Over.homMk (spMap e) h : Over.mk x' ⟶ Over.mk x₀)
    (Category.id_comp _) ht hth'
  have hu : ∀ i, (u ≫ x i) ^ (m ^ 2) = 1 := fun i => by rw [← MonObj.comp_pow, hx', MonObj.comp_one]
  have down : ∀ i, ThG P.A P.L ρ' m (SecM.toSec P.A (σ.appTop.hom (fnOf a) • SecM.ofSec P.A t)) (u ≫ x i)
      (fnOf (a * e (v i))) := fun i => by
    have e₁ : τ' ≫ (y i).left = (u ≫ x i).left ≫ φ :=
      (congrArg (spMap e ≫ ·) ((Category.id_comp _).symm.trans (hy i))).trans (Category.assoc _ _ _).symm
    have q := ThG.smul (th' := SecM.toSec P.A (σ.appTop.hom (fnOf a) • SecM.ofSec P.A t)) hL₁ rfl
      (ThG.move hp τ' hτ' hw hL hL₁ hr e₁ (hu i) ht (up i))
    have e₂ : σ.appTop.hom (fnOf a) * τ'.appTop.hom (fnOf (v i)) = fnOf (a * e (v i)) :=
      (congrArg (fnOf a * ·)
        (congrArg (fun q => q.hom (v i)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom e))).symm).trans
        (map_mul (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom _ _).symm
    rw [e₂] at q
    exact q
  have hK : ((m ^ 2 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hm.pos.ne')
  refine ⟨fun i => ?_, fun z c hz => ?_⟩
  · obtain ⟨z, hz, hz'⟩ := exists_torsion_up hp σ hσ _ (hu i)
    have q := ThG.up hp σ hσ hw hL hL₁ hr hz hz' hrel' (down i)
    rw [hj] at q
    exact ⟨z, q⟩
  · obtain ⟨z', hz₁, hz₂⟩ := exists_torsion_down hp σ hσ z hz.1
    obtain ⟨y', hy₁, rfl⟩ := TorsionFieldExt.exists_of_isAlgClosed hLaw P u hK
      (by rw [← map_natCast e]; exact (map_ne_zero e).2 hK) z' hz₂
    obtain ⟨i, rfl⟩ := (hx y').1 hy₁
    have hun : IsUnit ((m ^ 2 : ℕ) : Γ(Sp K, ⊤)) := by
      rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom]
      exact (IsUnit.mk0 _ hK).map _
    have q : fnOf c = fnOf (a * e (v i)) :=
      ThG.unique hLaw P hm hun (ThG.move hp σ hσ hw hL hL₁ hr hz₁ hz₂ hrel' hz) (down i)
    exact ⟨i, (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.injective q⟩

end GlobalTheory.Ex.OneGen
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_thetaConstants_over_algClosedExtensions : Laws → Laws2 → ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x₀ : Sp K ⟶ S) (P : PolAV (Sp K)) (φ : P.A.left ⟶ G.left), IsGrpPullback P.A G x₀ φ → LBIso P.L (L.pull φ) → ∀ (m : ℕ), Odd m → ∀ (Ix : Type) (x : Ix → (baseOver (Sp K) ⟶ P.A)) (v : Ix → K), (∀ y, y ^ (m ^ 2) = 1 ↔ ∃ i, x i = y) → IsThetaPt P m x (fun i => fnOf (v i)) → ∃ th : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x₀)), IsGenSec G L ((1 : ℕ) : ℤ) th ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] (e : K →+* F) (x' : Sp F ⟶ S) (h : spMap e ≫ x₀ = x') (a : F) (th' : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x'))), SecM.ofSec G th' = @id Γ((Over.mk x').left, ⊤) (fnOf a) • SecM.ofSec G (VVRank.pullS G _ (Over.homMk (spMap e) h : Over.mk x' ⟶ Over.mk x₀) th) → (∀ i, ∃ z, ThG G L ρ m th' z (fnOf (a * e (v i)))) ∧ ∀ z (c : F), ThG G L ρ m th' z (fnOf c) → ∃ i, c = a * e (v i) := by
  first | exact @GlobalTheory.Ex.OneGen.exists_gen_thG_generic | exact GlobalTheory.Ex.OneGen.exists_gen_thG_generic | (intros; apply GlobalTheory.Ex.OneGen.exists_gen_thG_generic <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam

noncomputable section
namespace GlobalTheory.Ex.OneGen

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

section Mod
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left}

def fnR {K : Type} [CommRing K] (x : Sp K ⟶ S) : K ≃+* Γ((Over.mk x).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm

def pl {K K' : Type} [CommRing K] [CommRing K'] (i : K →+* K') {x : Sp K ⟶ S} {x' : Sp K' ⟶ S} (h : spMap i ≫ x = x')
    (s : SecM G L ((1 : ℕ) : ℤ) (Over.mk x)) : SecM G L ((1 : ℕ) : ℤ) (Over.mk x') :=
  VVRank.pullM G L _ (Over.homMk (spMap i) h : Over.mk x' ⟶ Over.mk x) s

variable {K K' K'' : Type} [CommRing K] [CommRing K'] [CommRing K''] {x : Sp K ⟶ S} {x' : Sp K' ⟶ S} {x'' : Sp K'' ⟶ S}

theorem pl_smul (i : K →+* K') (h : spMap i ≫ x = x') (a : K) (s : SecM G L ((1 : ℕ) : ℤ) (Over.mk x)) :
    pl i h (fnR x a • s) = fnR x' (i a) • pl i h s := by
  refine ((VVRank.pullM G L _ (Over.homMk (spMap i) h : Over.mk x' ⟶ Over.mk x)).map_smulₛₗ _ _).trans
    (congrArg (· • pl i h s) ?_)
  exact (congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))).symm

theorem pl_ofSec (i : K →+* K') (h : spMap i ≫ x = x') (s : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x))) :
    pl i h (SecM.ofSec G s) =
      SecM.ofSec G (VVRank.pullS G _ (Over.homMk (spMap i) h : Over.mk x' ⟶ Over.mk x) s) := rfl

theorem ofSec_toSec {T : Over S} (f : SecM G L ((1 : ℕ) : ℤ) T) : SecM.ofSec G (SecM.toSec G f) = f := rfl

theorem pl_comp (hL : L.IsLB) (i : K →+* K') (j : K' →+* K'') (k : K →+* K'') (e : j.comp i = k) (h : spMap i ≫ x = x')
    (h' : spMap j ≫ x' = x'') (h'' : spMap k ≫ x = x'') (s : SecM G L ((1 : ℕ) : ℤ) (Over.mk x)) :
    pl j h' (pl i h s) = pl k h'' s := by
  subst e
  refine (VVRank.pullM_comp G hL _ _ _ s).trans (congrArg (fun q => VVRank.pullM G L _ q s) ?_)
  exact Over.OverMorphism.ext (sp_comp i j).symm

variable {e : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x))}

theorem UnivBasis.ex (he : UnivBasis G L x e) (i : K →+* K') (h : spMap i ≫ x = x')
    (s : SecM G L ((1 : ℕ) : ℤ) (Over.mk x')) : ∃ a : K', s = fnR x' a • pl i h (SecM.ofSec G e) := by
  obtain ⟨c, hc, -⟩ := he K' i x' h s
  obtain ⟨a, rfl⟩ := (fnR x').surjective c
  exact ⟨a, hc⟩

theorem UnivBasis.inj (he : UnivBasis G L x e) (i : K →+* K') (h : spMap i ≫ x = x') {a b : K'}
    (H : fnR x' a • pl i h (SecM.ofSec G e) = fnR x' b • pl i h (SecM.ofSec G e)) : a = b :=
  (fnR x').injective ((he K' i x' h _).unique rfl H)

theorem UnivBasis.smul_pull (hL : L.IsLB) (he : UnivBasis G L x e) (i : K →+* K') (h : spMap i ≫ x = x') {a : K'}
    (ha : IsUnit a) : UnivBasis G L x' (SecM.toSec G (fnR x' a • pl i h (SecM.ofSec G e))) := by
  intro K'' _ j x'' h' s
  have h'' : spMap (j.comp i) ≫ x = x'' := by rw [sp_comp, Category.assoc, h, h']
  obtain ⟨u, rfl⟩ := ha
  have E : ∀ c : K'', fnR x'' c • pl j h' (fnR x' u.val • pl i h (SecM.ofSec G e)) =
      fnR x'' (c * j u.val) • pl _ h'' (SecM.ofSec G e) := fun c => by
    rw [pl_smul, pl_comp hL i j _ rfl h h' h'', smul_smul, map_mul]
  obtain ⟨b, hb⟩ := he.ex _ h'' s
  refine ⟨fnR x'' (b * j u⁻¹.val), hb.trans (Eq.trans ?_ (E _).symm), fun c hc => ?_⟩
  · rw [_root_.mul_assoc, ← map_mul, u.inv_mul, map_one, _root_.mul_one]
  · obtain ⟨c, rfl⟩ := (fnR x'').surjective c
    rw [he.inj _ h'' (hb.symm.trans (hc.trans (E c))), _root_.mul_assoc, ← map_mul, u.mul_inv, map_one, _root_.mul_one]

theorem isGenSec_iff {T : Over S} (th : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)) : IsGenSec G L ((1 : ℕ) : ℤ) th ↔
    ∀ s : SecM G L ((1 : ℕ) : ℤ) T, ∃ r : Γ(T.left, ⊤), s = r • SecM.ofSec G th :=
  ⟨fun h s => (h (SecM.toSec G s)).imp fun _ hr => Subtype.ext (funext hr),
    fun h s => (h (SecM.ofSec G s)).imp fun _ hr j => congrArg (fun q => q.1 j) hr⟩

theorem UnivBasis.ne_zero [Nontrivial K'] (he : UnivBasis G L x e) (i : K →+* K') (h : spMap i ≫ x = x')
    {th : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x'))} (hth : IsGenSec G L ((1 : ℕ) : ℤ) th) {s : K'}
    (hs : SecM.ofSec G th = fnR x' s • pl i h (SecM.ofSec G e)) : s ≠ 0 := by
  rintro rfl
  obtain ⟨r, hr⟩ := (isGenSec_iff th).1 hth (pl i h (SecM.ofSec G e))
  refine one_ne_zero (he.inj i h (a := 1) (b := 0) ?_)
  rw [map_zero, zero_smul] at hs
  rw [hs, smul_zero] at hr
  rw [hr, smul_zero, smul_zero]

theorem UnivBasis.pl_ne_zero [Nontrivial K'] (he : UnivBasis G L x e) (i : K →+* K') (h : spMap i ≫ x = x') :
    pl i h (SecM.ofSec G e) ≠ 0 := fun h0 =>
  one_ne_zero (he.inj i h (a := 1) (b := 0) (by rw [h0, smul_zero, smul_zero]))

theorem isGenSec_unit (i : K →+* K') (h : spMap i ≫ x = x') (u : Kˣ)
    (H : IsGenSec G L ((1 : ℕ) : ℤ) (VVRank.pullS G _ (Over.homMk (spMap i) h : Over.mk x' ⟶ Over.mk x) e)) :
    IsGenSec G L ((1 : ℕ) : ℤ) (VVRank.pullS G _ (Over.homMk (spMap i) h : Over.mk x' ⟶ Over.mk x)
      (SecM.toSec G (fnR x u⁻¹.val • SecM.ofSec G e))) := by
  refine (isGenSec_iff _).2 fun s => ?_
  obtain ⟨r, hr⟩ := (isGenSec_iff _).1 H s
  refine ⟨r * fnR x' (i u.val), ?_⟩
  change s = _ • pl i h (fnR x u⁻¹.val • SecM.ofSec G e)
  rw [pl_smul, smul_smul, _root_.mul_assoc, ← map_mul, ← map_mul, u.mul_inv, map_one, map_one, _root_.mul_one]
  exact hr

theorem lin_of_pl (hL : L.IsLB) (i : K →+* K') (h : spMap i ≫ x = x') (s : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x')))
    (H : pl i h (SecM.ofSec G e) = SecM.ofSec G s) :
    GlobalTheory.LN.Lin G L 1 (Over.homMk (spMap i) h : Over.mk x' ⟶ Over.mk x) (fun _ : Fin 1 => e) (fun _ => 1) s :=
  (GlobalTheory.LN.PolFrames.lin_iff G L 1 _ hL (fun _ => VVRank.isPullSec_pullS G _ _ e) _ _).2 (by
    rw [Fin.sum_univ_one, one_smul]; exact H)

end Mod

theorem val_eq_zero {F I : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (a : F) (y : I → F) (h₁ : ∀ i, 0 ≤ v (y i))
    (h₂ : ∃ i, v (y i) = 0) (h₃ : ∀ i, 0 ≤ v (a * y i)) (h₄ : ∃ i, v (a * y i) = 0) : v a = 0 := by
  obtain ⟨i, hi⟩ := h₂
  obtain ⟨j, hj⟩ := h₄
  have e := h₃ i
  rw [AddValuation.map_mul, hi, add_zero] at e
  rw [AddValuation.map_mul] at hj
  exact le_antisymm (hj ▸ le_add_of_nonneg_right (h₁ j)) e

theorem exists_prime {O : Type} [CommRing O] [IsDomain O] {ϖ : O} (h : GlobalTheory.LN.ArcBase O ϖ) :
    ∃ n : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : O) := by
  have : IsLocalRing O := by
    rcases h with h | h
    · letI := h.1.toField; infer_instance
    · have := h.1; infer_instance
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one (a := ((3 : ℕ) : O) * 2) (b := ((5 : ℕ) : O) * (-1)) (by push_cast; ring) with
    h | h
  · exact ⟨3, by norm_num, by decide, isUnit_of_mul_isUnit_left h⟩
  · exact ⟨5, by norm_num, by decide, isUnit_of_mul_isUnit_left h⟩

set_option maxHeartbeats 800000 in

theorem basis_at_trait (hV : HV) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}
    (t : SAB H S) {K₂ K : Type} [Field K₂] [Field K] (e : K₂ →+* K) {x₂ : Sp K₂ ⟶ S} {x₀ : Sp K ⟶ S}
    (he : spMap e ≫ x₂ = x₀) {θ : LB.Sec (LPow t.G t.PP.L ((1 : ℕ) : ℤ) (Over.mk x₂))} (hθ : UnivBasis t.G t.PP.L x₂ θ)
    (hext : ∀ (F : Type) [Field F] [IsAlgClosed F] (g : K₂ →+* F), ∃ g' : K →+* F, g'.comp e = g)
    {th : LB.Sec (LPow t.G t.PP.L ((1 : ℕ) : ℤ) (Over.mk x₀))} (eth : pl e he (SecM.ofSec t.G θ) = SecM.ofSec t.G th)
    {m : ℕ} (hm : Odd m) (h3 : 3 ≤ m) {I : Type} (y : I → K)
    (hy : ∀ (F : Type) [Field F] [IsAlgClosed F] (g : K →+* F) (x' : Sp F ⟶ S) (h : spMap g ≫ x₀ = x') (a : F)
      (th' : LB.Sec (LPow t.G t.PP.L ((1 : ℕ) : ℤ) (Over.mk x'))),
      SecM.ofSec t.G th' = @id Γ((Over.mk x').left, ⊤) (fnOf a) •
        SecM.ofSec t.G (VVRank.pullS t.G _ (Over.homMk (spMap g) h : Over.mk x' ⟶ Over.mk x₀) th) →
      (∀ i, ∃ z, ThG t.G t.PP.L t.PP.rig m th' z (fnOf (a * g (y i)))) ∧
        ∀ z (c : F), ThG t.G t.PP.L t.PP.rig m th' z (fnOf c) → ∃ i, c = a * g (y i))
    {R : Type} (a₂ : R → K₂) (hint : ∀ A : ValuationSubring K, (∀ r, e (a₂ r) ∈ A) → (∀ i, y i ∈ A) ∧ ∃ i, A.valuation (y i) = 1)
    {W W' : Type} [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing W'] [IsDomain W'] [IsLocalRing W']
    (hW : GlobalTheory.LN.CDvr W) (hW' : GlobalTheory.LN.CDvr W') (io : W →+* W') (hi : Function.Injective io) (hf : io.Finite)
    (hu : IsUnit (m : W)) (gam : K₂ →+* FractionRing W) (hg : ∀ r, ∃ w, gam (a₂ r) = algebraMap W _ w) (χ : Sp W ⟶ S)
    (hχ : spMap gam ≫ x₂ = jK W ≫ χ) {t₁ : SAB H (Sp W)} (m₁ : SABMap t₁ t χ) (hp : GlobalTheory.LN.PolAt t₁ (jK W))
    {t' : SAB H (Sp W')} (m' : SABMap t' t (spMap io ≫ χ)) (P : PELUnif (maximalIdeal W') t') :
    ∃ b : LB.Sec (LPow t.G t.PP.L ((1 : ℕ) : ℤ) (Over.mk χ)),
      GlobalTheory.LN.BasisAlong t.G t.PP.L 1 (𝟙 (Over.mk χ)) (fun _ : Fin 1 => b) ∧
      pl (algebraMap W (FractionRing W)) (x' := jK W ≫ χ) rfl (SecM.ofSec t.G b) = pl gam hχ (SecM.ofSec t.G θ) := by
  have hL := t.PP.isLB
  have := hW.1
  have := hW'.1
  have := t.semi.smooth
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_nz_of_polAt' hV.1.1 hV.1.2.1 E H S t W χ t₁ m₁ hp
  obtain ⟨hgen, hval⟩ := GlobalTheory.T.theta_constants_at_uniformised_trait hV E H S t W' hW' _ t' m' P _ (hσ W' io _ rfl)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W'
  let F := AlgebraicClosure (FractionRing W')
  obtain ⟨v, hv⟩ := GlobalTheory.adic_base_embeds_valuation_algebraic_closure.2 W' ϖ hϖ
  obtain ⟨hpos, ⟨io', hio', hun⟩, hA⟩ := GlobalTheory.T.valuation_over_finite_dvr_extension W W' io hi hf ϖ hϖ F v hv
  let j : FractionRing W →+* F := (algebraMap (FractionRing W') F).comp io'
  let k : W' →+* F := (algebraMap (FractionRing W') F).comp (algebraMap W' _)
  obtain ⟨g, hge⟩ := hext F (j.comp gam)
  obtain ⟨A, hA⟩ := hA K g
  obtain ⟨hy₁, hy₂⟩ := hint A fun r => (hA _).1.2 (by
    obtain ⟨w, hw⟩ := hg r
    rw [← RingHom.comp_apply, hge, RingHom.comp_apply, hw]
    exact (congrArg (fun q => 0 ≤ v (algebraMap _ F q)) (hio' w)).mpr (hpos _))
  have ejk : j.comp (algebraMap W _) = k.comp io := RingHom.ext fun w => congrArg (algebraMap _ F) (hio' w)
  have h₁ : spMap j ≫ jK W ≫ χ = spMap g ≫ x₀ := by
    rw [← hχ, ← he, ← Category.assoc, ← Category.assoc, ← sp_comp, ← sp_comp, hge]
  have h₂ : spMap (k.comp io) ≫ χ = spMap g ≫ x₀ := by rw [← ejk, sp_comp, Category.assoc]; exact h₁
  have h₃ : spMap k ≫ spMap io ≫ χ = spMap g ≫ x₀ := by rw [← Category.assoc, ← sp_comp, h₂]
  have h₄ : spMap (j.comp gam) ≫ x₂ = spMap g ≫ x₀ := by rw [sp_comp, Category.assoc, hχ, h₁]
  obtain ⟨a, ha⟩ := hθ.ex gam hχ (pl (algebraMap W (FractionRing W)) (x' := jK W ≫ χ) rfl (SecM.ofSec t.G σ))
  have hF : pl k h₃ (pl io rfl (SecM.ofSec t.G σ)) = fnR (spMap g ≫ x₀) (j a) • pl g rfl (pl e he (SecM.ofSec t.G θ)) := by
    rw [pl_comp hL io k _ rfl rfl h₃ h₂, ← pl_comp hL _ j _ ejk (x' := jK W ≫ χ) rfl h₁ h₂, ha, pl_smul,
      pl_comp hL gam j _ rfl hχ h₁ h₄, pl_comp hL e g _ hge he rfl h₄]
  rw [pl_ofSec io, pl_ofSec k, eth, pl_ofSec g] at hF
  obtain ⟨q₁, q₂⟩ := hy F g _ rfl (j a) _ hF
  obtain ⟨p₁, z, c, p₂, p₃⟩ := hval ϖ hϖ F v hv m hm (by simpa using hu.map io) h3 _
    (Over.homMk (spMap k) h₃ : Over.mk (spMap g ≫ x₀) ⟶ Over.mk (spMap io ≫ χ)) (sp_comp _ _)
  obtain ⟨u, hu'⟩ := hun a (val_eq_zero v (j a) (fun i => g (y i)) (fun i => (hA _).1.1 (hy₁ i))
    (hy₂.imp fun i hi => (hA _).2 hi) (fun i => (q₁ i).elim fun z hz => p₁ z _ hz)
    ((q₂ z c p₂).elim fun i hi => ⟨i, (congrArg v hi).symm.trans p₃⟩))
  have hb : pl (algebraMap W (FractionRing W)) (x' := jK W ≫ χ) rfl (fnR χ u⁻¹.val • SecM.ofSec t.G σ) =
      pl gam hχ (SecM.ofSec t.G θ) := by
    rw [pl_smul, ha, smul_smul, ← map_mul, ← hu', ← map_mul, u.inv_mul, map_one, map_one, one_smul]
  exact ⟨SecM.toSec _ (fnR χ u⁻¹.val • SecM.ofSec t.G σ), GlobalTheory.T.generatingSection_finite_ext_normal_domain_isBasis S t.G t.PP.L hL W W' io hi hf χ _
    (isGenSec_unit io rfl u hgen) ⟨_, hθ.smul_pull hL gam hχ isUnit_one⟩
    (fun h0 => hθ.pl_ne_zero gam hχ (hb.symm.trans h0)), hb⟩

theorem exists_unif (hU : GlobalTheory.LN.UDvrSt) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b} {R₁ : Type} [CommRing R₁] [IsDomain R₁]
    {g : PowerSeries O' →+* R₁} {y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c} (hT : GlobalTheory.LN.TraitData Y a g y₁)
    {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (hW : GlobalTheory.LN.CDvr W) (ψ : R₁ →+* W)
    (gam : FractionRing R₁ →+* FractionRing W) (hg : ∀ r, gam (algebraMap R₁ _ r) = algebraMap W _ (ψ r))
    (χ : Sp W ⟶ Y.X) (hχ : spMap gam ≫ y₁ ≫ Y.j = jK W ≫ χ) :
    (∃ (t₁ : SAB H (Sp W)) (_ : SABMap t₁ Y.t χ), GlobalTheory.LN.PolAt t₁ (jK W)) ∧
    ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W')
      (io : W →+* W'), GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ ∃ (t' : SAB H (Sp W'))
      (_ : SABMap t' Y.t (spMap io ≫ χ)), Nonempty (PELUnif (maximalIdeal W') t') := by
  obtain ⟨t₁, ⟨m₁⟩⟩ := GlobalTheory.ArcData.exists_sab χ Y.t
  have hp₁ := GlobalTheory.ArcData.polAt_of_point Y m₁ (jK W) (spMap gam ≫ y₁) ((Category.assoc _ _ _).trans hχ)
  have T := hT.2 W hW ψ gam hg χ hχ
  refine ⟨⟨t₁, m₁, hp₁⟩, ?_⟩
  by_cases hu : IsUnit (ψ (g PowerSeries.X))
  · have e₀ : spMap (RingHom.id W) ≫ χ = χ := (congrArg (· ≫ χ) (Spec.map_id _)).trans (Category.id_comp _)
    exact ⟨W, inferInstance, inferInstance, inferInstance, RingHom.id W, hW, fun _ _ h => h, RingHom.Finite.id W, t₁,
      e₀.symm ▸ m₁, GlobalTheory.T.nonempty_uniformisation_trait_in_abelianLocus hU E H _ Y.t W hW χ t₁ m₁ hp₁ (T.1 hu)⟩
  · obtain ⟨W', _, _, _, io, hW', hi, hf, t', m', P, -⟩ := T.2 hu
    exact ⟨W', _, _, _, io, hW', hi, hf, t', m', ⟨P⟩⟩

set_option maxHeartbeats 800000 in

theorem main : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c), Function.Injective g → g.Finite → IsIntegrallyClosed R₁ → GlobalTheory.LN.TraitData Y a g y₁ → ThetaInt Y g y₁ → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (h : R₁ →+* R₂) (h' : FractionRing R₁ →+* FractionRing R₂), Function.Injective h ∧ h.Finite ∧ IsIntegrallyClosed R₂ ∧ (∀ r, h' (algebraMap R₁ _ r) = algebraMap R₂ _ (h r)) ∧ ∃ θ, GlobalTheory.LN.IsFrame Y.t.G Y.t.PP.L 1 ((spMap h' ≫ y₁) ≫ Y.j) (fun _ : Fin 1 => θ) := by
  intro hV _ hU _ _ _ _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hϖ R₁ _ _ g y₁ hg hfin hn hT ⟨o, ⟨φ, hp, hw, _⟩, hθ⟩
  have hL := Y.t.PP.isLB
  obtain ⟨n, hn₁, hn₂, hn₃⟩ := exists_prime hϖ
  have h3 : 3 ≤ n ^ 1 := by
    have := hn₁.two_le
    obtain ⟨k, rfl⟩ := hn₂
    rw [pow_one]
    omega
  obtain ⟨v, hv, hint⟩ := hθ n 1 hn₁ hn₂ hn₃ le_rfl
  have : IsNoetherianRing O' := by
    rcases hϖ with h | h
    · letI := h.1.toField; infer_instance
    · have := h.1; infer_instance
  have : IsNoetherianRing R₁ := by
    letI := g.toAlgebra
    have : Module.Finite (PowerSeries O') R₁ := hfin
    exact IsNoetherianRing.of_finite (PowerSeries O') R₁
  have : CharZero (PowerSeries O') := (RingHom.charZero_iff (PowerSeries.C_injective (R := O'))).1 ‹_›
  have : CharZero R₁ := (RingHom.charZero_iff hg).1 ‹_›
  have := o.charZero
  have hw₀ : LBIso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ) := Y.m.lin.imp fun _ h => h.1
  have hw' : LBIso o.P.L (Y.t.PP.L.pull (φ ≫ Y.m.φ)) :=
    LBIso.trans o.P.isLB (LB.isLB_pull Y.oF.t.PP.isLB _) (LB.isLB_pull hL _) hw
      (LBIso.chartPull (Geo.Tor.chartPullPull _ φ φ rfl) (chartPullSame _ _ _ _ φ fun _ => rfl) hw₀)
  obtain ⟨th, hth, hy⟩ := GlobalTheory.T.exists_generator_thetaConstants_over_algClosedExtensions hV.1.1 hV.1.2.1 _ Y.t.G Y.t.PP.L Y.t.PP.rig hL Y.t.PP.rigGen _ _ o.P _
    (hp.comp Y.m.cart) hw' (n ^ 1) hn₂.pow _ _ v (o.I.onto _ (by positivity)) hv
  obtain ⟨e₁, he₁⟩ := GlobalTheory.T.exists_universal_section_basis_polarised_fibre hV.1.2.1 _ _ Y.t.G Y.t.PP.L hL (objPolAV Y.oF) Y.j Y.m.φ Y.m.cart hw₀ _ y₁ _ rfl
  have hx₀ : spMap (algebraMap (FractionRing R₁) (AlgebraicClosure (FractionRing R₁))) ≫ y₁ ≫ Y.j =
      (spMap (algebraMap _ _) ≫ y₁) ≫ Y.j := (Category.assoc _ _ _).symm
  obtain ⟨s, hs⟩ := he₁.ex _ hx₀ (SecM.ofSec _ th)
  have hs₀ : s ≠ 0 := he₁.ne_zero _ hx₀ hth hs
  obtain ⟨R₂, _, _, h, h', e, i₁, i₂, i₃, hh, heh, ⟨s₂, rfl⟩, hext⟩ := GlobalTheory.T.exists_integrally_closed_extension_of_adjoin R₁ s
  have hx₂ : spMap h' ≫ y₁ ≫ Y.j = (spMap h' ≫ y₁) ≫ Y.j := (Category.assoc _ _ _).symm
  have he : spMap e ≫ (spMap h' ≫ y₁) ≫ Y.j = (spMap (algebraMap (FractionRing R₁) _) ≫ y₁) ≫ Y.j := by
    rw [← heh, sp_comp]; simp only [Category.assoc]
  have hb := he₁.smul_pull hL h' hx₂ (a := s₂) (IsUnit.mk0 _ fun h0 => hs₀ (by rw [h0, map_zero]))
  have eth : pl e he (fnR ((spMap h' ≫ y₁) ≫ Y.j) s₂ • pl h' hx₂ (SecM.ofSec _ e₁)) = SecM.ofSec _ th := by
    rw [pl_smul, pl_comp hL h' e _ heh hx₂ he hx₀]
    exact hs.symm
  obtain ⟨θ, hb, eth⟩ : ∃ θ, UnivBasis Y.t.G Y.t.PP.L ((spMap h' ≫ y₁) ≫ Y.j) θ ∧
      pl e he (SecM.ofSec _ θ) = SecM.ofSec _ th := ⟨_, hb, (congrArg (pl e he) (ofSec_toSec _)).trans eth⟩
  refine ⟨R₂, inferInstance, inferInstance, h, h', i₁, i₂, i₃, hh, θ, fun W _ _ _ hW ψ gam hgam χ hχ => ?_⟩
  have hχ' : spMap (gam.comp h') ≫ y₁ ≫ Y.j = jK W ≫ χ := by rw [sp_comp, Category.assoc, hx₂, hχ]
  obtain ⟨⟨t₁, m₁, hp₁⟩, W', _, _, _, io, hW', hi, hf, t', m', ⟨P⟩⟩ := exists_unif hU Y hT hW (ψ.comp h) (gam.comp h')
    (fun r => (congrArg gam (hh r)).trans (hgam _)) χ hχ'
  have hint' : ∀ A : ValuationSubring (AlgebraicClosure (FractionRing R₁)), (∀ r : R₁, e (h' (algebraMap R₁ _ r)) ∈ A) →
      (∀ i, v i ∈ A) ∧ ∃ i, A.valuation (v i) = 1 := fun A hA =>
    (hint A fun r => (congrArg (· ∈ A) (RingHom.congr_fun heh (algebraMap R₁ _ r))).mp (hA r)).imp_right fun h => h.1
  have hu : IsUnit ((n ^ 1 : ℕ) : W) := by
    have := hn₃.map (ψ.comp (h.comp (g.comp (PowerSeries.C (R := O')))))
    rwa [map_natCast, ← pow_one n] at this
  have hg' : ∀ r : R₁, ∃ w, gam (h' (algebraMap R₁ _ r)) = algebraMap W _ w :=
    fun r => ⟨_, (congrArg gam (hh r)).trans (hgam _)⟩
  obtain ⟨b', hb₁, hb₂⟩ := basis_at_trait hV Y.t e he hb hext eth hn₂.pow h3 v hy
    (fun r : R₁ => h' (algebraMap R₁ _ r)) hint' hW hW' io hi hf hu gam hg' χ hχ m₁ hp₁ m' P
  exact ⟨fun _ => b', hb₁, fun _ => ⟨SecM.toSec _ (pl gam hχ (SecM.ofSec _ θ)), lin_of_pl hL gam hχ _ (ofSec_toSec _).symm,
    lin_of_pl hL (algebraMap W _) rfl _ (hb₂.trans (ofSec_toSec _).symm)⟩⟩

end GlobalTheory.Ex.OneGen
end
end
