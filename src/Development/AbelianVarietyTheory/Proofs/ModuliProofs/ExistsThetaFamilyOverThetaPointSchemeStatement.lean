import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftClosedImmersionOfDense
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullbackStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullbackStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnitStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasThStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyFromVeryDensePointsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescentStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DescendToThetaConstantField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapeOfGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoGenericSpreadsOut
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsAffineOpenPreimageBasicOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBasicOpenKTrivOfFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianSchemeAway
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoExtendOfNormalBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelEndomorphismsSpreadOverBasicOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaConstantsLocallyOnBaseStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenericObjectMinimalPrimeModuliChartStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCoverStatement

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace GenericLB

theorem algHom_eq_val {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Subalgebra R K) (u : S →ₐ[R] K) (x : S) : u x = x := by
  obtain ⟨⟨a, b⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors R) (x : K)
  have hb : algebraMap R K (b : R) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hS : x * algebraMap R S (b : R) = algebraMap R S a := by
    apply Subtype.ext
    simpa using hx
  have hu : u x * algebraMap R K (b : R) = algebraMap R K a := by
    simpa only [map_mul, AlgHom.commutes] using congrArg u hS
  exact mul_right_cancel₀ hb (hu.trans hx.symm)

theorem mono_fst_localization {R : Type} [CommRing R] (M : Submonoid R) (A : Type) [CommRing A] [Algebra R A]
    [IsLocalization M A] {B : Scheme.{0}} (pB : B ⟶ Sp R) :
    Mono (pullback.fst pB (spMap (algebraMap R A))) := by
  haveI hepi : Epi (CommRingCat.ofHom (algebraMap R A)) :=
    ⟨fun g h e => CommRingCat.hom_ext (IsLocalization.ringHom_ext M (by
      simpa using congrArg CommRingCat.Hom.hom e))⟩
  haveI hsp : Mono (spMap (algebraMap R A)) :=
    (inferInstance : Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R A)).op))
  infer_instance

end GenericLB

theorem lb_generic_spreads_out : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (B : Scheme.{0}) (pB : B ⟶ Sp R) (M : LB (pullback pB (spMap (algebraMap R K)))), QuasiCompact pB → QuasiSeparated pB → M.IsLB → ∃ (f : R) (_ : f ≠ 0) (M' : LB (pullback pB (spMap (algebraMap R (Localization.Away f))))), M'.IsLB ∧ ∀ j : pullback pB (spMap (algebraMap R K)) ⟶ pullback pB (spMap (algebraMap R (Localization.Away f))), j ≫ pullback.fst _ _ = pullback.fst _ _ → LBIso M (M'.pull j) := by
  intro R K _ _ _ _ _ _ B pB M hqc hqs hM
  classical
  haveI := hqc
  haveI := hqs
  obtain ⟨s, M₀, hM₀, -, hfac⟩ := LBLimit.exists_lb_of_isLimit (Spread.bcDiagram pB K)
    (fun i => (Spread.bcCone pB K).π.app i) (fun g => (Spread.bcCone pB K).w g)
    (Spread.isLimitBcCone pB K) M hM
  obtain ⟨f, hf0, hlift⟩ := GenericLB.exists_denom (R := R) (K := K) s.unop
  obtain ⟨ψ, hψ⟩ := hlift (Localization.Away f) (algebraMap R (Localization.Away f))
    (IsLocalization.Away.algebraMap_isUnit f)
  let ψa : Algebra.adjoin R (s.unop : Set K) →ₐ[R] Localization.Away f :=
    { ψ with commutes' := fun r => RingHom.congr_fun hψ r }
  refine ⟨f, hf0, M₀.pull (Spread.bcMap pB ψa), pull_isLB hM₀ _, fun jm hjm => ?_⟩
  have hfK : IsUnit (algebraMap R K f) :=
    isUnit_iff_ne_zero.mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hf0))
  let χ : Localization.Away f →ₐ[R] K :=
    { IsLocalization.Away.lift f hfK with
      commutes' := fun r => IsLocalization.lift_eq _ r }
  haveI := GenericLB.mono_fst_localization (Submonoid.powers f) (Localization.Away f) pB
  have hj : jm = Spread.bcMap pB χ := by
    rw [← cancel_mono (pullback.fst pB (spMap (algebraMap R (Localization.Away f)))), hjm,
      Spread.bcMap_fst]
  have hcomp : jm ≫ Spread.bcMap pB ψa = (Spread.bcCone pB K).π.app s := by
    rw [hj, Spread.bcMap_comp]
    show _ = Spread.bcMap pB (Algebra.adjoin R (s.unop : Set K)).val
    congr 1
    exact AlgHom.ext fun x => GenericLB.algHom_eq_val _ _ x
  exact hfac _ jm (Spread.bcMap pB ψa) hcomp

end GlobalTheory
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_generic_fibre_spreads_out : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (B : Scheme.{0}) (pB : B ⟶ Sp R) (M : LB (pullback pB (spMap (algebraMap R K)))), QuasiCompact pB → QuasiSeparated pB → M.IsLB → ∃ (f : R) (_ : f ≠ 0) (M' : LB (pullback pB (spMap (algebraMap R (Localization.Away f))))), M'.IsLB ∧ ∀ j : pullback pB (spMap (algebraMap R K)) ⟶ pullback pB (spMap (algebraMap R (Localization.Away f))), j ≫ pullback.fst _ _ = pullback.fst _ _ → LBIso M (M'.pull j) := by
  atlas_forward_decl GlobalTheory.lb_generic_spreads_out
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PolSpread

set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K]

def Spreads (R : Type) [CommRing R] [Algebra R K] (T : ∀ (R' : Type) [CommRing R'], (R' →+* K) → Prop) : Prop :=
  ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R') (ψ : R' →+* K), IsUnit (g f) →
    ψ.comp g = algebraMap R K → T R' ψ

section Shrink

variable {R : Type} [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] in
theorem isUnit_algebraMap {f : R} (hf : f ≠ 0) : IsUnit (algebraMap R K f) :=
  (IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hf))

omit [IsDomain R] [IsFractionRing R K] in

theorem exists_factor {f : R} {ψ₀ : Localization.Away f →+* K} (h₀ : ψ₀.comp (algebraMap R _) = algebraMap R K)
    {R' : Type} [CommRing R'] {g : R →+* R'} {ψ : R' →+* K} (hg : IsUnit (g f)) (h : ψ.comp g = algebraMap R K) :
    ∃ g₁ : Localization.Away f →+* R', g₁.comp (algebraMap R _) = g ∧ ψ.comp g₁ = ψ₀ := by
  refine ⟨IsLocalization.Away.lift f hg, IsLocalization.Away.lift_comp f hg, ?_⟩
  refine IsLocalization.ringHom_ext (Submonoid.powers f) ?_
  rw [RingHom.comp_assoc, IsLocalization.Away.lift_comp, h, h₀]

theorem Spreads.step [IsNoetherianRing R] {T T' : ∀ (R' : Type) [CommRing R'], (R' →+* K) → Prop}
    (h : Spreads R T)
    (H : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsNoetherianRing R₁] [Algebra R₁ K] [IsFractionRing R₁ K],
      T R₁ (algebraMap R₁ K) → Spreads R₁ T') : Spreads R T' := by
  obtain ⟨f, hf, h⟩ := h
  have hp : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  let ψ₀ : Localization.Away f →+* K := IsLocalization.Away.lift f (isUnit_algebraMap hf)
  have h₀ : ψ₀.comp (algebraMap R _) = algebraMap R K := IsLocalization.Away.lift_comp f _
  letI : Algebra (Localization.Away f) K := ψ₀.toAlgebra
  haveI : IsScalarTower R (Localization.Away f) K := IsScalarTower.of_algebraMap_eq' h₀.symm
  haveI : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hp
  haveI : IsFractionRing (Localization.Away f) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f) _ K
  obtain ⟨f', hf', h'⟩ := H (Localization.Away f)
    (h _ (algebraMap R _) ψ₀ (IsLocalization.Away.algebraMap_isUnit f) h₀)
  obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj (Submonoid.powers f) f'
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at e
    exact hf' ((IsLocalization.map_units (Localization.Away f) s).mul_left_eq_zero.1 e)
  refine ⟨f * a, mul_ne_zero hf ha, fun R' _ g ψ hg hψ => ?_⟩
  rw [map_mul] at hg
  obtain ⟨g₁, e₁, e₂⟩ := exists_factor h₀ (isUnit_of_mul_isUnit_left hg) hψ
  refine h' R' g₁ ψ ?_ e₂
  have : g₁ f' * g₁ (algebraMap R _ s) = g a := by
    rw [← map_mul, e, ← e₁]; rfl
  exact isUnit_of_mul_isUnit_left (this ▸ isUnit_of_mul_isUnit_right hg)

end Shrink

variable (P : Out.PolAV (Sp K))

def GrpModel {R : Type} [CommRing R] (ψ : R →+* K) (A : Over (Sp R)) [GrpObj A] (φ : P.A.left ⟶ A.left) : Prop :=
  IsAbelianScheme A ∧ SmoothOfRelativeDimension P.g A.hom ∧ IsGrpPullback P.A A (spMap ψ) φ

variable {P}

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (g : R →+* R') (ψ : R' →+* R'') :
    spMap (ψ.comp g) = spMap ψ ≫ spMap g := by
  rw [← Spec.map_comp]; rfl

theorem GrpModel.baseChange {R R' : Type} [CommRing R] [CommRing R'] {ψ₀ : R →+* K} {A : Over (Sp R)} [GrpObj A]
    {φ : P.A.left ⟶ A.left} (h : GrpModel P ψ₀ A φ) {g : R →+* R'} {ψ : R' →+* K} (e : ψ.comp g = ψ₀) :
    ∃ φ' : P.A.left ⟶ ((Over.pullback (spMap g)).obj A).left,
      φ' ≫ pullback.fst A.hom (spMap g) = φ ∧ GrpModel P ψ ((Over.pullback (spMap g)).obj A) φ' := by
  obtain ⟨hA, hs, hp⟩ := h
  have e' : spMap ψ₀ = spMap ψ ≫ spMap g := by rw [← e, spMap_comp]
  have w : φ ≫ A.hom = (P.A.hom ≫ spMap ψ) ≫ spMap g := by rw [hp.1.w, e', Category.assoc]
  have hb := isGrpPullback_pullback A (spMap g)
  refine ⟨pullback.lift φ _ w, pullback.lift_fst _ _ _, PolPull.isAbelianScheme_of_isGrpPullback hA hb,
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hb.1 hs, ?_⟩
  exact hb.cancel (hp.congr e' (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)

theorem lbIso_baseChange {X Y Z : Scheme.{0}} {M : LB Z} {L : LB X} (hM : M.IsLB) (hL : L.IsLB) {φ : Z ⟶ X}
    {φ' : Z ⟶ Y} {π : Y ⟶ X} (e : φ' ≫ π = φ) (h : LBIso M (L.pull φ)) : LBIso M ((L.pull π).pull φ') :=
  LBIso.trans hM (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) h (GenSpread.lbIso_pull_pull hL φ' e.symm)

variable (P)

def HasGrp (R : Type) [CommRing R] (ψ : R →+* K) : Prop :=
  ∃ (A : Over (Sp R)) (_ : GrpObj A) (φ : P.A.left ⟶ A.left), GrpModel P ψ A φ

def HasLB (R : Type) [CommRing R] (ψ : R →+* K) : Prop :=
  ∃ (A : Over (Sp R)) (_ : GrpObj A) (φ : P.A.left ⟶ A.left) (L : LB A.left),
    GrpModel P ψ A φ ∧ L.IsLB ∧ LBIso P.L (L.pull φ)

def HasAmple (R : Type) [CommRing R] (ψ : R →+* K) : Prop :=
  ∃ (A : Over (Sp R)) (_ : GrpObj A) (φ : P.A.left ⟶ A.left) (L : LB A.left),
    GrpModel P ψ A φ ∧ L.IsLB ∧ LBIso P.L (L.pull φ) ∧ Out.RelAmple A L

def HasPol (R : Type) [CommRing R] (ψ : R →+* K) : Prop :=
  ∃ (P' : Out.PolAV (Sp R)) (φ : P.A.left ⟶ P'.A.left),
    P'.g = P.g ∧ IsGrpPullback P.A P'.A (spMap ψ) φ ∧ LBIso P.L (P'.L.pull φ)

variable (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Algebra R K] [IsFractionRing R K]

theorem spreads_grp : Spreads R (HasGrp P) := by
  obtain ⟨f, hf, ψ₀, A, _, φ, h₀, h⟩ := GlobalTheory.SpreadAb.exists_abelianScheme_away R K P
  refine ⟨f, hf, fun R' _ g ψ hg hψ => ?_⟩
  obtain ⟨g₁, -, e₂⟩ := exists_factor h₀ hg hψ
  obtain ⟨φ', -, h'⟩ := GrpModel.baseChange (P := P) h e₂
  exact ⟨_, _, φ', h'⟩

theorem spreads_lb (h : HasGrp P R (algebraMap R K)) : Spreads R (HasLB P) := by
  obtain ⟨A, _, φ, h⟩ := h
  have := h.1.proper
  let i := h.2.2.1.isoPullback
  obtain ⟨f, hf, M, hM, H⟩ := GlobalTheory.T.lineBundle_generic_fibre_spreads_out R K A.left A.hom (P.L.pull i.inv) inferInstance inferInstance
    (pull_isLB P.isLB _)
  let ψ₀ : Localization.Away f →+* K := IsLocalization.Away.lift f (isUnit_algebraMap hf)
  have h₀ : ψ₀.comp (algebraMap R _) = algebraMap R K := IsLocalization.Away.lift_comp f _
  obtain ⟨φ₁, e₁, h₁⟩ := h.baseChange h₀
  have H₁ := H (i.inv ≫ φ₁) (by
    rw [Category.assoc]
    exact (congrArg (i.inv ≫ ·) e₁).trans (h.2.2.1.isoPullback_inv_fst))
  have H₂ : LBIso P.L (M.pull φ₁) := by
    have a := (CechPic.cls_eq_iff (pull_isLB P.isLB _) (pull_isLB hM _)).2 H₁
    refine (CechPic.cls_eq_iff P.isLB (pull_isLB hM _)).1 ?_
    have b := congrArg (CechPic.pull i.hom) a
    rw [CechPic.cls_pull P.isLB, CechPic.cls_pull hM, ← CechPic.pull_comp, ← CechPic.pull_comp, i.hom_inv_id,
      CechPic.pull_id, i.hom_inv_id_assoc] at b
    exact b
  refine ⟨f, hf, fun R' _ g ψ hg hψ => ?_⟩
  obtain ⟨g₁, -, e₂⟩ := exists_factor h₀ hg hψ
  obtain ⟨φ', e', h'⟩ := h₁.baseChange e₂
  exact ⟨_, _, φ', M.pull (pullback.fst _ _), h', pull_isLB hM _, lbIso_baseChange P.isLB hM e' H₂⟩

theorem spreads_ample (h : HasLB P R (algebraMap R K)) : Spreads R (HasAmple P) := by
  obtain ⟨A, _, φ, L, h, hL, e⟩ := h
  have := h.1.proper
  let i := h.2.2.1.isoPullback
  have hi : IsPullback i.inv (pullback.snd A.hom (spMap (algebraMap R K))) P.A.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact h.2.2.1.isoPullback_inv_snd⟩
  obtain ⟨w, hw⟩ := (GenSpread.lbIso_pull_of_lbIso e i.inv h.2.2.1.isoPullback_inv_fst.symm).symm
  obtain ⟨f, hf, H⟩ := GlobalTheory.AmpleSpread.relAmple_spread R K A L inferInstance hL
    (relAmple_pull (A' := Over.mk (pullback.snd A.hom (spMap (algebraMap R K)))) hi P.isLB (pull_isLB hL _)
      ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) P.ample)
  refine ⟨f, hf, fun R' _ g ψ hg hψ => ?_⟩
  obtain ⟨φ', e', h'⟩ := h.baseChange hψ
  exact ⟨_, _, φ', L.pull (pullback.fst _ _), h', pull_isLB hL _, lbIso_baseChange P.isLB hL e' e, H R' g hg⟩

omit [IsDomain R] [IsNoetherianRing R] [Algebra R K] [IsFractionRing R K] in

theorem cls_inv : CechPic.pull (GrpObj.inv : P.A ⟶ P.A).left (CechPic.cls P.L P.isLB) = CechPic.cls P.L P.isLB := by
  obtain ⟨U, hU, ht⟩ := P.sym (default : PrimeSpectrum K)
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain rfl : U = ⊤ := top_le_iff.1 fun y _ => by rwa [Subsingleton.elim y (default : PrimeSpectrum K)]
  have a := (CechPic.cls_eq_zero_iff (LB.isLB_linComb P.isLB _ _)).2 ht
  rw [CechPic.cls_linComb P.isLB, Fin.sum_univ_two] at a
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, Matrix.cons_val_fin_one] at a
  have hj : ∃ j : P.A.left ⟶ (P.A.hom ⁻¹ᵁ ⊤).toScheme, j ≫ (P.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨P.A.left.topIso.inv, P.A.left.toIso_inv_ι⟩
  obtain ⟨j, c⟩ := hj
  have b := congrArg (CechPic.pull j) (add_neg_eq_zero.1 a)
  rwa [← CechPic.pull_comp, ← CechPic.pull_comp, ← Category.assoc, c, Category.id_comp, CechPic.pull_id] at b

theorem sym_of_cls {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    (h : CechPic.pull (GrpObj.inv : A ⟶ A).left (CechPic.cls L hL) = CechPic.cls L hL) : Out.Sym A L := by
  refine fun s => ⟨⊤, trivial, (CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_⟩
  rw [CechPic.cls_linComb hL, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, CechPic.pull_comp, h,
    Matrix.cons_val_fin_one, add_neg_cancel]

theorem spreads_pol (h : HasAmple P R (algebraMap R K)) : Spreads R (HasPol P) := by
  obtain ⟨A, _, φ, L, h, hL, e, hA⟩ := h
  have := h.1.proper
  have ec := (CechPic.cls_eq_iff P.isLB (pull_isLB hL _)).2 e
  rw [CechPic.cls_pull hL] at ec

  obtain ⟨i, hi⟩ := exists_chart hL (eSec A (genericPoint (Sp R)))
  obtain ⟨f₁, hf₁, H₁⟩ := GenSpread.exists_forall_mem (R := R) (V := eSec A ⁻¹ᵁ L.U i) hi

  obtain ⟨f₂, hf₂, H₂⟩ := GenSpread.exists_lbIso A.hom h.2.2.1 (pull_isLB hL (GrpObj.inv : A ⟶ A).left) hL (by
    refine (CechPic.cls_eq_iff (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _)).1 ?_
    rw [CechPic.cls_pull (pull_isLB hL _), CechPic.cls_pull hL, CechPic.cls_pull hL, ← CechPic.pull_comp,
      ← PolBaseChange.inv_comm h.2.2, CechPic.pull_comp, ← ec, cls_inv])

  obtain ⟨w, hw⟩ : LBIso (L.pull φ) (P.L.pull (𝟙 _)) := by
    refine (CechPic.cls_eq_iff (pull_isLB hL _) (pull_isLB P.isLB _)).1 ?_
    rw [CechPic.cls_pull hL, CechPic.cls_pull P.isLB, CechPic.pull_id, ec]
  obtain ⟨f₃, hf₃, H₃⟩ := GlobalTheory.KTrivSpread.exists_kTriv_of_isUnit R A L K (algebraMap R K) P.A φ h.1 hL hA h.2.2
    (kTriv_pull (@isGrpPullback_of_iso _ _ _ _ _ (Iso.refl P.A) (inferInstanceAs (IsMonHom (𝟙 P.A)))) P.isLB (pull_isLB hL _) ((isGen_iff w).1 hw) P.ktriv)
  have hf₃' : f₃ ≠ 0 := by rintro rfl; exact hf₃ (map_zero _)
  refine ⟨f₁ * f₂ * f₃, mul_ne_zero (mul_ne_zero hf₁ hf₂) hf₃', fun R' _ g ψ hg hψ => ?_⟩
  rw [map_mul, map_mul] at hg
  have u₁ := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hg)
  have u₂ := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hg)
  have u₃ := isUnit_of_mul_isUnit_right hg
  obtain ⟨φ', e', h'⟩ := h.baseChange hψ
  have hb := isGrpPullback_pullback A (spMap g)
  have hL' := pull_isLB hL (pullback.fst A.hom (spMap g))
  obtain ⟨w', hw'⟩ := PolBaseChange.lbIso_refl hL'
  refine ⟨{ A := (Over.pullback (spMap g)).obj A
            isAb := h'.1
            g := P.g
            smoothDim := h'.2.1
            L := L.pull (pullback.fst A.hom (spMap g))
            isLB := hL'
            rigid := ?_
            sym := ?_
            ample := relAmple_pull hb.1 hL hL' ((isGen_iff w').1 hw') ⊤ (isAffineOpen_top _) (fun _ => trivial) hA
            ktriv := H₃ R' g _ _ u₃ hb }, φ', rfl, h'.2.2, lbIso_baseChange P.isLB hL e' e⟩
  · refine IsoExtend.exists_gen_of_chart hL' _ (fun _ => i) fun y => mem_pull.2 ?_
    exact (congrArg (fun q => q y ∈ L.U i) (PolBaseChange.eSec_comm hb)).mpr (H₁ R' g u₁ y)
  · refine sym_of_cls hL' ?_
    have a := (CechPic.cls_eq_iff (pull_isLB (pull_isLB hL _) _) hL').2 (H₂ R' g u₂ _ _ _ hb.1.w)
    rw [CechPic.cls_pull (pull_isLB hL _), CechPic.cls_pull hL, CechPic.cls_pull hL, ← CechPic.pull_comp,
      ← PolBaseChange.inv_comm hb, CechPic.pull_comp] at a
    exact a

end GlobalTheory.PolSpread

open GlobalTheory.PolSpread in

theorem GlobalTheory.polAV_spread : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (P : Out.PolAV (Sp K)), ∃ (f : R) (_ : f ≠ 0) (ψ : (Localization.Away f) →+* K) (P' : Out.PolAV (Sp (Localization.Away f))) (φ : P.A.left ⟶ P'.A.left), ψ.comp (algebraMap R _) = algebraMap R K ∧ P'.g = P.g ∧ IsGrpPullback P.A P'.A (spMap ψ) φ ∧ LBIso P.L (P'.L.pull φ) := by
  intro R K _ _ _ _ _ _ P
  obtain ⟨f, hf, H⟩ := (((spreads_grp P R).step (spreads_lb P)).step (spreads_ample P)).step (spreads_pol P)
  have h₀ : (IsLocalization.Away.lift f (isUnit_algebraMap (K := K) hf) : Localization.Away f →+* K).comp
      (algebraMap R _) = algebraMap R K := IsLocalization.Away.lift_comp f _
  obtain ⟨P', φ, h⟩ := H _ _ _ (IsLocalization.Away.algebraMap_isUnit f) h₀
  exact ⟨f, hf, _, P', φ, h₀, h⟩
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principallyPolarised_model_localizationAway : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (P : Out.PolAV (Sp K)), ∃ (f : R) (_ : f ≠ 0) (ψ : (Localization.Away f) →+* K) (P' : Out.PolAV (Sp (Localization.Away f))) (φ : P.A.left ⟶ P'.A.left), ψ.comp (algebraMap R _) = algebraMap R K ∧ P'.g = P.g ∧ IsGrpPullback P.A P'.A (spMap ψ) φ ∧ LBIso P.L (P'.L.pull φ) := by
  atlas_forward_decl GlobalTheory.polAV_spread
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLevel_endomorphisms_spread_over_basicOpen : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) [Finite J] (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (β : o →+* R) (t : TObj g k J b (spMap (algebraMap R K) ≫ spMap β)) (P' : Out.PolAV (Sp R)) (φ : t.A.left ⟶ P'.A.left), P'.g = g → IsGrpPullback t.A P'.A (spMap (algebraMap R K)) φ → LBIso t.L (P'.L.pull φ) → ∃ (f : R) (_ : f ≠ 0) (t' : TObj g k J b (spMap (algebraMap R (Localization.Away f)) ≫ spMap β)) (ψ : Localization.Away f →+* K), ψ.comp (algebraMap R _) = algebraMap R K ∧ TMap t t' (spMap ψ) := by
  first | exact @GlobalTheory.SpreadLevel.main | exact GlobalTheory.SpreadLevel.main | (intros; apply GlobalTheory.SpreadLevel.main <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.lbIso_generic_spreads_out_alt : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (B : Scheme.{0}) (pB : B ⟶ Sp R) (M N : LB B), QuasiCompact pB → QuasiSeparated pB → M.IsLB → N.IsLB → LBIso (M.pull (pullback.fst pB (spMap (algebraMap R K)))) (N.pull (pullback.fst pB (spMap (algebraMap R K)))) → ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → LBIso (M.pull (pullback.fst pB (spMap φ))) (N.pull (pullback.fst pB (spMap φ))) := by
  first | exact @GlobalTheory.lbIso_generic_spreads_out | exact GlobalTheory.lbIso_generic_spreads_out | (intros; apply GlobalTheory.lbIso_generic_spreads_out <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.GenericSpread

theorem lbIso_pull_of_comp {X Y Z : Scheme.{0}} {M N : LB X} {a : Y ⟶ X} {c : Z ⟶ X} (h : Z ⟶ Y) (e : c = h ≫ a)
    (H : LBIso (M.pull a) (N.pull a)) : LBIso (M.pull c) (N.pull c) :=
  LBIso.chartPull (chartPullSame M _ _ _ h fun _ => e) (chartPullSame N _ _ _ h fun _ => e) H

section Grp

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

def sqMap (h : IsGrpPullback G' G f φ) : Over.mk ((G' ⊗ G').hom ≫ f) ⟶ G ⊗ G :=
  lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))

theorem isPullback_sqMap (h : IsGrpPullback G' G f φ) :
    IsPullback (sqMap h).left (G' ⊗ G').hom (G ⊗ G).hom f := by
  have e₁ : (sqMap h).left ≫ (fst G G).left = (fst G' G').left ≫ φ :=
    congrArg (fun z => z.left) (lift_fst (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')))
  have e₂ : (sqMap h).left ≫ (snd G G).left = (snd G' G').left ≫ φ :=
    congrArg (fun z => z.left) (lift_snd (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')))
  have a' : IsPullback (fst G' G').left (snd G' G').left G'.hom G'.hom := IsPullback.of_hasPullback _ _
  have a : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  have b := a'.paste_horiz h.1
  rw [← e₁, ← h.1.w] at b
  have c := (IsPullback.of_right b e₂ a).paste_vert h.1
  rw [Over.w, Over.w] at c
  exact c

theorem pushPt_comp (h : IsGrpPullback G' G f φ) {w' : G' ⟶ G'} {w : G ⟶ G} (hw : w'.left ≫ φ = φ ≫ w.left)
    {T : Over S'} (x : T ⟶ G') : pushPt h.1.w (x ≫ w') = pushPt h.1.w x ≫ w :=
  Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, hw, Category.assoc])

theorem mul_left_comp (h : IsGrpPullback G' G f φ) {w' v' : G' ⟶ G'} {w v : G ⟶ G} (hw : w'.left ≫ φ = φ ≫ w.left)
    (hv : v'.left ≫ φ = φ ≫ v.left) : (w' * v').left ≫ φ = φ ≫ (w * v).left := by
  have b : pushPt h.1.w (w' * v') = pushPt h.1.w w' * pushPt h.1.w v' := map_mul (pushHom h G') _ _
  have c := pushPt_comp h hw (𝟙 G')
  have d := pushPt_comp h hv (𝟙 G')
  rw [Category.id_comp] at c d
  rw [c, d, ← MonObj.comp_mul] at b
  have e := congrArg (fun z => z.left) b
  refine e.trans ?_
  show (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

variable [IsCommMonObj G] [IsCommMonObj G'] {L : LB G.left} {L' : LB G'.left}

theorem lbIso_cube_pull (h : IsGrpPullback G' G f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hb : LBIso L' (L.pull φ))
    {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G')) (x : Fin n → (T ⟶ G))
    (U : Over.mk (T'.hom ≫ f) ⟶ T) (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i) :
    LBIso (cubeLB G' x' L') ((cubeLB G x L).pull (Y := T'.left) U.left) :=
  LBIso.trans (DVR.linComb_isLB L' hL' _ _) (DVR.linComb_isLB _ (pull_isLB hL φ) _ _)
    (pull_isLB (DVR.linComb_isLB L hL _ _) _) (GlobalTheory.PowPrimitive.lbIso_linComb hb _ _)
    (LBIso.chartPull (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U hx I.down)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) (PolBaseChange.lbIso_refl (DVR.linComb_isLB L hL _ _)))

theorem adj_iff (h : IsGrpPullback G' G f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hb : LBIso L' (L.pull φ))
    {w' v' : G' ⟶ G'} {w v : G ⟶ G} (hw : w'.left ≫ φ = φ ≫ w.left) (hv : v'.left ≫ φ = φ ≫ v.left) :
    LBIso (cubeLB G' ![fst G' G' ≫ w', snd G' G'] L') (cubeLB G' ![fst G' G', snd G' G' ≫ v'] L') ↔
      LBIso ((cubeLB G ![fst G G ≫ w, snd G G] L).pull (Y := (G' ⊗ G').left) (sqMap h).left)
        ((cubeLB G ![fst G G, snd G G ≫ v] L).pull (Y := (G' ⊗ G').left) (sqMap h).left) := by
  have a := lbIso_cube_pull h hL hL' hb ![fst G' G' ≫ w', snd G' G'] ![fst G G ≫ w, snd G G] (sqMap h) fun i => by
    fin_cases i
    · exact (pushPt_comp h hw _).trans (by simp [sqMap])
    · simp [sqMap]
  have b := lbIso_cube_pull h hL hL' hb ![fst G' G', snd G' G' ≫ v'] ![fst G G, snd G G ≫ v] (sqMap h) fun i => by
    fin_cases i
    · simp [sqMap]
    · exact (pushPt_comp h hv _).trans (by simp [sqMap])
  have i' : ∀ x : Fin 2 → (G' ⊗ G' ⟶ G'), (cubeLB G' x L').IsLB := fun x => DVR.linComb_isLB L' hL' _ _
  have i : ∀ x : Fin 2 → (G ⊗ G ⟶ G), ((cubeLB G x L).pull (Y := (G' ⊗ G').left) (sqMap h).left).IsLB :=
    fun x => pull_isLB (DVR.linComb_isLB L hL _ _) _
  exact ⟨fun H => LBIso.trans (i _) (i' _) (i _) a.symm (LBIso.trans (i' _) (i' _) (i _) H b),
    fun H => LBIso.trans (i' _) (i _) (i' _) a (LBIso.trans (i _) (i _) (i' _) H b.symm)⟩

theorem prim_iff (h : IsGrpPullback G' G f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hb : LBIso L' (L.pull φ))
    {w' : G' ⟶ G'} {w : G ⟶ G} (hw : w'.left ≫ φ = φ ≫ w.left) :
    LBIso L' (cubeLB G' ![𝟙 G', w'] L') ↔ LBIso (L.pull φ) ((cubeLB G ![𝟙 G, w] L).pull φ) := by
  have a := lbIso_cube_pull h hL hL' hb ![𝟙 G', w'] ![𝟙 G, w] (pushPt h.1.w (𝟙 G')) fun i => by
    fin_cases i
    · simp
    · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pushPt_comp h hw _)
  have e : (pushPt h.1.w (𝟙 G')).left = φ := Category.id_comp _
  rw [e] at a
  have i' : (cubeLB G' ![𝟙 G', w'] L').IsLB := DVR.linComb_isLB L' hL' _ _
  have i : ((cubeLB G ![𝟙 G, w] L).pull φ).IsLB := pull_isLB (DVR.linComb_isLB L hL _ _) _
  have j := pull_isLB hL φ
  exact ⟨fun H => LBIso.trans j hL' i hb.symm (LBIso.trans hL' i' i H a),
    fun H => LBIso.trans hL' j i' hb (LBIso.trans j i i' H a.symm)⟩

end Grp

theorem spread_lbIso (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {B BK : Scheme.{0}} (pB : B ⟶ Sp R) [QuasiCompact pB] [QuasiSeparated pB] {M N : LB B}
    (hM : M.IsLB) (hN : N.IsLB) {U : BK ⟶ B} {p : BK ⟶ Sp K} (h : IsPullback U p pB (spMap (algebraMap R K)))
    (H : LBIso (M.pull U) (N.pull U)) :
    ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → ∀ {B' : Scheme.{0}} {U' : B' ⟶ B}
      {p' : B' ⟶ Sp R'}, U' ≫ pB = p' ≫ spMap φ → LBIso (M.pull U') (N.pull U') := by
  obtain ⟨f, hf, Hf⟩ := GlobalTheory.T.lbIso_generic_spreads_out_alt R K B pB M N inferInstance inferInstance hM hN
    (lbIso_pull_of_comp h.isoPullback.inv h.isoPullback_inv_fst.symm H)
  exact ⟨f, hf, fun R' _ φ hu B' U' p' e =>
    lbIso_pull_of_comp (pullback.lift U' p' e) (pullback.lift_fst _ _ _).symm (Hf R' φ hu)⟩

theorem spread_prim {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {w w' : J} (R K : Type) [CommRing R]
    [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] {s : Sp R ⟶ Sp o}
    {s' : Sp K ⟶ Sp o} (t' : TObj g k J b s) (t : TObj g k J b s') (hm : TMap t t' (spMap (algebraMap R K)))
    (hp : t.Prim w w') :
    ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (s'' : Sp R' ⟶ Sp o) (t'' : TObj g k J b s''),
      IsUnit (φ f) → TMap t'' t' (spMap φ) → t''.Prim w w' := by
  obtain ⟨ψ, h, hb, -, ha⟩ := hm
  obtain ⟨h₁, h₂, h₃⟩ := hp
  letI := t.ab.comm
  letI := t'.ab.comm
  haveI : IsProper t'.A.hom := t'.ab.proper
  haveI : Smooth t'.A.hom := t'.ab.smooth
  haveI : IsProper (t'.A ⊗ t'.A).hom := by
    rw [← Over.w (fst t'.A t'.A)]
    haveI : IsProper (fst t'.A t'.A).left := inferInstanceAs (IsProper (pullback.fst t'.A.hom t'.A.hom))
    infer_instance
  obtain ⟨q₁, q₂⟩ := GlobalTheory.ExtUnique.spec_fractionRing R K
  have e₁ : t'.act w * t'.act w' = 𝟙 t'.A := by
    refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback h.1 ?_
    rw [← mul_left_comp h (ha w) (ha w'), h₁]
    simp
  obtain ⟨f₂, hf₂, H₂⟩ := spread_lbIso R K (t'.A ⊗ t'.A).hom (DVR.linComb_isLB _ t'.isLB _ _)
    (DVR.linComb_isLB _ t'.isLB _ _) (isPullback_sqMap h) ((adj_iff h t'.isLB t.isLB hb (ha w) (ha w')).1 h₂)
  obtain ⟨f₃, hf₃, H₃⟩ := spread_lbIso R K t'.A.hom t'.isLB
    (DVR.linComb_isLB _ t'.isLB _ _) h.1 ((prim_iff h t'.isLB t.isLB hb (ha w)).1 h₃)
  refine ⟨f₂ * f₃, mul_ne_zero hf₂ hf₃, fun R' _ φ s'' t'' hu ⟨ψ', h', hb', _, ha'⟩ => ?_⟩
  rw [map_mul] at hu
  letI := t''.ab.comm
  refine ⟨?_, (adj_iff h' t'.isLB t''.isLB hb' (ha' w) (ha' w')).2
    (H₂ R' φ (isUnit_of_mul_isUnit_left hu) (isPullback_sqMap h').w),
    (prim_iff h' t'.isLB t''.isLB hb' (ha' w)).2 (H₃ R' φ (isUnit_of_mul_isUnit_right hu) h'.1.w)⟩
  apply Over.OverMorphism.ext
  apply h'.1.hom_ext
  · rw [mul_left_comp h' (ha' w) (ha' w'), e₁]
    simp
  · rw [Over.w, Over.w]

theorem hasTh_unit_mul {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {S : Scheme.{0}}
    {s : S ⟶ Sp o} {t : TObj g (N' ^ 2) J b s} {R : Type} [CommRing R] {x : Sp R ⟶ S} {v v' : Ix g (N' ^ 2) → R}
    (c : R) (hc : IsUnit c) (e : ∀ a, v' a = c * v a) (H : t.HasTh x v) : t.HasTh x v' := by
  obtain ⟨h₁, h₂, h₃⟩ := H
  refine ⟨h₁, h₂, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := h₃ p
  obtain ⟨u', hu⟩ : ∃ u' : Γ((Out.overRes V).left, ⊤)ˣ, u'.val =
      V.ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) :=
    (hc.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).map V.ι.appTop.hom
  refine ⟨V, hV, th, s1, α, τ, U, s2, w, u' * u, a₁, a₂, a₃, a₄, a₅, a₆, a₇, fun i => ?_⟩
  rw [Units.val_mul, _root_.mul_assoc, ← a₈ i, hu]
  beta_reduce
  rw [e, map_mul]
  exact map_mul V.ι.appTop.hom _ _

theorem exists_eq_mul_of_field (hL : Out.Laws) (hL2 : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type}
    {b : TBase o (N' ^ 2)} {S : Scheme.{0}} {s : S ⟶ Sp o} {t : TObj g (N' ^ 2) J b s} {K : Type} [Field K]
    {x : Sp K ⟶ S} {v v' : Ix g (N' ^ 2) → K} (H : t.HasTh x v) (H' : t.HasTh x v') :
    ∃ c : K, c ≠ 0 ∧ ∀ a, v' a = c * v a := by
  have key : ∀ z : Ix g (N' ^ 2) → K, Ideal.span (Set.range z) = ⊤ ∨ ∀ a, z a = 0 := fun z =>
    (Ideal.eq_bot_or_top (Ideal.span (Set.range z))).symm.imp id fun h a =>
      Ideal.span_eq_bot.1 h _ (Set.mem_range_self a)
  rcases key v with h | h
  · obtain ⟨u, hu⟩ := GlobalTheory.T.thetaConstants_unique_up_to_unit hL hL2 o g N' J b S s t K x v v' H H' h
    exact ⟨(u : K), u.ne_zero, hu⟩
  rcases key v' with h' | h'
  · obtain ⟨u, hu⟩ := GlobalTheory.T.thetaConstants_unique_up_to_unit hL hL2 o g N' J b S s t K x v' v H' H h'
    exact ⟨(u⁻¹ : Kˣ), (u⁻¹).ne_zero, fun a => by rw [hu, Units.inv_mul_cancel_left]⟩
  · exact ⟨1, one_ne_zero, fun a => by rw [h, h', mul_zero]⟩

theorem exists_hasTh_away (hL : Out.Laws) (hL2 : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type}
    {b : TBase o (N' ^ 2)} {R : Type} [CommRing R] [IsDomain R] {s : Sp R ⟶ Sp o} (t : TObj g (N' ^ 2) J b s)
    (hN : Odd N') : ∃ f : R, f ≠ 0 ∧ ∃ w : Ix g (N' ^ 2) → Localization.Away f,
      t.HasTh (spMap (algebraMap R (Localization.Away f))) w := by
  let p : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
  obtain ⟨R₁, _, x, w, hx, hp, H⟩ := GlobalTheory.T.exists_thetaConstants_locally_on_base hL hL2 o g N' J b _ s t hN p
  obtain ⟨_, ⟨f, rfl⟩, hf, hsub⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open
    hp x.isOpenEmbedding.isOpen_range
  have hr : Set.range (spMap (algebraMap R (Localization.Away f))) ⊆ Set.range x := by
    refine subset_trans (le_of_eq ?_) hsub
    exact PrimeSpectrum.localization_away_comap_range (Localization.Away f) f
  let y := IsOpenImmersion.lift x (spMap (algebraMap R (Localization.Away f))) hr
  have hy : spMap (Spec.preimage y).hom ≫ x = spMap (algebraMap R (Localization.Away f)) := by
    rw [← IsOpenImmersion.lift_fac x (spMap (algebraMap R (Localization.Away f))) hr]
    congr 1
    exact Spec.map_preimage y
  refine ⟨f, fun h => hf (by subst h; exact Ideal.zero_mem _), fun a => (Spec.preimage y).hom (w a), ?_⟩
  rw [← hy]
  exact GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b _ s t R₁ _ _ x w H

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem spread_hasTh (hL : Out.Laws) (hL2 : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type}
    {b : TBase o (N' ^ 2)} (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {s : Sp R ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) (v : Ix g (N' ^ 2) → R)
    (H : t.HasTh (spMap (algebraMap R K)) (fun a => algebraMap R K (v a))) :
    ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
      t.HasTh (spMap φ) (fun a => φ (v a)) := by
  obtain ⟨f, hf, w, Hw⟩ := exists_hasTh_away hL hL2 t H.1
  have pull : ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (hu : IsUnit (φ f)),
      t.HasTh (spMap φ) (fun a => IsLocalization.Away.lift f hu (w a)) := fun R' _ φ hu => by
    have := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b _ s t _ R' (IsLocalization.Away.lift f hu) _ w Hw
    rwa [spMap_comp, IsLocalization.Away.lift_comp] at this
  have inj := IsFractionRing.injective R K
  have hK : IsUnit (algebraMap R K f) := ((map_ne_zero_iff _ inj).2 hf).isUnit
  obtain ⟨c, hc, e⟩ := exists_eq_mul_of_field hL hL2 (pull K _ hK) H
  obtain ⟨a, a', ha', rfl⟩ := IsFractionRing.div_surjective (A := R) c
  have ha0' : a' ≠ 0 := nonZeroDivisors.ne_zero ha'
  have ha0 : a ≠ 0 := fun h => hc (by rw [h, map_zero, zero_div])
  have linj : Function.Injective (IsLocalization.Away.lift (S := Localization.Away f) f hK) := by
    unfold IsLocalization.Away.lift
    rw [IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h
      rw [IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hf) h]
    · intro h
      rw [inj h]
  have e' : ∀ i, algebraMap R (Localization.Away f) (a' * v i) = algebraMap R _ a * w i := fun i => by
    apply linj
    have := e i
    beta_reduce at this
    rw [IsLocalization.Away.lift_eq, map_mul (IsLocalization.Away.lift f hK), IsLocalization.Away.lift_eq, map_mul, this, ← _root_.mul_assoc,
      mul_div_cancel₀ _ ((map_ne_zero_iff _ inj).2 ha0')]
  refine ⟨f * (a * a'), mul_ne_zero hf (mul_ne_zero ha0 ha0'), fun R' _ φ hu => ?_⟩
  rw [map_mul, map_mul] at hu
  have u₁ := isUnit_of_mul_isUnit_left hu
  have u₂ := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right hu)
  obtain ⟨u₃, hu₃⟩ := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hu)
  refine hasTh_unit_mul ((u₃⁻¹ : R'ˣ) * φ a) ((u₃⁻¹).isUnit.mul u₂) (fun i => ?_) (pull R' φ u₁)
  have := congrArg (IsLocalization.Away.lift f u₁) (e' i)
  rw [map_mul (IsLocalization.Away.lift f u₁), IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq, map_mul,
    ← hu₃] at this
  beta_reduce
  rw [_root_.mul_assoc, ← this, Units.inv_mul_cancel_left]

theorem range_spMap_fractionRing (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] :
    Set.range (spMap (algebraMap R K)) = {genericPoint (Sp R)} := by
  have e : ∀ q : Sp K, spMap (algebraMap R K) q = genericPoint (Sp R) := fun q => by
    rw [genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap R K) q.asIdeal = ⊥
    rw [(Ideal.eq_bot_or_top q.asIdeal).resolve_right q.isPrime.ne_top]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨(default : PrimeSpectrum K), e _⟩, ?_⟩
  rintro _ ⟨q, rfl⟩
  exact e q

theorem exists_ne_zero_hasTh_shape_prim : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) Mat κ (w w' : J) (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (s : Sp R ⟶ Sp o) (s' : Sp K ⟶ Sp o) (t' : TObj g (N' ^ 2) J b s) (t : TObj g (N' ^ 2) J b s') (v : Ix g (N' ^ 2) → R), TMap t t' (spMap (algebraMap R K)) → t.HasTh (𝟙 _) (fun a => algebraMap R K (v a)) → t.Shape Mat κ → t.Prim w w' → ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (s'' : Sp R' ⟶ Sp o) (t'' : TObj g (N' ^ 2) J b s''), IsUnit (φ f) → TMap t'' t' (spMap φ) → t''.HasTh (𝟙 _) (fun a => φ (v a)) ∧ t''.Shape Mat κ ∧ t''.Prim w w' := by
  intro hL hL2 o _ g N' J b Mat κ w w' R K _ _ _ _ _ _ s s' t' t v hm hT hS hP
  have hS' : t'.Shape Mat κ :=
    GlobalTheory.T.thetaLevelShape_of_generic_point hL hL2 o g _ J b Mat κ _ s t' K _ s' t (range_spMap_fractionRing R K) hm hS
  have hT' := (GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b _ s t' _ s' t _ K _ _ hm).1 hT
  rw [Category.id_comp] at hT'
  obtain ⟨f₁, hf₁, H₁⟩ := spread_hasTh hL hL2 R K t' v hT'
  obtain ⟨f₂, hf₂, H₂⟩ := spread_prim R K t' t hm hP
  refine ⟨f₁ * f₂, mul_ne_zero hf₁ hf₂, fun R' _ φ s'' t'' hu hm' => ?_⟩
  rw [map_mul] at hu
  refine ⟨(GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b _ s t' _ s'' t'' _ R' _ _ hm').2 ?_,
    (GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ w w' _ _ s s'' _ t' t'' hm').1 hS',
    H₂ R' φ s'' t'' (isUnit_of_mul_isUnit_right hu) hm'⟩
  rw [Category.id_comp]
  exact H₁ R' φ (isUnit_of_mul_isUnit_left hu)

end GlobalTheory.GenericSpread
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaPoint_shape_primitivity_near_generic : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) Mat κ (w w' : J) (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (s : Sp R ⟶ Sp o) (s' : Sp K ⟶ Sp o) (t' : TObj g (N' ^ 2) J b s) (t : TObj g (N' ^ 2) J b s') (v : Ix g (N' ^ 2) → R), TMap t t' (spMap (algebraMap R K)) → t.HasTh (𝟙 _) (fun a => algebraMap R K (v a)) → t.Shape Mat κ → t.Prim w w' → ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (s'' : Sp R' ⟶ Sp o) (t'' : TObj g (N' ^ 2) J b s''), IsUnit (φ f) → TMap t'' t' (spMap φ) → t''.HasTh (𝟙 _) (fun a => φ (v a)) ∧ t''.Shape Mat κ ∧ t''.Prim w w' := by
  first | exact @GlobalTheory.GenericSpread.exists_ne_zero_hasTh_shape_prim | exact GlobalTheory.GenericSpread.exists_ne_zero_hasTh_shape_prim | (intros; apply GlobalTheory.GenericSpread.exists_ne_zero_hasTh_shape_prim <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SpreadGeneric

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    (h : A →+* C) (e : g.comp f = h) : spMap g ≫ spMap f = spMap h := by
  subst e
  exact (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

section Algebra
variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

def Near {R' : Type} [CommRing R'] (io : R →+* R') (χ : R' →+* K) (x : R') : Prop :=
  ∃ (F : R) (_ : F ≠ 0) (φ : R' →+* Localization.Away F) (ψ : Localization.Away F →+* K),
    φ.comp io = algebraMap R _ ∧ ψ.comp (algebraMap R _) = algebraMap R K ∧ ψ.comp φ = χ ∧ IsUnit (φ x)

theorem Near.shrink {R' : Type} [CommRing R'] {io : R →+* R'} {χ : R' →+* K} {y : R'} (h : Near io χ y)
    (x : R') (hx : χ x ≠ 0) : Near io χ x := by
  obtain ⟨F, hF, φ, ψ, h1, h2, h3, -⟩ := h
  obtain ⟨⟨a, ⟨s, n, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers F) (φ x)
  simp only at ha
  have hinj := IsFractionRing.injective R K
  have hK : ∀ r : R, ψ (algebraMap R _ r) = algebraMap R K r := fun r => RingHom.congr_fun h2 r
  have ha0 : a ≠ 0 := by
    rintro rfl
    have := congrArg ψ ha
    rw [map_mul, hK, hK, map_zero, ← RingHom.comp_apply, h3] at this
    rcases mul_eq_zero.1 this with h | h
    · exact hx h
    · exact pow_ne_zero n hF (hinj (h.trans (map_zero _).symm))
  have hFa : F * a ≠ 0 := mul_ne_zero hF ha0
  have hu : IsUnit (algebraMap R (Localization.Away (F * a)) (F * a)) :=
    IsLocalization.Away.algebraMap_isUnit (F * a)
  rw [map_mul] at hu
  have huK : IsUnit (algebraMap R K (F * a)) :=
    isUnit_iff_ne_zero.2 fun h => hFa (hinj (h.trans (map_zero _).symm))
  let ρ : Localization.Away F →+* Localization.Away (F * a) :=
    IsLocalization.Away.lift F (isUnit_of_mul_isUnit_left hu)
  have hρ : ρ.comp (algebraMap R _) = algebraMap R _ := IsLocalization.Away.lift_comp _ _
  let ψ' : Localization.Away (F * a) →+* K := IsLocalization.Away.lift (F * a) huK
  have hψ' : ψ'.comp (algebraMap R _) = algebraMap R K := IsLocalization.Away.lift_comp _ _
  have hc : ψ'.comp ρ = ψ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers F)
    rw [RingHom.comp_assoc, hρ, hψ', h2]
  refine ⟨F * a, hFa, ρ.comp φ, ψ', ?_, hψ', ?_, ?_⟩
  · rw [RingHom.comp_assoc, h1, hρ]
  · rw [← RingHom.comp_assoc, hc, h3]
  · have := congrArg ρ ha
    rw [map_mul, show ρ (algebraMap R _ a) = algebraMap R _ a from RingHom.congr_fun hρ a] at this
    exact isUnit_of_mul_isUnit_left (this ▸ isUnit_of_mul_isUnit_right hu)

omit [IsDomain R] [IsFractionRing R K] in
theorem Near.away {R' : Type} [CommRing R'] {io : R →+* R'} {χ : R' →+* K} {x : R'} (h : Near io χ x)
    (χ' : Localization.Away x →+* K) (e : χ'.comp (algebraMap R' _) = χ) :
    Near ((algebraMap R' (Localization.Away x)).comp io) χ' 1 := by
  obtain ⟨F, hF, φ, ψ, h1, h2, h3, h4⟩ := h
  have hρ : (IsLocalization.Away.lift (S := Localization.Away x) x h4).comp (algebraMap R' _) = φ :=
    IsLocalization.Away.lift_comp _ _
  refine ⟨F, hF, IsLocalization.Away.lift x h4, ψ, ?_, h2, ?_, by simp⟩
  · rw [← RingHom.comp_assoc, hρ, h1]
  · apply IsLocalization.ringHom_ext (Submonoid.powers x)
    rw [RingHom.comp_assoc, hρ, h3, e]

omit [IsFractionRing R K] in
theorem isDomain_away {f : R} (hf : f ≠ 0) : IsDomain (Localization.Away f) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hf)

theorem isFractionRing_away {f : R} (hf : f ≠ 0) (ψ : Localization.Away f →+* K)
    (e : ψ.comp (algebraMap R _) = algebraMap R K) :
    letI := ψ.toAlgebra
    IsFractionRing (Localization.Away f) K := by
  letI := ψ.toAlgebra
  haveI : IsScalarTower R (Localization.Away f) K := IsScalarTower.of_algebraMap_eq' e.symm
  exact IsFractionRing.isFractionRing_of_isLocalization (Submonoid.powers f) _ K
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)

end Algebra

theorem exists_spread : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) Mat κ (w w' : J) [Finite J] (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (t : TObj g (N' ^ 2) J b (spMap (algebraMap R K) ≫ spMap β)), t.HasTh (𝟙 _) (fun a => algebraMap R K (v a)) → t.Shape Mat κ → t.Prim w w' → ∃ (f : R) (_ : f ≠ 0) (t' : TObj g (N' ^ 2) J b (spMap (algebraMap R (Localization.Away f)) ≫ spMap β)) (ψ : Localization.Away f →+* K), ψ.comp (algebraMap R _) = algebraMap R K ∧ TMap t t' (spMap ψ) ∧ t'.HasTh (𝟙 _) (fun a => algebraMap R _ (v a)) ∧ t'.Shape Mat κ ∧ t'.Prim w w' := by
  intro l1 l2 o _ g N' J b Mat κ w w' _ R K _ _ _ _ _ _ β v t hth hsh hpr
  obtain ⟨f, hf, ψ₁, P', φ, e₁, hg, hpb, hL⟩ := GlobalTheory.T.exists_principallyPolarised_model_localizationAway R K t.pol
  haveI := isDomain_away hf
  letI := ψ₁.toAlgebra
  haveI := isFractionRing_away hf ψ₁ e₁
  have key : ∀ (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (φ : t.A.left ⟶ P'.A.left),
      s = spMap (algebraMap (Localization.Away f) K) ≫ spMap ((algebraMap R (Localization.Away f)).comp β) →
      IsGrpPullback t.A P'.A (spMap ψ₁) φ → LBIso t.L (P'.L.pull φ) →
      ∃ (f₁ : Localization.Away f) (_ : f₁ ≠ 0) (s' : Sp (Localization.Away f₁) ⟶ Sp o)
        (t' : TObj g (N' ^ 2) J b s') (ψ : Localization.Away f₁ →+* K),
        s' = spMap (algebraMap _ (Localization.Away f₁)) ≫ spMap ((algebraMap R (Localization.Away f)).comp β) ∧
        ψ.comp (algebraMap _ _) = ψ₁ ∧ TMap t t' (spMap ψ) := by
    rintro s t φ rfl h1 h2
    obtain ⟨f₁, h, t', ψ, h3, h4⟩ := GlobalTheory.T.thetaLevel_endomorphisms_spread_over_basicOpen l1 l2 o g (N' ^ 2) J b (Localization.Away f) K
      ((algebraMap R (Localization.Away f)).comp β) t P' φ hg h1 h2
    exact ⟨f₁, h, _, t', ψ, rfl, h3, h4⟩
  obtain ⟨f₁, hf₁, s₂, t₂, ψ₂, hs₂, e₂, hm⟩ := key _ t φ (by
    rw [spMap_comp_eq _ _ _ rfl, spMap_comp_eq _ _ _ rfl, ← RingHom.comp_assoc]
    exact congrArg (fun r => spMap (RingHom.comp r β)) e₁.symm) hpb hL
  haveI := isDomain_away hf₁
  letI := ψ₂.toAlgebra
  haveI := isFractionRing_away (K := K) hf₁ ψ₂ e₂
  let io : R →+* Localization.Away f₁ := (algebraMap (Localization.Away f) _).comp (algebraMap R _)
  have hio : ψ₂.comp io = algebraMap R K := by rw [← RingHom.comp_assoc, e₂, e₁]
  have hv : (fun a => algebraMap (Localization.Away f₁) K (io (v a))) = fun a => algebraMap R K (v a) :=
    funext fun a => RingHom.congr_fun hio (v a)
  obtain ⟨f₂, hf₂, H⟩ := GlobalTheory.T.exists_thetaPoint_shape_primitivity_near_generic l1 l2 o g N' J b Mat κ w w' (Localization.Away f₁) K s₂ _ t₂ t
    (fun a => io (v a)) hm (hv ▸ hth) hsh hpr
  have n0 : Near (algebraMap R (Localization.Away f)) ψ₁ 1 :=
    ⟨f, hf, RingHom.id _, ψ₁, rfl, e₁, rfl, isUnit_one⟩
  have n1 := (n0.shrink f₁ fun h =>
    hf₁ (IsFractionRing.injective (Localization.Away f) K (h.trans (map_zero _).symm))).away ψ₂ e₂
  obtain ⟨F, hF, ρ, ψ, h1, h2, h3, h4⟩ := n1.shrink f₂ fun h =>
    hf₂ (IsFractionRing.injective (Localization.Away f₁) K (h.trans (map_zero _).symm))
  obtain ⟨t', ht'⟩ := GlobalTheory.tObj_pull o g (N' ^ 2) J b _ _ s₂
    (spMap (algebraMap R (Localization.Away F)) ≫ spMap β) (spMap ρ) t₂ (by
      rw [hs₂, spMap_comp_eq _ _ _ rfl, spMap_comp_eq _ _ _ rfl, spMap_comp_eq _ _ _ rfl, ← h1])
  obtain ⟨c1, c2, c3⟩ := H _ ρ _ t' h4 ht'
  refine ⟨F, hF, t', ψ, h2, ?_, ?_, c2, c3⟩
  · refine ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g (N' ^ 2) J b _ _ _ _ _ _ t₂ t' t).2 (spMap ρ) (spMap ψ) ht').2 ?_
    rw [spMap_comp_eq _ _ _ h3]
    exact hm
  · have : (fun a => ρ (io (v a))) = fun a => algebraMap R (Localization.Away F) (v a) :=
      funext fun a => RingHom.congr_fun h1 (v a)
    exact this ▸ c1

end GlobalTheory.SpreadGeneric
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spread_theta_level_abelian_scheme_away : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) Mat κ (w w' : J) [Finite J] (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (t : TObj g (N' ^ 2) J b (spMap (algebraMap R K) ≫ spMap β)), t.HasTh (𝟙 _) (fun a => algebraMap R K (v a)) → t.Shape Mat κ → t.Prim w w' → ∃ (f : R) (_ : f ≠ 0) (t' : TObj g (N' ^ 2) J b (spMap (algebraMap R (Localization.Away f)) ≫ spMap β)) (ψ : Localization.Away f →+* K), ψ.comp (algebraMap R _) = algebraMap R K ∧ TMap t t' (spMap ψ) ∧ t'.HasTh (𝟙 _) (fun a => algebraMap R _ (v a)) ∧ t'.Shape Mat κ ∧ t'.Prim w w' := by
  atlas_forward_decl GlobalTheory.SpreadGeneric.exists_spread
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem exists_complete_dvr_point (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [Algebra.FiniteType ℤ R] (𝔪 : Ideal R) (h𝔪 : 𝔪.IsMaximal) (f : R) (hf : f ≠ 0) :
    ∃ (V F : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal V) V) (_ : Finite (IsLocalRing.ResidueField V))
      (_ : Field F) (_ : CharZero F) (_ : Algebra V F) (_ : IsFractionRing V F) (y : R →+* V),
      (IsLocalRing.maximalIdeal V).comap y = 𝔪 ∧ y f ≠ 0 := by
  obtain ⟨p, hp, hpm⟩ := GlobalTheory.exists_prime_natCast_mem_of_finiteType_int 𝔪
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨L, hL, y, hy, hyf⟩ := GlobalTheory.exists_padic_point 𝔪 hpm hf
  exact ⟨integralClosure ℤ_[p] L, L, inferInstance, inferInstance, inferInstance,
    GlobalTheory.DiscEval.isAdicComplete_integralClosure L, GlobalTheory.DiscEval.finite_residueField_integralClosure L,
    inferInstance, charZero_of_injective_algebraMap (algebraMap ℚ_[p] L).injective, inferInstance,
    inferInstance, y, hy, hyf⟩

theorem exists_obj_over_complete_dvr : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) Mat κ (w w' : J) [Finite J] (R K : Type) [CommRing R] [IsDomain R] [CharZero R] [Algebra.FiniteType ℤ R] [Field K] [Algebra R K] [IsFractionRing R K] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (t : TObj g (N' ^ 2) J b (spMap (algebraMap R K) ≫ spMap β)) (𝔪 : Ideal R), 𝔪.IsMaximal → t.HasTh (𝟙 _) (fun a => algebraMap R K (v a)) → t.Shape Mat κ → t.Prim w w' → ∃ (V F : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : IsAdicComplete (IsLocalRing.maximalIdeal V) V) (_ : Finite (IsLocalRing.ResidueField V)) (_ : Field F) (_ : CharZero F) (_ : Algebra V F) (_ : IsFractionRing V F) (y : R →+* V) (tF : TObj g (N' ^ 2) J b (spMap (algebraMap V F) ≫ spMap (y.comp β))), (IsLocalRing.maximalIdeal V).comap y = 𝔪 ∧ tF.Shape Mat κ ∧ tF.Prim w w' ∧ tF.HasTh (𝟙 _) (fun a => algebraMap V F (y (v a))) := by
  intro L1 L2 o _ g N' J b Mat κ w w' _ R K _ _ _ _ _ _ _ β v t 𝔪 h𝔪 hth hsh hpr
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  obtain ⟨f, hf, t', ψ, -, -, hth', hsh', hpr'⟩ :=
    GlobalTheory.T.exists_spread_theta_level_abelian_scheme_away L1 L2 o g N' J b Mat κ w w' R K β v t hth hsh hpr
  obtain ⟨V, F, i1, i2, i3, i4, i5, i6, i7, i8, i9, y, hy, hyf⟩ :=
    exists_complete_dvr_point R 𝔪 h𝔪 f hf
  have hu : IsUnit (((algebraMap V F).comp y) f) :=
    isUnit_iff_ne_zero.mpr fun h => hyf (IsFractionRing.injective V F (h.trans (map_zero _).symm))
  let φ : Localization.Away f →+* F := IsLocalization.Away.lift f hu
  have hφ : φ.comp (algebraMap R (Localization.Away f)) = (algebraMap V F).comp y :=
    IsLocalization.Away.lift_comp f hu
  have hsq : spMap φ ≫ spMap (algebraMap R (Localization.Away f)) ≫ spMap β =
      spMap (algebraMap V F) ≫ spMap (y.comp β) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← RingHom.comp_assoc, hφ, RingHom.comp_assoc]
  obtain ⟨tF, hm⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g (N' ^ 2) J b _ _ _ _ (spMap φ) t' hsq
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g (N' ^ 2) J b Mat κ w w' _ _ _ _ _ t' tF hm
  refine ⟨V, F, i1, i2, i3, i4, i5, i6, i7, i8, i9, y, tF, hy, h1 hsh', h2 hpr', ?_⟩
  have h3 := GlobalTheory.T.hasThetaConstants_ring_baseChange L2 o g N' J b _ _ t' _ _ φ _ _ hth'
  refine (GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b _ _ t' _ _ tF _ F _ _ hm).mpr ?_
  rw [Category.id_comp]
  rw [Category.comp_id] at h3
  have e : (fun a => algebraMap V F (y (v a))) =
      fun a => φ (algebraMap R (Localization.Away f) (v a)) :=
    funext fun a => (RingHom.congr_fun hφ (v a)).symm
  rw [e]
  exact h3

end GlobalTheory.ZM
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaObject_over_complete_dvr_specialisation : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) Mat κ (w w' : J) [Finite J] (R K : Type) [CommRing R] [IsDomain R] [CharZero R] [Algebra.FiniteType ℤ R] [Field K] [Algebra R K] [IsFractionRing R K] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (t : TObj g (N' ^ 2) J b (spMap (algebraMap R K) ≫ spMap β)) (𝔪 : Ideal R), 𝔪.IsMaximal → t.HasTh (𝟙 _) (fun a => algebraMap R K (v a)) → t.Shape Mat κ → t.Prim w w' → ∃ (V F : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : IsAdicComplete (IsLocalRing.maximalIdeal V) V) (_ : Finite (IsLocalRing.ResidueField V)) (_ : Field F) (_ : CharZero F) (_ : Algebra V F) (_ : IsFractionRing V F) (y : R →+* V) (tF : TObj g (N' ^ 2) J b (spMap (algebraMap V F) ≫ spMap (y.comp β))), (IsLocalRing.maximalIdeal V).comap y = 𝔪 ∧ tF.Shape Mat κ ∧ tF.Prim w w' ∧ tF.HasTh (𝟙 _) (fun a => algebraMap V F (y (v a))) := by
  atlas_forward_decl GlobalTheory.ZM.exists_obj_over_complete_dvr
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory
namespace ClosedPts

theorem spMap_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]
  rfl

theorem jacobson_int : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases h : P = ⊥
  · subst h
    refine le_antisymm (fun x hx => ?_) Ideal.le_jacobson
    rw [Ideal.mem_bot]
    by_contra h0
    have h1 := Ideal.mem_jacobson_bot.1 hx x
    have h2 : 0 < x * x := mul_self_pos.2 h0
    rcases Int.isUnit_iff.1 h1 with h3 | h3 <;> omega
  · have := Ring.DimensionLEOne.maximalOfPrime h hP
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem exists_maximal_notMem {R : Type} [CommRing R] [IsJacobsonRing R] (q : Ideal R) (f : R) (hq : q.IsPrime)
    (hf : f ∉ q) : ∃ m : Ideal R, m.IsMaximal ∧ q ≤ m ∧ f ∉ m := by
  by_contra hc
  push Not at hc
  apply hf
  rw [← IsJacobsonRing.out inferInstance hq.isRadical, Ideal.jacobson, Ideal.mem_sInf]
  rintro m ⟨h1, h2⟩
  exact hc m h2 h1

theorem charZero_quotient {o R : Type} [CommRing o] [IsDomain o] [CharZero o] [CommRing R] [Algebra o R]
    [Module.Flat o R] {q : Ideal R} (hq : q ∈ minimalPrimes R) : CharZero (R ⧸ q) := by
  have hp : q.IsPrime := hq.1.1
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra h0
  have h1 : (n : o) ∈ nonZeroDivisors o := mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast h0)
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) h1
  have h2 : (n : R) ∈ q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact hn
  refine Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hq) h2 ?_
  refine mem_nonZeroDivisors_iff_left.2 fun x hx => hreg ?_
  simpa [Algebra.smul_def] using hx

theorem finiteType_int_of_surjective {A B : Type} [CommRing A] [CommRing B] [Algebra.FiniteType ℤ A] (f : A →+* B)
    (hf : Function.Surjective f) : Algebra.FiniteType ℤ B :=
  Algebra.FiniteType.of_surjective f.toIntAlgHom hf

theorem range_spMap_fraction (V K : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K] :
    Set.range (spMap (algebraMap V K)) = {genericPoint (Sp V)} := by
  rw [genericPoint_eq_bot_of_affine]
  have key : ∀ y : Sp K, spMap (algebraMap V K) y = (⊥ : PrimeSpectrum V) := fun y => by
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (algebraMap V K) y.asIdeal = ⊥
    have hy : y.asIdeal = (⊥ : Ideal K) := Ideal.eq_bot_of_prime (K := K) y.asIdeal (h := y.isPrime)
    rw [hy]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V K)
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact key y
  · rintro rfl
    exact ⟨(⊥ : PrimeSpectrum K), key _⟩

theorem exists_pull (h2 : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) {A B : Type} [CommRing A] [CommRing B] (e : A →+* B)
    {s : Sp A ⟶ Sp o} (s' : Sp B ⟶ Sp o) (hs : spMap e ≫ s = s') (t : TObj g (N' ^ 2) J b s)
    (v : Ix g (N' ^ 2) → A) (hsh : t.Shape Mat κ) (hv : t.HasTh (𝟙 _) v) :
    ∃ t' : TObj g (N' ^ 2) J b s', t'.Shape Mat κ ∧ t'.HasTh (𝟙 _) (fun a => e (v a)) ∧
      ∀ w w' : J, t.Prim w w' → t'.Prim w w' := by
  obtain ⟨t', ht'⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g _ J b _ _ s s' (spMap e) t hs
  refine ⟨t', ?_, ?_, fun w w' => (GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ w w' _ _ s s' _ t t' ht').2.1⟩
  · intro j
    exact (GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ j j _ _ s s' _ t t' ht').1 hsh j
  · rw [GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b _ s t _ s' t' _ B (𝟙 _) _ ht', Category.id_comp]
    have := GlobalTheory.T.hasThetaConstants_ring_baseChange h2 o g N' J b _ s t A B e (𝟙 _) v hv
    rwa [Category.comp_id] at this

end ClosedPts

open ClosedPts in

theorem veryDense_objPrimes_of_minimalPrimes : Out.Laws → Out.Laws2 → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (R : Type) [CommRing R] [Algebra o R] (v : Ix g ((n ^ j) ^ 2) → R), Algebra.FiniteType o R → IsReduced R → Module.Flat o R → InMM n (n ^ j) (thIdeal em C) (algebraMap o R) v → (∀ q ∈ minimalPrimes R, ∃ (K : Type) (_ : Field K) (x : R →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap (algebraMap o R))), RingHom.ker x = q ∧ t.Shape Mat κ ∧ t.Prim w w' ∧ t.HasTh (𝟙 _) (fun a => x (v a))) → VeryDense (objPrimes b Mat κ (algebraMap o R) v) := by
  intro h1 h2 crit g J _ Mat κ n w w' hn hodd
  obtain ⟨j₁, crit⟩ := crit g n J w w' hn hodd
  obtain ⟨j₂, desc⟩ := GlobalTheory.T.descend_to_thetaConstant_field h1 h2 g J Mat κ n w w' hn hodd
  refine ⟨max j₁ j₂, fun j hj o _ b em C d har _ R _ _ v hft _ hflat hMM hmin q f hq hf => ?_⟩
  obtain ⟨hded, hfo, hinj⟩ := har
  have : CharZero o := em.charZero
  have : Algebra.FiniteType ℤ R := Algebra.FiniteType.trans hfo hft
  have := jacobson_int
  have : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := ℤ)
  obtain ⟨m, hm, hqm, hfm⟩ := exists_maximal_notMem q f hq hf
  refine ⟨m, ?_, hm.isPrime, hqm, hfm⟩
  have := hm.isPrime
  obtain ⟨q₀, hq₀, hq₀m⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := m) bot_le
  have hp₀ : q₀.IsPrime := hq₀.1.1
  have : CharZero (R ⧸ q₀) := charZero_quotient (o := o) hq₀
  have := finiteType_int_of_surjective (Ideal.Quotient.mk q₀) Ideal.Quotient.mk_surjective
  obtain ⟨K, _, x, t, hx, hsh, hpr, hth⟩ := hmin q₀ hq₀

  let Ω := AlgebraicClosure K
  obtain ⟨tΩ, hshΩ, hthΩ, hprΩ⟩ := exists_pull h2 Mat κ (algebraMap K Ω) _ rfl t _ hsh hth

  let R₀ := R ⧸ q₀
  let K₀ := FractionRing R₀
  let π : R →+* R₀ := Ideal.Quotient.mk q₀
  let x₀ : R₀ →+* Ω := Ideal.Quotient.lift q₀ ((algebraMap K Ω).comp x) fun a ha => by
    rw [← hx, RingHom.mem_ker] at ha
    simp [ha]
  have hx₀ : Function.Injective x₀ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : algebraMap K Ω (x a) = 0 := ha
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hx, RingHom.mem_ker]
    exact (map_eq_zero _).1 this
  let e : K₀ →+* Ω := IsFractionRing.lift hx₀
  have he : ∀ a : R, e (algebraMap R₀ K₀ (π a)) = algebraMap K Ω (x a) := fun a => by
    simp only [e, IsFractionRing.lift_algebraMap]
    rfl
  let β₀ : o →+* R₀ := π.comp (algebraMap o R)
  obtain ⟨t₀, -, hsh₀, hpr₀, hth₀⟩ := desc j (le_of_max_le_right hj) o b K₀ Ω ((algebraMap R₀ K₀).comp β₀) e _ tΩ
    (fun a => algebraMap R₀ K₀ (π (v a))) (by
      simp only [spMap_spMap]
      congr 1
      ext a
      exact (he _).symm) hshΩ (hprΩ w w' hpr) (by simpa only [he] using hthΩ)
  obtain ⟨t₁, hsh₁, hth₁, hpr₁⟩ := exists_pull h2 Mat κ (RingHom.id K₀) (spMap (algebraMap R₀ K₀) ≫ spMap β₀)
    (by simp only [spMap_spMap, RingHom.id_comp]) t₀ _ hsh₀ hth₀

  have hker : RingHom.ker π ≤ m := by rwa [Ideal.mk_ker]
  have hm₀ : (m.map π).IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective π Ideal.Quotient.mk_surjective hm).resolve_left fun h => by
      have := Ideal.comap_map_of_surjective' π Ideal.Quotient.mk_surjective m
      rw [h, Ideal.comap_top, sup_eq_left.2 hker] at this
      exact hm.ne_top this.symm
  have hcm : (m.map π).comap π = m := by
    rw [Ideal.comap_map_of_surjective' π Ideal.Quotient.mk_surjective m, sup_eq_left.2 hker]
  obtain ⟨V, F, _, _, _, _, _, _, _, _, _, y, tF, hy, hshF, hprF, hthF⟩ :=
    GlobalTheory.T.exists_thetaObject_over_complete_dvr_specialisation h1 h2 o g (n ^ j) J b Mat κ w w' R₀ K₀ β₀ (fun a => π (v a)) t₁ (m.map π) hm₀ hth₁ hsh₁ (hpr₁ w w' hpr₀)
  have hmem : ∀ a : R, y (π a) ∈ IsLocalRing.maximalIdeal V ↔ a ∈ m := fun a => by
    rw [← Ideal.mem_comap, hy, ← Ideal.mem_comap, hcm]
  have hcos : Coset n (n ^ j) (fun a => y (π (v a))) (IsLocalRing.maximalIdeal V) := fun a => by
    obtain ⟨c, hc⟩ := hMM.2 m hm.isPrime a
    exact ⟨c, fun h => hc ((hmem _).1 h)⟩

  obtain ⟨V', K', _, _, _, _, _, _, φ, ψ, t', tK, hφ, -, hK, hK', hth'⟩ :=
    crit j (le_of_max_le_left hj) o b V F (y.comp β₀) tF _ hprF hthF hcos
  have hshK : tK.Shape Mat κ :=
    (GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ w w' _ _ _ _ _ tF tK hK).1 hshF
  have hsh' : t'.Shape Mat κ :=
    GlobalTheory.T.thetaLevelShape_of_generic_point h1 h2 o g _ J b Mat κ (Sp V') _ t' K' _ _ tK (range_spMap_fraction V' K') hK' hshK

  let k := AlgebraicClosure (IsLocalRing.ResidueField V')
  let r : V' →+* k := (algebraMap (IsLocalRing.ResidueField V') k).comp (IsLocalRing.residue V')
  let z : R →+* k := r.comp (φ.comp (y.comp π))
  obtain ⟨tk, hshk, hthk, -⟩ := exists_pull h2 Mat κ r (spMap z ≫ spMap (algebraMap o R))
    (by simp only [spMap_spMap]) t' _ hsh' hth'
  refine ⟨k, inferInstance, inferInstance, z, tk, ?_, hshk, hthk⟩
  ext a
  rw [RingHom.mem_ker, ← hmem]
  change algebraMap (IsLocalRing.ResidueField V') k (IsLocalRing.residue V' (φ (y (π a)))) = 0 ↔ _
  rw [map_eq_zero, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.veryDense_closedPoint_objects_of_minimalPrimes : Out.Laws → Out.Laws2 → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (R : Type) [CommRing R] [Algebra o R] (v : Ix g ((n ^ j) ^ 2) → R), Algebra.FiniteType o R → IsReduced R → Module.Flat o R → InMM n (n ^ j) (thIdeal em C) (algebraMap o R) v → (∀ q ∈ minimalPrimes R, ∃ (K : Type) (_ : Field K) (x : R →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap (algebraMap o R))), RingHom.ker x = q ∧ t.Shape Mat κ ∧ t.Prim w w' ∧ t.HasTh (𝟙 _) (fun a => x (v a))) → VeryDense (objPrimes b Mat κ (algebraMap o R) v) := by
  atlas_forward_decl GlobalTheory.veryDense_objPrimes_of_minimalPrimes
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.FamGlue
open ShapePull ThetaClosed

theorem exists_spMap {R R' : Type} [CommRing R] [CommRing R'] (x : Sp R' ⟶ Sp R) : ∃ φ : R →+* R', spMap φ = x := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective x
  exact ⟨φ.hom, rfl⟩

theorem exists_geomPt {S : Scheme.{0}} (p : S) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (y : Sp K ⟶ S), p ∈ Set.range y :=
  ⟨AlgebraicClosure (S.residueField p), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField p) (AlgebraicClosure (S.residueField p)))) ≫
      S.fromSpecResidueField p, IsLocalRing.closedPoint _, Scheme.fromSpecResidueField_apply p _⟩

theorem range_spMap_field {R K : Type} [CommRing R] [Field K] (y : R →+* K) :
    Set.range (spMap y) = {(⟨RingHom.ker y, RingHom.ker_isPrime y⟩ : PrimeSpectrum R)} := by
  have h : ∀ p : Sp K, spMap y p = (⟨RingHom.ker y, RingHom.ker_isPrime y⟩ : PrimeSpectrum R) := fun p => by
    have hp : (show PrimeSpectrum K from p).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    refine PrimeSpectrum.ext ?_
    show Ideal.comap y (show PrimeSpectrum K from p).asIdeal = _
    rw [hp]; rfl
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨IsLocalRing.closedPoint K, h _⟩, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact h p

theorem exists_away_lift {X : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (x : Sp R ⟶ X) (x' : Sp R' ⟶ X)
    [IsOpenImmersion x'] (p : PrimeSpectrum R) (hp : x p ∈ Set.range x') :
    ∃ f ∉ p.asIdeal, ∃ z : R' →+* Localization.Away f,
      spMap z ≫ x' = spMap (algebraMap R (Localization.Away f)) ≫ x := by
  obtain ⟨_, ⟨f, rfl⟩, hf, hle⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (u := x ⁻¹' Set.range x') hp (x'.isOpenEmbedding.isOpen_range.preimage x.continuous)
  have h : Set.range (spMap (algebraMap R (Localization.Away f)) ≫ x) ⊆ Set.range x' := by
    rintro _ ⟨q, rfl⟩
    exact hle ((PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).le ⟨q, rfl⟩)
  obtain ⟨z, hz⟩ := exists_spMap (IsOpenImmersion.lift x' _ h)
  exact ⟨f, hf, z, by rw [hz, IsOpenImmersion.lift_fac]⟩

theorem span_eq_top_of_coset {g n N' : ℕ} {R : Type} [CommRing R] {v : Ix g (N' ^ 2) → R}
    (h : ∀ q : Ideal R, q.IsPrime → Coset n N' v q) : Ideal.span (Set.range v) = ⊤ := by
  by_contra h'
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h'
  obtain ⟨c, hc⟩ := h m hm.isPrime 0
  exact hc (hle (Ideal.subset_span ⟨_, rfl⟩))

section General

variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k}
  {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ}

theorem tpull {S S' : Scheme.{0}} {s : S ⟶ Sp o} (t : TObj g k J b s) (f : S' ⟶ S) (s' : S' ⟶ Sp o) (e : f ≫ s = s') :
    ∃ t' : TObj g k J b s', TMap t' t f := T.exists_thetaLevelAbelianScheme_pullback o g k J b S S' s s' f t e

theorem tcomp {S S' S'' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {s'' : S'' ⟶ Sp o} {t : TObj g k J b s}
    {t' : TObj g k J b s'} {t'' : TObj g k J b s''} {f : S' ⟶ S} {f' : S'' ⟶ S'} {f'' : S'' ⟶ S} (h : TMap t' t f)
    (e : f' ≫ f = f'') : TMap t'' t' f' ↔ TMap t'' t f'' :=
  e ▸ (T.thetaLevelPullback_id_comp_cancel o g k J b S S' S'' s s' s'' t t' t'').2 f f' h

theorem shape_pull {S S' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {t : TObj g k J b s}
    {t' : TObj g k J b s'} {f : S' ⟶ S} (h : TMap t' t f) (H : t.Shape Mat κ) : t'.Shape Mat κ := fun j =>
  (shape_prim_pull_and_descend o g k J b Mat κ j j S S' s s' f t t' h).1 H j

theorem retype {S : Scheme.{0}} {s s' : S ⟶ Sp o} (e : s = s') (t : TObj g k J b s) : ∃ t' : TObj g k J b s',
    (∀ (S₀ : Scheme.{0}) (s₀ : S₀ ⟶ Sp o) (u : TObj g k J b s₀) f, TMap t u f → TMap t' u f) ∧
    ∀ (S₀ : Scheme.{0}) (s₀ : S₀ ⟶ Sp o) (u : TObj g k J b s₀) f, TMap u t f → TMap u t' f := by
  subst e
  exact ⟨t, fun _ _ _ _ h => h, fun _ _ _ _ h => h⟩

theorem shape_of_fibres (h₁ : Out.Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] [IsReduced S] {s : S ⟶ Sp o}
    (t : TObj g k J b s) (H : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S),
      ∃ t' : TObj g k J b (y ≫ s), TMap t' t y ∧ t'.Shape Mat κ) : t.Shape Mat κ := by
  intro j
  have := t.ab.proper
  refine ⟨fun i => ?_, T.relAmple_of_ample_geometricFibres_abelianScheme h₁ S t.pol _ (DVR.linComb_isLB _ t.isLB _ _) fun K _ _ y => ?_⟩
  · refine Over.OverMorphism.ext (hom_ext_of_geometricPoints_dense (X := S) t.A.hom _ _
      ((Over.w _).trans (Over.w _).symm) Set.univ dense_univ fun K _ _ y _ => ?_)
    obtain ⟨t', ⟨φ, h, hL, hpt, hact⟩, hs⟩ := H K y
    have pt : ∀ i, pushPt h.1.w (t'.pt i) = baseMap y ≫ t.pt i := fun i => Over.OverMorphism.ext (hpt i)
    have p₁ := push_comp h _ (pt i) (hact j)
    have p₂ : ∀ a, pushPt h.1.w (t'.lab a) = baseMap y ≫ t.lab a := fun a => push_linComb h _ pt _
    rw [(hs j).1 i, p₂] at p₁
    exact congrArg (fun q => q.left) p₁.symm
  · obtain ⟨t', ⟨φ, h, hL, hpt, hact⟩, hs⟩ := H K y
    have i₁ : LBIso (LB.LinComb t'.L (K := Fin 2) ![𝟙 t'.A.left, (t'.act j).left] ![(κ : ℤ), -1])
        ((LB.LinComb t.L (K := Fin 2) ![𝟙 t.A.left, (t.act j).left] ![(κ : ℤ), -1]).pull φ) :=
      iso_linComb_pull hL _ _ _ φ fun i => by
        fin_cases i
        exacts [(Category.id_comp _).trans (Category.comp_id _).symm, hact j]
    obtain ⟨e, he, he'⟩ := grpPullback_iso (isGrpPullback_pullback t.A y) h
    exact (pol_pull _ _ t'.A ((Over.pullback y).obj t.A) (𝟙 _) e.hom.left _ _ (DVR.linComb_isLB _ t'.isLB _ _)
      (pull_isLB (DVR.linComb_isLB _ t.isLB _ _) _) t'.ab (isGrpPullback_of_iso e)
      (i₁.symm.chartPull (chartPullSame _ _ _ _ e.hom.left fun _ => he'.symm) (Geo.Tor.chartPullPull _ _ _ rfl))).2.1 (hs j).2

theorem shape_of_minimalPrimes (h₁ : Out.Laws) (h₂ : Out.Laws2) {R : Type} [CommRing R] [IsNoetherianRing R]
    [_root_.IsReduced R] {s : Sp R ⟶ Sp o} (t : TObj g k J b s)
    (H : ∀ q ∈ minimalPrimes R, ∃ (K : Type) (_ : Field K) (y : R →+* K) (s' : Sp K ⟶ Sp o) (t' : TObj g k J b s'),
      RingHom.ker y = q ∧ TMap t' t (spMap y) ∧ t'.Shape Mat κ) : t.Shape Mat κ := by
  refine shape_of_fibres h₁ t fun K _ _ x => ?_
  obtain ⟨x, rfl⟩ := exists_spMap x
  have := RingHom.ker_isPrime x
  obtain ⟨q, hq, hle⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := RingHom.ker x) bot_le
  obtain ⟨K', _, y, s', t', rfl, hm, hs⟩ := H q hq
  have := RingHom.ker_isPrime y
  obtain ⟨tq, htq⟩ := tpull t (spMap (Ideal.Quotient.mk (RingHom.ker y))) _ rfl
  have hq : tq.Shape Mat κ := by
    refine T.thetaLevelShape_of_generic_point h₁ h₂ o g k J b Mat κ _ _ tq K' (spMap (RingHom.kerLift y)) s' t' ?_
      ((tcomp htq ((spMap_comp' _ _).trans (congrArg spMap (RingHom.ext fun r => RingHom.kerLift_mk y r)))).2 hm) hs
    rw [range_spMap_field, genericPoint_eq_bot_of_affine]
    congr 1
    exact PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot _).1 (RingHom.kerLift_injective y))
  have e : spMap (Ideal.Quotient.lift (RingHom.ker y) x hle) ≫ spMap (Ideal.Quotient.mk (RingHom.ker y)) = spMap x :=
    (spMap_comp' _ _).trans (congrArg spMap (RingHom.ext fun r => rfl))
  obtain ⟨u, hu⟩ := tpull tq (spMap (Ideal.Quotient.lift (RingHom.ker y) x hle)) (spMap x ≫ s)
    (by rw [← Category.assoc, e])
  exact ⟨u, (tcomp htq e).1 hu, shape_pull hu hq⟩

theorem dense_fromSet {em : o →+* ℂ} {C : TObj g k J b (spMap em) → Prop} {S : Scheme.{0}} {s : S ⟶ Sp o}
    (t₀ : TObj g k J b s) (H : ∀ p : S, ∃ (S' : Scheme.{0}) (x : S' ⟶ S) (t : TObj g k J b (x ≫ s)),
      p ∈ Set.range x ∧ TMap t t₀ x ∧ Dense (fromSet em C t)) : Dense (fromSet em C t₀) := by
  intro p
  obtain ⟨S', x, t, ⟨p, rfl⟩, ht, hd⟩ := H p
  refine closure_mono ?_ (image_closure_subset_closure_image x.continuous ⟨p, hd p, rfl⟩)
  rintro _ ⟨_, ⟨K, _, y, ⟨p, rfl⟩, K₀, _, β, i, j, u₀, tx, tc, a₁, a₂, a₃, a₄, a₅, a₆⟩, rfl⟩
  obtain ⟨tx', c, -⟩ := retype (Category.assoc y x s).symm tx
  exact ⟨K, _, y ≫ x, ⟨p, rfl⟩, K₀, _, β, i, j, u₀, tx', tc, a₁, (Category.assoc _ _ _).trans a₂,
    (tcomp ht rfl).1 (c _ _ _ _ a₃), c _ _ _ _ a₄, a₅, a₆⟩

end General

section Theta

variable {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
  {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ}

theorem hasTh_iff {S S' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {t : TObj g (N' ^ 2) J b s}
    {t' : TObj g (N' ^ 2) J b s'} {f : S' ⟶ S} (h : TMap t' t f) {R : Type} [CommRing R] {x : Sp R ⟶ S'}
    {x' : Sp R ⟶ S} (e : x ≫ f = x') (v : Ix g (N' ^ 2) → R) : t'.HasTh x v ↔ t.HasTh x' v :=
  e ▸ T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b S s t S' s' t' f R x v h

theorem hasTh_pull (h₂ : Out.Laws2) {R R' : Type} [CommRing R] [CommRing R'] {φ : R →+* R'} {s : Sp R ⟶ Sp o}
    {s' : Sp R' ⟶ Sp o} {t : TObj g (N' ^ 2) J b s} {t' : TObj g (N' ^ 2) J b s'} (h : TMap t' t (spMap φ))
    {v : Ix g (N' ^ 2) → R} (H : t.HasTh (𝟙 _) v) : t'.HasTh (𝟙 _) (fun a => φ (v a)) :=
  (hasTh_iff h ((Category.id_comp _).trans (Category.comp_id _).symm) _).2 (T.hasThetaConstants_ring_baseChange h₂ o g N' J b _ s t R R' φ _ v H)

theorem hasTh_iff_secCoord (h₁ : Out.Laws) (h₂ : Out.Laws2) (ho : Odd N') (h2 : 2 ≤ N') {X : Scheme.{0}} {s : X ⟶ Sp o}
    (t : TObj g (N' ^ 2) J b s) (M : LB X) (hM : M.IsLB) (th : Ix g (N' ^ 2) → M.Sec)
    (H : ∀ p : X, ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (v : Ix g (N' ^ 2) → R),
      IsOpenImmersion x ∧ p ∈ Set.range x ∧ SecCoord M th x v ∧ t.HasTh x v)
    (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : Ix g (N' ^ 2) → R) : t.HasTh x v ↔ SecCoord M th x v := by
  have sp : ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : Ix g (N' ^ 2) → R), t.HasTh x v →
      Ideal.span (Set.range v) = ⊤ := fun R _ x v h => span_eq_top_of_coset fun q hq =>
    T.thetaCosetNonvanishing_of_hasTh h₁ h₂ o g N' J b X s t N' R x v q h2 dvd_rfl h hq
  have key : ∀ p : PrimeSpectrum R, ∃ f ∉ p.asIdeal, ∃ w,
      SecCoord M th (spMap (algebraMap R (Localization.Away f)) ≫ x) w ∧
      t.HasTh (spMap (algebraMap R (Localization.Away f)) ≫ x) w := fun p => by
    obtain ⟨R', _, x', v', _, hp, a, c⟩ := H (x p)
    obtain ⟨f, hf, z, e⟩ := exists_away_lift x x' p hp
    exact ⟨f, hf, fun i => z (v' i), e ▸ (Coord.secCoord_bc_scale_unique X M _ th R' x' v' hM a).1 _ z,
      e ▸ T.hasThetaConstants_ring_baseChange h₂ o g N' J b X s t R' _ z x' v' c⟩
  refine ⟨fun h => T.isSectionCoordinateVector_of_locally_on_ring X M _ th R x v hM (sp R x v h) fun p => ?_,
    fun h => hasTh_of_local t ho fun q hq => ?_⟩
  · obtain ⟨f, hf, w, a, c⟩ := key p
    refine ⟨Localization.Away f, inferInstance, algebraMap R _, inferInstance,
      (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).ge hf, ?_⟩
    obtain ⟨u, hu⟩ := T.thetaConstants_unique_up_to_unit h₁ h₂ o g N' J b X s t _ _ w _ c
      (T.hasThetaConstants_ring_baseChange h₂ o g N' J b X s t R _ (algebraMap R (Localization.Away f)) x v h) (sp _ _ _ c)
    rw [funext hu]
    exact (Coord.secCoord_bc_scale_unique X M _ th _ _ w hM a).2.1 u
  · obtain ⟨f, hf, w, a, c⟩ := key ⟨q, hq⟩
    refine ⟨f, hf, ?_⟩
    obtain ⟨u, hu⟩ := (Coord.secCoord_bc_scale_unique X M _ th _ _ w hM a).2.2 _
      ((Coord.secCoord_bc_scale_unique X M _ th R x v hM h).1 _ (algebraMap R (Localization.Away f)))
    rw [funext hu]
    exact hasTh_unit_mul t u c

theorem exists_glued (h₁ : Out.Laws) (h₂ : Out.Laws2) (ho : Odd N') {m : ℕ} (hm : 2 ≤ m) (hm' : m ^ 2 ∣ N')
    {em : o →+* ℂ} {C : TObj g (N' ^ 2) J b (spMap em) → Prop} {X : Scheme.{0}} [IsReduced X] [IsLocallyNoetherian X]
    (s : X ⟶ Sp o) (M : LB X) (hM : M.IsLB) (th : Ix g (N' ^ 2) → M.Sec)
    (H : ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : Ix g (N' ^ 2) → R), IsOpenImmersion x → SecCoord M th x v →
      ∃ t : TObj g (N' ^ 2) J b (x ≫ s), Dense (fromSet em C t) ∧ t.Shape Mat κ ∧ t.HasTh (𝟙 _) v ∧
        ∀ (K : Type) [Field K] [IsAlgClosed K] (z : R →+* K) (t' : TObj g (N' ^ 2) J b (spMap z ≫ x ≫ s)),
          t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => z (v a)) → TMap t' t (spMap z)) :
    ∃ t : TObj g (N' ^ 2) J b s, Dense (fromSet em C t) ∧ t.Shape Mat κ ∧
      (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : Ix g (N' ^ 2) → R), t.HasTh x v ↔ SecCoord M th x v) ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X) (t' : TObj g (N' ^ 2) J b (x ≫ s)) v,
        t'.Shape Mat κ → t'.HasTh (𝟙 _) v → SecCoord M th x v → TMap t' t x := by
  choose R iR x v hx hp hv using (T.sectionCoordinateVector_exists_locally X M _ th hM).2.2
  choose t hd hs ht hu using fun p => H (R p) (x p) (v p) (hx p) (hv p)
  have uniq : ∀ (p : X) (K : Type) [Field K] [IsAlgClosed K] (z : Sp K ⟶ Sp (R p)) (s' : Sp K ⟶ Sp o)
      (t' : TObj g (N' ^ 2) J b s') (y : Sp K ⟶ X) w, z ≫ x p = y → s' = y ≫ s → t'.Shape Mat κ → t'.HasTh (𝟙 _) w →
      SecCoord M th y w → TMap t' (t p) z := by
    intro p K _ _ z s' t' y w e e' a c d
    obtain ⟨z, rfl⟩ := exists_spMap z
    subst e
    rw [Category.assoc] at e'
    subst e'
    obtain ⟨u, hu'⟩ := (Coord.secCoord_bc_scale_unique X M _ th _ _ w hM d).2.2 _
      ((Coord.secCoord_bc_scale_unique X M _ th _ _ _ hM (hv p)).1 _ z)
    refine hu p K z t' a ?_
    rw [funext hu']
    exact hasTh_unit_mul t' u c
  have lift : ∀ (K : Type) [Field K] (y : Sp K ⟶ X), ∃ (p : X) (z : Sp K ⟶ Sp (R p)), z ≫ x p = y := fun K _ y => by
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    have := hx (y (IsLocalRing.closedPoint K))
    refine ⟨y (IsLocalRing.closedPoint K), IsOpenImmersion.lift _ y ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨q, rfl⟩
    rw [Subsingleton.elim q (IsLocalRing.closedPoint K)]
    exact hp _
  obtain ⟨t₀, h₀⟩ := T.exists_thetaLevelAbelianScheme_glue_affineCover h₁ h₂ o g N' J b m X s X R x t hm hm' ho hx (fun p => ⟨p, hp p⟩) (by
    intro i i' A _ a a' u ha e hu₁
    have := hx i
    have : IsReduced (Sp A) := isReduced_of_isOpenImmersion (a ≫ x i)
    have : _root_.IsReduced A := (affine_isReduced_iff (CommRingCat.of A)).1 this
    have e₁ : a' ≫ x i' ≫ s = a ≫ x i ≫ s := by rw [← Category.assoc, ← e, Category.assoc]
    generalize hs' : a ≫ x i ≫ s = s' at u e₁ hu₁
    obtain ⟨β, rfl⟩ := exists_spMap s'
    obtain ⟨u', hu'⟩ := tpull (t i') a' _ e₁
    refine (tcomp hu' (Category.id_comp _)).1
      (T.thetaLevel_iso_unique_of_dense_common_fibres h₁ h₂ o g N' J b m A β u u' hm hm' ho (Dense.mono (fun p _ => ?_) dense_univ)).1
    obtain ⟨K, _, _, y, hy⟩ := exists_geomPt p
    obtain ⟨w, hw⟩ := tpull u y _ rfl
    refine ⟨K, _, y, w, hy, hw, (tcomp hu' rfl).2 ?_⟩
    obtain ⟨z, hz⟩ := exists_spMap (y ≫ a)
    have hw' := (tcomp hu₁ hz.symm).1 hw
    exact uniq i' K (y ≫ a') _ w (spMap z ≫ x i) _ (by rw [hz, Category.assoc, Category.assoc, e])
      (by rw [hz, ← hs']; simp only [Category.assoc]) (shape_pull hw' (hs i)) (hasTh_pull h₂ hw' (ht i))
      ((Coord.secCoord_bc_scale_unique X M _ th _ _ _ hM (hv i)).1 _ z))
  refine ⟨t₀, dense_fromSet t₀ fun p => ⟨_, x p, t p, hp p, h₀ p, hd p⟩, shape_of_fibres h₁ t₀ fun K _ _ y => ?_,
    hasTh_iff_secCoord h₁ h₂ ho ?_ t₀ M hM th fun p => ⟨R p, _, x p, v p, hx p, hp p, hv p,
      (hasTh_iff (h₀ p) (Category.id_comp _) _).1 (ht p)⟩, fun K _ _ y t' w a c d => ?_⟩
  · obtain ⟨p, z, e⟩ := lift K y
    obtain ⟨u, hu'⟩ := tpull (t p) z (y ≫ s) (by rw [← Category.assoc, e])
    exact ⟨u, (tcomp (h₀ p) e).1 hu', shape_pull hu' (hs p)⟩
  · exact le_trans (by nlinarith) (Nat.le_of_dvd ho.pos hm')
  · obtain ⟨p, z, e⟩ := lift K y
    exact (tcomp (h₀ p) e).1 (uniq p K z _ t' y w e rfl a c d)

end Theta

end GlobalTheory.FamGlue

namespace GlobalTheory.ZM
open FamGlue ThetaClosed

theorem exists_family_over_MMPre : Out.Laws → Out.Laws2 → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ Y : MMPre n (n ^ j) (thIdeal em C), ∃ t : TObj g ((n ^ j) ^ 2) J b Y.s, Dense (fromSet em C t) ∧ t.Shape Mat κ ∧ (∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y.MM) (v : Ix g ((n ^ j) ^ 2) → R), t.HasTh x v ↔ SecCoord Y.de Y.th x v) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Y.MM) (t' : TObj g ((n ^ j) ^ 2) J b (x ≫ Y.s)) v, t'.Shape Mat κ → t'.HasTh (𝟙 _) v → SecCoord Y.de Y.th x v → TMap t' t x := by
  intro h₁ h₂ crit g J _ Mat κ n w w' hn ho
  obtain ⟨j₁, H₁⟩ := T.exists_theta_family_from_very_dense_points h₁ h₂ g J Mat κ n hn ho
  obtain ⟨j₂, H₂⟩ := T.veryDense_closedPoint_objects_of_minimalPrimes h₁ h₂ crit g J Mat κ n w w' hn ho
  obtain ⟨j₃, H₃⟩ := T.exists_generic_object_minimalPrime_moduli_chart h₁ h₂ g J Mat κ n w w' hn ho
  refine ⟨max (max j₁ j₂) (max j₃ 2), fun j hj o _ b em C d hb hC Y => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hj
  have : IsDedekindDomain o := hb.1
  have := Y.reduced
  have := Y.flat
  have lft : LocallyOfFiniteType Y.s := by
    obtain ⟨N, i, hi, -, e⟩ := Y.qproj
    have := isProper_str o N
    rw [← e]; infer_instance
  have : IsLocallyNoetherian Y.MM := LocallyOfFiniteType.isLocallyNoetherian Y.s
  refine exists_glued h₁ h₂ ho.pow hn.two_le (pow_dvd_pow n hj.2.2) Y.s Y.de Y.isLB Y.th fun R _ x v hx hv => ?_
  have hred : _root_.IsReduced R := (affine_isReduced_iff (CommRingCat.of R)).1 (isReduced_of_isOpenImmersion x)
  have a₁ : LocallyOfFiniteType (x ≫ Y.s) := inferInstance
  have a₂ : Flat (x ≫ Y.s) := inferInstance
  generalize hs : x ≫ Y.s = s at a₁ a₂
  obtain ⟨β, rfl⟩ := exists_spMap s
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at a₁
  rw [HasRingHomProperty.Spec_iff (P := @Flat)] at a₂
  letI := β.toAlgebra
  have ft : Algebra.FiniteType o R := a₁
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing o R
  have gen := H₃ j hj.2.1 o b em C d hb hC Y R β x v hx hs hv
  obtain ⟨t, ht, hu⟩ := H₁ j hj.1.1 o b R β v (H₂ j hj.1.2 o b em C d hb hC R v ft hred a₂ (Y.loc R β x v hs hv)
    fun q hq => by
      obtain ⟨K, _, y, e, tq, tc, c₁, -, -, -, c₂, c₃, c₄⟩ := gen q hq
      exact ⟨K, _, y, tq, c₁, c₂, c₃, c₄⟩)
  have gen' : ∀ q ∈ minimalPrimes R, ∃ (K : Type) (_ : Field K) (y : R →+* K)
      (t' : TObj g ((n ^ j) ^ 2) J b (spMap y ≫ spMap β)), RingHom.ker y = q ∧ TMap t' t (spMap y) ∧ t'.Shape Mat κ ∧
        FromC em C t (spMap y) := fun q hq => by
    obtain ⟨K, _, y, e, tq, tc, c₁, c₂, c₃, c₄, c₅, -, c₆⟩ := gen q hq
    let i := algebraMap K (AlgebraicClosure K)
    obtain ⟨t', ht'⟩ := tpull tq (spMap i) (spMap (i.comp y) ≫ spMap β) (by rw [← Category.assoc, spMap_comp'])
    have hm := hu _ (i.comp y) t' (shape_pull ht' c₅) (hasTh_pull h₂ ht' c₆)
    obtain ⟨t₀, -, h₀⟩ := retype (spMap_comp' β y) tq
    refine ⟨_, inferInstance, i.comp y, t', ?_, hm, shape_pull ht' c₅, K, _, y.comp β, i, e, t₀, t', tc, c₂, ?_, hm,
      h₀ _ _ _ _ ht', h₀ _ _ _ _ c₄, c₃⟩
    · rw [← c₁, ← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot i).1 i.injective]
      rfl
    · rw [spMap_comp', spMap_comp', RingHom.comp_assoc]
  refine ⟨t, fun p => ?_, shape_of_minimalPrimes h₁ h₂ t fun q hq => ?_, ht, hu⟩
  · obtain ⟨q, hq, hle⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := (show PrimeSpectrum R from p).asIdeal) bot_le
    obtain ⟨K, _, y, t', rfl, -, -, c⟩ := gen' q hq
    refine closure_mono (s := {(⟨RingHom.ker y, RingHom.ker_isPrime y⟩ : PrimeSpectrum R)}) ?_
      ((PrimeSpectrum.le_iff_mem_closure _ _).1 hle)
    rintro _ rfl
    exact ⟨K, _, spMap y, (range_spMap_field y).ge rfl, c⟩
  · obtain ⟨K, _, y, t', c₁, c₂, c₃, -⟩ := gen' q hq
    exact ⟨K, _, y, _, t', c₁, c₂, c₃⟩

end GlobalTheory.ZM
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaFamily_over_thetaPointScheme : Out.Laws → Out.Laws2 → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ Y : MMPre n (n ^ j) (thIdeal em C), ∃ t : TObj g ((n ^ j) ^ 2) J b Y.s, Dense (fromSet em C t) ∧ t.Shape Mat κ ∧ (∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y.MM) (v : Ix g ((n ^ j) ^ 2) → R), t.HasTh x v ↔ SecCoord Y.de Y.th x v) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Y.MM) (t' : TObj g ((n ^ j) ^ 2) J b (x ≫ Y.s)) v, t'.Shape Mat κ → t'.HasTh (𝟙 _) v → SecCoord Y.de Y.th x v → TMap t' t x := by
  first | exact @GlobalTheory.ZM.exists_family_over_MMPre | exact GlobalTheory.ZM.exists_family_over_MMPre | (intros; apply GlobalTheory.ZM.exists_family_over_MMPre <;> assumption)
end
