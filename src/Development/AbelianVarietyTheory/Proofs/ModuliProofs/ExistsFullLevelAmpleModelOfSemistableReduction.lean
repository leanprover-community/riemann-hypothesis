import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelSplitSpecialFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaUniformisationComplexAbelianVarietiesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationExistenceAndTorsionStatementsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ZarhinGeometricOfSemistableReduction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRingStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSectionOfDense
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenWeilIsIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfLbIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPELPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectFibreFromComplexCharZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmFamilyFiniteUnramifiedOverSiegelFamilyStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyAmpleFramedModelPELThetaFamily
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.DenseGenericOfFlat
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCyclotomicBaseRingInvertingPrime
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptySiegelFamilyOverArithmeticBaseStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelFamilyLocalisedCyclotomicIntegersStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFullLevelModelOfFamilyBirationalModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyPelSmoothGenericFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantValuationsUnitsEveryCosetStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPrimGenerator
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicBaseEmbedsValuationAlgebraicClosure
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoUniformisationsOfIsoDegenerationDataStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegDataIsPullDeg
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatementsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelEndomorphismsSpreadOverBasicOpen
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AbelianSchemeHomExtendsDedekindOfIsGrpPullbackAl
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianHomExtensionOfLaws
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaConstantsLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnitStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasThStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SmoothOfRelativeDimensionOfFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel

section
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SS

theorem semistablePol_of_padic : GlobalTheory.Published.SemistableReductionSt → GlobalTheory.SS.SemistablePol := by
  intro H V K _ _ _ _ _ _ _ _ hfin A
  obtain ⟨p, hp, K₀, e, e₀, hK₀, he⟩ := GlobalTheory.completeDVR_eq_integralClosure_padicInt.1 V K hfin
  obtain ⟨P, ψ, hψ⟩ : ∃ (P : PolAV (Sp K₀)) (ψ : P.A.left ⟶ A.A.left),
      IsGrpPullback P.A A.A (spMap e.toRingHom) ψ := by
    obtain ⟨P', g, hg, -, hm, -⟩ := GlobalTheory.polBaseChange_holds _ _ (spMap e.toRingHom) A
    refine ⟨P', g, hg, fun T x y x₀ y₀ hx hy => ?_⟩
    rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hg.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hg.w y), ← hm]
    rfl
  obtain ⟨K', h, hloc, hK', G, gG, hG, hE, φ, hφ⟩ :=
    GlobalTheory.exists_semiAbelian_model_split_specialFibre H p K₀ P
  obtain ⟨hdvr, hfr, hc, f, hf, hlf, hfx⟩ := GlobalTheory.completeDVR_eq_integralClosure_padicInt.2 p K₀ K' h hK'
  letI aV : Algebra V (integralClosure ℤ_[p] K') := (f.comp e₀.toRingHom).toAlgebra
  letI aK : Algebra K K' := ((IntermediateField.inclusion h).toRingHom.comp e.toRingHom).toAlgebra
  refine ⟨integralClosure ℤ_[p] K', K', inferInstance, inferInstance, hdvr, inferInstance, aV, inferInstance, aK, hfr,
    ?_, ?_, ?_, hc, G, gG, ?_, hG, hE⟩
  · ext1 x
    change ((f (e₀ x) : integralClosure ℤ_[p] K') : K') = IntermediateField.inclusion h (e (algebraMap V K x))
    rw [hfx, he]
  · exact RingHom.Finite.comp hf (RingHom.Finite.of_surjective _ e₀.surjective)
  · haveI : IsLocalHom e₀.toRingHom := isLocalHom_of_leftInverse e₀.symm.toRingHom e₀.left_inv
    exact RingHom.isLocalHom_comp f e₀.toRingHom
  · obtain ⟨i, hi, -⟩ := grpPullback_iso
      ((hφ.comp hψ).congr (GlobalTheory.SplitReduction.spMap_comp _ _) rfl)
      (isGrpPullback_pullback A.A (spMap (algebraMap K K')))
    exact ⟨i, hi⟩

end GlobalTheory.SS
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistableReductionSplit_of_padic : GlobalTheory.Published.SemistableReductionSt → GlobalTheory.SS.SemistablePol := by
  atlas_forward_decl GlobalTheory.SS.semistablePol_of_padic
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.CharZeroPts

theorem exists_generization {o : Type} [CommRing o] [IsDomain o] [CharZero o] {S : Scheme.{0}} (s : S ⟶ Sp o) [Flat s]
    (p : S) : ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ S) (β : o →+* K),
      x ≫ s = spMap β ∧ ∀ u, x u ⤳ p := by
  let ξ : Sp o := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum o)
  have hξ : ξ ⤳ s p := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨q, hq, hq'⟩ := Flat.generalizingMap s hξ
  obtain ⟨K, _, _, x, hx⟩ := FinEt.exists_algClosed_point S q
  have hx' : ∀ u, x u = q := fun u => by
    have : x u ∈ Set.range x := ⟨u, rfl⟩
    rwa [hx] at this
  let β : o →+* K := (Spec.preimage (x ≫ s)).hom
  have hβ : x ≫ s = spMap β := (Spec.map_preimage (x ≫ s)).symm
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have e : spMap β (default : PrimeSpectrum K) = ξ := by
      rw [← hβ]
      exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg s (hx' _)).trans hq')
    have e' : a ∈ (spMap β (default : PrimeSpectrum K)).asIdeal := by
      show β a ∈ (default : PrimeSpectrum K).asIdeal
      rw [ha]; exact zero_mem _
    rw [e] at e'
    exact e'
  exact ⟨K, inferInstance, inferInstance, charZero_of_injective_ringHom hinj, x, β, hβ, fun u => (hx' u).symm ▸ hq⟩

variable {S : Scheme.{0}}

abbrev toB {T : Scheme.{0}} (x : T ⟶ S) : Over.mk x ⟶ Out.baseOver S := Over.homMk x (by simp)

theorem smoothOfRelativeDimension_of_generization {X : Scheme.{0}} (f : X ⟶ S) [Smooth f] [GeometricallyConnected f]
    (g : ℕ) (h : ∀ y : X, ∃ (K : Type) (_ : Field K) (z : Sp K ⟶ X), (∀ u, z u ⤳ y) ∧
      ∀ m, SmoothOfRelativeDimension m (pullback.snd f (z ≫ f)) → m = g) : SmoothOfRelativeDimension g f := by
  choose n W hW hd using H1.exists_dim f
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  obtain ⟨k, _, z, hz, hg⟩ := h y
  have : ConnectedSpace ↥(pullback f (z ≫ f)) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) (z ≫ f) _ _ (IsPullback.of_hasPullback _ _)
  let z' : Sp k ⟶ pullback f (z ≫ f) := pullback.lift z (𝟙 _) (Category.id_comp _).symm
  obtain ⟨m, hm⟩ := exists_dim_of_preconnected (pullback.snd f (z ≫ f)) (z' (default : PrimeSpectrum k))
  have e₁ : n y = m := H1.dim_base (IsPullback.of_hasPullback _ _) (hd y) hm (z' (default : PrimeSpectrum k)) (by
    have e : z' ≫ pullback.fst f (z ≫ f) = z := pullback.lift_fst _ _ _
    have e' := congrArg (fun q : Sp k ⟶ X => q (default : PrimeSpectrum k)) e
    exact (congrArg (fun u => u ∈ W y) e').mpr ((hz _).mem_open (W y).isOpen (hW y)))
  rw [← hg m hm, ← e₁]
  exact hd y

theorem weilIs_of_generization (hL : Out.Laws) (P : Out.PolAV S) (n : ℕ) (x y : Out.baseOver S ⟶ P.A) (c : Γ(S, ⊤)ˣ)
    (hn : 0 < n) (hu : IsUnit (n : Γ(S, ⊤))) (hx : x ^ n = 1) (hy : y ^ n = 1) (hc : c ^ n = 1)
    (h : ∀ p : S, ∃ (K : Type) (_ : Field K) (z : Sp K ⟶ S), (∀ u, z u ⤳ p) ∧
      Out.WeilIs P.A P.L n (toB z ≫ x) (toB z ≫ y) (Units.map z.appTop.hom.toMonoidHom c)) :
    Out.WeilIs P.A P.L n x y c := by
  obtain ⟨U, hU, H⟩ := exists_clopen_weilIs_iff hL S P n (Out.baseOver S) x y c hn hu hx hy hc
  have := (H _ (𝟙 _)).2 (by
    rintro _ ⟨p, rfl⟩
    obtain ⟨K, _, z, hz, hw⟩ := h p
    exact (hz (default : PrimeSpectrum K)).mem_closed hU ((H _ (toB z)).1 hw ⟨_, rfl⟩))
  rw [Category.id_comp, Category.id_comp] at this
  convert this
  ext
  simp

theorem torsion_basis_of_generization (A : Over S) [GrpObj A] (k r : ℕ) (pt : Fin r → (Out.baseOver S ⟶ A))
    (hA : IsAbelianScheme A) (hk : 0 < k) (hu : IsUnit (k : Γ(S, ⊤))) (hpt : ∀ i, pt i ^ k = 1)
    (h : ∀ p : S, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (z : Sp K ⟶ S), (∀ u, z u ⤳ p) ∧
      ∀ y : Over.mk z ⟶ A, y ^ k = 1 →
        ∃! c : Fin r → ZMod k, Out.linComb (fun i => toB z ≫ pt i) (fun i => (c i).val) = y)
    (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A) (hy : y ^ k = 1) :
    ∃! c : Fin r → ZMod k, Out.linComb (fun i => toB x ≫ pt i) (fun i => (c i).val) = y := by
  refine torsion_basis_of_dense S A k r pt _ hA hk hu hpt ?_ (fun p hp => hp) K x y hy
  intro p
  obtain ⟨K, _, _, z, hz, H⟩ := h p
  exact (hz (default : PrimeSpectrum K)).mem_closed isClosed_closure
    (subset_closure ⟨K, inferInstance, inferInstance, z, ⟨_, rfl⟩, H⟩)

end GlobalTheory.CharZeroPts
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.TripleTheta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {g k : ℕ} {J : Type}
  {a : J → 𝓞 E} {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La} {o : Type} [CommRing o] {b : TBase o k} {S S' : Scheme.{0}}
  {s : S ⟶ Sp o} {s' : S' ⟶ Sp o}

def Under (t : SAB H S) (lv : D.La → (𝟙_ (Over S) ⟶ t.G)) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La)
    (T : TObj g k J b s) : Prop :=
  ∃ φ : t.G ≅ T.A, IsMonHom φ.hom ∧ LBIso t.PP.L (T.L.pull φ.hom.left) ∧
    (∀ j, t.act.act (a j) ≫ φ.hom = φ.hom ≫ T.act j) ∧
    ∀ i, (lv (bas (Pi.single i 1))).left ≫ φ.hom.left = (T.pt i).left

theorem lbIso_of_sabMap {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f) :
    LBIso t'.PP.L (t.PP.L.pull m.φ) := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨w, hw⟩

theorem inv_hom_left {A B : Over S} (φ : A ≅ B) : φ.inv.left ≫ φ.hom.left = 𝟙 _ := by
  rw [← Over.comp_left, φ.inv_hom_id, Over.id_left]

theorem hom_inv_left {A B : Over S} (φ : A ≅ B) : φ.hom.left ≫ φ.inv.left = 𝟙 _ := inv_hom_left φ.symm

theorem lbIso_inv {A B : Over S} (φ : A ≅ B) {L : LB A.left} {M : LB B.left}
    (h : LBIso L (M.pull φ.hom.left)) : LBIso M (L.pull φ.inv.left) :=
  (LBIso.chartPull (chartPullId _) (chartPullUnpull M (𝟙 _) rfl)
    (PELPull.lbIso_pull h φ.inv.left (inv_hom_left φ).symm)).symm

theorem tmap_of_sabMap {t : SAB H S} {t' : SAB H S'} {lv : D.La → (𝟙_ (Over S) ⟶ t.G)}
    {lv' : D.La → (𝟙_ (Over S') ⟶ t'.G)} {T : TObj g k J b s} {T' : TObj g k J b s'} (h : Under t lv a bas T)
    (h' : Under t' lv' a bas T') {f : S' ⟶ S} (m : SABMap t' t f) (hl : ∀ x, (lv' x).left ≫ m.φ = f ≫ (lv x).left) :
    TMap T' T f := by
  obtain ⟨φ, hφ, hφL, hφa, hφp⟩ := h
  obtain ⟨ψ, hψ, hψL, hψa, hψp⟩ := h'
  have : IsMonHom ψ.symm.hom := inferInstanceAs (IsMonHom ψ.inv)
  refine ⟨ψ.inv.left ≫ m.φ ≫ φ.hom.left, ?_, ?_, fun i => ?_, fun j => ?_⟩
  · exact ((isGrpPullback_of_iso ψ.symm).comp (m.cart.comp (isGrpPullback_of_iso φ))).congr (by simp) rfl
  · refine (lbIso_inv ψ hψL).trans T'.isLB (pull_isLB t'.PP.isLB _) (pull_isLB T.isLB _) (PELPull.lbIso_pull ?_ _ rfl)
    exact (lbIso_of_sabMap m).trans t'.PP.isLB (pull_isLB t.PP.isLB _) (pull_isLB T.isLB _)
      (PELPull.lbIso_pull hφL m.φ rfl)
  · rw [← hψp, ← hφp, Category.assoc, reassoc_of% hom_inv_left ψ, reassoc_of% hl]
  · have h₁ : (t.act.act (a j)).left ≫ φ.hom.left = φ.hom.left ≫ (T.act j).left := congrArg (fun z => z.left) (hφa j)
    have h₂ : (T'.act j).left ≫ ψ.inv.left = ψ.inv.left ≫ (t'.act.act (a j)).left := by
      rw [← Over.comp_left, ← Over.comp_left]
      congr 1
      rw [Iso.comp_inv_eq, Category.assoc, hψa, Iso.inv_hom_id_assoc]
    have h₃ : (t'.act.act (a j)).left ≫ m.φ = m.φ ≫ (t.act.act (a j)).left := m.act _
    rw [reassoc_of% h₂, reassoc_of% h₃, h₁, Category.assoc, Category.assoc]

theorem under_of_tmap {t : SAB H S} {t' : SAB H S'} {lv : D.La → (𝟙_ (Over S) ⟶ t.G)}
    {lv' : D.La → (𝟙_ (Over S') ⟶ t'.G)} {T : TObj g k J b s} {T' : TObj g k J b s'} (h : Under t lv a bas T)
    {f : S' ⟶ S} (h' : TMap T' T f) (m : SABMap t' t f) (hl : ∀ x, (lv' x).left ≫ m.φ = f ≫ (lv x).left) :
    Under t' lv' a bas T' := by
  obtain ⟨φ, hφ, hφL, hφa, hφp⟩ := h
  obtain ⟨ψ, hψ, hψL, hpt, hact⟩ := h'
  have hc : IsGrpPullback t'.G T.A f (m.φ ≫ φ.hom.left) :=
    (IsGrpPullback.comp m.cart (isGrpPullback_of_iso φ)).congr (Category.comp_id f) rfl
  obtain ⟨e, he, heF⟩ := grpPullback_iso hc hψ
  refine ⟨e, he, ?_, fun j => ?_, fun i => ?_⟩
  · exact ((lbIso_of_sabMap m).trans t'.PP.isLB (pull_isLB t.PP.isLB _) (pull_isLB T.isLB _)
      (PELPull.lbIso_pull hφL m.φ rfl)).trans
      t'.PP.isLB (pull_isLB T.isLB _) (pull_isLB T'.isLB _) (PELPull.lbIso_pull hψL e.hom.left heF.symm).symm
  · apply Over.OverMorphism.ext
    apply hψ.1.hom_ext
    · have h₁ : (t.act.act (a j)).left ≫ φ.hom.left = φ.hom.left ≫ (T.act j).left :=
        congrArg (fun z => z.left) (hφa j)
      have h₂ : (t'.act.act (a j)).left ≫ m.φ = m.φ ≫ (t.act.act (a j)).left := m.act _
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, heF, hact, ← Category.assoc, h₂,
        Category.assoc, h₁, ← Category.assoc, ← heF, Category.assoc]
    · rw [Over.w, Over.w]
  · apply hψ.1.hom_ext
    · rw [Category.assoc, heF, reassoc_of% hl, hφp, hpt]
    · rw [Category.assoc, Over.w, Over.w, Over.w]; rfl

theorem act_zero {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) : act.act 0 = 1 := by
  have := act.add 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem act_neg {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) (c : O) :
    act.act (-c) = (act.act c)⁻¹ := by
  have := act.add (-c) c
  rw [neg_add_cancel, act_zero] at this
  exact eq_inv_of_mul_eq_one_left this.symm

theorem act_comm_of_closure {O : Type} [CommRing O] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] (act : OAct O G)
    (act' : OAct O G') {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {a : J → O}
    (ha : Subring.closure (Set.range a) = ⊤) (hj : ∀ j, (act'.act (a j)).left ≫ φ = φ ≫ (act.act (a j)).left) (c : O) :
    (act'.act c).left ≫ φ = φ ≫ (act.act c).left := by
  let u : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w
  have key : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left ↔ pushHom h G' (act'.act c) = preHom u (act.act c) :=
    fun c => ⟨fun e => Over.OverMorphism.ext e, fun e => congrArg (fun z => z.left) e⟩
  have hc : c ∈ Subring.closure (Set.range a) := ha ▸ Subring.mem_top c
  induction hc using Subring.closure_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hj j
  | zero => rw [key, act_zero, act_zero, map_one, map_one]
  | one => rw [act.one, act'.one, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
  | add x y _ _ hx hy => rw [key] at hx hy ⊢; rw [act.add, act'.add, map_mul, map_mul, hx, hy]
  | neg x _ hx => rw [key] at hx ⊢; rw [act_neg, act_neg, map_inv, map_inv, hx]
  | mul x y _ _ hx hy => rw [act.mul, act'.mul, Over.comp_left, Over.comp_left, Category.assoc, hy, reassoc_of% hx]

theorem eq_of_basis {A : Type} [CommGroup A] (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (u v : D.La → A)
    (hu : ∀ x y, u (x + y) = u x * u y) (hv : ∀ x y, v (x + y) = v x * v y)
    (h : ∀ i, u (bas (Pi.single i 1)) = v (bas (Pi.single i 1))) (x : D.La) : u x = v x := by
  let u' : D.La →+ Additive A := AddMonoidHom.mk' (fun x => Additive.ofMul (u x)) fun x y => by rw [hu]; rfl
  let v' : D.La →+ Additive A := AddMonoidHom.mk' (fun x => Additive.ofMul (v x)) fun x y => by rw [hv]; rfl
  have : u'.comp bas.toLinearMap.toAddMonoidHom = v'.comp bas.toLinearMap.toAddMonoidHom := by
    refine AddMonoidHom.functions_ext' _ _ _ fun i => AddMonoidHom.ext_int ?_
    exact congrArg Additive.ofMul (h i)
  have e := DFunLike.congr_fun this (bas.symm x)
  simpa [u', v'] using e

theorem sabMap_of_tmap {t : SAB H S} {t' : SAB H S'} {lv : D.La → (𝟙_ (Over S) ⟶ t.G)}
    {lv' : D.La → (𝟙_ (Over S') ⟶ t'.G)} {T : TObj g k J b s} {T' : TObj g k J b s'} (h : Under t lv a bas T)
    (h' : Under t' lv' a bas T') (hlv : ∀ x y, lv (x + y) = lv x * lv y) (hlv' : ∀ x y, lv' (x + y) = lv' x * lv' y)
    (ha : Subring.closure (Set.range a) = ⊤) (hS : IsReduced S') (hp : IsProper t'.G.hom) {f : S' ⟶ S}
    (m : TMap T' T f) : ∃ ν : SABMap t' t f, ∀ x, (lv' x).left ≫ ν.φ = f ≫ (lv x).left := by
  obtain ⟨φ, hφ, hφL, hφa, hφp⟩ := h
  obtain ⟨ψ, hψ, hψL, hψa, hψp⟩ := h'
  obtain ⟨χ, hχ, hχL, hpt, hact⟩ := m
  have : IsMonHom φ.symm.hom := inferInstanceAs (IsMonHom φ.inv)
  have hc : IsGrpPullback t'.G t.G f (ψ.hom.left ≫ χ ≫ φ.inv.left) :=
    ((isGrpPullback_of_iso ψ).comp (hχ.comp (isGrpPullback_of_iso φ.symm))).congr (by simp) rfl
  obtain ⟨ν, hν⟩ := exists_sabMap_of_lbIso E H S S' t t' f _ ⟨hS, fun _ _ _ _ _ _ _ => inferInstance⟩ hc
    (act_comm_of_closure t.act t'.act hc ha fun j => by
      have h₁ : (t'.act.act (a j)).left ≫ ψ.hom.left = ψ.hom.left ≫ (T'.act j).left :=
        congrArg (fun z => z.left) (hψa j)
      have h₂ : (T.act j).left ≫ φ.inv.left = φ.inv.left ≫ (t.act.act (a j)).left := by
        rw [← Over.comp_left, ← Over.comp_left]
        congr 1
        rw [Iso.comp_inv_eq, Category.assoc, hφa, Iso.inv_hom_id_assoc]
      rw [reassoc_of% h₁, reassoc_of% hact, h₂, Category.assoc, Category.assoc])
    (hψL.trans t'.PP.isLB (pull_isLB T'.isLB _) (pull_isLB t.PP.isLB _) (PELPull.lbIso_pull
      (hχL.trans T'.isLB (pull_isLB T.isLB _) (pull_isLB t.PP.isLB _) (PELPull.lbIso_pull (lbIso_inv φ hφL) χ rfl)) _ rfl))
  refine ⟨ν, fun x => ?_⟩
  have e := eq_of_basis bas lv' (fun x => ObjPull.secPull hc (lv x)) hlv' (fun x y => by rw [hlv, map_mul])
    (fun i => Over.OverMorphism.ext (hc.1.hom_ext (by
      rw [ObjPull.secPull_left, reassoc_of% hψp, reassoc_of% hpt, ← hφp, Category.assoc, hom_inv_left,
        Category.comp_id]) (by rw [Over.w, Over.w]))) x
  rw [hν, e, ObjPull.secPull_left]

end GlobalTheory.TripleTheta
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.TripleTheta

open CharZeroPts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {g : ℕ} {J : Type}

theorem map_bas {A : Type} [CommGroup A] (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (u : D.La → A)
    (hu : ∀ x y, u (x + y) = u x * u y) (v : Fin (2 * g) → ℤ) :
    u (bas v) = ∏ i, u (bas (Pi.single i 1)) ^ v i := by
  rw [LatticeTorsion.eq_prod_zpow ((Pi.basisFun ℤ (Fin (2 * g))).map bas) u hu]
  simp

theorem map_nsmul' {A : Type} [Group A] (u : D.La → A) (hu : ∀ x y, u (x + y) = u x * u y) (n : ℕ) (x : D.La) :
    u (n • x) = u x ^ n :=
  (MonoidHom.mk' (fun x : Multiplicative D.La => u x.toAdd) fun _ _ => hu _ _).map_pow (Multiplicative.ofAdd x) n

theorem existsUnique_coeff {A : Type} [CommGroup A] (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (u : D.La → A)
    (hu : ∀ x y, u (x + y) = u x * u y) {N : ℕ} (hN : 0 < N) (hk : ∀ x, u x = 1 ↔ ∃ y, x = N • y) (x : D.La) :
    ∃! c : Fin (2 * g) → ZMod N, ∏ i, u (bas (Pi.single i 1)) ^ (c i).val = u x := by
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨v, rfl⟩ := bas.surjective x
  have key : ∀ c : Fin (2 * g) → ZMod N,
      ∏ i, u (bas (Pi.single i 1)) ^ (c i).val = u (bas v) ↔ c = fun i => (v i : ZMod N) := fun c => by
    have e₁ : ∏ i, u (bas (Pi.single i 1)) ^ (c i).val = u (bas fun i => ((c i).val : ℤ)) := by
      rw [map_bas bas u hu]; simp only [zpow_natCast]
    have e₂ := hu (bas (v - fun i => ((c i).val : ℤ))) (bas fun i => ((c i).val : ℤ))
    rw [← map_add, sub_add_cancel] at e₂
    rw [e₁, e₂, right_eq_mul, hk]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨w, rfl⟩ := bas.surjective y
      rw [← map_nsmul] at hy
      funext i
      have := congrArg (fun z : ℤ => (z : ZMod N)) (congrFun (bas.injective hy) i)
      simp at this
      exact (sub_eq_zero.1 this).symm
    · intro hc
      have : ∀ i, ∃ w : ℤ, v i - ((c i).val : ℤ) = N * w := fun i =>
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (by simp [hc])
      choose w hw using this
      refine ⟨bas w, ?_⟩
      rw [← map_nsmul]
      congr 1
      funext i
      simpa using hw i
  simp only [key]
  exact existsUnique_eq

theorem coe_rt (n N : ℕ) : ((RZ.rt H n N : RZ H n N) : ℂ) = H.rt0 := by
  show ((2 : RZ H n N) : ℂ) * ((1 + H.rt0) / 2) - 1 = H.rt0
  have : ((2 : RZ H n N) : ℂ) = 2 := map_ofNat (RZ H n N).subtype 2
  rw [this]; ring

theorem rt_sq (n N : ℕ) : RZ.rt H n N ^ 2 = -(H.d : RZ H n N) := by
  apply Subtype.ext
  push_cast
  rw [coe_rt, H.sqrt_neg_disc_sq]

theorem map_unitS {o K : Type} [CommRing o] [CommRing K] {S : Scheme.{0}} (s : S ⟶ Sp o) (x : Sp K ⟶ S) (β : o →+* K)
    (h : x ≫ s = spMap β) (u : oˣ) (v : Kˣ) (hv : (v : K) = β u) :
    Units.map x.appTop.hom.toMonoidHom (unitS s u) = unitOn v := by
  apply Units.ext
  show x.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom u)) =
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom v
  have e := congrArg (fun q => q.hom (u : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))
  have e' := congrArg (fun q : Sp K ⟶ Sp o => q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom u)) h
  rw [hv]
  exact e'.trans e.symm

set_option maxHeartbeats 800000 in

theorem exists_under (hL : Out.Laws) {n N : ℕ} (hN : 0 < N) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La)
    (hbas : IsSympBasis D bas) (b : TBase (RZ H n N) N) (hb : (b.ζ : RZ H n N) = RZ.ze H n N) {S : Scheme.{0}}
    {s : S ⟶ Sp (RZ H n N)} [Flat s] {t : SAB H S} {lv : D.La → (𝟙_ (Over S) ⟶ t.G)} (h : FullObj D s t lv) :
    ∃ T : TObj g N J b s, Under t lv a bas T ∧ IsPEL D a bas (RZ.rt H n N) T t := by
  have hab : IsAbelianScheme t.G := ⟨t.semi.comm, t.semi.smooth, h.proper, t.semi.geomConnected⟩
  have hg : Module.finrank ℚ E / 2 * (D.p + D.q) = g := by
    have := bas.finrank_eq
    rw [datum_finrank_int, Module.finrank_fin_fun] at this
    omega
  have hdim : SmoothOfRelativeDimension g t.G.hom := by
    have := t.semi.smooth
    have := t.semi.geomConnected
    refine smoothOfRelativeDimension_of_generization _ g fun y => ?_
    obtain ⟨K, _, _, _, z, β, hβ, hz⟩ := exists_generization (t.G.hom ≫ s) y
    refine ⟨K, inferInstance, z, hz, fun m hm => ?_⟩
    refine (ObjDim.dim_eq_of_detCond D t.act (z ≫ t.G.hom) ?_
      (h.geom K _ β ((Category.assoc _ _ _).trans hβ)).1 hm).trans hg
    rw [← map_pow, rt_sq, map_neg, map_natCast]
  let pt : Fin (2 * g) → (Out.baseOver S ⟶ t.G) := fun i => toUnit _ ≫ lv (bas (Pi.single i 1))
  have hpt : ∀ i, pt i ^ N = 1 := fun i => by
    rw [← MonObj.comp_pow, ← map_nsmul' lv h.add, h.ker, MonObj.comp_one]
  have hptx : ∀ {X : Scheme.{0}} (x : X ⟶ S) (i), toB x ≫ pt i = toUnit _ ≫ lv (bas (Pi.single i 1)) := fun x i => by
    rw [← Category.assoc, toUnit_unique (toB x ≫ toUnit _) (toUnit _)]
  have hu : IsUnit (N : Γ(S, ⊤)) := by
    have := b.unit.map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (RZ H n N))).inv.hom)
    rwa [map_natCast] at this
  have hζ : b.ζ ^ N = 1 := by
    apply Units.ext
    apply Subtype.val_injective
    exact (b.prim ℂ (RZ H n N).subtype).pow_eq_one
  let P : Out.PolAV S :=
    { A := t.G, isAb := hab, g := g, smoothDim := hdim, L := t.PP.L, isLB := t.PP.isLB, rigid := ObjDim.rigidified,
      sym := ObjDim.sym, ample := h.ample, ktriv := h.ktriv }
  have : IsMonHom (Iso.refl t.G).hom := inferInstanceAs (IsMonHom (𝟙 t.G))
  have hid : LBIso t.PP.L (t.PP.L.pull (Iso.refl t.G).hom.left) :=
    LBIso.chartPull (chartPullId _) (Geo.Tor.chartPullPull _ _ (𝟙 _) (Category.id_comp _).symm)
      (PolBaseChange.lbIso_refl t.PP.isLB)
  have hpl : ∀ i, (lv (bas (Pi.single i 1))).left ≫ (Iso.refl t.G).hom.left = (pt i).left := fun i => by
    have e : (toUnit (Out.baseOver S)).left = 𝟙 S := ObjPull.toUnit_left' _
    rw [Iso.refl_hom, Over.id_left, Category.comp_id, Over.comp_left, e]
    exact (Category.id_comp (X := S) _).symm
  refine ⟨{ A := t.G, ab := hab, dim := hdim, L := t.PP.L, isLB := t.PP.isLB, rigid := ObjDim.rigidified,
            sym := ObjDim.sym, ample := h.ample, ktriv := h.ktriv, pt := pt, torsion := hpt,
            bij := torsion_basis_of_generization t.G N _ pt hab hN hu hpt fun p => ?_,
            pairing := fun i j => weilIs_of_generization hL P N _ _ _ hN hu (hpt i) (hpt j) ?_ fun p => ?_,
            act := fun j => t.act.act (a j), hom := fun j => t.act.hom _ },
    ⟨Iso.refl _, this, hid, fun j => by simp, hpl⟩,
    ⟨Iso.refl _, this, hid, fun j => by simp, fun K _ _ _ x β hx => ?_⟩⟩
  · obtain ⟨K, _, _, _, z, β, hβ, hz⟩ := exists_generization s p
    obtain ⟨-, I, -, hI⟩ := h.geom K z β hβ
    refine ⟨K, inferInstance, inferInstance, z, hz, fun y hy => ?_⟩
    obtain ⟨x, rfl⟩ := (I.onto N hN y).1 hy
    simp only [hptx, hI, Out.linComb, List.prod_ofFn]
    exact existsUnique_coeff bas (I.ev N) (I.add N) hN (I.ker N hN) x
  · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, unitS, unitOn, ← map_pow, ← map_pow, hζ, map_one,
      map_one, one_zpow]
  · obtain ⟨K, _, _, _, z, β, hβ, hz⟩ := exists_generization s p
    obtain ⟨-, I, hIζ, hI⟩ := h.geom K z β hβ
    refine ⟨K, inferInstance, z, hz, ?_⟩
    have hc : Units.map z.appTop.hom.toMonoidHom (unitS s b.ζ ^ Out.stdSymp g i j) =
        unitOn (I.ζ N ^ Out.stdSymp g i j) := by
      rw [map_zpow, map_unitS s z β hβ b.ζ (I.ζ N) (by rw [hIζ, hb]), unitOn, unitOn, map_zpow]
    have e : Out.WeilIs t.G t.PP.L N (toB z ≫ pt i) (toB z ≫ pt j)
        (Units.map z.appTop.hom.toMonoidHom (unitS s b.ζ ^ Out.stdSymp g i j)) := by
      rw [hc, hptx z i, hptx z j, hI, hI, ← hbas i j]
      exact I.isom N hN _ _
    exact e
  · obtain ⟨hd, I, hIζ, hI⟩ := h.geom K x β hx
    refine ⟨hd, I, by rw [hIζ, hb], fun i => ?_⟩
    have e : I.ev N (bas (Pi.single i 1)) ≫ 𝟙 t.G = toB x ≫ pt i := by rw [hptx, hI, Category.comp_id]
    exact e

theorem exists_level {n N : ℕ} {a : J → 𝓞 E} {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La}
    {b : TBase (RZ H n N) N} (hb : (b.ζ : RZ H n N) = RZ.ze H n N) {S : Scheme.{0}}
    {s : S ⟶ Sp (RZ H n N)} {t : SAB H S} {T : TObj g N J b s} (h : IsPEL D a bas (RZ.rt H n N) T t) :
    ∃ lv : D.La → (𝟙_ (Over S) ⟶ t.G), Under t lv a bas T ∧ FullObj D s t lv := by
  obtain ⟨φ, hφ, hφL, hφa, hgeom⟩ := h
  let j : 𝟙_ (Over S) ⟶ Out.baseOver S := Over.homMk (𝟙 S) (Category.id_comp _)
  let q : Fin (2 * g) → (𝟙_ (Over S) ⟶ t.G) := fun i => j ≫ T.pt i ≫ φ.inv
  have hq : ∀ i, q i ^ N = 1 := fun i => by
    rw [← MonObj.comp_pow, ← MonObj.pow_comp, T.torsion, MonObj.one_comp, MonObj.comp_one]
  let lv : D.La → (𝟙_ (Over S) ⟶ t.G) := fun x => ∏ i, q i ^ bas.symm x i
  have hadd : ∀ x y, lv (x + y) = lv x * lv y := fun x y => by
    simp only [lv, map_add, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  have hlv : ∀ i, lv (bas (Pi.single i 1)) = q i := fun i => by
    simp only [lv, LinearEquiv.symm_apply_apply]
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
    simp
  obtain ⟨hab, hA, hK⟩ := PolPull.pol_pull_of_relAmple_local AmpleLocal.relAmple_of_locally S S T.A t.G _ _ T.L t.PP.L
    T.isLB t.PP.isLB T.ab (isGrpPullback_of_iso φ) hφL
  refine ⟨lv, ⟨φ, hφ, hφL, hφa, fun i => ?_⟩, hab.proper, hA T.ample, hK T.ktriv, hadd, fun x => ?_,
    fun K _ _ _ x β hx => ?_⟩
  · rw [hlv]
    show (𝟙 S ≫ (T.pt i).left ≫ φ.inv.left) ≫ _ = _
    rw [Category.assoc, Category.assoc, inv_hom_left]
    exact (Category.id_comp _).trans (Category.comp_id _)
  · rw [map_nsmul' lv hadd, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hq, one_zpow]
  · obtain ⟨hd, I, hIζ, hI⟩ := hgeom K x β hx
    refine ⟨hd, I, by rw [hIζ, hb], eq_of_basis bas (fun y => toUnit _ ≫ lv y) (I.ev N)
      (fun y y' => by rw [hadd, MonObj.comp_mul]) (I.add N) fun i => ?_⟩
    have e : toUnit (Over.mk x) ≫ j = toB x := Over.OverMorphism.ext
      ((Category.comp_id _).trans (ObjPull.toUnit_left' _))
    rw [hlv, ← Category.assoc, e, ← Category.assoc, Iso.comp_inv_eq]
    exact (hI i).symm

theorem arBase_RZ (H : Host E) {n N e : ℕ} (hn : 0 < n) (hN : 0 < N) (h : N ∣ n ^ e) : ArBase (RZ H n N).subtype := by
  obtain ⟨l⟩ : Nonempty (Level H) := HostModel.instNonemptyLevel H
  exact ⟨BaseRing.isDedekindDomain_RZ { l with A := N, A_pos := hN } hn h, BaseRing.finiteType_RZ H n N,
    Subtype.val_injective⟩

end GlobalTheory.TripleTheta

namespace GlobalTheory

open TripleTheta CharZeroPts in

theorem exists_famCore_of_thetaFam : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N' : ℕ) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (b : TBase (RZ H n (N' ^ 2)) (N' ^ 2)) (F : ThetaFam n (RZ H n (N' ^ 2)).subtype (PELClass (b := b) D a bas (RZ.rt H n (N' ^ 2)) (RZ H n (N' ^ 2)).subtype)) (τ : SAB H F.MM), IsSympBasis D bas → Subring.closure (Set.range a) = ⊤ → (∃ w w', a w = H.w0 ∧ a w' = H.bar H.w0) → (b.ζ : RZ H n (N' ^ 2)) = RZ.ze H n (N' ^ 2) → IsPEL D a bas (RZ.rt H n (N' ^ 2)) F.univ τ → SmoothOfRelativeDimension D.dim (pullback.snd F.s (spMap (algebraMap (RZ H n (N' ^ 2)) (FractionRing (RZ H n (N' ^ 2)))))) → 1 ≤ D.p + D.q → n.Prime → Odd n → (∃ j, 1 ≤ j ∧ N' = n ^ j) → ∃ lev : D.La → (𝟙_ (Over F.MM) ⟶ τ.G), FamCore D F.s τ lev := by
  intro hL hL2 E _ _ _ H D n N' g J _ a bas b F τ hbas ha ⟨w, w', hw, hw'⟩ hb hP hsm hpq hn _ ⟨j, _, hj⟩
  have hN : 0 < N' ^ 2 := by rw [hj]; exact pow_pos (pow_pos hn.pos _) _
  have hbase : ArBase (RZ H n (N' ^ 2)).subtype := arBase_RZ H (e := j * 2) hn.pos hN (by rw [hj, pow_mul])
  obtain ⟨lev, hU, hF⟩ := exists_level hb hP
  refine ⟨lev, F.reduced, F.flat, F.qproj, SmoothOfRelativeDimension.smooth D.dim _, hF,
    fun S s t lv hS _ hs ho => ?_, fun k _ x t lv ν ν' hx hν hν' => ?_⟩
  · obtain ⟨T, hT, hTP⟩ := exists_under hL hN a bas hbas b hb ho
    obtain ⟨f, ⟨hf, hm⟩, huniq⟩ := F.rep S s T hS fun p => by
      obtain ⟨K, _, _, _, z, β, -, hz⟩ := exists_generization s p
      exact (hz (default : PrimeSpectrum K)).mem_closed isClosed_closure (subset_closure ⟨K, inferInstance, z, ⟨_, rfl⟩,
        PELFrom.fromC_of_isPEL hL hL2 E H D g J a w w' bas hpq hbas hw hw' ha N' _ b _ _ (coe_rt n _) hbase S s T t hTP K z⟩)
    exact ⟨f, ⟨hf, sabMap_of_tmap hU hT hF.add ho.add ha hS ho.proper hm⟩,
      fun f' ⟨hf', ν, hν⟩ => huniq f' ⟨hf', tmap_of_sabMap hU hT ν hν⟩⟩
  · obtain ⟨T, hT⟩ := tObj_pull _ g _ J b _ _ F.s (x ≫ F.s) x F.univ rfl
    exact F.unram k x T hx hT (tmap_of_sabMap hU (under_of_tmap hU hT ν hν) ν' hν')

end GlobalTheory
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universal_fullLevel_of_pelThetaFamily : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N' : ℕ) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (b : TBase (RZ H n (N' ^ 2)) (N' ^ 2)) (F : ThetaFam n (RZ H n (N' ^ 2)).subtype (PELClass (b := b) D a bas (RZ.rt H n (N' ^ 2)) (RZ H n (N' ^ 2)).subtype)) (τ : SAB H F.MM), IsSympBasis D bas → Subring.closure (Set.range a) = ⊤ → (∃ w w', a w = H.w0 ∧ a w' = H.bar H.w0) → (b.ζ : RZ H n (N' ^ 2)) = RZ.ze H n (N' ^ 2) → IsPEL D a bas (RZ.rt H n (N' ^ 2)) F.univ τ → SmoothOfRelativeDimension D.dim (pullback.snd F.s (spMap (algebraMap (RZ H n (N' ^ 2)) (FractionRing (RZ H n (N' ^ 2)))))) → 1 ≤ D.p + D.q → n.Prime → Odd n → (∃ j, 1 ≤ j ∧ N' = n ^ j) → ∃ lev : D.La → (𝟙_ (Over F.MM) ⟶ τ.G), FamCore D F.s τ lev := by
  atlas_forward_decl GlobalTheory.exists_famCore_of_thetaFam
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.ZM.SiegelUniversal

theorem isAlgebraic_of_injective {p M : ℕ} (hM : M ≠ 0) {o : Type} [CommRing o] (i : o →+* ZP p M)
    (hi : Function.Injective i) : Algebra.IsAlgebraic ℤ o := by
  have hle : ZP p M ≤ (algebraicClosure ℚ ℂ).toSubalgebra.toSubring := by
    refine Subring.closure_le.2 ?_
    rintro y (rfl | ⟨n, -, rfl⟩)
    · have h1 : zeta M ^ M = 1 := (Complex.isPrimitiveRoot_exp M hM).pow_eq_one
      exact mem_algebraicClosure_iff.2
        (IsAlgebraic.of_pow (Nat.pos_of_ne_zero hM) (h1 ▸ isAlgebraic_one))
    · exact (algebraicClosure ℚ ℂ).inv_mem (natCast_mem _ n)
  refine ⟨fun x => ?_⟩
  rw [← isAlgebraic_algHom_iff ((ZP p M).subtype.comp i).toIntAlgHom (Subtype.val_injective.comp hi),
    IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ, ← mem_algebraicClosure_iff]
  exact hle (i x).2

theorem exists_siegelFamily_siegRep : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ h n : ℕ, 1 ≤ h → n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ p : ℕ, p.Prime → p ≠ n → ∃ Ag : SiegelFamily h p ((n ^ j) ^ 2), SiegRep Ag := by
  intro L L2 hθ hU h n hh hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.nonempty_siegelFamily_over_arithmetic_base L L2 hθ hU h n hh hn hodd
  refine ⟨max j₀ 1, fun j hj p hp hnp => ?_⟩
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  obtain ⟨o, _, b, em, i, hem, hζ, hi, hconst⟩ :=
    GlobalTheory.ZM.CycBase.exists_base n (j * 2) p ((n ^ j) ^ 2) hn hp hnp.symm (by omega) (pow_mul n j 2).symm
  obtain ⟨F⟩ := hj₀ j (le_trans (le_max_left _ _) hj) o b em hem
  have h3 : 3 ≤ n := by
    have := hn.two_le
    rcases hodd with ⟨m, rfl⟩
    omega
  have hk : 3 ≤ (n ^ j) ^ 2 := by
    rw [← pow_mul]
    exact h3.trans (Nat.le_self_pow (by omega) n)
  have hinj : Function.Injective i := fun x y hxy => hem.2.2 (by rw [← hi, ← hi, hxy])
  obtain ⟨Ag, hAg⟩ := GlobalTheory.T.exists_siegelFamily_localised_cyclotomic_integers L L2 h _ p o _ i (hodd.pow.pow) hk hp hinj hζ hconst
    (isAlgebraic_of_injective (by omega) i hinj) F
  obtain ⟨F', -⟩ := F.exists_baseChange i hinj hζ
  obtain ⟨Ag', -, H⟩ := F'.exists_sRep_siegRep (by omega) Ag hAg
  exact ⟨Ag', H⟩

end GlobalTheory.ZM.SiegelUniversal
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universal_quasiProjective_siegelFamily_large_level : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ h n : ℕ, 1 ≤ h → n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ p : ℕ, p.Prime → p ≠ n → ∃ Ag : SiegelFamily h p ((n ^ j) ^ 2), SiegRep Ag := by
  atlas_forward_decl GlobalTheory.ZM.SiegelUniversal.exists_siegelFamily_siegRep
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_ringGenerators (x y : 𝓞 E) : ∃ (J : Type) (_ : Finite J) (a : J → 𝓞 E) (w w' : J),
    a w = x ∧ a w' = y ∧ Subring.closure (Set.range a) = ⊤ := by
  classical
  let b := NumberField.RingOfIntegers.basis E
  refine ⟨Option (Option (Module.Free.ChooseBasisIndex ℤ (𝓞 E))), inferInstance,
    fun j => Option.elim j x (fun j' => Option.elim j' y b), none, some none, rfl, rfl, ?_⟩
  rw [eq_top_iff]
  rintro z -
  have hz : z ∈ Submodule.span ℤ (Set.range b) := by
    rw [b.span_eq]
    exact Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    exact Subring.subset_closure ⟨some (some i), rfl⟩
  | zero => exact zero_mem _
  | add u v _ _ hu hv => exact add_mem hu hv
  | smul m u _ hu => exact zsmul_mem hu m

theorem RZ.coe_rt (H : Host E) (S A : ℕ) : (RZ H S A).subtype (RZ.rt H S A) = H.rt0 := by
  rw [RZ.rt, map_sub, map_mul, map_ofNat, map_one]
  show 2 * ((1 + H.rt0) / 2) - 1 = H.rt0
  ring

theorem exists_tBase_RZ (H : Host E) {n N e : ℕ} (hn : 0 < n) (hN : N = n ^ e) :
    ∃ b : TBase (RZ H n N) N, (b.ζ : RZ H n N) = RZ.ze H n N := by
  have hN0 : N ≠ 0 := by
    rw [hN]
    exact pow_ne_zero _ hn.ne'
  have hζ : IsPrimitiveRoot (zeta N) N := Complex.isPrimitiveRoot_exp N hN0
  have hpow : (RZ.ze H n N) ^ N = 1 := by
    apply Subtype.val_injective
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact hζ.pow_eq_one
  have hinv : ((n : ℂ))⁻¹ ∈ RZ H n N := Subring.subset_closure (Or.inr (Or.inl rfl))
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hunit_n : IsUnit (n : RZ H n N) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, ?_⟩
    apply Subtype.val_injective
    simp [hn']
  have hunit : IsUnit (N : RZ H n N) := by
    have h : (N : RZ H n N) = (n : RZ H n N) ^ e := by rw [← Nat.cast_pow, ← hN]
    rw [h]
    exact hunit_n.pow e
  have key : ∀ {S : Type} [CommRing S] (f : RZ H n N →+* S),
      (Polynomial.cyclotomic N ℤ).eval₂ (Int.castRingHom S) (f (RZ.ze H n N)) =
        f ((Polynomial.cyclotomic N ℤ).eval₂ (Int.castRingHom (RZ H n N)) (RZ.ze H n N)) := by
    intro S _ f
    rw [Polynomial.hom_eval₂]
    congr 1
    exact RingHom.ext_int _ _
  have h0 : (Polynomial.cyclotomic N ℤ).eval₂ (Int.castRingHom (RZ H n N)) (RZ.ze H n N) = 0 := by
    apply Subtype.val_injective
    show (RZ H n N).subtype _ = (RZ H n N).subtype 0
    rw [map_zero, ← key]
    have hr := ((Polynomial.isRoot_cyclotomic_iff_charZero (R := ℂ) (Nat.pos_of_ne_zero hN0)).mpr hζ).eq_zero
    rw [← Polynomial.map_cyclotomic_int, Polynomial.eval_map] at hr
    exact hr
  refine ⟨⟨Units.ofPowEqOne _ N hpow hN0, hunit, ?_⟩, rfl⟩
  intro K _ β
  have : NeZero ((N : ℕ) : K) := ⟨by simpa [map_natCast] using (hunit.map β).ne_zero⟩
  show IsPrimitiveRoot (β (RZ.ze H n N)) N
  apply Polynomial.isRoot_cyclotomic_iff.mp
  show Polynomial.eval _ _ = 0
  rw [← Polynomial.map_cyclotomic_int, Polynomial.eval_map, key, h0, map_zero]

theorem arBase_RZ (H : Host E) {n N e : ℕ} (hn : 0 < n) (hN : N = n ^ e) : ArBase (RZ H n N).subtype := by
  have hN0 : 0 < N := by
    rw [hN]
    exact pow_pos hn e
  have hrt2 : H.rt ^ 2 = -(H.d : 𝓞 E) := H.5
  have hw0 : 2 * H.w0 = 1 + H.rt := H.7
  have hd16 : H.d % 16 = 7 := H.2
  have hconj : ∀ a : 𝓞 E, ((H.bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E) := H.9
  have hd0 : (0 : ℝ) < H.d := by exact_mod_cast H.3.pos

  have hbar_rt : H.bar H.rt = -H.rt := by
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
      have h := congrArg ((↑) : 𝓞 E → E) hrt2
      push_cast at h
      exact h
    have hz2 : (φ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
      rw [← map_pow, hE, map_neg, map_natCast]
    set z := φ (H.rt : E) with hz
    have hx : z.re = 0 := by
      have h1 := congrArg Complex.re hz2
      have h2 := congrArg Complex.im hz2
      simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.natCast_re, Complex.natCast_im, neg_zero] at h1 h2
      have h3 : z.re * z.im = 0 := by nlinarith
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exfalso
        rw [h] at h1
        nlinarith [mul_self_nonneg z.re]
    have hc : φ (IsCMField.complexConj E (H.rt : E)) = φ (-(H.rt : E)) := by
      rw [IsCMField.complexEmbedding_complexConj, map_neg, ← hz]
      apply Complex.ext <;> simp [hx]
    have h4 : ((H.bar H.rt : 𝓞 E) : E) = ((-H.rt : 𝓞 E) : E) := by
      rw [hconj, φ.injective hc]
      norm_cast
    exact_mod_cast h4
  obtain ⟨m, hm⟩ : ∃ m, H.d = 16 * m + 7 := ⟨H.d / 16, by omega⟩
  have hdE : (H.d : 𝓞 E) = 16 * m + 7 := by
    rw [hm]
    push_cast
    ring
  have hbal : H.bar (2 + H.rt) = 2 - H.rt := by
    rw [map_add, map_ofNat, hbar_rt]
    ring
  have hal : (2 + H.rt) ∈ Algebra.adjoin ℤ {H.w0} := by
    have h : 2 + H.rt = 1 + H.w0 + H.w0 := by linear_combination -hw0
    rw [h]
    have hw := Algebra.subset_adjoin (R := ℤ) (Set.mem_singleton H.w0)
    exact add_mem (add_mem (one_mem _) hw) hw

  obtain ⟨l, hl⟩ : ∃ l : Level H, l.A = N := by
    refine ⟨⟨H.d + 4, by omega, ⟨H.d / 2 + 2, by omega⟩, Ideal.span {2 + H.rt}, ?_, ?_, ?_, N, hN0⟩, rfl⟩
    · exact le_antisymm
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
          (Ideal.subset_span ⟨Ideal.subset_span (Set.mem_singleton _), hal⟩)))
        (Ideal.span_le.mpr fun a ha => ha.1)
    · rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_mul_span_singleton]
      congr 2
      rw [RingEquiv.coe_toRingHom, hbal]
      push_cast
      linear_combination -hrt2
    · rw [Ideal.map_span, Set.image_singleton, Ideal.eq_top_iff_one]
      have h1 : (1 : 𝓞 E) = ((4 * m + 3 : 𝓞 E) - (2 - H.rt)) * (2 + H.rt) +
          (4 * m + 3 : 𝓞 E) * H.bar (2 + H.rt) := by
        rw [hbal]
        linear_combination -hrt2 + hdE
      rw [h1]
      exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _)))
  subst hl
  obtain ⟨⟨β, hβ⟩, hft, hded⟩ := BaseRing.isDedFrac_RZ E H l n e hn ⟨1, by rw [hN, Nat.mul_one]⟩
  obtain ⟨⟨_, hD⟩, -, -⟩ := hded β hβ
  exact ⟨hD, hft, Subtype.val_injective⟩

theorem one_le_finrank_div_two : 1 ≤ Module.finrank ℚ E / 2 := by
  have h1 := NumberField.IsTotallyComplex.finrank (K := E)
  have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
  omega

theorem topAmpExists : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → GlobalTheory.ZH.ZHGeoSt → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → TopAmpExists := by
  intro hHE hL hL2 hSR hTU hUT hZG hRed hGen hTh
  unfold TopAmpExists
  intro E _ _ _ H D hpq Xo n hn
  have hnp : n.Prime := hn.1
  have hno : Odd n := hn.2.1
  have hn0 : 0 < n := hnp.pos
  obtain ⟨bas, hbas⟩ := GlobalTheory.ZM.exists_isSympBasis E H D
  obtain ⟨J, hJ, a, w, w', haw, haw', hcl⟩ := exists_ringGenerators H.w0 (H.bar H.w0)
  have := hJ
  have hg1 : 1 ≤ Module.finrank ℚ E / 2 * (D.p + D.q) :=
    calc 1 = 1 * 1 := rfl
      _ ≤ _ := Nat.mul_le_mul (one_le_finrank_div_two (E := E)) hpq
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.T.exists_thetaFamily_pel_smooth_generic_fibre hL hL2 hRed hGen hTh E H D _ J a w w' bas hpq hbas haw haw' hcl n hnp hno
  obtain ⟨k, j₂, hj₂⟩ := GlobalTheory.T.nonempty_ampleFramedModel_PELThetaFamily hL hL2 hSR hTU hUT hZG E H D n hpq hnp hno
  obtain ⟨j₃, hj₃⟩ := GlobalTheory.T.exists_universal_quasiProjective_siegelFamily_large_level hL hL2 hGen hTh _ n hg1 hnp hno
  obtain ⟨j, hj1, hj2, hj3, hj⟩ : ∃ j, j₁ ≤ j ∧ j₂ ≤ j ∧ j₃ ≤ j ∧ 1 ≤ j :=
    ⟨max (max j₁ j₂) (max j₃ 1), by omega, by omega, by omega, by omega⟩
  have hNe : (n ^ j) ^ 2 = n ^ (j * 2) := (pow_mul n j 2).symm
  obtain ⟨b, hb⟩ := exists_tBase_RZ H hn0 hNe
  have hAr := arBase_RZ H hn0 hNe
  obtain ⟨F, τ, hPEL, hsm⟩ := hj₁ j hj1 (RZ H n ((n ^ j) ^ 2)) b (RZ H n ((n ^ j) ^ 2)).subtype
    (RZ.rt H n ((n ^ j) ^ 2)) (RZ.coe_rt H n _) hAr
  obtain ⟨C⟩ := hj₂ j hj2 (n ^ j) rfl _ J a bas b F τ hbas hcl ⟨w, w', haw, haw'⟩ hb hPEL hsm
  obtain ⟨lev, hcore⟩ := GlobalTheory.T.exists_universal_fullLevel_of_pelThetaFamily hL hL2 E H D n (n ^ j) _ J a bas b F τ hbas hcl
    ⟨w, w', haw, haw'⟩ hb hPEL hsm hpq hnp hno ⟨j, hj, rfl⟩
  have hcl2 := GlobalTheory.T.cmFamily_finite_unramified_over_siegelFamily hHE hL hL2 E H D n ((n ^ j) ^ 2) F.MM F.s τ lev hpq hnp hno
    ⟨j * 2, by omega, hNe⟩ hcore (hj₃ j hj3)
  obtain ⟨T, hT⟩ := GlobalTheory.T.exists_fullLevel_model_of_family_birationalModel hHE hL hL2 E H D Xo n ((n ^ j) ^ 2) F.MM F.s τ lev (n ^ k) C hpq hn
    ⟨j * 2, by omega, hNe⟩ (pow_pos hn0 k) hcore hcl2
  refine ⟨j * 2, k, ?_⟩
  rw [← hNe]
  exact ⟨T, by omega, hT⟩

end GlobalTheory.Models
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fullLevel_model_ample_frames : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → GlobalTheory.ZH.ZHGeoSt → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → TopAmpExists := by
  atlas_forward_decl GlobalTheory.Models.topAmpExists
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ThetaCrit

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap (f'.comp f) = spMap f' ≫ spMap f := Spec.map_comp _ _

theorem exists_model (hS : GlobalTheory.SS.SemistablePol) {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k}
    (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V)
    (t : TObj g k J b (spMap (algebraMap V K) ≫ spMap β)) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (φ : V →+* W)
      (ψ : K →+* FractionRing W) (tK : TObj g k J b (spMap (algebraMap W (FractionRing W)) ≫ spMap φ ≫ spMap β))
      (G : Over (Sp W)) (_ : GrpObj G) (gen : (Over.pullback (Out.jK W)).obj G ≅ tK.A),
      IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap W (FractionRing W)).comp φ ∧
      IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ TMap tK t (spMap ψ) ∧ IsMonHom gen.hom ∧ GlobalTheory.SS.SplitSemi W G := by
  obtain ⟨W, L, _, _, _, _, _, _, _, _, hcomm, -, hloc, hc, G, _, ⟨e, he⟩, hG⟩ := hS V K ‹_› t.pol
  let ε : L →+* FractionRing W := (IsLocalization.algEquiv (nonZeroDivisors W) L (FractionRing W) : L →+* _)
  let ψ : K →+* FractionRing W := ε.comp (algebraMap K L)
  have hε : ε.comp (algebraMap W L) = algebraMap W (FractionRing W) :=
    RingHom.ext (IsLocalization.algEquiv (nonZeroDivisors W) L (FractionRing W)).commutes
  have hψ : ψ.comp (algebraMap V K) = (algebraMap W (FractionRing W)).comp (algebraMap V W) := by
    rw [RingHom.comp_assoc, ← hcomm, ← RingHom.comp_assoc, hε]
  obtain ⟨tK, hK⟩ := GlobalTheory.tObj_pull o g k J b _ _ _
    (spMap (algebraMap W (FractionRing W)) ≫ spMap (algebraMap V W) ≫ spMap β) (spMap ψ) t
    (by rw [← Category.assoc, ← spMap_comp, hψ, spMap_comp, Category.assoc])
  obtain ⟨χ, hχ, -⟩ := id hK
  have e₁ : spMap ε ≫ spMap (algebraMap W L) = Out.jK W := by rw [← spMap_comp, hε]
  have a₁ := ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback t.pol.A _)).congr (Category.id_comp _) rfl
  let m : ((Over.pullback (Out.jK W)).obj G).left ⟶ ((Over.pullback (spMap (algebraMap W L))).obj G).left :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap ε) (by rw [Category.assoc, e₁, pullback.condition])
  have a₂ : IsGrpPullback ((Over.pullback (Out.jK W)).obj G) ((Over.pullback (spMap (algebraMap W L))).obj G)
      (spMap ε) m := (isGrpPullback_pullback G _).cancel
    ((isGrpPullback_pullback G (Out.jK W)).congr e₁.symm (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)
  obtain ⟨gen, hgen, -⟩ := grpPullback_iso ((a₂.comp a₁).congr (spMap_comp _ _).symm rfl) hχ
  exact ⟨W, inferInstance, inferInstance, inferInstance, algebraMap V W, ψ, tK, G, inferInstance, gen, hloc, hψ, hc, hK,
    hgen, hG⟩

section
open Out UT NormTheta

theorem isThetaPtOver_of_eq {S : Scheme.{0}} (P : PolAV S) (m : ℕ) {T : Over S} {I : Type} (x : I → (T ⟶ P.A))
    (w : I → Γ(T.left, ⊤)) {k : ℤ} (hk : k = (m : ℤ) ^ 2) (th : LB.Sec (LPow P.A P.L 1 T))
    (s₁ : LB.Sec (LPow P.A P.L k T))
    (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![k, -1]))
    (τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (1 : T ⟶ P.A).left) (fun _ => k)))
    (U : I → ThetaGrp P.A P.L k T) (s₂ : I → LB.Sec (LPow P.A P.L k T))
    (h₁ : IsGenSec P.A P.L 1 th) (h₂ : α.IsGen) (h₃ : τ.IsGen)
    (h₄ : IsTwistPull P.A P.L (mulT P.A T m) (snd T P.A ^ m) (lift_snd _ _) k 1 α th s₁)
    (h₅ : ∀ i, SymLift P.A P.L k (m ^ 2) (x i) (U i)) (h₆ : ∀ i, IsActOf P.A P.L k (U i) s₁ (s₂ i))
    (h₇ : ∀ i, IsValueAt P.A P.L k (s₂ i) 1 τ (w i)) : IsThetaPtOver P m x w := by
  subst hk
  exact ⟨th, s₁, α, τ, U, s₂, w, 1, h₁, h₂, h₃, h₄, h₅, h₆, h₇, fun _ => (_root_.one_mul _).symm⟩

theorem isThetaPt_of_normalised (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R]
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) {F : Type} [Field F] [Algebra (FractionRing R) F]
    {ρ : LB.Gen (A.L.pull (eSec A.A))} (hρ : ρ.IsGen) {m : ℕ} (hm : Odd m) (hu : (m : F) ≠ 0) {th : SecA A F 1}
    (hth : IsGenSec A.A A.L 1 th) {I : Type} (i₀ : I) (x : I → (TFK (R := R) F ⟶ A.A)) (c : I → F)
    (h : ∀ i, ∃ σ, ThC A ρ m th (x i) σ (c i)) :
    IsThetaPt A m x (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) := by
  have hL := A.isLB
  let T := TFK (R := R) F
  choose σ α s₁ θ hα hn hs₁ hθ ht hc using h
  have es : ∀ i, s₁ i = s₁ i₀ := fun i => by
    have ea := gen_unique hL (fst T A.A).left (ptSecT A.A 1).left ptSec_fst
      (CommPairing.surj_fst hG A.isAb T) (hα i) (hα i₀) (fun y J hJ => by
        have a := (val_corr hJ (hn i) (𝟙 _)).trans (val_corr hJ (hn i₀) (𝟙 _)).symm
        rwa [val_pull hJ, val_pull hJ, Category.id_comp] at a)
    exact sec_ext (sec_ext_val hL fun y J hJ =>
      (ThetaLin.sval_of_isTwistPull A.A (hs₁ i) _ y hJ).trans
        (Eq.trans (by rw [ea _ _ y J hJ]) (ThetaLin.sval_of_isTwistPull A.A (hs₁ i₀) _ y hJ).symm))
  have H : IsThetaPtOver A m x (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) :=
    isThetaPtOver_of_eq A m x _ (Nat.cast_pow m 2) th (s₁ i₀) (α i₀) (rigT A.A A.L ρ T _) θ σ hth (hα i₀)
      (rigT_isGen hρ _) (hs₁ i₀) hθ (fun i => es i ▸ ht i)
      (fun i => ThetaCoord.isValueAt_of_sv (T := T) (w := 1) hL (rigT_isGen hρ _) (hc i))
  let r : T ⟶ overRes (T := T) ⊤ := Over.homMk T.left.topIso.inv (by
    show T.left.topIso.inv ≫ (⊤ : T.left.Opens).ι ≫ T.hom = T.hom
    rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp])
  have hh : r ≫ overResι (T := T) ⊤ = 𝟙 T := Over.OverMorphism.ext T.left.toIso_inv_ι
  have hi : overResι (T := T) ⊤ ≫ r = 𝟙 _ := by
    haveI : Mono (overResι (T := T) ⊤) := Over.mono_of_mono_left _ (hk := inferInstanceAs (Mono (⊤ : T.left.Opens).ι))
    rw [← cancel_mono (overResι (T := T) ⊤), Category.assoc, hh, Category.comp_id, Category.id_comp]
  refine ⟨hm, ?_, fun _ => ⟨⊤, trivial, ThetaCoord.isThetaPtOver_pull A H _ r hi⟩⟩
  have := (IsUnit.mk0 _ hu).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  rwa [map_natCast] at this

end

theorem subsingleton_of_divisible {X : Type} [AddCommGroup X] [Module.Free ℤ X] {d : ℕ} (hd : 2 ≤ d)
    (h : ∀ x : X, ∃ y, x = d • y) : Subsingleton X := by
  let b := Module.Free.chooseBasis ℤ X
  have : IsEmpty (Module.Free.ChooseBasisIndex ℤ X) := ⟨fun i => by
    obtain ⟨y, hy⟩ := h (b i)
    have e := congrArg (fun x => b.repr x i) hy
    simp only [Module.Basis.repr_self, Finsupp.single_eq_same, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul] at e
    have := Int.eq_one_of_mul_eq_one_right (Int.natCast_nonneg d) e.symm
    omega⟩
  exact b.repr.injective.subsingleton

attribute [local instance] TorusExt.gtGroup in

theorem subsingleton_characters (h₁ : Out.Laws) (h₂ : Out.Laws2) (hT : GlobalTheory.ZH.UTorsSt) {o : Type} [CommRing o]
    {g n j : ℕ} {J : Type} {b : TBase o ((n ^ j) ^ 2)} (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [CharZero W] (hc : IsAdicComplete (IsLocalRing.maximalIdeal W) W) {s : Sp (FractionRing W) ⟶ Sp o}
    (t : TObj g ((n ^ j) ^ 2) J b s) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (D : Out.DegData W (IsLocalRing.maximalIdeal W)) (U : Out.Unif (IsLocalRing.maximalIdeal W) D t.pol G)
    (hn : 2 ≤ n) (ho : Odd n) (hj : 2 ≤ j) (hu : IsUnit ((n ^ j : ℕ) : W)) (v : Ix g ((n ^ j) ^ 2) → W)
    (hv : t.HasTh (𝟙 _) (fun a => algebraMap W (FractionRing W) (v a)))
    (hC : Coset n (n ^ j) v (IsLocalRing.maximalIdeal W)) : Subsingleton D.toPre.X := by
  obtain ⟨hL, k₁, k₂, k₃, k₄⟩ := GlobalTheory.T.uniformization_laws_and_expansion_statements
  have hA : Out.AdmBase W (IsLocalRing.maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  choose Q hQ using DVR.QForm.exists_QVal hϖ D
  let F := AlgebraicClosure (FractionRing W)
  obtain ⟨ν, hν⟩ := GlobalTheory.adic_base_embeds_valuation_algebraic_closure.2 W ϖ hϖ
  obtain ⟨ρ, hρ⟩ := t.pol.rigid
  obtain ⟨w₀, hw⟩ := (GlobalTheory.UT.EvalZero.value_at_origin hL W _ hA D t.pol G hG U F).2.1 ρ hρ
  obtain ⟨th, ϑ, hE, hP, hth⟩ := GlobalTheory.UT.exists_prim_generator hL k₁ k₂ k₃ k₄ W hc ϖ hϖ D Q hQ F ν hν t.pol G hG U w₀ hw.1
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hd : n ^ (i + 1) / n = n ^ i := by rw [pow_succ, Nat.mul_div_cancel _ (by omega)]
  have hm : Odd (n ^ (i + 1)) := ho.pow
  have hM : 1 ≤ (n ^ (i + 1)) ^ 2 := pow_pos hm.pos 2
  haveI : NeZero ((n ^ (i + 1)) ^ 2) := ⟨by omega⟩
  haveI := t.ab.comm
  obtain ⟨ua₁, ua₂⟩ := GlobalTheory.T.theta_constant_valuations_units_every_coset hL k₁ k₂ k₃ k₄ W hc ϖ hϖ D Q hQ F ν hν t.pol G hG U w₀ ρ hw th ϑ hE hP _ hm hu
  obtain ⟨f, f₁, f₂, -, f₄, -⟩ := hT W hc t.pol G D U F _ hM
  let z : Out.TFK (R := W) F ⟶ Out.baseOver (Sp (FractionRing W)) :=
    Over.homMk (spMap (algebraMap (FractionRing W) F)) (Category.comp_id _)
  let pt : Fin (2 * g) → (Out.TFK (R := W) F ⟶ t.A) := fun l => z ≫ t.pt l
  have hpt : ∀ l, pt l ^ ((n ^ (i + 1)) ^ 2) = 1 := fun l => by
    rw [← MonObj.comp_pow, t.torsion, MonObj.comp_one]
  let x : Ix g ((n ^ (i + 1)) ^ 2) → (Out.TFK (R := W) F ⟶ t.A) := fun a => ThetaCoord.lab pt a
  have hx : (fun a => z ≫ t.lab a) = x := funext fun a => VVRank.comp_linComb z _ _
  have onto : ∀ y : Out.TFK (R := W) F ⟶ t.A, y ^ ((n ^ (i + 1)) ^ 2) = 1 → ∃ a, x a = y := fun y hy =>
    (t.bij F _ y hy).exists
  have uq := fun a => GlobalTheory.existsUnique_thetaConst hL W t.pol F ρ hρ _ hm th (x a) (ThetaCoord.lab_pow hpt a)
  choose q hq hq' using uq
  have hF : ((n ^ (i + 1) : ℕ) : F) ≠ 0 := by
    have := (hu.map (algebraMap W (FractionRing W))).map (algebraMap (FractionRing W) F)
    rw [map_natCast, map_natCast] at this
    exact this.ne_zero
  have hc₁ : t.HasTh (spMap (algebraMap (FractionRing W) F)) (fun a => (q a).2) := by
    have := isThetaPt_of_normalised h₁.globalFns t.pol hρ hm hF hth 0 x (fun a => (q a).2) fun a => ⟨_, hq a⟩
    rw [← hx] at this
    exact this
  have hc₂ := GlobalTheory.hasTh_baseChange h₂ o g _ J b _ s t _ F (algebraMap (FractionRing W) F) _ _ hv
  rw [Category.comp_id] at hc₂
  have unit : ∀ a, v a ∉ IsLocalRing.maximalIdeal W →
      ν (algebraMap (FractionRing W) F (algebraMap W (FractionRing W) (v a))) = 0 := fun a ha => by
    obtain ⟨y, hy⟩ : IsUnit (v a) := by_contra ha
    rw [← hy]; exact DVR.GC.v_alg_unit hν y
  obtain ⟨c₀, hc₀⟩ := hC 0
  obtain ⟨u, hu'⟩ := GlobalTheory.T.thetaConstants_unique_up_to_unit h₁ h₂ o g _ J b _ s t F _ _ _ hc₂ hc₁
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, rfl⟩)
      (((by_contra hc₀ : IsUnit _).map (algebraMap W (FractionRing W))).map (algebraMap (FractionRing W) F)))
  have tors : ∀ p, f p ^ ((n ^ (i + 1)) ^ 2) = 1 := fun p => ((f₁ p _).2 rfl w₀ hw.1).1
  have hB := D.tau_bimult
  have u₀ : ν u = 0 := by
    refine le_antisymm ?_ ?_
    · obtain ⟨p', x', σ, c, -, hp', -, hx', h0⟩ := ua₂ n hn (dvd_pow_self n (by omega)) (TorusExt.qkZero hB F _) _ rfl
        ((f₁ _ _).2 rfl)
      obtain ⟨a, rfl⟩ := onto x' (hp' w₀ hw.1).1
      have e : c = (q a).2 := congrArg Prod.snd (hq' a (σ, c) hx')
      rw [e, hu' a, ν.map_mul] at h0
      exact (le_add_of_nonneg_right (DVR.GC.v_alg_nonneg hϖ hν _)).trans h0.le
    · obtain ⟨p, hp⟩ := f₂ _ (ThetaCoord.lab_pow hpt (0 + (n ^ (i + 1) / n) • c₀))
      have := (ua₁ p _ _ _ ((f₁ _ _).2 hp.symm) (hq _)).1 0 fun χ => div_nonneg (by
        rcases eq_or_ne (n ^ (i + 1) • χ + p.y) 0 with h | h
        · rw [h, DVR.QForm.Q_zero hϖ D hQ]; simp
        · exact_mod_cast zero_le_one.trans (DVR.QForm.Q_pos hϖ D hQ h)) (Nat.cast_nonneg _)
      rwa [hu', ν.map_mul, unit _ hc₀, add_zero] at this
  have comb : ∀ (d : ℕ) (p p' : Out.QkPt D.toPre F ((n ^ (i + 1)) ^ 2)),
      ∃ r, f r = f p * f p' ^ d ∧ r.y = p.y + d • p'.y := fun d p p' => by
    induction d with
    | zero => exact ⟨p, by rw [pow_zero, _root_.mul_one], by rw [zero_smul, add_zero]⟩
    | succ d ih =>
      obtain ⟨r, r₁, r₂⟩ := ih
      refine ⟨TorusExt.qkAdd hB r p', ?_, ?_⟩
      · rw [f₄ _ _ _ (TorusExt.qkAdd_qkAdd hB r p'), r₁, pow_succ (f p'), _root_.mul_assoc]
      · show r.y + p'.y = _
        rw [r₂, succ_nsmul, add_assoc]
  refine subsingleton_of_divisible (d := n ^ i) (hn.trans (Nat.le_self_pow (by omega) n)) fun χ => ?_
  obtain ⟨g₀, hg₀⟩ := (GlobalTheory.UT.gt_onto_divisible_kernel hL W _ hA D F).2.1 _ hM (TorusExt.iota hB F χ)
  let p := TorusExt.qkMk hB χ g₀ ((TorusExt.isNsmul_iff_eq _ _ _).1 hg₀).symm
  obtain ⟨a, ha⟩ := onto _ (tors p)
  obtain ⟨c, hc'⟩ := hC a
  obtain ⟨p', hp'⟩ := f₂ _ (ThetaCoord.lab_pow hpt c)
  obtain ⟨r, r₁, r₂⟩ := comb (n ^ (i + 1) / n) p p'
  have e : x (a + (n ^ (i + 1) / n) • c) = f r := by
    rw [r₁, hp', ← ha]
    exact (ThetaCoord.lab_add hpt _ _).trans (congrArg _ (ThetaCoord.lab_nsmul hpt _ _))
  obtain ⟨y, hy⟩ := (ua₁ r _ _ _ ((f₁ _ _).2 e) (hq _)).2 (by rw [hu', ν.map_mul, unit _ hc', u₀, add_zero])
  refine ⟨n • y - p'.y, ?_⟩
  rw [smul_sub, ← mul_smul, ← pow_succ, ← hy, r₂, hd]
  exact (add_sub_cancel_right _ _).symm

theorem exists_pol_model (h₁ : Out.Laws) (h₂ : Out.Laws2) (W : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] (hc : IsAdicComplete (IsLocalRing.maximalIdeal W) W)
    (A : Out.PolAV (Sp (FractionRing W))) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (D : Out.DegData W (IsLocalRing.maximalIdeal W)) (U : Out.Unif (IsLocalRing.maximalIdeal W) D A G)
    [Subsingleton D.toPre.X] :
    ∃ (P : Out.PolAV (Sp W)) (φ : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (Out.jK W) φ ∧ LBIso A.L (P.L.pull φ) := by
  have hA : Out.AdmBase W (IsLocalRing.maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨O, hO, hψ⟩ := GlobalTheory.T.uniformization_laws_and_expansion_statements.1.2.2.2.2.psiOnExists W _ hA D
  obtain ⟨D', hD, -, -⟩ := GlobalTheory.exists_degData_isPullDeg h₁.polBaseChange h₁.globalFns W W _ _ (RingHom.id W)
    (Ideal.map_id _).le D O hψ (by
      rw [show Out.specOf (RingHom.id W) = 𝟙 _ from Spec.map_id _]; exact hO)
  have : Subsingleton D'.toPre.X := hD.xe.injective.subsingleton
  obtain ⟨A', χ, hχ₀, -, hm, c, hc'⟩ := h₁.polBaseChange _ _ (Out.jK W) D'.toPre.P
  have hχ : IsGrpPullback A'.A D'.toPre.P.A (Out.jK W) χ :=
    ⟨hχ₀, fun T x y x₀ y₀ hx hy => by
      rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hχ₀.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hχ₀.w y),
        ← hm]
      rfl⟩
  obtain ⟨eA, hA', e₁⟩ := grpPullback_iso (isGrpPullback_pullback D'.toPre.P.A (Out.jK W)) hχ
  have hw : LBIso (A'.L.pull eA.hom.left) (D'.toPre.P.L.pull (pullback.fst D'.toPre.P.A.hom (Out.jK W))) :=
    GenSpread.lbIso_pull_of_lbIso (LBIso.symm ⟨c, hc'⟩) _ e₁.symm
  let U' : Out.Unif (IsLocalRing.maximalIdeal W) D' A' D'.toPre.P.A := ⟨SelfUnif.selfPre D' A' eA hA' hw, fun k _ =>
    SelfUnif.expBij D' A' eA hA' hw h₁.globalFns (IsAdicComplete.le_jacobson_bot _) k⟩
  obtain ⟨ψ, bc, hψ', -, e₂, ⟨wL, hwL, -⟩⟩ := GlobalTheory.T.exists_iso_uniformisations_of_iso_degeneration_data h₁ h₂ W _ hA rfl D D' A A' G D'.toPre.P.A hG
    (isSemiAbelian_of_isAbelianScheme _ D'.toPre.P.isAb) U U' hD
  have l₁ : LBIso D'.toPre.P.L (U.LG.L.pull ψ.hom.left) := e₂ ▸ ⟨wL, hwL⟩
  have := U.gen_hom
  have : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have : IsMonHom ψ.symm.hom := inferInstanceAs (IsMonHom ψ.inv)
  let φ₀ : A.A.left ⟶ G.left := U.gen.inv.left ≫ pullback.fst G.hom (Out.jK W)
  have g₀ : IsGrpPullback A.A G (Out.jK W) φ₀ :=
    ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G _)).congr (Category.id_comp _) rfl
  have i₁ : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have i₂ : ψ.inv.left ≫ ψ.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have l₂ : LBIso (A.L.pull (𝟙 _)) (U.LG.L.pull φ₀) := GenSpread.lbIso_pull_comp U.gen.inv.left i₁.symm rfl U.ext
  have l₃ : LBIso (D'.toPre.P.L.pull (φ₀ ≫ ψ.inv.left)) (U.LG.L.pull φ₀) :=
    GenSpread.lbIso_pull_of_lbIso l₁ _ (by rw [Category.assoc, i₂, Category.comp_id])
  have l₄ : LBIso A.L (A.L.pull (𝟙 _)) :=
    LBIso.chartPull (chartPullUnpull A.L _ rfl) (chartPullId _) (lbIso_refl (pull_isLB A.isLB _))
  exact ⟨D'.toPre.P, φ₀ ≫ ψ.inv.left, (g₀.comp (isGrpPullback_of_iso ψ.symm)).congr (Category.comp_id _) rfl,
    (l₄.trans A.isLB (pull_isLB A.isLB _) (pull_isLB U.LG.isLB _) l₂).trans A.isLB (pull_isLB U.LG.isLB _)
      (pull_isLB D'.toPre.P.isLB _) l₃.symm⟩

theorem exists_obj_model (h₁ : Out.Laws) (h₂ : Out.Laws2) {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k}
    (W K : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K] [Algebra W K] [IsFractionRing W K]
    (β : o →+* W) {sK : Sp K ⟶ Sp o} (hs : spMap (algebraMap W K) ≫ spMap β = sK) (t : TObj g k J b sK)
    (P : Out.PolAV (Sp W)) (φ : t.A.left ⟶ P.A.left) (hφ : IsGrpPullback t.A P.A (spMap (algebraMap W K)) φ)
    (hL : LBIso t.L (P.L.pull φ)) {s : Sp W ⟶ Sp o} (hs' : spMap β = s) :
    ∃ t' : TObj g k J b s, TMap t t' (spMap (algebraMap W K)) := by
  have := P.isAb.proper
  have hex : ValuativeCriterion.Existence P.A.hom :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed P.A.hom)).1
  have hp : ∀ i, ∃ p : Out.baseOver (Sp W) ⟶ P.A, (t.pt i).left ≫ φ = spMap (algebraMap W K) ≫ p.left := fun i => by
    obtain ⟨⟨l, l₁, l₂⟩⟩ := (hex
      { R := W, K := K, i₁ := (t.pt i).left ≫ φ, i₂ := 𝟙 _
        commSq := ⟨by
          rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w (t.pt i)]
          exact (Category.id_comp _).trans (Category.comp_id _).symm⟩ }).exists_lift
    exact ⟨Over.homMk l l₂, l₁.symm⟩
  choose p hp using hp
  have ha : ∀ i, ∃ a : P.A ⟶ P.A, (t.act i).left ≫ φ = φ ≫ a.left := fun i => by
    obtain ⟨a, -, ha, -⟩ := GlobalTheory.abelianScheme_hom_extends_dedekind_of_isGrpPullback (GlobalTheory.T.semiAbelianHomExtension_of_laws h₁ h₂) W K P.A P.A t.A t.A
      φ φ P.isAb P.isAb hφ hφ (t.act i) (t.hom i)
    exact ⟨a, ha⟩
  choose a ha using ha
  have hd := GlobalTheory.CM.smoothOfRelativeDimension_of_fibre W K _ P.A _ φ t.A.hom g P.isAb hφ.1 t.dim
  have : IsSchemeTheoreticallyDominant (spMap (algebraMap W K)) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ (IsFractionRing.injective W K)
  have : PreconnectedSpace (Sp W) := inferInstanceAs (PreconnectedSpace (PrimeSpectrum W))
  have hk : 0 < k := Nat.pos_of_ne_zero fun h0 => by
    have := b.unit.map β
    rw [h0, Nat.cast_zero, map_zero] at this
    exact not_isUnit_zero this
  subst hs'
  exact SpreadLevel.exists_extension h₁ (spMap β) (spMap (algebraMap W K)) hs hk
    (SpreadLevel.unitS_spMap_pow β b.ζ k (IsFractionRing.injective W K (by
      rw [map_pow, map_one]; exact (b.prim K ((algebraMap W K).comp β)).pow_eq_one)))
    t { P with g := g, smoothDim := hd } φ rfl hφ hL p hp a ha

theorem hasTh_unit_mul {o : Type} [CommRing o] {g N : ℕ} {J : Type} {b : TBase o (N ^ 2)} {S : Scheme.{0}}
    {s : S ⟶ Sp o} (t : TObj g (N ^ 2) J b s) {R : Type} [CommRing R] {x : Sp R ⟶ S} {v : Ix g (N ^ 2) → R}
    (h : t.HasTh x v) {r : R} (hr : IsUnit r) : t.HasTh x (fun a => r * v a) := by
  refine ⟨h.1, h.2.1, fun p => ?_⟩
  obtain ⟨V, hV, th, s₁, α, τ, U, s₂, w, u, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := h.2.2 p
  refine ⟨V, hV, th, s₁, α, τ, U, s₂, w,
    Out.unitRes (T := Over.mk x) V (hr.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).unit * u, a₁, a₂, a₃, a₄, a₅, a₆, a₇,
    fun i => ?_⟩
  refine (congrArg V.ι.appTop.hom (map_mul _ _ _)).trans ((map_mul _ _ _).trans ?_)
  exact (congrArg (fun q : Γ((Out.overRes (T := Over.mk x) V).left, ⊤) => (_ : Γ((Out.overRes (T := Over.mk x) V).left, ⊤)) * q)
    (a₈ i)).trans (_root_.mul_assoc _ _ _).symm

theorem hasTh_of_generic (h₁ : Out.Laws) (h₂ : Out.Laws2) {o : Type} [CommRing o] {g n N : ℕ} {J : Type}
    {b : TBase o (N ^ 2)} (W K : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K] [Algebra W K]
    [IsFractionRing W K] {s : Sp W ⟶ Sp o} {sK : Sp K ⟶ Sp o} (t' : TObj g (N ^ 2) J b s) (t : TObj g (N ^ 2) J b sK)
    (h : TMap t t' (spMap (algebraMap W K))) (hn : 2 ≤ n) (hN : n ∣ N) (v : Ix g (N ^ 2) → W)
    (hv : t.HasTh (𝟙 _) (fun a => algebraMap W K (v a))) (hu : ∃ a, IsUnit (v a)) : t'.HasTh (𝟙 _) v := by
  obtain ⟨R, _, x, v₀, hx, hp, h₀⟩ := GlobalTheory.ThetaLocal.exists_hasTh h₁ h₂ o g N J b _ s t' hv.1 (IsLocalRing.closedPoint W)
  have hr : Set.range (𝟙 (Sp W) :) ⊆ Set.range x := fun y _ =>
    (IsLocalRing.specializes_closedPoint y).mem_open x.isOpenEmbedding.isOpen_range hp
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (IsOpenImmersion.lift x (𝟙 (Sp W)) hr)
  have e : spMap σ.hom ≫ x = 𝟙 _ := (congrArg (· ≫ x) hσ).trans (IsOpenImmersion.lift_fac _ _ _)
  have hW := GlobalTheory.hasTh_baseChange h₂ o g N J b _ s t' R W σ.hom x v₀ h₀
  rw [e] at hW
  have hK := GlobalTheory.hasTh_baseChange h₂ o g N J b _ s t' W K (algebraMap W K) _ _ hW
  have hv' := (GlobalTheory.hasTh_iff_of_tmap o g N J b _ s t' _ sK t _ K _ _ h).1 hv
  rw [Category.comp_id] at hK
  rw [Category.id_comp] at hv'
  obtain ⟨c, hc⟩ := GlobalTheory.T.thetaCosetNonvanishing_of_hasTh h₁ h₂ o g N J b _ s t' n W _ _ _ hn hN hW
    (IsLocalRing.maximalIdeal.isMaximal W).isPrime 0
  obtain ⟨y, hy⟩ : IsUnit (σ.hom (v₀ (0 + (N / n) • c))) := by_contra hc
  obtain ⟨u, hu'⟩ := GlobalTheory.T.thetaConstants_unique_up_to_unit h₁ h₂ o g N J b _ s t' K _ _ _ hK hv'
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, rfl⟩) ((hy ▸ y.isUnit).map (algebraMap W K)))
  have key : ∀ a, v a = (v (0 + (N / n) • c) * ↑y⁻¹) * σ.hom (v₀ a) := fun a => IsFractionRing.injective W K (by
    rw [map_mul, map_mul, hu', hu', ← hy, mul_assoc (u : K), ← map_mul, y.mul_inv, map_one, _root_.mul_one])
  obtain ⟨a₀, ha₀⟩ := hu
  rw [funext key]
  exact hasTh_unit_mul t' hW (isUnit_of_mul_isUnit_left (key a₀ ▸ ha₀))

theorem good_reduction_of_theta_point : Out.Laws → Out.Laws2 → GlobalTheory.SS.SemistablePol → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → ∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a)) := by
  intro h₁ h₂ hS hU hT g n J w w' hn ho
  refine ⟨2, fun j hj o _ b V K _ _ _ _ _ _ _ _ _ β t v hp hv hC => ?_⟩
  obtain ⟨W, _, _, _, φ, ψ, tK, G, _, gen, hφ, hψ, hc, hK, hgen, hG, hE⟩ := exists_model hS V K β t
  have : CharZero (FractionRing W) := charZero_of_injective_ringHom ψ.injective
  have : CharZero W := RingHom.charZero (algebraMap W (FractionRing W))
  have := hG.comm
  have hp' : tK.Prim w w' := (GlobalTheory.shape_prim_pull_and_descend o g _ J b (fun _ => 0) 0 w w' _ _ _ _ _ t tK hK).2.1 hp
  have hS' : GlobalTheory.ZH.HypS tK.pol.A tK.pol.L := ⟨tK.act w, tK.act w', tK.hom w, tK.hom w', hp'.1, hp'.2.2, hp'.2.1⟩
  obtain ⟨D, U, -⟩ := hU W hc tK.pol G hG hE hS' gen hgen
  have hvK : tK.HasTh (𝟙 _) (fun a => algebraMap W (FractionRing W) (φ (v a))) := by
    have a := GlobalTheory.hasTh_baseChange h₂ o g _ J b _ _ t _ _ ψ _ _ hv
    rw [Category.comp_id, ← Category.id_comp (spMap ψ)] at a
    have e : (fun a => algebraMap W (FractionRing W) (φ (v a))) = fun a => ψ (algebraMap V K (v a)) :=
      funext fun a => (RingHom.congr_fun hψ (v a)).symm
    rw [e]
    exact (GlobalTheory.hasTh_iff_of_tmap o g _ J b _ _ t _ _ tK _ _ _ _ hK).2 a
  have hC' : Coset n (n ^ j) (fun a => φ (v a)) (IsLocalRing.maximalIdeal W) := fun a =>
    (hC a).imp fun c hc h => hc fun hu => h (hu.map φ)
  have hu : IsUnit ((n ^ j : ℕ) : W) := by
    have := b.unit.map (φ.comp β)
    rw [map_natCast, Nat.cast_pow] at this
    exact (isUnit_pow_iff two_ne_zero).1 this
  have := subsingleton_characters h₁ h₂ hT W hc tK G hG D U hn.two_le ho hj hu _ hvK hC'
  obtain ⟨P, χ, hχ, hL⟩ := exists_pol_model h₁ h₂ W hc tK.pol G hG D U
  have e : spMap (φ.comp β) = spMap φ ≫ spMap β := Spec.map_comp _ _
  obtain ⟨t', ht'⟩ := exists_obj_model h₁ h₂ W (FractionRing W) (φ.comp β) (by rw [e]) tK P χ hχ hL e
  refine ⟨W, FractionRing W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    φ, ψ, t', tK, hφ, hψ, hK, ht', hasTh_of_generic h₁ h₂ W _ t' tK ht' hn.two_le (dvd_pow_self n (by omega)) _ hvK ?_⟩
  obtain ⟨c, hc⟩ := hC' 0
  exact ⟨_, by_contra hc⟩

end GlobalTheory.ThetaCrit
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodReduction_of_thetaPoint_units : Out.Laws → Out.Laws2 → GlobalTheory.SS.SemistablePol → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → ∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a)) := by
  atlas_forward_decl GlobalTheory.ThetaCrit.good_reduction_of_theta_point
end

section
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem topAmpExists_of_semistableReduction :
    GlobalTheory.Published.SemistableReductionSt → GlobalTheory.Models.TopAmpExists :=
  fun S => GlobalTheory.T.exists_fullLevel_model_ample_frames GlobalTheory.T.homExtension_semiAbelian_discreteValuationRing GlobalTheory.T.all_six_abelian_scheme_laws_hold.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.1 S GlobalTheory.T.uniformisationExistence_and_torsion_statements.1 GlobalTheory.T.uniformisationExistence_and_torsion_statements.2
    (GlobalTheory.T.zarhinGeometric_of_semistableReduction S)
    (GlobalTheory.T.goodReduction_of_thetaPoint_units GlobalTheory.T.all_six_abelian_scheme_laws_hold.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.1 (GlobalTheory.T.semistableReductionSplit_of_padic S) GlobalTheory.T.uniformisationExistence_and_torsion_statements.1 GlobalTheory.T.uniformisationExistence_and_torsion_statements.2)
    GlobalTheory.T.theorem_of_cube_polAbelianScheme GlobalTheory.T.theta_uniformisation_complex_abelian_varieties

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fullLevelAmpleModel_of_semistableReduction : GlobalTheory.Published.SemistableReductionSt → GlobalTheory.Models.TopAmpExists := by
  atlas_forward_decl GlobalTheory.topAmpExists_of_semistableReduction
end
