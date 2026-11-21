import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperRestrictOfSubsetAbLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAbelianLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfGenericFibreNormalLocalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NondegeneratePairingOfGenericFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionGeometricPointOfField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsUnconditional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingDeterminedAtGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDescendsFromGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyOfFiniteTypeKer
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SectionLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmEndomorphismPlaceIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSubextensionCls
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RigidifiedSymmetricKernelTrivialDescendFieldExt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedRingActionDescendOfGenerators
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslatesCoverSemiAbelian

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLocusAtPrime

theorem isAbelianScheme_localization : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (p : Sp R) [p.asIdeal.IsPrime], p ∈ abLocus G₁ → IsAbelianScheme ((Over.pullback (spMap (algebraMap R (Localization.AtPrime p.asIdeal)))).obj G₁) := by
  intro R _ _ _ G₁ _ _ hG p _ hp
  haveI : IsNoetherianRing R := inferInstance
  haveI : IsDomain (Localization.AtPrime p.asIdeal) :=
    IsLocalization.isDomain_localization p.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsNoetherianRing (Localization.AtPrime p.asIdeal) :=
    IsLocalization.isNoetherianRing p.asIdeal.primeCompl _ inferInstance
  set f := spMap (algebraMap R (Localization.AtPrime p.asIdeal)) with hf
  have hG' : IsSemiAbelian ((Over.pullback f).obj G₁) := IsSemiAbelian.pullback f G₁ hG
  have hopen : IsOpen (abLocus G₁) := GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian G₁ hG
  have hgen : ∀ z : Sp (Localization.AtPrime p.asIdeal), f z ∈ abLocus G₁ := by
    intro z
    have hle : (f z) ⤳ p := by
      refine (PrimeSpectrum.le_iff_specializes (R := R) (f z) p).1 ?_
      have hr : (f z : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal))) := by
        exact ⟨z, rfl⟩
      rw [PrimeSpectrum.localization_comap_range (Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl] at hr
      show (f z : PrimeSpectrum R).asIdeal ≤ (p : PrimeSpectrum R).asIdeal
      intro x hx
      by_contra hxp
      exact Set.disjoint_left.1 hr hxp hx
    exact hle.mem_open hopen hp
  have hab : abLocus ((Over.pullback f).obj G₁) = Set.univ := Set.eq_univ_of_forall fun z =>
    (abLocus_pullback abLocusOne hG (IsPullback.of_hasPullback G₁.hom f) z).1 (hgen z)
  exact
    { comm := hG'.comm
      smooth := hG'.smooth
      proper := GlobalTheory.AbLocusProperNormal.isProper_of_abLocus_eq_univ _ _ hG' hab
      geomConnected := hG'.geomConnected }

end GlobalTheory.AbLocusAtPrime
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_isAbelianScheme_localization_abelianLocus : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (p : Sp R) [p.asIdeal.IsPrime], p ∈ abLocus G₁ → IsAbelianScheme ((Over.pullback (spMap (algebraMap R (Localization.AtPrime p.asIdeal)))).obj G₁) := by
  atlas_forward_decl GlobalTheory.AbLocusAtPrime.isAbelianScheme_localization
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_of_genericFibre_normalLocalDomain : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Field K] [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A] (A' : Over (Sp K)) [GrpObj A'] (φ : A'.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback A' A (spMap (algebraMap O K)) φ → ∀ (M : LB A.left) (M' : LB A'.left), M.IsLB → M'.IsLB → LBIso M' (M.pull φ) → Out.RelAmple A' M' → Out.RelAmple A M := by
  first | exact @GlobalTheory.AmpleGenericLocal.relAmple_of_generic | exact GlobalTheory.AmpleGenericLocal.relAmple_of_generic | (intros; apply GlobalTheory.AmpleGenericLocal.relAmple_of_generic <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nondegenerate_pairing_of_generic_fibre : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field K] [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A] (A' : Over (Sp K)) [GrpObj A'] (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left), IsAbelianScheme A → IsGrpPullback A' A (spMap (algebraMap O K)) φ → IsSquare φ φ₂ → ∀ (P : LB (A ⊗ A).left) (P' : LB (A' ⊗ A').left), P.IsLB → P'.IsLB → LBIso P' (P.pull φ₂) → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x = 1) → ∀ (T : Over (Sp O)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1 := by
  first | exact @GlobalTheory.NondegSpread.nondeg_of_generic | exact GlobalTheory.NondegSpread.nondeg_of_generic | (intros; apply GlobalTheory.NondegSpread.nondeg_of_generic <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.FibreTorsion

theorem card_torsion_of_proper_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ (F : Type) [Field F] [IsAlgClosed F] (p : Sp F ⟶ S), IsProper (pullback.snd G.hom p) → ∀ N : ℕ, (N : F) ≠ 0 → Nat.card {x : Over.mk p ⟶ G // x ^ N = 1} = N ^ (2 * g) := by
  intro S G _ _ hG g hg F _ _ p hprop N hN
  let B := (Over.pullback p).obj G
  haveI : IsProper B.hom := hprop
  have hB : IsAbelianScheme B :=
    AbelianSchemeGerms.isAbelianScheme_of_proper B (IsSemiAbelian.pullback p G hG)
  have hg' : SmoothOfRelativeDimension g B.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hg
  have h := GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional F B g N hB hg' hN
  have hp := isGrpPullback_pullback G p
  have hbij : Function.Bijective (pushHom hp (𝟙_ (Over (Sp F)))) := by
    constructor
    · intro x y hxy
      have e : x.left ≫ pullback.fst G.hom p = y.left ≫ pullback.fst G.hom p := congrArg (fun z => z.left) hxy
      exact Over.OverMorphism.ext (hp.1.hom_ext e ((Over.w x).trans (Over.w y).symm))
    · intro y
      refine ⟨Over.homMk (hp.1.lift y.left (𝟙_ (Over (Sp F))).hom (Over.w y)) (hp.1.lift_snd _ _ _), ?_⟩
      exact Over.OverMorphism.ext (hp.1.lift_fst _ _ _)
  let e := MulEquiv.ofBijective _ hbij
  have h2 : Nat.card {x : Over.mk ((𝟙_ (Over (Sp F))).hom ≫ p) ⟶ G // x ^ N = 1} = N ^ (2 * g) := by
    rw [← h]
    refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)).symm
    show x ^ N = 1 ↔ e x ^ N = 1
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  have h3 : (𝟙_ (Over (Sp F))).hom ≫ p = p := Category.id_comp p
  rw [h3] at h2
  exact h2

end GlobalTheory.FibreTorsion
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LevelSpread

theorem eq_one_of_point (O : Type) [CommRing O] [IsLocalRing O] (A : Over (Sp O)) [GrpObj A]
    (hA : IsAbelianScheme A) (n : ℕ) (hn : IsUnit (n : O)) (s : 𝟙_ (Over (Sp O)) ⟶ A)
    (hs : s ^ n = 1) (k : Type) [Field k] (x : Sp k ⟶ Sp O) (hx : toUnit (Over.mk x) ≫ s = 1) :
    s = 1 := by
  haveI := GlobalTheory.AbelianDim.connectedSpace_spec_of_isLocalRing O
  have hn' : IsUnit (n : Γ(Sp O, ⊤)) := by
    have := hn.map (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
    simpa using this
  obtain ⟨⟨-, het⟩, -⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion (hG := hA) A hn'
  haveI := hA.proper
  haveI : IsSeparated ((mulN A n).left ≫ A.hom) := by
    rw [Over.w (mulN A n)]; infer_instance
  haveI : IsSeparated (mulN A n).left := IsSeparated.of_comp _ A.hom
  have hab : s ≫ mulN A n = (1 : 𝟙_ (Over (Sp O)) ⟶ A) ≫ mulN A n := by
    rw [GlobalTheory.GrpTangent.mulN_eq_pow, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id,
      Category.comp_id, hs, one_pow]
  have hj : toUnit (Over.mk x) ≫ s = toUnit (Over.mk x) ≫ (1 : 𝟙_ (Over (Sp O)) ⟶ A) := by
    rw [hx, MonObj.comp_one]
  exact Over.OverMorphism.ext (GlobalTheory.eq_of_connected_of_unramified_of_point (T := Sp O) (mulN A n).left
    (congrArg (·.left) hab) x (congrArg (·.left) hj))

end GlobalTheory.LevelSpread

namespace GlobalTheory.LevelSpread

theorem card_of_basis {I G : Type} [Fintype I] [Group G] {n : ℕ} (hn : n ≠ 0) (f : (I → ℤ) → G)
    (add : ∀ a b, f (a + b) = f a * f b) (tors : ∀ a, f a ^ n = 1)
    (ker : ∀ a, f a = 1 ↔ ∃ b, a = n • b) (onto : ∀ u : G, u ^ n = 1 → ∃ a, f a = u) :
    Nat.card {u : G // u ^ n = 1} = n ^ Fintype.card I := by
  haveI : NeZero n := ⟨hn⟩
  let F : (I → ZMod n) → {u : G // u ^ n = 1} := fun c => ⟨f fun i => (c i).val, tors _⟩
  have hF : Function.Injective F := fun c c' e => by
    have e₁ : f (fun i => (c i).val) = f fun i => (c' i).val := congrArg Subtype.val e
    have e₂ := add ((fun i => ((c i).val : ℤ)) - fun i => ((c' i).val : ℤ)) fun i => (c' i).val
    rw [sub_add_cancel, e₁] at e₂
    obtain ⟨b, hb⟩ := (ker _).1 (mul_eq_right.1 e₂.symm)
    funext i
    have := congrArg (fun z : ℤ => (z : ZMod n)) (congrFun hb i)
    simpa [sub_eq_zero] using this
  have hS : Function.Surjective F := by
    rintro ⟨u, hu⟩
    obtain ⟨a, rfl⟩ := onto u hu
    refine ⟨fun i => (a i : ZMod n), Subtype.ext ?_⟩
    show f (fun i => ((a i : ZMod n).val : ℤ)) = f a
    have hd : ∃ b, (fun i => ((a i : ZMod n).val : ℤ)) - a = n • b := by
      have : ∀ i, (n : ℤ) ∣ ((a i : ZMod n).val : ℤ) - a i := fun i => by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val, sub_self]
      choose b hb using this
      exact ⟨b, funext fun i => by simpa using hb i⟩
    have e := add ((fun i => ((a i : ZMod n).val : ℤ)) - a) a
    rw [sub_add_cancel, (ker _).2 hd, _root_.one_mul] at e
    exact e
  rw [← Nat.card_congr (Equiv.ofBijective F ⟨hF, hS⟩), Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_fintype_card]

theorem basis_at_every_point : ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (g n : ℕ), IsUnit (n : O) → ∀ (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp O)) ⟶ A)), (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ n = 1) → ∀ (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (x₀ : Sp k₀ ⟶ Sp O), (∀ a, (toUnit (Over.mk x₀) ≫ lev a = 1 ↔ ∃ b, a = n • b)) → (∀ u : Over.mk x₀ ⟶ A, u ^ n = 1 → ∃ a, toUnit _ ≫ lev a = u) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp O), (∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = n • b)) ∧ (∀ u : Over.mk x ⟶ A, u ^ n = 1 → ∃ a, toUnit _ ≫ lev a = u) := by
  intro O _ _ _ A _ _ hA g n hn lev add tors k₀ _ _ x₀ ker₀ onto₀ k _ _ x
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact not_isUnit_zero (M₀ := O) (by simpa using hn)
  have lev0 : lev 0 = 1 := mul_eq_left.1 ((add 0 0).symm.trans (by rw [add_zero]))
  have pw : ∀ (b : Fin g ⊕ Fin g → ℤ) (m : ℕ), lev (m • b) = lev b ^ m := fun b m => by
    induction m with
    | zero => rw [zero_smul, pow_zero, lev0]
    | succ m ih => rw [succ_nsmul, add, ih, pow_succ]
  have hunit : ∀ (F : Type) [Field F] (p : Sp F ⟶ Sp O), (n : F) ≠ 0 := fun F _ p => by
    obtain ⟨φ, rfl⟩ := Spec.map_surjective p
    have := (hn.map φ.hom).ne_zero
    simpa using this
  have ker : ∀ a, toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = n • b := fun a => by
    refine ⟨fun h => (ker₀ a).1 ?_, ?_⟩
    · rw [GlobalTheory.LevelSpread.eq_one_of_point O A hA n hn (lev a) (tors a) k x h, MonObj.comp_one]
    · rintro ⟨b, rfl⟩
      rw [pw, tors, MonObj.comp_one]
  refine ⟨ker, fun u hu => ?_⟩
  haveI := hA.proper
  obtain ⟨d, hd⟩ := GlobalTheory.AbelianDim.exists_relDim O A hA
  have hsa := GlobalTheory.isSemiAbelian_of_isAbelianScheme A hA
  have c₀ := GlobalTheory.FibreTorsion.card_torsion_of_proper_fibre (Sp O) A hsa d hd k₀ x₀ inferInstance n
    (hunit k₀ x₀)
  have c := GlobalTheory.FibreTorsion.card_torsion_of_proper_fibre (Sp O) A hsa d hd k x inferInstance n
    (hunit k x)
  have b₀ := card_of_basis hn0 (fun a => toUnit (Over.mk x₀) ≫ lev a)
    (fun a b => by rw [add, MonObj.comp_mul]) (fun a => by rw [← MonObj.comp_pow, tors, MonObj.comp_one])
    ker₀ onto₀
  exact GlobalTheory.SiegelOfPolarised.onto_torsion hn0 (fun a => toUnit (Over.mk x) ≫ lev a)
    (fun a b => by rw [add, MonObj.comp_mul]) (fun a => by rw [← MonObj.comp_pow, tors, MonObj.comp_one])
    (fun a => (ker a).1) (c.trans (c₀.symm.trans b₀)) u hu

end GlobalTheory.LevelSpread
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelBasis_every_geometricPoint_localRing : ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (g n : ℕ), IsUnit (n : O) → ∀ (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp O)) ⟶ A)), (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ n = 1) → ∀ (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (x₀ : Sp k₀ ⟶ Sp O), (∀ a, (toUnit (Over.mk x₀) ≫ lev a = 1 ↔ ∃ b, a = n • b)) → (∀ u : Over.mk x₀ ⟶ A, u ^ n = 1 → ∃ a, toUnit _ ≫ lev a = u) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp O), (∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = n • b)) ∧ (∀ u : Over.mk x ⟶ A, u ^ n = 1 → ∃ a, toUnit _ ≫ lev a = u) := by
  atlas_forward_decl GlobalTheory.LevelSpread.basis_at_every_point
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutatorPairing_determined_at_genericPoint : ∀ (O : Type) [CommRing O] [IsDomain O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (A ⊗ A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (N : ℕ), 0 < N → IsUnit (N : O) → ∀ (u v : 𝟙_ (Over (Sp O)) ⟶ A), u ^ N = 1 → v ^ N = 1 → ∀ (c : Oˣ) (k₀ : Type) [Field k₀] (j : O →+* k₀), Function.Injective j → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap j)) ≫ u) (toUnit (Over.mk (spMap j)) ≫ v) (unitOn (Units.map j.toMonoidHom c)) → ∀ (k : Type) [Field k] (ρ : O →+* k), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap ρ)) ≫ u) (toUnit (Over.mk (spMap ρ)) ≫ v) (unitOn (Units.map ρ.toMonoidHom c)) := by
  first | exact @GlobalTheory.WeilGeneric.weilIs_of_generic | exact GlobalTheory.WeilGeneric.weilIs_of_generic | (intros; apply GlobalTheory.WeilGeneric.weilIs_of_generic <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm GlobalTheory.HtGen GlobalTheory.RootFrameB
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped Classical

namespace GlobalTheory.LabelExt

section Gen

variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem lift_finite [IsIntegrallyClosed R] {X S : Scheme.{0}} (f : X ⟶ S) [IsFinite f] (y : Sp R ⟶ S) (w : Sp K ⟶ X)
    (h : w ≫ f = spMap (algebraMap R K) ≫ y) : ∃ v : Sp R ⟶ X, v ≫ f = y ∧ spMap (algebraMap R K) ≫ v = w :=
  _root_.UpperTheory.Reformulated.B.Yt7.lift_finite f y w h

theorem ext_frac {S : Scheme.{0}} {G : Over S} [IsSeparated G.hom] {y : Sp R ⟶ S} {u v : Over.mk y ⟶ G}
    (h : spMap (algebraMap R K) ≫ u.left = spMap (algebraMap R K) ≫ v.left) : u = v := by
  haveI : IsDominant (spMap (algebraMap R K)) := by
    refine ⟨?_⟩
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R K)).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)]; exact bot_le)
  haveI : IsReduced (Over.mk y).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of R)))
  ext1
  exact ext_of_isDominant_of_isSeparated G.hom (by rw [Over.w u, Over.w v]) (spMap (algebraMap R K)) h

theorem lift_tors [IsIntegrallyClosed R] {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsAbelianScheme G) {q : ℕ}
    (hq : q ≠ 0) {y : Sp R ⟶ S} {y' : Sp K ⟶ S} (hy : spMap (algebraMap R K) ≫ y = y') (w : Over.mk y' ⟶ G)
    (hw : w ^ q = 1) : ∃ v : Over.mk y ⟶ G, spMap (algebraMap R K) ≫ v.left = w.left := by
  haveI := (AbTorsionAnyBase.isFinite_and_flat_torsion S G hG q (Nat.one_le_iff_ne_zero.2 hq)).1
  have e : w ≫ mulN G q = CartesianMonoidalCategory.toUnit _ ≫ η[G] := by
    rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, hw]; rfl
  let w₁ : Over.mk y' ⟶ torsion G q := Limits.pullback.lift w _ e
  have h₁ : w₁ ≫ torsion.ι G q = w := Limits.pullback.lift_fst _ _ _
  obtain ⟨v, hv, hv'⟩ := lift_finite (torsion G q).hom y w₁.left ((Over.w w₁).trans hy.symm)
  refine ⟨(Over.homMk v hv : Over.mk y ⟶ torsion G q) ≫ torsion.ι G q, ?_⟩
  rw [← h₁, Over.comp_left, Over.comp_left, ← hv', Category.assoc]
  rfl

end Gen

end GlobalTheory.LabelExt

end
end

section
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TorusPart

theorem exists_finite_torusExtension_act : ∀ (O : Type) [CommRing O] (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (G : Over (Sp K)) [GrpObj G], IsSemiAbelian G → ∀ (i : OAct O G) (G' : Over (Sp Ω))
    [GrpObj G'] (i' : OAct O G') (φ : G'.left ⟶ G.left), IsActPull i' i (spMap (algebraMap K Ω)) φ →
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u' : splitTorus (Sp Ω) X ⟶ G')
    (A : Over (Sp Ω)) [GrpObj A] (q' : G' ⟶ A) (j : OAct O A),
    IsAbelianScheme A → IsMonHom u' → IsKer u' q' → (∀ a, i'.act a ≫ q' = q' ≫ j.act a) →
    ∃ F : IntermediateField K Ω, FiniteDimensional K F ∧
      ∃ (G₀ : Over (Sp F)) (_ : GrpObj G₀) (i₀ : OAct O G₀) (φ₀ : G₀.left ⟶ G.left)
        (Y : Type) (_ : AddCommGroup Y) (_ : Module.Free ℤ Y) (_ : Module.Finite ℤ Y) (u₀ : splitTorus (Sp F) Y ⟶ G₀)
        (B : Over (Sp F)) (_ : GrpObj B) (q₀ : G₀ ⟶ B) (j₀ : OAct O B) (ψ : A.left ⟶ B.left),
        IsActPull i₀ i (spMap (algebraMap K F)) φ₀ ∧ IsAbelianScheme B ∧ IsMonHom u₀ ∧ IsKer u₀ q₀ ∧
        (∀ a, i₀.act a ≫ q₀ = q₀ ≫ j₀.act a) ∧ IsActPull j j₀ (spMap (algebraMap F Ω)) ψ := by
  intro O _ K Ω _ _ _ _ G _ hG i G' _ i' φ hφ X _ _ _ u' A _ q' j hA hu hk hq
  have := hG.comm
  have := hG.smooth
  have := hG.quasiCompact
  have := hG.separated

  let T' : TorusExtension G' :=
    { X := X, B := A, isAbelian := hA, q := q', q_hom := hk.1, q_flat := hk.2.1, q_surjective := hk.2.2.1,
      q_quasiCompact := hk.2.2.2.1, i := u', i_hom := hu, isKernel := hk.2.2.2.2 }
  obtain ⟨e, he, -⟩ := grpPullback_iso hφ.1 (isGrpPullback_pullback G (spMap (algebraMap K Ω)))
  haveI := he
  obtain ⟨F, hF, ⟨T₀⟩⟩ := GlobalTheory.exists_finite_torusExtension K Ω G inferInstance inferInstance inferInstance
    ⟨torusExtOfIso e T'⟩
  letI := T₀.addCommGroup
  letI := T₀.grpB
  have := T₀.free
  have := T₀.finite
  have := T₀.isAbelian.proper
  have := T₀.isAbelian.comm
  have := T₀.i_hom
  have := T₀.q_hom

  let i₀ : OAct O ((Over.pullback (spMap (algebraMap K F))).obj G) := OAct.pullback _ G i
  have h₀ : IsActPull i₀ i (spMap (algebraMap K F)) (pullback.fst G.hom _) := exists_isActPull _ i
  have hk₀ : IsKer T₀.i T₀.q := isKer_torusExtension T₀
  have hu₀ : ∀ a, T₀.i ≫ i₀.act a ≫ T₀.q = toUnit _ ≫ η[T₀.B] := fun a => by
    have := i₀.hom a
    rw [GlobalTheory.SemiRigid.torus_const T₀.X T₀.B (T₀.i ≫ i₀.act a ≫ T₀.q)]
    simp [IsMonHom.one_hom_assoc, IsMonHom.one_hom]
  obtain ⟨j₀, hj₀⟩ := hk₀.exists_oAct i₀ hu₀

  let f := spMap (algebraMap F Ω)
  have hf : f ≫ spMap (algebraMap K F) = spMap (algebraMap K Ω) :=
    FieldModel.spMap_comp (IsScalarTower.algebraMap_eq K F Ω).symm
  obtain ⟨φ', eφ', Hφ'⟩ := FieldModel.exists_baseChange (X₀ := G) hf hφ.1.1
  have gp : IsGrpPullback G' ((Over.pullback (spMap (algebraMap K F))).obj G) f φ' :=
    (isGrpPullback_pullback G _).cancel (hφ.1.congr hf.symm eφ'.symm) Hφ'.w
  have hact : ∀ a, (i'.act a).left ≫ φ' = φ' ≫ (i₀.act a).left := fun a => by
    refine (isGrpPullback_pullback G (spMap (algebraMap K F))).1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, eφ', h₀.2 a, ← Category.assoc, eφ']
      exact hφ.2 a
    · rw [Category.assoc, Category.assoc, Over.w (i₀.act a), Hφ'.w, ← Category.assoc, Over.w (i'.act a)]

  obtain ⟨u'', hu'', -⟩ := existsUnique_torusCompat gp.1 T₀.i
  have : IsMonHom u'' := TorusCompat.isMonHom gp hu''
  obtain ⟨q'', hk'', hsq⟩ := IsKer.baseChange gp (isGrpPullback_pullback T₀.B f) hu'' hk₀
  have := hA.proper
  have hBp : IsProper ((Over.pullback f).obj T₀.B).hom := by
    show IsProper (pullback.snd T₀.B.hom f); infer_instance
  have := hk''.1
  have := hk.1
  have c₁ : u'' ≫ q' = toUnit _ ≫ η[A] := by
    rw [GlobalTheory.SemiRigid.torus_const T₀.X A (u'' ≫ q')]
    simp [IsMonHom.one_hom_assoc, IsMonHom.one_hom]
  have c₂ : u' ≫ q'' = toUnit _ ≫ η[(Over.pullback f).obj T₀.B] := by
    rw [GlobalTheory.SemiRigid.torus_const X _ (u' ≫ q'')]
    simp [IsMonHom.one_hom_assoc, IsMonHom.one_hom]
  obtain ⟨β, hβ, hβq⟩ := flatQuotient_iso_of_same_kernel _ G' _ A _ _ q'' u'' q' u' hk''.1 inferInstance hk''.2.1
    hk''.2.2.1 hk''.2.2.2.1 hk''.2.2.2.2 hk.1 hu hk.2.1 hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2 c₂ c₁
  haveI := hβ

  let jω : OAct O ((Over.pullback f).obj T₀.B) := OAct.pullback f T₀.B j₀
  have e1 : ∀ a, (i'.act a).left ≫ q''.left ≫ pullback.fst T₀.B.hom f =
      q''.left ≫ pullback.fst T₀.B.hom f ≫ (j₀.act a).left := fun a => by
    have h1 := congrArg CommaMorphism.left (hj₀ a)
    simp only [Over.comp_left] at h1
    rw [← hsq.w, reassoc_of% (hact a), h1]
    exact (reassoc_of% hsq.w) _
  have key : ∀ a, i'.act a ≫ q'' = q'' ≫ jω.act a := fun a => by
    apply Over.OverMorphism.ext
    refine (isGrpPullback_pullback T₀.B f).1.hom_ext ?_ ?_
    · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, (exists_isActPull f j₀).2 a]
      exact e1 a
    · exact (Over.w _).trans (Over.w _).symm
  have := hk.2.1
  have := hk.2.2.1
  haveI : Epi q' := FlatQuotient.epi_of_flat_surjective q'
  have key2 : ∀ a, j.act a ≫ β.hom = β.hom ≫ jω.act a := fun a => by
    rw [← cancel_epi q', ← reassoc_of% (hq a), hβq, reassoc_of% hβq]
    exact key a
  refine ⟨F, hF, _, inferInstance, i₀, pullback.fst G.hom _, T₀.X, T₀.addCommGroup, T₀.free, T₀.finite, T₀.i, T₀.B,
    T₀.grpB, T₀.q, j₀, β.hom.left ≫ pullback.fst T₀.B.hom f, h₀, T₀.isAbelian, T₀.i_hom, hk₀, hj₀, ?_, ?_⟩
  · exact ((isGrpPullback_of_iso β).comp (isGrpPullback_pullback T₀.B f)).congr (Category.id_comp f) rfl
  · intro a
    have k3 := congrArg CommaMorphism.left (key2 a)
    simp only [Over.comp_left] at k3
    rw [reassoc_of% k3, (exists_isActPull f j₀).2 a, Category.assoc]

end GlobalTheory.TorusPart
end
end

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_part_of_pulled_action : ∀ (O : Type) [CommRing O] (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (G : Over (Sp K)) [GrpObj G], IsSemiAbelian G → ∀ (i : OAct O G) (G' : Over (Sp Ω)) [GrpObj G'] (i' : OAct O G')
    (φ : G'.left ⟶ G.left), IsActPull i' i (spMap (algebraMap K Ω)) φ →
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u' : splitTorus (Sp Ω) X ⟶ G') (A : Over (Sp Ω)) [GrpObj A] (q' : G' ⟶ A) (j : OAct O A),
    IsAbelianScheme A → IsMonHom u' → IsKer u' q' → (∀ a, i'.act a ≫ q' = q' ≫ j.act a) →
    ∃ F : IntermediateField K Ω, FiniteDimensional K F ∧
      ∃ (G₀ : Over (Sp F)) (_ : GrpObj G₀) (i₀ : OAct O G₀) (φ₀ : G₀.left ⟶ G.left)
        (Y : Type) (_ : AddCommGroup Y) (_ : Module.Free ℤ Y) (_ : Module.Finite ℤ Y) (u₀ : splitTorus (Sp F) Y ⟶ G₀)
        (B : Over (Sp F)) (_ : GrpObj B) (q₀ : G₀ ⟶ B) (j₀ : OAct O B) (ψ : A.left ⟶ B.left),
        IsActPull i₀ i (spMap (algebraMap K F)) φ₀ ∧ IsAbelianScheme B ∧ IsMonHom u₀ ∧ IsKer u₀ q₀ ∧
        (∀ a, i₀.act a ≫ q₀ = q₀ ≫ j₀.act a) ∧ IsActPull j j₀ (spMap (algebraMap F Ω)) ψ := by
  atlas_forward_decl GlobalTheory.TorusPart.exists_finite_torusExtension_act
end

section
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorusPart

theorem exists_finite_polDescent : ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] (c : O →+* O) (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (j₀ : OAct O B) (P : Out.PolAV (Sp Ω))
    (j : OAct O P.A) (ψ : P.A.left ⟶ B.left), IsActPull j j₀ (spMap (algebraMap K Ω)) ψ → IsRosati c P j →
    ∃ F : IntermediateField K Ω, FiniteDimensional K F ∧ ∃ (P₁ : Out.PolAV (Sp F)) (j₁ : OAct O P₁.A)
      (ψ₁ : P₁.A.left ⟶ B.left), IsActPull j₁ j₀ (spMap (algebraMap K F)) ψ₁ ∧ IsRosati c P₁ j₁ := by
  intro O _ _ c K Ω _ _ _ _ B _ hB j₀ P j ψ hpull hros
  haveI := hB.comm
  haveI := hB.proper
  haveI := P.isAb.comm
  obtain ⟨F, hF, H⟩ := GlobalTheory.LBDescent.exists_finite_subextension_cls K Ω B.left P.A.left B.hom P.A.hom ψ
    hpull.1.1 P.L P.isLB
  let f : Sp F ⟶ Sp K := spMap (algebraMap K F)
  let A₁ := (Over.pullback f).obj B
  have hA₁ : IsAbelianScheme A₁ := isAbelianScheme_pullback_obj f B hB
  haveI := hA₁.comm
  haveI := hA₁.smooth
  haveI := hA₁.proper
  have hψ₁ : IsActPull (OAct.pullback f B j₀) j₀ f (pullback.fst B.hom f) := exists_isActPull f j₀
  have hcomp : spMap (algebraMap F Ω) ≫ f = spMap (algebraMap K Ω) := by
    simp only [f, spMap]
    rw [← Spec.map_comp]
    congr 1
  have w : ψ ≫ B.hom = (P.A.hom ≫ spMap (algebraMap F Ω)) ≫ f := by
    rw [Category.assoc, hcomp]
    exact hpull.1.1.w
  let jm : P.A.left ⟶ A₁.left := pullback.lift ψ (P.A.hom ≫ spMap (algebraMap F Ω)) w
  have hjf : jm ≫ pullback.fst B.hom f = ψ := pullback.lift_fst _ _ _
  have hjs : jm ≫ A₁.hom = P.A.hom ≫ spMap (algebraMap F Ω) := pullback.lift_snd _ _ _
  have hj : IsGrpPullback P.A A₁ (spMap (algebraMap F Ω)) jm :=
    IsGrpPullback.cancel hψ₁.1 (hpull.1.congr hcomp.symm hjf.symm) hjs
  obtain ⟨x, hx⟩ := H A₁.left A₁.hom (pullback.fst B.hom f) (IsPullback.of_hasPullback _ _) jm hjf hjs
  obtain ⟨L₁, hL₁, rfl⟩ := CechPic.cls_surj x
  have hw : LBIso P.L (L₁.pull jm) := by
    rw [← CechPic.cls_eq_iff P.isLB (pull_isLB hL₁ jm), CechPic.cls_pull hL₁ jm (pull_isLB hL₁ jm)]
    exact hx.symm
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim F A₁ hA₁
  have hd := GlobalTheory.PolDescent.rigidified_sym_kTriv_descend F Ω (algebraMap F Ω) A₁ P.A jm L₁ P.L hA₁ hj hL₁ P.isLB hw
  have ha := GlobalTheory.AmpleDescent.proper_relAmple_kTriv_of_fieldExtension F Ω (algebraMap F Ω) A₁ P.A jm hj L₁ P.L hL₁
    P.isLB hw P.isAb.proper P.ample P.ktriv
  let P₁ : Out.PolAV (Sp F) :=
    { A := A₁, isAb := hA₁, g := g, smoothDim := hg, L := L₁, isLB := hL₁, rigid := hd.1 P.rigid,
      sym := hd.2.1 P.sym, ample := ha.2.1, ktriv := ha.2.2 }
  have comm : ∀ b, (j.act b).left ≫ jm = jm ≫ ((OAct.pullback f B j₀).act b).left := fun b => by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hjf, hψ₁.2 b, ← Category.assoc, hjf, hpull.2 b]
    · show (j.act b).left ≫ jm ≫ A₁.hom = jm ≫ ((OAct.pullback f B j₀).act b).left ≫ A₁.hom
      rw [Over.w ((OAct.pullback f B j₀).act b), hjs, ← Category.assoc, Over.w (j.act b)]
  exact ⟨F, hF, P₁, OAct.pullback f B j₀, pullback.fst B.hom f, hψ₁, fun a =>
    GlobalTheory.RosatiDescent.rosatiAdj_descend (algebraMap F Ω) hA₁ hj hL₁ P.isLB hw (comm a) (comm (c a)) (hros a)⟩

end GlobalTheory.TorusPart
end
end

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosati_polarization_finite_extension : ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] (c : O →+* O) (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (j₀ : OAct O B) (P : Out.PolAV (Sp Ω))
    (j : OAct O P.A) (ψ : P.A.left ⟶ B.left), IsActPull j j₀ (spMap (algebraMap K Ω)) ψ → IsRosati c P j →
    ∃ F : IntermediateField K Ω, FiniteDimensional K F ∧ ∃ (P₁ : Out.PolAV (Sp F)) (j₁ : OAct O P₁.A)
      (ψ₁ : P₁.A.left ⟶ B.left), IsActPull j₁ j₀ (spMap (algebraMap K F)) ψ₁ ∧ IsRosati c P₁ j₁ := by
  atlas_forward_decl GlobalTheory.TorusPart.exists_finite_polDescent
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

namespace GlobalTheory.TorusPart

theorem isCommMonObj_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G]
    {G' : Over S'} [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : IsCommMonObj G' := by
  obtain ⟨e, he, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  refine ⟨?_⟩
  rw [← cancel_mono e.hom, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
    IsCommMonObj.mul_comm]


end GlobalTheory.TorusPart
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegExtend

open GlobalTheory.CechPic

section Bundle

variable {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]

omit [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] in

theorem pic_local [IsLocalRing O] (c : Pic (Sp O)) : c = 0 := by
  obtain ⟨D, hD, rfl⟩ := cls_surj c
  obtain ⟨i, hi⟩ := exists_chart hD (IsLocalRing.closedPoint O)
  have hV : D.U i = ⊤ := (IsLocalRing.closedPoint_mem_iff _).1 hi
  have := (cls_eq_zero_iff (pull_isLB hD (𝟙 _))).2 (IsoExtend.exists_gen_of_chart hD (𝟙 _) i fun y => by
    rw [hV]; trivial)
  rwa [cls_pull hD, pull_id] at this

theorem generic_props : IsPreimmersion (spMap (algebraMap O K)) ∧ Flat (spMap (algebraMap O K)) ∧
    IsDominant (spMap (algebraMap O K)) := by
  refine ⟨IsPreimmersion.of_isLocalization (nonZeroDivisors O), ?_, ⟨?_⟩⟩
  · exact (HasRingHomProperty.Spec_iff (P := @Flat)).2
      (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat K (nonZeroDivisors O)))
  · exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap O K)).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective O K)]; exact bot_le)

theorem pic_generic [IsLocalRing O] [IsNoetherianRing O] [IsIntegrallyClosed O] (X : Over (Sp O)) [Smooth X.hom]
    [GeometricallyIntegral X.hom] (e : 𝟙_ (Over (Sp O)) ⟶ X) {X' : Scheme.{0}} {t : X' ⟶ Sp K} {ψ : X' ⟶ X.left}
    (h : IsPullback ψ t X.hom (spMap (algebraMap O K))) {a b : Pic X.left} (hab : pull ψ a = pull ψ b) : a = b := by
  obtain ⟨_, _, _⟩ := generic_props (O := O) (K := K)
  refine ZH.EndoExtend.pic_ext (spMap (algebraMap O K)) (ZJ.isNormalScheme_sp O) X e.left (Over.w e)
    ((pic_local _).trans (pic_local _).symm) ?_
  rw [← h.isoPullback_inv_fst, pull_comp, pull_comp, hab]

theorem exists_extension [IsRegularRing O] (X : Over (Sp O)) [Smooth X.hom] [IsProper X.hom]
    [GeometricallyIntegral X.hom] {X' : Scheme.{0}} {t : X' ⟶ Sp K} {ψ : X' ⟶ X.left}
    (h : IsPullback ψ t X.hom (spMap (algebraMap O K))) (L : LB X') (hL : L.IsLB) :
    ∃ M : LB X.left, M.IsLB ∧ LBIso (M.pull ψ) L := by
  obtain ⟨h₁, h₂, _⟩ := generic_props (O := O) (K := K)
  have : IsIntegral X.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian X.hom
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : GeometricallyIntegral t := MorphismProperty.of_isPullback (P := @GeometricallyIntegral) h inferInstance
  have : Smooth t := MorphismProperty.of_isPullback (P := @Smooth) h inferInstance
  have : IsIntegral X' := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian t
  have : IsPreimmersion ψ := MorphismProperty.of_isPullback (P := @IsPreimmersion) h.flip h₁
  have : Flat ψ := MorphismProperty.of_isPullback (P := @Flat) h.flip h₂
  have hY : ∀ y, IsRegularLocalRing ((Sp O).presheaf.stalk y) := fun y => by
    have := y.isPrime
    have := isRegularRing_iff.1 ‹IsRegularRing O› y.asIdeal
    letI : Algebra O ((Sp O).presheaf.stalk y) := StructureSheaf.stalkAlgebra O y
    haveI : IsLocalization.AtPrime ((Sp O).presheaf.stalk y) y.asIdeal := StructureSheaf.IsLocalization.to_stalk O y
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.algEquiv y.asIdeal.primeCompl (Localization.AtPrime y.asIdeal) ((Sp O).presheaf.stalk y)).toRingEquiv
  exact exists_lineBundle_extension_of_generalizing X.left X' ψ (Flat.generalizingMap ψ)
    (fun x => have := ThetaExtend.isRegularRing_stalk hY X.hom x; ThetaExtend.ufd_of_regular _) L hL

theorem exists_bundle [IsRegularLocalRing O] {A : Over (Sp O)} [GrpObj A] {A' : Over (Sp K)} [GrpObj A']
    {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (hA : IsAbelianScheme A)
    (h : IsGrpPullback A' A (spMap (algebraMap O K)) φ) (sq : IsSquare φ φ₂) {P' : LB (A' ⊗ A').left} (hP' : P'.IsLB)
    (r₁ : ∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen)
    (r₂ : ∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen)
    (sy : LBIso P' (P'.pull (lift (snd A' A') (fst A' A')).left)) :
    ∃ P : LB (A ⊗ A).left, P.IsLB ∧ LBIso P' (P.pull φ₂) ∧
      (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧
      (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧
      LBIso P (P.pull (lift (snd A A) (fst A A)).left) := by
  have := isRegularRing_of_isRegularLocalRing O
  have := ThetaExtend.ufd_of_regular O
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have : GeometricallyIntegral A.hom := geometricallyIntegral_of_smooth _
  have := smooth_tensorObj_hom A A
  have := geometricallyIntegral_tensorObj_hom A A
  have : IsProper (A ⊗ A).hom := inferInstanceAs (IsProper (pullback.fst A.hom A.hom ≫ A.hom))
  have h₂ := AbDual.isPullback_prod h.1 h.1 sq.1 sq.2
  obtain ⟨P, hP, e⟩ := exists_extension (A ⊗ A) h₂ P' hP'
  have e₀ : pull φ₂ (cls P hP) = cls P' hP' := (cls_eq_iff (pull_isLB hP φ₂) hP').2 e
  have one : (1 : A' ⟶ A').left ≫ φ = φ ≫ (1 : A ⟶ A).left := by
    have a := congrArg (fun q => q.left) (map_one (pushHom h A'))
    have b := congrArg (fun q => q.left) (GlobalTheory.Mum.Cover.comp_one_pt (G := A) (Over.homMk φ h.1.w :
      Over.mk (A'.hom ≫ spMap (algebraMap O K)) ⟶ A))
    exact a.trans b.symm
  have key : ∀ (a' b' : A' ⟶ A') (a b : A ⟶ A), a'.left ≫ φ = φ ≫ a.left → b'.left ≫ φ = φ ≫ b.left →
      (∃ t : (P'.pull (lift a' b').left).Gen, t.IsGen) → ∃ t : (P.pull (lift a b).left).Gen, t.IsGen := by
    intro a' b' a b ha hb ht
    refine (cls_eq_zero_iff (pull_isLB hP _)).1 (pic_generic A η[A] h.1 ?_)
    have := SiegelPull.lift_sq sq (T := Over.mk (φ ≫ A.hom)) (T' := A') (𝟙 A'.left) a' b' φ a b
      ((Category.id_comp _).trans ha) ((Category.id_comp _).trans hb)
    have e : (lift a' b').left ≫ φ₂ = φ ≫ (lift a b).left := (Category.id_comp _).symm.trans this
    rw [map_zero, cls_pull hP, ← pull_comp, ← e, pull_comp, e₀, ← cls_pull hP']
    exact (cls_eq_zero_iff (pull_isLB hP' _)).2 ht
  refine ⟨P, hP, e.symm, key _ _ _ _ one (by simp) r₁, key _ _ _ _ (by simp) one r₂, ?_⟩
  refine (cls_eq_iff hP (pull_isLB hP _)).1 (pic_generic (A ⊗ A) (lift η[A] η[A]) h₂ ?_)
  have := SiegelPull.lift_sq sq (T := Over.mk (φ₂ ≫ (A ⊗ A).hom)) (T' := A' ⊗ A') (𝟙 _) (snd A' A') (fst A' A')
    φ₂ (snd A A) (fst A A) ((Category.id_comp _).trans sq.2.symm) ((Category.id_comp _).trans sq.1.symm)
  rw [Category.id_comp] at this
  rw [cls_pull hP, ← pull_comp, ← this, pull_comp, e₀, ← cls_pull hP']
  exact (cls_eq_iff hP' (pull_isLB hP' _)).2 sy

end Bundle

section Level

variable {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]

omit [IsDomain O] [IsFractionRing O K] in
theorem spMap_inj {R R' : Type} [CommRing R] [CommRing R'] {f f' : R →+* R'} (e : spMap f = spMap f') : f = f' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective e)

variable {A : Over (Sp O)} [GrpObj A] {A' : Over (Sp K)} [GrpObj A'] {ψ : A'.left ⟶ A.left}

theorem sec_ext (hA : IsAbelianScheme A) {u v : 𝟙_ (Over (Sp O)) ⟶ A}
    (e : spMap (algebraMap O K) ≫ u.left = spMap (algebraMap O K) ≫ v.left) : u = v := by
  have := hA.proper
  exact LabelExt.ext_frac (K := K) (G := A) (y := 𝟙 (Sp O)) e

theorem exists_lev [IsIntegrallyClosed O] (hA : IsAbelianScheme A) (h : IsGrpPullback A' A (spMap (algebraMap O K)) ψ)
    {g n : ℕ} (hn : n ≠ 0) (lev' : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp K)) ⟶ A'))
    (add' : ∀ a b, lev' (a + b) = lev' a * lev' b) (tors' : ∀ a, lev' a ^ n = 1) :
    ∃ lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp O)) ⟶ A), (∀ a b, lev (a + b) = lev a * lev b) ∧
      (∀ a, lev a ^ n = 1) ∧ ∀ a, (lev' a).left ≫ ψ = spMap (algebraMap O K) ≫ (lev a).left := by
  have hy : spMap (algebraMap O K) ≫ 𝟙 (Sp O) = (𝟙_ (Over (Sp K))).hom ≫ spMap (algebraMap O K) := by
    rw [Category.comp_id]; exact (Category.id_comp _).symm
  have ex : ∀ a, ∃ v : Over.mk (𝟙 (Sp O)) ⟶ A, spMap (algebraMap O K) ≫ v.left = (pushHom h _ (lev' a)).left :=
    fun a => LabelExt.lift_tors (K := K) A hA hn hy (pushHom h _ (lev' a)) (by rw [← map_pow, tors', map_one])
  choose lev hlev using ex
  have hl : ∀ a, (lev' a).left ≫ ψ = spMap (algebraMap O K) ≫ (lev a).left := fun a => (hlev a).symm
  let J : Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap (algebraMap O K)) ⟶ 𝟙_ (Over (Sp O)) := toUnit _
  have K1 : ∀ a, J ≫ lev a = pushHom h _ (lev' a) := fun a => by
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    change (toUnit (Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap (algebraMap O K)))).left ≫ (lev a).left =
      (lev' a).left ≫ ψ
    rw [Over.toUnit_left, hl]
    exact congrArg (· ≫ (lev a).left) (Category.id_comp (spMap (algebraMap O K)))
  have K2 : ∀ u v : 𝟙_ (Over (Sp O)) ⟶ A, J ≫ u = J ≫ v → u = v := fun u v e => by
    refine sec_ext (K := K) hA ?_
    have e' := congrArg (fun q => q.left) e
    simp only [Over.comp_left, J, Over.toUnit_left] at e'
    simpa using e'
  refine ⟨lev, fun a b => K2 _ _ ?_, fun a => K2 _ _ ?_, hl⟩
  · rw [MonObj.comp_mul, K1, K1, K1, add', map_mul]
  · rw [MonObj.comp_pow, K1, ← map_pow, tors', map_one, MonObj.comp_one]

omit [IsDomain O] [IsFractionRing O K] in

theorem push_lev (h : IsGrpPullback A' A (spMap (algebraMap O K)) ψ) {u' : 𝟙_ (Over (Sp K)) ⟶ A'}
    {u : 𝟙_ (Over (Sp O)) ⟶ A} (hu : u'.left ≫ ψ = spMap (algebraMap O K) ≫ u.left) (T : Over (Sp K)) :
    pushHom h T (toUnit T ≫ u') = toUnit (Over.mk (T.hom ≫ spMap (algebraMap O K))) ≫ u := by
  apply Over.OverMorphism.ext
  change (toUnit T ≫ u').left ≫ ψ = (toUnit (Over.mk (T.hom ≫ spMap (algebraMap O K))) ≫ u).left
  rw [Over.comp_left, Over.comp_left, Category.assoc, hu, Over.toUnit_left, Over.toUnit_left, ← Category.assoc]
  rfl

end Level

section Extend

open SiegelPull in

theorem extend (O K : Type) [CommRing O] [IsRegularLocalRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    {B : Type} [CommRing B] (ζ : B) (hζ : IsUnit ζ) (g n : ℕ) (hn : n ≠ 0) (hnB : IsUnit (n : B))
    (s' : Sp O ⟶ Sp B) (s₀ : Sp K ⟶ Sp B) (hs₀ : spMap (algebraMap O K) ≫ s' = s₀) (A : Over (Sp O)) [GrpObj A]
    [IsCommMonObj A] (hA : IsAbelianScheme A) (c' : SiegPre g n ζ s₀) (hc' : c'.Principal) (ψ : c'.A.left ⟶ A.left)
    (h : IsGrpPullback c'.A A (spMap (algebraMap O K)) ψ) :
    ∃ c : SiegPre g n ζ s', c.Principal ∧ SiegPB c' c (spMap (algebraMap O K)) := by
  subst hs₀
  obtain ⟨_, _⟩ := isDomain_and_isIntegrallyClosed_of_isRegularLocalRing O
  obtain ⟨φ₂, q₁, q₂⟩ := AbDual.exists_prod_pullback h h
  have sq : IsSquare ψ φ₂ := ⟨q₁, q₂⟩
  obtain ⟨P, hP, e, r₁, r₂, sy⟩ := exists_bundle hA h sq c'.isLB c'.rig₁ c'.rig₂ c'.symm
  have ed : LBIso c'.diag ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull ψ) := diag_iso sq e
  have amp : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) :=
    GlobalTheory.T.relAmple_of_genericFibre_normalLocalDomain O K A c'.A ψ hA h _ _ (pull_isLB hP _) (pull_isLB c'.isLB _) ed hc'.1
  have nd := GlobalTheory.T.nondegenerate_pairing_of_generic_fibre O K A c'.A ψ φ₂ hA h sq P c'.P hP c'.isLB e r₁ r₂ sy amp hc'.2
  obtain ⟨σ, rfl⟩ := Models.RankZero.exists_spMap s'
  have hnO : IsUnit (n : O) := by simpa using hnB.map σ
  obtain ⟨lev, add, tors, hl⟩ := exists_lev (K := K) hA h hn c'.lev c'.lev_add c'.lev_tors
  let k₀ := AlgebraicClosure K
  let xk : Sp k₀ ⟶ Sp K := spMap (algebraMap K k₀)
  let j : O →+* k₀ := (algebraMap K k₀).comp (algebraMap O K)
  have hj : xk ≫ spMap (algebraMap O K) = spMap j := Models.RankZero.spMap_comp _ _
  have hjinj : Function.Injective j := (algebraMap K k₀).injective.comp (IsFractionRing.injective O K)
  let ζO : Oˣ := (hζ.map σ).unit
  have hβ₀ : xk ≫ spMap (algebraMap O K) ≫ spMap σ = spMap (j.comp σ) := by
    rw [← Category.assoc, hj, Models.RankZero.spMap_comp]
  obtain ⟨g1, g2, g3⟩ := c'.geom k₀ xk (j.comp σ) (Units.map j.toMonoidHom ζO) hβ₀ rfl
  have pl : ∀ a, pushHom h (Over.mk xk) (toUnit _ ≫ c'.lev a) =
      toUnit (Over.mk (xk ≫ spMap (algebraMap O K))) ≫ lev a := fun a => push_lev h (hl a) _
  have t1 : ∀ a, (toUnit (Over.mk (xk ≫ spMap (algebraMap O K))) ≫ lev a = 1 ↔ ∃ b, a = n • b) := fun a => by
    rw [← g1 a, ← pl a, ← map_one (pushHom h (Over.mk xk))]
    exact (push_injective h _).eq_iff
  have t2 : ∀ u : Over.mk (xk ≫ spMap (algebraMap O K)) ⟶ A, u ^ n = 1 →
      ∃ a, toUnit _ ≫ lev a = u := fun u hu => by
    obtain ⟨u', rfl⟩ := push_surjective h (Over.mk xk) u
    obtain ⟨a, ha⟩ := g2 u' (push_injective h _ (by rw [map_pow, hu, map_one]))
    exact ⟨a, by rw [← pl a, ha]⟩
  have TT := GlobalTheory.T.levelBasis_every_geometricPoint_localRing O A hA g n hnO lev add tors k₀ _ t1 t2
  have w0 : ∀ a b, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n (toUnit (Over.mk (spMap j)) ≫ lev a)
      (toUnit (Over.mk (spMap j)) ≫ lev b) (unitOn (Units.map j.toMonoidHom (ζO ^ (2 * omegaStd a b)))) :=
    fun a b => by
      rw [← hj, map_zpow]
      exact (weilIs_grpPullback_of_comm (Sp O) (Sp K) A c'.A (spMap (algebraMap O K)) ψ _ _ (pull_isLB hP _)
        (pull_isLB c'.isLB _) h ed (Over.mk xk) n _ _ _ _ _ (congrArg (fun q => q.left) (pl a)).symm
        (congrArg (fun q => q.left) (pl b)).symm).1 (g3 a b)
  refine ⟨{
      A := A
      ab := hA
      P := P
      isLB := hP
      rig₁ := r₁
      rig₂ := r₂
      symm := sy
      lev := lev
      lev_add := add
      lev_tors := tors
      geom := ?_ }, ⟨amp, nd⟩, ψ, φ₂, h, sq, e, hl⟩
  intro k _ _ x β z hx hz
  obtain ⟨ρ, rfl⟩ := Models.RankZero.exists_spMap x
  obtain ⟨c1, c2⟩ := TT k (spMap ρ)
  refine ⟨c1, c2, fun a b => ?_⟩
  have hβ : ρ.comp σ = β := spMap_inj ((Models.RankZero.spMap_comp σ ρ).symm.trans hx)
  have hzz : Units.map ρ.toMonoidHom ζO = z := Units.ext (by rw [hz, ← hβ]; rfl)
  have := GlobalTheory.T.commutatorPairing_determined_at_genericPoint O A hA P hP r₁ r₂ amp n (Nat.pos_of_ne_zero hn) hnO (lev a) (lev b) (tors a) (tors b)
    (ζO ^ (2 * omegaStd a b)) k₀ j hjinj (w0 a b) k ρ
  rwa [map_zpow, hzz] at this

end Extend

section Main

theorem zero_case {g : ℕ} {K : Type} [Field K] [CharZero K] {s₀ : Sp K ⟶ Sp (cycAway 0)}
    (c' : SiegPre g 0 (zetaAway 0) s₀) : g = 0 ∧ IsIso c'.A.hom := by
  have hz1 : zetaAway 0 = 1 := Subtype.ext (by simp [zetaAway, zeta])
  have key : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp K),
      (∀ a, toUnit (Over.mk x) ≫ c'.lev a = 1 ↔ a = 0) ∧ ∀ u : Over.mk x ⟶ c'.A, ∃ a, toUnit _ ≫ c'.lev a = u := by
    intro k _ _ x
    obtain ⟨β, hβ⟩ := Models.RankZero.exists_spMap (x ≫ s₀)
    obtain ⟨g1, g2, -⟩ := c'.geom k x β 1 hβ (by rw [hz1, map_one]; rfl)
    exact ⟨fun a => (g1 a).trans (by simp), fun u => g2 u (pow_zero u)⟩
  have lev0 : c'.lev 0 = 1 := by
    have := c'.lev_add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have iso : IsIso c'.A.hom := by
    refine Models.RankZero.isIso_of_no_torsion GlobalTheory.card_torsion_abelianVariety c'.A c'.ab fun k _ _ x => ?_
    obtain ⟨ρ, rfl⟩ := Models.RankZero.exists_spMap x
    have : CharZero k := charZero_of_injective_ringHom ρ.injective
    refine ⟨2, one_lt_two, two_ne_zero, fun u hu => ?_⟩
    obtain ⟨a, rfl⟩ := (key k _).2 u
    have h2 : toUnit (Over.mk (spMap ρ)) ≫ c'.lev (a + a) = 1 := by
      rw [c'.lev_add, MonObj.comp_mul, ← sq, hu]
    have ha : a = 0 := by
      have h0 := ((key k _).1 _).1 h2
      funext i
      have := congrFun h0 i
      simp only [Pi.add_apply, Pi.zero_apply] at this
      show a i = 0
      omega
    rw [ha, lev0, MonObj.comp_one]
  refine ⟨?_, iso⟩
  by_contra hg
  let k := AlgebraicClosure K
  let a : Fin g ⊕ Fin g → ℤ := Pi.single (Sum.inl ⟨0, Nat.pos_of_ne_zero hg⟩) 1
  have h0 := ((key k (spMap (algebraMap K k))).1 a).1 (Models.RankZero.hom_unique iso _ _)
  have := congrFun h0 (Sum.inl ⟨0, Nat.pos_of_ne_zero hg⟩)
  simp [a] at this

theorem exists_principal_extension : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R] (b : cycAway n →+* R) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → ∀ (p : Sp R) [p.asIdeal.IsPrime], IsAbelianScheme ((Over.pullback (spMap (algebraMap R (Localization.AtPrime p.asIdeal)))).obj G₁) → ∀ (κ : Sp (FractionRing R) ⟶ Sp (Localization.AtPrime p.asIdeal)) (s' : Sp (Localization.AtPrime p.asIdeal) ⟶ Sp (cycAway n)), κ ≫ spMap (algebraMap R (Localization.AtPrime p.asIdeal)) = jK R → κ ≫ s' = y ≫ F.s → ∃ (c : SiegPre g n (zetaAway n) s') (c' : SiegPre g n (zetaAway n) (y ≫ F.s)), c.Principal ∧ SiegPB c' c κ ∧ SiegPB c' F.univ y := by
  intro g n F R _ _ _ _ b G₁ _ _ y A₁ _ i₁ β hsemi hp1 hp2 p _ hab κ s' hκ hs'
  let O := Localization.AtPrime p.asIdeal
  have : IsRegularLocalRing O := isRegularRing_iff.mp (isRegularRing_of_isRegularLocalRing R) p.asIdeal
  obtain ⟨κ₀, rfl⟩ := Models.RankZero.exists_spMap κ
  have hκ₀ : κ₀.comp (algebraMap R O) = algebraMap R (FractionRing R) :=
    spMap_inj ((Models.RankZero.spMap_comp _ _).symm.trans hκ)
  letI : Algebra O (FractionRing R) := κ₀.toAlgebra
  haveI : IsScalarTower R O (FractionRing R) :=
    IsScalarTower.of_algebraMap_eq fun r => (RingHom.congr_fun hκ₀ r).symm
  haveI : IsFractionRing O (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.asIdeal.primeCompl O (FractionRing R)
  have hAp := isGrpPullback_pullback G₁ (spMap (algebraMap R O))
  haveI : IsCommMonObj ((Over.pullback (spMap (algebraMap R O))).obj G₁) :=
    GlobalTheory.TorusPart.isCommMonObj_of_isGrpPullback hAp
  obtain ⟨φ', hφ', -⟩ := GlobalTheory.PlaceModel.exists_factor_pullback hAp hp1 (spMap κ₀) hκ
  obtain ⟨⟨c'₀, hpb⟩, hprin⟩ := siegPre_pullback g n (cycAway n) (zetaAway n) F.X (Sp (FractionRing R)) F.s
    (y ≫ F.s) y F.univ rfl
  have pc' := hprin c'₀ hpb F.princ
  obtain ⟨φc, -, hφc, -⟩ := id hpb
  obtain ⟨e, he, -⟩ := grpPullback_iso hφc hp2
  have hψ : IsGrpPullback c'₀.A ((Over.pullback (spMap (algebraMap R O))).obj G₁) (spMap κ₀) (e.hom.left ≫ φ') :=
    ((isGrpPullback_of_iso e).comp hφ').congr (Category.id_comp _) rfl
  by_cases hn : n = 0
  · subst hn
    have : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
    obtain ⟨rfl, iso⟩ := zero_case c'₀
    exact ⟨Models.RankZero.zeroSieg 0 (zetaAway 0) s', c'₀, Models.RankZero.principal_zeroSieg s',
      Models.RankZero.siegPB_zero iso (Models.RankZero.isIso_unit _) _, hpb⟩
  · have hζ : IsUnit (zetaAway n) := by
      have h1 : zetaAway n ^ n = 1 := Subtype.ext (by
        simpa [zetaAway, zeta] using (Complex.isPrimitiveRoot_exp n hn).pow_eq_one)
      exact ⟨Units.ofPowEqOne _ n h1 hn, rfl⟩
    obtain ⟨c, hc, pb⟩ := extend O (FractionRing R) (zetaAway n) hζ g n hn (GlobalTheory.SiegelTor.isUnit_natCast hn) s'
      (y ≫ F.s) hs' _ hab c'₀ pc' _ hψ
    exact ⟨c, c'₀, hc, pb, hpb⟩

end Main

end GlobalTheory.SiegExtend
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principalSiegelObject_extension_abelianLocus : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R] (b : cycAway n →+* R) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → ∀ (p : Sp R) [p.asIdeal.IsPrime], IsAbelianScheme ((Over.pullback (spMap (algebraMap R (Localization.AtPrime p.asIdeal)))).obj G₁) → ∀ (κ : Sp (FractionRing R) ⟶ Sp (Localization.AtPrime p.asIdeal)) (s' : Sp (Localization.AtPrime p.asIdeal) ⟶ Sp (cycAway n)), κ ≫ spMap (algebraMap R (Localization.AtPrime p.asIdeal)) = jK R → κ ≫ s' = y ≫ F.s → ∃ (c : SiegPre g n (zetaAway n) s') (c' : SiegPre g n (zetaAway n) (y ≫ F.s)), c.Principal ∧ SiegPB c' c κ ∧ SiegPB c' F.univ y := by
  atlas_forward_decl GlobalTheory.SiegExtend.exists_principal_extension
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbChart

theorem exists_siegPre_localization : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R] (b : cycAway n →+* R) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → ∀ (p : Sp R) [p.asIdeal.IsPrime], p ∈ abLocus G₁ → ∀ (κ : Sp (FractionRing R) ⟶ Sp (Localization.AtPrime p.asIdeal)) (s' : Sp (Localization.AtPrime p.asIdeal) ⟶ Sp (cycAway n)), κ ≫ spMap (algebraMap R (Localization.AtPrime p.asIdeal)) = jK R → κ ≫ s' = y ≫ F.s → ∃ (c : SiegPre g n (zetaAway n) s') (c' : SiegPre g n (zetaAway n) (y ≫ F.s)), c.Principal ∧ SiegPB c' c κ ∧ SiegPB c' F.univ y := fun g n F R _ _ _ _ b G₁ _ _ y A₁ _ i₁ β hG h₁ h₂ p _ hp κ s' hκ hs =>
  GlobalTheory.T.exists_principalSiegelObject_extension_abelianLocus g n F R b G₁ y A₁ i₁ β hG h₁ h₂ p (GlobalTheory.T.semiAbelian_isAbelianScheme_localization_abelianLocus R G₁ hG p hp) κ s' hκ hs

theorem exists_spMap_ext : ∀ (n : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (b : cycAway n →+* R) (x : Sp (FractionRing R) ⟶ Sp (cycAway n)), ∃ s : Sp R ⟶ Sp (cycAway n), jK R ≫ s = x := by
  intro n R _ _ _ b x
  obtain ⟨φ, rfl⟩ : ∃ φ : cycAway n →+* FractionRing R, spMap φ = x := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  let A := algebraMap R (FractionRing R)
  have hAi : Function.Injective A := IsFractionRing.injective R (FractionRing R)
  have hgen : ∀ (w : ℂ) (hw : w ∈ cycAway n), φ ⟨w, hw⟩ ∈ A.range := by
    intro w hw
    induction hw using Subring.closure_induction with
    | mem w hw =>
      rcases hw with rfl | rfl
      · rcases Nat.eq_zero_or_pos n with h0 | hn
        · subst h0
          have : (⟨zeta 0, Subring.subset_closure (Or.inl rfl)⟩ : cycAway 0) = 1 := Subtype.ext (by simp [zeta])
          rw [this, map_one]; exact A.range.one_mem
        · have hpow : (⟨zeta n, Subring.subset_closure (Or.inl rfl)⟩ : cycAway n) ^ n = 1 :=
            Subtype.ext (by simpa [zeta] using (Complex.isPrimitiveRoot_exp n hn.ne').pow_eq_one)
          have hI : IsIntegral R (φ ⟨zeta n, Subring.subset_closure (Or.inl rfl)⟩) := by
            refine IsIntegral.of_pow hn ?_
            rw [← map_pow, hpow, map_one]; exact isIntegral_one
          obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hI
          exact ⟨r, hr⟩
      · rcases Nat.eq_zero_or_pos n with h0 | hn
        · subst h0
          have : (⟨((0 : ℕ) : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ : cycAway 0) = 0 := Subtype.ext (by simp)
          rw [this, map_zero]; exact A.range.zero_mem
        · set u : cycAway n := ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩
          have hu : u * (n : cycAway n) = 1 := Subtype.ext (by simp [u, hn.ne'])
          have e1 : φ u * (n : FractionRing R) = 1 := by rw [← map_natCast φ, ← map_mul, hu, map_one]
          have e2 : A (b u) * (n : FractionRing R) = 1 := by rw [← map_natCast A, ← map_mul, ← map_natCast b, ← map_mul, hu, map_one, map_one]
          have hn0 : (n : FractionRing R) ≠ 0 := right_ne_zero_of_mul_eq_one e1
          exact ⟨b u, mul_right_cancel₀ hn0 (e2.trans e1.symm)⟩
    | zero => exact ⟨0, by rw [map_zero]; exact (map_zero φ).symm⟩
    | one => exact ⟨1, by rw [map_one]; exact (map_one φ).symm⟩
    | add w v hw hv ihw ihv =>
      have : (⟨w + v, add_mem hw hv⟩ : cycAway n) = ⟨w, hw⟩ + ⟨v, hv⟩ := rfl
      rw [this, map_add]; exact A.range.add_mem ihw ihv
    | neg w hw ih =>
      have : (⟨-w, neg_mem hw⟩ : cycAway n) = -⟨w, hw⟩ := rfl
      rw [this, map_neg]; exact A.range.neg_mem ih
    | mul w v hw hv ihw ihv =>
      have : (⟨w * v, mul_mem hw hv⟩ : cycAway n) = ⟨w, hw⟩ * ⟨v, hv⟩ := rfl
      rw [this, map_mul]; exact A.range.mul_mem ihw ihv
  let e : R ≃+* A.range := RingEquiv.ofBijective A.rangeRestrict ⟨fun a a' h => hAi (congrArg Subtype.val h), A.rangeRestrict_surjective⟩
  let ψ : cycAway n →+* R := (e.symm : A.range →+* R).comp (φ.codRestrict A.range fun z => hgen z.1 z.2)
  have hψ : A.comp ψ = φ := by
    ext z
    have h := congrArg Subtype.val (e.apply_symm_apply ⟨φ z, hgen z.1 z.2⟩)
    exact h
  refine ⟨spMap ψ, ?_⟩
  exact (spMap_comp ψ A).symm.trans (congrArg spMap hψ)

theorem asIdeal_eq_bot_of_charZero : ∀ (n : ℕ) (K : Type) [Field K] [CharZero K] (x : Sp K ⟶ Sp (cycAway n)) (q : Sp K), (x q).asIdeal = ⊥ := by
  intro n K _ _ x q
  obtain ⟨φ, rfl⟩ : ∃ φ : cycAway n →+* K, spMap φ = x := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  have hq : q.asIdeal = ⊥ := (Ideal.eq_bot_or_top q.asIdeal).resolve_right q.isPrime.ne_top
  change Ideal.comap φ q.asIdeal = ⊥
  rw [hq, ← RingHom.ker_eq_comap_bot]
  by_contra hne
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have halg : IsAlgebraic ℤ a := by
    have hC : ∀ z ∈ cycAway n, IsIntegral ℚ z := by
      intro z hz
      refine Subring.closure_le (t := (integralClosure ℚ ℂ).toSubring) |>.2 ?_ hz
      rintro w (rfl | rfl)
      · show IsIntegral ℚ (Complex.exp (2 * ↑Real.pi * Complex.I / ↑n))
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simpa using (isIntegral_one : IsIntegral ℚ (1 : ℂ))
        · exact ((Complex.isPrimitiveRoot_exp n hn.ne').isIntegral hn).tower_top
      · show IsIntegral ℚ ((n : ℂ)⁻¹)
        simpa using (isIntegral_algebraMap (R := ℚ) (A := ℂ) (x := ((n : ℚ)⁻¹)))
    have h1 : IsAlgebraic ℚ (a : ℂ) := (hC a a.2).isAlgebraic
    have h2 : IsAlgebraic ℤ (a : ℂ) := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).2 h1
    exact (isAlgebraic_algHom_iff ((cycAway n).subtype.toIntAlgHom) Subtype.val_injective).1 h2
  have := Ideal.comap_ne_bot_of_algebraic_mem ha0 ha halg
  apply this
  rw [eq_bot_iff]
  intro m hm
  rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast] at hm
  exact (Ideal.mem_bot).2 (Int.cast_eq_zero.1 hm)

theorem mem_range_of_mem_abLocus : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) [S.IsSeparated] (j : F.X ⟶ S) [IsOpenImmersion j] (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R] (b : cycAway n →+* R) (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → y ≫ j = jK R ≫ ξ → ∀ p : Sp R, p ∈ abLocus G₁ → ξ p ∈ Set.range j := by
  intro g n F S _ j _ R _ _ _ _ b ξ G₁ _ _ y A₁ _ i₁ β hG h₁ h₂ hy p hp
  haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
  have hu : ∀ x : p.asIdeal.primeCompl, IsUnit (algebraMap R (FractionRing R) x) := fun x =>
    IsLocalization.map_units (FractionRing R)
      (⟨x.1, mem_nonZeroDivisors_of_ne_zero (fun h => x.2 (h ▸ p.asIdeal.zero_mem))⟩ : nonZeroDivisors R)
  let lf : Localization.AtPrime p.asIdeal →+* FractionRing R := IsLocalization.lift hu
  let ιp := spMap (algebraMap R (Localization.AtPrime p.asIdeal))
  let κ : Sp (FractionRing R) ⟶ Sp (Localization.AtPrime p.asIdeal) := spMap lf
  have hκ : κ ≫ ιp = jK R := by
    rw [← spMap_comp]
    exact congrArg spMap (IsLocalization.lift_comp hu)
  have hnorm := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2
  obtain ⟨s, hs⟩ := exists_spMap_ext n R b (y ≫ F.s)
  have hs' : κ ≫ ιp ≫ s = y ≫ F.s := by rw [← Category.assoc, hκ, hs]
  obtain ⟨c, c', hc, m₁, m₂⟩ := exists_siegPre_localization g n F R b G₁ y A₁ i₁ β hG h₁ h₂ p hp κ (ιp ≫ s) hκ hs'
  have hinj : Function.Injective lf := by
    refine (IsLocalization.lift_injective_iff hu).2 fun x x' => ?_
    rw [(IsLocalization.injective (Localization.AtPrime p.asIdeal) (Ideal.primeCompl_le_nonZeroDivisors p.asIdeal)).eq_iff,
      (IsFractionRing.injective R (FractionRing R)).eq_iff]
  haveI hdom : IsDominant κ := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical lf).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot lf).1 hinj]; exact bot_le)⟩
  have hdense : Dense {x : Sp (Localization.AtPrime p.asIdeal) | ((ιp ≫ s) x).asIdeal = ⊥} := by
    refine Dense.mono ?_ hdom.denseRange
    rintro _ ⟨q, rfl⟩
    show ((ιp ≫ s) (κ q)).asIdeal = ⊥
    rw [← Scheme.Hom.comp_apply, hs']
    exact asIdeal_eq_bot_of_charZero n (FractionRing R) (y ≫ F.s) q
  obtain ⟨f, hfs, hf⟩ := F.rep _ (ιp ≫ s) c inferInstance hdense hc
  have hfy : κ ≫ f = y := F.inj (FractionRing R) (κ ≫ f) y (y ≫ F.s) c'
    (by rw [Category.assoc, hfs, hs']) (GlobalTheory.SiegelPullComp.pb_comp hf m₁) m₂
  have hξ : ιp ≫ ξ = f ≫ j := by
    refine ext_of_isDominant κ ?_
    rw [← Category.assoc, hκ, ← hy, ← Category.assoc, hfy]
  refine ⟨f (closedPoint (Localization.AtPrime p.asIdeal)), ?_⟩
  change (f ≫ j) (closedPoint _) = ξ p
  rw [← hξ]
  change ξ (ιp (closedPoint _)) = ξ p
  congr 1
  apply PrimeSpectrum.ext
  exact Localization.AtPrime.comap_maximalIdeal

end GlobalTheory.AbChart
end
end
