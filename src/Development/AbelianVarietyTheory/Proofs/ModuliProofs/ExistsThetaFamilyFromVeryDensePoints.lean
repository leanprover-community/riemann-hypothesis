import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalMultiplicationPullbackThetaEmbeddingI
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SpMapCompRingHomComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFlatProjectiveThroughPointsGoodFibres
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmoothOfRelDimOfIsUnitProperFlat
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeometricallyConnectedOpenConditionSmoothProjectStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffineStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionCoordsThetaTimesRoots
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalMultiplicationPullbackThetaEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EmbeddedAbelianVarietyCutOutByTorsionForms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasThStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyAdditionMorphismThetaLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsInversionEndomorphismsThetaLevelFamily
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GrpObjOfDenseFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSectionOfDense
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBasicOpenKTrivOfFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescended
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLevelCoverOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AlgebraMapSurjectiveOfUnramifiedOfUniquePoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelEqOfPowEqOfHasTh
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIdealOfLocally
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_smoothOfRelDim_of_isUnit_proper_flat : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (g : ℕ) (K : Type) [Field K] (x : R →+* K), IsProper s → Flat s → SmoothOfRelativeDimension g (pullback.snd s (spMap x)) → ∃ f : R, x f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → SmoothOfRelativeDimension g (pullback.snd s (spMap φ)) := by
  first | exact @GlobalTheory.SmoothNearFibre.exists_smoothOfRelativeDimension_of_isUnit | exact GlobalTheory.SmoothNearFibre.exists_smoothOfRelativeDimension_of_isUnit | (intros; apply GlobalTheory.SmoothNearFibre.exists_smoothOfRelativeDimension_of_isUnit <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem of_local_near_veryDense (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q]
    (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (P : Set (Ideal R))
    (hP : ∀ (q : Ideal R) (f : R), q.IsPrime → f ∉ q → ∃ p ∈ P, p.IsPrime ∧ q ≤ p ∧ f ∉ p)
    (h : ∀ q ∈ P, ∃ f : R, f ∉ q ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
      Q (pullback.snd s (spMap φ))) : Q s := by
  let S : Set R := {f | ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
      Q (pullback.snd s (spMap φ))}
  have hS : Ideal.span S = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨p, hp, -, hmp, -⟩ := hP m 1 hm.isPrime ((Ideal.ne_top_iff_one m).1 hm.ne_top)
    obtain ⟨f, hf, hfS⟩ := h p hp
    exact hf (hmp (hle (Ideal.subset_span hfS)))
  have hS' : Ideal.span (Set.range (fun f : S => (f : R))) = ⊤ := by
    rw [Subtype.range_coe]; exact hS
  refine IsZariskiLocalAtTarget.of_openCover (P := Q)
    (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of R) (fun f : S => (f : R)) hS').openCover ?_
  intro i
  exact (show S from i).2 (Localization.Away ((show S from i) : R)) (algebraMap R _)
    (IsLocalization.Away.algebraMap_isUnit _)

theorem smooth_and_geomConnected_of_veryDense : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (g : ℕ) (P : Set (Ideal R)), (∀ (q : Ideal R) (f : R), q.IsPrime → f ∉ q → ∃ p ∈ P, p.IsPrime ∧ q ≤ p ∧ f ∉ p) → IsProjOver s → Flat s → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K), RingHom.ker x = q ∧ SmoothOfRelativeDimension g (pullback.snd s (spMap x)) ∧ GeometricallyConnected (pullback.snd s (spMap x))) → SmoothOfRelativeDimension g s ∧ GeometricallyConnected s := by
  intro R _ _ Z s g P hP hproj hflat h
  have hsm : SmoothOfRelativeDimension g s := by
    have : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension.{0} g) := HasRingHomProperty.instIsZariskiLocalAtTarget _
    refine of_local_near_veryDense (@SmoothOfRelativeDimension.{0} g) R Z s P hP ?_
    intro q hq
    obtain ⟨K, _, x, hx, h1, -⟩ := h q hq
    obtain ⟨f, hf, H⟩ := GlobalTheory.T.exists_smoothOfRelDim_of_isUnit_proper_flat R Z s g K x (projProper R Z s hproj) hflat h1
    exact ⟨f, by rw [← hx]; exact hf, H⟩
  refine ⟨hsm, ?_⟩
  have : IsZariskiLocalAtTarget (@GeometricallyConnected.{0}) := by
    rw [GeometricallyConnected.eq_geometrically]; infer_instance
  refine of_local_near_veryDense (@GeometricallyConnected.{0}) R Z s P hP ?_
  intro q hq
  obtain ⟨K, _, x, hx, -, h2⟩ := h q hq
  obtain ⟨f, hf, H⟩ := GlobalTheory.T.geometricallyConnected_open_condition_smooth_projective R Z s K x hproj (SmoothOfRelativeDimension.smooth g s) h2
  exact ⟨f, by rw [← hx]; exact hf, H⟩

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_sectionCoords_theta_times_roots : Out.Laws → Out.Laws2 → ∀ (g m N' : ℕ), Odd N' → m ^ 2 ∣ N' → ∃ (e : Ix g (N' ^ 2) → Ix g (N' ^ 2) → ℕ) (idx : Ix g (N' ^ 2) → Ix g (N' ^ 2) → Ix g (N' ^ 2)), ∀ (o : Type) [CommRing o] (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (R : Type) [CommRing R] (β : o →+* R) (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R) σ, x ≫ s = spMap β → t.HasTh x v → Ideal.span (Set.range v) = ⊤ → t.Emb m (Over.mk x) σ → ∀ h (y : Sp R ⟶ (Over.mk x ⊗ t.A).left), y = (lift (𝟙 (Over.mk x)) (((Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ t.lab h) ^ N')).left → ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R'), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ SecCoord _ σ (spMap φ ≫ y) (fun a => φ (β (b.ζ ^ e a h : oˣ) * v (idx a h))) := by
  first | exact @GlobalTheory.torsion_secCoord | exact GlobalTheory.torsion_secCoord | (intros; apply GlobalTheory.torsion_secCoord <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeddedAbelianVariety_cutOut_by_torsionForms : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)), ∃ (Hh : Type) (_ : Finite Hh) (hh : Hh → Ix g ((n ^ j) ^ 2)) (Q : Polynomial ℚ) (d : ℕ), ∀ (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap β)) σ (p : Hh → Ix g ((n ^ j) ^ 2) → K), t.Emb (n ^ 2) (Over.mk (𝟙 _)) σ → (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab (hh h) ^ n ^ j)).left (p h)) → CutBy (idealOf (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _)) Q d p := by
  first | exact @GlobalTheory.cutBy_embedded_abelian | exact GlobalTheory.cutBy_embedded_abelian | (intros; apply GlobalTheory.cutBy_embedded_abelian <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.FamilyScheme

theorem spMap_id (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _

theorem exists_retraction {K R' : Type} [Field K] [CommRing R'] (φ : K →+* R') (hφ : IsOpenImmersion (spMap φ))
    (p : Sp K) (hp : p ∈ Set.range (spMap φ)) : ∃ ψ : R' →+* K, ψ.comp φ = RingHom.id K := by
  haveI : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  haveI : IsIso (spMap φ) := isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by
    rw [eq_top_iff]
    intro q _
    rw [Subsingleton.elim q p]
    exact hp)
  refine ⟨(Spec.preimage (inv (spMap φ))).hom, ?_⟩
  have h : spMap ((Spec.preimage (inv (spMap φ))).hom.comp φ) = spMap (RingHom.id K) := by
    rw [spMap_id, spMap_comp]
    have : spMap (Spec.preimage (inv (spMap φ))).hom = inv (spMap φ) := Spec.map_preimage _
    rw [this, IsIso.inv_hom_id]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem secCoord_of_local {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {I : Type} {th : I → M.Sec} {K R' : Type} [Field K]
    [CommRing R'] {y : Sp K ⟶ X} {v : I → K} (φ : K →+* R') (hφ : IsOpenImmersion (spMap φ)) (p : Sp K)
    (hp : p ∈ Set.range (spMap φ)) (h : SecCoord M th (spMap φ ≫ y) (fun i => φ (v i))) : SecCoord M th y v := by
  obtain ⟨ψ, hψ⟩ := exists_retraction φ hφ p hp
  have h1 := (Coord.secCoord_bc_scale_unique X M I th R' _ _ hM h).1 K ψ
  rw [← Category.assoc, ← spMap_comp, hψ, spMap_id, Category.id_comp] at h1
  have e : (fun i => ψ (φ (v i))) = v := funext fun i => RingHom.congr_fun hψ (v i)
  rwa [e] at h1

theorem projRep_congr {R σ : Type} [CommRing R] {I : Ideal (MvPolynomial σ R)} {Z : Scheme.{0}} {s : Z ⟶ Sp R}
    {M M' : LB Z} {th : σ → M.Sec} {th' : σ → M'.Sec} (hM' : M'.IsLB) (h : ProjRep I s M th)
    (e : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Z) (w : σ → T), SecCoord M' th' y w ↔ SecCoord M th y w) :
    ProjRep I s M' th' := by
  refine ⟨hM', fun T _ β x v hx hv => h.2.1 T β x v hx ((e T x v).1 hv), fun T _ β v hu hF => ?_⟩
  simp only [e]
  exact h.2.2 T β v hu hF

theorem exists_emb (l1 : Out.Laws) (l2 : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {K : Type} [Field K] {s : Sp K ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) (m : ℕ) (v : Ix g (N' ^ 2) → K)
    (hm : m ^ 2 ∣ N') (h2 : 2 ≤ m) (hth : t.HasTh (𝟙 _) v) :
    ∃ σ, t.Emb m (Over.mk (𝟙 _)) σ ∧
      ProjRep (idealOf (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _)) (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ := by
  obtain ⟨R', _, φ, σ, hφ, hp, hE, hP⟩ := GlobalTheory.T.exists_local_multiplicationPullback_theta_embedding l1 l2 o g N' J b _ s t m K (𝟙 _) v hm h2 hth
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  obtain ⟨ψ, hψ⟩ := exists_retraction φ hφ _ hp
  let h : Over.mk (𝟙 (Sp K)) ⟶ Over.mk (spMap φ ≫ 𝟙 (Sp K)) := Over.homMk (spMap ψ) (by
    show spMap ψ ≫ spMap φ ≫ 𝟙 _ = 𝟙 _
    rw [Category.comp_id, ← spMap_comp, hψ, spMap_id])
  obtain ⟨σ', hE', hc⟩ := GlobalTheory.T.thetaEmbeddingSections_baseChange_affine l2 o g N' J b _ s t m _ _ h σ
    (inferInstanceAs (IsAffine (Spec _))) (inferInstanceAs (IsAffine (Spec _))) hE
  refine ⟨σ', hE', ?_⟩
  obtain ⟨th', hP', hc'⟩ := RepBC.projRep_baseChange R' K _ ψ _ _ _ _ _ (h ▷ t.A).left _ σ hP
    (EmbedLocal.isPullback_whisker t.A h)
  exact ideals_homogeneous.2.2 K _ _ _ _ _ σ' (projRep_congr (LB.isLB_linComb t.isLB _ _) hP'
    fun T _ y w => (hc T y w).trans (hc' T y w).symm)

section Unit
variable {S : Scheme.{0}} (A : Over S)

def unitInv : A ⟶ Over.mk (𝟙 S) ⊗ A := lift (Over.homMk A.hom (by simp)) (𝟙 A)

theorem unitInv_snd : (unitInv A).left ≫ (snd (Over.mk (𝟙 S)) A).left = 𝟙 _ := by
  rw [← Over.comp_left, unitInv, lift_snd]; rfl

theorem to_base_ext {T : Over S} (f f' : T ⟶ Over.mk (𝟙 S)) : f = f' :=
  Over.mkIdTerminal.hom_ext f f'

theorem snd_unitInv : (snd (Over.mk (𝟙 S)) A).left ≫ (unitInv A).left = 𝟙 _ := by
  rw [← Over.comp_left]
  have : snd (Over.mk (𝟙 S)) A ≫ unitInv A = 𝟙 _ :=
    CartesianMonoidalCategory.hom_ext _ _ (to_base_ext _ _) (by simp [unitInv])
  rw [this]; rfl

theorem unitInv_fst : (unitInv A).left ≫ (fst (Over.mk (𝟙 S)) A).left = A.hom := by
  rw [← Over.comp_left, unitInv, lift_fst]; rfl

theorem pt_unitInv (z : Over.mk (𝟙 S) ⟶ A) : z.left ≫ (unitInv A).left = (lift (𝟙 (Over.mk (𝟙 S))) z).left := by
  rw [← Over.comp_left]
  congr 1
  exact CartesianMonoidalCategory.hom_ext _ _ (to_base_ext _ _) (by simp [unitInv])

theorem isPullback_unitInv : IsPullback (unitInv A).left A.hom (fst (Over.mk (𝟙 S)) A).left (𝟙 S) := by
  haveI : IsIso (unitInv A).left := ⟨_, unitInv_snd A, snd_unitInv A⟩
  exact IsPullback.of_horiz_isIso ⟨by rw [unitInv_fst, Category.comp_id]⟩

def chartPullUnit (L : LB A.left) (k : ℕ) (a : ℤ) (ha : a = k) :
    ChartPull (lbPow L k) (Out.LPow A L a (Over.mk (𝟙 S))) (unitInv A).left :=
  have le : ∀ j : PUnit → L.ι, LB.wchart L (fun _ : PUnit => 𝟙 A.left) j ≤ (unitInv A).left ⁻¹ᵁ
      LB.wchart L (fun _ : Fin 1 => (snd (Over.mk (𝟙 S)) A).left) (fun _ => j PUnit.unit) :=
    fun j y hy => Set.mem_iInter.2 fun _ => by
      have h1 : y ∈ L.U (j PUnit.unit) := Set.mem_iInter.1 hy PUnit.unit
      show ((unitInv A).left ≫ (snd (Over.mk (𝟙 S)) A).left) y ∈ L.U (j PUnit.unit)
      rw [unitInv_snd]; exact h1
  { idx := fun j _ => j PUnit.unit
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L (fun _ : PUnit => 𝟙 A.left) (fun _ => (k : ℤ)) (𝟙 _) y j j' hj hj').trans
        (Eq.trans ?_ (gm_linComb L (fun _ : Fin 1 => (snd (Over.mk (𝟙 S)) A).left) (fun _ => a) (unitInv A).left y _ _
          (le j hj) (le j' hj')).symm)
      rw [Fintype.prod_unique, Fintype.prod_unique, unitInv_snd, Category.comp_id, ha] }

end Unit

theorem prop_pullback_snd (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange] {X Z S S' : Scheme.{0}}
    {φ : X ⟶ Z} {a : X ⟶ S'} {s : Z ⟶ S} {x : S' ⟶ S} (h : IsPullback φ a s x) (ha : P a) : P (pullback.snd s x) :=
  P.of_isPullback (IsPullback.of_horiz_isIso (fst := h.isoPullback.inv) (snd := pullback.snd s x) (f := a) (g := 𝟙 S')
    ⟨by rw [h.isoPullback_inv_snd, Category.comp_id]⟩) ha

theorem exists_section {R σ : Type} [CommRing R] [IsReduced R] {I : Ideal (MvPolynomial σ R)} {Z : Over (Sp R)}
    {M : LB Z.left} {th : σ → M.Sec} (hP : ProjRep I Z.hom M th) (p : σ → R) {P : Set (Ideal R)} (hvd : VeryDense P)
    (h : ∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K) (y : Sp K ⟶ Z.left), RingHom.ker x = q ∧
      y ≫ Z.hom = spMap x ∧ SecCoord M th y (fun a => x (p a))) :
    ∃ sc : Out.baseOver (Sp R) ⟶ Z, SecCoord M th sc.left p := by
  have hu : Ideal.span (Set.range p) = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨q', hq', hpr, hqq, -⟩ := hvd q 1 hq.isPrime ((Ideal.ne_top_iff_one q).1 hq.ne_top)
    obtain ⟨K, _, x, y, hx, hy, hc⟩ := h q' hq'
    have h1 := (hP.2.1 K x y _ hy hc).1
    have h2 : Ideal.span (Set.range fun a => x (p a)) ≤ ⊥ := by
      rw [Ideal.span_le]
      rintro _ ⟨a, rfl⟩
      have h3 : p a ∈ RingHom.ker x := by
        rw [hx]
        exact hqq (hle (Ideal.subset_span ⟨a, rfl⟩))
      exact h3
    rw [h1] at h2
    exact absurd (top_le_iff.1 h2) bot_ne_top
  have hF : ∀ F ∈ I, MvPolynomial.eval₂ (RingHom.id R) p F = 0 := by
    intro F hF
    apply IsNilpotent.eq_zero
    rw [nilpotent_iff_mem_prime]
    intro q hq
    by_contra hn
    obtain ⟨q', hq', hpr, hqq, hf⟩ := hvd q _ hq hn
    obtain ⟨K, _, x, y, hx, hy, hc⟩ := h q' hq'
    have h1 := (hP.2.1 K x y _ hy hc).2 F hF
    apply hf
    rw [← hx, RingHom.mem_ker, MvPolynomial.eval₂_comp_left, RingHom.comp_id]
    exact h1
  obtain ⟨y, ⟨hy, hc⟩, -⟩ := hP.2.2 R (RingHom.id R) p hu hF
  exact ⟨Over.homMk y (hy.trans (spMap_id R)), hc⟩

theorem pt_unique {R σ : Type} [CommRing R] {I : Ideal (MvPolynomial σ R)} {Z : Scheme.{0}} {s : Z ⟶ Sp R}
    {M : LB Z} {th : σ → M.Sec} (hP : ProjRep I s M th) {T : Type} [CommRing T] {β : R →+* T} {y y' : Sp T ⟶ Z}
    {w : σ → T} (hy : y ≫ s = spMap β) (hy' : y' ≫ s = spMap β) (hc : SecCoord M th y w) (hc' : SecCoord M th y' w) :
    y = y' := by
  obtain ⟨h1, h2⟩ := hP.2.1 T β y w hy hc
  exact (hP.2.2 T β w h1 h2).unique ⟨hy, hc⟩ ⟨hy', hc'⟩

theorem span_theta (l1 : Out.Laws) (l2 : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {K : Type} [Field K] {s : Sp K ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) (n : ℕ) (v : Ix g (N' ^ 2) → K)
    (h2 : 2 ≤ n) (hn : n ∣ N') (hth : t.HasTh (𝟙 _) v) : Ideal.span (Set.range v) = ⊤ := by
  obtain ⟨c, hc⟩ := GlobalTheory.T.thetaCosetNonvanishing_of_hasTh l1 l2 o g N' J b _ s t n K (𝟙 _) v ⊥ h2 hn hth Ideal.isPrime_bot 0
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, rfl⟩) (Ne.isUnit fun h => hc (Ideal.mem_bot.2 h))

theorem fibre_of_unit {R K σ : Type} [CommRing R] [CommRing K] {x : R →+* K} {Z : Scheme.{0}} {s : Z ⟶ Sp R} {M : LB Z}
    {th : σ → M.Sec} (A : Over (Sp K)) (L : LB A.left) (k : ℕ) (a : ℤ) (ha : a = k)
    (th' : σ → (Out.LPow A L a (Over.mk (𝟙 (Sp K)))).Sec) (φ₀ : (Over.mk (𝟙 (Sp K)) ⊗ A).left ⟶ Z)
    (h1 : IsPullback φ₀ (fst (Over.mk (𝟙 (Sp K))) A).left s (spMap x))
    (h2 : LBIso (Out.LPow A L a (Over.mk (𝟙 (Sp K)))) (M.pull φ₀))
    (h3 : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ A).left) (w : σ → T),
      SecCoord _ th' y w ↔ SecCoord M th (y ≫ φ₀) w) :
    ∃ φ : A.left ⟶ Z, IsPullback φ A.hom s (spMap x) ∧
      (∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ A).left) (w : σ → T),
        SecCoord _ th' y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) A).left ≫ φ) w) ∧
      LBIso (lbPow L k) (M.pull φ) ∧
      ∀ (z : Over.mk (𝟙 (Sp K)) ⟶ A) (w : σ → K), SecCoord _ th' (lift (𝟙 (Over.mk (𝟙 (Sp K)))) z).left w →
        SecCoord M th (z.left ≫ φ) w := by
  refine ⟨(unitInv A).left ≫ φ₀, ?_, fun T _ y w => ?_, ?_, fun z w hz => ?_⟩
  · have := (isPullback_unitInv A).paste_horiz h1
    rwa [Category.id_comp] at this
  · have e : (snd (Over.mk (𝟙 (Sp K))) A).left ≫ (unitInv A).left ≫ φ₀ = φ₀ := by
      rw [← Category.assoc, snd_unitInv, Category.id_comp]
    rw [e]
    exact h3 T y w
  · exact LBIso.chartPull (chartPullUnit A L k a ha) (chartPullSame M _ _ _ (unitInv A).left fun _ => rfl) h2
  · have e : z.left ≫ (unitInv A).left ≫ φ₀ = (lift (𝟙 (Over.mk (𝟙 (Sp K)))) z).left ≫ φ₀ := by
      rw [← Category.assoc, pt_unitInv]
    rw [e]
    exact (h3 K _ w).1 hz

theorem exists_scheme_sections_fibres : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R), VeryDense (objPrimes b Mat κ β v) → ∃ (Z : Over (Sp R)) (I : Ideal (MvPolynomial (Ix g ((n ^ j) ^ 2)) R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R), (ProjRep I Z.hom M th ∧ SmoothOfRelativeDimension g Z.hom ∧ GeometricallyConnected Z.hom ∧ (∀ h, SecCoord M th (sc h).left (p h))) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ φ : t'.A.left ⟶ Z.left, (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left)) := by
  intro l1 l2 g J _ Mat κ n hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.embeddedAbelianVariety_cutOut_by_torsionForms l1 l2 g J Mat κ n hn hodd
  refine ⟨max j₀ 4, fun j hj o _ b R _ _ _ β v hvd => ?_⟩
  have hj4 : 4 ≤ j := le_of_max_le_right hj
  have hdiv : (n ^ 2) ^ 2 ∣ n ^ j := by rw [← pow_mul]; exact pow_dvd_pow n hj4
  have hnd : n ∣ n ^ j := dvd_pow_self n (by omega)
  have h2 : 2 ≤ n ^ 2 := hn.two_le.trans (Nat.le_self_pow two_ne_zero n)
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero 2 (pow_ne_zero j hn.ne_zero)⟩
  obtain ⟨Hh, _, hh, Q, d, hcut⟩ := hj₀ j (le_of_max_le_left hj) o b
  obtain ⟨e, idx, hco⟩ := GlobalTheory.T.torsion_sectionCoords_theta_times_roots l1 l2 g (n ^ 2) (n ^ j) hodd.pow hdiv
  obtain ⟨p, hp⟩ : ∃ p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R,
      ∀ h a, p h a = β (b.ζ ^ e a h : oˣ) * v (idx a h) := ⟨_, fun _ _ => rfl⟩
  have hcut' : ∀ (K : Type) [Field K] [IsAlgClosed K] (β' : o →+* K) (s : Sp K ⟶ Sp o), s = spMap β' →
      ∀ (t : TObj g ((n ^ j) ^ 2) J b s) σ (p : Hh → Ix g ((n ^ j) ^ 2) → K), t.Emb (n ^ 2) (Over.mk (𝟙 _)) σ →
      (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab (hh h) ^ n ^ j)).left (p h)) →
      CutBy (idealOf (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _)) Q d p := by
    intro K _ _ β' s hs
    subst hs
    exact hcut K β'
  have fib : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)),
      t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧
      ProjRep (idealOf (fst (Over.mk (𝟙 (Sp K))) t'.A).left _ σ (𝟙 _)) (fst (Over.mk (𝟙 (Sp K))) t'.A).left _ σ ∧
      (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t'.lab h ^ n ^ j)).left (fun a => x (p h a))) ∧
      CutBy (idealOf (fst (Over.mk (𝟙 (Sp K))) t'.A).left _ σ (𝟙 _)) Q d (fun h i => x (p (hh h) i)) := by
    intro K _ _ x t' hth
    obtain ⟨σ, hE, hP⟩ := exists_emb l1 l2 t' (n ^ 2) _ hdiv h2 hth
    have hc : ∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t'.lab h ^ n ^ j)).left (fun a => x (p h a)) := by
      intro h
      obtain ⟨R', _, φ, hφ, hpt, hs⟩ := hco o J b (Sp K) _ t' K (x.comp β) (𝟙 _) (fun a => x (v a)) σ
        (by rw [Category.id_comp, spMap_comp]) hth (span_theta l1 l2 t' n _ hn.two_le hnd hth) hE h
        (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t'.lab h ^ n ^ j)).left
        (congrArg (fun z => (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (z ^ n ^ j)).left)
          ((Category.id_comp (t'.lab h)).symm.trans (congrArg (· ≫ t'.lab h) (to_base_ext _ _))))
        (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
      refine secCoord_of_local hP.1 φ hφ _ hpt ?_
      simp only [hp, map_mul x]
      exact hs
    exact ⟨σ, hE, hP, hc, hcut' K (x.comp β) _ (spMap_comp β x).symm t' σ _ hE fun h => hc (hh h)⟩
  obtain ⟨Z, M, th, hZ, hproj, hflat, -, hφ⟩ := GlobalTheory.T.exists_flat_projective_through_points_goodFibres R _ Hh (fun h => p (hh h)) Q d
    (fun K _ x I => (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) ∧ CutBy I Q d (fun h i => x (p (hh h) i)))
    (fun _ _ _ _ h => h) (by
      intro q f hq hf
      obtain ⟨q', ⟨K, _, _, x, t', hx, -, hth⟩, h⟩ := hvd q f hq hf
      obtain ⟨σ, -, hP, -, hc⟩ := fib K x t' hth
      exact ⟨q', ⟨K, inferInstance, x, _, hx, ideals_homogeneous.1 K _ _ _ _ _ σ _ hP.1, hc⟩, h⟩)
  have key : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)),
      t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ φ : t'.A.left ⟶ Z.left, IsPullback φ t'.A.hom Z.hom (spMap x) ∧
      (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T]
        (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T),
        SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧
      LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧
      ∀ h, ((t'.lab h ^ n ^ j).left ≫ φ) ≫ Z.hom = spMap x ∧
        SecCoord M th ((t'.lab h ^ n ^ j).left ≫ φ) (fun a => x (p h a)) := by
    intro K _ _ x t' hth
    obtain ⟨σ, hE, hP, hs, hc⟩ := fib K x t' hth
    obtain ⟨φ₀, a1, a2, a3⟩ := hφ K x _ _ _ _ σ ⟨ideals_homogeneous.1 K _ _ _ _ _ σ _ hP.1, hc⟩ hP
    obtain ⟨φ, b1, b2, b3, b4⟩ := fibre_of_unit t'.A t'.L ((n ^ 2) ^ 2) _ (Nat.cast_pow (n ^ 2) 2).symm σ φ₀ a1 a2 a3
    refine ⟨φ, b1, ⟨σ, hE, b2⟩, b3, fun h => ⟨?_, b4 _ _ (hs h)⟩⟩
    rw [Category.assoc, b1.w, ← Category.assoc, Over.w]
    exact Category.id_comp _
  have hsm := GlobalTheory.smooth_and_geomConnected_of_veryDense R Z.left Z.hom g _ hvd hproj hflat (by
    rintro q ⟨K, _, _, x, t', hx, -, hth⟩
    obtain ⟨φ, h1, -⟩ := key K x t' hth
    exact ⟨K, inferInstance, x, hx,
      @prop_pullback_snd _ (smoothOfRelativeDimension_isStableUnderBaseChange g) _ _ _ _ _ _ _ _ h1 t'.dim,
      prop_pullback_snd @GeometricallyConnected h1 t'.ab.geomConnected⟩)
  have hsc : ∀ h, ∃ sc : Out.baseOver (Sp R) ⟶ Z, SecCoord M th sc.left (p h) := fun h =>
    exists_section hZ (p h) hvd (by
      rintro q ⟨K, _, _, x, t', hx, -, hth⟩
      obtain ⟨φ, -, -, -, h4⟩ := key K x t' hth
      exact ⟨K, inferInstance, x, _, hx, h4 h⟩)
  choose sc hsc using hsc
  refine ⟨Z, _, M, th, sc, p, ⟨hZ, hsm.1, hsm.2, hsc⟩, fun K _ _ x t' _ hth => ?_⟩
  obtain ⟨φ, h1, h2, h3, h4⟩ := key K x t' hth
  refine ⟨φ, h1, h2, h3, fun h => pt_unique hZ (h4 h).1 ?_ (h4 h).2
    ((Coord.secCoord_bc_scale_unique _ M _ th R _ _ hZ.1 (hsc h)).1 K x)⟩
  rw [Category.assoc, Over.w]
  exact Category.comp_id _

end GlobalTheory.ZM.FamilyScheme
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_scheme_sections_good_fibres : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R), VeryDense (objPrimes b Mat κ β v) → ∃ (Z : Over (Sp R)) (I : Ideal (MvPolynomial (Ix g ((n ^ j) ^ 2)) R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R), (ProjRep I Z.hom M th ∧ SmoothOfRelativeDimension g Z.hom ∧ GeometricallyConnected Z.hom ∧ (∀ h, SecCoord M th (sc h).left (p h))) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ φ : t'.A.left ⟶ Z.left, (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left)) := by
  first | exact @GlobalTheory.ZM.FamilyScheme.exists_scheme_sections_fibres | exact GlobalTheory.ZM.FamilyScheme.exists_scheme_sections_fibres | (intros; apply GlobalTheory.ZM.FamilyScheme.exists_scheme_sections_fibres <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_family_addition_morphism_thetaLevel : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (I : Ideal (MvPolynomial (Ix g ((n ^ j) ^ 2)) R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R), VeryDense (objPrimes b Mat κ β v) → (ProjRep I Z.hom M th ∧ SmoothOfRelativeDimension g Z.hom ∧ GeometricallyConnected Z.hom ∧ (∀ h, SecCoord M th (sc h).left (p h))) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ φ : t'.A.left ⟶ Z.left, (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left)) → ∃ m : Z ⊗ Z ⟶ Z, (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ φ₂ : (t'.A ⊗ t'.A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[t'.A]).left ≫ φ) := by
  first | exact @GlobalTheory.ZM.BuildAdd.exists_add | exact GlobalTheory.ZM.BuildAdd.exists_add | (intros; apply GlobalTheory.ZM.BuildAdd.exists_add <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inversion_endomorphisms_thetaLevelFamily : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (I : Ideal (MvPolynomial (Ix g ((n ^ j) ^ 2)) R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R), VeryDense (objPrimes b Mat κ β v) → (ProjRep I Z.hom M th ∧ SmoothOfRelativeDimension g Z.hom ∧ GeometricallyConnected Z.hom ∧ (∀ h, SecCoord M th (sc h).left (p h))) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ φ : t'.A.left ⟶ Z.left, (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left)) → ∃ F : Option J → (Z ⟶ Z), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), t'.Shape Mat κ → (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ i : Option J, φ ≫ (F i).left = (i.elim (𝟙 t'.A)⁻¹ t'.act : t'.A ⟶ t'.A).left ≫ φ) := by
  first | exact @GlobalTheory.ZM.EndBuild.exists_endomorphisms | exact GlobalTheory.ZM.EndBuild.exists_endomorphisms | (intros; apply GlobalTheory.ZM.EndBuild.exists_endomorphisms <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.MulDescent

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem comp_eq_one_of_kTriv_pull {S S' : Scheme.{0}} {f : S' ⟶ S}
    {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}
    (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hK : KTriv A' L')
    {R : Type} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (x : Over.mk t ⟶ A)
    (hx : ∀ p : Spec (CommRingCat.of R), ∃ V : (Spec (CommRingCat.of R)).Opens, p ∈ V ∧
      ∃ c : LB.Gen ((translDiff A L x).pull ((fst (Over.mk t) A).left ⁻¹ᵁ V).ι), c.IsGen)
    {R' : CommRingCat.{0}} (g : Spec R' ⟶ Spec (CommRingCat.of R)) (t' : Spec R' ⟶ S') (sq : g ≫ t = t' ≫ f) :
    g ≫ x.left = g ≫ (1 : Over.mk t ⟶ A).left := by
  obtain ⟨w, hw⟩ := hw
  let T : Over S := Over.mk t
  let T' : Over S' := Over.mk t'
  have hxw : (g ≫ x.left) ≫ A.hom = t' ≫ f := by rw [Category.assoc, Over.w x]; exact sq
  let x' : T' ⟶ A' := Over.homMk (h.1.lift _ _ hxw) (h.1.lift_snd _ _ _)
  have hx' : x'.left ≫ φ = g ≫ x.left := h.1.lift_fst _ _ _
  have key : x' = toUnit _ ≫ η[A'] := hK R' t' x' fun p => by
    obtain ⟨V, hV, c, hc⟩ := hx (g p)
    refine ⟨g ⁻¹ᵁ V, hV, ?_⟩
    let a : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ T := Over.homMk ((fst T' A').left ≫ g)
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) sq).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ f) (Over.w (fst T' A'))))))
    let b : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ A := pushPt h.1.w (snd T' A')
    have k₁ : (lift a b).left ≫ (fst T A).left = (fst T' A').left ≫ g := congrArg (fun q => q.left) (lift_fst a b)
    have k₂ : (lift a b).left ≫ (snd T A).left = (snd T' A').left ≫ φ := congrArg (fun q => q.left) (lift_snd a b)
    have k₃ : (lift a b).left ≫ ((fst T A ≫ x) * snd T A).left = ((fst T' A' ≫ x') * snd T' A').left ≫ φ := by
      have e : lift a b ≫ ((fst T A ≫ x) * snd T A) = (a ≫ x) * b := by
        rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
      refine (congrArg (fun q => q.left) e).trans (h.2 (T' ⊗ A') _ _ _ _ ?_ rfl)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hx'.symm).trans (Category.assoc _ _ _).symm)
    have le : (fst T' A').left ⁻¹ᵁ g ⁻¹ᵁ V ≤ (lift a b).left ⁻¹ᵁ (fst T A).left ⁻¹ᵁ V := fun y hy =>
      (congrArg (fun q => q y ∈ V) k₁).mpr hy
    have hn := Scheme.Hom.resLE_comp_ι (lift a b).left le
    obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn L _ _ _) c hc
    obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame L (fun k : Fin 2 => (((fst T' A').left ⁻¹ᵁ g ⁻¹ᵁ V).ι ≫
      ![(lift (fst T' A' ≫ x') (snd T' A') ≫ μ[A']).left, (snd T' A').left] k) ≫ φ) _ _
      ((lift a b).left.resLE _ _ le) fun k => by
        rw [← Category.assoc, hn, Category.assoc, Category.assoc]
        fin_cases k
        exacts [congrArg (_ ≫ ·) k₃.symm, congrArg (_ ≫ ·) k₂.symm]) c₁ h₁
    obtain ⟨c₃, h₃⟩ := exists_down ((isGen_iff w).1 hw) hL hL' c₂ h₂
    exact gen_chartPull (chartPullOut L' _ _ _ _ fun _ => rfl) c₃ h₃
  let U : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk g sq
  have e₁ : U ≫ x = pushHom h T' x' := Over.OverMorphism.ext hx'.symm
  have e₂ : U ≫ x = U ≫ (1 : T ⟶ A) := by
    rw [e₁, MonObj.comp_one]
    exact (congrArg (pushHom h T') key).trans (map_one (pushHom h T'))
  exact congrArg (fun q => q.left) e₂

theorem kTriv_of_locally {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    (H : ∀ s : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S), IsOpenImmersion f ∧ IsAffineHom f ∧ s ∈ Set.range f ∧
      KTriv ((Over.pullback f).obj A) (L.pull (pullback.fst A.hom f))) : KTriv A L := by
  intro R _ t x hx
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall x.left (1 : Over.mk t ⟶ A).left fun p => ?_)
  obtain ⟨S', f, h₁, h₂, ⟨s, hs⟩, hK⟩ := H (t p)
  have : IsAffine (pullback t f) := isAffine_of_isAffineHom (pullback.fst t f)
  let g := (pullback t f).isoSpec.inv ≫ pullback.fst t f
  have e := comp_eq_one_of_kTriv_pull (isGrpPullback_pullback A f) hL (pull_isLB hL _)
    (PolBaseChange.lbIso_refl (pull_isLB hL _)) hK t x hx g ((pullback t f).isoSpec.inv ≫ pullback.snd t f)
    (by rw [Category.assoc, Category.assoc, pullback.condition])
  have e' : pullback.fst t f ≫ x.left = pullback.fst t f ≫ (1 : Over.mk t ⟶ A).left := by
    rw [← cancel_epi (pullback t f).isoSpec.inv, ← Category.assoc, ← Category.assoc]
    exact e
  refine ⟨(pullback.fst t f).opensRange, ?_, ?_⟩
  · show p ∈ Set.range (pullback.fst t f)
    rw [Scheme.Pullback.range_fst]
    exact ⟨s, hs⟩
  · rw [← cancel_epi (pullback.fst t f).isoOpensRange.hom, ← Category.assoc, ← Category.assoc]
    erw [Scheme.Hom.isoOpensRange_hom_ι]
    exact e'

theorem kTriv_of_lbIso {S : Scheme.{0}} {A : Over S} [GrpObj A] {L L' : LB A.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (h : LBIso L L') (hK : KTriv A L) : KTriv A L' := by
  obtain ⟨w, hw⟩ : LBIso L' (L.pull (Iso.refl A).hom.left) :=
    h.symm.chartPull (Geo.Tor.chartPullId L') (Geo.Tor.chartPullPull L (𝟙 _) (𝟙 _) rfl)
  have : IsMonHom (Iso.refl A).hom := inferInstanceAs (IsMonHom (𝟙 A))
  exact kTriv_pull (isGrpPullback_of_iso (Iso.refl A)) hL hL' ((isGen_iff w).1 hw) hK

end GlobalTheory.MulDescent

namespace GlobalTheory.MulDescent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem exists_polarisation_of_veryDense : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (g m : ℕ) (M : LB A.left) (P : Set (Ideal R)) (pt : Fin (2 * g) → (𝟙_ (Over (Sp R)) ⟶ A)), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Odd m → IsUnit (m : R) → M.IsLB → Out.RelAmple A M → (∀ (q₀ : Ideal R) (f₀ : R), q₀.IsPrime → f₀ ∉ q₀ → ∃ p₀ ∈ P, p₀.IsPrime ∧ q₀ ≤ p₀ ∧ f₀ ∉ p₀) → (∀ i, pt i ^ m = 1) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ A), y ^ m = 1 → ∃! c : Fin (2 * g) → ZMod m, Out.linComb (fun i => toUnit (Over.mk x) ≫ pt i) (fun i => (c i).val) = y) → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left), RingHom.ker x = q ∧ IsGrpPullback Pl.A A (spMap x) φ ∧ LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ)) → ∃ L : LB A.left, L.IsLB ∧ Out.Rigidified A L ∧ Out.Sym A L ∧ Out.RelAmple A L ∧ Out.KTriv A L ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left), IsGrpPullback Pl.A A (spMap x) φ → LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ) → LBIso Pl.L (L.pull φ) := by
  intro h₁ h₂ R _ _ _ A _ g m M P pt hA hg hm hu hM hamp hP hpt hbas hfib
  obtain ⟨L, hL, hrig, hsym, hLa, hiso⟩ := GlobalTheory.OddDescent.exists_descended h₁ h₂ R A g m M pt hA hg hm hu hM hamp hpt hbas (by
    intro f hf
    refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.2 fun q hq => ?_)
    by_contra hn
    obtain ⟨p, hp, hp', -, hfp⟩ := hP q f hq hn
    exact hfp (hf p (hfib p hp) hp'))
  refine ⟨L, hL, hrig, hsym, hLa, kTriv_of_locally hL fun s => ?_, hiso⟩
  have hs : (s : PrimeSpectrum R).asIdeal.IsPrime := (s : PrimeSpectrum R).isPrime
  obtain ⟨p, hp, -, hle, -⟩ := hP (s : PrimeSpectrum R).asIdeal 1 hs
    (fun h => hs.ne_top ((Ideal.eq_top_iff_one _).2 h))
  obtain ⟨K, _, _, x, Pl, φ, hker, hφ, hw⟩ := hfib p hp
  obtain ⟨f, hf, H⟩ := GlobalTheory.KTrivSpread.exists_kTriv_of_isUnit R A L K x Pl.A φ hA hL hLa hφ
    (kTriv_of_lbIso Pl.isLB (pull_isLB hL _) (hiso K x Pl φ hφ hw) Pl.ktriv)
  have hfs : f ∉ (s : PrimeSpectrum R).asIdeal := fun h => hf (by
    have := hle h
    rwa [← hker, RingHom.mem_ker] at this)
  have ho : IsOpenImmersion (spMap (algebraMap R (Localization.Away f))) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))))
  refine ⟨_, spMap (algebraMap R (Localization.Away f)), ho, inferInstance, ?_,
    H (Localization.Away f) (algebraMap R _) _ _ (IsLocalization.Away.algebraMap_isUnit f)
      (isGrpPullback_pullback A _)⟩
  have : s ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
    exact hfs
  exact this

end GlobalTheory.MulDescent
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarisation_descent_mul_odd_veryDense : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (g m : ℕ) (M : LB A.left) (P : Set (Ideal R)) (pt : Fin (2 * g) → (𝟙_ (Over (Sp R)) ⟶ A)), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Odd m → IsUnit (m : R) → M.IsLB → Out.RelAmple A M → (∀ (q₀ : Ideal R) (f₀ : R), q₀.IsPrime → f₀ ∉ q₀ → ∃ p₀ ∈ P, p₀.IsPrime ∧ q₀ ≤ p₀ ∧ f₀ ∉ p₀) → (∀ i, pt i ^ m = 1) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ A), y ^ m = 1 → ∃! c : Fin (2 * g) → ZMod m, Out.linComb (fun i => toUnit (Over.mk x) ≫ pt i) (fun i => (c i).val) = y) → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left), RingHom.ker x = q ∧ IsGrpPullback Pl.A A (spMap x) φ ∧ LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ)) → ∃ L : LB A.left, L.IsLB ∧ Out.Rigidified A L ∧ Out.Sym A L ∧ Out.RelAmple A L ∧ Out.KTriv A L ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left), IsGrpPullback Pl.A A (spMap x) φ → LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ) → LBIso Pl.L (L.pull φ) := by
  first | exact @GlobalTheory.MulDescent.exists_polarisation_of_veryDense | exact GlobalTheory.MulDescent.exists_polarisation_of_veryDense | (intros; apply GlobalTheory.MulDescent.exists_polarisation_of_veryDense <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.DensePol

theorem dense_of_veryDense {R : Type} [CommRing R] {P : Set (Ideal R)} (h : VeryDense P) :
    Dense {p : Sp R | PrimeSpectrum.asIdeal (R := R) p ∈ P} := by
  refine (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).dense_iff.2 ?_
  rintro _ ⟨f, rfl⟩ ⟨q, hq⟩
  obtain ⟨p, hp, hp', -, hf⟩ := h q.asIdeal f q.isPrime hq
  exact ⟨⟨p, hp'⟩, hf, hp⟩

theorem mem_range_spMap {R K : Type} [CommRing R] [Field K] (x : R →+* K) (p : Sp R)
    (h : RingHom.ker x = PrimeSpectrum.asIdeal (R := R) p) : p ∈ Set.range (spMap x) := by
  refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), ?_⟩
  apply PrimeSpectrum.ext
  rw [← h]
  rfl

theorem basis_pow {G : Type} [CommGroup G] {r k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0) (y : Fin r → G)
    (hy : ∀ i, y i ^ (k * l) = 1)
    (h : ∀ z : G, z ^ (k * l) = 1 → ∃! c : Fin r → ZMod (k * l), ∏ i, y i ^ (c i).val = z)
    (z : G) (hz : z ^ k = 1) : ∃! c : Fin r → ZMod k, ∏ i, (y i ^ l) ^ (c i).val = z := by
  haveI : NeZero k := ⟨hk⟩
  have red : ∀ e : Fin r → ℕ, ∏ i, y i ^ ((e i : ZMod (k * l))).val = ∏ i, y i ^ e i := fun e =>
    Finset.prod_congr rfl fun i _ => by rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (hy i)]
  have tor : ∀ e : Fin r → ℕ, (∏ i, y i ^ e i) ^ (k * l) = 1 := fun e => by
    rw [← Finset.prod_pow]
    exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]
  have inj : ∀ e e' : Fin r → ℕ, ∏ i, y i ^ e i = ∏ i, y i ^ e' i → ∀ i, e i ≡ e' i [MOD k * l] := by
    intro e e' he i
    have := (h _ (tor e)).unique (y₁ := fun i => (e i : ZMod (k * l))) (y₂ := fun i => (e' i : ZMod (k * l)))
      (red e) ((red e').trans he.symm)
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 (congrFun this i)
  obtain ⟨c, hc, -⟩ := h z (by rw [pow_mul, hz, one_pow])
  have hd : ∀ i, l ∣ (c i).val := fun i => by
    have := inj (fun i => k * (c i).val) (fun _ => 0) (by
      simp only [pow_zero, Finset.prod_const_one]
      rw [← hz, ← hc, ← Finset.prod_pow]
      exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul, mul_comm]) i
    exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hk) ((Nat.modEq_zero_iff_dvd).1 this)
  choose d hd using hd
  refine ⟨fun i => (d i : ZMod k), ?_, fun c' hc' => funext fun i => ?_⟩
  · rw [← hc]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (by rw [← pow_mul, mul_comm, hy]), hd, pow_mul]
  · have := inj (fun i => l * (c' i).val) (fun i => l * d i) (by
      simp only [pow_mul, ← hd]
      rw [hc, ← hc']) i
    rw [mul_comm k l] at this
    have h2 := Nat.ModEq.mul_left_cancel' hl this
    rw [← (ZMod.natCast_eq_natCast_iff _ _ _).2 h2, ZMod.natCast_zmod_val]

variable {S S' : Scheme.{0}}

theorem basis_pow_linComb {A T : Over S} [GrpObj A] [IsCommMonObj A] {r k l N : ℕ} (hN : N = k * l) (hN0 : N ≠ 0)
    (u : T ⟶ Out.baseOver S) (y : Fin r → (Out.baseOver S ⟶ A)) (hy : ∀ i, y i ^ N = 1)
    (h : ∀ z : T ⟶ A, z ^ N = 1 → ∃! c : Fin r → ZMod N, Out.linComb (fun i => u ≫ y i) (fun i => (c i).val) = z)
    (z : T ⟶ A) (hz : z ^ k = 1) :
    ∃! c : Fin r → ZMod k, Out.linComb (fun i => u ≫ y i ^ l) (fun i => (c i).val) = z := by
  subst hN
  simp only [Out.linComb, List.prod_ofFn, MonObj.comp_pow] at h ⊢
  exact basis_pow (left_ne_zero_of_mul hN0) (right_ne_zero_of_mul hN0) _
    (fun i => by rw [← MonObj.comp_pow, hy, MonObj.comp_one]) h z hz

variable {A : Over S'} {Z : Over S} {x : S' ⟶ S} {φ : A.left ⟶ Z.left}

theorem comp_eq_pushPt (w : φ ≫ Z.hom = A.hom ≫ x) {a : Out.baseOver S' ⟶ A} {s : Out.baseOver S ⟶ Z}
    (h : a.left ≫ φ = x ≫ s.left) {T : Over S'} (u : T ⟶ Out.baseOver S')
    (t : Over.mk (T.hom ≫ x) ⟶ Out.baseOver S) : t ≫ s = pushPt w (u ≫ a) := by
  apply Over.OverMorphism.ext
  have h1 : t.left = T.hom ≫ x := by simpa using Over.w t
  have h2 : u.left = T.hom := by simpa using Over.w u
  change t.left ≫ s.left = (u.left ≫ a.left) ≫ φ
  rw [h1, h2, Category.assoc, Category.assoc, h]

theorem basis_push [GrpObj A] [GrpObj Z] (hφ : IsGrpPullback A Z x φ) {r k : ℕ}
    {a : Fin r → (Out.baseOver S' ⟶ A)} {s : Fin r → (Out.baseOver S ⟶ Z)}
    (h : ∀ i, (a i).left ≫ φ = x ≫ (s i).left) {T : Over S'} (u : T ⟶ Out.baseOver S')
    (t : Over.mk (T.hom ≫ x) ⟶ Out.baseOver S)
    (hb : ∀ z : T ⟶ A, z ^ k = 1 → ∃! c : Fin r → ZMod k, Out.linComb (fun i => u ≫ a i) (fun i => (c i).val) = z)
    (z : Over.mk (T.hom ≫ x) ⟶ Z) (hz : z ^ k = 1) :
    ∃! c : Fin r → ZMod k, Out.linComb (fun i => t ≫ s i) (fun i => (c i).val) = z := by
  have inj : Function.Injective (pushHom hφ T) := fun y y' e =>
    Over.OverMorphism.ext (hφ.1.hom_ext (congrArg (fun z => z.left) e) ((Over.w y).trans (Over.w y').symm))
  obtain ⟨z, rfl⟩ := GrpDense.pushPt_surjective hφ.1 T z
  change pushHom hφ T z ^ k = 1 at hz
  rw [← map_pow, map_eq_one_iff _ inj] at hz
  have key : ∀ e : Fin r → ℕ, Out.linComb (fun i => t ≫ s i) e =
      pushHom hφ T (Out.linComb (fun i => u ≫ a i) e) := fun e => by
    simp only [Out.linComb, map_list_prod, List.map_ofFn]
    congr 2
    funext i
    simp only [Function.comp, map_pow]
    rw [comp_eq_pushPt hφ.1.w (h i) u t]
    rfl
  simp only [key]
  change ∃! c : Fin r → ZMod k, _ = pushHom hφ T z
  simp only [inj.eq_iff]
  exact hb z hz

theorem lab_single {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
    (t : TObj g k J b s) (i : Fin (2 * g)) : t.lab (Pi.single i 1) = t.pt i := by
  have := t.ab.comm
  rw [TObj.lab, Out.linComb, List.prod_ofFn, Finset.prod_eq_single i]
  · rw [Pi.single_eq_same, ← Nat.cast_one, ZMod.val_natCast, ← pow_eq_pow_mod _ (t.torsion i), pow_one]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, ZMod.val_zero, pow_zero]
  · simp

theorem lab_zero {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
    (t : TObj g k J b s) : t.lab 0 = 1 := by
  have := t.ab.comm
  rw [TObj.lab, Out.linComb, List.prod_ofFn]
  simp

theorem one_left {A : Over S} [GrpObj A] : (1 : Out.baseOver S ⟶ A).left = (η[A]).left :=
  Category.id_comp _

end GlobalTheory.DensePol

namespace GlobalTheory

open DensePol

theorem exists_polAV_of_veryDense_fibres :
    Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (I : Ideal (MvPolynomial (Ix g ((n ^ j) ^ 2)) R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R) (m : Z ⊗ Z ⟶ Z) (F : Option J → (Z ⟶ Z)), VeryDense (objPrimes b Mat κ β v) → (ProjRep I Z.hom M th ∧ SmoothOfRelativeDimension g Z.hom ∧ GeometricallyConnected Z.hom ∧ (∀ h, SecCoord M th (sc h).left (p h))) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ φ : t'.A.left ⟶ Z.left, (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ φ₂ : (t'.A ⊗ t'.A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[t'.A]).left ≫ φ) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), t'.Shape Mat κ → (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ i : Option J, φ ≫ (F i).left = (i.elim (𝟙 t'.A)⁻¹ t'.act : t'.A ⟶ t'.A).left ≫ φ) → ∃ (P : Out.PolAV (Sp R)) (act : J → (P.A ⟶ P.A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ P.A)), (P.g = g ∧ (∀ i, IsMonHom (act i)) ∧ (∀ i, Q i ^ (n ^ j) = 1) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ P.A), y ^ (n ^ j) = 1 → ∃! c : Ix g (n ^ j), Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp R)) ≫ Q i) (fun i => (c i).val) = y)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ ψ : t'.A.left ⟶ P.A.left, (IsGrpPullback t'.A P.A (spMap x) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ (n ^ j)).left ≫ ψ = (spMap x) ≫ (Q i).left) := by
  intro hL hL2 g J _ Mat κ n hn hodd
  refine ⟨2, fun j hj o _ b R _ _ _ β v Z I M th sc p m F hVD ⟨hrep, hsm, hgc, _⟩ hfib hm hF => ?_⟩
  have hn0 : n ≠ 0 := hn.ne_zero
  have hN0 : n ^ j ≠ 0 := pow_ne_zero _ hn0
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ hN0⟩
  have hun : IsUnit (n : R) := by
    have := b.unit.map β
    rw [map_natCast, Nat.cast_pow, Nat.cast_pow, isUnit_pow_iff two_ne_zero, isUnit_pow_iff (by omega)] at this
    exact this
  obtain ⟨-, hpr, hamp⟩ := GlobalTheory.ZM.projRep_projective_ample R _ I Z M th hrep
  have hD := dense_of_veryDense hVD
  have hs : Smooth Z.hom := SmoothOfRelativeDimension.smooth g _
  have s1 : Smooth (Out.baseOver (Sp R)).hom := inferInstanceAs (Smooth (𝟙 _))
  have h0 : ∀ {K : Type} [Field K] {x : R →+* K} (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β))
      {φ : t'.A.left ⟶ Z.left}, (∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) →
      (1 : Out.baseOver _ ⟶ t'.A).left ≫ φ = spMap x ≫ (sc 0).left := fun t' φ h => by
    have := h 0
    rwa [lab_zero, one_pow] at this
  have h1 : ∀ {K : Type} [Field K] {x : R →+* K} (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β))
      {φ : t'.A.left ⟶ Z.left}, (∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) →
      ∀ i, (t'.pt i ^ n ^ j).left ≫ φ = spMap x ≫ (sc (Pi.single i 1)).left := fun t' φ h i => by
    have := h (Pi.single i 1)
    rwa [lab_single] at this
  obtain ⟨_, -, hη, -, hab, hgp⟩ := grpObj_of_dense_fibres R Z m (F none) (sc 0) _ hD hs hpr hgc (by
    rintro q ⟨K, _, _, x, t', hx, hsh, hth⟩
    obtain ⟨φ, hφ⟩ := hfib K x t' hsh hth
    refine ⟨K, inferInstance, spMap x, t'.A, inferInstance, φ, mem_range_spMap x q hx, t'.ab.comm, hφ.1,
      hm K x t' φ hφ, ?_, ?_⟩
    · have := hF K x t' φ hsh hφ none
      rwa [Option.elim, Hom.inv_def, Category.id_comp] at this
    · rw [← one_left, h0 t' hφ.2.2.2])
  have := hab.comm
  have hhom : ∀ i, IsMonHom (F (some i)) := fun i => hL.rigidity _ Z Z hab hab _ (by
    rw [hη]
    refine FibreGrp.hom_ext_of_fibres (X := Out.baseOver (Sp R)) hD ?_
    rintro q ⟨K, _, _, x, t', hx, hsh, hth⟩
    obtain ⟨φ, hφ⟩ := hfib K x t' hsh hth
    refine ⟨_, spMap x, mem_range_spMap x q hx, fun T t => ?_⟩
    rw [← Category.assoc, comp_eq_pushPt hφ.1.w (h0 t' hφ.2.2.2) (toUnit T) t]
    have := t'.hom i
    have e : (toUnit T ≫ (1 : Out.baseOver _ ⟶ t'.A)) ≫ t'.act i = toUnit T ≫ (1 : Out.baseOver _ ⟶ t'.A) := by
      rw [Category.assoc, MonObj.one_comp]
    apply Over.OverMorphism.ext
    change (_ ≫ φ) ≫ (F (some i)).left = _ ≫ φ
    rw [Category.assoc, hF K x t' φ hsh hφ (some i), ← Category.assoc, ← Over.comp_left]
    exact congrArg (fun z => z.left ≫ φ) e)
  have htor : ∀ {K : Type} [Field K] {x : R →+* K} (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (i),
      (t'.pt i ^ n ^ j) ^ n ^ j = 1 := fun t' i => by
    have e : n ^ j * n ^ j = (n ^ j) ^ 2 := (pow_two _).symm
    rw [← pow_mul (t'.pt i), e, t'.torsion]
  have hQ : ∀ i, sc (Pi.single i 1) ^ n ^ j = 1 := fun i => by
    refine FibreGrp.hom_ext_of_fibres (X := Out.baseOver (Sp R)) hD ?_
    rintro q ⟨K, _, _, x, t', hx, hsh, hth⟩
    obtain ⟨φ, hφ⟩ := hfib K x t' hsh hth
    refine ⟨_, spMap x, mem_range_spMap x q hx, fun T t => ?_⟩
    rw [MonObj.comp_pow, MonObj.comp_one, comp_eq_pushPt hφ.1.w (h1 t' hφ.2.2.2 i) (toUnit T) t]
    change pushHom (hgp _ _ _ φ hφ.1 (hm K x t' φ hφ)) T _ ^ _ = 1
    rw [← map_pow]
    erw [← MonObj.comp_pow]
    rw [htor]
    erw [MonObj.comp_one]
    rw [map_one]
  have hB := torsion_basis_of_dense (Sp R) Z (n ^ j) (2 * g) (fun i => sc (Pi.single i 1)) _ hab
    (Nat.pos_of_ne_zero hN0) (by
      have := (hun.pow j).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      simpa using this) hQ hD (by
      rintro q ⟨K, _, _, x, t', hx, hsh, hth⟩
      obtain ⟨φ, hφ⟩ := hfib K x t' hsh hth
      have := t'.ab.comm
      refine ⟨K, inferInstance, inferInstance, 𝟙 _ ≫ spMap x, by simpa using mem_range_spMap x q hx, ?_⟩
      exact basis_push (hgp _ _ _ φ hφ.1 (hm K x t' φ hφ)) (h1 t' hφ.2.2.2) (T := Over.mk (𝟙 _)) _ _
        (basis_pow_linComb (pow_two _) (NeZero.ne _) _ t'.pt t'.torsion (t'.bij K (𝟙 _))))
  have hj2 : n ^ j = n ^ 2 * n ^ (j - 2) := by rw [← pow_add]; congr 1; omega
  obtain ⟨L, l1, l2, l3, l4, l5, l6⟩ := GlobalTheory.T.exists_polarisation_descent_mul_odd_veryDense hL hL2 R Z g (n ^ 2) M _
    (fun i => (sc (Pi.single i 1) ^ n ^ (j - 2) : Out.baseOver (Sp R) ⟶ Z)) hab hsm hodd.pow
    (by simpa using hun.pow 2) hrep.1 hamp hVD
    (fun i => by
      have e : n ^ (j - 2) * n ^ 2 = n ^ j := by rw [mul_comm, ← hj2]
      have : (sc (Pi.single i 1) ^ n ^ (j - 2)) ^ n ^ 2 = 1 := by rw [← pow_mul, e, hQ]
      exact this)
    (fun K _ _ x => basis_pow_linComb hj2 hN0 _ _ hQ (hB K x))
    (by
      rintro q ⟨K, _, _, x, t', hx, hsh, hth⟩
      obtain ⟨φ, hφ⟩ := hfib K x t' hsh hth
      exact ⟨K, inferInstance, inferInstance, x, t'.pol, φ, hx, hgp _ _ _ φ hφ.1 (hm K x t' φ hφ), hφ.2.2.1⟩)
  refine ⟨{ A := Z, isAb := hab, g := g, smoothDim := hsm, L := L, isLB := l1, rigid := l2, sym := l3,
            ample := l4, ktriv := l5 }, fun i => F (some i), fun i => sc (Pi.single i 1),
    ⟨rfl, hhom, hQ, hB⟩, fun K _ _ x t' hsh hth => ?_⟩
  obtain ⟨φ, hφ⟩ := hfib K x t' hsh hth
  have hg := hgp _ _ _ φ hφ.1 (hm K x t' φ hφ)
  exact ⟨φ, hg, l6 K x t'.pol φ hg hφ.2.2.1, fun i => (hF K x t' φ hsh hφ (some i)).symm, h1 t' hφ.2.2.2⟩

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principallyPolarised_of_veryDense_fibres : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (I : Ideal (MvPolynomial (Ix g ((n ^ j) ^ 2)) R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R) (m : Z ⊗ Z ⟶ Z) (F : Option J → (Z ⟶ Z)), VeryDense (objPrimes b Mat κ β v) → (ProjRep I Z.hom M th ∧ SmoothOfRelativeDimension g Z.hom ∧ GeometricallyConnected Z.hom ∧ (∀ h, SecCoord M th (sc h).left (p h))) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ φ : t'.A.left ⟶ Z.left, (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ φ₂ : (t'.A ⊗ t'.A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[t'.A]).left ≫ φ) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), t'.Shape Mat κ → (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ i : Option J, φ ≫ (F i).left = (i.elim (𝟙 t'.A)⁻¹ t'.act : t'.A ⟶ t'.A).left ≫ φ) → ∃ (P : Out.PolAV (Sp R)) (act : J → (P.A ⟶ P.A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ P.A)), (P.g = g ∧ (∀ i, IsMonHom (act i)) ∧ (∀ i, Q i ^ (n ^ j) = 1) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ P.A), y ^ (n ^ j) = 1 → ∃! c : Ix g (n ^ j), Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp R)) ≫ Q i) (fun i => (c i).val) = y)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ ψ : t'.A.left ⟶ P.A.left, (IsGrpPullback t'.A P.A (spMap x) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ (n ^ j)).left ≫ ψ = (spMap x) ≫ (Q i).left) := by
  atlas_forward_decl GlobalTheory.exists_polAV_of_veryDense_fibres
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.LevelTheta

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_id {A : Type} [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := Spec.map_id _

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {ψ : Y ⟶ X} (φ : Z ⟶ Y) {χ : Z ⟶ X}
    (H : LBIso M (L.pull ψ)) (e : χ = φ ≫ ψ) : LBIso (M.pull φ) (L.pull χ) :=
  H.chartPull (chartPullPull M φ φ rfl)
    (chartPullSame L (fun _ : PUnit => χ) (fun _ : PUnit => ψ) (fun _ => 1) φ (fun _ => e))

theorem pow_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (x' : Out.baseOver S' ⟶ G') (x : Out.baseOver S ⟶ G)
    (e : x'.left ≫ φ = f ≫ x.left) (m : ℕ) : (x' ^ m).left ≫ φ = f ≫ (x ^ m).left := by
  let U : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S := Over.homMk f (by simp)
  have e₁ : pushHom h _ x' = preHom U x := Over.OverMorphism.ext e
  have e₂ : pushHom h _ (x' ^ m) = preHom U (x ^ m) := by rw [map_pow, map_pow, e₁]
  exact congrArg (fun z => z.left) e₂

variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k}

def Above {S S' : Scheme.{0}} (P : Out.PolAV S) (act : J → (P.A ⟶ P.A)) (Q : Fin (2 * g) → (Out.baseOver S ⟶ P.A))
    (m : ℕ) {s' : S' ⟶ Sp o} (t : TObj g k J b s') (f : S' ⟶ S) (ψ : t.A.left ⟶ P.A.left) : Prop :=
  IsGrpPullback t.A P.A f ψ ∧ LBIso t.L (P.L.pull ψ) ∧ (∀ i, (t.act i).left ≫ ψ = ψ ≫ (act i).left) ∧
    ∀ i, (t.pt i ^ m).left ≫ ψ = f ≫ (Q i).left

theorem Above.comp {S S' S'' : Scheme.{0}} {P : Out.PolAV S} {act : J → (P.A ⟶ P.A)}
    {Q : Fin (2 * g) → (Out.baseOver S ⟶ P.A)} {m : ℕ} {s' : S' ⟶ Sp o} {s'' : S'' ⟶ Sp o} {t : TObj g k J b s'}
    {u : TObj g k J b s''} {f : S' ⟶ S} {ψ : t.A.left ⟶ P.A.left} (h : Above P act Q m t f ψ) {f' : S'' ⟶ S'}
    {φ : u.A.left ⟶ t.A.left} (h₁ : IsGrpPullback u.A t.A f' φ) (h₂ : LBIso u.L (t.L.pull φ))
    (h₃ : ∀ i, (u.pt i).left ≫ φ = f' ≫ (t.pt i).left) (h₄ : ∀ j, (u.act j).left ≫ φ = φ ≫ (t.act j).left) :
    Above P act Q m u (f' ≫ f) (φ ≫ ψ) := by
  refine ⟨h₁.comp h.1, LBIso.trans u.isLB (pull_isLB t.isLB _) (pull_isLB P.isLB _) h₂
    (lbIso_pull_comp φ h.2.1 rfl), fun i => ?_, fun i => ?_⟩
  · rw [← Category.assoc, h₄, Category.assoc, h.2.2.1, Category.assoc]
  · rw [← Category.assoc, pow_push h₁ _ _ (h₃ i), Category.assoc, h.2.2.2, Category.assoc]

theorem Above.compare {S S' : Scheme.{0}} {P : Out.PolAV S} {act : J → (P.A ⟶ P.A)}
    {Q : Fin (2 * g) → (Out.baseOver S ⟶ P.A)} {m : ℕ} {s' : S' ⟶ Sp o} {u u' : TObj g k J b s'}
    {f : S' ⟶ S} {ψ : u.A.left ⟶ P.A.left} {ψ' : u'.A.left ⟶ P.A.left} (h : Above P act Q m u f ψ)
    (h' : Above P act Q m u' f ψ') :
    ∃ χ : u'.A.left ⟶ u.A.left, χ ≫ ψ = ψ' ∧ IsGrpPullback u'.A u.A (𝟙 _) χ ∧ LBIso u'.L (u.L.pull χ) ∧
      (∀ i, (u'.pt i ^ m).left ≫ χ = (u.pt i ^ m).left) ∧ ∀ j, (u'.act j).left ≫ χ = χ ≫ (u.act j).left := by
  have hp := h.1.1
  let χ : u'.A.left ⟶ u.A.left := hp.lift ψ' u'.A.hom h'.1.1.w
  have e₁ : χ ≫ ψ = ψ' := hp.lift_fst _ _ _
  have e₂ : χ ≫ u.A.hom = u'.A.hom := hp.lift_snd _ _ _
  refine ⟨χ, e₁, h.1.cancel (h'.1.congr (Category.id_comp _).symm e₁.symm) (by rw [e₂, Category.comp_id]),
    LBIso.trans u'.isLB (pull_isLB P.isLB _) (pull_isLB u.isLB _) h'.2.1
      (lbIso_pull_comp χ h.2.1 e₁.symm).symm, fun i => ?_, fun j => ?_⟩
  · apply hp.hom_ext
    · rw [Category.assoc, e₁, h'.2.2.2, h.2.2.2]
    · rw [Category.assoc, e₂, Over.w, Over.w]
  · apply hp.hom_ext
    · rw [Category.assoc, e₁, h'.2.2.1, Category.assoc, h.2.2.1, ← Category.assoc, e₁]
    · rw [Category.assoc, e₂, Over.w, Category.assoc, Over.w, e₂]

theorem exists_level_with_theta_point : Out.Laws → Out.Laws2 → ∀ (g n j : ℕ) (J : Type), n.Prime → Odd n → 2 ≤ j → ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (P : Out.PolAV (Sp R)) (act : J → (P.A ⟶ P.A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ P.A)), (P.g = g ∧ (∀ i, IsMonHom (act i)) ∧ (∀ i, Q i ^ (n ^ j) = 1) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ P.A), y ^ (n ^ j) = 1 → ∃! c : Ix g (n ^ j), Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp R)) ≫ Q i) (fun i => (c i).val) = y)) → VeryDense {q | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (ψ : t'.A.left ⟶ P.A.left), RingHom.ker x = q ∧ t'.HasTh (𝟙 _) (fun a => x (v a)) ∧ (IsGrpPullback t'.A P.A (spMap x) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ (n ^ j)).left ≫ ψ = (spMap x) ≫ (Q i).left)} → ∃ t : TObj g ((n ^ j) ^ 2) J b (spMap β), t.HasTh (𝟙 _) v ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (ψ : t'.A.left ⟶ P.A.left), t'.HasTh (𝟙 _) (fun a => x (v a)) → (IsGrpPullback t'.A P.A (spMap x) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ (n ^ j)).left ≫ ψ = (spMap x) ≫ (Q i).left) → TMap t' t (spMap x) := by
  intro hL hL2 g n j J hn hodd hj o _ b R _ _ _ β v P act Q hP hdense
  have hn2 : 2 ≤ n := hn.two_le
  have hpos : 0 < n ^ j := pow_pos hn.pos j
  have hdvd : n ∣ n ^ j := dvd_pow_self n (by omega)
  have h3 : 3 ≤ n ^ j := by
    have h4 : 2 ^ 2 ≤ n ^ j := (Nat.pow_le_pow_left hn2 2).trans (Nat.pow_le_pow_right hn.pos hj)
    omega
  obtain ⟨R₁, _, _, t₁, ψ₁, hfin, het, hab, huniv⟩ := GlobalTheory.exists_finiteEtale_level_cover hL hL2 o g (n ^ j) J b R β P act Q hpos hP
  have hab' : Above P act Q (n ^ j) t₁ (spMap (algebraMap R R₁)) ψ₁ := hab
  have hspan : Ideal.span (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨p, ⟨K, _, _, x, t', ψ, hker, hth, -⟩, -, hqp, -⟩ :=
      hdense q 1 hq.isPrime (fun h => hq.ne_top ((Ideal.eq_top_iff_one _).2 h))
    obtain ⟨c, hc⟩ := GlobalTheory.coset_of_hasTh hL hL2 o g (n ^ j) J b _ _ t' n K (𝟙 _) _ ⊥ hn2 hdvd hth Ideal.isPrime_bot 0
    apply hc
    have : v (0 + (n ^ j / n) • c) ∈ RingHom.ker x := hker ▸ hqp (hle (Ideal.subset_span ⟨_, rfl⟩))
    exact this
  have hspan₁ : Ideal.span (Set.range fun a => algebraMap R R₁ (v a)) = ⊤ := by
    have := congrArg (Ideal.map (algebraMap R R₁)) hspan
    rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  obtain ⟨𝔞, h𝔞⟩ := GlobalTheory.ThetaClosed.exists_ideal_hasTh_iff hL hL2 o g (n ^ j) J b R₁ _ t₁ _ hodd.pow h3 hspan₁

  have hth : ∀ (R' : Type) [CommRing R'] (x : R →+* R') (y : R₁ →+* R') (s' : Sp R' ⟶ Sp o)
      (t' : TObj g ((n ^ j) ^ 2) J b s'), y.comp (algebraMap R R₁) = x → TMap t' t₁ (spMap y) →
      (t'.HasTh (𝟙 _) (fun a => x (v a)) ↔ ∀ r ∈ 𝔞, y r = 0) := by
    intro R' _ x y s' t' e hm
    subst e
    rw [GlobalTheory.hasTh_iff_of_tmap o g (n ^ j) J b _ _ t₁ _ _ t' _ R' _ _ hm, Category.id_comp]
    exact h𝔞 R' y

  have huniq : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (y y' : R₁ →+* K),
      y.comp (algebraMap R R₁) = x → y'.comp (algebraMap R R₁) = x → (∀ r ∈ 𝔞, y r = 0) → (∀ r ∈ 𝔞, y' r = 0) →
      y = y' := by
    intro K _ _ x y y' e e' k k'
    have d : spMap y ≫ spMap (algebraMap R R₁) = spMap x := by rw [spMap_comp, e]
    have d' : spMap y' ≫ spMap (algebraMap R R₁) = spMap x := by rw [spMap_comp, e']
    obtain ⟨u, hu⟩ := GlobalTheory.tObj_pull o g _ J b _ _ _ (spMap x ≫ spMap β) (spMap y) t₁ (by rw [← Category.assoc, d])
    obtain ⟨u', hu'⟩ := GlobalTheory.tObj_pull o g _ J b _ _ _ (spMap x ≫ spMap β) (spMap y') t₁ (by rw [← Category.assoc, d'])
    have T := (hth K x y _ u e hu).2 k
    have T' := (hth K x y' _ u' e' hu').2 k'
    obtain ⟨φ, a₁, a₂, a₃, a₄⟩ := id hu
    obtain ⟨φ', a₁', a₂', a₃', a₄'⟩ := id hu'
    have A := hab'.comp a₁ a₂ a₃ a₄
    have A' := hab'.comp a₁' a₂' a₃' a₄'
    rw [d] at A
    rw [d'] at A'
    obtain ⟨χ, c₀, c₁, c₂, c₃, c₄⟩ := A.compare A'
    have c₅ := GlobalTheory.level_eq_of_pow_eq_of_hasTh hL hL2 g n j J hn hodd hj o b K _ u u' χ _ c₁ c₂ c₃ T T'
    have hχ : TMap u' u (𝟙 _) := ⟨χ, c₁, c₂, fun i => by rw [c₅, Category.id_comp], c₄⟩
    have hm : TMap u' t₁ (spMap y) := by
      have := ((GlobalTheory.ZM.tmap_id_comp_cancel o g _ J b _ _ _ _ _ _ t₁ u u').2 _ _ hu).1 hχ
      rwa [Category.id_comp] at this
    refine (huniv K x u' (φ' ≫ ψ₁) A').unique ⟨e, fun i => ?_, hm⟩ ⟨e', fun i => ?_, hu'⟩
    · rw [← c₀, ← Category.assoc, c₅, ← Category.assoc, a₃, Category.assoc]
    · rw [← Category.assoc, a₃', Category.assoc]
  have hcomp : (Ideal.Quotient.mk 𝔞).comp (algebraMap R R₁) = algebraMap R (R₁ ⧸ 𝔞) := rfl
  have : Algebra.FormallyUnramified R (R₁ ⧸ 𝔞) :=
    Algebra.FormallyUnramified.of_surjective (Ideal.Quotient.mkₐ R 𝔞) Ideal.Quotient.mk_surjective
  have hbij : Function.Bijective (algebraMap R (R₁ ⧸ 𝔞)) := by
    refine GlobalTheory.algebraMap_bijective_of_unramified_of_unique_geometric_point R (R₁ ⧸ 𝔞) _ hdense ?_
    rintro q ⟨K, _, _, x, t', ψ, hker, T, A⟩
    obtain ⟨y, ⟨e, -, hm⟩, -⟩ := huniv K x t' ψ A
    have k := (hth K x y _ t' e hm).1 T
    refine ⟨K, inferInstance, inferInstance, x, hker, Ideal.Quotient.lift 𝔞 y k, ?_, fun z hz => ?_⟩
    · exact e
    · have := huniq K x (z.comp (Ideal.Quotient.mk 𝔞)) y hz e
        (fun r hr => by rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]) k
      exact Ideal.Quotient.ringHom_ext (this.trans (by ext r; rfl))
  let ε : R ≃+* R₁ ⧸ 𝔞 := RingEquiv.ofBijective _ hbij
  let ρ : R₁ →+* R := (ε.symm : R₁ ⧸ 𝔞 →+* R).comp (Ideal.Quotient.mk 𝔞)
  have hρ : ρ.comp (algebraMap R R₁) = RingHom.id R := RingHom.ext fun r => ε.symm_apply_apply r
  have hρ' : ∀ r, r - algebraMap R R₁ (ρ r) ∈ 𝔞 := fun r =>
    Ideal.Quotient.eq.1 (ε.apply_symm_apply (Ideal.Quotient.mk 𝔞 r)).symm
  obtain ⟨t, ht⟩ := GlobalTheory.tObj_pull o g _ J b _ _ _ (spMap β) (spMap ρ) t₁
    (by rw [← Category.assoc, spMap_comp, hρ, spMap_id, Category.id_comp])
  refine ⟨t, (hth R (RingHom.id R) ρ _ t hρ ht).2 fun r hr => ?_, fun K _ _ x t' ψ T A => ?_⟩
  · show ε.symm (Ideal.Quotient.mk 𝔞 r) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
  · obtain ⟨y, ⟨e, -, hm⟩, -⟩ := huniv K x t' ψ A
    have k := (hth K x y _ t' e hm).1 T
    have hy : x.comp ρ = y := RingHom.ext fun r => by
      have := k _ (hρ' r)
      rw [map_sub, sub_eq_zero] at this
      rw [this, ← e]; rfl
    refine ((GlobalTheory.ZM.tmap_id_comp_cancel o g _ J b _ _ _ _ _ _ t₁ t t').2 _ _ ht).2 ?_
    rwa [spMap_comp ρ x, hy]

end GlobalTheory.LevelTheta
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_square_level_with_given_thetaPoint : Out.Laws → Out.Laws2 → ∀ (g n j : ℕ) (J : Type), n.Prime → Odd n → 2 ≤ j → ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (P : Out.PolAV (Sp R)) (act : J → (P.A ⟶ P.A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ P.A)), (P.g = g ∧ (∀ i, IsMonHom (act i)) ∧ (∀ i, Q i ^ (n ^ j) = 1) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ P.A), y ^ (n ^ j) = 1 → ∃! c : Ix g (n ^ j), Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp R)) ≫ Q i) (fun i => (c i).val) = y)) → VeryDense {q | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (ψ : t'.A.left ⟶ P.A.left), RingHom.ker x = q ∧ t'.HasTh (𝟙 _) (fun a => x (v a)) ∧ (IsGrpPullback t'.A P.A (spMap x) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ (n ^ j)).left ≫ ψ = (spMap x) ≫ (Q i).left)} → ∃ t : TObj g ((n ^ j) ^ 2) J b (spMap β), t.HasTh (𝟙 _) v ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (ψ : t'.A.left ⟶ P.A.left), t'.HasTh (𝟙 _) (fun a => x (v a)) → (IsGrpPullback t'.A P.A (spMap x) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ (n ^ j)).left ≫ ψ = (spMap x) ≫ (Q i).left) → TMap t' t (spMap x) := by
  atlas_forward_decl GlobalTheory.LevelTheta.exists_level_with_theta_point
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem exists_tObj_of_veryDense : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R), VeryDense (objPrimes b Mat κ β v) → ∃ t : TObj g ((n ^ j) ^ 2) J b (spMap β), t.HasTh (𝟙 _) v ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → TMap t' t (spMap x) := by
  intro h1 h2 g J _ Mat κ n hn hodd
  obtain ⟨j1, H1⟩ := GlobalTheory.T.exists_theta_scheme_sections_good_fibres h1 h2 g J Mat κ n hn hodd
  obtain ⟨j2, H2⟩ := GlobalTheory.T.exists_family_addition_morphism_thetaLevel h1 h2 g J Mat κ n hn hodd
  obtain ⟨j3, H3⟩ := GlobalTheory.T.exists_inversion_endomorphisms_thetaLevelFamily h1 h2 g J Mat κ n hn hodd
  obtain ⟨j4, H4⟩ := GlobalTheory.T.exists_principallyPolarised_of_veryDense_fibres h1 h2 g J Mat κ n hn hodd
  refine ⟨j1 + j2 + j3 + j4 + 4, ?_⟩
  intro j hj o _ b R _ _ _ β v hv
  obtain ⟨Z, I, M, th, sc, p, hZ, hfib⟩ := H1 j (by omega) o b R β v hv
  obtain ⟨m, hm⟩ := H2 j (by omega) o b R β v Z I M th sc p hv hZ hfib
  obtain ⟨F, hF⟩ := H3 j (by omega) o b R β v Z I M th sc p hv hZ hfib
  obtain ⟨P, act, Q, hP, hgood⟩ := H4 j (by omega) o b R β v Z I M th sc p m F hv hZ hfib hm hF
  obtain ⟨t, ht, hlast⟩ := GlobalTheory.T.exists_square_level_with_given_thetaPoint h1 h2 g n j J hn hodd (by omega) o b R β v P act Q hP (by
    intro q f hq hf
    obtain ⟨p', ⟨K, iK, iK', x, t', hker, hsh, hth⟩, hp'⟩ := hv q f hq hf
    obtain ⟨ψ, hψ⟩ := hgood K x t' hsh hth
    exact ⟨p', ⟨K, iK, iK', x, t', ψ, hker, hth, hψ⟩, hp'⟩)
  refine ⟨t, ht, ?_⟩
  intro K _ _ x t' hsh hth
  obtain ⟨ψ, hψ⟩ := hgood K x t' hsh hth
  exact hlast K x t' ψ hth hψ

end GlobalTheory.ZM
end
