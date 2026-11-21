import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalTripleFibrePrincipallyPolarisedDimensio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointExtendsAlongThetaMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveHomogeneousCoordsFieldDetermineDescendStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueProjectiveSpaceMapsOfAgreeGeometricPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantListAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreExistsGeneratorStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdThetaMapOnNormalCharZeroAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMapPullO1Power
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMapFiniteGeometricFibresOfLargeLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsPrimitiveAtUniformisedTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantListsUniqueUpToPermScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitThroughModuliGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalTripleFibrePrincipallyPolarisedDimensioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreIffOfGrpPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHasDivOfGenericPointProjectiveCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMapCoordsOfSymmetricThetaIsomorphicFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFamiliesThetaSymmetricMinMemberCompareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSymmetricFunctionValuesInGroundField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantListRealisedSystemUpToRootsOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedThetaSystemSectionGeneratesFieldFibresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDivisorOfForallCompleteDvrPointsStatement
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedBlowupCyclotomicAwayProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomExtOfSecCoord
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecCoordOfSubsingletonPic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOverProjectiveSpaceProjectiveAmpleTwist

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_mem_mul_eq_zero_of_algebraMap_eq_zero {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] (M : Submonoid R) [IsLocalization M S] :
    ∃ f ∈ M, ∀ a : R, algebraMap R S a = 0 → f * a = 0 := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (RingHom.ker (algebraMap R S)) :
    (RingHom.ker (algebraMap R S)).FG)
  have hk : ∀ a ∈ s, ∃ m : M, (m : R) * a = 0 := by
    intro a ha
    have : a ∈ RingHom.ker (algebraMap R S) := hs ▸ Submodule.subset_span ha
    exact (IsLocalization.map_eq_zero_iff M S a).1 this
  choose! m hm using hk
  refine ⟨∏ a ∈ s, (m a : R), Submonoid.prod_mem _ fun a _ => (m a).2, ?_⟩
  have key : ∀ a ∈ Submodule.span R (s : Set R), (∏ a ∈ s, (m a : R)) * a = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem b hb =>
        rw [← Finset.prod_erase_mul _ _ hb, _root_.mul_assoc, hm b hb, mul_zero]
    | zero => simp
    | add b c _ _ hb hc => rw [mul_add, hb, hc, add_zero]
    | smul r b _ hb => rw [smul_eq_mul, _root_.mul_left_comm, hb, mul_zero]
  intro a ha
  exact key a (hs ▸ ha)

theorem exists_affineOpen_isIntegrallyClosed_charZero (X : Scheme.{0})
    (hN : Geo.Tor.IsNormalScheme X) (hL : IsLocallyNoetherian X)
    (h0 : ∀ x : X, CharZero (X.residueField x)) (x : X) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ IsDomain Γ(X, U) ∧ IsNoetherianRing Γ(X, U) ∧
      IsIntegrallyClosed Γ(X, U) ∧ CharZero Γ(X, U) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  letI := X.presheaf.algebra_section_stalk (U := V) ⟨x, hxV⟩
  haveI := hV.isLocalization_stalk ⟨x, hxV⟩
  obtain ⟨f, hfM, hf⟩ := exists_mem_mul_eq_zero_of_algebraMap_eq_zero (R := Γ(X, V))
    (S := X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
  have hU : IsAffineOpen (X.basicOpen f) := hV.basicOpen f
  have hxU : x ∈ X.basicOpen f := by
    rw [X.mem_basicOpen f x hxV]
    exact IsLocalization.map_units (X.presheaf.stalk x) ⟨f, hfM⟩

  letI : Algebra Γ(X, V) Γ(X, X.basicOpen f) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
  haveI : IsLocalization.Away f Γ(X, X.basicOpen f) := hV.isLocalization_basicOpen f
  let g : Γ(X, X.basicOpen f) →+* X.presheaf.stalk x := (X.presheaf.germ _ x hxU).hom
  have hcomp : ∀ a : Γ(X, V), g (algebraMap Γ(X, V) Γ(X, X.basicOpen f) a) =
      algebraMap Γ(X, V) (X.presheaf.stalk x) a := fun a =>
    X.presheaf.germ_res_apply (homOfLE (X.basicOpen_le f)) x hxU a
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro σ hσ
    obtain ⟨⟨r, m⟩, hrm⟩ := IsLocalization.surj (Submonoid.powers f) σ
    have hr : algebraMap Γ(X, V) (X.presheaf.stalk x) r = 0 := by
      rw [← hcomp, ← hrm, map_mul, hσ, zero_mul]
    have hfr := congrArg (algebraMap Γ(X, V) Γ(X, X.basicOpen f)) (hf r hr)
    rw [map_mul, map_zero] at hfr
    have hu : IsUnit (algebraMap Γ(X, V) Γ(X, X.basicOpen f) f) :=
      IsLocalization.map_units Γ(X, X.basicOpen f) ⟨f, Submonoid.mem_powers f⟩
    have hr0 := hu.mul_right_eq_zero.1 hfr
    have hmu : IsUnit (algebraMap Γ(X, V) Γ(X, X.basicOpen f) (m : Γ(X, V))) :=
      IsLocalization.map_units Γ(X, X.basicOpen f) m
    rw [hr0] at hrm
    exact hmu.mul_left_eq_zero.1 hrm
  haveI : IsDomain (X.presheaf.stalk x) := (hN x).1
  haveI hD : IsDomain Γ(X, X.basicOpen f) := hinj.isDomain g
  haveI : CharZero (X.residueField x) := h0 x
  have hcz : CharZero Γ(X, X.basicOpen f) := by
    refine ⟨fun a b hab => ?_⟩
    have := congrArg ((X.residue x).hom.comp g) hab
    simp only [map_natCast] at this
    exact Nat.cast_injective this
  have hIC : IsIntegrallyClosed Γ(X, X.basicOpen f) := by
    refine IsIntegrallyClosed.of_localization_maximal fun p _ hp ↦ ?_
    let P : Spec Γ(X, X.basicOpen f) := ⟨p, hp.isPrime⟩
    have hy : hU.fromSpec P ∈ X.basicOpen f := hU.range_fromSpec.le ⟨P, rfl⟩
    letI : Algebra Γ(X, X.basicOpen f) (X.presheaf.stalk (hU.fromSpec P)) :=
      X.presheaf.algebra_section_stalk (U := X.basicOpen f) ⟨_, hy⟩
    have h : IsLocalization p.primeCompl (X.presheaf.stalk (hU.fromSpec P)) :=
      hU.isLocalization_stalk' P hy
    haveI := (hN (hU.fromSpec P)).1
    haveI := (hN (hU.fromSpec P)).2
    exact IsIntegrallyClosed.of_equiv (R := X.presheaf.stalk (hU.fromSpec P))
      (IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk (hU.fromSpec P))
        (Localization.AtPrime p)).toRingEquiv
  exact ⟨⟨X.basicOpen f, hU⟩, hxU, hD, IsLocallyNoetherian.component_noetherian ⟨_, hU⟩, hIC, hcz⟩

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineOpen_normal_noetherian_charZero : ∀ (X : Scheme.{0}), Geo.Tor.IsNormalScheme X → IsLocallyNoetherian X → (∀ x : X, CharZero (X.residueField x)) → ∀ x : X,
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ IsDomain Γ(X, U) ∧ IsNoetherianRing Γ(X, U) ∧ IsIntegrallyClosed Γ(X, U) ∧ CharZero Γ(X, U) := by
  atlas_forward_decl GlobalTheory.exists_affineOpen_isIntegrallyClosed_charZero
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ThetaMapGen

theorem agree_at_geom : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen →
    ∀ (g m n : ℕ) (o K : Type) [CommRing o] [Field K] [IsAlgClosed K] (z : Sp K ⟶ S) (f₁ f₂ : Sp K ⟶ PSpace o n),
    Odd m → IsUnit (m : o) → n + 1 = m ^ (4 * g) → PolFib G L g z → f₁ ≫ PSpace.str o n = f₂ ≫ PSpace.str o n →
    (∀ c : Fin (n + 1) → K, HasTh G L ρ m z c → PCrd f₁ (symTup c)) → (∀ c : Fin (n + 1) → K, HasTh G L ρ m z c → PCrd f₂ (symTup c)) → f₁ = f₂ := by
  intro S G _ _ L ρ hL hρ g m n o K _ _ _ z f₁ f₂ hm hu hn hP hs h₁ h₂
  obtain ⟨⟨θ, hθ⟩, -⟩ := GlobalTheory.T.principallyPolarisedFibre_exists_generator_stable S G L hL g K z hP
  have hmK : (m : K) ≠ 0 := by
    let φ : o →+* K := (Spec.preimage (f₁ ≫ PSpace.str o n)).hom
    have := hu.map φ
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨pt, c, hc⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed S G L ρ hL hρ g m (n + 1) K z θ hm hmK hn hP
  have hH : HasTh G L ρ m z c := ⟨θ, pt, hθ, hc⟩
  exact (GlobalTheory.T.projectiveHomogeneousCoords_field_determine_descend).1 o K n f₁ f₂ (symTup c) hs (h₁ c hH) (h₂ c hH)

theorem main : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m n : ℕ) (o : Type) [CommRing o] (X : Scheme.{0}) (s : X ⟶ Sp o) (q : X ⟶ S), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * g) → Geo.Tor.IsNormalScheme X → IsLocallyNoetherian X → (∀ x : X, CharZero (X.residueField x)) → (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X), PolFib G L g (x ≫ q)) → ∃ f : X ⟶ PSpace o n, f ≫ PSpace.str o n = s ∧ ThMap G L ρ m q f := by
  intro S G _ _ L ρ hL hρ g m n o _ X s q hm h3 hu hn hN hLN h0 hP
  have loc : ∀ x : X, ∃ (W : X.Opens) (h : W.toScheme ⟶ PSpace o n), x ∈ W ∧ h ≫ PSpace.str o n = W.ι ≫ s ∧
      ThMap G L ρ m (W.ι ≫ q) h := by
    intro x
    obtain ⟨U, hxU, h1, h2, h3', h4⟩ := GlobalTheory.T.exists_affineOpen_normal_noetherian_charZero X hN hLN h0 x
    exact GlobalTheory.T.exists_nhd_thetaMap_on_normal_charZero_affine S G L ρ hL hρ g m n o X s q hm h3 hu hn hP U h1 h2 h3' h4 x hxU
  choose W h hxW hs hT using loc
  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    haveI := (hN x).1; infer_instance
  haveI : IsReduced X := isReduced_of_isReduced_stalk X
  have hcov : (⨆ x, W x) = ⊤ := by
    rw [eq_top_iff]; intro x _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩
  obtain ⟨f, hf, hfW⟩ := GlobalTheory.T.glue_projectiveSpace_maps_of_agree_geometric_points o n X s X W h hcov hs (by
    intro i j K _ _ y y' hyy
    refine agree_at_geom S G L ρ hL hρ g m n o K (y ≫ (W i).ι ≫ q) _ _ hm hu hn (by rw [← Category.assoc]; exact hP K _) ?_ ?_ ?_
    · rw [Category.assoc, hs, Category.assoc, hs, ← Category.assoc, hyy, Category.assoc]
    · intro c hc; exact hT i K y c hc
    · intro c hc
      have := hT j K y' c (by rwa [← Category.assoc, ← hyy, Category.assoc])
      exact this)
  refine ⟨f, hf, ?_⟩
  intro K _ x c hc
  let p0 : Sp K := IsLocalRing.closedPoint K
  let i := x.base p0
  have hr : Set.range x.base ⊆ Set.range (W i).ι.base := by
    rintro _ ⟨y, rfl⟩
    have : y = p0 := Subsingleton.elim _ _
    subst this
    rw [Scheme.Opens.range_ι]; exact hxW i
  let x' := IsOpenImmersion.lift (W i).ι x hr
  have hx' : x' ≫ (W i).ι = x := IsOpenImmersion.lift_fac _ _ _
  have := hT i K x' c (by rw [← Category.assoc, hx']; exact hc)
  rw [← hx', Category.assoc, hfW i]; exact this

end GlobalTheory.UMin.ThetaMapGen
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMap_abelianScheme_normal_charZero_base : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m n : ℕ) (o : Type) [CommRing o] (X : Scheme.{0}) (s : X ⟶ Sp o) (q : X ⟶ S), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * g) → Geo.Tor.IsNormalScheme X → IsLocallyNoetherian X → (∀ x : X, CharZero (X.residueField x)) → (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X), PolFib G L g (x ≫ q)) → ∃ f : X ⟶ PSpace o n, f ≫ PSpace.str o n = s ∧ ThMap G L ρ m q f := by
  atlas_forward_decl GlobalTheory.UMin.ThetaMapGen.main
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.CmpTrait

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  rw [← Spec.map_id]; rfl

theorem comp_pow'' {S : Scheme.{0}} {A T T₀ : Over S} [GrpObj A] (ρ : T₀ ⟶ T) (x : T ⟶ A) (n : ℕ) :
    ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem card_le_of_thList {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m : ℕ} {K : Type} [Field K] [IsAlgClosed K] {x : Sp K ⟶ S} {θ θ' : SecAt G L x} {N N' : ℕ}
    {pt : Fin N → (Over.mk x ⟶ G)} {pt' : Fin N' → (Over.mk x ⟶ G)} {c : Fin N → K} {c' : Fin N' → K}
    (h : ThList G L ρ m x θ pt c) (h' : ThList G L ρ m x θ' pt' c') : N ≤ N' := by
  let e : Over.mk (spMap (RingHom.id K) ≫ x) ⟶ Over.mk x := Over.homMk (spMap (RingHom.id K)) rfl
  have key : ∀ a, ∃ b, pt a = pt' b := fun a => by
    have hp : (e ≫ pt a) ^ (m ^ 2) = 1 := by
      rw [← comp_pow'', (h.2.1 a).1, MonObj.comp_one]
    obtain ⟨b, hb⟩ := h'.2.2 K (RingHom.id K) (e ≫ pt a) hp
    refine ⟨b, Over.OverMorphism.ext ?_⟩
    have hb' : spMap (RingHom.id K) ≫ (pt a).left = spMap (RingHom.id K) ≫ (pt' b).left := hb
    rwa [spMap_id', Category.id_comp, Category.id_comp] at hb'
  choose s hs using key
  have hs' : Function.Injective s := fun a a' he => h.1 ((hs a).trans ((congrArg pt' he).trans (hs a').symm))
  simpa using Fintype.card_le_of_injective s hs'

theorem card_eq_of_thList {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m : ℕ} {K : Type} [Field K] [IsAlgClosed K] {x : Sp K ⟶ S} {θ θ' : SecAt G L x} {N N' : ℕ}
    {pt : Fin N → (Over.mk x ⟶ G)} {pt' : Fin N' → (Over.mk x ⟶ G)} {c : Fin N → K} {c' : Fin N' → K}
    (h : ThList G L ρ m x θ pt c) (h' : ThList G L ρ m x θ' pt' c') : N = N' :=
  le_antisymm (card_le_of_thList h h') (card_le_of_thList h' h)

theorem isGenSec_of_nz {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB) {g : ℕ} {K : Type}
    [Field K] {x : Sp K ⟶ S} (hP : PolFib G L g x) {θ : SecAt G L x} (hθ : NZ G L x θ) : IsGenSec G L _ θ := by
  obtain ⟨P, α, -, hp, hw⟩ := hP
  obtain ⟨e, he⟩ := exists_univBasis_of_fibre abelianSchemeLaws_all.2 S (Sp K) G L hL P x α hp hw K (𝟙 _) x
    (Category.id_comp x)
  have h0 : spMap (RingHom.id K) ≫ x = x := by rw [spMap_id', Category.id_comp]
  obtain ⟨a, ha⟩ := he.ex (RingHom.id K) h0 (SecM.ofSec G θ)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_smul] at ha
    obtain ⟨q, -, hq⟩ := hθ
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hq
    have e0 : θ.f j = 0 := congrArg (fun s => s.1 j) ha
    rw [e0, Scheme.basicOpen_zero] at hj
    exact hj
  refine (isGenSec_iff θ).2 fun s => ?_
  obtain ⟨b, hb⟩ := he.ex (RingHom.id K) h0 s
  refine ⟨fnR x (b * a⁻¹), ?_⟩
  rw [hb, ha, smul_smul, ← map_mul, _root_.mul_assoc, inv_mul_cancel₀ ha0, _root_.mul_one]

theorem prim_of_finite {V V' K : Type} [CommRing V] [CommRing V'] [Field K] (f : V →+* V') (i : V' →+* K) {J : Type}
    (c : J → K) (hf : f.Finite) (h : Prim i c) : Prim (i.comp f) c := by
  letI := f.toAlgebra
  letI := i.toAlgebra
  letI := (i.comp f).toAlgebra
  haveI : IsScalarTower V V' K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite V V' := hf
  haveI : Algebra.IsIntegral V V' := Algebra.IsIntegral.of_finite V V'
  have key : ∀ z : K, i.IsIntegralElem z → (i.comp f).IsIntegralElem z := fun z hz =>
    isIntegral_trans (R := V) (A := V') z hz
  obtain ⟨h1, a, ha, ha'⟩ := h
  exact ⟨fun b => key _ (h1 b), a, ha, key _ ha'⟩

theorem exists_ext {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (f : V →+* V')
    (fK : FractionRing V →+* FractionRing V') {K : Type} [Field K] [IsAlgClosed K] (io : FractionRing V →+* K)
    (hf : f.Finite) (hfK : ∀ a, fK (algebraMap V _ a) = algebraMap V' _ (f a)) :
    ∃ io' : FractionRing V' →+* K, io'.comp fK = io := by
  letI := fK.toAlgebra
  letI := io.toAlgebra
  letI := f.toAlgebra
  haveI : Module.Finite V V' := hf
  haveI : Algebra.IsIntegral V V' := Algebra.IsIntegral.of_finite V V'
  have hint : ∀ b : V', IsAlgebraic (FractionRing V) (algebraMap V' (FractionRing V') b) := fun b => by
    obtain ⟨p, hp, hp0⟩ := Algebra.IsIntegral.isIntegral (R := V) b
    refine (show IsIntegral (FractionRing V) (algebraMap V' (FractionRing V') b) from
      ⟨p.map (algebraMap V (FractionRing V)), hp.map _, ?_⟩).isAlgebraic
    rw [Polynomial.eval₂_map]
    have e : (algebraMap (FractionRing V) (FractionRing V')).comp (algebraMap V (FractionRing V)) =
        (algebraMap V' (FractionRing V')).comp (algebraMap V V') := RingHom.ext hfK
    rw [e, ← Polynomial.hom_eval₂, hp0, map_zero]
  haveI : Algebra.IsAlgebraic (FractionRing V) (FractionRing V') := ⟨fun z => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V') z
    exact (hint a).mul (hint b).inv⟩
  let φ : FractionRing V' →ₐ[FractionRing V] K := IsAlgClosed.lift
  exact ⟨φ.toRingHom, RingHom.ext fun a => φ.commutes a⟩

theorem prim_comp {V K : Type} [CommRing V] [Field K] {i : V →+* K} {J J' : Type} {c : J → K} (h : Prim i c)
    (s : J' → J) (hs : Function.Surjective s) : Prim i (c ∘ s) := by
  obtain ⟨h1, a, ha, ha'⟩ := h
  obtain ⟨b, rfl⟩ := hs a
  exact ⟨fun b => h1 _, b, ha, ha'⟩

theorem cmp_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (y : Sp (FractionRing V) ⟶ Xo.XF c) (K : Type) [Field K] [IsAlgClosed K] (io : FractionRing V →+* K) (m m' N N' : ℕ) (d : Fin N → K) (d' : Fin N' → K), Odd m → 3 ≤ m → IsUnit (m : V) → Odd m' → 3 ≤ m' → IsUnit (m' : V) → HasTh₂ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m m' (spMap io ≫ y ≫ pullback.fst _ _) d d' → ∃ a : K, a ≠ 0 ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => d b / a) ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => d' b / a) := by
  intro E _ _ _ H Dw l Xo c V _ _ _ hV y K _ _ io m m' N N' d d' hmo hm3 hmu hmo' hm3' hmu' hd
  have hbase : GlobalTheory.Mum.Base V := ⟨ArcPointDescent.admissibleBase_maximalIdeal_completeDVR hV, hV.2.2⟩
  obtain ⟨T, f, fK, -, -, hff, hfK, hTy⟩ := GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint E H Dw l Xo c V hbase hV.1 y
  obtain ⟨io', hio'⟩ := exists_ext f fK io hff hfK
  set i : T.V →+* K := io'.comp (algebraMap T.V (FractionRing T.V)) with hi
  have hinj : Function.Injective i := io'.injective.comp (IsFractionRing.injective T.V (FractionRing T.V))
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  obtain ⟨tK, ⟨mK⟩, ⟨mx⟩⟩ := T.gen
  obtain ⟨m0, -⟩ := ObjMaps.exists_sab_id T.t
  have hpol : GlobalTheory.LN.PolAt T.t (jK T.V) := UnifAfterExt.polAt_of_sabMap m0 mK mx Xo.univ.proper Xo.univ.ample
    Xo.univ.ktriv (jK T.V) (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
  obtain ⟨σ, hσ⟩ := exists_nz_of_polAt abelianSchemeLaws_all.1 abelianSchemeLaws_all.2 E H (Sp T.V) T.t T.V (𝟙 _) T.t m0
    hpol
  have h0 : spMap (RingHom.id T.V) ≫ 𝟙 (Sp T.V) = 𝟙 _ := by rw [Category.comp_id, spMap_id']
  have hσσ : VVRank.pullS T.t.G _ (Over.homMk (spMap (RingHom.id T.V)) h0 : Over.mk (𝟙 (Sp T.V)) ⟶ Over.mk (𝟙 _)) σ = σ := by
    have e : (Over.homMk (spMap (RingHom.id T.V)) h0 : Over.mk (𝟙 (Sp T.V)) ⟶ Over.mk (𝟙 _)) = 𝟙 _ :=
      Over.OverMorphism.ext (spMap_id' T.V)
    rw [e]
    have := VVRank.pullM_id T.t.G T.t.PP.isLB ((1 : ℕ) : ℤ) (SecM.ofSec T.t.G σ)
    rw [VVRank.pullM_ofSec] at this
    exact congrArg (SecM.toSec T.t.G) this
  have hnz : NZ T.t.G T.t.PP.L (𝟙 _) σ := by
    have := hσ T.V (RingHom.id _) _ h0
    rwa [hσσ] at this
  have hmT : ∀ {k : ℕ}, IsUnit (k : V) → IsUnit (k : T.V) := fun h => by simpa using h.map f
  have hmK : ∀ {k : ℕ}, IsUnit (k : V) → (k : K) ≠ 0 := fun h => by
    have := h.map (io.comp (algebraMap V (FractionRing V))); simpa using this.ne_zero
  set x₁ : Sp K ⟶ Sp T.V := spMap i ≫ 𝟙 (Sp T.V) with hx₁
  have ex₁ : spMap io' ≫ jK T.V = x₁ := by rw [hx₁, Category.comp_id, hi, spMap_comp']
  set x : Sp K ⟶ Xo.X := spMap io ≫ y ≫ pullback.fst _ _ with hx
  have ex : spMap io' ≫ T.y ≫ pullback.fst _ _ = x := by rw [hx, hTy, ← hio', spMap_comp']; simp only [Category.assoc]
  set g := Module.finrank ℚ E / 2 * (Dw.p + Dw.q) with hg
  have hPx : PolFib Xo.univ.t.G Xo.univ.t.PP.L g x := GlobalTheory.T.universalTriple_fibre_principallyPolarised_dimension E H Dw l Xo c K x
  obtain ⟨wK, hwK, -⟩ := mK.lin
  obtain ⟨wx, hwx, -⟩ := mx.lin
  have hPK : PolFib tK.G tK.PP.L g (spMap io') :=
    ((GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback _ _ _ _ _ _ _ _ Xo.univ.t.PP.isLB tK.PP.isLB mx.cart ⟨wx, hwx⟩ g K (spMap io')).1).2 (ex ▸ hPx)
  have hP₁ : PolFib T.t.G T.t.PP.L g x₁ :=
    ex₁ ▸ ((GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback _ _ _ _ _ _ _ _ T.t.PP.isLB tK.PP.isLB mK.cart ⟨wK, hwK⟩ g K (spMap io')).1).1 hPK
  set θ := SecAt.pull T.t.G T.t.PP.L σ i with hθdef
  have hθnz : NZ T.t.G T.t.PP.L x₁ θ := hσ K i x₁ rfl
  have hθ : IsGenSec T.t.G T.t.PP.L _ θ := isGenSec_of_nz T.t.PP.isLB hP₁ hθnz
  obtain ⟨pt, cc, hc⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed _ T.t.G T.t.PP.L T.t.PP.rig T.t.PP.isLB T.t.PP.rigGen g m _ K x₁ θ hmo (hmK hmu)
    rfl hP₁
  obtain ⟨pt', cc', hc'⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed _ T.t.G T.t.PP.L T.t.PP.rig T.t.PP.isLB T.t.PP.rigGen g m' _ K x₁ θ hmo'
    (hmK hmu') rfl hP₁
  have hpr : Prim i cc := GlobalTheory.T.thetaConstants_primitive_at_uniformisedTrait E H (Sp T.V) T.t T.V T.cdvr (𝟙 _) T.t ⟨m0⟩ ⟨T.P⟩ σ hnz m _ hmo hm3 (hmT hmu)
    K i pt cc hinj hc
  have hpr' : Prim i cc' := GlobalTheory.T.thetaConstants_primitive_at_uniformisedTrait E H (Sp T.V) T.t T.V T.cdvr (𝟙 _) T.t ⟨m0⟩ ⟨T.P⟩ σ hnz m' _ hmo' hm3'
    (hmT hmu') K i pt' cc' hinj hc'
  have h₁ : HasTh₂ T.t.G T.t.PP.L T.t.PP.rig m m' x₁ cc cc' := ⟨θ, pt, pt', hθ, hc, hc'⟩
  have hK : HasTh₂ tK.G tK.PP.L tK.PP.rig m m' (spMap io') cc cc' :=
    (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian _ T.t.G T.t.PP.L T.t.PP.rig T.t.PP.isLB T.t.PP.rigGen _ tK.G tK.PP.L tK.PP.rig (jK T.V) mK.φ
      tK.PP.isLB tK.PP.rigGen mK.cart ⟨wK, hwK⟩ m m' _ _ K (spMap io') cc cc').2 (ex₁ ▸ h₁)
  have hX : HasTh₂ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m m' x cc cc' :=
    ex ▸ (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian _ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig Xo.univ.t.PP.isLB Xo.univ.t.PP.rigGen _ tK.G
      tK.PP.L tK.PP.rig (T.y ≫ pullback.fst _ _) mx.φ tK.PP.isLB tK.PP.rigGen mx.cart ⟨wx, hwx⟩ m m' _ _ K (spMap io')
      cc cc').1 hK
  have eN : N = m ^ (4 * g) := by
    obtain ⟨_, _, _, _, hd1, -⟩ := hd
    obtain ⟨_, _, _, _, hc1, -⟩ := hX
    exact card_eq_of_thList hd1 hc1
  have eN' : N' = m' ^ (4 * g) := by
    obtain ⟨_, _, _, _, -, hd2⟩ := hd
    obtain ⟨_, _, _, _, -, hc2⟩ := hX
    exact card_eq_of_thList hd2 hc2
  subst eN eN'
  obtain ⟨a, s, s', ha, hds, hds'⟩ := (GlobalTheory.T.thetaConstantLists_unique_up_to_perm_scalar _ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig Xo.univ.t.PP.isLB
    Xo.univ.t.PP.rigGen g m m' _ _ K x hmo (hmK hmu) hmo' (hmK hmu') hPx).2 cc d cc' d' hX hd
  have ei : i.comp f = io.comp (algebraMap V (FractionRing V)) := by
    ext v
    simp only [hi, RingHom.comp_apply, ← hfK, ← hio']
  have e1 : (fun b => d b / a) = cc ∘ s := funext fun b => by
    rw [hds b, Function.comp_apply, mul_div_cancel_left₀ _ ha]
  have e2 : (fun b => d' b / a) = cc' ∘ s' := funext fun b => by
    rw [hds' b, Function.comp_apply, mul_div_cancel_left₀ _ ha]
  refine ⟨a, ha, ?_, ?_⟩
  · rw [e1, ← ei]
    exact prim_of_finite f i _ hff (prim_comp hpr s s.surjective)
  · rw [e2, ← ei]
    exact prim_of_finite f i _ hff (prim_comp hpr' s' s'.surjective)

end GlobalTheory.UMin.CmpTrait
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstants_two_levels_same_scale_at_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (y : Sp (FractionRing V) ⟶ Xo.XF c) (K : Type) [Field K] [IsAlgClosed K] (io : FractionRing V →+* K) (m m' N N' : ℕ) (d : Fin N → K) (d' : Fin N' → K), Odd m → 3 ≤ m → IsUnit (m : V) → Odd m' → 3 ≤ m' → IsUnit (m' : V) → HasTh₂ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m m' (spMap io ≫ y ≫ pullback.fst _ _) d d' → ∃ a : K, a ≠ 0 ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => d b / a) ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => d' b / a) := by
  atlas_forward_decl GlobalTheory.UMin.CmpTrait.cmp_trait
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThInt

theorem spMap_comp_ring' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem grpPullback_self' {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem sec_eq' {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'
  simp only [LB.Sec.mk.injEq]
  exact funext h

theorem pullS_comp' {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) (a : ℤ) {T T' T'' : Over S}
    (h : T' ⟶ T) (h' : T'' ⟶ T') (s : LB.Sec (LPow G L a T)) :
    VVRank.pullS G a h' (VVRank.pullS G a h s) = VVRank.pullS G a (h' ≫ h) s := by
  refine sec_eq' (sec_ext_val hL (fun y J hJ => ?_))
  refine (VVRank.sv_pullS G a h' _ (𝟙 _) y hJ).trans ((VVRank.sv_pullS G a h s _ y hJ).trans ?_)
  refine Eq.trans ?_ (VVRank.sv_pullS G a (h' ≫ h) s (𝟙 _) y hJ).symm
  rw [MonoidalCategory.comp_whiskerRight, Over.comp_left, Category.assoc]

theorem thList_congr' {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m : ℕ} {R : Type} [CommRing R] {x : Sp R ⟶ S} (θ : SecAt G L x) {K : Type} [Field K]
    {y y' : Sp K ⟶ S} (e : y = y') (u : Over.mk y ⟶ Over.mk x) (u' : Over.mk y' ⟶ Over.mk x) (hu : u.left = u'.left)
    {N : ℕ} {pt : Fin N → (Over.mk y ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m y (VVRank.pullS G _ u θ) pt c) :
    ∃ pt' : Fin N → (Over.mk y' ⟶ G), ThList G L ρ m y' (VVRank.pullS G _ u' θ) pt' c := by
  subst e
  obtain rfl : u = u' := Over.OverMorphism.ext hu
  exact ⟨pt, H⟩

theorem thList_pull_pull {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB)
    {ρ : LB.Gen (L.pull (eSec G))} {m : ℕ} {R R' : Type} [CommRing R] [CommRing R'] {K : Type} [Field K]
    (x : Sp R ⟶ S) (θ : SecAt G L x) (i : R →+* R') (j : R' →+* K) {N : ℕ}
    {pt : Fin N → (Over.mk (spMap j ≫ spMap i ≫ x) ⟶ G)} {c : Fin N → K}
    (H : ThList G L ρ m (spMap j ≫ spMap i ≫ x) (SecAt.pull G L (SecAt.pull G L θ i) j) pt c) :
    ∃ pt' : Fin N → (Over.mk (spMap (j.comp i) ≫ x) ⟶ G), ThList G L ρ m (spMap (j.comp i) ≫ x)
      (SecAt.pull G L θ (j.comp i)) pt' c := by
  simp only [SecAt.pull] at H ⊢
  rw [pullS_comp' G hL] at H
  refine thList_congr' θ (by rw [← Category.assoc, spMap_comp_ring']) _ _ ?_ H
  simp only [Over.comp_left, Over.homMk_left]
  rw [spMap_comp_ring']

end GlobalTheory.UMin.ThInt

namespace GlobalTheory.UMin

open GlobalTheory.UMin.ThInt in

theorem thetaInt_hasDiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp (ratHull S.R) ⟶ Xo.XF c), UOver Xo c ρ.P (toRat S.R) u → ∀ (M : RatModel o' Ω) (g : M.Z ⟶ PSpace o n), Geo.Tor.IsNormalScheme M.Z → M.pt ≫ g = spMap (ratHull S.R).val.toRingHom ≫ u ≫ f → M.HasDiv S.th := by
  intro E _ _ _ H Dw l Xo c o _ m n f hm hm3 hmu hn hf o' Ω _ _ _ _ S ρ u hu M g hnorm hg
  haveI : CharZero Ω := ArithBase.char o'
  haveI : IsDedekindDomain o' := ArithBase.ded Ω
  haveI : IsAbelianScheme ρ.P.A := ρ.P.isAb
  haveI : IsCommMonObj ρ.P.A := IsAbelianScheme.comm
  set gd := Module.finrank ℚ E / 2 * (Dw.p + Dw.q) with hgd
  let vH : ratHull S.R →+* Ω := (ratHull S.R).val.toRingHom
  let v : S.R →+* Ω := S.R.val.toRingHom
  have hv : vH.comp (toRat S.R) = v := RingHom.ext fun _ => rfl
  let x₀ : Sp Ω ⟶ Sp S.R := spMap v ≫ 𝟙 (Sp S.R)
  let θ : SecAt ρ.P.A ρ.P.L x₀ := SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ v
  have hθ : IsGenSec ρ.P.A ρ.P.L _ θ := GlobalTheory.T.realisedThetaSystem_section_generates_field_fibres o' Ω S ρ Ω v
  obtain ⟨G, _, α, β, hα, hβ, hL⟩ := hu
  haveI : IsAbelianScheme G := PolPull.isAbelianScheme_of_isGrpPullback ρ.P.isAb hα
  haveI : IsCommMonObj G := IsAbelianScheme.comm
  have hLG : (ρ.P.L.pull α).IsLB := pull_isLB ρ.P.isLB α
  have hU := Xo.univ.t.PP.isLB
  have hUr := Xo.univ.t.PP.rigGen

  have hdim := GlobalTheory.UMin.polFib_univ E H Dw l Xo c Ω (spMap vH ≫ u ≫ pullback.fst _ _)
  have hmv1 := GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback Xo.X (Sp (ratHull S.R)) Xo.univ.t.G Xo.univ.t.PP.L G (ρ.P.L.pull α) (u ≫ pullback.fst _ _) β
    hU hLG hβ hL gd Ω (spMap vH)
  have hmv2 := GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback (Sp S.R) (Sp (ratHull S.R)) ρ.P.A ρ.P.L G (ρ.P.L.pull α) (spMap (toRat S.R)) α
    ρ.P.isLB hLG hα (PolBaseChange.lbIso_refl hLG) gd Ω (spMap vH)
  have hPG : PolFib G (ρ.P.L.pull α) gd (spMap vH) := hmv1.1.2 hdim
  have hPF : PolFib ρ.P.A ρ.P.L gd x₀ := by
    have h := hmv2.1.1 hPG
    rwa [spMap_comp_ring', hv, ← Category.comp_id (spMap v)] at h

  obtain ⟨e, he⟩ := GlobalTheory.T.exists_theta_symmetric_function_values_in_ground_field (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen gd m (n + 1) Ω x₀ θ hm hn hPF

  obtain ⟨P', φG, hgP, hφG, hφGL⟩ := hPG
  have hPL : P'.L.IsLB := P'.isLB
  have hφGα : IsGrpPullback P'.A ρ.P.A x₀ (φG ≫ α) :=
    (hφG.comp hα).congr (by rw [spMap_comp_ring', hv]; exact (Category.comp_id _).symm) rfl
  have hφGβ : IsGrpPullback P'.A Xo.univ.t.G ((spMap vH ≫ u) ≫ pullback.fst _ _) (φG ≫ β) :=
    (hφG.comp hβ).congr (by rw [Category.assoc]) rfl
  have hLα : LBIso P'.L (ρ.P.L.pull (φG ≫ α)) :=
    LBIso.trans hPL (pull_isLB hLG φG) (pull_isLB ρ.P.isLB _) hφGL
      (GenSpread.lbIso_pull_of_lbIso (PolBaseChange.lbIso_refl hLG) φG rfl)
  have hLβ : LBIso P'.L (Xo.univ.t.PP.L.pull (φG ≫ β)) :=
    LBIso.trans hPL (pull_isLB ρ.P.isLB _) (pull_isLB hU _) hLα (GenSpread.lbIso_pull_comp φG rfl rfl hL)
  have hcrd := GlobalTheory.T.thetaMap_coords_of_symmetric_theta_isomorphic_fibre Xo.X Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig hU hUr gd m n o (Xo.XF c)
    (pullback.fst _ _) f (Sp S.R) ρ.P.A ρ.P.L ρ.rig Ω (spMap vH ≫ u) x₀ P' (φG ≫ β) (φG ≫ α) θ e hm hn hf
    ρ.P.isLB ρ.rig_gen hgP hφGβ hLβ hφGα hLα hθ he
  have hdiv : M.HasDiv e := by
    refine GlobalTheory.T.model_hasDiv_of_genericPoint_projectiveCoords o' Ω o M n g e ?_
    rw [hg, ← Category.assoc]
    exact hcrd

  haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  have hkodd : Odd (S.r * S.N) := by
    obtain ⟨j, -, hj⟩ := ρ.r_eq
    rw [hj, ρ.N_eq]
    exact (ρ.n_odd.pow).mul ((ρ.n_odd.pow).pow)
  have hk3 : 3 ≤ S.r * S.N := by
    have h2 : 2 ≤ S.r * S.N := le_trans S.N_ge (Nat.le_mul_of_pos_left _ S.r_pos)
    obtain ⟨t, ht⟩ := hkodd
    omega
  refine GlobalTheory.T.hasDivisor_of_forall_complete_dvr_points o' Ω M S.Gam (Fin (n + 1)) S.th e (n + 1).factorial (Nat.factorial_pos _) hnorm hdiv ?_
  intro V _ _ _ hV ξ emb _ j₀ hj₀ hej
  haveI : IsDiscreteValuationRing V := hV.1
  let K := AlgebraicClosure (FractionRing V)
  let io : FractionRing V →+* K := algebraMap _ _
  let i : Ω →+* K := io.comp emb
  have hcast : ∀ t : ℕ, t ≠ 0 → (t : K) ≠ 0 := fun t ht => by
    rw [← map_natCast i t]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 ht)
  have hmV : IsUnit (m : V) := by
    simpa using hmu.map (Spec.preimage (ξ ≫ g ≫ PSpace.str o n)).hom
  have hkV : IsUnit ((S.r * S.N : ℕ) : V) := by
    simpa using S.unit.map (Spec.preimage (ξ ≫ M.s)).hom

  have hPK : PolFib ρ.P.A ρ.P.L gd (spMap i ≫ x₀) :=
    (GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback (Sp S.R) (Sp S.R) ρ.P.A ρ.P.L ρ.P.A ρ.P.L (𝟙 _) (𝟙 _) ρ.P.isLB ρ.P.isLB (grpPullback_self' _)
      (ThetaAffineGlue.lbIso_pull_id ρ.P.isLB) gd Ω x₀).2 K i hPF
  have hθK := (GlobalTheory.T.principallyPolarisedFibre_exists_generator_stable (Sp S.R) ρ.P.A ρ.P.L ρ.P.isLB gd Ω x₀ hPF).2 θ hθ K i
  obtain ⟨pt, d, hd⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen gd m (n + 1) K (spMap i ≫ x₀)
    (SecAt.pull ρ.P.A ρ.P.L θ i) hm (hcast m hm.pos.ne') hn hPK
  obtain ⟨pt', d', hd'⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen gd (S.r * S.N)
    ((S.r * S.N) ^ (4 * gd)) K (spMap i ≫ x₀) (SecAt.pull ρ.P.A ρ.P.L θ i) hkodd (hcast _ (NeZero.ne _)) rfl hPK
  have hsym : ∀ j, io (emb (e j)) = symTup d j := he K i pt d hd
  obtain ⟨pt'', hd''⟩ := thList_pull_pull ρ.P.isLB (𝟙 (Sp S.R)) ρ.th₁ v i hd'
  have hT := GlobalTheory.T.thetaConstantList_realisedSystem_up_to_rootsOfUnity o' Ω S ρ K (i.comp v) _ pt'' d' hd''

  have h₁ : HasTh₂ ρ.P.A ρ.P.L ρ.rig m (S.r * S.N) (spMap i ≫ x₀) d d' := ⟨_, pt, pt', hθK, hd, hd'⟩
  obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl hLG
  obtain ⟨ρG, hρG, -⟩ := exists_rigidificationPullbackCompatibleIso hα hw ρ.P.isLB hLG ρ.rig_gen
  let xV : Sp K ⟶ Sp (ratHull S.R) := spMap io ≫ spMap emb ≫ spMap vH
  have hxV : spMap i ≫ x₀ = xV ≫ spMap (toRat S.R) := by
    simp only [xV, x₀, i, Category.comp_id, Category.assoc, spMap_comp_ring', ← hv, RingHom.comp_assoc]
  rw [hxV] at h₁
  have h₂ := (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen (Sp (ratHull S.R)) G (ρ.P.L.pull α) ρG
    (spMap (toRat S.R)) α hLG hρG hα (PolBaseChange.lbIso_refl hLG) m (S.r * S.N) (n + 1) _ K xV d d').2 h₁
  have h₃ := (GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian Xo.X Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig hU hUr (Sp (ratHull S.R)) G (ρ.P.L.pull α) ρG
    (u ≫ pullback.fst _ _) β hLG hρG hβ hL m (S.r * S.N) (n + 1) _ K xV d d').1 h₂
  let y : Sp (FractionRing V) ⟶ Xo.XF c := spMap emb ≫ spMap vH ≫ u
  have h₄ : HasTh₂ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (S.r * S.N) (spMap io ≫ y ≫ pullback.fst _ _) d d' := by
    have e₄ : spMap io ≫ y ≫ pullback.fst _ _ = xV ≫ u ≫ pullback.fst _ _ := by
      simp only [xV, y, Category.assoc]
    rw [e₄]
    exact h₃
  obtain ⟨a, ha, hPa, hPa'⟩ := GlobalTheory.T.thetaConstants_two_levels_same_scale_at_trait E H Dw l Xo c V hV y K io m (S.r * S.N) (n + 1) _ d d' hm hm3 hmV hkodd hk3
    hkV h₄
  have hP := GlobalTheory.T.primitive_families_thetaSymmetric_min_member_compare V K io (n + 1) _ ((S.r * S.N) ^ 2) S.Gam d d' a (fun j => emb (e j)) (fun b => emb (S.th b)) ha
    (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (NeZero.ne _))) hPa hPa' hsym hT.1 hT.2 j₀ ((map_ne_zero emb).2 hj₀)
    (fun j => by simpa [map_div₀] using hej j)
  refine ⟨fun b => by simpa [map_div₀, map_pow] using hP.1 b, ?_⟩
  obtain ⟨b, hb, hb'⟩ := hP.2
  exact ⟨b, fun h0 => hb (by simp [h0]), by simpa [map_div₀, map_pow] using hb'⟩

end GlobalTheory.UMin
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstants_projectively_integral_normalModels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp (ratHull S.R) ⟶ Xo.XF c), UOver Xo c ρ.P (toRat S.R) u → ∀ (M : RatModel o' Ω) (g : M.Z ⟶ PSpace o n), Geo.Tor.IsNormalScheme M.Z → M.pt ≫ g = spMap (ratHull S.R).val.toRingHom ≫ u ≫ f → M.HasDiv S.th := by
  atlas_forward_decl GlobalTheory.UMin.thetaInt_hasDiv
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem xF_charZero_residueField {X : Scheme.{0}} {K : Type} [Field K] [CharZero K] (s : X ⟶ Sp K) (x : X) :
    CharZero (X.residueField x) := by
  let φ : K →+* X.residueField x :=
    (X.residue x).hom.comp ((X.presheaf.germ ⊤ x trivial).hom.comp
      (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom))
  exact (RingHom.charZero_iff φ.injective).1 inferInstance

theorem xF_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) , Geo.Tor.IsNormalScheme (Xo.XF c) ∧ IsLocallyNoetherian (Xo.XF c) ∧ (∀ x : Xo.XF c, CharZero ((Xo.XF c).residueField x)) ∧ IsSeparated (pullback.snd _ _ : Xo.XF c ⟶ Sp c.F) ∧ LocallyOfFiniteType (pullback.snd _ _ : Xo.XF c ⟶ Sp c.F) ∧ QuasiCompact (pullback.snd _ _ : Xo.XF c ⟶ Sp c.F) := by
  intro E _ _ _ H Dw l Xo c
  obtain ⟨N, i, hi, hq, hc⟩ := Xo.qproj
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim _
  have : IsProper (PSpace.str (KA l) N) := isProper_str (KA l) N
  have : IsSeparated Xo.s := by rw [← hc]; infer_instance
  have : QuasiCompact Xo.s := by rw [← hc]; infer_instance
  have hsm : Smooth (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := inferInstance
  obtain ⟨-, hn, hl⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ hsm
  exact ⟨hn, hl, fun x => xF_charZero_residueField (pullback.snd _ _) x, inferInstance, inferInstance, inferInstance⟩

end GlobalTheory.UMin
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduliScheme_coefficientField_normal_noetherian_separated : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) , Geo.Tor.IsNormalScheme (Xo.XF c) ∧ IsLocallyNoetherian (Xo.XF c) ∧ (∀ x : Xo.XF c, CharZero ((Xo.XF c).residueField x)) ∧ IsSeparated (pullback.snd _ _ : Xo.XF c ⟶ Sp c.F) ∧ LocallyOfFiniteType (pullback.snd _ _ : Xo.XF c ⟶ Sp c.F) ∧ QuasiCompact (pullback.snd _ _ : Xo.XF c ⟶ Sp c.F) := by
  atlas_forward_decl GlobalTheory.UMin.xF_props
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaFin

theorem isFinite_fromNormalization_and_normal : ∀ (o F : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field F] [CharZero F] (b : o →+* F) (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp F) (f : X ⟶ PSpace o n) [QuasiCompact f] [QuasiSeparated f], Function.Injective b → (∀ x : F, ∃ a d : o, b d ≠ 0 ∧ x * b d = b a) → Geo.Tor.IsNormalScheme X → IsSeparated s → LocallyOfFiniteType s → QuasiCompact s → f ≫ PSpace.str o n = s ≫ spMap b → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.Finite {y : Sp K ⟶ X | y ≫ s = x ≫ s ∧ y ≫ f = x ≫ f}) → IsFinite f.fromNormalization ∧ Geo.Tor.IsNormalScheme f.normalization := by
  intro o F _ _ _ _ _ _ b n X s f _ _ hinj hfrac hX _ _ _ hw _
  letI : Algebra o F := b.toAlgebra
  haveI : IsFractionRing o F := by
    refine ⟨fun d => ?_, fun x => ?_, fun {x y} h => ?_⟩
    · refine IsUnit.mk0 _ ?_
      change b d ≠ 0
      exact (map_ne_zero_iff b hinj).mpr (nonZeroDivisors.ne_zero d.2)
    · obtain ⟨a, d, hd, e⟩ := hfrac x
      refine ⟨⟨a, ⟨d, mem_nonZeroDivisors_of_ne_zero fun h0 => hd (by rw [h0, map_zero])⟩⟩, e⟩
    · exact ⟨1, by simpa using hinj h⟩
  haveI : CharZero o := ⟨fun m k h => by
    have := congrArg b h
    simp only [map_natCast] at this
    exact Nat.cast_injective this⟩
  haveI : IsDedekindDomain (CommRingCat.of o) := ‹IsDedekindDomain o›
  haveI : CharZero (CommRingCat.of o) := ‹CharZero o›
  haveI hN : GlobalTheory.IsNormalScheme X := GlobalTheory.IsNormalScheme.of_pred hX
  haveI : IsReduced X := isReduced_of_isReduced_stalk X
  haveI : IsProper (PSpace.str o n) := isProper_str o n
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  refine ⟨GlobalTheory.isFinite_fromNormalization_of_over_fractionRing (o := CommRingCat.of o) f
    (PSpace.str o n) F s hw, ?_⟩
  exact GlobalTheory.IsNormalScheme.pred _

end GlobalTheory.ThetaFin
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinite_normal_normalisation_projectiveSpace_arith : ∀ (o F : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field F] [CharZero F] (b : o →+* F) (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp F) (f : X ⟶ PSpace o n) [QuasiCompact f] [QuasiSeparated f], Function.Injective b → (∀ x : F, ∃ a d : o, b d ≠ 0 ∧ x * b d = b a) → Geo.Tor.IsNormalScheme X → IsSeparated s → LocallyOfFiniteType s → QuasiCompact s → f ≫ PSpace.str o n = s ≫ spMap b → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.Finite {y : Sp K ⟶ X | y ≫ s = x ≫ s ∧ y ≫ f = x ≫ f}) → IsFinite f.fromNormalization ∧ Geo.Tor.IsNormalScheme f.normalization := by
  atlas_forward_decl GlobalTheory.ThetaFin.isFinite_fromNormalization_and_normal
end

section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GeomFibre

theorem finite_of_finite_sections {K : Type} [Field K] [IsAlgClosed K] {P : Scheme.{0}}
    (g : P ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType g]
    (h : Finite {p : Spec (CommRingCat.of K) ⟶ P // p ≫ g = 𝟙 _}) : Finite P := by
  have := LocallyOfFiniteType.jacobsonSpace g
  have h1 : (closedPoints P).Finite :=
    Set.finite_coe_iff.mp ((pointEquivClosedPoint g).finite_iff.mp h)
  have hc : IsClosed (closedPoints P) := by
    rw [← Set.biUnion_of_singleton (closedPoints P)]
    exact h1.isClosed_biUnion fun x hx ↦ hx
  have h2 := JacobsonSpace.closure_inter_closedPoints (isClosed_univ (X := P))
  rw [Set.univ_inter, hc.closure_eq] at h2
  exact Set.finite_univ_iff.mp (h2 ▸ h1)

theorem locallyQuasiFinite_of_finite_geometric_fibres :
    ∀ (X Y : Scheme.{0}) (f : X ⟶ Y), LocallyOfFiniteType f →
      (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X),
        Set.Finite {y : Sp K ⟶ X | y ≫ f = x ≫ f}) → LocallyQuasiFinite f := by
  intro X Y f _ H
  refine LocallyQuasiFinite.of_finite_preimage_singleton f fun y ↦ ?_
  rcases (f ⁻¹' {y}).eq_empty_or_nonempty with h | ⟨x₀, hx₀⟩
  · rw [h]; exact Set.finite_empty
  obtain rfl : f x₀ = y := hx₀
  let K := AlgebraicClosure (X.residueField x₀)
  let x : Sp K ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x₀) K)) ≫ X.fromSpecResidueField x₀
  have hx : ∀ z, x z = x₀ := fun z ↦ by
    simp only [x, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  have hfin : Finite ↥(pullback f (x ≫ f)) := by
    refine finite_of_finite_sections (pullback.snd f (x ≫ f)) ?_
    have := (H K x).to_subtype
    refine Finite.of_injective (β := {y : Sp K ⟶ X | y ≫ f = x ≫ f})
      (fun p ↦ ⟨p.1 ≫ pullback.fst f (x ≫ f), ?_⟩) fun a b hab ↦ ?_
    · change (p.1 ≫ _) ≫ f = x ≫ f
      rw [Category.assoc, pullback.condition, reassoc_of% p.2]
    · exact Subtype.ext (pullback.hom_ext (congrArg Subtype.val hab) (a.2.trans b.2.symm))
  refine (Set.finite_range (pullback.fst f (x ≫ f))).subset fun z hz ↦ ?_
  rw [Scheme.Pullback.range_fst]
  exact ⟨IsLocalRing.closedPoint K,
    ((Scheme.Hom.comp_apply x f _).trans (congrArg f (hx _))).trans hz.symm⟩

end GlobalTheory.GeomFibre
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.SecCompact

theorem exists_openImmersion_genericFibre (F : Type) [Field F] (o : Type) [CommRing o] [Algebra o F]
    [IsFractionRing o F] [Algebra.FiniteType ℤ o] (m : ℕ) (X : Scheme.{0}) (sX : X ⟶ Sp F) [IsReduced X]
    [IsSeparated sX] [LocallyOfFiniteType sX] [QuasiCompact sX] (f : X ⟶ PSpace o m) [QuasiCompact f]
    [QuasiSeparated f] (hf : f ≫ PSpace.str o m = sX ≫ spMap (algebraMap o F))
    (hfib : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X),
      Set.Finite {y : Sp K ⟶ X | y ≫ sX = x ≫ sX ∧ y ≫ f = x ≫ f}) :
    IsFinite f.fromNormalization ∧
      ∃ iF : X ⟶ pullback (f.fromNormalization ≫ PSpace.str o m) (spMap (algebraMap o F)),
        IsOpenImmersion iF ∧ Dense (Set.range iF) ∧ iF ≫ pullback.snd _ _ = sX ∧
          iF ≫ pullback.fst _ _ = f.toNormalization := by
  haveI := isProper_str o m
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI := IsPreimmersion.of_isLocalization (R := o) (S := F) (nonZeroDivisors o)
  haveI : Algebra.FiniteType ℤ (CommRingCat.of o) := ‹Algebra.FiniteType ℤ o›
  refine ⟨GlobalTheory.NormBlowupInt.isFinite_fromNormalization_int_of_isReduced (o := CommRingCat.of o) f
    (PSpace.str o m) fun x _ => ?_, ?_⟩
  · have h1 : ((f ≫ PSpace.str o m).stalkMap x).hom.EssFiniteType := by
      rw [hf, Scheme.Hom.stalkMap_comp]
      exact .comp (RingHom.FiniteType.of_surjective _
        (Scheme.Hom.stalkMap_surjective _ _)).essFiniteType (LocallyOfFiniteType.stalkMap sX x)
    rw [Scheme.Hom.stalkMap_comp] at h1
    have h2 : (f.stalkMap x).hom.EssFiniteType := .of_comp _ h1
    exact h2.residueFieldMap
  have hb := IsPullback.of_hasPullback (PSpace.str o m) (spMap (algebraMap o F))
  let f' : X ⟶ pullback (PSpace.str o m) (spMap (algebraMap o F)) := pullback.lift f sX hf
  have e₁ : f' ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  have e₂ : f' ≫ pullback.snd _ _ = sX := pullback.lift_snd _ _ _
  haveI : LocallyOfFiniteType (f' ≫ pullback.snd _ _) := by rw [e₂]; infer_instance
  haveI : LocallyOfFiniteType f' := locallyOfFiniteType_of_comp f' (pullback.snd _ _)
  haveI : QuasiCompact (f' ≫ pullback.snd _ _) := by rw [e₂]; infer_instance
  haveI : QuasiCompact f' := QuasiCompact.of_comp f' (pullback.snd _ _)
  haveI : IsSeparated (f' ≫ pullback.snd _ _) := by rw [e₂]; infer_instance
  haveI : IsSeparated f' := IsSeparated.of_comp f' (pullback.snd _ _)
  haveI : LocallyQuasiFinite f' := by
    refine GlobalTheory.GeomFibre.locallyQuasiFinite_of_finite_geometric_fibres X _ f' inferInstance fun K _ _ x => ?_
    refine (hfib K x).subset fun y (hy : y ≫ f' = x ≫ f') => ⟨?_, ?_⟩
    · rw [← e₂, ← Category.assoc, hy, Category.assoc]
    · rw [← e₁, ← Category.assoc, hy, Category.assoc]
  obtain ⟨hoi, -, hdom⟩ :=
    GlobalTheory.isOpenImmersion_lift_toNormalization_of_isLocalization (nonZeroDivisors o) hb f' f e₁.symm
  refine ⟨pullback.lift f.toNormalization f' (by simp [e₁]) ≫
    (pullbackRightPullbackFstIso (PSpace.str o m) (spMap (algebraMap o F)) f.fromNormalization).hom,
    inferInstance, (Scheme.Hom.denseRange _), ?_, ?_⟩
  · rw [Category.assoc, pullbackRightPullbackFstIso_hom_snd, pullback.lift_snd_assoc, e₂]
  · rw [Category.assoc, pullbackRightPullbackFstIso_hom_fst, pullback.lift_fst]

end GlobalTheory.SecCompact
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem isOpenImmersion_dense_genericFibre_normalization : ∀ (o F : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field F] [CharZero F] (b : o →+* F) (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp F) (f : X ⟶ PSpace o n) [QuasiCompact f] [QuasiSeparated f], Function.Injective b → (∀ x : F, ∃ a d : o, b d ≠ 0 ∧ x * b d = b a) → Geo.Tor.IsNormalScheme X → IsSeparated s → LocallyOfFiniteType s → QuasiCompact s → f ≫ PSpace.str o n = s ≫ spMap b → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.Finite {y : Sp K ⟶ X | y ≫ s = x ≫ s ∧ y ≫ f = x ≫ f}) → ∀ iF : X ⟶ pullback (f.fromNormalization ≫ PSpace.str o n) (spMap b), iF ≫ pullback.fst _ _ = f.toNormalization → iF ≫ pullback.snd _ _ = s → IsOpenImmersion iF ∧ Dense (Set.range iF) := by
  intro o F _ _ _ _ _ _ b n X s f _ _ hb hfrac hN _ _ _ hfs hfib iF h1 h2
  letI : Algebra o F := b.toAlgebra
  haveI : FaithfulSMul o F := (faithfulSMul_iff_algebraMap_injective _ _).mpr hb
  haveI : IsFractionRing o F := IsFractionRing.of_field o F fun x => by
    obtain ⟨a, d, hd, e⟩ := hfrac x
    exact ⟨a, d, (eq_div_iff hd).mpr e⟩
  haveI : GlobalTheory.IsNormalScheme X := GlobalTheory.IsNormalScheme.of_pred hN
  haveI : IsReduced X := inferInstance
  obtain ⟨-, i₀, hoi, hd, hsnd, hfst⟩ :=
    GlobalTheory.SecCompact.exists_openImmersion_genericFibre F o n X s f hfs hfib
  have e : iF = i₀ := by
    apply pullback.hom_ext
    · rw [h1, hfst]
    · rw [h2, hsnd]
  subst e
  exact ⟨hoi, hd⟩

end GlobalTheory.UMin
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpenImmersion_dense_genericFibre_normalisation : ∀ (o F : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field F] [CharZero F] (b : o →+* F) (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp F) (f : X ⟶ PSpace o n) [QuasiCompact f] [QuasiSeparated f], Function.Injective b → (∀ x : F, ∃ a d : o, b d ≠ 0 ∧ x * b d = b a) → Geo.Tor.IsNormalScheme X → IsSeparated s → LocallyOfFiniteType s → QuasiCompact s → f ≫ PSpace.str o n = s ≫ spMap b → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.Finite {y : Sp K ⟶ X | y ≫ s = x ≫ s ∧ y ≫ f = x ≫ f}) → ∀ iF : X ⟶ pullback (f.fromNormalization ≫ PSpace.str o n) (spMap b), iF ≫ pullback.fst _ _ = f.toNormalization → iF ≫ pullback.snd _ _ = s → IsOpenImmersion iF ∧ Dense (Set.range iF) := by
  atlas_forward_decl GlobalTheory.UMin.isOpenImmersion_dense_genericFibre_normalization
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.RetractionLiftSection

theorem exists_retraction {R K A : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing A] (φ : R →+* A) (hφ : φ.IsIntegral) (ψ : A →+* K)
    (h : ψ.comp φ = algebraMap R K) :
    ∃ σ : A →+* R, (algebraMap R K).comp σ = ψ ∧ σ.comp φ = RingHom.id R := by
  have inj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have key : ∀ a : A, ∃ r : R, algebraMap R K r = ψ a := by
    intro a
    obtain ⟨f, hf, hfa⟩ := hφ a
    have hi : IsIntegral R (ψ a) := by
      refine ⟨f, hf, ?_⟩
      rw [← h, ← Polynomial.hom_eval₂, hfa, map_zero]
    exact IsIntegrallyClosed.algebraMap_eq_of_integral hi
  choose s hs using key
  let σ : A →+* R :=
    { toFun := s
      map_one' := inj (by rw [hs, map_one, map_one])
      map_mul' := fun a b => inj (by rw [map_mul, hs, hs, hs, map_mul])
      map_zero' := inj (by rw [hs, map_zero, map_zero])
      map_add' := fun a b => inj (by rw [map_add, hs, hs, hs, map_add]) }
  refine ⟨σ, RingHom.ext hs, RingHom.ext fun r => inj ?_⟩
  exact (hs (φ r)).trans (RingHom.congr_fun h r)

theorem exists_section {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] {W : Scheme.{0}} (q : W ⟶ Spec (CommRingCat.of R)) [IsFinite q]
    (y : Spec (CommRingCat.of K) ⟶ W) (h : y ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ s : Spec (CommRingCat.of R) ⟶ W, Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s = y ∧ s ≫ q = 𝟙 _ := by
  haveI : IsAffine W := isAffine_of_isAffineHom q
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (W.isoSpec.inv ≫ q)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (y ≫ W.isoSpec.hom)
  have hfin : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hint : φ.hom.IsIntegral := ((IsFinite.SpecMap_iff φ).1 hfin).to_isIntegral
  have hc : φ ≫ ψ = CommRingCat.ofHom (algebraMap R K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc, h]
  obtain ⟨σ, h₁, h₂⟩ := exists_retraction (R := R) (K := K) φ.hom hint ψ.hom (congrArg CommRingCat.Hom.hom hc)
  refine ⟨Spec.map (CommRingCat.ofHom σ) ≫ W.isoSpec.inv, ?_, ?_⟩
  · have e : CommRingCat.ofHom σ ≫ CommRingCat.ofHom (algebraMap R K) = ψ := CommRingCat.hom_ext h₁
    rw [← Category.assoc, ← Spec.map_comp]
    erw [e]
    rw [hψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · have e : φ ≫ CommRingCat.ofHom σ = 𝟙 _ := CommRingCat.hom_ext h₂
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    erw [e]
    rw [Spec.map_id]

theorem exists_lift {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] {Z P : Scheme.{0}} (p : Z ⟶ P) [IsFinite p] (x : Spec (CommRingCat.of R) ⟶ P)
    (y : Spec (CommRingCat.of K) ⟶ Z) (h : y ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ x) :
    ∃ ξ : Spec (CommRingCat.of R) ⟶ Z, Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ ξ = y ∧ ξ ≫ p = x := by
  obtain ⟨s, h₁, h₂⟩ := exists_section (K := K) (pullback.snd p x) (pullback.lift y _ h) (pullback.lift_snd _ _ _)
  refine ⟨s ≫ pullback.fst p x, ?_, ?_⟩
  · rw [← Category.assoc, h₁, pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, h₂, Category.id_comp]

theorem lift_finite : ∀ (R : Type) [inst : CommRing R] [IsDomain R] [IsIntegrallyClosed R] (Z P : AlgebraicGeometry.Scheme) (p : Z ⟶ P) (ξ₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ P) (y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (FractionRing R) ⟶ Z), AlgebraicGeometry.IsFinite p → CategoryTheory.CategoryStruct.comp y p = CategoryTheory.CategoryStruct.comp (ReciprocityTheory.ChartRestriction.G.Out.jK R) ξ₀ → ∃ (ξ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Z), CategoryTheory.CategoryStruct.comp (ReciprocityTheory.ChartRestriction.G.Out.jK R) ξ = y ∧ CategoryTheory.CategoryStruct.comp ξ p = ξ₀ :=
  fun R _ _ _ _ _ p x y _ h => exists_lift (R := R) (K := FractionRing R) p x y h

end GlobalTheory.RetractionLiftSection
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory

theorem finite_lift_fractionField (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (Z P : Scheme.{0}) (p : Z ⟶ P) (ξ₀ : Sp R ⟶ P) (y : Sp (FractionRing R) ⟶ Z)
    (hp : IsFinite p) (hy : y ≫ p = jK R ≫ ξ₀) :
    ∃ ξ : Sp R ⟶ Z, jK R ≫ ξ = y ∧ ξ ≫ p = ξ₀ := by
  first
  | exact @_root_.GlobalTheory.RetractionLiftSection.lift_finite
  | exact _root_.GlobalTheory.RetractionLiftSection.lift_finite
  | (apply _root_.GlobalTheory.RetractionLiftSection.lift_finite <;> assumption)
  | (intros; apply _root_.GlobalTheory.RetractionLiftSection.lift_finite <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RetractionLiftSection.lift_finite <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RetractionLiftSection.lift_finite ..)

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_morphism_valuative_lifting_normal_domain : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (Z P : Scheme.{0}) (p : Z ⟶ P) (ξ₀ : Sp R ⟶ P) (y : Sp (FractionRing R) ⟶ Z), IsFinite p → y ≫ p = jK R ≫ ξ₀ → ∃ ξ : Sp R ⟶ Z, jK R ≫ ξ = y ∧ ξ ≫ p = ξ₀ := by
  atlas_forward_decl GlobalTheory.finite_lift_fractionField
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMinTop

theorem exists_baseRing_away (F : IntermediateField ℚ ℂ) (hF : FiniteDimensional ℚ F) (N : ℤ) (hN : N ≠ 0) :
    ∃ (o : Type) (_ : CommRing o) (b : o →+* F), Function.Injective b ∧ IsDedekindDomain o ∧ Algebra.FiniteType ℤ o ∧
      IsUnit (N : o) ∧ ∀ x : F, ∃ a d : o, b d ≠ 0 ∧ x * b d = b a := by
  haveI : NumberField F := ⟨⟩
  have h3 : (N : 𝓞 F) ≠ 0 := by exact_mod_cast hN
  have hM : Submonoid.powers (N : 𝓞 F) ≤ nonZeroDivisors (𝓞 F) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors h3
  have hg : ∀ y : Submonoid.powers (N : 𝓞 F), IsUnit (algebraMap (𝓞 F) F y) := fun y =>
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2
      (nonZeroDivisors.ne_zero (hM y.2)))
  let o := Localization.Away (N : 𝓞 F)
  let b : o →+* F := IsLocalization.lift (M := Submonoid.powers (N : 𝓞 F)) hg
  have hb : ∀ a : 𝓞 F, b (algebraMap (𝓞 F) o a) = algebraMap (𝓞 F) F a := fun a =>
    IsLocalization.lift_eq (M := Submonoid.powers (N : 𝓞 F)) hg a
  haveI : IsDomain o := IsLocalization.isDomain_localization hM
  refine ⟨o, inferInstance, b, ?_, IsLocalization.isDedekindDomain (𝓞 F) hM o, ?_, ?_, ?_⟩
  · rw [IsLocalization.lift_injective_iff]
    intro x y
    rw [(IsLocalization.injective o hM).eq_iff, (IsFractionRing.injective (𝓞 F) F).eq_iff]
  · have : Algebra.FiniteType (𝓞 F) o :=
      IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (N : 𝓞 F)) o
    exact @Algebra.FiniteType.trans ℤ (𝓞 F) o _ _ _ _ (Ring.toIntAlgebra o) _ _ inferInstance this
  · simpa only [map_intCast] using IsLocalization.Away.algebraMap_isUnit (S := o) (N : 𝓞 F)
  · intro x
    obtain ⟨⟨a, d⟩, h⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 F)) x
    refine ⟨algebraMap (𝓞 F) o a, algebraMap (𝓞 F) o d, ?_, ?_⟩
    · rw [hb]
      exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 (nonZeroDivisors.ne_zero d.2)
    · rw [hb, hb]; exact h

theorem integral_normal_model_dense : ∀ (o F : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field F] [CharZero F] (b : o →+* F) (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp F) (f : X ⟶ PSpace o n), Function.Injective b → (∀ x : F, ∃ a d : o, b d ≠ 0 ∧ x * b d = b a) → Geo.Tor.IsNormalScheme X → IsSeparated s → LocallyOfFiniteType s → QuasiCompact s → f ≫ PSpace.str o n = s ≫ spMap b → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.Finite {y : Sp K ⟶ X | y ≫ s = x ≫ s ∧ y ≫ f = x ≫ f}) → ∃ (Z : Scheme.{0}) (p : Z ⟶ PSpace o n) (iF : X ⟶ pullback (p ≫ PSpace.str o n) (spMap b)), IsFinite p ∧ Geo.Tor.IsNormalScheme Z ∧ IsOpenImmersion iF ∧ Dense (Set.range iF) ∧ iF ≫ pullback.snd _ _ = s ∧ iF ≫ pullback.fst _ _ ≫ p = f ∧ Dense (Set.range (iF ≫ pullback.fst _ _)) := by
  intro o F _ _ _ _ _ _ b n X s f hb hfr hX hsep hlft hqc hcomm hfin
  haveI : IsProper (PSpace.str o n) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str o n
  haveI : QuasiCompact (f ≫ PSpace.str o n) := by rw [hcomm]; infer_instance
  haveI : QuasiSeparated (f ≫ PSpace.str o n) := by rw [hcomm]; infer_instance
  haveI : QuasiCompact f := QuasiCompact.of_comp f (PSpace.str o n)
  haveI : QuasiSeparated f := QuasiSeparated.of_comp f (PSpace.str o n)
  have hw : f.toNormalization ≫ (f.fromNormalization ≫ PSpace.str o n) = s ≫ spMap b := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hcomm]
  obtain ⟨h1, h2⟩ := GlobalTheory.T.isFinite_normal_normalisation_projectiveSpace_arith o F b n X s f hb hfr hX hsep hlft hqc hcomm hfin
  obtain ⟨h3, h4⟩ := GlobalTheory.T.isOpenImmersion_dense_genericFibre_normalisation o F b n X s f hb hfr hX hsep hlft hqc hcomm hfin
    (pullback.lift _ _ hw) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  refine ⟨f.normalization, f.fromNormalization, pullback.lift _ _ hw, h1, h2, h3, h4,
    pullback.lift_snd _ _ _, ?_, ?_⟩
  · rw [pullback.lift_fst_assoc, Scheme.Hom.toNormalization_fromNormalization]
  · rw [pullback.lift_fst]
    exact f.toNormalization.denseRange

end GlobalTheory.UMinTop

namespace GlobalTheory

set_option maxHeartbeats 1000000 in

theorem umin_theta_compactification_exists : UMinSt := by
  have h_dim := @GlobalTheory.UMin.polFib_univ
  have h_xf := GlobalTheory.T.moduliScheme_coefficientField_normal_noetherian_separated
  have h_map_gen := GlobalTheory.T.thetaMap_abelianScheme_normal_charZero_base
  have h_qf := GlobalTheory.T.thetaMap_finite_geometricFibres_of_large_level
  have h_zb := GlobalTheory.UMinTop.integral_normal_model_dense
  have h_zb_amp := @GlobalTheory.FiniteOverPSpace.isProjOver_and_isAmpleLB
  have h_zb_lift := GlobalTheory.T.finite_morphism_valuative_lifting_normal_domain
  have h_ext_P := GlobalTheory.T.uniformisedPoint_extends_along_thetaMap
  have h_thint_P := GlobalTheory.T.thetaConstants_projectively_integral_normalModels
  have h_om_P := GlobalTheory.T.theta_map_pull_O1_power
  intro E _ _ _ H Dw _ l Xo c
  have hM'0 : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have hd0 : H.d ≠ 0 := H.d_prime.ne_zero
  have hD0 : NumberField.discr E ≠ 0 := NumberField.discr_ne_zero E
  obtain ⟨o, _, b, hb, hded, hft, hNu, hfr⟩ := GlobalTheory.UMinTop.exists_baseRing_away c.F c.fin
    (3 * (l.M' : ℤ) * (H.d : ℤ) * NumberField.discr E) (by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_) hD0 <;> exact_mod_cast ‹_›)
  have hNu' : IsUnit ((3 : o) * (l.M' : o) * (H.d : o) * ((NumberField.discr E : ℤ) : o)) := by
    simpa [Int.cast_mul] using hNu
  have h3 : IsUnit (3 : o) := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hNu'))
  have hM'u : IsUnit (l.M' : o) := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hNu'))
  have hdu : IsUnit (H.d : o) := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hNu')
  have hDu : IsUnit ((NumberField.discr E : ℤ) : o) := isUnit_of_mul_isUnit_right hNu'
  haveI := hded
  haveI := hft
  obtain ⟨j, hj⟩ : ∃ j : ℕ, 81 ^ (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)).factorial < 3 ^ j * 81 := by
    refine ⟨81 ^ (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)).factorial, ?_⟩
    exact lt_of_lt_of_le (Nat.lt_pow_self (by norm_num : 1 < 3)) (Nat.le_mul_of_pos_right _ (by norm_num))
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n + 1 = (3 ^ j * 81) ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) :=
    ⟨_, Nat.succ_pred_eq_of_pos (by positivity)⟩
  have hodd : Odd (3 ^ j * 81) := (Odd.pow (by decide)).mul (by decide)
  have h3m : 3 ≤ 3 ^ j * 81 := le_trans (by norm_num) (Nat.le_mul_of_pos_left 81 (by positivity))
  have hu : IsUnit ((3 ^ j * 81 : ℕ) : o) := by
    have : ((3 ^ j * 81 : ℕ) : o) = 3 ^ (j + 4) := by push_cast; ring
    rw [this]; exact h3.pow _
  obtain ⟨hN, hno, hch, hsep, hlft, hqc⟩ := h_xf E H Dw l Xo c
  obtain ⟨f, hf, hT⟩ := h_map_gen Xo.X Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig Xo.univ.t.PP.isLB Xo.univ.t.PP.rigGen
    _ _ n o (Xo.XF c) (pullback.snd _ _ ≫ spMap b) (pullback.fst _ _) hodd h3m hu hn hN hno hch
    (fun R _ x => h_dim E H Dw l Xo c R _)
  obtain ⟨Z, p, iF, hp, hZ, hio, hd, hs, hif, hdense⟩ := h_zb o c.F b n (Xo.XF c) (pullback.snd _ _) f hb hfr hN hsep hlft hqc hf
    (h_qf E H Dw l Xo c o j n f hj hn hT)
  have hD : 1 ≤ (n + 1).factorial := Nat.factorial_pos _
  obtain ⟨hpr, hlb, ham, hpull⟩ := h_zb_amp o n (8 * (n + 1).factorial) Z p (by omega) hp
  refine ⟨{ o := o, b := b, inj := hb, frac := ?_, ded := hded, ft := hft, unit_level := hM'u, unit_d := hdu,
            unit_discr := hDu, Z := Z, z := p ≫ PSpace.str o n, proj := hpr, normal := GlobalTheory.IsNormalScheme.of_pred hZ,
            iF := iF, iF_open := hio, iF_dense := hd, iF_over := hs, i_dense := hdense, OZ := _, OZ_lb := hlb, OZ_ample := ham,
            N := 4 * (n + 1).factorial * (n + 1).factorial, N_pos := Nat.mul_pos (by omega) hD,
            omega := ?_, ext := ?_, thetaInt := ?_ }⟩
  · intro x
    obtain ⟨a, d, hbd, e⟩ := hfr x
    exact ⟨a, d, eq_div_of_mul_eq hbd e⟩
  · intro Y g hg hY
    have e₂ := h_om_P E H Dw l Xo c o _ n f hodd h3m hu hn hT Y ((g ≫ pullback.fst _ _) ≫ p)
      (by rw [Category.assoc, reassoc_of% hg, hif]) hY
    exact LBIso.trans (pull_isLB hlb _)
      (isLB_lbPow (pull_isLB (ProjSpace.O1_isLB o n) _) _) (isLB_lbPow hY _) (hpull _ (g ≫ pullback.fst _ _)) e₂
  · intro R _ _ _ hR t ht y hy σ hσ
    obtain ⟨ξ₀, h₁, h₂⟩ := h_ext_P E H Dw l Xo c o _ n f hodd h3m hu hn hT b hf R hR t ht y hy σ hσ
    haveI := hR.1.2.2.1
    obtain ⟨ξ, h₃, h₄⟩ := h_zb_lift R Z _ p ξ₀ (y ≫ iF ≫ pullback.fst _ _) hp (by simp only [Category.assoc, hif, h₁])
    exact ⟨ξ, h₃, by rw [reassoc_of% h₄, h₂]⟩
  · intro o' Ω _ _ _ _ S ρ u hu' _ M π hM hπ
    exact h_thint_P E H Dw l Xo c o _ n f hodd h3m hu hn hT o' Ω S ρ u hu' M (π ≫ p) (@GlobalTheory.IsNormalScheme.pred _ hM)
      (by rw [reassoc_of% hπ]; simp only [Category.assoc, hif])

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_integral_compactification_exists_via_theta : UMinSt := by
  atlas_forward_decl GlobalTheory.umin_theta_compactification_exists
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem uMinSt_holds : UMinSt := GlobalTheory.T.unitary_integral_compactification_exists_via_theta

end GlobalTheory.UPoinc
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_integral_compactifications_exist : UMinSt := by
  atlas_forward_decl GlobalTheory.UPoinc.uMinSt_holds
end
