import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CurveSemiAbelianConjecture
import Development.AutomorphicSpectrum.Statements.GeometryStatements.SeparableFormGroupElementFixesUniquePositiveLine
import Development.WeilBound.CoreStatements.HodgeTatePoints.CiField
import BuildAid.ForwardExisting
import Development.WeilBound.CoreStatements.HodgeTatePoints.CiCurveIn
import Development.WeilBound.CoreStatements.HodgeTatePoints.CiEigVal
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NefThresholdGapCondition
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeIsMaximalOfIsFractionRing
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LengthFormulaSumValuations
import Development.WeilBound.CoreStatements.HodgeTatePoints.CiGrDeg
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FunctionFieldCurveExists
import Development.WeilBound.CoreStatements.HodgeTatePoints.CiIsDeg
import Development.WeilBound.CoreStatements.HodgeTatePoints.ChIsDeg
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SplitCharactersUnramified
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceDecompositionInternal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteProjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeStableUnderAction
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubAndQuotientBundles
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeInvariantLinearEquiv
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenFlagSlopeBound
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
import Development.WeilBound.CoreStatements.HodgeTatePoints.FamilyEx
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FamilyGivesConjugateLieDataStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermLieBasis

section
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Crv.Field

theorem curve_field : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (W : Ideal (MRing J)) (p : ℕ) [Fact p.Prime], IsMultiProjPrime W → charOf W = p → ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card B : ℕ) : WithBot ℕ∞) → ∃ (K : Type) (_ : Field K) (_ : Algebra (ZMod p) K) (_ : GroundTheory.FunctionField.IsFunctionField (ZMod p) K) (w : (Σ k, J k) → K), mCoordIdeal w = W ∧ Birational w ∧ ∀ k, ∃ c, w ⟨k, c⟩ ≠ 0 :=
  PositivityTheory.HtPt.Ci.curve_field

end GlobalTheory.CompanionTheory.Ar.Crv.Field
end

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.function_field_model_exists : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (W : Ideal (MRing J)) (p : ℕ) [Fact p.Prime], IsMultiProjPrime W → charOf W = p → ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card B : ℕ) : WithBot ℕ∞) → ∃ (K : Type) (_ : Field K) (_ : Algebra (ZMod p) K) (_ : GroundTheory.FunctionField.IsFunctionField (ZMod p) K) (w : (Σ k, J k) → K), mCoordIdeal w = W ∧ Birational w ∧ ∀ k, ∃ c, w ⟨k, c⟩ ≠ 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Crv.Field.curve_field
end

section
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.curve_through_coordinates : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (segre y) → ∀ (K : Type) [Field K] (C : ACurve K) (w : (Σ k, J k) → K), mCoordIdeal y ≤ mCoordIdeal w → (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → ∃ (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)), CoordsAt ξ y z w ∧ ∀ p : ℕ, (p : K) = 0 → InFibre ξ p ⟨centre z, h₀⟩ ∧ ∀ i, InFibre ξ p ⟨centre (Y.x i), h i⟩ := by
  first | exact @PositivityTheory.HtPt.Ci.curve_in_cpt | exact PositivityTheory.HtPt.Ci.curve_in_cpt
end

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_through_coordinates : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (segre y) → ∀ (K : Type) [Field K] (C : ACurve K) (w : (Σ k, J k) → K), mCoordIdeal y ≤ mCoordIdeal w → (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → ∃ (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)), CoordsAt ξ y z w ∧ ∀ p : ℕ, (p : K) = 0 → InFibre ξ p ⟨centre z, h₀⟩ ∧ ∀ i, InFibre ξ p ⟨centre (Y.x i), h i⟩ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.curve_through_coordinates
end

section
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.EigVal

theorem values_eigen_sheaves : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (k K : Type) [Field k] [Field K] [Algebra k K] (z : Spec (CommRingCat.of K) ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (Vz : Type) [AddCommGroup Vz] [Module K Vz] (Mz : LieModel G z Vz) (h₀ : genPt ξ ⤳ centre z) (O S : Type) [CommRing O] [Fintype S] (act : O → (G ⟶ G)) (r : O →+* Module.End Ω V) (rz : O →+* Module.End K Vz) (σ : S → (O →+* Ω)) (χ : S → (O →+* k)), IsCptGen ξ → Smooth G.hom → (∀ a, IsMonHom (act a)) → M.IsActOf act r → Mz.IsActOf act rz → IsSplit χ → (∀ s a, ValAt ξ z (σ s a) (algebraMap k K (χ s a))) → M.lat ⟨centre z, h₀⟩ = ⨆ s, M.eigLat r (σ s) ⟨centre z, h₀⟩ → ∀ s, Submodule.span K {v | ∃ e ∈ M.eigLat r (σ s) ⟨centre z, h₀⟩, M.ValAt z e (Mz.pt v)} = eigSp rz ((algebraMap k K).comp (χ s)) :=
  @PositivityTheory.HtPt.Ci.eig_val

end GlobalTheory.CompanionTheory.Ar.EigVal
end

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_lie_eigen_decomposition : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (k K : Type) [Field k] [Field K] [Algebra k K] (z : Spec (CommRingCat.of K) ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (Vz : Type) [AddCommGroup Vz] [Module K Vz] (Mz : LieModel G z Vz) (h₀ : genPt ξ ⤳ centre z) (O S : Type) [CommRing O] [Fintype S] (act : O → (G ⟶ G)) (r : O →+* Module.End Ω V) (rz : O →+* Module.End K Vz) (σ : S → (O →+* Ω)) (χ : S → (O →+* k)), IsCptGen ξ → Smooth G.hom → (∀ a, IsMonHom (act a)) → M.IsActOf act r → Mz.IsActOf act rz → IsSplit χ → (∀ s a, ValAt ξ z (σ s a) (algebraMap k K (χ s a))) → M.lat ⟨centre z, h₀⟩ = ⨆ s, M.eigLat r (σ s) ⟨centre z, h₀⟩ → ∀ s, Submodule.span K {v | ∃ e ∈ M.eigLat r (σ s) ⟨centre z, h₀⟩, M.ValAt z e (Mz.pt v)} = eigSp rz ((algebraMap k K).comp (χ s)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.EigVal.values_eigen_sheaves
end

section
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoDeg

open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointChart (chartMono_notMem)
open GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionsNonzero (chartMono isMultiHomog_chartMono aeval_chartMono)
open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds (homog_X mem_locRing_iff div_mem_locRing fracHom fracHom_eq_zero_iff isUnit_iff)

theorem aeval_ratio_mul_chartMono {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    (φ : MRing J →+* Ω) (c : ∀ k, J k) (hc : ∀ k, φ (X ⟨k, c k⟩) ≠ 0) (S : Subring Ω) (x : (Σ k, J k) → S)
    (hx : ∀ q, (x q : Ω) = φ (X q) / φ (X ⟨q.1, c q.1⟩)) {g : MRing J} {e : B → ℕ} (hg : IsMultiHomog g e) :
    ((aeval x g : S) : Ω) * φ (chartMono c e) = φ g := by
  classical
  let ψ : MRing J →+* Ω := S.subtype.comp (aeval x : MRing J →ₐ[ℤ] S).toRingHom
  have hψX : ∀ q, ψ (X q) = φ (X q) / φ (X ⟨q.1, c q.1⟩) := fun q => by
    show ((aeval x (X q) : S) : Ω) = _
    rw [aeval_X]
    exact hx q
  have hψC : ∀ a : ℤ, ψ (C a) = φ (C a) := fun a =>
    RingHom.congr_fun (RingHom.ext_int (ψ.comp C) (φ.comp C)) a
  show ψ g * φ (chartMono c e) = φ g
  rw [g.as_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∀ k, ∑ i, m ⟨k, i⟩ = e k := hg m hm
  have hchart : φ (chartMono c e) = ∏ q : (Σ k, J k), φ (X ⟨q.1, c q.1⟩) ^ m q := by
    rw [Fintype.prod_sigma]
    simp only [Finset.prod_pow_eq_pow_sum, hdeg]
    show φ (∏ k, X ⟨k, c k⟩ ^ e k) = _
    rw [map_prod]
    simp only [map_pow]
  have hne : ∏ q : (Σ k, J k), φ (X ⟨q.1, c q.1⟩) ^ m q ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun q _ => pow_ne_zero _ (hc q.1)
  rw [hchart, monomial_eq, map_mul, map_mul, hψC, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [map_prod, map_pow, hψX, div_pow, Finset.prod_div_distrib]
  rw [mul_assoc, div_mul_cancel₀ _ hne]

theorem essFiniteType_locRing : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime]
    (K : Type) [Field K] (w : (Σ k, J k) → K) (W : Ideal (MRing J)) (c : ∀ k, J k),
    (mCoordIdeal w).IsPrime → W.IsPrime → mCoordIdeal w ≤ W → (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) →
    ∀ [Algebra (ZMod p) (locRing (mCoordIdeal w) W)],
      Algebra.EssFiniteType (ZMod p) (locRing (mCoordIdeal w) W) := by
  intro B _ J _ p _ K _ w W c hP hW hle hcW _
  classical
  haveI : (mCoordIdeal w).IsPrime := hP
  haveI : W.IsPrime := hW
  have hXP : ∀ k, fracHom (mCoordIdeal w) (X ⟨k, c k⟩) ≠ 0 := fun k h =>
    hcW k (hle (fracHom_eq_zero_iff.1 h))
  have hchartP : ∀ a : B → ℕ, fracHom (mCoordIdeal w) (chartMono c a) ≠ 0 := fun a h =>
    chartMono_notMem hW hcW a (hle (fracHom_eq_zero_iff.1 h))
  let xS : (Σ k, J k) → locRing (mCoordIdeal w) W := fun q =>
    ⟨fracHom (mCoordIdeal w) (X q) / fracHom (mCoordIdeal w) (X ⟨q.1, c q.1⟩),
      div_mem_locRing hle (homog_X q.1 q.2) (homog_X q.1 (c q.1)) (hcW q.1)⟩
  let s : Finset (locRing (mCoordIdeal w) W) := Finset.univ.image xS
  have hsub : Set.range xS ⊆ (s : Set (locRing (mCoordIdeal w) W)) := by
    rintro _ ⟨q, rfl⟩
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem xS (Finset.mem_univ q))
  have hmem : ∀ g : MRing J, aeval xS g ∈ Algebra.adjoin (ZMod p) (s : Set (locRing (mCoordIdeal w) W)) := by
    intro g
    refine Algebra.adjoin_mono hsub ?_
    induction g using MvPolynomial.induction_on
    next a =>
      rw [aeval_C, algebraMap_int_eq, Int.coe_castRingHom]
      exact intCast_mem _ a
    next f g hf hg =>
      rw [map_add]
      exact add_mem hf hg
    next f q hf =>
      rw [map_mul, aeval_X]
      exact mul_mem hf (Algebra.subset_adjoin ⟨q, rfl⟩)
  refine ⟨⟨s, ?_⟩⟩
  constructor
  constructor
  · intro y
    exact y.2
  · intro z
    obtain ⟨u, v, a, hu, hv, hvW, hz⟩ := (mem_locRing_iff hle).1 z.2
    have hA := aeval_ratio_mul_chartMono (fracHom (mCoordIdeal w)) c hXP _ xS (fun q => rfl) hu
    have hB := aeval_ratio_mul_chartMono (fracHom (mCoordIdeal w)) c hXP _ xS (fun q => rfl) hv
    have hBu : IsUnit (aeval xS v) :=
      (isUnit_iff hle (aeval xS v) hv (isMultiHomog_chartMono c a) (chartMono_notMem hW hcW a) hB).2 hvW
    refine ⟨(⟨aeval xS u, hmem u⟩, ⟨⟨aeval xS v, hmem v⟩, hBu⟩), ?_⟩
    apply Subtype.ext
    apply mul_right_cancel₀ (hchartP a)
    show ((z : FractionRing (MRing J ⧸ mCoordIdeal w)) * (aeval xS v : FractionRing (MRing J ⧸ mCoordIdeal w))) *
        fracHom (mCoordIdeal w) (chartMono c a) =
      (aeval xS u : FractionRing (MRing J ⧸ mCoordIdeal w)) * fracHom (mCoordIdeal w) (chartMono c a)
    rw [mul_assoc, hB, hA, hz]
  · intro x y h
    exact ⟨1, by rw [Subtype.ext h]⟩

end GlobalTheory.CompanionTheory.Ar.GeoDeg
end
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_ring_ess_finite_type : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (w : (Σ k, J k) → K) (W : Ideal (MRing J)) (c : ∀ k, J k), (mCoordIdeal w).IsPrime → W.IsPrime → mCoordIdeal w ≤ W → (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) → ∀ [Algebra (ZMod p) (locRing (mCoordIdeal w) W)], Algebra.EssFiniteType (ZMod p) (locRing (mCoordIdeal w) W) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.GeoDeg.essFiniteType_locRing
end

section
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoDeg.ResDeg

open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointResidue (exists_homog exists_homog_mem aeval_div)
open GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionsNonzero (chartMono isMultiHomog_chartMono mem_mCoordIdeal_of_aeval_eq_zero)
open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointChart (chartMono_notMem)
open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds (homog_X fracHom fracHom_apply fracHom_eq_zero_iff mem_locRing_iff div_mem_locRing)

theorem length_toNat_of_addEquiv {M κ : Type*} [AddCommGroup M] [Module ℤ M] [Field κ] (e : M ≃+ κ)
    (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) κ] :
    (Module.length ℤ M).toNat = Module.finrank (ZMod p) κ := by
  let l : M ≃ₗ[ℤ] κ := { e with map_smul' := fun n x => by simpa using map_intCast_smul e ℤ ℤ n x }
  rw [l.length_eq, Module.length_eq_of_surjective (R := ZMod p) (S := ℤ) (M := κ)
    (fun z => ⟨(z.cast : ℤ), by simp⟩), Module.length_eq_rank, Cardinal.toNat_toENat]
  rfl

attribute [local instance 2000] Ring.toIntAlgebra

variable {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)]
variable {P W : Ideal (MRing J)} [P.IsPrime] [W.IsPrime]

def dehom (hPW : P ≤ W) (c : ∀ k, J k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) : MRing J →+* locRing P W := by
  classical
  exact (aeval (R := ℤ) fun p : Σ k, J k =>
    (⟨fracHom P (X p) / fracHom P (X ⟨p.1, c p.1⟩),
      div_mem_locRing hPW (homog_X p.1 p.2) (homog_X p.1 (c p.1)) (hc p.1)⟩ : locRing P W)).toRingHom

theorem frac_chart_ne_zero (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (k : B) :
    fracHom P (X ⟨k, c k⟩ : MRing J) ≠ 0 := fun h =>
  hc k (hPW (fracHom_eq_zero_iff.1 h))

theorem coe_dehom (hPW : P ≤ W) (c : ∀ k, J k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (f : MRing J) :
    ((dehom hPW c hc f : locRing P W) : FractionRing (MRing J ⧸ P)) =
      aeval (fun p : Σ k, J k => fracHom P (X p) / fracHom P (X ⟨p.1, c p.1⟩)) f := by
  classical
  have h : (locRing P W).subtype.comp (dehom hPW c hc) =
      (aeval (R := ℤ) (fun p : Σ k, J k => fracHom P (X p) / fracHom P (X ⟨p.1, c p.1⟩))).toRingHom := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun p => ?_
    simp [dehom]
  exact RingHom.congr_fun h f

theorem fracHom_eq_aeval (f : MRing J) :
    fracHom P f = aeval (fun p : Σ k, J k => fracHom P (X p)) f := by
  have h : fracHom P = (aeval (R := ℤ) (fun p : Σ k, J k => fracHom P (X p))).toRingHom :=
    MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun p => by simp
  exact RingHom.congr_fun h f

theorem dehom_form (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) {G : MRing J} {n : B → ℕ}
    (hG : IsMultiHomog G n) :
    ((dehom hPW c hc G : locRing P W) : FractionRing (MRing J ⧸ P)) * fracHom P (chartMono c n) = fracHom P G := by
  have hD : fracHom P (chartMono c n) = ∏ k, fracHom P (X ⟨k, c k⟩ : MRing J) ^ n k := by
    simp [chartMono, map_prod, map_pow]
  have hD0 : ∏ k, fracHom P (X ⟨k, c k⟩ : MRing J) ^ n k ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (frac_chart_ne_zero hPW hc k)
  rw [coe_dehom, aeval_div (fun p : Σ k, J k => fracHom P (X p)) c G n hG, hD, ← fracHom_eq_aeval,
    mul_assoc, inv_mul_cancel₀ hD0, mul_one]

theorem dehom_X_chart (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (k : B) :
    dehom hPW c hc (X ⟨k, c k⟩) = 1 := by
  apply Subtype.ext
  rw [coe_dehom, aeval_X]
  exact div_self (frac_chart_ne_zero hPW hc k)

variable [IsLocalRing (locRing P W)]

theorem dehom_mem_maximalIdeal_iff (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W)
    {G : MRing J} {n : B → ℕ} (hG : IsMultiHomog G n) :
    dehom hPW c hc G ∈ maximalIdeal (locRing P W) ↔ G ∈ W :=
  regularityLocalFlat_holds.mem_maximalIdeal_iff hPW _ hG (isMultiHomog_chartMono c n)
    (chartMono_notMem ‹W.IsPrime› hc n) (dehom_form hPW hc hG)

def theta (hPW : P ≤ W) (c : ∀ k, J k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) :
    MRing J →+* ResidueField (locRing P W) :=
  (residue (locRing P W)).comp (dehom hPW c hc)

theorem theta_eq_zero_iff (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W)
    {G : MRing J} {n : B → ℕ} (hG : IsMultiHomog G n) : theta hPW c hc G = 0 ↔ G ∈ W :=
  (residue_eq_zero_iff _).trans (dehom_mem_maximalIdeal_iff hPW hc hG)

theorem theta_X_chart (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (k : B) :
    theta hPW c hc (X ⟨k, c k⟩) = 1 := by
  simp [theta, dehom_X_chart]

theorem ker_theta (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W)
    (hWh : IsMultiHomogIdeal W) :
    RingHom.ker (theta hPW c hc) = W ⊔ Ideal.span (Set.range fun k => (X ⟨k, c k⟩ : MRing J) - 1) := by
  set I0 := Ideal.span (Set.range fun k => (X ⟨k, c k⟩ : MRing J) - 1) with hI0
  have hIk : I0 ≤ RingHom.ker (theta hPW c hc) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    simp [SetLike.mem_coe, RingHom.mem_ker, theta_X_chart]
  apply le_antisymm
  · intro f hf
    have hχ : ∀ k, Ideal.Quotient.mk I0 (X ⟨k, c k⟩) = 1 := fun k => by
      rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
      exact Ideal.subset_span ⟨k, rfl⟩
    obtain ⟨n, G, hG, hGf⟩ := exists_homog _ c hχ f
    have hd : G - f ∈ I0 := Ideal.Quotient.eq.mp hGf
    have hG0 : G ∈ RingHom.ker (theta hPW c hc) := by simpa using add_mem (hIk hd) hf
    have hGW : G ∈ W := (theta_eq_zero_iff hPW hc hG).1 hG0
    have e : f = G - (G - f) := by ring
    rw [e]
    exact sub_mem (Ideal.mem_sup_left hGW) (Ideal.mem_sup_right hd)
  · refine sup_le ?_ hIk
    intro f hf
    obtain ⟨n, G, hGW, hG, e⟩ := exists_homog_mem (theta hPW c hc) c (theta_X_chart hPW hc) hWh hf
    rw [RingHom.mem_ker, ← e]
    exact (theta_eq_zero_iff hPW hc hG).2 hGW

theorem theta_surjective (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W)
    (hmax : (RingHom.ker (theta hPW c hc)).IsMaximal) : Function.Surjective (theta hPW c hc) := by
  intro z
  obtain ⟨x, rfl⟩ := residue_surjective z
  obtain ⟨u, v, a, hu, hv, hvW, hx⟩ := (mem_locRing_iff hPW).1 x.2
  have hvk : v ∉ RingHom.ker (theta hPW c hc) := fun h => hvW ((theta_eq_zero_iff hPW hc hv).1 h)
  obtain ⟨g, i, hi, hgi⟩ := hmax.exists_inv hvk
  have hD0 : fracHom P (chartMono c a) ≠ 0 := fun h =>
    chartMono_notMem ‹W.IsPrime› hc a (hPW (fracHom_eq_zero_iff.1 h))
  have h1 : dehom hPW c hc u = x * dehom hPW c hc v := by
    apply Subtype.ext
    apply mul_right_cancel₀ hD0
    rw [dehom_form hPW hc hu, ← hx, Subring.coe_mul, mul_assoc, dehom_form hPW hc hv]
  have h2 : theta hPW c hc g * theta hPW c hc v = 1 := by
    have := congrArg (theta hPW c hc) hgi
    rwa [map_add, map_mul, RingHom.mem_ker.1 hi, add_zero, map_one] at this
  refine ⟨u * g, ?_⟩
  have h3 : theta hPW c hc u = residue _ x * theta hPW c hc v := by
    simp only [theta, RingHom.comp_apply, h1, map_mul]
  rw [map_mul, h3, mul_assoc, mul_comm (theta hPW c hc v), h2, mul_one]

omit [P.IsPrime] [W.IsPrime] in

def chartHom {K : Type} [Field K] (w : (Σ k, J k) → K) (c : ∀ k, J k) : MRing J →+* chartRingZ w c :=
  (aeval (R := ℤ) fun p : Σ k, J k =>
    (⟨w p / w ⟨p.1, c p.1⟩, Algebra.subset_adjoin ⟨p, rfl⟩⟩ : chartRingZ w c)).toRingHom

theorem coe_chartHom {K : Type} [Field K] (w : (Σ k, J k) → K) (c : ∀ k, J k) (f : MRing J) :
    ((chartHom w c f : chartRingZ w c) : K) = aeval (fun p : Σ k, J k => w p / w ⟨p.1, c p.1⟩) f := by
  have h : (chartRingZ w c).val.toRingHom.comp (chartHom w c) =
      (aeval (R := ℤ) (fun p : Σ k, J k => w p / w ⟨p.1, c p.1⟩)).toRingHom := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun p => ?_
    simp [chartHom]
  exact RingHom.congr_fun h f

theorem chartHom_surjective {K : Type} [Field K] (w : (Σ k, J k) → K) (c : ∀ k, J k) :
    Function.Surjective (chartHom w c) := by
  rintro ⟨r, hr⟩
  rw [chartRingZ, Algebra.adjoin_range_eq_range_aeval] at hr
  obtain ⟨f, hf⟩ := (AlgHom.mem_range _).mp hr
  exact ⟨f, Subtype.ext ((coe_chartHom w c f).trans hf)⟩

theorem ker_chartHom_le {K : Type} [Field K] {w : (Σ k, J k) → K} {c : ∀ k, J k} {W : Ideal (MRing J)}
    (hPW : mCoordIdeal w ≤ W) (hwc : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    RingHom.ker (chartHom w c) ≤ W ⊔ Ideal.span (Set.range fun k => (X ⟨k, c k⟩ : MRing J) - 1) := by
  set I0 := Ideal.span (Set.range fun k => (X ⟨k, c k⟩ : MRing J) - 1) with hI0
  have hspan : I0 ≤ RingHom.ker (chartHom w c) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    apply Subtype.ext
    rw [coe_chartHom]
    simp [hwc k]
  intro f hf
  have hχ : ∀ k, Ideal.Quotient.mk I0 (X ⟨k, c k⟩) = 1 := fun k => by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    exact Ideal.subset_span ⟨k, rfl⟩
  obtain ⟨n, G, hG, hGf⟩ := exists_homog _ c hχ f
  have hd : G - f ∈ I0 := Ideal.Quotient.eq.mp hGf
  have hG0 : chartHom w c G = 0 := by simpa using add_mem (hspan hd) hf
  have hGv : aeval w G = 0 := by
    have h1 := congrArg Subtype.val hG0
    rw [coe_chartHom, aeval_div w c G n hG] at h1
    exact (mul_eq_zero.1 h1).resolve_right
      (inv_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hwc k)))
  have hGW : G ∈ W := hPW (mem_mCoordIdeal_of_aeval_eq_zero w hG hGv)
  have e : f = G - (G - f) := by ring
  rw [e]
  exact sub_mem (Ideal.mem_sup_left hGW) (Ideal.mem_sup_right hd)

theorem ker_theta_isMaximal {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    [IsFunctionField (ZMod p) K] {w : (Σ k, J k) → K} {W : Ideal (MRing J)} [(mCoordIdeal w).IsPrime] [W.IsPrime]
    [IsLocalRing (locRing (mCoordIdeal w) W)] (hbir : Birational w) (hPW : mCoordIdeal w ≤ W)
    {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (hWh : IsMultiHomogIdeal W)
    {k : B} {i : J k} (hw : w ⟨k, i⟩ ≠ 0) (hX : (X ⟨k, i⟩ : MRing J) ∈ W) :
    (RingHom.ker (theta hPW c hc)).IsMaximal := by
  have hwc : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k h => hc k (hPW ((X_mem_iff w k _).2 h))
  have hs := chartHom_surjective w c
  have hker := ker_theta hPW hc hWh
  have hle : RingHom.ker (chartHom w c) ≤ RingHom.ker (theta hPW c hc) := by
    rw [hker]
    exact ker_chartHom_le hPW hwc
  haveI : (RingHom.ker (theta hPW c hc)).IsPrime := RingHom.ker_isPrime _
  have hq : (Ideal.map (chartHom w c) (RingHom.ker (theta hPW c hc))).IsPrime :=
    Ideal.map_isPrime_of_surjective hs hle
  have h0 : Ideal.map (chartHom w c) (RingHom.ker (theta hPW c hc)) ≠ ⊥ := by
    intro h
    have hx : (X ⟨k, i⟩ : MRing J) ∈ RingHom.ker (theta hPW c hc) := by
      rw [hker]
      exact Ideal.mem_sup_left hX
    have h1 := Ideal.mem_map_of_mem (chartHom w c) hx
    rw [h, Ideal.mem_bot] at h1
    have h2 := congrArg Subtype.val h1
    rw [coe_chartHom, aeval_X] at h2
    exact div_ne_zero hw (hwc k) h2
  haveI := chart_prime_isMaximal (p := p) w hbir c hwc _ hq h0
  have h3 := Ideal.comap_isMaximal_of_surjective (chartHom w c) hs
    (K := Ideal.map (chartHom w c) (RingHom.ker (theta hPW c hc)))
  have hle' : Ideal.comap (chartHom w c) ⊥ ≤ RingHom.ker (theta hPW c hc) := hle
  rwa [Ideal.comap_map_of_surjective (chartHom w c) hs, sup_eq_left.2 hle'] at h3

theorem geoNum_zero_eq_finrank : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K), Birational w → ∀ (k : B) (c : J k), w ⟨k, c⟩ ≠ 0 → ∀ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), ∀ (b : Fin 0 → B → ℤ) [IsLocalRing (locRing (mCoordIdeal w) W)] [Algebra (ZMod p) (locRing (mCoordIdeal w) W)], geoNum 0 W b = (Module.finrank (ZMod p) (ResidueField (locRing (mCoordIdeal w) W)) : ℤ) := by
  intro B _ J _ p _ K _ _ _ w hbir k i hw W hW b _ _
  classical
  obtain ⟨hmin, hrel⟩ := hW
  haveI hWp : W.IsPrime := hmin.1.1
  haveI hPp : (mCoordIdeal w).IsPrime := RingHom.ker_isPrime _
  have hPW : mCoordIdeal w ≤ W := le_sup_left.trans hmin.1.2
  have hX : (X ⟨k, i⟩ : MRing J) ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  have hWh : IsMultiHomogIdeal W :=
    isMultiHomogIdeal_of_mem_minimalPrimes (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal w)
      (homog_X k i) hmin
  have hc : ∀ k, (X ⟨k, (hrel k).choose⟩ : MRing J) ∉ W := fun k => (hrel k).choose_spec
  have hmax := ker_theta_isMaximal (p := p) hbir hPW hc hWh hw hX
  have hsurj := theta_surjective hPW hc hmax
  rw [geoNum, dif_pos hrel]
  congr 1
  exact length_toNat_of_addEquiv
    ((Ideal.quotEquivOfEq (ker_theta hPW hc hWh).symm).trans
      (RingHom.quotientKerEquivOfSurjective hsurj)).toAddEquiv p

end GlobalTheory.CompanionTheory.Ar.GeoDeg.ResDeg
end
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_number_zero_finrank : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K), Birational w → ∀ (k : B) (c : J k), w ⟨k, c⟩ ≠ 0 → ∀ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), ∀ (b : Fin 0 → B → ℤ) [IsLocalRing (locRing (mCoordIdeal w) W)] [Algebra (ZMod p) (locRing (mCoordIdeal w) W)], geoNum 0 W b = (Module.finrank (ZMod p) (ResidueField (locRing (mCoordIdeal w) W)) : ℤ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.GeoDeg.ResDeg.geoNum_zero_eq_finrank
end

section
section
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg

namespace GlobalTheory.CompanionTheory.Ar.GeoDeg.Centre

section

variable {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)]
  {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K]

theorem mem_mCoordIdeal_iff {Ω : Type} [Field Ω] (y : (Σ k, J k) → Ω) {g : MRing J} {e : B → ℕ}
    (hg : IsMultiHomog g e) : g ∈ mCoordIdeal y ↔ aeval y g = 0 := by
  have hT : (∏ k, (X k : MvPolynomial B Ω) ^ e k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)
  rw [mCoordIdeal, RingHom.mem_ker]
  show mConeMap y g = 0 ↔ _
  rw [GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.mConeMap_form y hg, mul_eq_zero, or_iff_right hT, C_eq_zero]

variable (v : Place (ZMod p) K) (w : (Σ k, J k) → K) (c : ∀ k, J k)

def ratio (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (hle : ∀ k i, v.valuation (w ⟨k, i⟩) ≤ v.valuation (w ⟨k, c k⟩))
    (q : Σ k, J k) : v.ring :=
  ⟨w q / w ⟨q.1, c q.1⟩, by
    rw [← v.valuation_le_one_iff, map_div₀]
    exact div_le_one_of_le₀ (hle q.1 q.2) zero_le'⟩

variable {v w c}
variable (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (hle : ∀ k i, v.valuation (w ⟨k, i⟩) ≤ v.valuation (w ⟨k, c k⟩))

include hc in
theorem prod_ne_zero (e : B → ℕ) : (∏ k, w ⟨k, c k⟩ ^ e k) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)

theorem coe_aeval_ratio {g : MRing J} {e : B → ℕ} (hg : IsMultiHomog g e) :
    ((aeval (ratio v w c hc hle) g : v.ring) : K) = aeval w g * (∏ k, w ⟨k, c k⟩ ^ e k)⁻¹ := by
  rw [← GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointResidue.aeval_div w c g e hg]
  exact MvPolynomial.comp_aeval_apply (φ := (algebraMap v.ring K).toIntAlgHom) _ g

theorem aeval_residue (g : MRing J) :
    aeval (fun q => residue v.ring (ratio v w c hc hle q)) g =
      residue v.ring (aeval (ratio v w c hc hle) g) :=
  (MvPolynomial.comp_aeval_apply (φ := (residue v.ring).toIntAlgHom) _ g).symm

theorem valuation_prod (e : B → ℕ) :
    v.valuation (∏ k, w ⟨k, c k⟩ ^ e k) = ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun k _ => map_pow _ _ _

include hc in
theorem prod_valuation_pos (e : B → ℕ) : 0 < ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k := by
  rw [← valuation_prod]
  exact zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (prod_ne_zero hc e))

include hc hle in

theorem valuation_aeval_le {g : MRing J} {e : B → ℕ} (hg : IsMultiHomog g e) :
    v.valuation (aeval w g) ≤ ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k := by
  have h := (v.valuation_le_one_iff _).2 (aeval (ratio v w c hc hle) g).2
  rw [coe_aeval_ratio hc hle hg, map_mul, map_inv₀, valuation_prod] at h
  rwa [mul_inv_le_iff₀ (prod_valuation_pos hc e), one_mul] at h

theorem mem_iff {g : MRing J} {e : B → ℕ} (hg : IsMultiHomog g e) :
    g ∈ mCoordIdeal (fun q => residue v.ring (ratio v w c hc hle q)) ↔
      v.valuation (aeval w g) < ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k := by
  refine (mem_mCoordIdeal_iff _ hg).trans (Iff.trans (Eq.congr_left (aeval_residue hc hle g)) ?_)
  rw [residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff, ← v.valuation_lt_one_iff,
    coe_aeval_ratio hc hle hg, map_mul, map_inv₀, valuation_prod,
    mul_inv_lt_iff₀ (prod_valuation_pos hc e), one_mul]

end

theorem exists_centre : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type)
    [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K) (v : Place (ZMod p) K)
    (c : ∀ k, J k), (∀ k, w ⟨k, c k⟩ ≠ 0) →
    (∀ k i, v.valuation (w ⟨k, i⟩) ≤ v.valuation (w ⟨k, c k⟩)) →
    ∃ W : Ideal (MRing J), W.IsPrime ∧ IsMultiHomogIdeal W ∧ mCoordIdeal w ≤ W ∧
      (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) ∧ Dom v w W ∧
      ∀ (e : B → ℕ) (g : MRing J), IsMultiHomog g e →
        (g ∈ W ↔ v.valuation (aeval w g) < ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k) := by
  intro B _ J _ p _ K _ _ _ w v c hc hle
  refine ⟨mCoordIdeal (fun q => residue v.ring (ratio v w c hc hle q)), RingHom.ker_isPrime _,
    GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal _, ?_, ?_, ?_, fun e g hg => mem_iff hc hle hg⟩
  · obtain ⟨S, hS, hSe⟩ := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal w
    have hSV : Ideal.span S ≤ mCoordIdeal w := hSe.ge
    rw [hSe, Ideal.span_le]
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    have hf0 : aeval w f = 0 := (mem_mCoordIdeal_iff w ha).1 (hSV (Ideal.subset_span hf))
    refine (mem_iff hc hle ha).2 ?_
    rw [hf0, map_zero]
    exact prod_valuation_pos hc a
  · intro k h
    have h1 := (X_mem_iff _ k (c k)).1 h
    have h2 : ratio v w c hc hle ⟨k, c k⟩ = 1 := Subtype.ext (div_self (hc k))
    rw [h2, map_one] at h1
    exact one_ne_zero h1
  · intro e g h hg hh hhW
    have hh' : v.valuation (aeval w h) = ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k :=
      le_antisymm (valuation_aeval_le hc hle hh) (not_lt.1 fun hlt => hhW ((mem_iff hc hle hh).2 hlt))
    rw [hh']
    exact ⟨valuation_aeval_le hc hle hg, (mem_iff hc hle hg).1⟩

end GlobalTheory.CompanionTheory.Ar.GeoDeg.Centre
end
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multihomog_prime_of_place : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K) (v : Place (ZMod p) K) (c : ∀ k, J k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k i, v.valuation (w ⟨k, i⟩) ≤ v.valuation (w ⟨k, c k⟩)) → ∃ W : Ideal (MRing J), W.IsPrime ∧ IsMultiHomogIdeal W ∧ mCoordIdeal w ≤ W ∧ (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) ∧ Dom v w W ∧ ∀ (e : B → ℕ) (g : MRing J), IsMultiHomog g e → (g ∈ W ↔ v.valuation (aeval w g) < ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.GeoDeg.Centre.exists_centre
end

section
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoDeg.ChartMin

open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointChart

variable {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)] {K : Type} [Field K]

def chartIdeal (w : (Σ k, J k) → K) (c : ∀ k, J k) (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (U : Ideal (MRing J)) :
    Ideal (chartRingZ w c) where
  carrier := {r | (r : K) ∈ chartPrime w c U}
  add_mem' ha hb := chartPrime_add w ha hb
  zero_mem' := ⟨0, 0, fun m hm => by simp at hm, U.zero_mem, by simp⟩
  smul_mem' a _ hb := chartPrime_mul w hc a.2 hb

theorem mem_chartIdeal {w : (Σ k, J k) → K} {c : ∀ k, J k} {hc : ∀ k, w ⟨k, c k⟩ ≠ 0} {U : Ideal (MRing J)}
    {r : chartRingZ w c} : r ∈ chartIdeal w c hc U ↔ (r : K) ∈ chartPrime w c U :=
  Iff.rfl

theorem chartIdeal_mono {w : (Σ k, J k) → K} {c : ∀ k, J k} (hc : ∀ k, w ⟨k, c k⟩ ≠ 0)
    {U U' : Ideal (MRing J)} (h : U ≤ U') : chartIdeal w c hc U ≤ chartIdeal w c hc U' := by
  rintro r ⟨e, g, hg, hgU, hr⟩
  exact ⟨e, g, hg, h hgU, hr⟩

theorem chartIdeal_isPrime (w : (Σ k, J k) → K) {c : ∀ k, J k} (hc : ∀ k, w ⟨k, c k⟩ ≠ 0)
    {U : Ideal (MRing J)} (hVU : mCoordIdeal w ≤ U) (hU : U.IsPrime)
    (hXU : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ U) : (chartIdeal w c hc U).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one]
    intro h
    have h1 := (mem_chartPrime_iff w hVU hU hXU (r := ((1 : chartRingZ w c) : K)) (e := 0) (k := 1)
      GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_one (by simp)).mp (mem_chartIdeal.mp h)
    exact hU.ne_top ((Ideal.eq_top_iff_one U).mpr h1)
  · intro a b hab
    obtain ⟨e, k, hk, ha⟩ := exists_rep w hc a.2
    obtain ⟨e', k', hk', hb⟩ := exists_rep w hc b.2
    have hkk : k * k' ∈ U := (mem_chartPrime_iff w hVU hU hXU (r := ((a * b : chartRingZ w c) : K))
      (GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_mul hk hk') (by
        rw [MulMemClass.coe_mul, map_mul, prod_pow_add]
        linear_combination ((b : K) * ∏ k, w ⟨k, c k⟩ ^ e' k) * ha + (aeval w k) * hb)).mp
      (mem_chartIdeal.mp hab)
    rcases hU.mem_or_mem hkk with h | h
    · exact Or.inl ⟨e, k, hk, h, ha⟩
    · exact Or.inr ⟨e', k', hk', h, hb⟩

theorem mem_minimalPrimes_of_coord (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime]
    (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K)
    (hbir : Birational w) (W : Ideal (MRing J)) (c : ∀ k, J k) (hWp : W.IsPrime) (hWh : IsMultiHomogIdeal W)
    (hVW : mCoordIdeal w ≤ W) (hXc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (k : B) (c₀ : J k)
    (hw : w ⟨k, c₀⟩ ≠ 0) (hx : (X ⟨k, c₀⟩ : MRing J) ∈ W) :
    W ∈ (mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c₀⟩ : MRing J)}).minimalPrimes := by
  classical
  have hIW : mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c₀⟩ : MRing J)} ≤ W :=
    sup_le hVW ((Ideal.span_singleton_le_iff_mem _).2 hx)
  refine ⟨⟨hWp, hIW⟩, ?_⟩
  rintro Q ⟨hQp, hIQ⟩ hQW
  have hwc : ∀ j, w ⟨j, c j⟩ ≠ 0 := fun j h => hXc j (hVW ((X_mem_iff w j (c j)).2 h))
  have hVQ : mCoordIdeal w ≤ Q := le_sup_left.trans hIQ
  have hxQ : (X ⟨k, c₀⟩ : MRing J) ∈ Q := hIQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hXQ : ∀ j, (X ⟨j, c j⟩ : MRing J) ∉ Q := fun j h => hXc j (hQW h)

  have hpW := chartIdeal_isPrime w hwc hVW hWp hXc
  have hpQ := chartIdeal_isPrime w hwc hVQ hQp hXQ

  let r : chartRingZ w c := ⟨w ⟨k, c₀⟩ / w ⟨k, c k⟩, Algebra.subset_adjoin ⟨⟨k, c₀⟩, rfl⟩⟩
  have hr : r ∈ chartIdeal w c hwc Q := by
    refine ⟨Pi.single k 1, X ⟨k, c₀⟩, GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds.homog_X k c₀, hxQ, ?_⟩
    have hprod : ∏ j, w ⟨j, c j⟩ ^ (Pi.single k 1 : B → ℕ) j = w ⟨k, c k⟩ := by
      rw [Fintype.prod_eq_single k (fun j hj => by simp [Pi.single_eq_of_ne hj])]
      simp
    rw [hprod, aeval_X]
    exact div_mul_cancel₀ _ (hwc k)
  have hne : chartIdeal w c hwc Q ≠ ⊥ := by
    intro h0
    have h1 : r = 0 := by simpa [h0] using hr
    exact div_ne_zero hw (hwc k) (congrArg Subtype.val h1)
  have hmax := chart_prime_isMaximal (p := p) w hbir c hwc _ hpQ hne
  have heq := hmax.eq_of_le hpW.ne_top (chartIdeal_mono hwc hQW)

  obtain ⟨S, hS, hSe⟩ := hWh
  have hSW : Ideal.span S ≤ W := hSe.ge
  rw [hSe, Ideal.span_le]
  intro g hg
  obtain ⟨e, he⟩ := hS g hg
  have hprod : (∏ j, w ⟨j, c j⟩ ^ e j) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (hwc j)
  have hrep : aeval w g * (∏ j, w ⟨j, c j⟩ ^ e j)⁻¹ * ∏ j, w ⟨j, c j⟩ ^ e j = aeval w g :=
    inv_mul_cancel_right₀ hprod _
  let t : chartRingZ w c := ⟨_, form_div_mem_chart w c he⟩
  have htW : t ∈ chartIdeal w c hwc W := ⟨e, g, he, hSW (Ideal.subset_span hg), hrep⟩
  rw [← heq] at htW
  exact (mem_chartPrime_iff w hVQ hQp hXQ he hrep).1 (mem_chartIdeal.1 htW)

end GlobalTheory.CompanionTheory.Ar.GeoDeg.ChartMin

end
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multihomog_prime_mem_divisor_support : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K), Birational w → ∀ (W : Ideal (MRing J)) (c : ∀ k, J k), W.IsPrime → IsMultiHomogIdeal W → mCoordIdeal w ≤ W → (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) → ∀ (k : B) (c₀ : J k), w ⟨k, c₀⟩ ≠ 0 → (X ⟨k, c₀⟩ : MRing J) ∈ W → W ∈ (mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c₀⟩ : MRing J)}).minimalPrimes := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.GeoDeg.ChartMin.mem_minimalPrimes_of_coord
end

section
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.GeoDeg
open MvPolynomial GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing

local notation "T_eft" => GlobalTheory.T.local_ring_ess_finite_type
local notation "T_geo" => GlobalTheory.T.geometric_number_zero_finrank
local notation "T_ex1" => GlobalTheory.T.exists_multihomog_prime_of_place
local notation "T_ex2" => GlobalTheory.T.multihomog_prime_mem_divisor_support

section
variable {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)]
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K]

theorem exists_centre (w : (Σ k, J k) → K) (hbir : Birational w) (hw : ∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) (v : Place (ZMod p) K) (k : B) (c : J k)
    (hc : w ⟨k, c⟩ ≠ 0) (hlt : v.valuation (w ⟨k, c⟩) < (Finset.univ.sup fun i => v.valuation (w ⟨k, i⟩))) :
    ∃ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), Dom v w W := by
  classical
  have hch : ∀ k', ∃ c' : J k', w ⟨k', c'⟩ ≠ 0 ∧ ∀ i, v.valuation (w ⟨k', i⟩) ≤ v.valuation (w ⟨k', c'⟩) := by
    intro k'
    obtain ⟨c0, h0⟩ := hw k'
    haveI : Nonempty (J k') := ⟨c0⟩
    obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun i => v.valuation (w ⟨k', i⟩)) Finset.univ_nonempty
    refine ⟨m, ?_, fun i => hm i (Finset.mem_univ i)⟩
    intro h
    have h1 := hm c0 (Finset.mem_univ _)
    simp only [h, map_zero] at h1
    exact ((Valuation.ne_zero_iff _).2 h0) (le_zero_iff.1 h1)
  choose c' hc1 hc2 using hch
  obtain ⟨W, hWp, hWh, hVW, hcW, hD, hiff⟩ := T_ex1 B J p K w v c' hc1 hc2
  have hx : (X ⟨k, c⟩ : MRing J) ∈ W := by
    rw [hiff (Pi.single k 1) _ (GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds.homog_X k c)]
    have hs : (Finset.univ.sup fun i => v.valuation (w ⟨k, i⟩)) = v.valuation (w ⟨k, c' k⟩) :=
      le_antisymm (Finset.sup_le fun i _ => hc2 k i)
        (Finset.le_sup (f := fun i => v.valuation (w ⟨k, i⟩)) (Finset.mem_univ _))
    rw [hs] at hlt
    simpa [Pi.single_apply, pow_ite, Finset.prod_ite_eq'] using hlt
  exact ⟨W, ⟨T_ex2 B J p K w hbir W c' hWp hWh hVW hcW k c hc hx, fun k' => ⟨c' k', hcW k'⟩⟩, hD⟩

open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds (homog_X fracHom fracHom_apply fracHom_eq_zero_iff isLocalRing mem_maximalIdeal_iff isUnit_iff)

theorem local_term (w : (Σ k, J k) → K) (hbir : Birational w) (k : B) (c : J k) (hc : w ⟨k, c⟩ ≠ 0)
    (W : Ideal (MRing J)) (hWd : W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩)) (c' : ∀ k, J k)
    (hc' : ∀ k, (X ⟨k, c' k⟩ : MRing J) ∉ W) (b : Fin 0 → B → ℤ) :
    (multAt (mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c⟩ : MRing J)}) W : ℤ) * geoNum 0 W b =
      ∑ᶠ v ∈ {v : Place (ZMod p) K | Dom v w W}, (v.deg : ℤ) * v.ord (w ⟨k, c⟩ / w ⟨k, c' k⟩) := by
  classical
  have hV : (mCoordIdeal w).IsPrime := RingHom.ker_isPrime _
  have hVh : IsMultiHomogIdeal (mCoordIdeal w) := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal w
  have hVW : mCoordIdeal w ≤ W := le_trans le_sup_left hWd.1.1.2
  have hWp : W.IsPrime := hWd.1.1.1
  haveI := hV
  haveI := hWp
  obtain ⟨ρ, hρ⟩ := exists_rho w W hV hWp hVW
  haveI hloc : IsLocalRing (locRing (mCoordIdeal w) W) := isLocalRing hVW
  letI : Algebra (locRing (mCoordIdeal w) W) K := ρ.toAlgebra
  haveI hfr : IsFractionRing (locRing (mCoordIdeal w) W) K := hρ.isFractionRing hbir hV hWp hVW hc'
  have hpK : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  have hpA : CharP (locRing (mCoordIdeal w) W) p :=
    (RingHom.charP_iff (algebraMap (locRing (mCoordIdeal w) W) K) (IsFractionRing.injective _ _) p).2 hpK
  letI : Algebra (ZMod p) (locRing (mCoordIdeal w) W) := ZMod.algebra _ p
  haveI : IsScalarTower (ZMod p) (locRing (mCoordIdeal w) W) K :=
    IsScalarTower.of_algebraMap_eq fun x =>
      DFunLike.congr_fun (Subsingleton.elim (algebraMap (ZMod p) K)
        ((algebraMap (locRing (mCoordIdeal w) W) K).comp (algebraMap (ZMod p) (locRing (mCoordIdeal w) W)))) x
  haveI hE : Algebra.EssFiniteType (ZMod p) (locRing (mCoordIdeal w) W) :=
    T_eft B J p K w W c' hV hWp hVW hc'
  haveI hN : IsNoetherianRing (locRing (mCoordIdeal w) W) := Algebra.EssFiniteType.isNoetherianRing (ZMod p) _
  have hs : IsMultiHomog (X ⟨k, c⟩ : MRing J) (Pi.single k 1) := homog_X k c
  have ht : IsMultiHomog (X ⟨k, c' k⟩ : MRing J) (Pi.single k 1) := homog_X k (c' k)
  have hsV : (X ⟨k, c⟩ : MRing J) ∉ mCoordIdeal w := fun h => hc ((X_mem_iff w k c).1 h)
  have hproj : IsMultiProjPrime (mCoordIdeal w) :=
    ⟨hV, hVh, fun k => ⟨c' k, fun h => hc' k (hVW h)⟩⟩
  have ht0 : fracHom (mCoordIdeal w) (X ⟨k, c' k⟩) ≠ 0 := fun h => hc' k (hVW (fracHom_eq_zero_iff.1 h))
  have hy : (fracHom (mCoordIdeal w) (X ⟨k, c⟩) / fracHom (mCoordIdeal w) (X ⟨k, c' k⟩)) *
      fracHom (mCoordIdeal w) (X ⟨k, c' k⟩) = fracHom (mCoordIdeal w) (X ⟨k, c⟩) := div_mul_cancel₀ _ ht0
  obtain ⟨hym, hlen⟩ := GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.regularityDehomogenization_holds B J (mCoordIdeal w) (X ⟨k, c⟩) (X ⟨k, c' k⟩)
    (Pi.single k 1) W _ hproj hs hsV hWd ht (hc' k) hy
  set f : locRing (mCoordIdeal w) W := ⟨_, hym⟩ with hfdef
  have hf1 := hρ f _ _ _ hs ht (hc' k) hy
  have hne : w ⟨k, c' k⟩ ≠ 0 := fun h => hc' k (hVW ((X_mem_iff w k _).2 h))
  have hf2 : ρ f = w ⟨k, c⟩ / w ⟨k, c' k⟩ := by
    rw [eq_div_iff hne]
    simpa using hf1
  have hf0 : f ≠ 0 := by
    intro h
    rw [h, map_zero] at hf2
    exact div_ne_zero hc hne hf2.symm
  have hxW : (X ⟨k, c⟩ : MRing J) ∈ W := hWd.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  have hnf : ¬ IsField (locRing (mCoordIdeal w) W) := by
    intro hF
    have hu : IsUnit f := by
      obtain ⟨g, hg⟩ := hF.mul_inv_cancel hf0
      exact IsUnit.of_mul_eq_one _ hg
    exact ((isUnit_iff hVW f hs ht (hc' k) hy).1 hu) hxW
  have key := GlobalTheory.T.length_formula_sum_valuations (ZMod p) K (locRing (mCoordIdeal w) W) hnf f hf0
  have hset : {v : Place (ZMod p) K | (∀ a : locRing (mCoordIdeal w) W, v.valuation (algebraMap _ K a) ≤ 1) ∧
      ∀ a ∈ maximalIdeal (locRing (mCoordIdeal w) W), v.valuation (algebraMap _ K a) < 1} =
      {v : Place (ZMod p) K | Dom v w W} := by
    ext v
    exact hρ.dom_iff hV hWp hVW v
  rw [hset] at key
  rw [hlen, locIdeal_eq_span hym, T_geo B J p K w hbir k c hc W hWd b]
  have : (algebraMap (locRing (mCoordIdeal w) W) K f) = w ⟨k, c⟩ / w ⟨k, c' k⟩ := hf2
  rw [this] at key
  rw [← key]
  push_cast
  rfl

theorem block_sum (local_term : ∀ (w : (Σ k, J k) → K), Birational w → ∀ (k : B) (c : J k), w ⟨k, c⟩ ≠ 0 →
      ∀ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), ∀ c' : ∀ k, J k, (∀ k, (X ⟨k, c' k⟩ : MRing J) ∉ W) → ∀ b : Fin 0 → B → ℤ,
      (multAt (mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c⟩ : MRing J)}) W : ℤ) * geoNum 0 W b =
        ∑ᶠ v ∈ {v : Place (ZMod p) K | Dom v w W}, (v.deg : ℤ) * v.ord (w ⟨k, c⟩ / w ⟨k, c' k⟩))
    (exists_centre : ∀ (w : (Σ k, J k) → K), Birational w → (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → ∀ (v : Place (ZMod p) K) (k : B) (c : J k),
      w ⟨k, c⟩ ≠ 0 → v.valuation (w ⟨k, c⟩) < (Finset.univ.sup fun i => v.valuation (w ⟨k, i⟩)) →
      ∃ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), Dom v w W)
    (w : (Σ k, J k) → K) (hbir : Birational w) (hw : ∀ k, ∃ c, w ⟨k, c⟩ ≠ 0)
    (hfin : ∀ x : K, x ≠ 0 → {v : Place (ZMod p) K | v.valuation x ≠ 1}.Finite)
    (hprod : ∀ x : K, x ≠ 0 → ∑ᶠ v : Place (ZMod p) K, (v.deg : ℤ) * WithZero.log (v.valuation x) = 0)
    (k : B) (c : J k) (hc : w ⟨k, c⟩ ≠ 0) (b : Fin 0 → B → ℤ) :
    ∑ᶠ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩),
        (multAt (mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c⟩ : MRing J)}) W : ℤ) * geoNum 0 W b =
      ∑ᶠ v : Place (ZMod p) K, (v.deg : ℤ) * WithZero.log (Finset.univ.sup fun i => v.valuation (w ⟨k, i⟩)) := by
  classical
  have hV : (mCoordIdeal w).IsPrime := RingHom.ker_isPrime _
  have hVh : IsMultiHomogIdeal (mCoordIdeal w) := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal w
  set S : Place (ZMod p) K → WithZero (Multiplicative ℤ) := fun v => Finset.univ.sup fun i => v.valuation (w ⟨k, i⟩) with hSdef
  set f : Place (ZMod p) K → ℤ := fun v =>
    (v.deg : ℤ) * (WithZero.log (S v) - WithZero.log (v.valuation (w ⟨k, c⟩))) with hf
  set T : Set (Place (ZMod p) K) := {v | v.valuation (w ⟨k, c⟩) < S v} with hTdef
  have hle : ∀ v : Place (ZMod p) K, v.valuation (w ⟨k, c⟩) ≤ S v := fun v =>
    Finset.le_sup (f := fun i => v.valuation (w ⟨k, i⟩)) (Finset.mem_univ c)
  set U : Set (Place (ZMod p) K) := ⋃ j ∈ {j : J k | w ⟨k, j⟩ ≠ 0}, {v | v.valuation (w ⟨k, j⟩) ≠ 1} with hUdef
  have hU : U.Finite := (Set.toFinite _).biUnion fun j hj => hfin _ hj
  have h1 : ∀ v ∉ U, ∀ j, w ⟨k, j⟩ ≠ 0 → v.valuation (w ⟨k, j⟩) = 1 := by
    intro v hv j hj
    by_contra h
    exact hv (Set.mem_biUnion (show j ∈ {j : J k | w ⟨k, j⟩ ≠ 0} from hj) h)
  have hS1 : ∀ v ∉ U, S v = 1 := by
    intro v hv
    apply le_antisymm
    · refine Finset.sup_le fun i _ => ?_
      by_cases hi : w ⟨k, i⟩ = 0
      · simp [hi]
      · exact (h1 v hv i hi).le
    · calc 1 = v.valuation (w ⟨k, c⟩) := (h1 v hv c hc).symm
        _ ≤ S v := hle v
  have hTU : T ⊆ U := by
    intro v hv
    by_contra hvU
    have h2 : S v = 1 := hS1 v hvU
    have h3 := h1 v hvU c hc
    have h4 : v.valuation (w ⟨k, c⟩) < S v := hv
    rw [h2, h3] at h4
    exact lt_irrefl _ h4
  have hTfin : T.Finite := hU.subset hTU
  have hmain : ∀ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩),
      (multAt (mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c⟩ : MRing J)}) W : ℤ) * geoNum 0 W b =
        ∑ᶠ v ∈ {v : Place (ZMod p) K | Dom v w W}, f v := by
    intro W hW
    choose c' hc' using hW.2
    rw [local_term w hbir k c hc W hW c' hc' b]
    refine finsum_mem_congr rfl fun v hv => ?_
    have hVW : mCoordIdeal w ≤ W := le_trans le_sup_left hW.1.1.2
    have hne : w ⟨k, c' k⟩ ≠ 0 := fun h => hc' k (hVW ((X_mem_iff w k _).2 h))
    have hsup : S v = v.valuation (w ⟨k, c' k⟩) := Dom.sup_eq hv hc' k
    simp only [hf, hsup]
    rw [v.ord_div hc hne]
    simp only [Place.ord]
    ring
  have hset : ∀ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), {v : Place (ZMod p) K | Dom v w W} ⊆ T := by
    intro W hW v hv
    choose c' hc' using hW.2
    have hx : (X ⟨k, c⟩ : MRing J) ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
    have h2 : S v = v.valuation (w ⟨k, c' k⟩) := Dom.sup_eq hv hc' k
    show v.valuation (w ⟨k, c⟩) < S v
    rw [h2]
    exact Dom.lt_chart hv hc' k hx
  have hcover : T ⊆ ⋃ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), {v : Place (ZMod p) K | Dom v w W} := by
    intro v hv
    obtain ⟨W, hW, hD⟩ := exists_centre w hbir hw v k c hc hv
    exact Set.mem_biUnion hW hD
  have hdisj : (divSupp (mCoordIdeal w) (X ⟨k, c⟩)).PairwiseDisjoint
      (fun W => {v : Place (ZMod p) K | Dom v w W}) := by
    intro W hW W' hW' hne
    refine Set.disjoint_left.2 fun v hv hv' => hne (le_antisymm ?_ ?_)
    · choose c' hc' using hW.2
      exact Dom.le_of_dom hv hv' (isMultiHomogIdeal_of_mem_minimalPrimes hVh
        (GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds.homog_X k c) hW.1) hW.1.1.1 hc'
    · choose c' hc' using hW'.2
      exact Dom.le_of_dom hv' hv (isMultiHomogIdeal_of_mem_minimalPrimes hVh
        (GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds.homog_X k c) hW'.1) hW'.1.1.1 hc'
  have hsupp : T ∩ Function.support f = Set.univ ∩ Function.support f := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_univ, true_and, and_iff_right_iff_imp]
    intro hv
    by_contra hvT
    have h2 : S v = v.valuation (w ⟨k, c⟩) := le_antisymm (not_lt.1 hvT) (hle v)
    exact hv (by simp [hf, h2])
  have hF1 : (Function.support fun v : Place (ZMod p) K => (v.deg : ℤ) * WithZero.log (S v)).Finite := by
    refine hU.subset fun v hv => ?_
    by_contra hvU
    exact hv (by simp [hS1 v hvU])
  have hF2 : (Function.support fun v : Place (ZMod p) K => (v.deg : ℤ) * WithZero.log (v.valuation (w ⟨k, c⟩))).Finite := by
    refine (hfin _ hc).subset fun v hv => ?_
    intro h
    exact hv (by simp [h])
  calc _ = ∑ᶠ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), ∑ᶠ v ∈ {v : Place (ZMod p) K | Dom v w W}, f v :=
        finsum_mem_congr rfl hmain
    _ = ∑ᶠ v ∈ ⋃ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), {v : Place (ZMod p) K | Dom v w W}, f v :=
        (finsum_mem_biUnion hdisj (divSupp_finite _ _) fun W hW => hTfin.subset (hset W hW)).symm
    _ = ∑ᶠ v ∈ T, f v := by
        rw [Set.Subset.antisymm (Set.iUnion₂_subset hset) hcover]
    _ = ∑ᶠ v ∈ (Set.univ : Set (Place (ZMod p) K)), f v := finsum_mem_inter_support_eq f _ _ hsupp
    _ = ∑ᶠ v, f v := finsum_mem_univ f
    _ = ∑ᶠ v : Place (ZMod p) K, ((v.deg : ℤ) * WithZero.log (S v) - (v.deg : ℤ) * WithZero.log (v.valuation (w ⟨k, c⟩))) :=
        finsum_congr fun v => by simp only [hf]; ring
    _ = _ := by
        rw [finsum_sub_distrib hF1 hF2, hprod _ hc, sub_zero]

theorem degree_of_local (local_term : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K), Birational w → ∀ (k : B) (c : J k), w ⟨k, c⟩ ≠ 0 →
      ∀ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), ∀ c' : ∀ k, J k, (∀ k, (X ⟨k, c' k⟩ : MRing J) ∉ W) → ∀ b : Fin 0 → B → ℤ,
      (multAt (mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c⟩ : MRing J)}) W : ℤ) * geoNum 0 W b =
        ∑ᶠ v ∈ {v : Place (ZMod p) K | Dom v w W}, (v.deg : ℤ) * v.ord (w ⟨k, c⟩ / w ⟨k, c' k⟩))
    (exists_centre : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K), Birational w → (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → ∀ (v : Place (ZMod p) K) (k : B) (c : J k),
      w ⟨k, c⟩ ≠ 0 → v.valuation (w ⟨k, c⟩) < (Finset.univ.sup fun i => v.valuation (w ⟨k, i⟩)) →
      ∃ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), Dom v w W) :
    ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [GroundTheory.FunctionField.IsFunctionField (ZMod p) K] (C : ACurve K) (w : (Σ k, J k) → K) (a : B → ℤ), IsFFCurve (ZMod p) C → Birational w → (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → geoNum 1 (mCoordIdeal w) (fun _ => a) = coordDeg C w a := by
  intro B _ J _ p _ K _ _ _ C w a hC hbir hw
  classical
  obtain ⟨e, he⟩ := hC
  have hfin : ∀ x : K, x ≠ 0 → {v : Place (ZMod p) K | v.valuation x ≠ 1}.Finite := by
    intro x hx
    refine ((C.fin x hx).image e).subset fun v hv => ⟨e.symm v, ?_, by simp⟩
    have := (he (e.symm v)).1
    simp only [Equiv.apply_symm_apply] at this
    simpa [this] using hv
  have hprod : ∀ x : K, x ≠ 0 → ∑ᶠ v : Place (ZMod p) K, (v.deg : ℤ) * WithZero.log (v.valuation x) = 0 := by
    intro x hx
    rw [← C.prod x hx, ← finsum_comp_equiv e]
    refine finsum_congr fun i => ?_
    rw [(he i).1, (he i).2]
  have hrel : IsRelevant (mCoordIdeal w) := fun k => by
    obtain ⟨c, hc⟩ := hw k
    exact ⟨c, fun h => hc ((X_mem_iff w k c).1 h)⟩
  show geoNum (0 + 1) (mCoordIdeal w) (fun _ => a) = _
  rw [geoNum, dif_pos hrel, coordDeg]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hck : w ⟨k, (hrel k).choose⟩ ≠ 0 := fun h => (hrel k).choose_spec ((X_mem_iff w k _).2 h)
  rw [block_sum (local_term B J p K) (exists_centre B J p K) w hbir hw hfin hprod k _ hck, ← finsum_comp_equiv e]
  congr 1
  refine finsum_congr fun i => ?_
  simp only [(he i).1, (he i).2]

theorem geoNum_one_eq_coordDeg : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [GroundTheory.FunctionField.IsFunctionField (ZMod p) K] (C : ACurve K) (w : (Σ k, J k) → K) (a : B → ℤ), IsFFCurve (ZMod p) C → Birational w → (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → geoNum 1 (mCoordIdeal w) (fun _ => a) = coordDeg C w a :=
  degree_of_local (fun _ _ _ _ _ _ _ _ _ _ w hbir k c hc W hW c' hc' b => local_term w hbir k c hc W hW c' hc' b)
    (fun _ _ _ _ _ _ _ _ _ _ w hbir hw v k c hc hlt => exists_centre w hbir hw v k c hc hlt)

end
end GlobalTheory.CompanionTheory.Ar.GeoDeg
end
end

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.function_field_degree_eq : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [GroundTheory.FunctionField.IsFunctionField (ZMod p) K] (C : ACurve K) (w : (Σ k, J k) → K) (a : B → ℤ), IsFFCurve (ZMod p) C → Birational w → (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → geoNum 1 (mCoordIdeal w) (fun _ => a) = coordDeg C w a := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.GeoDeg.geoNum_one_eq_coordDeg
end

section
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.GrDeg

theorem grLine_deg_eq_sub : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (G : Over X) [GrpObj G] [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (Vz : Type) [AddCommGroup Vz] [Module K Vz] [FiniteDimensional K Vz] (Mz : LieModel G z Vz) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)) (S : Set (Cpt ξ)) (L L' : Lat ξ V) (r r' : ℕ) (b₀ : Fin r → V) (U' : Submodule Ω V), IsCptGen ξ → Smooth G.hom → (⟨centre z, h₀⟩ : Cpt ξ) ∈ S → (∀ i, (⟨centre (Y.x i), h i⟩ : Cpt ξ) ∈ S) → LinearIndependent Ω b₀ → L.IsFlagVBOn S b₀ → L'.IsVBOn S r' U' → IsCompl (Submodule.span Ω (Set.range b₀)) U' → (∀ q ∈ S, M.lat q = L q ⊔ L' q) → ∃ W : ℕ → Submodule K Vz, W 0 = ⊥ ∧ W r = Submodule.span K {v | ∃ e ∈ L ⟨centre z, h₀⟩, M.ValAt z e (Mz.pt v)} ∧ ∀ s : Fin r, Y.IsDeg (L.gr b₀ s) (subDeg C (Y.lieLat Mz) (W (s + 1)) - subDeg C (Y.lieLat Mz) (W s)) :=
  PositivityTheory.HtPt.Ci.gr_deg

end GlobalTheory.CompanionTheory.Ar.GrDeg
end

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_lie_lattice_degree : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (G : Over X) [GrpObj G] [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (Vz : Type) [AddCommGroup Vz] [Module K Vz] [FiniteDimensional K Vz] (Mz : LieModel G z Vz) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)) (S : Set (Cpt ξ)) (L L' : Lat ξ V) (r r' : ℕ) (b₀ : Fin r → V) (U' : Submodule Ω V), IsCptGen ξ → Smooth G.hom → (⟨centre z, h₀⟩ : Cpt ξ) ∈ S → (∀ i, (⟨centre (Y.x i), h i⟩ : Cpt ξ) ∈ S) → LinearIndependent Ω b₀ → L.IsFlagVBOn S b₀ → L'.IsVBOn S r' U' → IsCompl (Submodule.span Ω (Set.range b₀)) U' → (∀ q ∈ S, M.lat q = L q ⊔ L' q) → ∃ W : ℕ → Submodule K Vz, W 0 = ⊥ ∧ W r = Submodule.span K {v | ∃ e ∈ L ⟨centre z, h₀⟩, M.ValAt z e (Mz.pt v)} ∧ ∀ s : Fin r, Y.IsDeg (L.gr b₀ s) (subDeg C (Y.lieLat Mz) (W (s + 1)) - subDeg C (Y.lieLat Mz) (W s)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.GrDeg.grLine_deg_eq_sub
end

section
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem isDeg_coordDeg : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (w : (Σ k, J k) → K) (Λ : Lat ξ Ω) (S : Set (Cpt ξ)) (a : B → ℤ) (e₀ : Ω) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)), CoordTie ℤ ξ (segre y) → CoordsAt ξ y z w → (⟨centre z, h₀⟩ : Cpt ξ) ∈ S → (∀ i, (⟨centre (Y.x i), h i⟩ : Cpt ξ) ∈ S) → Λ.IsDegOn S y a e₀ → Y.IsDeg Λ (coordDeg C w a) :=
  PositivityTheory.HtPt.Ci.isdeg_coord

end GlobalTheory.CompanionTheory.Ar.Crv
end

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_lattice_degree_formula : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (w : (Σ k, J k) → K) (Λ : Lat ξ Ω) (S : Set (Cpt ξ)) (a : B → ℤ) (e₀ : Ω) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)), CoordTie ℤ ξ (segre y) → CoordsAt ξ y z w → (⟨centre z, h₀⟩ : Cpt ξ) ∈ S → (∀ i, (⟨centre (Y.x i), h i⟩ : Cpt ξ) ∈ S) → Λ.IsDegOn S y a e₀ → Y.IsDeg Λ (coordDeg C w a) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Crv.isDeg_coordDeg
end

section
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem curveIn_isDeg_unique_of_isCptGen : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (Λ : Lat ξ Ω) (n n' : ℤ), IsCptGen ξ → Y.IsDeg Λ n → Y.IsDeg Λ n' → n = n' :=
  @PositivityTheory.HtPt.Ch.isdeg_unique

end GlobalTheory.CompanionTheory.Ar.Crv
end

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_degree_unique : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (Λ : Lat ξ Ω) (n n' : ℤ), IsCptGen ξ → Y.IsDeg Λ n → Y.IsDeg Λ n' → n = n' := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Crv.curveIn_isDeg_unique_of_isCptGen
end

section
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj.ModelNefness

theorem iSup_split {α I : Type} [CompleteLattice α] (f : I → α) (s₀ : I) :
    ⨆ s, f s = f s₀ ⊔ ⨆ s : {s // s ≠ s₀}, f s := by
  apply le_antisymm
  · refine iSup_le fun s => ?_
    by_cases h : s = s₀
    · subst h; exact le_sup_left
    · exact le_sup_of_le_right (le_iSup (fun s : {s // s ≠ s₀} => f s) ⟨s, h⟩)
  · exact sup_le (le_iSup f s₀) (iSup_le fun s => le_iSup f s.1)

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem isVBOn_iSup {E : Type} [AddCommGroup E] [Module Ω E] {I : Type} [Fintype I]
    (L : I → Lat ξ E) (T : Set (Cpt ξ)) (r : I → ℕ) (V : I → Submodule Ω E) (hV : iSupIndep V)
    (hL : ∀ s, (L s).IsVBOn T (r s) (V s)) :
    Lat.IsVBOn (ξ := ξ) (fun q => ⨆ s, L s q) T (∑ s, r s) (⨆ s, V s) := by
  classical
  intro p hp
  choose U hU b hb hfr using fun s => hL s p hp
  have hmem : ∀ (x : X) (s : Finset I), x ∈ s.inf U ↔ ∀ i ∈ s, x ∈ U i := by
    intro x s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [Finset.inf_insert, ih]
  let e : (Σ s, Fin (r s)) ≃ Fin (∑ s, r s) := Fintype.equivFinOfCardEq (by simp [Fintype.card_sigma])
  let c : Fin (∑ s, r s) → E := fun i => b (e.symm i).1 (e.symm i).2
  have hsp : ∀ (A : Type) [Semiring A] [Module A E],
      Submodule.span A (Set.range c) = ⨆ s, Submodule.span A (Set.range (b s)) := by
    intro A _ _
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (le_iSup (fun s => Submodule.span A (Set.range (b s))) (e.symm i).1)
        (Submodule.subset_span ⟨_, rfl⟩)
    · refine iSup_le fun s => ?_
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨e ⟨s, i⟩, congrArg (fun x : Σ s, Fin (r s) => b x.1 x.2) (e.symm_apply_apply ⟨s, i⟩)⟩
  have hli : LinearIndependent Ω c := by
    have h1 : LinearIndependent Ω fun ji : Σ s, Fin (r s) => b ji.1 ji.2 := by
      refine linearIndependent_iUnion_finite (fun s => (hfr s p hp (hU s)).1) fun i t _ hi => ?_
      rw [hb i]
      refine (hV i).mono_right (iSup₂_le fun s hs => ?_)
      rw [hb s]
      exact le_iSup₂_of_le s (fun h => hi (h ▸ hs)) le_rfl
    exact h1.comp e.symm e.symm.injective
  refine ⟨Finset.univ.inf U, (hmem _ _).2 fun s _ => hU s, c, ?_, fun q hq hqU => ⟨hli, ?_⟩⟩
  · rw [hsp Ω]
    exact iSup_congr hb
  · rw [hsp (regAt ξ q)]
    exact iSup_congr fun s => (hfr s q hq ((hmem _ _).1 hqU s (Finset.mem_univ s))).2

theorem unitAt_of_isUnit {q : Cpt ξ} {a : regAt ξ q} (h : IsUnit a) : unitAt ξ q (a : Ω) := by
  obtain ⟨u, rfl⟩ := h
  refine ⟨fun h0 => u.ne_zero (Subtype.ext h0), u.1.2, ?_⟩
  have : ((u : regAt ξ q) : Ω)⁻¹ = (((u⁻¹ : (regAt ξ q)ˣ) : regAt ξ q) : Ω) := by
    exact inv_eq_of_mul_eq_one_right (congrArg Subtype.val u.mul_inv)
  rw [this]
  exact (((u⁻¹ : (regAt ξ q)ˣ) : regAt ξ q)).2

theorem unitAt_int_of_fibre [CharZero Ω] {p : ℕ} (hp : p.Prime) (q : Cpt ξ) (hq : InFibre ξ p q) {d : ℤ}
    (hd : ¬ (p : ℤ) ∣ d) : unitAt ξ q (d : Ω) := by
  haveI := EigSplit.isLocalRing_regAt q
  obtain ⟨a, b, hab⟩ := ((Nat.prime_iff_prime_int.1 hp).coprime_iff_not_dvd).2 hd
  have hP : ¬ IsUnit ((p : ℕ) : regAt ξ q) := fun h => hq (by simpa using unitAt_of_isUnit h)
  have h1 : ((a : regAt ξ q) * (p : regAt ξ q)) + (b : regAt ξ q) * (d : regAt ξ q) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → regAt ξ q) hab
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h1 with h | h
  · exact absurd (isUnit_of_mul_isUnit_right h) hP
  · have e : ((d : regAt ξ q) : Ω) = (d : Ω) := map_intCast (regAt ξ q).subtype d
    rw [← e]
    exact unitAt_of_isUnit (isUnit_of_mul_isUnit_right (x := (b : regAt ξ q)) (by rwa [mul_comm] at h ⊢))

theorem charZero_of_isArithVar {B : Type} [Fintype B] {ι : B → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω} {d : ℕ}
    (h : IsArithVar (mCoordIdeal y) d) : CharZero Ω := by
  obtain ⟨-, -, hh, -⟩ := h
  refine charZero_of_inj_zero fun n hn => ?_
  have h1 : (n : ℤ) ∈ (mCoordIdeal y).comap (MvPolynomial.C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker]
    have : mConeMap y (MvPolynomial.C (n : ℤ)) = MvPolynomial.C (n : Ω) := by
      simpa using (mConeMap y).commutes (n : ℤ)
    simpa [hn] using this
  rw [show (mCoordIdeal y).comap (MvPolynomial.C : ℤ →+* MRing ι) = ⊥ from hh] at h1
  simpa using h1

open Module in

theorem flag_at (E : Type) [Field E] [NumberField E] [CharZero Ω] (hg : IsCptGen ξ)
    {K k : Type} [Field K] [Field k] [Algebra k K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z)
    (G : Over X) [GrpObj G] [IsCommMonObj G] (hsm : Smooth G.hom) (act : OAct (𝓞 E) G)
    (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V)
    (Vz : Type) [AddCommGroup Vz] [Module K Vz] [FiniteDimensional K Vz] (Mz : LieModel G z Vz)
    (r : 𝓞 E →+* Module.End Ω V) (rz : 𝓞 E →+* Module.End K Vz) (hr : M.IsActOf act.act r)
    (hrz : Mz.IsActOf act.act rz) (I : Type) [Fintype I] (σ : I → (𝓞 E →+* Ω)) (χ : I → (𝓞 E →+* k))
    (hσ : Function.Injective σ) (hcard : Fintype.card I = finrank ℚ E) (hχ : IsSplit χ)
    (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)) (S : Set (Cpt ξ))
    (hz : (⟨centre z, h₀⟩ : Cpt ξ) ∈ S) (hS : ∀ i, (⟨centre (Y.x i), h i⟩ : Cpt ξ) ∈ S)
    (hreg : ∀ q ∈ S, ∀ s a, σ s a ∈ regAt ξ q) (hdisc : ∀ q ∈ S, unitAt ξ q ((discr E : ℤ) : Ω))
    (hval : ∀ s a, ValAt ξ z (σ s a) (algebraMap k K (χ s a)))
    (s₀ : I) {n : ℕ} (b : Fin n → V) (hb : LinearIndependent Ω b)
    (hspan : Submodule.span Ω (Set.range b) = eigSp r (σ s₀)) (hfl : (M.eigLat r (σ s₀)).IsFlagVBOn S b) :
    ∃ W : ℕ → Submodule K Vz, W 0 = ⊥ ∧ W n = eigSp rz ((algebraMap k K).comp (χ s₀)) ∧
      ∀ s : Fin n, Y.IsDeg ((M.eigLat r (σ s₀)).gr b s)
        (subDeg C (Y.lieLat Mz) (W (s + 1)) - subDeg C (Y.lieLat Mz) (W s)) := by
  classical
  have hvb : M.lat.IsVBOn S (finrank Ω V) ⊤ := fun p _ => by
    obtain ⟨U, hU, c, hc, hf⟩ := (GlobalTheory.T.lie_omega_lattice_vector_bundle X Ω ξ G V M hg hsm).1 p trivial
    exact ⟨U, hU, c, hc, fun q _ hq => hf q trivial hq⟩
  obtain ⟨hE, hsum⟩ := EigSplit.isVBOn_eigSp X Ω ξ V E r M.lat S _ I σ hg hσ hcard hvb
    (fun p _ a e he => LieStable.lat_stable X Ω ξ G V M _ act r hr p a e he) hreg hdisc
  have hint := GlobalTheory.T.eigenspace_decomposition_internal Ω V E r I σ hσ hcard
  have hind := hint.submodule_iSupIndep
  let U' : Submodule Ω V := ⨆ s : {s // s ≠ s₀}, eigSp r (σ s)
  let L' : Lat ξ V := fun q => ⨆ s : {s // s ≠ s₀}, M.eigLat r (σ s) q
  have hL' : L'.IsVBOn S (∑ s : {s // s ≠ s₀}, finrank Ω (eigSp r (σ s))) U' :=
    isVBOn_iSup (fun s : {s // s ≠ s₀} => M.eigLat r (σ s)) S _ (fun s => eigSp r (σ s))
      (hind.comp Subtype.val_injective) fun s => hE s
  have hcompl : IsCompl (Submodule.span Ω (Set.range b)) U' := by
    rw [hspan]
    refine ⟨(hind s₀).mono_right (iSup_le fun s => le_iSup₂_of_le s.1 s.2 le_rfl), ?_⟩
    rw [codisjoint_iff, ← iSup_split (fun s => eigSp r (σ s)) s₀]
    exact hint.submodule_iSup_eq_top
  have hlat : ∀ q ∈ S, M.lat q = M.eigLat r (σ s₀) q ⊔ L' q := fun q hq =>
    (hsum q hq).trans (iSup_split (fun s => M.eigLat r (σ s) q) s₀)
  obtain ⟨W, hW0, hWn, hdeg⟩ := GlobalTheory.T.curve_lie_lattice_degree X Ω ξ K C z Y G V M Vz Mz h₀ h S (M.eigLat r (σ s₀)) L' n _ b U'
    hg hsm hz hS hb hfl hL' hcompl hlat
  refine ⟨W, hW0, ?_, hdeg⟩
  rw [hWn]
  exact GlobalTheory.T.curve_lie_eigen_decomposition X Ω ξ k K z G V M Vz Mz h₀ (𝓞 E) I act.act r rz σ χ hg hsm act.hom hr hrz hχ hval
    (hsum _ hz) s₀

end GlobalTheory.CompanionTheory.Ar.Conj.ModelNefness

namespace GlobalTheory.CompanionTheory.Ar.Conj

open ModelNefness GlobalTheory.CompanionTheory.Ar.Top in

theorem m2Model_of_m2Curve : CurveSemiAbelianConjecture → RootLineDeRhamModel := by
  intro hC Ψ _ N M j p E _ _ _ H D hp hp2 hj hjN mu hdom hthr Wi hW
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hprime, hPW, hchar, hdim⟩ := hW
  haveI : CharZero M.Ω := charZero_of_isArithVar M.arith
  obtain ⟨K, _, _, _, w, hwW, hbir, hwk⟩ := GlobalTheory.T.function_field_model_exists M.K M.ι Wi p hprime hchar hdim
  obtain ⟨C, hFF, hne, hv⟩ := GlobalTheory.T.function_field_curve_exists (ZMod p) K
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  obtain ⟨z, Y, h₀, h, hco, hfib⟩ := GlobalTheory.T.curve_through_coordinates D.X M.Ω D.ξ M.K M.ι M.y D.tie K C w
    (by rw [hwW]; exact hPW) hwk
  obtain ⟨hz, hi⟩ := hfib p (CharP.cast_eq_zero K p)
  have hg : IsCptGen D.ξ := D.tie.gen
  obtain ⟨φ, hφ, -⟩ := ValHom.exists_valAt_hom D.X M.Ω D.ξ K z h₀ hg
  let σ' : Ψ ⊕ Ψ → (𝓞 E →+* regAt D.ξ ⟨centre z, h₀⟩) := fun s => (D.σ s).codRestrict _ (D.reg _ hz s)
  have hσ' : Function.Injective σ' := fun s s' e => D.σ_inj (RingHom.ext fun a =>
    congrArg Subtype.val (RingHom.congr_fun e a))
  have hcard : Fintype.card (Ψ ⊕ Ψ) = Module.finrank ℚ E := by
    rw [Fintype.card_sum, ← D.card]; ring
  obtain ⟨χ, hχ, hχv⟩ := GlobalTheory.T.split_characters_unramified E (regAt D.ξ ⟨centre z, h₀⟩) K (Ψ ⊕ Ψ) p σ' φ hσ' hcard D.unram
  have hval : ∀ s a, ValAt D.ξ z (D.σ s a) (algebraMap (algebraicClosure (ZMod p) K) K (χ s a)) := fun s a =>
    (hφ _ _).2 ⟨D.reg _ hz s a, (hχv s a).symm⟩
  have hconj : ∀ τ a, χ (Sum.inr τ) a = χ (Sum.inl τ) (H.bar a) := fun τ a => Subtype.ext (by
    rw [hχv, hχv]
    exact congrArg φ (Subtype.ext (D.conj τ a)))
  have hconst : ∀ i (c : algebraicClosure (ZMod p) K), C.v i (algebraMap _ K c) ≤ 1 := fun i c =>
    hv i _ (mem_algebraicClosure_iff.1 c.2)
  obtain ⟨Vz, _, _, ⟨Mz⟩⟩ := lieModel_exists D.X D.t.G K z
  haveI : Smooth D.t.G.hom := D.t.semi.smooth
  haveI : FiniteDimensional K Vz := (GlobalTheory.T.lie_model_finite_projective D.X D.t.G K z Vz Mz).1
  obtain ⟨rz, hrz, -⟩ := lieModel_exists_unique_act D.X D.t.G K z Vz Mz (𝓞 E) D.t.act.act D.t.act.hom
    D.t.act.one D.t.act.mul D.t.act.add
  have hreg : ∀ q ∈ {q | InFibre D.ξ p q}, ∀ s a, D.σ s a ∈ regAt D.ξ q := fun q hq s a => D.reg q hq s a
  have hdisc : ∀ q ∈ {q | InFibre D.ξ p q}, unitAt D.ξ q ((NumberField.discr E : ℤ) : M.Ω) := fun q hq =>
    unitAt_int_of_fibre hp q hq D.unram
  choose Wf hW0 hWj hdegW using fun τ => flag_at E hg C z Y D.t.G D.t.semi.smooth D.t.act D.V D.L Vz Mz D.r rz
    D.act hrz (Ψ ⊕ Ψ) D.σ χ D.σ_inj hcard hχ h₀ h {q | InFibre D.ξ p q} hz hi hreg hdisc hval (Sum.inl τ)
    (D.b₁ τ) (D.ind₁ τ).1 (D.ind₁ τ).2 (D.flag₁ τ)
  choose Lf hL0 hLq hdegL using fun τ => flag_at E hg C z Y D.t.G D.t.semi.smooth D.t.act D.V D.L Vz Mz D.r rz
    D.act hrz (Ψ ⊕ Ψ) D.σ χ D.σ_inj hcard hχ h₀ h {q | InFibre D.ξ p q} hz hi hreg hdisc hval (Sum.inr τ)
    (D.b₂ τ) (D.ind₂ τ).1 (D.ind₂ τ).2 (D.flag₂ τ)
  have hxdeg : ∀ r, geoNum 1 Wi (fun _ => M.xdeg r) = coordDeg C w (M.xdeg r) := fun r => by
    rw [← hwW]
    exact GlobalTheory.T.function_field_degree_eq M.K M.ι p K C w (M.xdeg r) hFF hbir hwk
  let x : Ψ × Fin N → ℝ := fun r => (geoNum 1 Wi (fun _ => M.xdeg r) : ℝ)
  let wd : Ψ → ℕ → ℝ := fun τ i => (subDeg C (Y.lieLat Mz) (Wf τ i) : ℝ)
  let ld : Ψ → ℕ → ℝ := fun τ i => (subDeg C (Y.lieLat Mz) (Lf τ i) : ℝ)
  have hx1 : ∀ τ (i : Fin N), (i : ℕ) < j → x (τ, i) = wd τ (i + 1) - wd τ i := by
    intro τ i hij
    obtain ⟨e₀, hdo⟩ := D.deg₁ τ i hij
    have h1 := GlobalTheory.T.curve_lattice_degree_formula D.X M.Ω D.ξ K C z Y M.K M.ι M.y w _ {q | InFibre D.ξ p q} _ e₀ h₀ h D.tie hco hz hi hdo
    have h2 := GlobalTheory.T.curve_degree_unique D.X M.Ω D.ξ K C z Y _ _ _ hg h1 (hdegW τ ⟨i, hij⟩)
    simp only [x, wd, hxdeg, h2]
    push_cast
    rfl
  have hx2 : ∀ τ (i : Fin N), j ≤ (i : ℕ) → x (τ, i) = -(ld τ (N - 1 - i + 1) - ld τ (N - 1 - i)) := by
    intro τ i hij
    have hlt : N - 1 - (i : ℕ) < N - j := by have := i.2; omega
    obtain ⟨e₀, hdo⟩ := D.deg₂ τ i hlt hij
    have h1 := GlobalTheory.T.curve_lattice_degree_formula D.X M.Ω D.ξ K C z Y M.K M.ι M.y w _ {q | InFibre D.ξ p q} _ e₀ h₀ h D.tie hco hz hi hdo
    have h2 := GlobalTheory.T.curve_degree_unique D.X M.Ω D.ξ K C z Y _ _ _ hg h1 (hdegL τ ⟨N - 1 - i, hlt⟩)
    have h3 : coordDeg C w (-M.xdeg (τ, i)) = -coordDeg C w (M.xdeg (τ, i)) := by
      simp [coordDeg]
    rw [h3] at h2
    have h4 : coordDeg C w (M.xdeg (τ, i)) = -(subDeg C (Y.lieLat Mz) (Lf τ (N - 1 - i + 1)) -
        subDeg C (Y.lieLat Mz) (Lf τ (N - 1 - i))) := by
      rw [← neg_eq_iff_eq_neg]; exact h2
    simp only [x, ld, hxdeg, h4]
    push_cast
    rfl
  obtain ⟨hgap, heq⟩ := GlobalTheory.T.nef_threshold_gap_condition Ψ N j p mu x wd ld hp2 hj hjN hdom hthr hx1 hx2
  have hfin := hC E H D.X D.t D.pow (algebraicClosure (ZMod p) K) K p hp2 C z Y hne hconst
    (fun i => D.fib ⟨_, h i⟩ (hi i)) Vz Mz rz hrz Ψ χ hχ hconj j (N - j) _ Wf Lf hj (by omega) hW0 hL0 hWj hLq hgap
  have hfin' : 0 ≤ ∑ r : Ψ × Fin N, -mu r.1 r.2 * x r := heq ▸ hfin
  have hcd : M.curveDeg mu 0 Wi = ∑ r : Ψ × Fin N, -mu r.1 r.2 * x r := by
    unfold RootModel.curveDeg
    rw [Fintype.sum_option]
    simp only [RootModel.coef, RootModel.line, M.x_deg, zero_div, zero_mul, zero_add, x]
  rw [hcd]
  exact hfin'

end GlobalTheory.CompanionTheory.Ar.Conj
end
end

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootLineDeRhamModel_of_curveSemiAbelian : CurveSemiAbelianConjecture → RootLineDeRhamModel := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Conj.m2Model_of_m2Curve
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.curve_family_formal_germ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (C : ACurve K) (z : Sp K ⟶ X0) (Y : CurveIn C z), (∀ i, FibPF t (GlobalTheory.CompanionTheory.Ar.centre (Y.x i))) → ∃ (d : ℕ) (F : Family C p d (𝓞 E)) (g : GermAt t z d), g.B = F.B ∧ ∀ i, ∃ gi : GermAt t (Y.x i) d, ∀ l, IsCombAtG t z g.tg (fun j => lin (F.φ i) 1 j l) (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l) := by
  first | exact @PositivityTheory.HtPt.Cf.family_ex | exact PositivityTheory.HtPt.Cf.family_ex
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_family_formal_germ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (C : ACurve K) (z : Sp K ⟶ X0) (Y : CurveIn C z), (∀ i, FibPF t (GlobalTheory.CompanionTheory.Ar.centre (Y.x i))) → ∃ (d : ℕ) (F : Family C p d (𝓞 E)) (g : GermAt t z d), g.B = F.B ∧ ∀ i, ∃ gi : GermAt t (Y.x i) d, ∀ l, IsCombAtG t z g.tg (fun j => lin (F.φ i) 1 j l) (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.curve_family_formal_germ
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj.TopH2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

theorem comp_one_over {G T T' : Over X0} [GrpObj G] (f : T' ⟶ T) : f ≫ (1 : T ⟶ G) = 1 := by
  show f ≫ (toUnit T ≫ η[G]) = toUnit T' ≫ η[G]
  rw [← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]

theorem comp_prod_ofFn {G T T' : Over X0} [GrpObj G] (f : T' ⟶ T) :
    ∀ {m : ℕ} (u : Fin m → (T ⟶ G)), f ≫ (List.ofFn u).prod = (List.ofFn fun l => f ≫ u l).prod
  | 0, u => by simp only [List.ofFn_zero, List.prod_nil]; exact comp_one_over f
  | m + 1, u => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.comp_mul,
      comp_prod_ofFn f (fun l => u l.succ)]

theorem spMap_comp_eq {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (a : B →+* C) (b : A →+* B) (c : D →+* C) (d : A →+* D) (h : a.comp b = c.comp d) :
    spMap a ≫ spMap b = spMap c ≫ spMap d := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

section Rings

variable {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R')

theorem dualMap_comp_algebraMap :
    (GlobalTheory.CompanionTheory.Ar.dualMap f).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_comp_epsMul (c : R) :
    (GlobalTheory.CompanionTheory.Ar.dualMap f).comp (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul c) =
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (f c)).comp (GlobalTheory.CompanionTheory.Ar.dualMap f) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [GlobalTheory.CompanionTheory.Ar.dualMap, ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, mul_comm]

theorem fst_comp_dualMap :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (GlobalTheory.CompanionTheory.Ar.dualMap f) =
      f.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  simp [GlobalTheory.CompanionTheory.Ar.dualMap]

end Rings

variable (t : SAB H X0)

theorem isTanAt_iff {S : Type} [CommRing S] (x : Sp S ⟶ X0) (w : GlobalTheory.CompanionTheory.Ar.epsAt x ⟶ t.G) :
    GlobalTheory.CompanionTheory.Ar.IsTanAt t.G x w ↔ IsTanAtG t x w.left :=
  ⟨fun h => ⟨Over.w w, h⟩, fun h => h.2⟩

theorem isTanAtG_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {x : Sp R ⟶ X0}
    {v : Sp (DualNumber R) ⟶ t.G.left} (h : IsTanAtG t x v) :
    IsTanAtG t (spMap f ≫ x) (spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ v) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h.1, ← Category.assoc, ← Category.assoc,
      spMap_comp_eq _ _ _ _ (dualMap_comp_algebraMap f)]
  · rw [← Category.assoc, spMap_comp_eq _ _ _ _ (fst_comp_dualMap f), Category.assoc, h.2]
    have := comp_one_over (G := t.G) (Over.homMk (U := Over.mk (spMap f ≫ x)) (V := Over.mk x) (spMap f) rfl)
    rw [← this, Over.comp_left]
    rfl

theorem isCombAtG_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {x : Sp R ⟶ X0} {m : ℕ}
    {v : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} {cf : Fin m → R} {w : Sp (DualNumber R) ⟶ t.G.left}
    (h : IsCombAtG t x v cf w) :
    IsCombAtG t (spMap f ≫ x) (fun l => spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ v l) (fun l => f (cf l))
      (spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ w) := by
  obtain ⟨u, hu, hw⟩ := h
  let k : tEpsG (spMap f ≫ x) ⟶ tEpsG x := Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap f)) (by
    simp only [Over.mk_hom]
    rw [← Category.assoc, ← Category.assoc, spMap_comp_eq _ _ _ _ (dualMap_comp_algebraMap f)])
  refine ⟨fun l => k ≫ u l, fun l => ?_, ?_⟩
  · show spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ (u l).left = _
    rw [hu l, ← Category.assoc, ← Category.assoc,
      spMap_comp_eq _ _ _ _ (dualMap_comp_epsMul f (cf l))]
  · rw [← comp_prod_ofFn, Over.comp_left, hw]
    rfl

theorem pt_sum {S : Type} [CommRing S] {x : Sp S ⟶ X0} {V : Type} [AddCommGroup V] [Module S V]
    (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G x V) :
    ∀ {m : ℕ} (c : Fin m → V), (List.ofFn fun l => M.pt (c l)).prod = M.pt (∑ l, c l)
  | 0, c => by
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    have h := M.add 0 0
    rw [add_zero] at h
    exact (mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)).symm
  | m + 1, c => by
    rw [List.ofFn_succ, List.prod_cons, pt_sum M (fun l => c l.succ), Fin.sum_univ_succ, M.add]

theorem isCombAtG_iff_lie {S : Type} [CommRing S] {x : Sp S ⟶ X0} {V : Type} [AddCommGroup V] [Module S V]
    (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G x V) {m : ℕ} (b : Fin m → V) (cf : Fin m → S)
    (w : Sp (DualNumber S) ⟶ t.G.left) :
    IsCombAtG t x (fun l => (M.pt (b l)).left) cf w ↔ w = (M.pt (∑ l, cf l • b l)).left := by
  constructor
  · rintro ⟨u, hu, hw⟩
    have hu' : u = fun l => M.pt (cf l • b l) :=
      funext fun l => Over.OverMorphism.ext (by rw [hu l, M.smul]; rfl)
    rw [← hw, hu', pt_sum]
  · intro hw
    exact ⟨fun l => M.pt (cf l • b l), fun l => by rw [M.smul]; rfl, by rw [pt_sum, hw]⟩

theorem lieLat_conjData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (C : ACurve K) (z : Sp K ⟶ X0) (Y : CurveIn C z), Nonempty C.I → (∀ i, FibPF t (GlobalTheory.CompanionTheory.Ar.centre (Y.x i))) → ∀ (V : Type) [AddCommGroup V] [Module K V] (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G z V) (r : 𝓞 E →+* Module.End K V), M.IsActOf t.act.act r → ∃ (d : ℕ) (D : ConjData C p (𝓞 E) d) (e : V ≃ₗ[K] (Fin d → K)), (∀ i v, v ∈ Y.lieLat M i ↔ e v ∈ D.lie i) ∧ ∀ a v, e (r a v) = (D.ρ a).mulVec (e v) := by
  intro E _ _ _ H _ hbar X0 t hPow K _ p _ _ C z Y hne hFib V _ _ M r hr
  obtain ⟨d, F, g, hgB, hfam⟩ := GlobalTheory.T.curve_family_formal_germ E H hbar X0 t hPow K p C z Y hFib
  obtain ⟨D, hDρ, hDlie⟩ := GlobalTheory.T.family_gives_conjugate_lie_data K C p d (𝓞 E) F hne
  obtain ⟨e, hecomb, heact⟩ := GlobalTheory.T.formal_germ_lie_basis E H hbar X0 t K z d g V M
  refine ⟨d, D, e, fun i v => ?_, fun a v => by rw [heact r hr a v, hDρ a, hgB]⟩
  obtain ⟨gi, hgi⟩ := hfam i
  obtain ⟨hΦΨ, hΨΦ, -⟩ := GlobalTheory.T.formal_isomorphism_transport K d (𝓞 E) F.B (F.BK i) (F.φ i) (F.ψ i) (F.lam i) (F.iso i)
  have hgen : spMap (C.v i).valuationSubring.subtype ≫ Y.x i = z := Y.gen i
  have htan : ∀ l, IsTanAtG t z (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l) :=
    fun l => by
      have h0 := isTanAtG_map t (C.v i).valuationSubring.subtype (gi.tan l)
      rwa [hgen] at h0
  choose c hc using fun l => M.onto (Over.homMk _ (htan l).1) ((isTanAt_iff t z _).2 (htan l))
  have hcl : ∀ l, (M.pt (c l)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l :=
    fun l => by rw [hc l]; rfl
  have hec : ∀ l j, e (c l) j = lin (F.φ i) 1 j l := by
    intro l
    have hw : IsTanAtG t z (M.pt (c l)).left := (isTanAt_iff t z _).1 (M.tan _)
    have := (g.basis _ hw).unique (hecomb (c l)) (by rw [hcl]; exact hgi l)
    exact fun j => congrFun this j
  have key : ∀ (a : Fin d → (C.v i).valuationSubring)
      (w : Sp (DualNumber (C.v i).valuationSubring) ⟶ t.G.left), IsCombAtG t (Y.x i) gi.tg a w →
      spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ w = (M.pt (∑ l, (a l : K) • c l)).left ∧
        e (∑ l, (a l : K) • c l) = (lin (F.φ i) 1).mulVec (fun l => (a l : K)) := by
    intro a w hw
    refine ⟨?_, ?_⟩
    · have h1 := isCombAtG_map t (C.v i).valuationSubring.subtype hw
      rw [hgen] at h1
      have h2 : (fun l => spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.v i).valuationSubring.subtype) ≫ gi.tg l) =
          fun l => (M.pt (c l)).left := funext fun l => (hcl l).symm
      rw [h2] at h1
      exact (isCombAtG_iff_lie t M c _ _).1 h1
    · funext j
      simp [map_sum, Matrix.mulVec, dotProduct, hec, mul_comm]
  constructor
  · intro hv
    have hsub : Y.lieLat M i ≤ (D.lie i).comap e.toLinearMap.toAddMonoidHom := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro v ⟨w, hw, hvw⟩
      obtain ⟨a, ha, -⟩ := gi.basis w.left ((isTanAt_iff t (Y.x i) w).1 hw)
      obtain ⟨hbc, hea⟩ := key a w.left ha
      have hv' : v = ∑ l, (a l : K) • c l := M.inj (Over.OverMorphism.ext (hvw.trans hbc))
      show e v ∈ D.lie i
      rw [hDlie, hv', hea, Matrix.mulVec_mulVec, hΨΦ, Matrix.one_mulVec]
      intro j
      exact (a j).2
    exact hsub hv
  · intro hv
    have hint : ∀ j, C.v i ((lin (F.ψ i) 1).mulVec (e v) j) ≤ 1 := (hDlie i (e v)).1 hv
    let a : Fin d → (C.v i).valuationSubring := fun j => ⟨_, hint j⟩
    obtain ⟨Vi, _, _, ⟨Mi⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists X0 t.G (C.v i).valuationSubring (Y.x i)
    choose b hb using fun l =>
      Mi.onto (Over.homMk (gi.tg l) (gi.tan l).1) ((isTanAt_iff t (Y.x i) _).2 (gi.tan l))
    have hbl : ∀ l, (Mi.pt (b l)).left = gi.tg l := fun l => by rw [hb l]; rfl
    have hcomb : IsCombAtG t (Y.x i) gi.tg a (Mi.pt (∑ l, a l • b l)).left := by
      have h3 := (isCombAtG_iff_lie t Mi b a (Mi.pt (∑ l, a l • b l)).left).2 rfl
      have h2 : (fun l => (Mi.pt (b l)).left) = gi.tg := funext hbl
      rwa [h2] at h3
    obtain ⟨hbc, hea⟩ := key a _ hcomb
    have hsum : ∑ l, (a l : K) • c l = v := by
      apply e.injective
      rw [hea]
      show (lin (F.φ i) 1).mulVec ((lin (F.ψ i) 1).mulVec (e v)) = e v
      rw [Matrix.mulVec_mulVec, hΦΨ, Matrix.one_mulVec]
    refine AddSubgroup.subset_closure ⟨Mi.pt (∑ l, a l • b l), Mi.tan _, ?_⟩
    rw [← hsum]
    exact hbc.symm

end GlobalTheory.CompanionTheory.Ar.Conj.TopH2
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_lie_eigen_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (C : ACurve K) (z : Sp K ⟶ X0) (Y : CurveIn C z), Nonempty C.I → (∀ i, FibPF t (GlobalTheory.CompanionTheory.Ar.centre (Y.x i))) → ∀ (V : Type) [AddCommGroup V] [Module K V] (M : GlobalTheory.CompanionTheory.Ar.LieModel t.G z V) (r : 𝓞 E →+* Module.End K V), M.IsActOf t.act.act r → ∃ (d : ℕ) (D : ConjData C p (𝓞 E) d) (e : V ≃ₗ[K] (Fin d → K)), (∀ i v, v ∈ Y.lieLat M i ↔ e v ∈ D.lie i) ∧ ∀ a v, e (r a v) = (D.ρ a).mulVec (e v) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Conj.TopH2.lieLat_conjData
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj.CurveDegreeNonneg

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem subDeg_map {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {d : ℕ} (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup (Fin d → K))
    (e : V ≃ₗ[K] (Fin d → K)) (hL' : IsBun C L') (h : ∀ i v, v ∈ L i ↔ e v ∈ L' i)
    (U : Submodule K V) :
    subDeg C L' (U.map (e : V →ₗ[K] (Fin d → K))) = subDeg C L U := by
  have hb := (GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot K C (Fin d → K) L' (U.map (e : V →ₗ[K] (Fin d → K))) hL').1
  refine (GlobalTheory.CompanionTheory.Ar.Crv.DegEquiv.deg_equiv K C _ _ (sub C L' (U.map (e : V →ₗ[K] (Fin d → K)))) (sub C L U)
    (e.submoduleMap U).symm hb ?_).2.symm
  intro i x
  have hx : e ((e.submoduleMap U).symm x : V) = x := by
    have := (e.submoduleMap U).apply_symm_apply x
    exact congrArg Subtype.val this
  simp only [sub, AddSubgroup.mem_comap, LinearMap.toAddMonoidHom_coe, Submodule.subtype_apply]
  rw [h i, hx]

theorem mem_eigSp {K V O : Type} [Field K] [AddCommGroup V] [Module K V] [CommRing O]
    (r : O →+* Module.End K V) (σ : O →+* K) (v : V) :
    v ∈ eigSp r σ ↔ ∀ a, r a v = σ a • v := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem mem_eig {K V O : Type} [Field K] [AddCommGroup V] [Module K V]
    (ρ : O → V →ₗ[K] V) (χ : O → K) (v : V) :
    v ∈ eig ρ χ ↔ ∀ a, ρ a v = χ a • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

theorem map_eigSp {K V O : Type} [Field K] [AddCommGroup V] [Module K V] [CommRing O] {d : ℕ}
    (r : O →+* Module.End K V) (ρ : O →+* Matrix (Fin d) (Fin d) K) (σ : O →+* K)
    (e : V ≃ₗ[K] (Fin d → K)) (h : ∀ a v, e (r a v) = (ρ a).mulVec (e v)) :
    (eigSp r σ).map (e : V →ₗ[K] (Fin d → K)) = eig (fun a => Matrix.toLin' (ρ a)) (fun a => σ a) := by
  ext y
  obtain ⟨v, rfl⟩ := e.surjective y
  have h1 : e v ∈ (eigSp r σ).map (e : V →ₗ[K] (Fin d → K)) ↔ v ∈ eigSp r σ := by
    constructor
    · rintro ⟨u, hu, huv⟩
      have : u = v := e.injective huv
      exact this ▸ hu
    · exact fun hv => ⟨v, hv, rfl⟩
  rw [h1, mem_eigSp, mem_eig]
  refine forall_congr' fun a => ?_
  rw [Matrix.toLin'_apply, ← h, ← map_smul]
  exact e.injective.eq_iff.symm

theorem m2Curve_holds : CurveSemiAbelianConjecture := by
  intro E _ _ _ H X0 t hpow k K _ _ _ p _ _ hp C z Y hne hk hfib V _ _ _ M r hact T _ χ hsplit hχ
    j q w W L hj hq hW0 hL0 hWj hLq hgap
  letI := H.starRing
  obtain ⟨d, D, e, hlie, her⟩ := GlobalTheory.T.curve_lie_eigen_degree E H (fun _ => rfl) X0 t hpow K p C z Y hne hfib V M r hact
  let f : V →ₗ[K] (Fin d → K) := e
  have key := GlobalTheory.T.eigen_flag_slope_bound K C p (𝓞 E) k (T ⊕ T) T χ d D Sum.inl Sum.inr j q w
    (fun τ i => (W τ i).map f) (fun τ i => (L τ i).map f) hp hsplit hk
    (by
      have : (Sum.elim Sum.inl Sum.inr : T ⊕ T → T ⊕ T) = id := by ext (x | x) <;> rfl
      rw [this]; exact Function.bijective_id)
    (fun τ a => hχ τ a) hj hq
    (fun τ => by simp [hW0 τ]) (fun τ => by simp [hL0 τ])
    (fun τ => by rw [hWj τ]; exact map_eigSp r D.ρ _ e her)
    (fun τ => by rw [hLq τ]; exact map_eigSp r D.ρ _ e her) hgap
  simpa only [subDeg_map C (Y.lieLat M) D.lie e D.lie_bun hlie, f] using key

end GlobalTheory.CompanionTheory.Ar.Conj.CurveDegreeNonneg
end
end

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curveSemiAbelianConjecture : CurveSemiAbelianConjecture := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Conj.CurveDegreeNonneg.m2Curve_holds
end

section
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem m2Model_holds : RootLineDeRhamModel := GlobalTheory.T.rootLineDeRhamModel_of_curveSemiAbelian GlobalTheory.T.curveSemiAbelianConjecture

end GlobalTheory.CompanionTheory.Ar.Conj
end

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootLineDeRhamModel_holds : RootLineDeRhamModel := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Conj.m2Model_holds
end
