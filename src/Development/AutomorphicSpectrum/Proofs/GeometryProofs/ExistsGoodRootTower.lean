import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCptGenResidueFieldGeneric
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsReferenceGeometrySameGeneric
import Development.WeilBound.CoreStatements.CentralCharts.ReferenceGeometryHolomorphicInverse
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NefPolarizationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptBirationalArithVar
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeTensorPowerDegree
import Development.WeilBound.CoreStatements.CentralCharts.GapPolynomialPositive
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GapN
import Development.WeilBound.CoreStatements.VolumeEquality.ChartMeetsPoint
import Development.WeilBound.CoreStatements.VolumeEquality.CoverRootsSch
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRingHomComplexCompEqOfCountable
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointComponentLocalRing
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFibreNormDehomRoots
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EffectiveScaledWeightOfRetraction
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptProjectiveModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptLabelBases
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentGenericIsGenericPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointFactorsOpen
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFiniteExtensionPrimesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAfterFiniteExtension
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompComparisonLeft
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompComparisonMiddle
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenFieldExtension
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeStableUnderActionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralElementRegularStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCoordsOverField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPointsOpenIntegralCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCptGen_residue_field_generic : ∀ (X : Scheme.{0}), (∀ x : X, IsDomain (X.presheaf.stalk x)) → ∀ x : X, (∀ y : X, y ⤳ x → y = x) → IsCptGen (Ω := X.residueField x) (X.fromSpecResidueField x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.isCptGen_of_maximal | exact GlobalTheory.CompanionTheory.Ar.isCptGen_of_maximal | (intros; apply GlobalTheory.CompanionTheory.Ar.isCptGen_of_maximal <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_tensor_power_degree : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (I : Type) [Fintype I] (Λ : I → Lat ξ Ω) (T : Set (Cpt ξ)) (d : I → K → ℤ) (e : I → Ω), (∀ i, (Λ i).IsDegOn T y (d i) (e i)) → ∀ a : I → ℤ, (Lat.tens Λ a).IsDegOn T y (∑ i, a i • d i) (∏ i, e i ^ a i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lat.tens_isDegOn | exact GlobalTheory.CompanionTheory.Ar.Lat.tens_isDegOn | (intros; apply GlobalTheory.CompanionTheory.Ar.Lat.tens_isDegOn <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.ExRefEff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.global_reference_gap_positive : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → ∀ (G : RefGeo Y) (A : G.An) (ν : RootIx D → ℤ), (∀ τ (i k : Fin (D.p + D.q)), i < k → ν (τ, k) < ν (τ, i)) → 0 < MvPolynomial.eval (fun a => (gapN ν a : ℝ)) A.Sys.degPoly := by
  first | exact @AnalyticReference.gap_polynomial_positive | exact AnalyticReference.gap_polynomial_positive
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.ExRefEff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_reference_gap_positive : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → ∀ (G : RefGeo Y) (A : G.An) (ν : RootIx D → ℤ), (∀ τ (i k : Fin (D.p + D.q)), i < k → ν (τ, k) < ν (τ, i)) → 0 < MvPolynomial.eval (fun a => (gapN ν a : ℝ)) A.Sys.degPoly := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.global_reference_gap_positive
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.ExRefEff

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ExRefEff.BdForm

open MvPolynomial

section Forms

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

def bdeg (m : (Σ k, J k) →₀ ℕ) : K → ℕ := fun k => ∑ i, m ⟨k, i⟩

open Classical in

def bcomp (g : MRing J) (d : K → ℕ) : MRing J :=
  ∑ m ∈ g.support.filter (fun m => bdeg m = d), monomial m (coeff m g)

open Classical in
theorem coeff_bcomp (g : MRing J) (d : K → ℕ) (m : (Σ k, J k) →₀ ℕ) :
    coeff m (bcomp g d) = if bdeg m = d then coeff m g else 0 := by
  rw [bcomp, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, mem_support_iff]
  by_cases h : bdeg m = d <;> by_cases h' : coeff m g = 0 <;> simp [h, h']

theorem bcomp_homog (g : MRing J) (d : K → ℕ) : IsMultiHomog (bcomp g d) d := by
  classical
  intro m hm k
  rw [mem_support_iff, coeff_bcomp] at hm
  have h : bdeg m = d := by
    by_contra h
    exact hm (if_neg h)
  exact congrFun h k

theorem sum_bcomp [DecidableEq (K → ℕ)] (g : MRing J) : ∑ d ∈ g.support.image bdeg, bcomp g d = g := by
  classical
  ext m
  rw [coeff_sum]
  by_cases h : coeff m g = 0
  · rw [h]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [coeff_bcomp]
    split_ifs
    · exact h
    · rfl
  · rw [Finset.sum_eq_single (bdeg m)]
    · rw [coeff_bcomp, if_pos rfl]
    · intro d _ hd
      rw [coeff_bcomp, if_neg (Ne.symm hd)]
    · intro hn
      exact absurd (Finset.mem_image_of_mem _ (mem_support_iff.2 h)) hn

theorem bcomp_eq_zero [DecidableEq (K → ℕ)] (g : MRing J) {d : K → ℕ} (h : d ∉ g.support.image bdeg) : bcomp g d = 0 := by
  classical
  ext m
  rw [coeff_bcomp, coeff_zero]
  split_ifs with e
  · by_contra h0
    exact h (e ▸ Finset.mem_image_of_mem _ (mem_support_iff.2 h0))
  · rfl

theorem exists_aeval_bcomp_ne {Ω : Type} [Field Ω] (t : (Σ k, J k) → Ω) (g : MRing J) (h : aeval t g ≠ 0) :
    ∃ d : K → ℕ, aeval t (bcomp g d) ≠ 0 := by
  classical
  rw [← sum_bcomp g, map_sum] at h
  obtain ⟨d, -, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨d, hd⟩

theorem aeval_bcomp_eq_zero (w : (Σ k, J k) → ℂ) (g : MRing J)
    (h : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → aeval (fun p => w p * c p.1) g = 0) (d : K → ℕ) :
    aeval w (bcomp g d) = 0 := by
  classical
  have h0 : mConeMap w g = 0 := by
    refine funext_set (fun _ => ({0}ᶜ : Set ℂ)) (fun _ => (Set.finite_singleton (0 : ℂ)).infinite_compl) fun c hc => ?_
    rw [map_zero, GroundTheory.Heights₂.Heights.HilbertSamuel.FibreNormDehomRoots.eval_mConeMap]
    exact h c fun k => hc k (Set.mem_univ k)
  have h1 : mConeMap w g = ∑ d' ∈ g.support.image bdeg, C (aeval w (bcomp g d')) * ∏ k, X k ^ d' k := by
    conv_lhs => rw [← sum_bcomp g, map_sum]
    exact Finset.sum_congr rfl fun d' _ =>
      GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mConeMap_eq_of_isMultiHomog w (bcomp_homog g d')
  have hm : ∀ d' : K → ℕ, (∏ k, (X k : MvPolynomial K ℂ) ^ d' k) = monomial (Finsupp.equivFunOnFinite.symm d') 1 := by
    intro d'
    rw [monomial_eq, C_1, _root_.one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rfl
  by_cases hd : d ∈ g.support.image bdeg
  · have h2 := congrArg (coeff (Finsupp.equivFunOnFinite.symm d)) (h1.symm.trans h0)
    rw [coeff_sum, coeff_zero] at h2
    simp only [hm, coeff_C_mul, coeff_monomial, mul_ite, _root_.mul_one, mul_zero, EmbeddingLike.apply_eq_iff_eq] at h2
    rwa [Finset.sum_ite_eq', if_pos hd] at h2
  · rw [bcomp_eq_zero g hd, map_zero]

theorem mem_chartLat {Ω : Type} [Field Ω] {y : (Σ k, J k) → Ω} {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d) :
    aeval y g ∈ chartLat y (fun κ => (d κ : ℤ)) 1 := by
  intro c _
  have hprod : ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (d k : ℤ))) = ∏ k, (y ⟨k, c k⟩)⁻¹ ^ d k := by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Nat.cast_one, _root_.one_mul, zpow_neg, zpow_natCast, inv_pow]
  rw [hprod, ← GroundTheory.Heights₂.Heights.HilbertSamuel.FibreNormDehomRoots.aeval_scale hg y (fun k => (y ⟨k, c k⟩)⁻¹),
    chartRingZ, Algebra.adjoin_range_eq_range_aeval]
  refine ⟨g, ?_⟩
  simp only [div_eq_mul_inv]
  rfl

theorem dehom_eq {Ω : Type} [Field Ω] (y : (Σ k, J k) → Ω) {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d)
    (c : ∀ k, J k) :
    aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-((1 : ℕ) * (d k : ℤ))) = aeval (fun p => y p / y ⟨p.1, c p.1⟩) g := by
  have hprod : ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (d k : ℤ))) = ∏ k, (y ⟨k, c k⟩)⁻¹ ^ d k := by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Nat.cast_one, _root_.one_mul, zpow_neg, zpow_natCast, inv_pow]
  rw [hprod, ← GroundTheory.Heights₂.Heights.HilbertSamuel.FibreNormDehomRoots.aeval_scale hg y (fun k => (y ⟨k, c k⟩)⁻¹)]
  simp only [div_eq_mul_inv]

end Forms

theorem nonempty_hom_complex (k : Type) [Field k] [CharZero k] [Countable k] : Nonempty (k →+* ℂ) :=
  (GlobalTheory.nonempty_algHom_complex_of_countable ℤ k).map AlgHom.toRingHom

theorem exists_hom_ker {A : Type} [CommRing A] [Countable A] (P : Ideal A) [P.IsPrime]
    (hP : ∀ r : ℕ, r.Prime → (r : A) ∉ P) : ∃ ψ : A →+* ℂ, ∀ a, ψ a = 0 ↔ a ∈ P := by
  let B := A ⧸ P
  let F := FractionRing B
  have hinj : Function.Injective (algebraMap B F) := IsFractionRing.injective B F
  have hB : Countable B := Quotient.countable
  have hF : Countable F := by
    refine Function.Surjective.countable (f := fun q : B × B => algebraMap B F q.1 / algebraMap B F q.2) ?_
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    exact ⟨(a, b), rfl⟩
  have hc : CharZero F := by
    obtain ⟨q, hq⟩ := CharP.exists F
    rcases CharP.char_is_prime_or_zero F q with h | h
    · exfalso
      refine hP q h ?_
      have h1 : algebraMap B F (q : B) = 0 := by
        rw [map_natCast]
        exact (CharP.cast_eq_zero_iff F q q).2 dvd_rfl
      have h2 : (q : B) = 0 := hinj (h1.trans (map_zero _).symm)
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact h2
    · subst h
      exact CharP.charP_to_charZero F
  obtain ⟨j⟩ := nonempty_hom_complex F
  refine ⟨j.comp ((algebraMap B F).comp (Ideal.Quotient.mk P)), fun a => ?_⟩
  simp only [RingHom.comp_apply]
  rw [map_eq_zero_iff _ j.injective, map_eq_zero_iff _ hinj, Ideal.Quotient.eq_zero_iff_mem]

section Points

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem coordsAt_scale {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} {z : Spec (CommRingCat.of ℂ) ⟶ X}
    {w : (Σ k, J k) → ℂ} (h : CoordsAt ξ y z w) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) :
    CoordsAt ξ y z (fun p => w p * c p.1) := by
  refine ⟨fun k => (h.1 k).imp fun i hi => hi.mul (Ne.isUnit (hc k)), fun k i hu => ?_⟩
  have hu' : IsUnit (w ⟨k, i⟩) := Ne.isUnit (left_ne_zero_of_mul hu.ne_zero)
  obtain ⟨h0, h1⟩ := h.2 k i hu'
  refine ⟨h0, fun j => ?_⟩
  obtain ⟨r, hr, e⟩ := h1 j
  refine ⟨r, hr, ?_⟩
  show w ⟨k, j⟩ * c k = r * (w ⟨k, i⟩ * c k)
  rw [e, _root_.mul_assoc]

theorem isUnit_stalk_iff (hξ : IsCptGen ξ) (p : Cpt ξ) (s : X.presheaf.stalk p.1) :
    IsUnit s ↔ unitAt ξ p (genMap ξ p s) := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨(u.isUnit.map (genMap ξ p)).ne_zero, ⟨_, rfl⟩, ⟨((u⁻¹ : (X.presheaf.stalk p.1)ˣ) : X.presheaf.stalk p.1),
      map_units_inv (genMap ξ p) u⟩⟩
  · rintro ⟨h0, -, t, ht⟩
    refine isUnit_iff_exists_inv.2 ⟨t, hξ.inj p ?_⟩
    rw [map_mul, ht, mul_inv_cancel₀ h0, map_one]

theorem isUnit_stalk_point {z : Spec (CommRingCat.of ℂ) ⟶ X} (s : X.presheaf.stalk (centre z)) :
    IsUnit s ↔ (Scheme.stalkClosedPointTo z).hom s ≠ 0 :=
  ⟨fun h => (h.map (Scheme.stalkClosedPointTo z).hom).ne_zero, fun h =>
    (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit s (isUnit_iff_ne_zero.mpr h)⟩

theorem centre_eq_of_ker {κ : Type} {x : κ → Ω} (T : CoordTie ℤ ξ x) (c : κ) (hc : x c ≠ 0) (p : Cpt ξ)
    (hp : InChart ξ x c p) (ψ : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* ℂ)
    (hψ : ∀ a, ψ a = 0 ↔ ¬ unitAt ξ p (a : Ω)) {z : Spec (CommRingCat.of ℂ) ⟶ X} (hz : genPt ξ ⤳ centre z)
    (hval : ∀ a : Algebra.adjoin ℤ (Set.range fun j => x j / x c), ValAt ξ z (a : Ω) (ψ a)) : centre z = p.1 := by
  obtain ⟨U, hU, hmem⟩ := T.affine c hc
  have hpU : p.1 ∈ U := (hmem _).2 ⟨p.2, hp⟩
  have hzU : centre z ∈ U := by
    refine (hmem _).2 ⟨hz, hc, fun j => ?_⟩
    obtain ⟨h, s, e, -⟩ := hval ⟨x j / x c, Algebra.subset_adjoin ⟨j, rfl⟩⟩
    exact ⟨s, e⟩
  have hg : genPt ξ ∈ U := p.2.mem_open U.isOpen hpU
  let q : Cpt ξ := ⟨centre z, hz⟩
  have key : ∀ f : Γ(X, U), p.1 ∈ X.basicOpen f ↔ centre z ∈ X.basicOpen f := by
    intro f
    have e1 := SheetDecomposition.CovSch.genMap_germ' p U hpU hg f
    have e2 := SheetDecomposition.CovSch.genMap_germ' q U hzU hg f
    have ha : SheetDecomposition.CovSch.val ξ U hg f ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) :=
      (T.ring c hc _).2 fun r hr => ⟨_, SheetDecomposition.CovSch.genMap_germ' r U ((hmem _).2 ⟨r.2, hr⟩) hg f⟩
    obtain ⟨h, s, e3, e4⟩ := hval ⟨_, ha⟩
    have hs : s = X.presheaf.germ U (centre z) hzU f := T.gen.inj q (e3.trans e2.symm)
    rw [Scheme.mem_basicOpen _ f _ hpU, Scheme.mem_basicOpen _ f _ hzU, isUnit_stalk_iff T.gen p, e1, ← hs,
      isUnit_stalk_point, e4, ne_eq, hψ, not_not]
  have hP : ∀ (t : U) (f : Γ(X, U)), f ∉ (hU.primeIdealOf t).asIdeal ↔ t.1 ∈ X.basicOpen f := by
    intro t f
    have h1 : hU.fromSpec (hU.primeIdealOf t) = t.1 := hU.fromSpec_primeIdealOf t
    have h2 : hU.primeIdealOf t ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f ↔ t.1 ∈ X.basicOpen f := by
      rw [← h1]
      rfl
    rw [hU.fromSpec_preimage_basicOpen f] at h2
    exact h2
  have hEq : hU.primeIdealOf ⟨p.1, hpU⟩ = hU.primeIdealOf ⟨centre z, hzU⟩ := by
    refine PrimeSpectrum.ext (Ideal.ext fun f => ?_)
    have h1 := hP ⟨p.1, hpU⟩ f
    have h2 := hP ⟨centre z, hzU⟩ f
    exact not_iff_not.1 (h1.trans ((key f).trans h2.symm))
  have h1 : hU.fromSpec (hU.primeIdealOf ⟨p.1, hpU⟩) = p.1 := hU.fromSpec_primeIdealOf ⟨p.1, hpU⟩
  have h2 : hU.fromSpec (hU.primeIdealOf ⟨centre z, hzU⟩) = centre z := hU.fromSpec_primeIdealOf ⟨centre z, hzU⟩
  rw [← h2, ← hEq, h1]

theorem exists_point_at {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
    (T : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (cc : ∀ k, J k) (p : Cpt ξ)
    (hp : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) cc p)
    (hchar : ∀ r : ℕ, r.Prime → unitAt ξ p (r : Ω)) :
    ∃ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), centre z = p.1 ∧ CoordsAt ξ y z w ∧
      ∀ g : MRing J, unitAt ξ p (aeval (fun s => y s / y ⟨s.1, cc s.1⟩) g) → aeval w g ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : ((k : K) → J k) → Ω, x = fun c' => ∏ k, y ⟨k, c' k⟩ := ⟨_, rfl⟩
  rw [← hx] at T hp
  have hc : x cc ≠ 0 := hp.1
  have hy : ∀ k, y ⟨k, cc k⟩ ≠ 0 := fun k => by
    rw [hx] at hc
    exact (Finset.prod_ne_zero_iff.1 hc) k (Finset.mem_univ k)
  have hreg : ∀ a : Algebra.adjoin ℤ (Set.range fun j => x j / x cc), (a : Ω) ∈ regAt ξ p :=
    fun a => (T.ring cc hc a).1 a.2 p hp
  let inc : Algebra.adjoin ℤ (Set.range fun j => x j / x cc) →+* regAt ξ p :=
    { toFun := fun a => ⟨a, hreg a⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  haveI : IsLocalRing (regAt ξ p) := GlobalTheory.CompanionTheory.Ar.Flat.CPoint.isLocalRing_regAt X Ω ξ T.gen p
  let P : Ideal (Algebra.adjoin ℤ (Set.range fun j => x j / x cc)) := (IsLocalRing.maximalIdeal (regAt ξ p)).comap inc
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have hPmem : ∀ a, a ∈ P ↔ ¬ unitAt ξ p (a : Ω) := by
    intro a
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_iff_not]
    constructor
    · intro h
      obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 h
      have hb' : (a : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
      have h0 : (a : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one hb'
      exact ⟨h0, hreg a, by rw [inv_eq_of_mul_eq_one_right hb']; exact b.2⟩
    · rintro ⟨h0, -, h2⟩
      exact isUnit_iff_exists_inv.2 ⟨⟨_, h2⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
  have hcount : Countable (Algebra.adjoin ℤ (Set.range fun j => x j / x cc)) := by
    have hcm : Countable (MvPolynomial ((k : K) → J k) ℤ) := by
      rw [← Cardinal.mk_le_aleph0_iff]
      refine MvPolynomial.cardinalMk_le_max.trans ?_
      first
        | exact max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl
        | exact max_le (max_le (Cardinal.lift_le_aleph0.2 Cardinal.mk_le_aleph0) (Cardinal.lift_le_aleph0.2 Cardinal.mk_le_aleph0)) le_rfl
    have hs : (((Algebra.adjoin ℤ (Set.range fun j => x j / x cc) : Subalgebra ℤ Ω)) : Set Ω).Countable := by
      rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.coe_range]
      exact Set.countable_range _
    exact hs.to_subtype
  have hP : ∀ r : ℕ, r.Prime → (r : Algebra.adjoin ℤ (Set.range fun j => x j / x cc)) ∉ P := by
    intro r hr h
    refine (hPmem _).1 h ?_
    have := hchar r hr
    simpa using this
  obtain ⟨ψ, hψ⟩ := exists_hom_ker P hP
  obtain ⟨z, hz, hval⟩ := SheetDecomposition.ChartForm.exists_point_hom T cc hc ψ
  have htA : ∀ s : Σ k, J k, y s / y ⟨s.1, cc s.1⟩ ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x cc) := by
    rintro ⟨k, i⟩
    have h1 : y ⟨k, i⟩ / y ⟨k, cc k⟩ = x (Function.update cc k i) / x cc := by
      rw [hx]
      exact (GlobalTheory.CompanionTheory.Ar.TiePoints.ratio_update y cc hy k i).symm
    rw [h1]
    exact Algebra.subset_adjoin ⟨_, rfl⟩
  let t' : (Σ k, J k) → Algebra.adjoin ℤ (Set.range fun j => x j / x cc) := fun s => ⟨_, htA s⟩
  refine ⟨z, fun s => ψ (t' s), centre_eq_of_ker T cc hc p hp ψ (fun a => (hψ a).trans (hPmem a)) hz hval,
    SheetDecomposition.CovSch.coordsAt_of_val cc hy (fun s => hval (t' s)) (fun k => ?_), fun g hg h0 => ?_⟩
  · have : t' ⟨k, cc k⟩ = 1 := Subtype.ext (div_self (hy k))
    rw [this, map_one]
  · have e1 : aeval (fun s => ψ (t' s)) g = ψ (aeval t' g) :=
      (GroundTheory.Heights₂.Heights.HilbertSamuel.FibreNormDehomRoots.ringHom_aeval ψ t' g).symm
    have e2 : ((aeval t' g : Algebra.adjoin ℤ (Set.range fun j => x j / x cc)) : Ω) =
        aeval (fun s => y s / y ⟨s.1, cc s.1⟩) g :=
      GroundTheory.Heights₂.Heights.HilbertSamuel.FibreNormDehomRoots.ringHom_aeval (Algebra.adjoin ℤ (Set.range fun j => x j / x cc)).val.toRingHom t' g
    rw [e1] at h0
    refine (hψ _).1 h0 |> (hPmem _).1 <| ?_
    rw [e2]
    exact hg

end Points

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β₀ : O →+* c.F} {Y : Model Xo c β₀}

theorem exists_chart_form (G : RefGeo Y) : ∃ (c : ∀ k, G.J k) (g : MRing G.J), g ∈ G.bd ∧ (∀ k, G.y ⟨k, c k⟩ ≠ 0) ∧
    aeval (fun p => G.y p / G.y ⟨p.1, c p.1⟩) g ≠ 0 := by
  obtain ⟨c, hc⟩ := G.𝔐.tie.cover ⟨genPt G.𝔐.ξ, specializes_rfl⟩
  have hy : ∀ k, G.y ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hc.1) k (Finset.mem_univ k)
  by_contra hno
  have hz : ∀ g ∈ G.bd, aeval (fun p => G.y p / G.y ⟨p.1, c p.1⟩) g = 0 := by
    intro g hg
    by_contra h
    exact hno ⟨c, g, hg, hy, h⟩
  obtain ⟨m, f, a, -, -, hsum, hS⟩ := G.snc c hy
  obtain ⟨l, hl⟩ : ∃ l, f l ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h] at hsum
  obtain ⟨-, z, n, -, hli, -, hq⟩ := hS l hl _ rfl
  obtain ⟨i, -, hi⟩ := (hq ⊥ Ideal.isPrime_bot).1 fun g hg s hs =>
    Ideal.mem_bot.2 (Subtype.ext (hs.trans (hz g hg)))
  have h1 := hli.ne_zero i
  rw [Ideal.mem_bot.1 hi, map_zero] at h1
  exact h1 rfl

end Main

theorem bd_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β₀ : O →+* c.F) (Y : Model Xo c β₀) (G : RefGeo Y), ∃ (β : MRing G.J) (dβ : G.K → ℕ), IsMultiHomog β dβ ∧ β ∉ mCoordIdeal G.y ∧ MvPolynomial.aeval G.y β ≠ 0 ∧ MvPolynomial.aeval G.y β ∈ chartLat G.y (fun κ => (dβ κ : ℤ)) 1 ∧ ∀ p : Cpt G.𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre G.𝔐.ξ r p) → p.1 ∉ abLocus G.𝔐.t.G → ∀ cc : ∀ k, G.J k, InChart G.𝔐.ξ (fun c' : ∀ k, G.J k => ∏ k, G.y ⟨k, c' k⟩) cc p → ¬ unitAt G.𝔐.ξ p (MvPolynomial.aeval G.y β * ∏ k, G.y ⟨k, cc k⟩ ^ (-((1 : ℕ) * (dβ k : ℤ)))) := by
  intro E _ _ _ H D l Xo c O _ β₀ Y G
  obtain ⟨c₀, g, hg, hy, hne⟩ := exists_chart_form G
  obtain ⟨d, hd⟩ := exists_aeval_bcomp_ne _ g hne
  have hhom := bcomp_homog g d
  have hyne : aeval G.y (bcomp g d) ≠ 0 := by
    intro h0
    rw [← dehom_eq G.y hhom c₀, h0, zero_mul] at hd
    exact hd rfl
  refine ⟨bcomp g d, d, hhom, fun hm => hyne ?_, hyne, mem_chartLat hhom, fun p hchar hab cc hp hu => ?_⟩
  · have h1 := GroundTheory.Heights₂.Heights.HilbertSamuel.FibreNormDehomRoots.aeval_eq_zero_of_mem hm (fun _ => 1)
    simpa using h1
  · rw [dehom_eq G.y hhom cc] at hu
    obtain ⟨z, w, hcen, hco, hval⟩ := exists_point_at G.𝔐.tie cc p hp (fun r hr => not_not.1 (hchar r hr))
    refine hval _ hu (aeval_bcomp_eq_zero w g (fun t ht => ?_) d)
    have hnot : ¬ G.𝔐.Interior z := fun hi => hab (hcen ▸ hi)
    have h1 := (G.bd_iff z _ (coordsAt_scale hco ht)).2 hnot
    have h2 := h1.2 g hg
    rwa [MvPolynomial.eval_map] at h2

end GlobalTheory.CompanionTheory.Ar.ExRefEff.BdForm
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.ExRefEff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reference_geometry_multihomog_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β₀ : O →+* c.F) (Y : Model Xo c β₀) (G : RefGeo Y), ∃ (β : MRing G.J) (dβ : G.K → ℕ), IsMultiHomog β dβ ∧ β ∉ mCoordIdeal G.y ∧ MvPolynomial.aeval G.y β ≠ 0 ∧ MvPolynomial.aeval G.y β ∈ chartLat G.y (fun κ => (dβ κ : ℤ)) 1 ∧ ∀ p : Cpt G.𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre G.𝔐.ξ r p) → p.1 ∉ abLocus G.𝔐.t.G → ∀ cc : ∀ k, G.J k, InChart G.𝔐.ξ (fun c' : ∀ k, G.J k => ∏ k, G.y ⟨k, c' k⟩) cc p → ¬ unitAt G.𝔐.ξ p (MvPolynomial.aeval G.y β * ∏ k, G.y ⟨k, cc k⟩ ^ (-((1 : ℕ) * (dβ k : ℤ)))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.ExRefEff.BdForm.bd_form
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.ExRefEff

theorem tele (F : ℕ → ℤ) (k M : ℕ) (hk : k ≤ M) :
    ∑ n ∈ Finset.range M, (if k ≤ n then F n - F (n + 1) else 0) = F k - F M := by
  induction M, hk using Nat.le_induction with
  | base =>
    rw [Finset.sum_eq_zero]
    · simp
    · intro n hn
      rw [if_neg (by simpa using hn)]
  | succ M hM ih =>
    rw [Finset.sum_range_succ, ih, if_pos hM]
    ring

theorem abel (N : ℕ) (f x : Fin N → ℤ) :
    ∑ i : Fin N, (f i - if h : (i : ℕ) + 1 < N then f ⟨i + 1, h⟩ else 0) * ∑ k ∈ Finset.Iic i, x k =
      ∑ k, f k * x k := by
  classical
  let F : ℕ → ℤ := fun n => if h : n < N then f ⟨n, h⟩ else 0
  have hF : ∀ i : Fin N, (f i - if h : (i : ℕ) + 1 < N then f ⟨i + 1, h⟩ else 0) = F i - F (i + 1) := by
    intro i
    simp [F, i.2]
  have hFN : F N = 0 := by simp [F]
  have h1 : ∀ k : Fin N, ∑ i ∈ Finset.Ici k, (F i - F (i + 1)) = f k := by
    intro k
    have h2 := tele F k N k.2.le
    rw [hFN, sub_zero, ← Fin.sum_univ_eq_sum_range (fun n => if (k : ℕ) ≤ n then F n - F (n + 1) else 0) N] at h2
    have h3 : Finset.Ici k = Finset.univ.filter (fun i => k ≤ i) := by ext i; simp
    rw [h3, Finset.sum_filter]
    simp only [Fin.le_def]
    rw [h2]
    simp [F, k.2]
  simp_rw [hF, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun k => Finset.Ici k) (by intro i k; simp)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_mul, h1]

section Chart

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K]
  {J : K → Type} {y : (Σ k, J k) → Ω}

theorem ne_of_chart {p : Cpt ξ} {c : ∀ k, J k} (h : InChart ξ (fun c' : ∀ k, J k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) :
    y ⟨k, c k⟩ ≠ 0 :=
  (Finset.prod_ne_zero_iff.1 h.1) k (Finset.mem_univ k)

theorem ratio_mem {p : Cpt ξ} {c : ∀ k, J k} (h : InChart ξ (fun c' : ∀ k, J k => ∏ k, y ⟨k, c' k⟩) c p)
    (k : K) (i : J k) : y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ regAt ξ p := by
  classical
  have h1 := h.2 (Function.update c k i)
  have h2 : (∏ l, y ⟨l, Function.update c k i l⟩) / ∏ l, y ⟨l, c l⟩ = y ⟨k, i⟩ / y ⟨k, c k⟩ := by
    rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
    · simp
    · intro l _ hl
      rw [Function.update_of_ne hl, div_self (ne_of_chart h l)]
    · simp
  rwa [h2] at h1

theorem chart_update {p : Cpt ξ} {c : ∀ k, J k} (h : InChart ξ (fun c' : ∀ k, J k => ∏ k, y ⟨k, c' k⟩) c p)
    [DecidableEq K] (k₀ : K) (i : J k₀) (hi : InChart ξ (fun i' : J k₀ => y ⟨k₀, i'⟩) i p) :
    InChart ξ (fun c' : ∀ k, J k => ∏ k, y ⟨k, c' k⟩) (Function.update c k₀ i) p := by
  have hne : ∀ k, y ⟨k, Function.update c k₀ i k⟩ ≠ 0 := by
    intro k
    by_cases hk : k = k₀
    · subst hk
      simpa using hi.1
    · rw [Function.update_of_ne hk]
      exact ne_of_chart h k
  refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => hne k, fun c' => ?_⟩
  show (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, Function.update c k₀ i k⟩ ∈ regAt ξ p
  rw [← Finset.prod_div_distrib]
  refine Subring.prod_mem _ fun k _ => ?_
  by_cases hk : k = k₀
  · subst hk
    simpa using hi.2 (c' k)
  · rw [Function.update_of_ne hk]
    exact ratio_mem h k (c' k)

theorem chartRing_mem {p : Cpt ξ} {c : ∀ k, J k} (h : InChart ξ (fun c' : ∀ k, J k => ∏ k, y ⟨k, c' k⟩) c p)
    {a : Ω} (ha : a ∈ chartRingZ y c) : a ∈ regAt ξ p := by
  unfold chartRingZ at ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨q, rfl⟩ := hx
    exact ratio_mem h q.1 q.2
  | algebraMap r => simpa using intCast_mem (regAt ξ p) r
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

end Chart

section Ref

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β₀ : O →+* c.F} {Y : Model Xo c β₀}

theorem comb_a {G : RefGeo Y} (A : G.An) (ν : RootIx D → ℤ) (κ : G.K) :
    (PB.combLine A.Re.ref (gapN ν)).a κ = -∑ r, ν r * G.xdeg r κ := by
  rw [PB.combLine_a, Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
  simp only [gapN, zero_mul, zero_add]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h := abel (D.p + D.q) (fun i => ν (τ, i)) (fun k => G.xdeg (τ, k) κ)
  rw [← h, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [A.fund_deg τ i]
  simp [Finset.sum_apply]

open Classical in

theorem isEff_of_data (G : RefGeo Y) (n : RootIx D → ℤ) (e : G.Ω) (b : G.Ω) (dβ : G.K → ℕ)
    (i₀ : ∀ k, G.J k) (hi₀ : ∀ k, G.y ⟨k, i₀ k⟩ ≠ 0)
    (he : e ∈ chartLat G.y (fun κ => (∑ r, (-n r) • G.xdeg r) κ - 1 - dβ κ) 1)
    (hb : b ∈ chartLat G.y (fun κ => (dβ κ : ℤ)) 1)
    (hbd : ∀ p : Cpt G.𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre G.𝔐.ξ r p) → p.1 ∉ abLocus G.𝔐.t.G →
      ∀ cc : ∀ k, G.J k, InChart G.𝔐.ξ (fun c' : ∀ k, G.J k => ∏ k, G.y ⟨k, c' k⟩) cc p →
        ¬ unitAt G.𝔐.ξ p (b * ∏ k, G.y ⟨k, cc k⟩ ^ (-((1 : ℕ) * (dβ k : ℤ))))) :
    G.IsEff n 1 (e * b * (∏ κ ∈ Finset.univ.erase G.k₀, G.y ⟨κ, i₀ κ⟩) * ∏ r, G.e r ^ (-n r)) := by
  classical
  have hDeg := GlobalTheory.T.lattice_tensor_power_degree _ _ G.𝔐.ξ G.K G.J G.y _ G.Fl.rootLat Set.univ G.xdeg G.e G.lines (fun r => -n r)
  intro p hp i t hi ht
  obtain ⟨c0, hc0⟩ := G.𝔐.tie.cover p
  have hc := chart_update hc0 G.k₀ i hi
  set cc := Function.update c0 G.k₀ i with hcc
  have hcck : cc G.k₀ = i := by simp [hcc]
  have hne := ne_of_chart hc
  have hgen := hDeg.2 p (Set.mem_univ _) cc hc
  set a : G.K → ℤ := ∑ r, (-n r) • G.xdeg r with ha
  set E₀ : G.Ω := ∏ r, G.e r ^ (-n r) with hE₀
  have hE₀0 : E₀ ≠ 0 := hDeg.1
  set Pa : G.Ω := ∏ k, G.y ⟨k, cc k⟩ ^ a k with hPa
  have hPa0 : Pa ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hne k)
  have hsp : (Lat.tens G.Fl.rootLat fun r => -n r) p = Submodule.span (regAt G.𝔐.ξ p) {Pa * E₀} := by
    rw [hgen, smul_eq_mul]
  have hg0 : Pa * E₀ ≠ 0 := mul_ne_zero hPa0 hE₀0
  obtain ⟨ht0, htp⟩ := ht
  have hgt : Pa * E₀ ∈ Submodule.span (regAt G.𝔐.ξ p) {t} := by
    rw [← htp, hsp]; exact Submodule.mem_span_singleton_self _
  obtain ⟨v, hv⟩ := Submodule.mem_span_singleton.1 hgt
  have hv' : (v : G.Ω) * t = Pa * E₀ := hv
  have hv0 : (v : G.Ω) ≠ 0 := fun h => hg0 (by rw [← hv', h, zero_mul])
  have hvm : (v : G.Ω) ∈ regAt G.𝔐.ξ p := v.2
  have hW := chartRing_mem hc (he cc hne)
  have hB := chartRing_mem hc (hb cc hne)
  set Q1 : G.Ω := ∏ k, G.y ⟨k, cc k⟩ ^ (-(((1 : ℕ) : ℤ) * (a k - 1 - dβ k))) with hQ1
  set Q2 : G.Ω := ∏ k, G.y ⟨k, cc k⟩ ^ (-(((1 : ℕ) : ℤ) * (dβ k : ℤ))) with hQ2
  set M : G.Ω := ∏ κ ∈ Finset.univ.erase G.k₀, G.y ⟨κ, i₀ κ⟩ with hM
  set Ec : G.Ω := ∏ κ ∈ Finset.univ.erase G.k₀, G.y ⟨κ, cc κ⟩ with hEc
  have hEc0 : Ec ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hne k
  have hMc : M / Ec ∈ regAt G.𝔐.ξ p := by
    rw [hM, hEc, ← Finset.prod_div_distrib]
    exact Subring.prod_mem _ fun k _ => ratio_mem hc k (i₀ k)
  have hP : Q1 * Q2 * Pa = G.y ⟨G.k₀, i⟩ * Ec := by
    have h1 : G.y ⟨G.k₀, i⟩ * Ec = ∏ k, G.y ⟨k, cc k⟩ := by
      rw [hEc, ← Finset.mul_prod_erase Finset.univ (fun k => G.y ⟨k, cc k⟩) (Finset.mem_univ G.k₀), hcck]
    rw [h1, hQ1, hQ2, hPa, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hne k), ← zpow_add₀ (hne k)]
    have : -(((1 : ℕ) : ℤ) * (a k - 1 - dβ k)) + -(((1 : ℕ) : ℤ) * (dβ k : ℤ)) + a k = 1 := by
      push_cast; ring
    rw [this, zpow_one]
  have hX : e * b * M * E₀ * G.y ⟨G.k₀, i⟩ ^ 1 / t =
      (v : G.Ω) * ((e * Q1) * (b * Q2) * (M / Ec)) := by
    have ht' : t = Pa * E₀ / v := by field_simp; rw [mul_comm]; exact hv'
    have hq : Q1 * Q2 = G.y ⟨G.k₀, i⟩ * Ec / Pa := by field_simp; exact hP
    have : (e * Q1) * (b * Q2) * (M / Ec) = e * b * (Q1 * Q2) * (M / Ec) := by ring
    rw [this, hq, ht']
    field_simp
  rw [hX]
  refine ⟨mul_mem hvm (mul_mem (mul_mem hW hB) hMc), fun hab hu => ?_⟩
  refine hbd p hp hab cc hc ⟨?_, hB, ?_⟩
  · intro h0
    apply hu.1
    rw [h0]; simp
  · have hb0 : b * Q2 ≠ 0 := fun h0 => hu.1 (by rw [h0]; simp)
    have : (b * Q2)⁻¹ = ((v : G.Ω) * ((e * Q1) * (b * Q2) * (M / Ec)))⁻¹ * ((v : G.Ω) * (e * Q1) * (M / Ec)) := by
      have hx := hu.1
      have hx1 : (v : G.Ω) * (e * Q1) * (M / Ec) ≠ 0 := by
        intro h0
        apply hx
        have : (v : G.Ω) * ((e * Q1) * (b * Q2) * (M / Ec)) = ((v : G.Ω) * (e * Q1) * (M / Ec)) * (b * Q2) := by ring
        rw [this, h0, zero_mul]
      have : (v : G.Ω) * ((e * Q1) * (b * Q2) * (M / Ec)) = ((v : G.Ω) * (e * Q1) * (M / Ec)) * (b * Q2) := by ring
      have key : ∀ w z : G.Ω, w ≠ 0 → z ≠ 0 → z⁻¹ = (w * z)⁻¹ * w := by
        intro w z hw hz
        field_simp
      rw [this]
      exact key _ _ hx1 hb0
    rw [this]
    exact mul_mem hu.2.2 (mul_mem (mul_mem hvm hW) hMc)

end Ref

theorem exists_eff : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → ∀ (G : RefGeo Y), Nonempty G.An → ∀ ν : RootIx D → ℤ, (∀ τ (i k : Fin (D.p + D.q)), i < k → ν (τ, k) < ν (τ, i)) → ∃ (k q' : ℕ) (s : G.Ω), 0 < k ∧ 0 < q' ∧ s ≠ 0 ∧ G.IsEff (fun r => (k * q' : ℕ) * ν r) q' s := by
  intro hG E _ _ _ H D Xo l c Y hgl hp hq G ⟨A⟩ ν hν
  classical
  have hIn : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  haveI : Nonempty G.K := ⟨G.k₀⟩
  have hb : Birational G.y := (GlobalTheory.T.hodge_cpt_birational_arith_var E H D l (Xo l) c (𝓞 c.F) (algebraMap _ _) Y ∅ G.Ω G.K G.J G.y G.𝔐 G.Fl
    (RingOfIntegers.coe_injective)).1
  obtain ⟨β, dβ, hβ, hβP, hb0, hβc, hbd⟩ := GlobalTheory.T.reference_geometry_multihomog_form E H D l (Xo l) c _ _ Y G
  let Fl : Set (Option (RootIx D)) := {a | ∃ (τ : CMType H) (i : Fin (D.p + D.q)), (i : ℕ) + 1 = D.p + D.q ∧ a = some (τ, i)}
  have hFl : ∀ a ∈ Fl, ∀ t, ReciprocityTheory.AnForm.M.IsPsh A.Sys.A ((A.Sys.potT a t).rsmul (-1)) ∧
      ReciprocityTheory.AnForm.M.IsPsh A.Sys.A (A.Sys.potT a t) := by
    rintro _ ⟨τ, i, hi, rfl⟩ t
    exact A.flat τ i hi t
  have hn : ∀ a ∉ Fl, 0 ≤ gapN ν a := by
    intro a ha
    cases a with
    | none => simp [gapN]
    | some r =>
      obtain ⟨τ, i⟩ := r
      have hi : (i : ℕ) + 1 < D.p + D.q := by
        by_contra h
        exact ha ⟨τ, i, by have := i.2; omega, rfl⟩
      have := hν τ i ⟨i + 1, hi⟩ (by simp [Fin.lt_def])
      simp only [gapN, dif_pos hi]
      omega
  obtain ⟨-, h2⟩ := GlobalTheory.T.nef_polarization hIn _ _ A.Sys Fl hFl G.K G.J G.Ω G.y A.Re A.J_top hb
    (fun V _ L => GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ V L) (GroundTheory.Heights₂.Heights.NumbersDVR.IntNumIsFieldIntersection.full ℚ G.K G.J) (gapN ν) hn
  obtain ⟨k, hk, e, he, he0⟩ := h2 (GlobalTheory.T.global_reference_gap_positive hG E H D Xo l c Y hgl hp hq G A ν hν) β dβ hβ hβP
  have hne0 : ∀ κ, ∃ i, G.y ⟨κ, i⟩ ≠ 0 := by
    obtain ⟨c0, hc0⟩ := G.𝔐.tie.cover ⟨genPt G.𝔐.ξ, specializes_rfl⟩
    exact fun κ => ⟨c0 κ, ne_of_chart hc0 κ⟩
  choose i₀ hi₀ using hne0
  set n : RootIx D → ℤ := fun r => ((k * 1 : ℕ) : ℤ) * ν r with hn'
  have hdeg : ∀ κ, (∑ r, (-n r) • G.xdeg r) κ = (k : ℤ) * (PB.combLine A.Re.ref (gapN ν)).a κ := by
    intro κ
    rw [comb_a, Finset.sum_apply, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [hn']
    ring
  have he' : e ∈ chartLat G.y (fun κ => (∑ r, (-n r) • G.xdeg r) κ - 1 - dβ κ) 1 := by
    have : (fun κ => (∑ r, (-n r) • G.xdeg r) κ - 1 - (dβ κ : ℤ)) =
        fun κ => (k : ℤ) * (PB.combLine A.Re.ref (gapN ν)).a κ - 1 - dβ κ := by
      funext κ
      rw [hdeg]
    rw [this]
    exact he
  refine ⟨k, 1, _, by omega, one_pos, ?_, isEff_of_data G n e _ dβ i₀ hi₀ he' hβc hbd⟩
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero he0 hb0) (Finset.prod_ne_zero_iff.2 fun κ _ => hi₀ κ)) ?_
  have hDeg := GlobalTheory.T.lattice_tensor_power_degree _ _ G.𝔐.ξ G.K G.J G.y _ G.Fl.rootLat Set.univ G.xdeg G.e G.lines (fun r => -n r)
  exact hDeg.1

end GlobalTheory.CompanionTheory.Ar.ExRefEff
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_effective_weight_section : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → ∀ (G : RefGeo Y), Nonempty G.An → ∀ ν : RootIx D → ℤ, (∀ τ (i k : Fin (D.p + D.q)), i < k → ν (τ, k) < ν (τ, i)) → ∃ (k q' : ℕ) (s : G.Ω), 0 < k ∧ 0 < q' ∧ s ≠ 0 ∧ G.IsEff (fun r => (k * q' : ℕ) * ν r) q' s := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.ExRefEff.exists_eff
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_comparison_left : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S₀ y₁) (B : HodgeCpt Y S y) (i : Ω₁ →+* Ω) (h : B.X ⟶ A.X), GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i → B.f = h ≫ A.f → ∃ jA : A.Li →+ B.Li, IsExtOver i jA ∧ (∀ e, (B.M.pt (jA e)).left ≫ B.m.φ = spMap (dualMap i) ≫ (A.M.pt e).left ≫ A.m.φ) ∧ (∀ a e, jA (A.ρ a e) = B.ρ a (jA e)) ∧ B.M.lat = A.M.lat.pull B.ξ h jA := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CoverLie.main | exact GlobalTheory.CompanionTheory.Ar.CoverLie.main | (intros; apply GlobalTheory.CompanionTheory.Ar.CoverLie.main <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_comparison_middle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S₀ y₁) (Fl : A.Flag) (B : HodgeCpt Y S y) (i : Ω₁ →+* Ω) (h : B.X ⟶ A.X) (jA : A.Li →+ B.Li), (letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) → GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i → B.f = h ≫ A.f → B.cst = i.comp A.cst → IsExtOver i jA → (∀ e, (B.M.pt (jA e)).left ≫ B.m.φ = spMap (dualMap i) ≫ (A.M.pt e).left ≫ A.m.φ) → (∀ a e, jA (A.ρ a e) = B.ρ a (jA e)) → ∃ (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module B.Ω₀ Li₀) (M₀ : LieModel Y.t.G B.ξ₀ Li₀) (j : Li₀ →+ B.Li) (V₀ : CMType H ⊕ CMType H → Submodule B.Ω₀ Li₀), (∀ s, Submodule.span Ω (Set.range fun a => jA (Fl.b s a)) = B.Vgen s) ∧ (∀ e, (B.M.pt (j e)).left ≫ B.m.φ = spMap (dualMap B.fn) ≫ (M₀.pt e).left) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ B.Vgen s) ∧ (letI := B.fn.toAlgebra; IsGenericFlag (Ω' := Ω) j V₀ (fun s a => jA (Fl.b s a)) ((letI := i.toAlgebra; Module.finrank Ω₁ Ω) * Fl.deg)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagRead.generic_read | exact GlobalTheory.CompanionTheory.Ar.FlagRead.generic_read | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagRead.generic_read <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.VbGen

theorem flagStep_comp {Ω Ω' V V' : Type} [Field Ω] [Field Ω'] [AddCommGroup V] [Module Ω V] [AddCommGroup V']
    [Module Ω' V'] (i : Ω →+* Ω') (j : V →+ V') (hj : ∀ (a : Ω) (e : V), j (a • e) = i a • j e) {r : ℕ}
    (b b' : Fin r → V) (k : ℕ) (h : flagStep Ω b k = flagStep Ω b' k) :
    flagStep Ω' (fun a => j (b a)) k = flagStep Ω' (fun a => j (b' a)) k := by
  have key : ∀ c c' : Fin r → V, flagStep Ω c k ≤ flagStep Ω c' k →
      flagStep Ω' (fun a => j (c a)) k ≤ flagStep Ω' (fun a => j (c' a)) k := by
    intro c c' hle
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    have hmem : c a ∈ flagStep Ω c' k := hle (Submodule.subset_span ⟨a, ha, rfl⟩)
    show j (c a) ∈ _
    refine Submodule.span_induction (p := fun v _ => j v ∈ flagStep Ω' (fun a => j (c' a)) k) ?_ ?_ ?_ ?_ hmem
    · rintro _ ⟨d, hd, rfl⟩
      exact Submodule.subset_span ⟨d, hd, rfl⟩
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact add_mem hx hy
    · intro t x _ hx
      rw [hj]
      exact Submodule.smul_mem _ _ hx
  exact le_antisymm (key _ _ h.le) (key _ _ h.ge)

theorem span_image_span {Ω Ω' V V' : Type} [Field Ω] [Field Ω'] [AddCommGroup V] [Module Ω V] [AddCommGroup V']
    [Module Ω' V'] (i : Ω →+* Ω') (j : V →+ V') (hj : ∀ (a : Ω) (e : V), j (a • e) = i a • j e)
    (R : Subring Ω) (R' : Subring Ω') (hR : ∀ a ∈ R, i a ∈ R') {r : ℕ} (b : Fin r → V) :
    Submodule.span R' (j '' (Submodule.span R (Set.range b) : Set V)) =
      Submodule.span R' (Set.range fun a => j (b a)) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    refine Submodule.span_induction
      (p := fun v _ => j v ∈ Submodule.span R' (Set.range fun a => j (b a))) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨d, rfl⟩
      exact Submodule.subset_span ⟨d, rfl⟩
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact add_mem hx hy
    · intro t x _ hx
      have h1 : j (t • x) = (⟨i t, hR t t.2⟩ : R') • j x := hj (t : Ω) x
      rw [h1]
      exact Submodule.smul_mem _ _ hx
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span ⟨b a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩

theorem discr_inv_mem {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (p : Cpt ξ)
    (F : Type) [Field F] [NumberField F] (h : ∀ n : ℕ, 0 < n → unitAt ξ p (n : Ω)) :
    (((NumberField.discr F : ℤ) : Ω))⁻¹ ∈ regAt ξ p := by
  have hn0 : 0 < (NumberField.discr F).natAbs := Int.natAbs_pos.2 (NumberField.discr_ne_zero F)
  obtain ⟨-, -, hu⟩ := h _ hn0
  rcases Int.natAbs_eq (NumberField.discr F) with e | e
  · rw [e]; simpa using hu
  · rw [e]
    simpa using (regAt ξ p).neg_mem hu

set_option maxHeartbeats 1000000 in

theorem isFlagVBOn_genFib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S₀ y₁) (Fl : A.Flag) (B : HodgeCpt Y S y) (i : Ω₁ →+* Ω) (h : B.X ⟶ A.X) (jA : A.Li →+ B.Li), GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i → B.f = h ≫ A.f → B.cst = i.comp A.cst → IsExtOver i jA → (∀ e, (B.M.pt (jA e)).left ≫ B.m.φ = spMap (dualMap i) ≫ (A.M.pt e).left ≫ A.m.φ) → (∀ a e, jA (A.ρ a e) = B.ρ a (jA e)) → B.M.lat = A.M.lat.pull B.ξ h jA → ∀ q ∈ genFib B.ξ, ∀ s, (B.V s).IsFlagVBOn {q} (fun a => jA (Fl.b s a)) := by
  intro E _ _ _ H D l Xo c Y S₀ S Ω₁ Ω _ _ K₁ _ J₁ _ y₁ K _ J _ y A Fl B i h jA hdom hf hcst hext hpt hρ hlat q hq s
  intro q' hq'
  obtain rfl : q' = q := hq'
  haveI : CharZero Ω₁ := charZero_of_injective_ringHom A.cst.injective
  have hgenA := A.tie.gen
  have hgenB := B.tie.gen
  obtain ⟨hsp, hreg, hun⟩ := RegAtDom.regAt_dominates A.X Ω₁ A.ξ B.X Ω B.ξ h i hdom q'
  have hunit : ∀ n : ℕ, 0 < n → unitAt A.ξ ⟨h q'.1, hsp⟩ (n : Ω₁) := fun n hn =>
    hun hgenB _ (natCast_mem _ n) (by simpa using hq n hn)
  have hVA : A.V s ⟨h q'.1, hsp⟩ = A.dR s ⟨h q'.1, hsp⟩ :=
    Lat.patch_of_not S₀ _ _ fun r hr hfib => hfib (hunit r (A.S_prime r hr).pos)
  have hVB : B.V s q' = B.dR s q' :=
    Lat.patch_of_not S _ _ fun r hr hfib => hfib (hq r (B.S_prime r hr).pos)
  have hdisc := discr_inv_mem ⟨h q'.1, hsp⟩ E hunit
  have hint : ∀ a, A.emb s a ∈ regAt A.ξ ⟨h q'.1, hsp⟩ := fun a =>
    GlobalTheory.T.integral_element_regular A.X Ω₁ A.ξ ⟨h q'.1, hsp⟩ hgenA (A.normal (h q'.1)).2 _
      ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map (A.emb s).toIntAlgHom)
  obtain ⟨U, hU, b, hb, hfr⟩ := Fl.sub s ⟨h q'.1, hsp⟩ trivial
  obtain ⟨hli, hbs⟩ := hfr ⟨h q'.1, hsp⟩ trivial hU
  refine ⟨⊤, trivial, fun a => jA (b a), fun k => flagStep_comp i jA hext.1 _ _ k (hb k), ?_⟩
  intro q'' hq'' _
  rw [show q'' = q' from hq'']
  refine ⟨hext.2 _ b hli, ?_⟩
  have key := GlobalTheory.T.lattice_eigen_field_extension E Ω₁ Ω i A.Li B.Li jA A.ρ B.ρ (A.emb s) _ _ (A.M.lat ⟨h q'.1, hsp⟩) hext
    (fun a e => (hρ a e).symm) hreg
    (fun a e he => GlobalTheory.T.lie_lattice_stable_under_action A.X Ω₁ A.ξ A.t.G A.Li A.M (𝓞 E) A.t.act A.ρ A.act _ a e he) hint hdisc
  have hem : B.emb s = i.comp (A.emb s) := by
    show B.cst.comp _ = i.comp (A.cst.comp _)
    rw [hcst]; rfl
  have hL : B.M.lat q' = Submodule.span (regAt B.ξ q') (jA '' (A.M.lat ⟨h q'.1, hsp⟩ : Set A.Li)) := by
    rw [hlat]
    show Lat.pull _ _ _ _ _ = _
    unfold Lat.pull
    congr 1
    ext e'
    constructor
    · rintro ⟨_, e, he, rfl⟩
      exact ⟨e, he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨hsp, e, he, rfl⟩
  have hA : A.M.lat ⟨h q'.1, hsp⟩ ⊓ (eigSp A.ρ (A.emb s)).restrictScalars (regAt A.ξ ⟨h q'.1, hsp⟩) =
      Submodule.span (regAt A.ξ ⟨h q'.1, hsp⟩) (Set.range b) := hVA.symm.trans hbs
  rw [hVB]
  show B.M.lat q' ⊓ (eigSp B.ρ (B.emb s)).restrictScalars (regAt B.ξ q') = _
  rw [hL, hem, key, hA]
  exact span_image_span i jA hext.1 _ _ hreg b

end GlobalTheory.CompanionTheory.Ar.VbGen
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_comparison_right : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S₀ y₁) (Fl : A.Flag) (B : HodgeCpt Y S y) (i : Ω₁ →+* Ω) (h : B.X ⟶ A.X) (jA : A.Li →+ B.Li), GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i → B.f = h ≫ A.f → B.cst = i.comp A.cst → IsExtOver i jA → (∀ e, (B.M.pt (jA e)).left ≫ B.m.φ = spMap (dualMap i) ≫ (A.M.pt e).left ≫ A.m.φ) → (∀ a e, jA (A.ρ a e) = B.ρ a (jA e)) → B.M.lat = A.M.lat.pull B.ξ h jA → ∀ q ∈ genFib B.ξ, ∀ s, (B.V s).IsFlagVBOn {q} (fun a => jA (Fl.b s a)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.VbGen.isFlagVBOn_genFib
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ChangeGeo

theorem genPt_comp {X : Scheme.{0}} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] (φ : Ω₀ →+* Ω) (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) :
    GlobalTheory.CompanionTheory.Ar.genPt (Spec.map (CommRingCat.ofHom φ) ≫ ξ) = GlobalTheory.CompanionTheory.Ar.genPt ξ := by
  show ξ ((Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint Ω)) = ξ (IsLocalRing.closedPoint Ω₀)
  congr 1
  exact Subsingleton.elim _ _

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (a : R →+* S) (b : T →+* R) :
    spMap (a.comp b) = spMap a ≫ spMap b := by
  show Spec.map (CommRingCat.ofHom (a.comp b)) = Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom b)
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_inj {R S : Type} [CommRing R] [CommRing S] {a b : R →+* S} (h : spMap a = spMap b) : a = b := by
  have h' : Spec.map (CommRingCat.ofHom a) = Spec.map (CommRingCat.ofHom b) := h
  have := Spec.map_injective h'
  exact CommRingCat.hom_ext_iff.1 this |> fun e => by simpa using e

theorem spMap_dualMap_id (Ω : Type) [Field Ω] : spMap (dualMap (RingHom.id Ω)) = 𝟙 _ := by
  have : dualMap (RingHom.id Ω) = RingHom.id _ := by
    ext a <;> simp [dualMap]
  rw [this]
  show Spec.map (CommRingCat.ofHom (RingHom.id _)) = _
  simp

theorem cst_ext {F Ω : Type} [Field F] [NumberField F] [Field Ω] {a b : F →+* Ω}
    (h : a.comp (algebraMap (𝓞 F) F) = b.comp (algebraMap (𝓞 F) F)) : a = b :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) h

theorem exists_cover : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx) (S : Finset ℕ), (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) → o.Fl.deg = 1 → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (bk : R.K → K) (bx : ∀ k, R.ι k ≃ J (bk k)) (i : R.Ω →+* Ω) (𝔐 : HodgeCpt Y S y) (h : 𝔐.X ⟶ o.𝔐.X) (Fl : 𝔐.Flag) (xdeg : RootIx D → K → ℤ) (e : RootIx D → Ω), Function.Injective bk ∧ (∀ k a, y ⟨bk k, bx k a⟩ = i (R.y ⟨k, a⟩)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ o.𝔐.ξ h i ∧ 𝔐.f = h ≫ o.𝔐.f ∧ 𝔐.cst = i.comp o.𝔐.cst ∧ (∀ s a, (𝔐.M.pt (Fl.b s a)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (o.𝔐.M.pt (o.Fl.b s a)).left ≫ o.𝔐.m.φ) ∧ (letI := i.toAlgebra; Module.finrank R.Ω Ω = Fl.deg) ∧ Fl.RootLines xdeg e ∧ 𝔐.OmVB ∧ SmoothGenericFibreM y ∧ ∀ p ∈ S, 𝔐.R p = 4 := by
  intro hG hW E _ _ _ H D l Xo c Y Sys Fx R o S hSp hSd hdeg
  have hRes : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement := hG.2.2.2.2.1
  haveI : CharZero R.Ω := charZero_of_injective_ringHom o.𝔐.cst.injective
  have hgen₀ := GlobalTheory.T.component_generic_is_generic_point E H D l Xo c Y o.𝔐.Ω₀ o.𝔐.ξ₀ o.𝔐.gen₀
  have hgen : GlobalTheory.CompanionTheory.Ar.genPt (o.𝔐.ξ ≫ o.𝔐.f) ∈ genericPoints Y.X := by
    have e : o.𝔐.ξ ≫ o.𝔐.f = Spec.map (CommRingCat.ofHom o.𝔐.fn) ≫ o.𝔐.ξ₀ := o.𝔐.fn_over
    rw [e, genPt_comp]; exact hgen₀
  obtain ⟨Ω, _, _, i, hfin, htors, hroot⟩ := GlobalTheory.T.exists_finite_extension_primes E H D l Xo c Y R.Ω (o.𝔐.ξ ≫ o.𝔐.f) S hgen hSp
  obtain ⟨K₁, _, J₁, _, y₁, bk₁, bx₁, M₁, h₁, hbk₁, hy₁, hdom₁, hnorm₁, hsm₁⟩ :=
    GlobalTheory.T.coords_after_finite_extension hRes R.K R.ι R.Ω Ω i R.y o.𝔐.X o.𝔐.ξ hfin o.𝔐.all o.𝔐.tie
  have hξ₁ : M₁.ξ ≫ h₁ ≫ o.𝔐.f = spMap i ≫ o.𝔐.ξ ≫ o.𝔐.f := by
    have e : M₁.ξ ≫ h₁ = Spec.map (CommRingCat.ofHom i) ≫ o.𝔐.ξ := hdom₁
    rw [← Category.assoc, e, Category.assoc]
  have hgen₁ : GlobalTheory.CompanionTheory.Ar.genPt (M₁.ξ ≫ h₁ ≫ o.𝔐.f) ∈ genericPoints Y.X := by
    rw [hξ₁]; show GlobalTheory.CompanionTheory.Ar.genPt (Spec.map (CommRingCat.ofHom i) ≫ _) ∈ _
    rw [genPt_comp]; exact hgen
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.generic_point_factors_open E H D l Xo c Y Ω (M₁.ξ ≫ h₁ ≫ o.𝔐.f) hgen₁
  obtain ⟨K₂, _, J₂, _, y₂, bk₂, bx₂, B, g, hbk₂, hy₂, hdom₂, hf₂, hR₂, hfree₂, hiso₂⟩ :=
    GlobalTheory.T.hodge_cpt_projective_model hW E H D l Xo c Y S (fun _ => 4) Ω K₁ J₁ y₁ M₁ (h₁ ≫ o.𝔐.f) y₀ hnorm₁ hy₀ hgen₁ hSp hSd
      (fun _ _ => le_rfl) (fun p hp => by rw [hξ₁]; exact htors p hp) hroot
  have hgB : B.ξ ≫ g = M₁.ξ := by
    have e : B.ξ ≫ g = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ M₁.ξ := hdom₂
    rw [e]; simp
  have hdomB : GlobalTheory.CompanionTheory.Ar.Dominates B.ξ o.𝔐.ξ (g ≫ h₁) i := by
    show B.ξ ≫ g ≫ h₁ = _
    rw [← Category.assoc, hgB]; exact hdom₁
  have hfB : B.f = (g ≫ h₁) ≫ o.𝔐.f := by rw [hf₂, Category.assoc]
  have hBξ : B.ξ ≫ B.f = y₀ ≫ Y.j := by
    rw [hf₂, ← Category.assoc, hgB]; exact hy₀
  have hcst : B.cst = i.comp o.𝔐.cst := by
    have h1 := B.cst_over
    have h2 := o.𝔐.cst_over
    have h3 : B.ξ ≫ B.f = spMap i ≫ o.𝔐.ξ ≫ o.𝔐.f := by
      rw [hf₂, ← Category.assoc, hgB]; exact hξ₁
    have h4 : spMap (B.cst.comp (algebraMap (𝓞 c.F) c.F)) =
        spMap ((i.comp o.𝔐.cst).comp (algebraMap (𝓞 c.F) c.F)) := by
      rw [← h1, ← Category.assoc, h3, RingHom.comp_assoc, spMap_comp', ← h2]
      simp
    haveI := c.fin
    haveI : NumberField c.F := {}
    exact cst_ext (spMap_inj h4)
  obtain ⟨jA, hext, hpt, hact, hlat⟩ :=
    GlobalTheory.T.hodge_comp_comparison_left E H D l Xo c Y ∅ S R.Ω Ω R.K R.ι R.y K₂ J₂ y₂ o.𝔐 B i (g ≫ h₁) hdomB hfB
  obtain ⟨Li₀, _, _, M₀, j, V₀, hspan, hj, hV, hflag⟩ :=
    GlobalTheory.T.hodge_comp_comparison_middle E H D l Xo c Y ∅ S R.Ω Ω R.K R.ι R.y K₂ J₂ y₂ o.𝔐 o.Fl B i (g ≫ h₁) jA hfin hdomB hfB hcst hext hpt hact
  have hvb := GlobalTheory.T.hodge_comp_comparison_right E H D l Xo c Y ∅ S R.Ω Ω R.K R.ι R.y K₂ J₂ y₂ o.𝔐 o.Fl B i (g ≫ h₁) jA hdomB hfB hcst hext hpt hact hlat
  obtain ⟨K₃, _, J₃, _, y₃, bk₃, bx₃, 𝔐, g', Fl, xdeg, e, hbk₃, hy₃, hdom₃, hf₃, hR₃, hc₃, hfree₃, hFd, hFb, hlines, -, hiso₃⟩ :=
    GlobalTheory.T.hodge_cpt_label_bases hW E H D l Xo c Y S Ω K₂ J₂ y₂ B y₀ (fun s a => jA (o.Fl.b s a)) Li₀ _ _ M₀ j V₀ _ hBξ hSd hfree₂
      (fun p hp => by rw [hR₂]; exact hroot p hp) hspan hj hV hflag
  have hsm₂ : SmoothGenericFibreM y₂ :=
    GlobalTheory.T.smoothGenericFibre_of_dominates Ω K₁ J₁ y₁ K₂ J₂ y₂ M₁.X B.X M₁.ξ B.ξ g M₁.all B.all M₁.tie B.tie hdom₂ hsm₁ hiso₂
  have hsm₃ : SmoothGenericFibreM y₃ :=
    GlobalTheory.T.smoothGenericFibre_of_dominates Ω K₂ J₂ y₂ K₃ J₃ y₃ B.X 𝔐.X B.ξ 𝔐.ξ g' B.all 𝔐.all B.tie 𝔐.tie hdom₃ hsm₂
      (fun q hq => hiso₃ q hq (hvb q hq))
  have hg' : 𝔐.ξ ≫ g' = B.ξ := by
    have e : 𝔐.ξ ≫ g' = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ B.ξ := hdom₃
    rw [e]; simp
  refine ⟨Ω, inferInstance, inferInstance, K₃, inferInstance, J₃, inferInstance, y₃, fun k => bk₃ (bk₂ (bk₁ k)),
    fun k => (bx₁ k).trans ((bx₂ _).trans (bx₃ _)), i, 𝔐, g' ≫ g ≫ h₁, Fl, xdeg, e,
    hbk₃.comp (hbk₂.comp hbk₁), ?_, ?_, ?_, ?_, ?_, ?_, hlines, ?_, hsm₃, ?_⟩
  · intro k a
    simp only [Equiv.trans_apply]
    rw [hy₃, hy₂, hy₁]
  · show 𝔐.ξ ≫ g' ≫ g ≫ h₁ = _
    rw [← Category.assoc, hg']; exact hdomB
  · rw [hf₃, hf₂]; simp
  · rw [hc₃, hcst]
  · intro s a
    rw [hFb, hpt, spMap_dualMap_id, Category.id_comp]
  · rw [hFd, hdeg, _root_.mul_one]
  · intro p hp
    have := hfree₃ p hp
    exact this
  · intro p hp
    rw [hR₃, hR₂]

end GlobalTheory.CompanionTheory.Ar.ChangeGeo
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_good_primes_finite : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx) (S : Finset ℕ), (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) → o.Fl.deg = 1 → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (bk : R.K → K) (bx : ∀ k, R.ι k ≃ J (bk k)) (i : R.Ω →+* Ω) (𝔐 : HodgeCpt Y S y) (h : 𝔐.X ⟶ o.𝔐.X) (Fl : 𝔐.Flag) (xdeg : RootIx D → K → ℤ) (e : RootIx D → Ω), Function.Injective bk ∧ (∀ k a, y ⟨bk k, bx k a⟩ = i (R.y ⟨k, a⟩)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ o.𝔐.ξ h i ∧ 𝔐.f = h ≫ o.𝔐.f ∧ 𝔐.cst = i.comp o.𝔐.cst ∧ (∀ s a, (𝔐.M.pt (Fl.b s a)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (o.𝔐.M.pt (o.Fl.b s a)).left ≫ o.𝔐.m.φ) ∧ (letI := i.toAlgebra; Module.finrank R.Ω Ω = Fl.deg) ∧ Fl.RootLines xdeg e ∧ 𝔐.OmVB ∧ SmoothGenericFibreM y ∧ ∀ p ∈ S, 𝔐.R p = 4 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.ChangeGeo.exists_cover
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Comps

theorem finite_maximal_points (X : Type) [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X]
    [QuasiSober X] [T0Space X] : {x : X | ∀ x' : X, x' ⤳ x → x' = x}.Finite := by
  refine Set.Finite.of_injOn (f := fun x : X => closure {x}) (t := irreducibleComponents X) ?_ ?_
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents)
  · intro x hx
    have hZ : irreducibleComponent x ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
    have hirr : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
    have hcl : IsClosed (irreducibleComponent x) := isClosed_irreducibleComponent
    have hg := hirr.isGenericPoint_genericPoint_closure
    rw [hcl.closure_eq] at hg
    have hs : hirr.genericPoint ⤳ x := by
      rw [specializes_iff_mem_closure, hg.def]
      exact mem_irreducibleComponent
    have he := hx _ hs
    show closure {x} ∈ irreducibleComponents X
    rw [← he, hg.def]
    exact hZ
  · intro x _ y _ h
    exact (inseparable_iff_closure_eq.2 h).eq

theorem nonempty_maximal_points (X : Type) [TopologicalSpace X] [QuasiSober X] [T0Space X] [Nonempty X] :
    {x : X | ∀ x' : X, x' ⤳ x → x' = x}.Nonempty := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have hZ : irreducibleComponent x ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  have hirr : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hcl : IsClosed (irreducibleComponent x) := isClosed_irreducibleComponent
  have hg := hirr.isGenericPoint_genericPoint_closure
  rw [hcl.closure_eq] at hg
  refine ⟨hirr.genericPoint, fun x' hx' => ?_⟩
  have hm : Maximal IsIrreducible (irreducibleComponent x) := hZ
  have hsub : irreducibleComponent x ⊆ closure {x'} := by
    rw [← hg.def]
    exact hx'.closure_subset
  have hirr' : IsIrreducible (closure {x'}) := isIrreducible_singleton.closure
  have heq : closure {x'} = irreducibleComponent x := (hm.eq_of_subset hirr' hsub).symm
  exact (inseparable_iff_closure_eq.2 (heq.trans hg.def.symm)).eq

theorem exists_typeFn {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ) :
    ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H p q ty := by
  classical
  let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then p else q
  let e := Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))
  refine ⟨_, fun i => (e.symm i).1, ?_⟩
  have key : ∀ τ : E →+* ℂ, Nat.card {i // (e.symm i).1 = τ} = m τ := by
    intro τ
    have e1 : {i // (e.symm i).1 = τ} ≃ Fin (m τ) :=
      (e.symm.subtypeEquiv (fun _ => Iff.rfl)).trans (Equiv.sigmaSubtype τ)
    rw [Nat.card_congr e1, Nat.card_fin]
  intro τ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [key]; simp [m, h]
  · rw [key]; simp [m, h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}

theorem moduli_nonempty (hc : N1c) (Xo : Moduli D l) : Nonempty Xo.X := by
  rcases Nat.eq_zero_or_pos (D.p + D.q) with h | h
  · obtain ⟨f, -, -⟩ := Xo.rep (Sp (KA l)) (𝟙 _) inferInstance (GlobalTheory.Models.RankZero.zeroObj h l _)
    exact ⟨f (IsLocalRing.closedPoint (KA l))⟩
  · obtain ⟨g, ty, hty⟩ := exists_typeFn H D.p D.q
    obtain ⟨F⟩ := hc E H D l Xo (KA l).val.toRingHom g ty h rfl hty
    exact ⟨F.u ⟨0, F.n_pos⟩ 0 (IsLocalRing.closedPoint ℂ)⟩

theorem model_nonempty {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    (h : Nonempty Xo.X) : Nonempty Y.X := by
  obtain ⟨x⟩ := h
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := Xo.s) (g := spMap (IntermediateField.inclusion c.le).toRingHom) x (IsLocalRing.closedPoint c.F)
    (Subsingleton.elim _ _)
  exact ⟨Y.j z⟩

theorem finite_nonempty_maximal : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)), {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}.Finite ∧ {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}.Nonempty := by
  intro hG E _ _ _ H D l Xo c Y
  have : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have : TopologicalSpace.NoetherianSpace Y.X := GlobalTheory.ModelSum.noetherianSpace_of_isProjOver Y.proj
  have : Nonempty Y.X := model_nonempty Y (moduli_nonempty hG.1.2.2.1 Xo)
  exact ⟨finite_maximal_points Y.X, nonempty_maximal_points Y.X⟩

end GlobalTheory.CompanionTheory.Ar.Comps
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_points_finite_nonempty : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)), {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}.Finite ∧ {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}.Nonempty := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Comps.finite_nonempty_maximal
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TopTower

theorem comp_data (hG : Top.Given) (hA0 : Flat.FlatLineGenerator) (hA1 : Flat.FlatLineGeneratorComponent)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l)
    (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
    (hgl : Top.IsGlobal Xo l c Y) (hsp : SplitComps Y) (hp : 1 ≤ D.p) (hq : 1 ≤ D.q)
    (x : Y.X) (hx : ∀ x' : Y.X, x' ⤳ x → x' = x) :
    ∃ (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys)
      (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx),
      genPt Fx.ξf = x ∧
      (∀ r : RootIx D, (Fx.n r : ℝ) = ((Fx.kA * Fx.q' : ℕ) : ℝ) * (-((r.2 : ℕ) : ℝ))) ∧
      o.Fl.deg = 1 ∧ o.Re.J = ⊤ ∧ Ht.AmpleQ R.y R.A.a ∧
      Cmp.IsEmbedded o.Re.R.A R.P o.Re.R.U o.Re.R.lift ∧ Function.Bijective o.Re.π ∧
      (∀ τ (i : Fin (D.p + D.q)), (i : ℕ) + 1 = D.p + D.q → ∀ t,
        ReciprocityTheory.AnForm.M.IsPsh Sys.A ((Sys.potT (some (τ, i)) t).rsmul (-1)) ∧
          ReciprocityTheory.AnForm.M.IsPsh Sys.A (Sys.potT (some (τ, i)) t)) ∧
      (∀ x : Sys.X, ∃ (U : Set Sys.X) (lam : Sys.X → Fin (Fx.m + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
        (∀ i, Sys.A.HoloOn U fun y => lam y i) ∧ (∀ y ∈ U, ∃ a₀ : ℂ, a₀ ≠ 0 ∧ lam y = a₀ • Fx.pt y) ∧
        ∀ p, lam x p ≠ 0 → ∀ j, x ∈ (Sys.A.chart j).source →
          (fderiv ℂ (fun z i => lam ((Sys.A.chart j).symm z) i / lam ((Sys.A.chart j).symm z) p)
            (Sys.A.chart j x)).ker = ⊥) := by
  have hdom : ∀ x, IsDomain (Y.X.presheaf.stalk x) := fun x => (Y.normal x).1
  have hcg := GlobalTheory.T.isCptGen_residue_field_generic Y.X hdom x hx
  obtain ⟨G, hG0⟩ := GlobalTheory.T.exists_reference_geometry_same_generic hG.2.2.2.2.1 E H D l (Xo l) c Y _ (Y.X.fromSpecResidueField x) hcg
  obtain ⟨A, hinv⟩ := GlobalTheory.T.exists_holomorphic_section_of_analytic hG hA0 hA1 E H D Xo l c Y hgl hsp hp hq G
  let ν : RootIx D → ℤ := fun r => -((r.2 : ℕ) : ℤ)
  have hν : ∀ τ (i k : Fin (D.p + D.q)), i < k → ν (τ, k) < ν (τ, i) := by
    intro τ i k hik
    simp only [ν, neg_lt_neg_iff]
    exact_mod_cast hik
  obtain ⟨k, q', s, hk, hq', hs, heff⟩ := GlobalTheory.T.exists_effective_weight_section hG E H D Xo l c Y hgl hp hq G ⟨A⟩ ν hν
  obtain ⟨Fx, R, o, hgen, hkA, hq'', hn, hdeg, hJ, hamp, hemb, hbij, hlam⟩ :=
    GlobalTheory.T.effective_scaled_weight_of_retraction E H D l (Xo l) c Y G A ν k q' s hinv hsp hk hq' hs heff
  refine ⟨A.Sys, Fx, R, o, ?_, ?_, hdeg, hJ, hamp, hemb, hbij, A.flat, hlam⟩
  · rw [hgen, hG0]
    exact Scheme.fromSpecResidueField_apply x _
  · intro r
    rw [hn r, hkA, hq'']
    simp [ν]

theorem level_data (hG : Top.Given) (hW : Out.WeilSt)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
    {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} (Fx : FixedData Y Sys)
    (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx)
    (hdeg : o.Fl.deg = 1) (hemb : Cmp.IsEmbedded o.Re.R.A R.P o.Re.R.U o.Re.R.lift)
    (hbij : Function.Bijective o.Re.π)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) :
    ∃ (RM : Top.RootModel (CMType H) (D.p + D.q)) (o' : RootOrigin Y S RM Fx), o'.𝔐.OmVB ∧
      (∀ p ∈ S, o'.𝔐.R p = 4) ∧ o'.Re.J = ⊤ ∧ ∃ _ : Algebra ℚ RM.Ω, SmoothGenericFibreM RM.y := by
  obtain ⟨Ω, _, _, K, _, J, _, y, bk, bx, i, 𝔐, h, Fl, xdeg, e, hbk, hy, hd, hf, hcst, hfl, hfin, hlines,
    hom, hsm, hR⟩ := GlobalTheory.T.root_origin_good_primes_finite hG hW E H D l Xo c Y Sys Fx R o S hS hdisc hdeg
  obtain ⟨RM, o', h1, h2, h3, h4⟩ := GlobalTheory.T.root_origin_coords_over_field hG E H D l Xo c Y Sys Fx R o S Ω K J y bk bx i 𝔐 h Fl
    xdeg e hdeg hemb hbij hbk hy hd hf hcst hfl hfin hlines hom hsm
  refine ⟨RM, o', h1, fun p hp => ?_, h3, h4⟩
  rw [h2]
  exact hR p hp

theorem exists_good_tower : Top.Given → Out.WeilSt → Flat.FlatLineGenerator → Flat.FlatLineGeneratorComponent → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)], Top.IsGlobal Xo l c Y → SplitComps Y → 1 ≤ D.p → 1 ≤ D.q → ∃ (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T), (∀ a, (∀ x : (o.Sys a).X, ∃ (U : Set (o.Sys a).X) (lam : (o.Sys a).X → Fin ((o.Fx a).m + 1) → ℂ), IsOpen U ∧ x ∈ U ∧ (∀ i, (o.Sys a).A.HoloOn U fun y => lam y i) ∧ (∀ y ∈ U, ∃ a₀ : ℂ, a₀ ≠ 0 ∧ lam y = a₀ • (o.Fx a).pt y) ∧ ∀ p, lam x p ≠ 0 → ∀ j, x ∈ ((o.Sys a).A.chart j).source → (fderiv ℂ (fun z i => lam (((o.Sys a).A.chart j).symm z) i / lam (((o.Sys a).A.chart j).symm z) p) ((o.Sys a).A.chart j x)).ker = ⊥)) ∧ ∀ B a, ∀ p ∈ o.S B, (o.Or B a).𝔐.R p = 4 := by
  intro hG hW hA0 hA1 E _ _ _ H D Xo l c Y _ hgl hsp hp hq
  obtain ⟨hfin, hne⟩ := GlobalTheory.T.generic_points_finite_nonempty hG E H D l (Xo l) c Y
  let Smax : Set Y.X := {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}
  haveI : Fintype Smax := Set.Finite.fintype hfin
  haveI : Nonempty Smax := hne.to_subtype
  choose Sys Fx R o hgen hnu hdeg hJ hamp hemb hbij hflat hlam using
    fun a : Smax => comp_data hG hA0 hA1 Xo l c Y hgl hsp hp hq a.1 a.2
  have hM' : l.M' ≠ 0 := by
    show Nat.lcm l.M l.A ≠ 0
    exact Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have hn0 : 2 * (discr E).natAbs * l.M' ≠ 0 := by
    exact Nat.mul_ne_zero (Nat.mul_ne_zero two_ne_zero (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero E))) hM'
  let bad : Finset ℕ := (2 * (discr E).natAbs * l.M').primeFactors
  have hbad : ∀ r : ℕ, r ∈ bad ↔ r.Prime ∧ (r : ℤ) ∣ 2 * discr E * l.M' := by
    intro r
    simp only [bad, Nat.mem_primeFactors, Int.natCast_dvd, Int.natAbs_mul]
    simp [hn0]
  let SB : ℕ → Finset ℕ := fun B => (Finset.range (B + 1)).filter Nat.Prime ∪ bad
  have hSB : ∀ B r, r ∈ SB B ↔ r.Prime ∧ (r ≤ B ∨ r ∈ bad) := by
    intro B r
    simp only [SB, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro (⟨h1, h2⟩ | h)
      · exact ⟨h2, Or.inl (by omega)⟩
      · exact ⟨((hbad r).1 h).1, Or.inr h⟩
    · rintro ⟨h1, h2 | h2⟩
      · exact Or.inl ⟨by omega, h1⟩
      · exact Or.inr h2
  have hSBp : ∀ B, ∀ p ∈ SB B, p.Prime := fun B p hp => ((hSB B p).1 hp).1
  have hSBd : ∀ B, ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ SB B := by
    intro B p hp hd
    refine (hSB B p).2 ⟨hp, Or.inr ((hbad p).2 ⟨hp, ?_⟩)⟩
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hd 2) _
  choose RM o' hom hR hJ' hsm using fun (B : ℕ) (a : Smax) =>
    level_data hG hW Y (Fx a) (R a) (o a) (hdeg a) (hemb a) (hbij a) (SB B) (hSBp B) (hSBd B)
  let T : Top.RootTower (CMType H) (D.p + D.q) :=
    { j := D.p
      j_pos := hp
      j_lt := by omega
      Comp := Smax
      bad := bad
      two_mem := (hbad 2).2 ⟨Nat.prime_two, Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl _) _) _⟩
      nu := fun _ i => -((i : ℕ) : ℝ)
      nu_rat := fun _ i => ⟨-((i : ℕ) : ℚ), by push_cast; rfl⟩
      M := RM }
  let tor : TowerOrigin Y T :=
    { j_eq := rfl
      bad_iff := hbad
      S := SB
      S_iff := hSB
      Sys := Sys
      Fx := Fx
      comp_inj := fun a a' h => Subtype.ext (by rw [← hgen a, ← hgen a']; exact h)
      comp_onto := fun x hx => ⟨⟨x, hx⟩, hgen _⟩
      nu_eq := fun a r => hnu a r
      Or := o' }
  let go : Top.GoodOrigin Y T :=
    { toTowerOrigin := tor
      omVB := hom
      smooth := fun B a => ⟨hJ' B a, hsm B a⟩
      flat := hflat
      R := R
      refOr := o
      ref_deg := hdeg
      ref_top := hJ
      ample := hamp }
  exact ⟨T, go, fun a => hlam a, fun B a p hp => hR B a p hp⟩

end GlobalTheory.CompanionTheory.Ar.TopTower
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_good_root_tower : Top.Given → Out.WeilSt → Flat.FlatLineGenerator → Flat.FlatLineGeneratorComponent → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)], Top.IsGlobal Xo l c Y → SplitComps Y → 1 ≤ D.p → 1 ≤ D.q → ∃ (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T), (∀ a, (∀ x : (o.Sys a).X, ∃ (U : Set (o.Sys a).X) (lam : (o.Sys a).X → Fin ((o.Fx a).m + 1) → ℂ), IsOpen U ∧ x ∈ U ∧ (∀ i, (o.Sys a).A.HoloOn U fun y => lam y i) ∧ (∀ y ∈ U, ∃ a₀ : ℂ, a₀ ≠ 0 ∧ lam y = a₀ • (o.Fx a).pt y) ∧ ∀ p, lam x p ≠ 0 → ∀ j, x ∈ ((o.Sys a).A.chart j).source → (fderiv ℂ (fun z i => lam (((o.Sys a).A.chart j).symm z) i / lam (((o.Sys a).A.chart j).symm z) p) ((o.Sys a).A.chart j x)).ker = ⊥)) ∧ ∀ B a, ∀ p ∈ o.S B, (o.Or B a).𝔐.R p = 4 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.TopTower.exists_good_tower
end
