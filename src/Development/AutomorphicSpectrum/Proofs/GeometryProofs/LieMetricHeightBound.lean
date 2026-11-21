import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartLocalNormalForm
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalNearBoundary
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.HeightBoundComplexConjugate
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartLieModelExists
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.QuotientUniformizationLower
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.QuotientUniformizationChartAt
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.QuotientUniformizationCharts

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_near_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → ∃ ρ K : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ P : AbPart C.t (spMap (C.ψ z)), IsPrincipal P.tB ∧ ∀ (Mz : LieModel C.t.G (spMap (C.ψ z)) (Fin C.g → ℂ)), (∀ i, C.M.Lifts (C.ψ z) (𝟙 _) (Pi.single i 1) (Mz.pt (Pi.single i 1))) → ∀ (x : Fin C.g → ℂ) (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (c : ℂ), v.left ≫ P.m.φ = (Mz.pt x).left → HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (v ≫ P.τ.q ≫ P.e.hom) (v ≫ P.τ.q ≫ P.e.hom) c → c.re ≤ K * ∑ i, ‖x i‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotLoc.abPart_principal_and_bound | exact GlobalTheory.CompanionTheory.Ar.QuotLoc.abPart_principal_and_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotLoc.abPart_principal_and_bound <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif

theorem abBound_of_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (h : LieMetric M y) (C : ℝ) (z : Sp ℂ ⟶ X), AbBound t h C (spMap (starRingEnd ℂ) ≫ z) → AbBound t h C z := by
  exact @PositivityTheory.Xgn.height_bound_complex_conjugate

end GlobalTheory.CompanionTheory.Ar.QuotUnif
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_bound_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (h : LieMetric M y) (C : ℝ) (z : Sp ℂ ⟶ X), AbBound t h C (spMap (starRingEnd ℂ) ≫ z) → AbBound t h C z := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.QuotUnif.abBound_of_conj
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif.Dich

theorem ringOfIntegers_hom_injective {F : Type} [Field F] [NumberField F] (r : 𝓞 F →+* ℂ) :
    Function.Injective r := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
  rw [eq_bot_iff]
  intro n hn
  have h0 : r (algebraMap ℤ (𝓞 F) n) = 0 := hn
  have : (n : ℂ) = 0 := by simpa using h0
  simpa using this

theorem exists_extension_to_field {F : Type} [Field F] [NumberField F] (r : 𝓞 F →+* ℂ) :
    ∃ r' : F →+* ℂ, r'.comp (algebraMap (𝓞 F) F) = r :=
  ⟨IsFractionRing.lift (K := F) (ringOfIntegers_hom_injective r), RingHom.ext fun a => by
    simp only [RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (K := F) (ringOfIntegers_hom_injective r) a⟩

theorem conj_eq_neg_of_sq_eq_neg_natCast {x : ℂ} {d : ℕ} (h : x ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ x = -x := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero] at hre him
  have h0 : x.re = 0 := by
    by_contra hne
    have : x.im = 0 := by
      have : x.re * x.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [this] at hre
    nlinarith [mul_self_pos.2 hne]
  apply Complex.ext <;> simp [h0]

theorem goodPt_or_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X), GoodPt 𝔐 z ∨ GoodPt 𝔐 (spMap (starRingEnd ℂ) ≫ z) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 z
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  let r : 𝓞 c.F →+* ℂ := (Spec.preimage (z ≫ 𝔐.f ≫ Y.s)).hom
  have hr : z ≫ 𝔐.f ≫ Y.s = spMap r := by
    simp [r, spMap]
  obtain ⟨τ, hτ⟩ := exists_extension_to_field r
  have h1 := congrArg (τ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ_sq
  have h2 : ((τ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, h1, H.sqrt_neg_disc_sq, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
  · exact Or.inl ⟨τ, by rw [hr, hτ], h⟩
  · refine Or.inr ⟨(starRingEnd ℂ).comp τ, ?_, ?_⟩
    · rw [Category.assoc, hr, ← hτ]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.comp_assoc]
    · rw [RingHom.comp_assoc, RingHom.comp_apply, h, map_neg,
        conj_eq_neg_of_sq_eq_neg_natCast H.sqrt_neg_disc_sq, neg_neg]

end GlobalTheory.CompanionTheory.Ar.QuotUnif.Dich
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_point_or_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X), GoodPt 𝔐 z ∨ GoodPt 𝔐 (spMap (starRingEnd ℂ) ≫ z) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.QuotUnif.Dich.goodPt_or_conj
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif

set_option backward.isDefEq.respectTransparency false in

theorem lie_frame_values_basis : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (z₀ : Sp ℂ ⟶ X), IsCptGen ξ → genPt ξ ⤳ centre z₀ → ∃ (N : ℕ) (s : Fin N → Li), (∀ i, ∃ v : epsAt z₀ ⟶ G, M.ValAt z₀ (s i) v) ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel G z₀ V) (b : Fin N → V), (∀ i, M.ValAt z₀ (s i) (Mz.pt (b i))) → LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤ := by
  intro X Ω _ ξ G _ _ _ Li _ _ M z₀ hξ h
  obtain ⟨R, _, x, hx, F, _, _, MR, n, b₀, hp⟩ := LieVB.exists_chart G (centre z₀)
  have hq' : (X.fromSpecStalk (centre z₀)) (IsLocalRing.closedPoint (X.presheaf.stalk (centre z₀))) ∈
      x.opensRange := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hp
  obtain ⟨ψ, hψ⟩ := LieVB.exists_lift (A := X.presheaf.stalk (centre z₀)) x (X.fromSpecStalk (centre z₀)) hq'
  obtain ⟨EA, _, _, ⟨MA⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre z₀)) (X.fromSpecStalk (centre z₀))
  obtain ⟨-, BA, -, -⟩ := LieVB.basis_tr (A := X.presheaf.stalk (centre z₀)) ψ x (X.fromSpecStalk (centre z₀))
    hψ MR MA b₀
  obtain ⟨i, hi⟩ := LieVB.exists_tr (A := X.presheaf.stalk (centre z₀)) (X.fromSpecStalk (centre z₀)) ξ
    (genMap ξ ⟨centre z₀, h⟩) (LieTangent.spec_genMap ξ ⟨centre z₀, h⟩) MA M
  have hext : ∀ a, M.Extends ⟨centre z₀, h⟩ (i a) (MA.pt a) := fun a => ⟨MA.tan a, hi a⟩
  refine ⟨n, fun k => i (BA k), fun k => ?_, fun V _ _ Mz b hb => ?_⟩
  · obtain ⟨E₀, _, _, ⟨M₀⟩⟩ := lieModel_exists X G ℂ z₀
    obtain ⟨j, hj⟩ := LieVB.exists_tr (A := X.presheaf.stalk (centre z₀)) (X.fromSpecStalk (centre z₀)) z₀
      (Scheme.stalkClosedPointTo z₀).hom (LieTangent.spec_centre z₀) MA M₀
    exact ⟨M₀.pt (j (BA k)), h, _, hext _, hj _⟩
  · obtain ⟨β, B, hB, hβ⟩ := LieVB.basis_tr (R := X.presheaf.stalk (centre z₀))
      (Scheme.stalkClosedPointTo z₀).hom (X.fromSpecStalk (centre z₀)) z₀ (LieTangent.spec_centre z₀) MA Mz BA
    have hbB : b = B := by
      funext k
      obtain ⟨_, v, hv, hw⟩ := hb k
      have hva : MA.pt (BA k) = v := (hext (BA k)).unique (hξ.inj _) hv
      subst hva
      rw [hB]
      exact LieVB.pt_left_inj Mz (hw.trans (hβ _).symm)
    rw [hbB]
    exact ⟨B.linearIndependent, B.span_eq⟩

end GlobalTheory.CompanionTheory.Ar.QuotUnif
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_finite_generating_values : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (z₀ : Sp ℂ ⟶ X), IsCptGen ξ → genPt ξ ⤳ centre z₀ → ∃ (N : ℕ) (s : Fin N → Li), (∀ i, ∃ v : epsAt z₀ ⟶ G, M.ValAt z₀ (s i) v) ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel G z₀ V) (b : Fin N → V), (∀ i, M.ValAt z₀ (s i) (Mz.pt (b i))) → LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.QuotUnif.lie_frame_values_basis
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

theorem GlobalTheory.CompanionTheory.Ar.QuotUnif.chart_coords_le_metric : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (X : Scheme.{0}) (t : SAB H X) (jj : Sp C.R ⟶ X) (m : SABMap C.t t jj) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (h : LieMetric M y) (N : ℕ) (s : Fin N → Li) (sc : Fin N → Fin C.g → C.R) (ww : (Fin n → ℂ) → (Σ k, J k) → ℂ), ContinuousOn ww (ball 0 1) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, ∃ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), ∀ e : Fin C.g → C.R, C.M.Lifts (C.ψ u) (𝟙 _) e (Mz.pt fun i => C.ψ u (e i))) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, CoordsAt ξ y (spMap (C.ψ u) ≫ jj) (ww u)) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, ∀ i, ∃ v : epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G, M.ValAt (spMap (C.ψ u) ≫ jj) (s i) v ∧ v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt (sc i)).left ≫ m.φ) → (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel t.G (spMap (C.ψ 0) ≫ jj) V) (b : Fin N → V), (∀ i, M.ValAt (spMap (C.ψ 0) ≫ jj) (s i) (Mz.pt (b i))) → LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤) → ∃ ρ Kc : ℝ, 0 < ρ ∧ 0 < Kc ∧ ∀ u ∈ ball (0 : Fin n → ℂ) ρ, ∀ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), (∀ e : Fin C.g → C.R, C.M.Lifts (C.ψ u) (𝟙 _) e (Mz.pt fun i => C.ψ u (e i))) → ∀ (x : Fin C.g → ℂ) (v₀ : epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G), (Mz.pt x).left ≫ m.φ = v₀.left → ∑ i, ‖x i‖ ^ 2 ≤ Kc * (h.ip (spMap (C.ψ u) ≫ jj) v₀ v₀).re :=
  @PositivityTheory.Xgn.quotient_uniformization_lower
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_chart_lie_metric_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (X : Scheme.{0}) (t : SAB H X) (jj : Sp C.R ⟶ X) (m : SABMap C.t t jj) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (h : LieMetric M y) (N : ℕ) (s : Fin N → Li) (sc : Fin N → Fin C.g → C.R) (ww : (Fin n → ℂ) → (Σ k, J k) → ℂ), ContinuousOn ww (ball 0 1) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, ∃ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), ∀ e : Fin C.g → C.R, C.M.Lifts (C.ψ u) (𝟙 _) e (Mz.pt fun i => C.ψ u (e i))) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, CoordsAt ξ y (spMap (C.ψ u) ≫ jj) (ww u)) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, ∀ i, ∃ v : epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G, M.ValAt (spMap (C.ψ u) ≫ jj) (s i) v ∧ v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt (sc i)).left ≫ m.φ) → (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel t.G (spMap (C.ψ 0) ≫ jj) V) (b : Fin N → V), (∀ i, M.ValAt (spMap (C.ψ 0) ≫ jj) (s i) (Mz.pt (b i))) → LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤) → ∃ ρ Kc : ℝ, 0 < ρ ∧ 0 < Kc ∧ ∀ u ∈ ball (0 : Fin n → ℂ) ρ, ∀ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), (∀ e : Fin C.g → C.R, C.M.Lifts (C.ψ u) (𝟙 _) e (Mz.pt fun i => C.ψ u (e i))) → ∀ (x : Fin C.g → ℂ) (v₀ : epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G), (Mz.pt x).left ≫ m.φ = v₀.left → ∑ i, ‖x i‖ ^ 2 ≤ Kc * (h.ip (spMap (C.ψ u) ≫ jj) v₀ v₀).re := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.QuotUnif.chart_coords_le_metric
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif

theorem exists_chart_at_of_polydisc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (n a : ℕ) (w : (Fin n → ℂ) → (Σ k, J k) → ℂ) (N : ℕ) (s : Fin N → 𝔐.Li) (z₀ : Sp ℂ ⟶ 𝔐.X), a ≤ n → DifferentiableOn ℂ w (ball 0 1) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, w u ∈ mcPts (mCoordIdeal y)) → (∀ u ∈ Flat.punct n a 1, ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w u) → 𝔐.Interior z) → CoordsAt 𝔐.ξ y z₀ (w 0) → (∀ i, ∃ v : epsAt z₀ ⟶ 𝔐.t.G, 𝔐.M.ValAt z₀ (s i) v) → ∃ (ρ : ℝ) (τ : c.F →+* ℂ) (C : Flat.BdryChart Xo (τ.comp (IntermediateField.inclusion c.le).toRingHom) n a) (jj : Sp C.R ⟶ 𝔐.X) (m : SABMap C.t 𝔐.t jj) (sc : Fin N → Fin C.g → C.R), 0 < ρ ∧ ρ ≤ 1 ∧ ∀ u ∈ ball (0 : Fin n → ℂ) 1, CoordsAt 𝔐.ξ y (spMap (C.ψ u) ≫ jj) (w ((ρ : ℂ) • u)) ∧ spMap (C.ψ u) ≫ jj ≫ 𝔐.f ≫ Y.s = spMap (τ.comp (algebraMap (𝓞 c.F) c.F)) ∧ ∀ i, ∃ v : epsAt (spMap (C.ψ u) ≫ jj) ⟶ 𝔐.t.G, 𝔐.M.ValAt (spMap (C.ψ u) ≫ jj) (s i) v ∧ v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt (sc i)).left ≫ m.φ := by
  exact @PositivityTheory.Xgn.quotient_uniformization_chart_at

end GlobalTheory.CompanionTheory.Ar.QuotUnif
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_component_holomorphic_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (n a : ℕ) (w : (Fin n → ℂ) → (Σ k, J k) → ℂ) (N : ℕ) (s : Fin N → 𝔐.Li) (z₀ : Sp ℂ ⟶ 𝔐.X), a ≤ n → DifferentiableOn ℂ w (ball 0 1) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, w u ∈ mcPts (mCoordIdeal y)) → (∀ u ∈ Flat.punct n a 1, ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w u) → 𝔐.Interior z) → CoordsAt 𝔐.ξ y z₀ (w 0) → (∀ i, ∃ v : epsAt z₀ ⟶ 𝔐.t.G, 𝔐.M.ValAt z₀ (s i) v) → ∃ (ρ : ℝ) (τ : c.F →+* ℂ) (C : Flat.BdryChart Xo (τ.comp (IntermediateField.inclusion c.le).toRingHom) n a) (jj : Sp C.R ⟶ 𝔐.X) (m : SABMap C.t 𝔐.t jj) (sc : Fin N → Fin C.g → C.R), 0 < ρ ∧ ρ ≤ 1 ∧ ∀ u ∈ ball (0 : Fin n → ℂ) 1, CoordsAt 𝔐.ξ y (spMap (C.ψ u) ≫ jj) (w ((ρ : ℂ) • u)) ∧ spMap (C.ψ u) ≫ jj ≫ 𝔐.f ≫ Y.s = spMap (τ.comp (algebraMap (𝓞 c.F) c.F)) ∧ ∀ i, ∃ v : epsAt (spMap (C.ψ u) ≫ jj) ⟶ 𝔐.t.G, 𝔐.M.ValAt (spMap (C.ψ u) ≫ jj) (s i) v ∧ v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt (sc i)).left ≫ m.φ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.QuotUnif.exists_chart_at_of_polydisc
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif.Charts

theorem exists_halfPolydisc_cover : Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), ∃ (n nc : ℕ) (w : Fin nc → (Fin n → ℂ) → (Σ k, J k) → ℂ) (a : Fin nc → ℕ), (∀ i, a i ≤ n) ∧ (∀ i, AnalyticOnNhd ℂ (w i) (ball 0 1)) ∧ (∀ i, ∀ t ∈ ball (0 : Fin n → ℂ) 1, w i t ∈ mcPts (mCoordIdeal y)) ∧ (∀ i, ∀ t ∈ ball (0 : Fin n → ℂ) 1, (∀ j : Fin n, (j : ℕ) < a i → t j ≠ 0) → ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w i t) → 𝔐.Interior z) ∧ ∀ x ∈ mcPts (mCoordIdeal y), ∃ (i : Fin nc) (t : Fin n → ℂ) (b : K → ℂ), ‖t‖ ≤ 1 / 2 ∧ (∀ k, b k ≠ 0) ∧ x = GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul b (w i t) :=
  PositivityTheory.Xgn.quotient_uniformization_charts

end GlobalTheory.CompanionTheory.Ar.QuotUnif.Charts
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_component_finite_charts : Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), ∃ (n nc : ℕ) (w : Fin nc → (Fin n → ℂ) → (Σ k, J k) → ℂ) (a : Fin nc → ℕ), (∀ i, a i ≤ n) ∧ (∀ i, AnalyticOnNhd ℂ (w i) (ball 0 1)) ∧ (∀ i, ∀ t ∈ ball (0 : Fin n → ℂ) 1, w i t ∈ mcPts (mCoordIdeal y)) ∧ (∀ i, ∀ t ∈ ball (0 : Fin n → ℂ) 1, (∀ j : Fin n, (j : ℕ) < a i → t j ≠ 0) → ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w i t) → 𝔐.Interior z) ∧ ∀ x ∈ mcPts (mCoordIdeal y), ∃ (i : Fin nc) (t : Fin n → ℂ) (b : K → ℂ), ‖t‖ ≤ 1 / 2 ∧ (∀ k, b k ≠ 0) ∧ x = GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul b (w i t) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.QuotUnif.Charts.exists_halfPolydisc_cover
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif
open _root_.Metric

theorem exists_recentre {n : ℕ} (a : ℕ) {t₀ : Fin n → ℂ} (ht₀ : t₀ ∈ ball (0 : Fin n → ℂ) 1) :
    ∃ (a₀ : ℕ) (π : Equiv.Perm (Fin n)) (ρ₀ : ℝ), a₀ ≤ n ∧ 0 < ρ₀ ∧ ρ₀ ≤ 1 ∧ ∀ u ∈ ball (0 : Fin n → ℂ) 1,
      HodgeMetric.recentre t₀ ρ₀ π u ∈ ball (0 : Fin n → ℂ) 1 ∧
      (u ∈ Flat.punct n a₀ 1 → ∀ j : Fin n, (j : ℕ) < a → HodgeMetric.recentre t₀ ρ₀ π u j ≠ 0) := by
  classical
  let A : Finset (Fin n) := Finset.univ.filter (fun i => (i : ℕ) < a ∧ t₀ i = 0)
  have hA : ∀ i, i ∈ A ↔ (i : ℕ) < a ∧ t₀ i = 0 := fun i => by simp [A]
  obtain ⟨π, hπ⟩ := ChartGeo.exists_perm_prefix A
  have e2 : ∀ᶠ t : Fin n → ℂ in 𝓝 t₀, ∀ i : Fin n, t₀ i ≠ 0 → t i ≠ 0 := by
    refine Filter.eventually_all.2 fun i => ?_
    by_cases hi : t₀ i = 0
    · exact Filter.Eventually.of_forall fun t h => absurd hi h
    · filter_upwards [(continuous_apply i).continuousAt.eventually_ne hi] with t ht _ using ht
  have e3 : ∀ᶠ t in 𝓝 t₀, t ∈ ball (0 : Fin n → ℂ) 1 := isOpen_ball.mem_nhds ht₀
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (e2.and e3)
  have hle : A.card ≤ n := by simpa using A.card_le_univ
  refine ⟨A.card, π, min ε 1, hle, lt_min hε one_pos, min_le_right _ _, fun u hu => ?_⟩
  have hρ : 0 < min ε 1 := lt_min hε one_pos
  obtain ⟨hne, hb⟩ := hball _ (ChartGeo.recentre_mem_ball hρ (min_le_left _ _) π hu)
  refine ⟨hb, ?_⟩
  rintro ⟨-, hu'⟩ j hj h0
  have hρc : ((min ε 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  by_cases hti : t₀ j = 0
  · have hm : j ∈ A := (hA j).2 ⟨hj, hti⟩
    have := hu' (π j) ((hπ j).2 hm)
    rw [ChartGeo.recentre_apply, hti, zero_add] at h0
    exact (mul_ne_zero hρc this) h0
  · exact hne j hti h0

theorem exists_preimage {n : ℕ} {t₀ t : Fin n → ℂ} (π : Equiv.Perm (Fin n)) {ρ₀ ρ₁ r : ℝ} (h₀ : 0 < ρ₀) (h₁ : 0 < ρ₁)
    (hr : 0 < r) (ht : t ∈ ball t₀ (ρ₀ * ρ₁ * r)) :
    ∃ u ∈ ball (0 : Fin n → ℂ) r, HodgeMetric.recentre t₀ ρ₀ π ((ρ₁ : ℂ) • u) = t := by
  have hp : 0 < ρ₀ * ρ₁ := mul_pos h₀ h₁
  have hpc : ((ρ₀ : ℂ) * (ρ₁ : ℂ)) ≠ 0 := by
    have : ((ρ₀ * ρ₁ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    simpa using this
  refine ⟨fun j => ((ρ₀ : ℂ) * ρ₁)⁻¹ * (t (π.symm j) - t₀ (π.symm j)), ?_, ?_⟩
  · rw [mem_ball_zero_iff, pi_norm_lt_iff hr]
    intro j
    have h1 : ‖t (π.symm j) - t₀ (π.symm j)‖ < ρ₀ * ρ₁ * r := by
      have := lt_of_le_of_lt (norm_le_pi_norm (t - t₀) (π.symm j)) (mem_ball_iff_norm.1 ht)
      simpa using this
    have h2 : ‖((ρ₀ : ℂ) * ρ₁)⁻¹‖ = (ρ₀ * ρ₁)⁻¹ := by
      rw [norm_inv, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg h₀.le,
        Real.norm_of_nonneg h₁.le]
    rw [norm_mul, h2, inv_mul_lt_iff₀ hp]
    exact h1
  · funext i
    rw [ChartGeo.recentre_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Equiv.symm_apply_apply]
    have c0 : (ρ₀ : ℂ) ≠ 0 := by exact_mod_cast h₀.ne'
    have c1 : (ρ₁ : ℂ) ≠ 0 := by exact_mod_cast h₁.ne'
    field_simp
    ring

theorem smul_mem_ball {n : ℕ} {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1) {u : Fin n → ℂ}
    (hu : u ∈ ball (0 : Fin n → ℂ) 1) : (ρ : ℂ) • u ∈ ball (0 : Fin n → ℂ) 1 := by
  rw [mem_ball_zero_iff] at hu ⊢
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg h0.le]
  nlinarith [norm_nonneg u]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K]
  {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem exists_tan {S : Scheme.{0}} (t : SAB H S) (z : Sp ℂ ⟶ S) {tK : SAB H (Sp ℂ)} (mK : SABMap tK t z) {V : Type}
    [AddCommGroup V] [Module ℂ V] (Mz : LieModel t.G z V) (v : epsAt (𝟙 (Sp ℂ)) ⟶ tK.G) (hv : IsTanAt _ _ v) :
    ∃ x : V, v.left ≫ mK.φ = (Mz.pt x).left := by
  have key : ∀ (z' : Sp ℂ ⟶ S) (_ : 𝟙 (Sp ℂ) ≫ z = z') (Mz' : LieModel t.G z' V),
      ∃ x : V, v.left ≫ mK.φ = (Mz'.pt x).left := by
    rintro z' rfl Mz'
    obtain ⟨Mk, hMk⟩ := (LiePull.lieModel_pullback S (Sp ℂ) t.G tK.G z mK.φ mK.cart ℂ (𝟙 _) V).1 Mz'
    obtain ⟨x, rfl⟩ := Mk.onto v hv
    exact ⟨x, hMk x⟩
  exact key z (Category.id_comp z) Mz

theorem local_bound (𝔐 : HodgeCpt Y S y) (h : LieMetric 𝔐.M y) (hpq : 1 ≤ D.p + D.q) {n a : ℕ}
    (w : (Fin n → ℂ) → (Σ k, J k) → ℂ) (hw : AnalyticOnNhd ℂ w (ball 0 1))
    (hm : ∀ t ∈ ball (0 : Fin n → ℂ) 1, w t ∈ mcPts (mCoordIdeal y))
    (hi : ∀ t ∈ ball (0 : Fin n → ℂ) 1, (∀ j : Fin n, (j : ℕ) < a → t j ≠ 0) → ∀ z : Sp ℂ ⟶ 𝔐.X,
      CoordsAt 𝔐.ξ y z (w t) → 𝔐.Interior z) {t₀ : Fin n → ℂ} (ht₀ : t₀ ∈ ball (0 : Fin n → ℂ) 1) :
    ∃ ε Kc : ℝ, 0 < ε ∧ 1 ≤ Kc ∧ ∀ K', Kc ≤ K' → ∀ t ∈ ball t₀ ε, ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w t) →
      GoodPt 𝔐 z → AbBound 𝔐.t h K' z := by
  classical
  obtain ⟨a₀, π, ρ₀, ha₀, hρ₀, hρ₀', hrc⟩ := exists_recentre a ht₀
  set w' : (Fin n → ℂ) → (Σ k, J k) → ℂ := fun u => w (HodgeMetric.recentre t₀ ρ₀ π u) with hw'
  have hrd : Differentiable ℂ (HodgeMetric.recentre t₀ ρ₀ π) := by
    unfold HodgeMetric.recentre
    exact (differentiable_const _).add (differentiable_pi.2 fun i => by
      simpa using (differentiable_apply (π i) : Differentiable ℂ fun u : Fin n → ℂ => u (π i)).const_mul (ρ₀ : ℂ))
  have hw'd : DifferentiableOn ℂ w' (ball 0 1) :=
    hw.differentiableOn.comp hrd.differentiableOn fun u hu => (hrc u hu).1
  have hall := 𝔐.all
  have htie := 𝔐.tie
  obtain ⟨z₀, hz₀g, hz₀⟩ := (GlobalTheory.T.complex_points_iff_centres 𝔐.X Ω 𝔐.ξ K J y htie (w t₀)).1 (hm _ ht₀)
  haveI : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨N, s, hs, hfr⟩ := GlobalTheory.T.lie_model_finite_generating_values 𝔐.X Ω 𝔐.ξ 𝔐.t.G 𝔐.Li 𝔐.M z₀ htie.gen hz₀g
  have hw0 : w' 0 = w t₀ := by simp only [hw', HodgeMetric.recentre_zero]
  obtain ⟨ρ₁, τ, C, jj, m, sc, hρ₁, hρ₁', hC⟩ := GlobalTheory.T.hodge_component_holomorphic_cover E H D l Xo c Y S Ω K J y 𝔐 n a₀ w' N s z₀ ha₀ hw'd
    (fun u hu => hm _ (hrc u hu).1) (fun u hu z hz => hi _ (hrc u hu.1).1 ((hrc u hu.1).2 hu) z hz)
    (by rw [hw0]; exact hz₀) hs
  have huniq : ∀ (z z' : Sp ℂ ⟶ 𝔐.X) (w₁ : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w₁ → CoordsAt 𝔐.ξ y z' w₁ → z = z' :=
    fun z z' w₁ h₁ h₂ => by
      obtain ⟨e1, -, e3⟩ := GlobalTheory.T.local_ring_points_existsUnique 𝔐.X Ω 𝔐.ξ K J y htie ℂ
      exact (e1 w₁ h₁.1 (e3 z w₁ (hall _) h₁).1).unique ⟨hall _, h₁⟩ ⟨hall _, h₂⟩
  have hsm : ∀ {r : ℝ}, r ≤ 1 → ∀ u ∈ ball (0 : Fin n → ℂ) r, u ∈ ball (0 : Fin n → ℂ) 1 := fun hr u hu =>
    ball_subset_ball hr hu
  have hpt : ∀ {r : ℝ}, 0 < r → r ≤ 1 → ∀ t ∈ ball t₀ (ρ₀ * ρ₁ * r), ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w t) →
      ∃ u ∈ ball (0 : Fin n → ℂ) r, z = spMap (C.ψ u) ≫ jj := fun {r} hr hr1 t ht z hz => by
    obtain ⟨u, hu, e⟩ := exists_preimage π hρ₀ hρ₁ hr ht
    refine ⟨u, hu, huniq _ _ (w t) hz ?_⟩
    have := (hC u (hsm hr1 u hu)).1
    simp only [hw', e] at this
    exact this
  by_cases hgood : (τ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0
  · obtain ⟨ρ₂, K₂, hρ₂, hρ₂', hQ⟩ := GlobalTheory.T.principal_near_boundary E H D l Xo _ n a₀ C hpq hgood
    have hz0 : spMap (C.ψ 0) ≫ jj = z₀ :=
      huniq _ _ (w t₀) (by
        have := (hC 0 (by simp)).1
        rw [smul_zero, hw0] at this
        exact this) hz₀
    subst hz0
    have hcont : ContinuousOn (fun u : Fin n → ℂ => w' ((ρ₁ : ℂ) • u)) (ball 0 1) := by
      refine hw'd.continuousOn.comp (continuous_const_smul _).continuousOn fun u hu => ?_
      exact smul_mem_ball hρ₁ hρ₁' hu
    obtain ⟨ρ₃, K₃, hρ₃, hK₃, hL⟩ := GlobalTheory.T.boundary_chart_lie_metric_bound E H D l Xo _ n a₀ C 𝔐.X 𝔐.t jj m Ω 𝔐.ξ K J y 𝔐.Li 𝔐.M h N s sc _ hcont
      (fun u _ => GlobalTheory.T.boundary_chart_lie_model_exists E H D l Xo _ n a₀ C u) (fun u hu => (hC u hu).1) (fun u hu i => (hC u hu).2.2 i) hfr
    have hr : 0 < min 1 (min ρ₂ ρ₃) := lt_min one_pos (lt_min hρ₂ hρ₃)
    refine ⟨ρ₀ * ρ₁ * min 1 (min ρ₂ ρ₃), max 1 (|K₂| * K₃), mul_pos (mul_pos hρ₀ hρ₁) hr, le_max_left _ _,
      fun K' hK' t ht z hz _ => ?_⟩
    obtain ⟨u, hu, rfl⟩ := hpt hr (min_le_left _ _) t ht z hz
    have hu₂ : u ∈ ball (0 : Fin n → ℂ) ρ₂ :=
      ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hu
    have hu₃ : u ∈ ball (0 : Fin n → ℂ) ρ₃ :=
      ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hu
    intro P
    obtain ⟨mK, hmK⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m P.m
    let P' : AbPart C.t (spMap (C.ψ u)) := ⟨P.tK, mK, P.τ, P.tB, P.e, P.e_hom, P.act, P.pp⟩
    obtain ⟨Mz, hMz⟩ := GlobalTheory.T.boundary_chart_lie_model_exists E H D l Xo _ n a₀ C u
    have hsingle : ∀ i, C.M.Lifts (C.ψ u) (𝟙 _) (Pi.single i 1) (Mz.pt (Pi.single i 1)) := fun i => by
      have := hMz (Pi.single i 1)
      have e : (fun j => C.ψ u ((Pi.single i 1 : Fin C.g → C.R) j)) = Pi.single i 1 := by
        funext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [Pi.single_eq_of_ne hj]
      rwa [e] at this
    obtain ⟨hpr, hb⟩ := hQ u hu₂ P'
    refine ⟨hpr, fun v v₀ c' hv hvv hH => ?_⟩
    obtain ⟨x, hx⟩ := exists_tan C.t (spMap (C.ψ u)) mK Mz v hv
    have h1 : c'.re ≤ K₂ * ∑ i, ‖x i‖ ^ 2 := hb Mz hsingle x v c' hx hH
    have h2 : ∑ i, ‖x i‖ ^ 2 ≤ K₃ * (h.ip _ v₀ v₀).re := hL u hu₃ Mz hMz x v₀ (by
      rw [← hx, Category.assoc, ← hmK, hvv])
    have h3 : 0 ≤ ∑ i, ‖x i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
    have h4 : 0 ≤ (h.ip _ v₀ v₀).re := by
      by_contra hn
      push_neg at hn
      nlinarith
    calc c'.re ≤ K₂ * ∑ i, ‖x i‖ ^ 2 := h1
      _ ≤ |K₂| * ∑ i, ‖x i‖ ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) h3
      _ ≤ |K₂| * (K₃ * (h.ip _ v₀ v₀).re) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = (|K₂| * K₃) * (h.ip _ v₀ v₀).re := by ring
      _ ≤ K' * (h.ip _ v₀ v₀).re := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hK') h4
  · refine ⟨ρ₀ * ρ₁ * 1, 1, mul_pos (mul_pos hρ₀ hρ₁) one_pos, le_rfl, fun K' _ t ht z hz hG => ?_⟩
    obtain ⟨u, hu, rfl⟩ := hpt one_pos le_rfl t ht z hz
    obtain ⟨τ', e1, e2⟩ := hG
    exfalso
    apply hgood
    haveI : FiniteDimensional ℚ c.F := c.fin
    haveI : NumberField c.F := ⟨⟩
    have e3 := (hC u hu).2.1
    rw [Category.assoc] at e1
    rw [e1] at e3
    have e4 : τ'.comp (algebraMap (𝓞 c.F) c.F) = τ.comp (algebraMap (𝓞 c.F) c.F) := by
      have := Spec.map_injective e3
      exact congrArg CommRingCat.Hom.hom this
    have e5 : τ' = τ := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) e4
    rw [← e5]
    exact e2

end GlobalTheory.CompanionTheory.Ar.QuotUnif

open GlobalTheory.CompanionTheory.Ar.QuotUnif in

theorem GlobalTheory.CompanionTheory.Ar.QuotUnif.main : Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (h : LieMetric 𝔐.M y), 1 ≤ D.p + D.q → ∃ K : ℝ, 1 ≤ K ∧ ∀ (z : Sp ℂ ⟶ 𝔐.X) (P : AbPart 𝔐.t z), IsPrincipal P.tB ∧ ∀ (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (v₀ : epsAt z ⟶ 𝔐.t.G) (c : ℂ), IsTanAt _ _ v → v.left ≫ P.m.φ = v₀.left → HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (v ≫ P.τ.q ≫ P.e.hom) (v ≫ P.τ.q ≫ P.e.hom) c → c.re ≤ K * (h.ip z v₀ v₀).re := by
  intro hR E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 h hpq
  obtain ⟨n, nc, w, a, -, hw, hm, hi, hcov⟩ := GlobalTheory.T.hodge_component_finite_charts hR E H D l Xo c Y S Ω K J y 𝔐
  have hcpt : ∀ i, ∃ Kc : ℝ, 1 ≤ Kc ∧ ∀ K', Kc ≤ K' → ∀ t ∈ Metric.closedBall (0 : Fin n → ℂ) (1 / 2),
      ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w i t) → GoodPt 𝔐 z → AbBound 𝔐.t h K' z := by
    intro i
    refine (isCompact_closedBall (0 : Fin n → ℂ) (1 / 2)).induction_on
      (p := fun A => ∃ Kc : ℝ, 1 ≤ Kc ∧ ∀ K', Kc ≤ K' → ∀ t ∈ A,
        ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w i t) → GoodPt 𝔐 z → AbBound 𝔐.t h K' z) ?_ ?_ ?_ ?_
    · exact ⟨1, le_rfl, fun _ _ t ht => absurd ht (Set.notMem_empty t)⟩
    · rintro A B hAB ⟨Kc, h1, h2⟩
      exact ⟨Kc, h1, fun K' hK t ht => h2 K' hK t (hAB ht)⟩
    · rintro A B ⟨K₁, h1, h2⟩ ⟨K₂, h3, h4⟩
      refine ⟨max K₁ K₂, h1.trans (le_max_left _ _), fun K' hK t ht => ?_⟩
      rcases ht with ht | ht
      · exact h2 K' ((le_max_left _ _).trans hK) t ht
      · exact h4 K' ((le_max_right _ _).trans hK) t ht
    · intro t₀ ht₀
      have ht₀' : t₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 :=
        Metric.closedBall_subset_ball (by norm_num) ht₀
      obtain ⟨ε, Kc, hε, h1, h2⟩ := local_bound 𝔐 h hpq (a := a i) (w i) (hw i) (hm i) (hi i) ht₀'
      exact ⟨Metric.ball t₀ ε, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ hε), Kc, h1, h2⟩
  choose Kf hKf1 hKf using hcpt
  have hle : ∀ i, Kf i ≤ 1 + ∑ j, Kf j := fun i => by
    have : Kf i ≤ ∑ j, Kf j :=
      Finset.single_le_sum (f := Kf) (fun j _ => by have := hKf1 j; linarith) (Finset.mem_univ i)
    linarith
  have hB : ∀ z : Sp ℂ ⟶ 𝔐.X, GoodPt 𝔐 z → AbBound 𝔐.t h (1 + ∑ j, Kf j) z := by
    intro z hz
    obtain ⟨-, e2, e3⟩ := GlobalTheory.T.local_ring_points_existsUnique 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie ℂ
    obtain ⟨x, hx⟩ := e2 z (𝔐.all _)
    have hxm := (GlobalTheory.T.complex_points_iff_centres 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie x).2 ⟨z, 𝔐.all _, hx⟩
    obtain ⟨i, t, b, ht, hb, rfl⟩ := hcov x hxm
    have hc : CoordsAt 𝔐.ξ y z (w i t) := by
      refine ((e3 z _ (𝔐.all _) hx).2 _).2 ⟨fun k => (Units.mk0 (b k) (hb k))⁻¹, ?_⟩
      funext p
      simp [GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul, hb p.1]
    exact hKf i _ (hle i) t (by simpa using ht) z hc hz
  have h1 : (1 : ℝ) ≤ 1 + ∑ j, Kf j := by
    have : 0 ≤ ∑ j, Kf j := Finset.sum_nonneg fun j _ => by have := hKf1 j; linarith
    linarith
  refine ⟨1 + ∑ j, Kf j, h1, fun z => ?_⟩
  rcases GlobalTheory.T.good_point_or_conjugate E H D l Xo c Y S Ω K J y 𝔐 z with hg | hg
  · exact hB z hg
  · exact GlobalTheory.T.abelian_bound_conjugate E H 𝔐.X 𝔐.t Ω 𝔐.ξ 𝔐.Li 𝔐.M K J y h _ z (hB _ hg)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_metric_height_bound : Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (h : LieMetric 𝔐.M y), 1 ≤ D.p + D.q → ∃ K : ℝ, 1 ≤ K ∧ ∀ (z : Sp ℂ ⟶ 𝔐.X) (P : AbPart 𝔐.t z), IsPrincipal P.tB ∧ ∀ (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (v₀ : epsAt z ⟶ 𝔐.t.G) (c : ℂ), IsTanAt _ _ v → v.left ≫ P.m.φ = v₀.left → HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (v ≫ P.τ.q ≫ P.e.hom) (v ≫ P.τ.q ≫ P.e.hom) c → c.re ≤ K * (h.ip z v₀ v₀).re := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.QuotUnif.main
end
