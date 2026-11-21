import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnimodularSolCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmCurveTorsionTransportSecondPeriod
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotallyPositivePolarizationProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticMapTangentDifferential
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticRational
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusToAbelianVarietyConst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RingKrullDimLeOfQuasiFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeDecompositionOfIdeleApprox

section
section
namespace GlobalTheory.TangentVecUnique

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

theorem eq_of_isDiff_of_isTangent : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (n : ℕ) (u : HolUnif A L n)
    (v : epsR ℂ ⟶ A) (w w' : Fin n → ℂ), IsTangent v → u.IsDiff w v → u.IsDiff w' v → w = w' := by
  intro A _ L n u v w w' hv h h'
  have hd : u.IsDiff (w - w') (toUnit (epsR ℂ) ≫ η[A]) := by
    intro U h₁ f
    have hv₁ : ⊤ ≤ v.left ⁻¹ᵁ U := (GlobalTheory.TangentOrigin.tangent_mem_iff (u := u) hv U).2
      ((GlobalTheory.TangentOrigin.tangent_mem_iff (u := u) (GlobalTheory.ArchMetricCompare.isTangent_zero A) U).1 h₁)
    rw [GlobalTheory.ArchMetricCompare.isDiff_zero u U h₁ f, map_zero, map_sub, ← h U hv₁ f, ← h' U hv₁ f, sub_self]
  exact sub_eq_zero.1 (GlobalTheory.ArchMetricCompare.eq_zero_of_isDiff u hd)

end GlobalTheory.TangentVecUnique
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_differential_unique : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (n : ℕ) (u : HolUnif A L n) (v : epsR ℂ ⟶ A) (w w' : Fin n → ℂ), IsTangent v → u.IsDiff w v → u.IsDiff w' v → w = w' := by
  atlas_forward_decl GlobalTheory.TangentVecUnique.eq_of_isDiff_of_isTangent
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

theorem GlobalTheory.GrpPullback.points_conj : ∀ (G G' : Over (Sp ℂ)) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (g : ℂ ≃+* ℂ) (p : G'.left ⟶ G.left), IsGrpPullback G' G (spMap (g : ℂ →+* ℂ)) p → (∀ P Q : 𝟙_ (Over (Sp ℂ)) ⟶ G', P.left ≫ p = Q.left ≫ p → P = Q) ∧ (∀ (P Q : 𝟙_ (Over (Sp ℂ)) ⟶ G) (P' Q' : 𝟙_ (Over (Sp ℂ)) ⟶ G'), P'.left ≫ p = spMap (g : ℂ →+* ℂ) ≫ P.left → Q'.left ≫ p = spMap (g : ℂ →+* ℂ) ≫ Q.left → (P' * Q').left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (P * Q).left) ∧ ∀ (J : Type) (s : Finset J) (P : J → (𝟙_ (Over (Sp ℂ)) ⟶ G)) (P' : J → (𝟙_ (Over (Sp ℂ)) ⟶ G')), (∀ i ∈ s, (P' i).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (P i).left) → (∏ i ∈ s, P' i : 𝟙_ (Over (Sp ℂ)) ⟶ G').left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (∏ i ∈ s, P i : 𝟙_ (Over (Sp ℂ)) ⟶ G).left := by
  intro G G' _ _ _ _ g p h
  obtain ⟨hpb, hmul⟩ := h
  have h1 : ∀ P Q : 𝟙_ (Over (Sp ℂ)) ⟶ G', P.left ≫ p = Q.left ≫ p → P = Q := by
    intro P Q hPQ
    have hw : P.left ≫ G'.hom = Q.left ≫ G'.hom := by rw [Over.w P, Over.w Q]
    exact Over.OverMorphism.ext (hpb.hom_ext hPQ hw)
  have h2 : ∀ (P Q : 𝟙_ (Over (Sp ℂ)) ⟶ G) (P' Q' : 𝟙_ (Over (Sp ℂ)) ⟶ G'),
      P'.left ≫ p = spMap (g : ℂ →+* ℂ) ≫ P.left → Q'.left ≫ p = spMap (g : ℂ →+* ℂ) ≫ Q.left →
      (P' * Q').left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (P * Q).left := by
    intro P Q P' Q' hP hQ
    let u : Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ spMap (g : ℂ →+* ℂ)) ⟶ 𝟙_ (Over (Sp ℂ)) := toUnit _
    have hu : u.left = spMap (g : ℂ →+* ℂ) := by
      have := Over.w u
      simpa using this
    have key := hmul (𝟙_ (Over (Sp ℂ))) P' Q' (u ≫ P) (u ≫ Q) (by simp [hu, hP]) (by simp [hu, hQ])
    rw [← key, ← MonObj.comp_mul]
    simp [hu]
  have h0 : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ G').left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ G).left := by
    have hw : (spMap (g : ℂ →+* ℂ) ≫ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ G).left) ≫ G.hom = 𝟙 _ ≫ spMap (g : ℂ →+* ℂ) := by
      rw [Category.assoc, Over.w]; simp
    let e' : Sp ℂ ⟶ G'.left := hpb.lift _ _ hw
    have he' : e' ≫ G'.hom = (𝟙_ (Over (Sp ℂ))).hom := by
      simp only [e', IsPullback.lift_snd]; rfl
    let E' : 𝟙_ (Over (Sp ℂ)) ⟶ G' := Over.homMk e' he'
    have hE : E'.left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ G).left := by
      simp [E', e']
    have hEE : E' * E' = E' := by
      apply h1
      rw [h2 1 1 E' E' hE hE, hE, _root_.mul_one (1 : 𝟙_ (Over (Sp ℂ)) ⟶ G)]
    have : E' = 1 := mul_eq_left.mp hEE
    rw [← this, hE]
  refine ⟨h1, h2, ?_⟩
  intro J s P P' hs
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact h2 _ _ _ _ (hs a (Finset.mem_insert_self a s)) (ih fun i hi => hs i (Finset.mem_insert_of_mem hi))
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_group_points_injective_mul : ∀ (G G' : Over (Sp ℂ)) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (g : ℂ ≃+* ℂ) (p : G'.left ⟶ G.left), IsGrpPullback G' G (spMap (g : ℂ →+* ℂ)) p → (∀ P Q : 𝟙_ (Over (Sp ℂ)) ⟶ G', P.left ≫ p = Q.left ≫ p → P = Q) ∧ (∀ (P Q : 𝟙_ (Over (Sp ℂ)) ⟶ G) (P' Q' : 𝟙_ (Over (Sp ℂ)) ⟶ G'), P'.left ≫ p = spMap (g : ℂ →+* ℂ) ≫ P.left → Q'.left ≫ p = spMap (g : ℂ →+* ℂ) ≫ Q.left → (P' * Q').left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (P * Q).left) ∧ ∀ (J : Type) (s : Finset J) (P : J → (𝟙_ (Over (Sp ℂ)) ⟶ G)) (P' : J → (𝟙_ (Over (Sp ℂ)) ⟶ G')), (∀ i ∈ s, (P' i).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (P i).left) → (∏ i ∈ s, P' i : 𝟙_ (Over (Sp ℂ)) ⟶ G').left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (∏ i ∈ s, P i : 𝟙_ (Over (Sp ℂ)) ⟶ G).left := by
  atlas_forward_decl GlobalTheory.GrpPullback.points_conj
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

open scoped nonZeroDivisors

namespace GlobalTheory.CMTorsion.ConjPt

theorem coords_conj : ∀ (K : Type) [Field K] [NumberField K] (io : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair)
    (Ω₀ Ω₁ : ℂ), TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ → ∀ (a a' : K),
    (∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((t : Af K) * algebraMap K (Af K) a' - algebraMap K (Af K) a) v) ≤ 1) →
    coords Λ₁ Ω₁ (io a') = (g : ℂ →+* ℂ) ∘ coords Λ₀ Ω₀ (io a) := by
  intro K _ _ io g t Λ₀ Λ₁ Ω₀ Ω₁ hT a a' hint
  obtain ⟨hΩ₀, hΩ₁, hfix, hL0, ⟨𝔞, h𝔞, hL1⟩, h2, h3, hval⟩ := hT
  have hA : ∀ y : Af K, y ∈ GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) ↔
      ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (y v) ≤ 1 := fun y => GlobalTheory.Idele.mem_adelicIdeal_one_iff
  have hone : ∀ x : K, x ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) ↔
      algebraMap K (Af K) x ∈ GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := fun x =>
    (GlobalTheory.Idele.algebraMap_mem_adelicIdeal (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0) x).symm
  have hd : (t : Af K) * algebraMap K (Af K) a' - algebraMap K (Af K) a ∈
      GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := (hA _).2 hint
  have hmem𝔞 : a' ∈ 𝔞 ↔ (t : Af K) * algebraMap K (Af K) a' ∈
      GlobalTheory.Idele.adelicIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [h𝔞, hA]
  have hL0' : ∀ z, z ∈ Λ₀.lattice ↔ z ∈ io '' ((1 : FractionalIdeal (𝓞 K)⁰ K) : Set K) := fun z => Set.ext_iff.1 hL0 z
  have hL1' : ∀ z, z ∈ Λ₁.lattice ↔ z ∈ io '' ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Set K) := fun z => Set.ext_iff.1 hL1 z
  have h0 : io a ∈ Λ₀.lattice ↔ a ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hL0']
    constructor
    · rintro ⟨x, hx, e⟩; rwa [← io.injective e]
    · intro h; exact ⟨a, h, rfl⟩
  have h1 : io a' ∈ Λ₁.lattice ↔ a' ∈ 𝔞 := by
    rw [hL1']
    constructor
    · rintro ⟨x, hx, e⟩; rwa [← io.injective e]
    · intro h; exact ⟨a', h, rfl⟩
  by_cases ha : io a ∈ Λ₀.lattice
  · have ha' : io a' ∈ Λ₁.lattice := by
      rw [h1, hmem𝔞]
      have := add_mem hd ((hone a).1 (h0.1 ha))
      rwa [sub_add_cancel] at this
    simp only [coords, if_pos ha, if_pos ha']
    ext i; fin_cases i <;> simp
  · have ha' : io a' ∉ Λ₁.lattice := by
      intro h
      apply ha
      rw [h0, hone]
      have := sub_mem (hmem𝔞.1 (h1.1 h)) hd
      rwa [sub_sub_cancel] at this
    obtain ⟨e2, e3⟩ := hval a a' ha hint
    simp only [coords, if_neg ha, if_neg ha']
    have e3' : g (Λ₀.derivWeierstrassP (io a) / (2 * Ω₀ ^ 3)) = Λ₁.derivWeierstrassP (io a') / (2 * Ω₁ ^ 3) := by
      rw [mul_comm, ← div_div, map_div₀, e3, map_ofNat, div_div, mul_comm]
    ext i; fin_cases i <;> simp [e2, e3']

end GlobalTheory.CMTorsion.ConjPt

namespace GlobalTheory.CMTorsion.ConjPt

theorem conj_pt : ∀ (K : Type) [Field K] [NumberField K] (io : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ → ∀ (h : (curve Λ₀ Ω₀).map (g : ℂ →+* ℂ) = curve Λ₁ Ω₁) (a a' : K), (∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((t : Af K) * algebraMap K (Af K) a' - algebraMap K (Af K) a) v) ≤ 1) → pt Λ₁ Ω₁ (io a') ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ (io a) := by
  intro K _ _ io g t Λ₀ Λ₁ Ω₀ Ω₁ hT h a a' hint
  have e := coords_conj K io g t Λ₀ Λ₁ Ω₀ Ω₁ hT a a' hint
  unfold pt
  rw [GlobalTheory.WeierstrassCurve.ptHom_mapHom, spMap, GlobalTheory.WeierstrassCurve.SpecMap_ptHom]
  exact GlobalTheory.WeierstrassCurve.ptHom_congr _ _ _ _ (by ext; simp) e _

end GlobalTheory.CMTorsion.ConjPt
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_torsion_point_compat : ∀ (K : Type) [Field K] [NumberField K] (io : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ → ∀ (h : (curve Λ₀ Ω₀).map (g : ℂ →+* ℂ) = curve Λ₁ Ω₁) (a a' : K), (∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((t : Af K) * algebraMap K (Af K) a' - algebraMap K (Af K) a) v) ≤ 1) → pt Λ₁ Ω₁ (io a') ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ (io a) := by
  atlas_forward_decl GlobalTheory.CMTorsion.ConjPt.conj_pt
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

noncomputable section

namespace GlobalTheory.CMTorsion

theorem tan_mapHom_conj (W₀ W₁ : WeierstrassCurve ℂ) (g : ℂ →+* ℂ) (h : W₀.map g = W₁) (c : ℂ) :
    tan W₁ (g c) ≫ mapHom W₀ g h = spMap (Chart.dualMapR g) ≫ tan W₀ c := by
  unfold tan
  rw [GlobalTheory.WeierstrassCurve.ptHom_mapHom, GlobalTheory.WeierstrassCurve.SpecMap_ptHom]
  apply GlobalTheory.WeierstrassCurve.ptHom_congr
  · ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · funext i
    fin_cases i
    · show g c • DualNumber.eps = Chart.dualMapR g (c • DualNumber.eps)
      ext <;> simp [Chart.dualMapR]
    · show (-1 : DualNumber ℂ) = Chart.dualMapR g (-1)
      simp
    · show (0 : DualNumber ℂ) = Chart.dualMapR g 0
      simp

end GlobalTheory.CMTorsion

end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_curve_tangent_compat : ∀ (W₀ W₁ : WeierstrassCurve ℂ) (g : ℂ →+* ℂ) (h : W₀.map g = W₁) (c : ℂ), tan W₁ (g c) ≫ mapHom W₀ g h = spMap (Chart.dualMapR g) ≫ tan W₀ c := by
  atlas_forward_decl GlobalTheory.CMTorsion.tan_mapHom_conj
end

section
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

namespace GlobalTheory.CMTorsion.Conj

open PeriodPair

theorem ptHom_eq_iff_of_eq {W : WeierstrassCurve ℂ} {ρ ρ' : ℂ →+* ℂ} (e : ρ = ρ') {P Q : Fin 3 → ℂ}
    (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P)
    (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ') Q) :
    GlobalTheory.WeierstrassCurve.ptHom W ρ P hP = GlobalTheory.WeierstrassCurve.ptHom W ρ' Q hQ ↔
      ∃ v : ℂˣ, Q = (v : ℂ) • P := by
  subst e
  exact GlobalTheory.WeierstrassCurve.ptHom_eq_ptHom_iff W hP hQ

theorem rel_iff (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ) (g : ℂ ≃+* ℂ) (hΩ₀ : Ω₀ ≠ 0) (hΩ₁ : Ω₁ ≠ 0)
    (h : (curve Λ₀ Ω₀).map (g : ℂ →+* ℂ) = curve Λ₁ Ω₁) (z z' : ℂ) :
    (pt Λ₁ Ω₁ z' ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ z) ↔
      GlobalTheory.ConjPoint.IsConj (GlobalTheory.scalePeriods Λ₀ Ω₀ hΩ₀) (GlobalTheory.scalePeriods Λ₁ Ω₁ hΩ₁) g
        (Ω₀ * z) (Ω₁ * z') := by
  have H₀ := GlobalTheory.isHomothetic_scalePeriods Λ₀ Ω₀ hΩ₀
  have H₁ := GlobalTheory.isHomothetic_scalePeriods Λ₁ Ω₁ hΩ₁
  unfold pt
  rw [GlobalTheory.WeierstrassCurve.ptHom_mapHom, spMap, GlobalTheory.WeierstrassCurve.SpecMap_ptHom,
    ptHom_eq_iff_of_eq ((RingHom.id_comp _).trans (RingHom.comp_id _).symm)]
  unfold GlobalTheory.ConjPoint.IsConj
  rw [H₀ z, H₁ z', H₀.weierstrassP_mul, H₁.weierstrassP_mul, H₀.derivWeierstrassP_mul,
    H₁.derivWeierstrassP_mul]
  by_cases hz : z ∈ Λ₀.lattice <;> by_cases hz' : z' ∈ Λ₁.lattice
  · simp only [coords, hz, hz', if_true]
    refine iff_of_true ⟨1, ?_⟩ (Or.inl ⟨trivial, trivial⟩)
    ext i; fin_cases i <;> simp
  · simp only [coords, hz, hz', if_true, if_false]
    refine iff_of_false ?_ (by tauto)
    rintro ⟨v, hv⟩
    have := congrFun hv 2
    simp at this
    exact v.ne_zero this.symm
  · simp only [coords, hz, hz', if_true, if_false]
    refine iff_of_false ?_ (by tauto)
    rintro ⟨v, hv⟩
    have := congrFun hv 2
    simp at this
  · simp only [coords, hz, hz', if_false, not_false_iff, true_and, false_and, false_or]
    constructor
    · rintro ⟨v, hv⟩
      have h2 := congrFun hv 2
      have h0 := congrFun hv 0
      have h1 := congrFun hv 1
      have g2 : g 2 = 2 := map_ofNat g 2
      simp [g2] at h0 h1 h2
      rw [← h2] at h0 h1
      simp only [map_mul, map_inv₀, map_pow]
      constructor
      · linear_combination -h0
      · linear_combination -2 * h1
    · rintro ⟨e1, e2⟩
      simp only [map_mul, map_inv₀, map_pow] at e1 e2
      refine ⟨1, ?_⟩
      funext i
      have g2 : g 2 = 2 := map_ofNat g 2
      fin_cases i <;> simp [g2] <;> first | linear_combination -e1 | linear_combination (-1/2 : ℂ) * e2

theorem pt_conj_onto_add : ∀ (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ) (g : ℂ ≃+* ℂ), Ω₀ ≠ 0 → Ω₁ ≠ 0 → ∀ h : (curve Λ₀ Ω₀).map (g : ℂ →+* ℂ) = curve Λ₁ Ω₁, (∀ z', ∃ z, pt Λ₁ Ω₁ z' ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ z) ∧ ∀ z w z' w', pt Λ₁ Ω₁ z' ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ z → pt Λ₁ Ω₁ w' ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ w → pt Λ₁ Ω₁ (z' + w') ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ (z + w) := by
  intro Λ₀ Λ₁ Ω₀ Ω₁ g hΩ₀ hΩ₁ h
  have H₀ := GlobalTheory.isHomothetic_scalePeriods Λ₀ Ω₀ hΩ₀
  have H₁ := GlobalTheory.isHomothetic_scalePeriods Λ₁ Ω₁ hΩ₁
  have g4 : g 4 = 4 := map_ofNat g 4
  have e₄ := congrArg WeierstrassCurve.a₄ h
  have e₆ := congrArg WeierstrassCurve.a₆ h
  simp [curve, g4] at e₄ e₆
  have h₂ : (GlobalTheory.scalePeriods Λ₁ Ω₁ hΩ₁).g₂ = g (GlobalTheory.scalePeriods Λ₀ Ω₀ hΩ₀).g₂ := by
    rw [H₁.g₂_eq, H₀.g₂_eq, map_mul, map_inv₀, map_pow]
    linear_combination -e₄
  have h₃ : (GlobalTheory.scalePeriods Λ₁ Ω₁ hΩ₁).g₃ = g (GlobalTheory.scalePeriods Λ₀ Ω₀ hΩ₀).g₃ := by
    rw [H₁.g₃_eq, H₀.g₃_eq, map_mul, map_inv₀, map_pow]
    linear_combination -e₆
  obtain ⟨s, -, hs⟩ := GlobalTheory.ConjPoint.exists_conjEquiv h₂ h₃
  have R := rel_iff Λ₀ Λ₁ Ω₀ Ω₁ g hΩ₀ hΩ₁ h
  refine ⟨fun z' => ?_, fun z w z' w' hz hw => ?_⟩
  · obtain ⟨t, ht⟩ := GlobalTheory.latticePoint_surjective _ (s.symm (GlobalTheory.latticePoint _ (Ω₁ * z')))
    refine ⟨Ω₀⁻¹ * t, (R _ _).2 ((hs _ _).2 ?_)⟩
    rw [← _root_.mul_assoc, mul_inv_cancel₀ hΩ₀, _root_.one_mul, ht, AddEquiv.apply_symm_apply]
  · rw [R, hs] at hz hw ⊢
    rw [_root_.mul_add, _root_.mul_add, GlobalTheory.latticePoint_add, GlobalTheory.latticePoint_add, map_add, hz, hw]

end GlobalTheory.CMTorsion.Conj
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_curve_point_addition_compat : ∀ (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ) (g : ℂ ≃+* ℂ), Ω₀ ≠ 0 → Ω₁ ≠ 0 → ∀ h : (curve Λ₀ Ω₀).map (g : ℂ →+* ℂ) = curve Λ₁ Ω₁, (∀ z', ∃ z, pt Λ₁ Ω₁ z' ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ z) ∧ ∀ z w z' w', pt Λ₁ Ω₁ z' ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ z → pt Λ₁ Ω₁ w' ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ w → pt Λ₁ Ω₁ (z' + w') ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ (z + w) := by
  atlas_forward_decl GlobalTheory.CMTorsion.Conj.pt_conj_onto_add
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

namespace GlobalTheory.CMTorsion

theorem exists_pt_eq : ∀ (Λ : PeriodPair) (Ω : ℂ), Ω ≠ 0 → ∀ x : Sp ℂ ⟶ scheme (curve Λ Ω), x ≫ toSpec (curve Λ Ω) = 𝟙 _ → ∃ z : ℂ, pt Λ Ω z = x := by
  intro Λ Ω hΩ x hx
  have hx' : x ≫ GlobalTheory.WeierstrassCurve.toSpec (curve Λ Ω) = Spec.map (CommRingCat.ofHom (RingHom.id ℂ)) := by
    rw [hx]; exact (Spec.map_id _).symm
  obtain ⟨P, h, rfl⟩ := GlobalTheory.WeierstrassCurve.exists_eq_ptHom (curve Λ Ω) (RingHom.id ℂ) x hx'
  have e := (WeierstrassCurve.Projective.equation_iff _).mp h.equation
  simp only [WeierstrassCurve.map_id, curve] at e
  have hne : P ≠ 0 := (GlobalTheory.WeierstrassCurve.isUnimodularSol_iff_ne_zero.mp h).2
  by_cases h2 : P 2 = 0
  · have h0 : P 0 = 0 := by
      rw [h2] at e
      have : P 0 ^ 3 = 0 := by linear_combination -e
      exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp this
    have h1 : P 1 ≠ 0 := by
      intro h1; apply hne; ext i; fin_cases i <;> simp [h0, h1, h2]
    refine ⟨0, ?_⟩
    unfold pt
    refine (GlobalTheory.WeierstrassCurve.ptHom_eq_ptHom_iff _ _ _).mpr ⟨Units.mk0 (P 1) h1, ?_⟩
    ext i; fin_cases i <;> simp [coords, h0, h2]
  · set a := P 0 / P 2
    set b := P 1 / P 2
    have hY : (2 * b * Ω ^ 3) ^ 2 = 4 * (a * Ω ^ 2) ^ 3 - Λ.g₂ * (a * Ω ^ 2) - Λ.g₃ := by
      simp only [a, b]
      linear_combination (norm := skip) (4 * Ω ^ 6 / P 2 ^ 3) * e
      field_simp
      ring
    obtain ⟨z, hz, hp, hd⟩ := GlobalTheory.exists_weierstrassP_eq_and_derivWeierstrassP_eq Λ hY
    refine ⟨z, ?_⟩
    unfold pt
    refine (GlobalTheory.WeierstrassCurve.ptHom_eq_ptHom_iff _ _ _).mpr ⟨Units.mk0 (P 2) h2, ?_⟩
    ext i; fin_cases i
    · simp [coords, hz, hp, a]; field_simp
    · simp [coords, hz, hd, b]; field_simp
    · simp [coords, hz]

end GlobalTheory.CMTorsion
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_section_from_uniformization : ∀ (Λ : PeriodPair) (Ω : ℂ), Ω ≠ 0 → ∀ x : Sp ℂ ⟶ scheme (curve Λ Ω), x ≫ toSpec (curve Λ Ω) = 𝟙 _ → ∃ z : ℂ, pt Λ Ω z = x := by
  atlas_forward_decl GlobalTheory.CMTorsion.exists_pt_eq
end

section
open CategoryTheory AlgebraicGeometry Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ProjSpace
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ProjHol

variable {N : ℕ}

abbrev InChart (x : Sp ℂ ⟶ PSpace ℂ N) (i : Fin (N + 1)) : Prop := ⊤ ≤ x ⁻¹ᵁ chart ℂ N i

def rv (x : Sp ℂ ⟶ PSpace ℂ N) (i j : Fin (N + 1)) : ℂ := valAt' x (chart ℂ N i) (ratio ℂ N i j)

theorem rv_eq {x : Sp ℂ ⟶ PSpace ℂ N} {i : Fin (N + 1)} (h : InChart x i) (j : Fin (N + 1)) :
    rv x i j = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (pullRatio x ⊤ i h j) := by
  rw [rv, valAt', dif_pos h]
  rfl

theorem rv_self {x : Sp ℂ ⟶ PSpace ℂ N} {i : Fin (N + 1)} (h : InChart x i) : rv x i i = 1 := by
  rw [rv_eq h, pullRatio_self, map_one]

theorem rv_mul {x : Sp ℂ ⟶ PSpace ℂ N} {i j : Fin (N + 1)} (hi : InChart x i) (hj : InChart x j)
    (k : Fin (N + 1)) : rv x i j * rv x j k = rv x i k := by
  rw [rv_eq hi, rv_eq hj, rv_eq hi, ← map_mul, pullRatio_mul_pullRatio]

theorem inChart_iff {x : Sp ℂ ⟶ PSpace ℂ N} {i : Fin (N + 1)} (hi : InChart x i) (j : Fin (N + 1)) :
    InChart x j ↔ rv x i j ≠ 0 := by
  rw [rv, ← GlobalTheory.HolHom.le_basicOpen_iff x hi, ratio, basicOpen_ratioOn, Scheme.Hom.preimage_inf, le_inf_iff]
  exact ⟨fun h => ⟨hi, h⟩, fun h => h.2⟩

theorem exists_inChart (x : Sp ℂ ⟶ PSpace ℂ N) : ∃ i, InChart x i :=
  (exists_mem_chart ℂ N (x (default : PrimeSpectrum ℂ))).imp fun _ h => (GlobalTheory.HolHom.le_preimage_iff x _).2 h

theorem eq_of_rv_eq {x y : Sp ℂ ⟶ PSpace ℂ N} (h : x ≫ PSpace.str ℂ N = y ≫ PSpace.str ℂ N) {i : Fin (N + 1)}
    (hx : InChart x i) (hy : InChart y i) (H : ∀ j, rv x i j = rv y i j) : x = y := by
  refine hom_ext h fun p => ⟨⊤, trivial, i, hx, hy, fun j => ?_⟩
  have := H j
  rw [rv_eq hx, rv_eq hy] at this
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).1 this

theorem inChart_pt (c : ℂ →+* ℂ) (v : Fin (N + 1) → ℂ) (hv : Ideal.span (Set.range v) = ⊤) {i : Fin (N + 1)}
    (hi : v i ≠ 0) : InChart (pt c v hv) i := by
  rw [InChart, pt_preimage_chart]
  intro p _
  rw [mem_spOpen]
  exact fun h => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsUnit.mk0 _ hi))

theorem rv_pt (c : ℂ →+* ℂ) (v : Fin (N + 1) → ℂ) (hv : Ideal.span (Set.range v) = ⊤) {i : Fin (N + 1)}
    (hi : v i ≠ 0) (j : Fin (N + 1)) : rv (pt c v hv) i j = v j / v i := by
  have h := inChart_pt c v hv hi
  have e : ∀ a : ℂ, (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (fnOn ⊤ a) = a := fun a => by
    have : fnOn (A := ℂ) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a :=
      GlobalTheory.Cartier.resG_self (X := Sp ℂ) le_top _
    rw [this]
    exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv_hom_id_apply a
  rw [rv_eq h, eq_div_iff hi, ← e (v i), ← e (v j), ← map_mul, pullRatio_pt_mul]

section Hol

variable {φ ψ : ℂ → (Sp ℂ ⟶ PSpace ℂ N)}

theorem eventually_inChart (hφ : IsHolTo (Set.univ : Set ℂ) φ) {z : ℂ} {i : Fin (N + 1)} (h : InChart (φ z) i) :
    ∀ᶠ w in 𝓝 z, InChart (φ w) i :=
  (GlobalTheory.HolHom.holAt_of_isHolTo hφ (Set.mem_univ z) _ h).1

theorem analyticAt_rv (hφ : IsHolTo (Set.univ : Set ℂ) φ) {z : ℂ} {i : Fin (N + 1)} (h : InChart (φ z) i)
    (j : Fin (N + 1)) : AnalyticAt ℂ (fun w => rv (φ w) i j) z :=
  (hφ (chart ℂ N i) (ratio ℂ N i j)).2.analyticAt ((hφ _ (ratio ℂ N i j)).1.mem_nhds ⟨trivial, h⟩)

theorem eq_of_eventuallyEq (hφ : IsHolTo (Set.univ : Set ℂ) φ) (hψ : IsHolTo (Set.univ : Set ℂ) ψ) {z : ℂ}
    (hs : φ z ≫ PSpace.str ℂ N = ψ z ≫ PSpace.str ℂ N) (h : ∀ᶠ w in 𝓝[≠] z, φ w = ψ w) : φ z = ψ z := by
  obtain ⟨k, hk⟩ := exists_inChart (φ z)
  obtain ⟨l, hl⟩ := exists_inChart (ψ z)
  have key : ∀ j, rv (ψ z) l k * rv (φ z) k j = rv (ψ z) l j := fun j => by
    have h1 := ((analyticAt_rv hψ hl k).continuousAt.mul (analyticAt_rv hφ hk j).continuousAt).tendsto
    have h2 := (analyticAt_rv hψ hl j).continuousAt.tendsto
    refine tendsto_nhds_unique_of_eventuallyEq (h1.mono_left nhdsWithin_le_nhds)
      (h2.mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))) ?_
    filter_upwards [h, nhdsWithin_le_nhds (eventually_inChart hφ hk), nhdsWithin_le_nhds (eventually_inChart hψ hl)]
      with w e a b
    rw [e] at a
    simp only [Pi.mul_apply, e]
    exact rv_mul b a j
  have h0 : rv (ψ z) l k ≠ 0 := left_ne_zero_of_mul_eq_one ((key l).trans (rv_self hl))
  have hk' : InChart (ψ z) k := (inChart_iff hl k).2 h0
  exact eq_of_rv_eq hs hk hk' fun j => mul_left_cancel₀ h0 ((key j).trans (rv_mul hl hk' j).symm)

theorem eventually_nhdsNE_inChart (hφ : IsHolTo (Set.univ : Set ℂ) φ) {z₀ : ℂ} {k : Fin (N + 1)}
    (h₀ : InChart (φ z₀) k) (z : ℂ) : ∀ᶠ w in 𝓝[≠] z, InChart (φ w) k := by
  let A : Set ℂ := {z | ∀ᶠ w in 𝓝[≠] z, InChart (φ w) k}
  have dich : ∀ z, z ∈ A ∨ ∀ᶠ w in 𝓝 z, ¬ InChart (φ w) k := fun z => by
    obtain ⟨i, hi⟩ := exists_inChart (φ z)
    rcases (analyticAt_rv hφ hi k).eventually_eq_zero_or_eventually_ne_zero with h | h
    · right
      filter_upwards [h, eventually_inChart hφ hi] with w a b c using (inChart_iff b k).1 c a
    · left
      filter_upwards [h, nhdsWithin_le_nhds (eventually_inChart hφ hi)] with w a b using (inChart_iff b k).2 a
  have ho : IsOpen A := isOpen_iff_mem_nhds.2 fun z hz => by
    have hz' : ∀ᶠ w in 𝓝 z, w ≠ z → InChart (φ w) k := eventually_nhdsWithin_iff.1 hz
    filter_upwards [hz'] with w hw
    by_cases e : w = z
    · exact e ▸ hz
    · exact nhdsWithin_le_nhds (eventually_inChart hφ (hw e))
  have hc : IsOpen Aᶜ := isOpen_iff_mem_nhds.2 fun z hz => by
    filter_upwards [((dich z).resolve_left hz).eventually_nhds] with w hw
    intro (hA : ∀ᶠ u in 𝓝[≠] w, InChart (φ u) k)
    obtain ⟨u, a, b⟩ := (hA.and (nhdsWithin_le_nhds hw)).exists
    exact b a
  have hA : A = Set.univ := IsClopen.eq_univ ⟨isOpen_compl_iff.1 hc, ho⟩
    ⟨z₀, nhdsWithin_le_nhds (eventually_inChart hφ h₀)⟩
  exact hA.ge (Set.mem_univ z)

theorem meromorphic_rv (hφ : IsHolTo (Set.univ : Set ℂ) φ) {z₀ : ℂ} {k : Fin (N + 1)}
    (h₀ : InChart (φ z₀) k) (j : Fin (N + 1)) : Meromorphic fun w => rv (φ w) k j := fun z => by
  obtain ⟨i, hi⟩ := exists_inChart (φ z)
  refine ((analyticAt_rv hφ hi j).meromorphicAt.div (analyticAt_rv hφ hi k).meromorphicAt).congr ?_
  filter_upwards [eventually_nhdsNE_inChart hφ h₀ z, nhdsWithin_le_nhds (eventually_inChart hφ hi)] with w a b
  rw [Pi.div_apply, div_eq_iff ((inChart_iff b k).1 a), mul_comm, rv_mul b a]

end Hol

end GlobalTheory.ProjHol
end
end

section
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.WeierstrassCurve (scheme toSpec chartZ)
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ProjHol

theorem valuationRing_stalk {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp K)
    [hf : SmoothOfRelativeDimension 1 f] (x : X) : ValuationRing (X.presheaf.stalk x) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : GlobalTheory.IsNormalScheme X := GlobalTheory.isNormalScheme_of_smooth f
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have h : Order.coheight x ≤ 1 := by simpa using GlobalTheory.AffineCover.coheight_le_of_smooth f hf x
  rcases h.eq_or_lt with h | h
  · have := GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk h
    infer_instance
  · have h0 : Order.coheight x = 0 := by simpa using h
    have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le h0.le
    letI := (Ring.KrullDimLE.isField_of_isDomain (R := X.presheaf.stalk x)).toField
    exact ValuationRing.of_field _

theorem exists_extend {K : Type} [Field K] (W : WeierstrassCurve K) [W.IsElliptic] {N : ℕ}
    (v : Fin (N + 1) → W.toAffine.CoordinateRing) (k : Fin (N + 1)) (hk : v k ≠ 0) :
    ∃ ψ : scheme W ⟶ PSpace K N, ψ ≫ PSpace.str K N = toSpec W ∧
      ∀ (e : W.toAffine.CoordinateRing →+* K), e (v k) ≠ 0 → ∀ hv,
        spMap e ≫ chartZ W ≫ ψ = GlobalTheory.ProjSpace.pt (e.comp (algebraMap K _)) (e ∘ v) hv := by
  let A := W.toAffine.CoordinateRing
  let B := Localization.Away (v k)
  have hu : IsUnit (algebraMap A B (v k)) := IsLocalization.Away.algebraMap_isUnit (v k)
  have hv : Ideal.span (Set.range (algebraMap A B ∘ v)) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨k, rfl⟩) hu
  have h1 : IsOpenImmersion (spMap (algebraMap A B)) := IsOpenImmersion.of_isLocalization (v k)
  have : IsDomain B := IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hk)
  have := isProper_str K N
  have : (PSpace K N).IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from (PSpace.str K N)]
    infer_instance⟩
  obtain ⟨ψ, h₁, h₂⟩ := GlobalTheory.TorusConst.exists_extension (valuationRing_stalk (toSpec W))
    (spMap (algebraMap A B) ≫ chartZ W) (toSpec W) (PSpace.str K N)
    (GlobalTheory.ProjSpace.pt ((algebraMap A B).comp (algebraMap K A)) _ hv) (by
      rw [GlobalTheory.ProjSpace.pt_str, Category.assoc, GlobalTheory.WeierstrassCurve.chartZ_toSpec, ← Spec.map_comp]
      rfl)
  refine ⟨ψ, h₂, fun e he hv' => ?_⟩
  let e' : B →+* K := IsLocalization.Away.lift (v k) (IsUnit.mk0 _ he)
  have h3 : e'.comp (algebraMap A B) = e := IsLocalization.Away.lift_comp _ _
  have h4 : spMap e = spMap e' ≫ spMap (algebraMap A B) := by
    rw [← Spec.map_comp, ← h3]
    rfl
  rw [h4, Category.assoc, ← Category.assoc (spMap (algebraMap A B)), h₁, GlobalTheory.ProjSpace.spMap_pt]
  congr 1
  · rw [← RingHom.comp_assoc, h3]
  · exact funext fun j => RingHom.congr_fun h3 (v j)

end GlobalTheory.ProjHol
end
end

section
section
section

open Filter Polynomial
open GlobalTheory.WeierstrassCurve (affineX affineY)
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ProjHol

open GroundTheory.Global.Elliptic

variable (Λ : PeriodPair) {Ω : ℂ} (W : WeierstrassCurve ℂ)

def IsEvalAt (Ω z : ℂ) (e : W.toAffine.CoordinateRing →+* ℂ) : Prop :=
  (∀ r, e (algebraMap ℂ _ r) = r) ∧ e (affineX W) = Λ.weierstrassP z / Ω ^ 2 ∧
    e (affineY W) = Λ.derivWeierstrassP z / (2 * Ω ^ 3)

theorem exists_quotient (hΩ : Ω ≠ 0) {f : ℂ → ℂ} (hf : IsEllipticFunction Λ f) :
    ∃ a d : W.toAffine.CoordinateRing, ∀ᶠ z in codiscrete ℂ, ∀ e, IsEvalAt Λ W Ω z e →
      e d ≠ 0 ∧ e a = e d * f z := by
  obtain ⟨P, Q, R, S, hQ, hS, h⟩ := exists_rational_weierstrassP hf
  let t : ℂ[X] → W.toAffine.CoordinateRing := fun p =>
    p.eval₂ (algebraMap ℂ _) (algebraMap ℂ _ (Ω ^ 2) * affineX W)
  refine ⟨t P * t S + algebraMap ℂ _ (2 * Ω ^ 3) * affineY W * t R * t Q, t Q * t S, ?_⟩
  filter_upwards [h, eventually_codiscrete_eval_weierstrassP_ne_zero (L := Λ) hQ,
    eventually_codiscrete_eval_weierstrassP_ne_zero (L := Λ) hS] with z hz h1 h2 e ⟨e0, ex, ey⟩
  have ht : ∀ p, e (t p) = p.eval (Λ.weierstrassP z) := fun p => by
    have h3 : e.comp (algebraMap ℂ _) = RingHom.id ℂ := RingHom.ext e0
    rw [hom_eval₂, h3, map_mul, e0, ex, mul_div_cancel₀ _ (pow_ne_zero 2 hΩ), eval₂_id]
  simp only [map_add, map_mul, ht, e0, ey, hz]
  refine ⟨mul_ne_zero h1 h2, ?_⟩
  field_simp

theorem exists_vector (hΩ : Ω ≠ 0) {ι : Type} [Fintype ι] {f : ι → ℂ → ℂ} (hf : ∀ j, IsEllipticFunction Λ (f j)) :
    ∃ v : ι → W.toAffine.CoordinateRing, ∀ᶠ z in codiscrete ℂ, ∀ e, IsEvalAt Λ W Ω z e →
      ∃ c : ℂ, c ≠ 0 ∧ ∀ j, e (v j) = c * f j z := by
  classical
  choose a d h using fun j => exists_quotient Λ W hΩ (hf j)
  refine ⟨fun j => a j * ∏ i ∈ Finset.univ.erase j, d i, ?_⟩
  filter_upwards [eventually_all.2 h] with z hz e he
  refine ⟨∏ i, e (d i), Finset.prod_ne_zero_iff.2 fun i _ => (hz i e he).1, fun j => ?_⟩
  rw [map_mul, map_prod, (hz j e he).2, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  ring

end GlobalTheory.ProjHol

end

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

namespace GlobalTheory.CMTorsion

open Filter Topology GlobalTheory.ProjHol

theorem curve_Δ_ne_zero (Λ : PeriodPair) (Ω : ℂ) (hΩ : Ω ≠ 0) : (curve Λ Ω).Δ ≠ 0 := by
  have h := GlobalTheory.latticeCurve_Δ_ne_zero Λ
  rw [GlobalTheory.latticeCurve_Δ] at h
  have e : (curve Λ Ω).Δ = (Λ.g₂ ^ 3 - 27 * Λ.g₃ ^ 2) / Ω ^ 12 := by
    simp only [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    field_simp
    ring
  rw [e]
  exact div_ne_zero h (pow_ne_zero _ hΩ)

theorem eventually_nhdsNE_of_codiscrete {p : ℂ → Prop} (h : ∀ᶠ z in codiscrete ℂ, p z) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, p w := by
  have := mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h z (Set.mem_univ z)
  simpa [Filter.Eventually] using this

theorem exists_hom_of_periodic_holomorphic : ∀ (Λ : PeriodPair) (Ω : ℂ), Ω ≠ 0 → ∀ (N : ℕ) (φ : ℂ → (Sp ℂ ⟶ PSpace ℂ N)), (∀ z, φ z ≫ PSpace.str ℂ N = 𝟙 _) → (∀ z, ∀ l ∈ Λ.lattice, φ (z + l) = φ z) → (∀ (U : (PSpace ℂ N).Opens) (s : Γ(PSpace ℂ N, U)), IsOpen {z | ⊤ ≤ (φ z) ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun z => valAt' (φ z) U s) {z | ⊤ ≤ (φ z) ⁻¹ᵁ U}) → ∃ ψ : scheme (curve Λ Ω) ⟶ PSpace ℂ N, ψ ≫ PSpace.str ℂ N = toSpec (curve Λ Ω) ∧ ∀ z, pt Λ Ω z ≫ ψ = φ z := by
  intro Λ Ω hΩ N φ hstr hper hhol
  have hH : IsHolTo (Set.univ : Set ℂ) φ := fun U s => by
    simpa only [Set.mem_univ, true_and] using hhol U s
  have : (curve Λ Ω).IsElliptic := ⟨IsUnit.mk0 _ (curve_Δ_ne_zero Λ Ω hΩ)⟩
  obtain ⟨k, hk⟩ := exists_inChart (φ 0)
  obtain ⟨v, hv⟩ := exists_vector Λ (curve Λ Ω) hΩ (f := fun j w => rv (φ w) k j)
    fun j => ⟨meromorphic_rv hH hk j, fun z l hl => by simp only [hper z l hl]⟩
  have hev : ∀ z₀, ∀ᶠ z in 𝓝[≠] z₀, InChart (φ z) k ∧
      ∃ e : (curve Λ Ω).toAffine.CoordinateRing →+* ℂ, (∀ r, e (algebraMap ℂ _ r) = r) ∧
        pt Λ Ω z = spMap e ≫ GlobalTheory.WeierstrassCurve.chartZ (curve Λ Ω) ∧
        ∃ c : ℂ, c ≠ 0 ∧ ∀ j, e (v j) = c * rv (φ z) k j := fun z₀ => by
    have hl : ∀ᶠ z in 𝓝[≠] z₀, z ∉ Λ.lattice := by
      filter_upwards [nhdsWithin_le_nhds (Λ.compl_lattice_sdiff_singleton_mem_nhds z₀), self_mem_nhdsWithin]
        with z h1 h2 h3 using h1 ⟨h3, h2⟩
    filter_upwards [eventually_nhdsNE_inChart hH hk z₀, eventually_nhdsNE_of_codiscrete hv z₀, hl] with z h1 h2 h3
    have h4 := GlobalTheory.WeierstrassCurve.affineEval_algebraMap (curve Λ Ω) (RingHom.id ℂ) _ _
      (HolPt.affine_equation Λ Ω hΩ z h3)
    exact ⟨h1, _, h4, HolPt.pt_eq_chartZ Λ Ω hΩ z h3, h2 _ ⟨h4,
      GlobalTheory.WeierstrassCurve.affineEval_affineX .., GlobalTheory.WeierstrassCurve.affineEval_affineY ..⟩⟩
  have hvk : v k ≠ 0 := by
    obtain ⟨z, h1, e, -, -, c, hc, h⟩ := (hev 0).exists
    intro h0
    have := h k
    rw [h0, map_zero, rv_self h1, _root_.mul_one] at this
    exact hc this.symm
  obtain ⟨ψ, hψ, hpt⟩ := exists_extend (curve Λ Ω) v k hvk
  have hs : ∀ z, (pt Λ Ω z ≫ ψ) ≫ PSpace.str ℂ N = φ z ≫ PSpace.str ℂ N := fun z => by
    rw [hstr, Category.assoc, hψ, pt, GlobalTheory.WeierstrassCurve.ptHom_toSpec]
    exact Spec.map_id _
  refine ⟨ψ, hψ, fun z₀ => eq_of_eventuallyEq
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp (HolPt.isHolTo_pt Λ Ω hΩ) ψ) hH (hs z₀) ?_⟩
  filter_upwards [hev z₀] with z ⟨h1, e, _, h2, c, hc, h⟩
  have h3 : e (v k) = c := by rw [h, rv_self h1, _root_.mul_one]
  have h4 : (e ∘ v) k ≠ 0 := h3.trans_ne hc
  have h5 : Ideal.span (Set.range (e ∘ v)) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨k, rfl⟩) (IsUnit.mk0 _ h4)
  have h6 : pt Λ Ω z ≫ ψ = GlobalTheory.ProjSpace.pt (e.comp (algebraMap ℂ _)) (e ∘ v) h5 := by
    rw [h2, Category.assoc, hpt e h4 h5]
  refine eq_of_rv_eq (hs z) (h6 ▸ inChart_pt _ _ h5 h4) h1 fun j => ?_
  rw [h6, rv_pt _ _ h5 h4, Function.comp_apply, Function.comp_apply, h3, h, mul_div_cancel_left₀ _ hc]

end GlobalTheory.CMTorsion
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_map_to_projective_space : ∀ (Λ : PeriodPair) (Ω : ℂ), Ω ≠ 0 → ∀ (N : ℕ) (φ : ℂ → (Sp ℂ ⟶ PSpace ℂ N)), (∀ z, φ z ≫ PSpace.str ℂ N = 𝟙 _) → (∀ z, ∀ l ∈ Λ.lattice, φ (z + l) = φ z) → (∀ (U : (PSpace ℂ N).Opens) (s : Γ(PSpace ℂ N, U)), IsOpen {z | ⊤ ≤ (φ z) ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun z => valAt' (φ z) U s) {z | ⊤ ≤ (φ z) ⁻¹ᵁ U}) → ∃ ψ : scheme (curve Λ Ω) ⟶ PSpace ℂ N, ψ ≫ PSpace.str ℂ N = toSpec (curve Λ Ω) ∧ ∀ z, pt Λ Ω z ≫ ψ = φ z := by
  atlas_forward_decl GlobalTheory.CMTorsion.exists_hom_of_periodic_holomorphic
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.CMTorsion.AlgMap

theorem exists_totPos (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) : ∃ c : 𝔠.elt, IsTotPos (c : F) := by
  have h0 : (𝔠 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := 𝔠.ne_zero
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := ((𝔠 : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F)) (by
    intro h; exact h0 (FractionalIdeal.coeToSubmodule_injective (by simpa using h)))
  obtain ⟨a, ha, hint⟩ := (𝔠 : FractionalIdeal (𝓞 F)⁰ F).isFractional
  obtain ⟨y, hy⟩ := hint x hx
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero, Algebra.smul_def] at hy
    exact mul_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 ha0) hx0 hy.symm
  have hm := Ideal.absNorm_mem (Ideal.span {y})
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hm
  set m := Ideal.absNorm (Ideal.span {y})
  have hm0 : m ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hy0
  have hmem : (m : F) ∈ 𝔠.elt := by
    have e : (m : F) = t • (a • x) := by
      rw [← hy, Algebra.smul_def, ← map_mul, ht, map_natCast]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hx)
  refine ⟨⟨_, hmem⟩, fun τ => ?_⟩
  simp only [map_natCast]
  exact_mod_cast Nat.pos_of_ne_zero hm0

end GlobalTheory.CMTorsion.AlgMap

namespace GlobalTheory.CMTorsion.AlgMap

theorem valAt'_comp {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' (x ≫ φ) U f = valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) := by
  unfold valAt'
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U)
  · rw [dif_pos h, dif_pos (show ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U from h)]
    unfold valAt
    congr 1
  · rw [dif_neg h, dif_neg (show ¬ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U from h)]

theorem factor : ∀ (Λ : PeriodPair) (Ω : ℂ), Ω ≠ 0 → ∀ (Y : Scheme.{0}) (N : ℕ) (i : Y ⟶ PSpace ℂ N),
    IsClosedImmersion i → ∀ (ψ : scheme (curve Λ Ω) ⟶ PSpace ℂ N) (φ : ℂ → (Sp ℂ ⟶ Y)),
    (∀ z, pt Λ Ω z ≫ ψ = φ z ≫ i) → ∃ f : scheme (curve Λ Ω) ⟶ Y, f ≫ i = ψ := by
  intro Λ Ω hΩ Y N i hi ψ φ h
  refine GlobalTheory.AbelianSubgroupFinite.exists_lift_of_range_subset ψ i ?_
  have hc : IsClosed (ψ ⁻¹' Set.range i) := i.isClosedEmbedding.isClosed_range.preimage ψ.continuous
  have hJ : JacobsonSpace (scheme (curve Λ Ω)) := LocallyOfFiniteType.jacobsonSpace (toSpec (curve Λ Ω))
  have hcp : closedPoints (scheme (curve Λ Ω)) ⊆ ψ ⁻¹' Set.range i := by
    intro y hy
    have hy₁ : IsClosed {y} := hy
    obtain ⟨z, hz⟩ := GlobalTheory.T.elliptic_section_from_uniformization Λ Ω hΩ (pointOfClosedPoint (toSpec (curve Λ Ω)) y hy₁)
      (pointOfClosedPoint_comp _ _ _)
    obtain ⟨a⟩ : Nonempty (Sp ℂ) := inferInstance
    have hy' : pt Λ Ω z a = y := by rw [hz, pointOfClosedPoint_apply]
    refine ⟨φ z a, ?_⟩
    rw [← hy']
    simpa [Scheme.Hom.comp_apply] using (congrArg (fun g : Sp ℂ ⟶ PSpace ℂ N => g a) (h z)).symm
  have hu : closure (closedPoints (scheme (curve Λ Ω))) = Set.univ := by
    have := JacobsonSpace.closure_inter_closedPoints_eq_closure (X := scheme (curve Λ Ω)) (S := Set.univ) isOpen_univ.isLocallyClosed
    rwa [Set.univ_inter, closure_univ] at this
  rintro _ ⟨y, rfl⟩
  have : y ∈ closure (closedPoints (scheme (curve Λ Ω))) := hu ▸ Set.mem_univ y
  exact (closure_minimal hcp hc) this

theorem main : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt) (n : ℕ) (u : HolUnif X.A (X.diag c) n) (Λ : PeriodPair) (Ω : ℂ), Ω ≠ 0 → ∀ β : Fin n → ℂ, (∀ l ∈ Λ.lattice, l • β ∈ u.Λ) → ∃ f : scheme (curve Λ Ω) ⟶ X.A.left, f ≫ X.A.hom = toSpec (curve Λ Ω) ∧ ∀ z, pt Λ Ω z ≫ f = (u.ex (z • β)).left := by
  intro F _ _ 𝔠 X c n u Λ Ω hΩ β hβ
  obtain ⟨c', hc'⟩ := exists_totPos F 𝔠
  obtain ⟨N, i, hi, hstr⟩ := GlobalTheory.RealMult.ProjOverC.isProjOver_A F 𝔠 X c' hc'
  let φ : ℂ → (Sp ℂ ⟶ X.A.left) := fun z => (u.ex (z • β)).left
  have hcomp : ∀ z, (φ z ≫ i) ≫ PSpace.str ℂ N = 𝟙 _ := fun z => by
    rw [Category.assoc, hstr]
    exact Over.w (u.ex (z • β))
  have hper : ∀ z, ∀ l ∈ Λ.lattice, φ (z + l) ≫ i = φ z ≫ i := fun z l hl => by
    have e : u.ex ((z + l) • β) = u.ex (z • β) := by
      rw [add_smul, u.ex_add, (u.ker _).2 (hβ l hl), _root_.mul_one]
    simp only [φ, e]
  have hhol : ∀ (U : (PSpace ℂ N).Opens) (s : Γ(PSpace ℂ N, U)), IsOpen {z | ⊤ ≤ (φ z ≫ i) ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (φ z ≫ i) U s) {z | ⊤ ≤ (φ z ≫ i) ⁻¹ᵁ U} := fun U s => by
    obtain ⟨h1, h2⟩ := u.hol (i ⁻¹ᵁ U) ((i.app U).hom s)
    have hL : Differentiable ℂ (fun z : ℂ => z • β) := differentiable_id.smul_const β
    have hset : {z : ℂ | ⊤ ≤ (φ z ≫ i) ⁻¹ᵁ U} = (fun z : ℂ => z • β) ⁻¹' {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ (i ⁻¹ᵁ U)} := rfl
    rw [hset]
    refine ⟨h1.preimage hL.continuous, ?_⟩
    have e : (fun z => valAt' (φ z ≫ i) U s) = (fun w => valAt' (u.ex w).left (i ⁻¹ᵁ U) ((i.app U).hom s)) ∘ (fun z : ℂ => z • β) :=
      funext fun z => valAt'_comp _ _ _ _
    rw [e]
    exact h2.comp hL.differentiableOn (fun z hz => hz)
  obtain ⟨ψ, hψ1, hψ2⟩ := GlobalTheory.T.holomorphic_map_to_projective_space Λ Ω hΩ N (fun z => φ z ≫ i) hcomp hper hhol
  obtain ⟨f, hf⟩ := factor Λ Ω hΩ X.A.left N i hi ψ φ hψ2
  refine ⟨f, ?_, fun z => ?_⟩
  · rw [← hstr, ← Category.assoc, hf, hψ1]
  · rw [← cancel_mono i, Category.assoc, hf, hψ2]

end GlobalTheory.CMTorsion.AlgMap
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_curve_map_to_abelian : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt) (n : ℕ) (u : HolUnif X.A (X.diag c) n) (Λ : PeriodPair) (Ω : ℂ), Ω ≠ 0 → ∀ β : Fin n → ℂ, (∀ l ∈ Λ.lattice, l • β ∈ u.Λ) → ∃ f : scheme (curve Λ Ω) ⟶ X.A.left, f ≫ X.A.hom = toSpec (curve Λ Ω) ∧ ∀ z, pt Λ Ω z ≫ f = (u.ex (z • β)).left := by
  atlas_forward_decl GlobalTheory.CMTorsion.AlgMap.main
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_map_uniformization_line : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt) (n : ℕ) (u : HolUnif X.A (X.diag c) n) (Λ : PeriodPair) (Ω : ℂ), Ω ≠ 0 → ∀ f : scheme (curve Λ Ω) ⟶ X.A.left, f ≫ X.A.hom = toSpec (curve Λ Ω) → ∀ e : ℂ → (𝟙_ (Over (Sp ℂ)) ⟶ X.A), (∀ z w, e (z + w) = e z * e w) → (∀ z, (e z).left = pt Λ Ω z ≫ f) → ∃ β₁ : Fin n → ℂ, ∀ z, pt Λ Ω z ≫ f = (u.ex (z • β₁)).left := by
  first | exact @GlobalTheory.CMTorsion.exists_vector_of_additive_curve_hom | exact GlobalTheory.CMTorsion.exists_vector_of_additive_curve_hom | (intros; apply GlobalTheory.CMTorsion.exists_vector_of_additive_curve_hom <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

noncomputable section

namespace GlobalTheory.CMTorsionTangent

open Filter Topology

def locZ (Λ : PeriodPair) (Ω t : ℂ) : ℂ :=
  2 * Ω * (t + t ^ 3 * Λ.weierstrassPExcept 0 t) / (2 - t ^ 3 * Λ.derivWeierstrassPExcept 0 t)

def locW (Λ : PeriodPair) (Ω t : ℂ) : ℂ :=
  2 * Ω ^ 3 * t ^ 3 / (2 - t ^ 3 * Λ.derivWeierstrassPExcept 0 t)

theorem eventually_den_ne (Λ : PeriodPair) :
    ∀ᶠ t in 𝓝 (0 : ℂ), 2 - t ^ 3 * Λ.derivWeierstrassPExcept 0 t ≠ 0 := by
  have hc : ContinuousAt (fun t : ℂ => 2 - t ^ 3 * Λ.derivWeierstrassPExcept 0 t) 0 :=
    continuousAt_const.sub ((continuousAt_id.pow 3).mul (Λ.analyticAt_derivWeierstrassPExcept 0).continuousAt)
  exact hc.eventually_ne (by simp)

theorem hasDerivAt_locZ (Λ : PeriodPair) (Ω : ℂ) : HasDerivAt (locZ Λ Ω) Ω 0 := by
  have hP := (Λ.analyticAt_weierstrassPExcept 0).differentiableAt.hasDerivAt
  have hP' := (Λ.analyticAt_derivWeierstrassPExcept 0).differentiableAt.hasDerivAt
  have hn := ((hasDerivAt_id (0 : ℂ)).add ((hasDerivAt_pow 3 (0 : ℂ)).mul hP)).const_mul (2 * Ω)
  have hd := (hasDerivAt_const (0 : ℂ) (2 : ℂ)).sub ((hasDerivAt_pow 3 (0 : ℂ)).mul hP')
  refine ((hn.div hd (by simp)).congr_deriv (by simp; ring)).congr_of_eventuallyEq
    (Eventually.of_forall fun t => ?_)
  simp [locZ]

theorem hasDerivAt_locW (Λ : PeriodPair) (Ω : ℂ) : HasDerivAt (locW Λ Ω) 0 0 := by
  have hP' := (Λ.analyticAt_derivWeierstrassPExcept 0).differentiableAt.hasDerivAt
  have hn := (hasDerivAt_pow 3 (0 : ℂ)).const_mul (2 * Ω ^ 3)
  have hd := (hasDerivAt_const (0 : ℂ) (2 : ℂ)).sub ((hasDerivAt_pow 3 (0 : ℂ)).mul hP')
  refine ((hn.div hd (by simp)).congr_deriv (by simp)).congr_of_eventuallyEq
    (Eventually.of_forall fun t => ?_)
  simp [locW]

theorem pt_eq_ptHom (Λ : PeriodPair) {Ω : ℂ} (hΩ : Ω ≠ 0) :
    ∀ᶠ t in 𝓝 (0 : ℂ), ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol ((curve Λ Ω).map (RingHom.id ℂ))
      ![locZ Λ Ω t, -1, locW Λ Ω t],
      pt Λ Ω t = GlobalTheory.WeierstrassCurve.ptHom (curve Λ Ω) (RingHom.id ℂ) _ h := by
  filter_upwards [eventually_den_ne Λ, Λ.compl_lattice_sdiff_singleton_mem_nhds 0] with t hden hlat
  obtain ⟨c, hc, e⟩ : ∃ c : ℂ, IsUnit c ∧ ![locZ Λ Ω t, -1, locW Λ Ω t] = c • coords Λ Ω t := by
    by_cases ht : t = 0
    · subst ht
      refine ⟨-1, isUnit_one.neg, ?_⟩
      ext i; fin_cases i <;> simp [coords, locZ, locW]
    · have hl : t ∉ Λ.lattice := fun h => hlat ⟨h, ht⟩
      have hP := Λ.weierstrassPExcept_def 0 t
      have hP' := Λ.derivWeierstrassPExcept_def 0 t
      simp only [ZeroMemClass.coe_zero, sub_zero, div_zero, zero_sub] at hP hP'
      have hd : Λ.derivWeierstrassP t ≠ 0 := by
        intro h0
        apply hden
        rw [hP', h0]
        field_simp
        ring
      refine ⟨-(2 * Ω ^ 3 / Λ.derivWeierstrassP t), (neg_ne_zero.2 (div_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 3 hΩ)) hd)).isUnit, ?_⟩
      ext i; fin_cases i
      · simp [coords, hl, locZ]
        rw [hP, hP']
        field_simp
        ring
      · simp [coords, hl]
        field_simp
      · simp [coords, hl, locW]
        rw [hP']
        field_simp
        ring
  have h0 := isUnimodularSol_coords Λ Ω t
  refine ⟨e ▸ h0.smul hc, ?_⟩
  exact (GlobalTheory.WeierstrassCurve.ptHom_smul _ _ _ h0 hc).symm.trans
    (GlobalTheory.WeierstrassCurve.ptHom_congr _ _ _ _ rfl e.symm _)

end GlobalTheory.CMTorsionTangent

namespace GlobalTheory.CMTorsionTangent

open Filter Topology
open GlobalTheory.WeierstrassCurve (ptHom OriginRing originEval originZ originW chartY coordOpen originPolynomial)

variable (Λ : PeriodPair) (Ω : ℂ)

def epsEval (c : ℂ) : OriginRing (curve Λ Ω) →+* DualNumber ℂ :=
  originEval (curve Λ Ω) (algebraMap ℂ (DualNumber ℂ)) (c • DualNumber.eps) 0
    (isUnimodularSol_tan (curve Λ Ω) c).equation

open Classical in

def locEval (t : ℂ) (r : OriginRing (curve Λ Ω)) : ℂ :=
  if h : ((curve Λ Ω).map (RingHom.id ℂ)).toProjective.Equation ![locZ Λ Ω t, -1, locW Λ Ω t] then
    originEval (curve Λ Ω) (RingHom.id ℂ) _ _ h r else 0

theorem epsEval_fst (c : ℂ) (r : OriginRing (curve Λ Ω)) (h0 : ((curve Λ Ω).map (RingHom.id ℂ)).toProjective.Equation
    ![locZ Λ Ω 0, -1, locW Λ Ω 0]) :
    (epsEval Λ Ω c r).fst = originEval (curve Λ Ω) (RingHom.id ℂ) _ _ h0 r := by
  have : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (epsEval Λ Ω c) =
      originEval (curve Λ Ω) (RingHom.id ℂ) _ _ h0 := by
    refine GlobalTheory.WeierstrassCurve.origin_hom_ext _ (fun a => ?_) ?_ ?_ <;>
      simp [epsEval, locZ, locW]
  exact congrArg (fun φ : OriginRing (curve Λ Ω) →+* ℂ => φ r) this

theorem epsEval_snd (c : ℂ) (r : OriginRing (curve Λ Ω)) :
    (epsEval Λ Ω c r).snd = c * (epsEval Λ Ω 1 r).snd := by
  have : (epsScaleR c).comp (epsEval Λ Ω 1) = epsEval Λ Ω c := by
    refine GlobalTheory.WeierstrassCurve.origin_hom_ext _ (fun a => ?_) ?_ ?_ <;>
      simp [epsEval, epsScaleR]
    exact TrivSqZeroExt.ext (by simp) (by simp)
  rw [← this]
  simp [epsScaleR]

variable {Λ Ω}

theorem eventually_equation (hΩ : Ω ≠ 0) : ∀ᶠ t in 𝓝 (0 : ℂ),
    ((curve Λ Ω).map (RingHom.id ℂ)).toProjective.Equation ![locZ Λ Ω t, -1, locW Λ Ω t] := by
  filter_upwards [pt_eq_ptHom Λ hΩ] with t ⟨h, _⟩
  exact h.equation

theorem hasDerivAt_locEval (hΩ : Ω ≠ 0) (r : OriginRing (curve Λ Ω)) :
    HasDerivAt (fun t => locEval Λ Ω t r) (Ω * (epsEval Λ Ω 1 r).snd) 0 := by
  have hev := eventually_equation (Λ := Λ) hΩ
  have h0 := hev.self_of_nhds
  have hE : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ a b : OriginRing (curve Λ Ω),
      locEval Λ Ω t (a * b) = locEval Λ Ω t a * locEval Λ Ω t b ∧
      locEval Λ Ω t (a + b) = locEval Λ Ω t a + locEval Λ Ω t b ∧
      locEval Λ Ω t (-a) = - locEval Λ Ω t a := by
    filter_upwards [hev] with t ht a b
    simp only [locEval, dif_pos ht, map_mul, map_add, map_neg, and_self]
  have hE0 : ∀ a, locEval Λ Ω 0 a = (epsEval Λ Ω 1 a).fst := fun a => by
    rw [locEval, dif_pos h0, epsEval_fst Λ Ω 1 a h0]
  have hconst : ∀ a : ℂ, HasDerivAt (fun t => locEval Λ Ω t (algebraMap ℂ _ a))
      (Ω * (epsEval Λ Ω 1 (algebraMap ℂ _ a)).snd) 0 := fun a => by
    refine ((hasDerivAt_const (0 : ℂ) a).congr_deriv (by simp [epsEval, TrivSqZeroExt.algebraMap_eq_inl])).congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    rw [locEval, dif_pos ht]
    simp
  let S : Subring (OriginRing (curve Λ Ω)) :=
    { carrier := {r | HasDerivAt (fun t => locEval Λ Ω t r) (Ω * (epsEval Λ Ω 1 r).snd) 0}
      mul_mem' := fun {a b} ha hb => by
        refine ((ha.mul hb).congr_deriv ?_).congr_of_eventuallyEq ?_
        · simp only [map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
            MulOpposite.unop_op, hE0]
          ring
        · filter_upwards [hE] with t ht
          exact (ht a b).1
      one_mem' := by simpa using hconst 1
      add_mem' := fun {a b} ha hb => by
        refine ((ha.add hb).congr_deriv ?_).congr_of_eventuallyEq ?_
        · simp only [map_add, TrivSqZeroExt.snd_add]
          ring
        · filter_upwards [hE] with t ht
          exact (ht a b).2.1
      zero_mem' := by simpa using hconst 0
      neg_mem' := fun {a} ha => by
        refine (ha.neg.congr_deriv ?_).congr_of_eventuallyEq ?_
        · simp only [map_neg, TrivSqZeroExt.snd_neg]
          ring
        · filter_upwards [hE] with t ht
          exact (ht a a).2.2 }
  have hC : ∀ a : ℂ, algebraMap ℂ (OriginRing (curve Λ Ω)) a ∈ S := hconst
  have hZ : originZ (curve Λ Ω) ∈ S := by
    change HasDerivAt _ _ _
    refine ((hasDerivAt_locZ Λ Ω).congr_deriv (by simp [epsEval])).congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    rw [locEval, dif_pos ht]
    simp
  have hW : originW (curve Λ Ω) ∈ S := by
    change HasDerivAt _ _ _
    refine ((hasDerivAt_locW Λ Ω).congr_deriv (by simp [epsEval])).congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    rw [locEval, dif_pos ht]
    simp
  have hCa : ∀ a : Polynomial ℂ, AdjoinRoot.mk (originPolynomial (curve Λ Ω)) (Polynomial.C a) ∈ S := by
    intro a
    induction a using Polynomial.induction_on with
    | C b => exact hC b
    | add p q hp hq => rw [Polynomial.C_add, map_add]; exact S.add_mem hp hq
    | monomial n b _ =>
      rw [Polynomial.C_mul, Polynomial.C_pow, map_mul, map_pow]
      exact S.mul_mem (hC b) (S.pow_mem hW _)
  have hall : ∀ x, x ∈ S := by
    intro x
    refine AdjoinRoot.induction_on (f := originPolynomial (curve Λ Ω)) x fun p => ?_
    induction p using Polynomial.induction_on with
    | C a => exact hCa a
    | add p q hp hq => rw [map_add]; exact S.add_mem hp hq
    | monomial n a _ =>
      rw [map_mul, map_pow]
      exact S.mul_mem (hCa a) (S.pow_mem hZ _)
  exact hall r

end GlobalTheory.CMTorsionTangent

namespace GlobalTheory.CMTorsionTangent

open Filter Topology
open GlobalTheory.WeierstrassCurve (ptHom OriginRing originEval originZ originW chartY coordOpen originPolynomial)
open GlobalTheory.TangentOrigin (evalPt evalPt_res evalPt_spMap_comp fstC)

variable {Λ : PeriodPair} {Ω : ℂ}

theorem top_le_chartY : ⊤ ≤ chartY (curve Λ Ω) ⁻¹ᵁ coordOpen (curve Λ Ω) 1 := by
  rw [← GlobalTheory.WeierstrassCurve.opensRange_chartY]
  simp

theorem top_le_comp_chartY {X : Scheme.{0}} (g : X ⟶ Sp (OriginRing (curve Λ Ω))) :
    ⊤ ≤ (g ≫ chartY (curve Λ Ω)) ⁻¹ᵁ coordOpen (curve Λ Ω) 1 := by
  rw [Scheme.Hom.comp_preimage]
  exact fun p _ => top_le_chartY (Set.mem_univ (g.base p))

def chartVal : Γ(scheme (curve Λ Ω), coordOpen (curve Λ Ω) 1) →+* OriginRing (curve Λ Ω) :=
  evalPt (chartY (curve Λ Ω)) _ top_le_chartY

theorem evalPt_chart {R : Type} [CommRing R] (e : OriginRing (curve Λ Ω) →+* R)
    (h : ⊤ ≤ (spMap e ≫ chartY (curve Λ Ω)) ⁻¹ᵁ coordOpen (curve Λ Ω) 1)
    (G : Γ(scheme (curve Λ Ω), coordOpen (curve Λ Ω) 1)) :
    evalPt (spMap e ≫ chartY (curve Λ Ω)) _ h G = e (chartVal G) :=
  evalPt_spMap_comp e _ _ top_le_chartY h G

theorem tan_eq (c : ℂ) : tan (curve Λ Ω) c = spMap (epsEval Λ Ω c) ≫ chartY (curve Λ Ω) :=
  (GlobalTheory.WeierstrassCurve.SpecMap_originEval_chartY _ _ _ _ _).symm

theorem eventually_pt_eq (hΩ : Ω ≠ 0) : ∀ᶠ t in 𝓝 (0 : ℂ), ∃ h : ((curve Λ Ω).map (RingHom.id ℂ)).toProjective.Equation
    ![locZ Λ Ω t, -1, locW Λ Ω t],
    pt Λ Ω t = spMap (originEval (curve Λ Ω) (RingHom.id ℂ) _ _ h) ≫ chartY (curve Λ Ω) := by
  filter_upwards [pt_eq_ptHom Λ hΩ] with t ⟨h, e⟩
  exact ⟨h.equation, e.trans (GlobalTheory.WeierstrassCurve.SpecMap_originEval_chartY _ _ _ _ _).symm⟩

theorem eventually_valAt' (hΩ : Ω ≠ 0) (G : Γ(scheme (curve Λ Ω), coordOpen (curve Λ Ω) 1)) :
    ∀ᶠ t in 𝓝 (0 : ℂ), ⊤ ≤ pt Λ Ω t ⁻¹ᵁ coordOpen (curve Λ Ω) 1 ∧
      valAt' (pt Λ Ω t) _ G = locEval Λ Ω t (chartVal G) := by
  filter_upwards [eventually_pt_eq (Λ := Λ) hΩ] with t ⟨h, e⟩
  have key : ∀ (x : Sp ℂ ⟶ scheme (curve Λ Ω)), x = spMap (originEval (curve Λ Ω) (RingHom.id ℂ) _ _ h) ≫
      chartY (curve Λ Ω) → ⊤ ≤ x ⁻¹ᵁ coordOpen (curve Λ Ω) 1 ∧ valAt' x _ G = locEval Λ Ω t (chartVal G) := by
    rintro _ rfl
    refine ⟨top_le_comp_chartY _, ?_⟩
    rw [GlobalTheory.TangentOrigin.valAt'_eq_evalPt _ _ (top_le_comp_chartY _), evalPt_chart, locEval, dif_pos h]
  exact key _ e

theorem spMap_fst_tan (hΩ : Ω ≠ 0) (c : ℂ) : spMap fstC ≫ tan (curve Λ Ω) c = pt Λ Ω 0 := by
  obtain ⟨h, e⟩ := (pt_eq_ptHom Λ hΩ).self_of_nhds
  rw [e, tan, GlobalTheory.WeierstrassCurve.SpecMap_ptHom]
  refine GlobalTheory.WeierstrassCurve.ptHom_congr _ _ _ _ (RingHom.ext fun a => by simp) ?_ _
  ext i; fin_cases i <;> simp [locZ, locW]

theorem exists_deriv (hΩ : Ω ≠ 0) (c : ℂ) (V : (scheme (curve Λ Ω)).Opens) (hT : ⊤ ≤ tan (curve Λ Ω) c ⁻¹ᵁ V)
    (G : Γ(scheme (curve Λ Ω), V)) :
    ∃ d : ℂ, HasDerivAt (fun s => valAt' (pt Λ Ω s) V G) (Ω * d) 0 ∧ (evalPt (tan (curve Λ Ω) c) V hT G).snd = c * d := by
  set U₀ := coordOpen (curve Λ Ω) 1
  have hU₀ : IsAffineOpen U₀ := GlobalTheory.WeierstrassCurve.isAffineOpen_coordOpen _ _
  have hp0 : ⊤ ≤ pt Λ Ω 0 ⁻¹ᵁ V := by
    rw [← spMap_fst_tan hΩ c]; exact (GlobalTheory.TangentOrigin.top_le_preimage_iff _ V).1 hT
  have hp0U : ⊤ ≤ pt Λ Ω 0 ⁻¹ᵁ U₀ := (eventually_valAt' hΩ 0).self_of_nhds.1
  let q : Sp ℂ := (default : PrimeSpectrum ℂ)
  obtain ⟨s, hsV, hs⟩ := hU₀.exists_basicOpen_le (V := V) ⟨(pt Λ Ω 0).base q, hp0 (Set.mem_univ q)⟩
    (hp0U (Set.mem_univ q))
  set B := (scheme (curve Λ Ω)).basicOpen s
  have hB0 : ⊤ ≤ pt Λ Ω 0 ⁻¹ᵁ B := (GlobalTheory.top_le_preimage_iff_mem _ _).2 hs
  have hTB : ⊤ ≤ tan (curve Λ Ω) c ⁻¹ᵁ B := by
    rw [GlobalTheory.TangentOrigin.top_le_preimage_iff, spMap_fst_tan hΩ c]; exact hB0
  have := hU₀.isLocalization_basicOpen s
  obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) (resG _ hsV G)
  change IsLocalization.mk' _ a m = _ at hm
  obtain ⟨n, hn⟩ := m.2
  have hkey := IsLocalization.mk'_spec Γ(scheme (curve Λ Ω), B) a m
  rw [hm] at hkey
  change resG _ hsV G * resG _ ((scheme (curve Λ Ω)).basicOpen_le s) m.1 =
    resG _ ((scheme (curve Λ Ω)).basicOpen_le s) a at hkey

  have hX := congrArg (evalPt (tan (curve Λ Ω) c) B hTB) hkey
  have hTU : ⊤ ≤ tan (curve Λ Ω) c ⁻¹ᵁ U₀ := fun p hp => (scheme (curve Λ Ω)).basicOpen_le s (hTB hp)
  rw [map_mul, evalPt_res _ _ hT, evalPt_res _ _ hTU, evalPt_res _ _ hTU] at hX
  have ht : ∀ G' : Γ(scheme (curve Λ Ω), U₀), evalPt (tan (curve Λ Ω) c) U₀ hTU G' = epsEval Λ Ω c (chartVal G') := by
    intro G'
    have key : ∀ (x : Sp (DualNumber ℂ) ⟶ scheme (curve Λ Ω)) (hx : ⊤ ≤ x ⁻¹ᵁ U₀),
        x = spMap (epsEval Λ Ω c) ≫ chartY (curve Λ Ω) → evalPt x U₀ hx G' = epsEval Λ Ω c (chartVal G') := by
      rintro _ hx rfl; exact evalPt_chart _ hx G'
    exact key _ hTU (tan_eq c)
  rw [ht, ht] at hX

  have hev := eventually_equation (Λ := Λ) hΩ
  have h0 := hev.self_of_nhds
  have hda := hasDerivAt_locEval hΩ (chartVal a)
  have hdm := hasDerivAt_locEval hΩ (chartVal m.1)
  have hds := hasDerivAt_locEval hΩ (chartVal s)
  have hm0 : locEval Λ Ω 0 (chartVal m.1) ≠ 0 := by
    have e1 := (eventually_valAt' hΩ s).self_of_nhds.2
    have e2 := (GlobalTheory.top_le_preimage_basicOpen_iff (pt Λ Ω 0) U₀ s).1 hB0
    rw [e1] at e2
    rw [← hn, map_pow, locEval, dif_pos h0, map_pow]
    rw [locEval, dif_pos h0] at e2
    exact pow_ne_zero _ e2
  have hsne : ∀ᶠ t in 𝓝 (0 : ℂ), locEval Λ Ω t (chartVal s) ≠ 0 := by
    refine hds.continuousAt.eventually_ne ?_
    have e1 := (eventually_valAt' hΩ s).self_of_nhds.2
    have e2 := (GlobalTheory.top_le_preimage_basicOpen_iff (pt Λ Ω 0) U₀ s).1 hB0
    rwa [e1] at e2
  have hmne : ∀ᶠ t in 𝓝 (0 : ℂ), locEval Λ Ω t (chartVal m.1) ≠ 0 :=
    hdm.continuousAt.eventually_ne hm0
  have hH : (fun s' => valAt' (pt Λ Ω s') V G) =ᶠ[𝓝 0]
      fun t => locEval Λ Ω t (chartVal a) / locEval Λ Ω t (chartVal m.1) := by
    filter_upwards [eventually_valAt' hΩ s, eventually_valAt' hΩ a, eventually_valAt' hΩ m.1, hsne, hmne]
      with t ⟨hU, es⟩ ⟨_, ea⟩ ⟨_, em⟩ hs' hm'
    have hBt : ⊤ ≤ pt Λ Ω t ⁻¹ᵁ B := (GlobalTheory.top_le_preimage_basicOpen_iff (pt Λ Ω t) U₀ s).2 (by rwa [es])
    have e := congrArg (valAt' (pt Λ Ω t) B) hkey
    rw [GlobalTheory.valAt'_mul, GlobalTheory.valAt'_res _ _ _ hBt, GlobalTheory.valAt'_res _ _ _ hBt, GlobalTheory.valAt'_res _ _ _ hBt, ea, em] at e
    rw [eq_div_iff hm', e]
  have hE0 : ∀ r, locEval Λ Ω 0 r = (epsEval Λ Ω 1 r).fst := fun r => by
    rw [locEval, dif_pos h0, epsEval_fst Λ Ω 1 r h0]
  have hF : ∀ r, (epsEval Λ Ω c r).fst = (epsEval Λ Ω 1 r).fst := fun r => by
    rw [epsEval_fst Λ Ω c r h0, epsEval_fst Λ Ω 1 r h0]
  have hE0a : locEval Λ Ω 0 (chartVal a) = (epsEval Λ Ω 1 (chartVal a)).fst := hE0 _
  have hE0m : locEval Λ Ω 0 (chartVal m.1) = (epsEval Λ Ω 1 (chartVal m.1)).fst := hE0 _
  have h1 := congrArg TrivSqZeroExt.fst hX
  have h2 := congrArg TrivSqZeroExt.snd hX
  simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, hF, epsEval_snd Λ Ω c] at h1 h2
  have hd := (hda.div hdm hm0).congr_of_eventuallyEq hH
  generalize epsEval Λ Ω 1 (chartVal a) = α at hd hE0a h1 h2
  generalize epsEval Λ Ω 1 (chartVal m.1) = β at hd hE0m h1 h2
  generalize evalPt (tan (curve Λ Ω) c) V hT G = X at h1 h2 ⊢
  rw [hE0a, hE0m] at hd
  rw [hE0m] at hm0
  refine ⟨(α.snd * β.fst - α.fst * β.snd) / β.fst ^ 2, hd.congr_deriv (by field_simp), ?_⟩
  rw [← eq_div_iff hm0] at h1
  rw [h1] at h2
  field_simp at h2 ⊢
  linear_combination h2

end GlobalTheory.CMTorsionTangent

namespace GlobalTheory.CMTorsionTangent

open Filter Topology
open GlobalTheory.TangentOrigin (evalPt fstC)

theorem evalPt_comp {R : Type} [CommRing R] {X Y : Scheme.{0}} (x : Sp R ⟶ X) (f : X ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ (x ≫ f) ⁻¹ᵁ U) (h' : ⊤ ≤ x ⁻¹ᵁ (f ⁻¹ᵁ U)) (F : Γ(Y, U)) :
    evalPt (x ≫ f) U h F = evalPt x (f ⁻¹ᵁ U) h' ((f.app U).hom F) := by
  unfold evalPt
  rw [Scheme.Hom.comp_appLE]
  rfl

theorem isTangent_and_isDiff : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (n : ℕ) (u : HolUnif A L n)
    (Λ : PeriodPair) (Ω : ℂ), Ω ≠ 0 → ∀ (f : scheme (curve Λ Ω) ⟶ A.left) (β₁ : Fin n → ℂ),
    (∀ z, pt Λ Ω z ≫ f = (u.ex (z • β₁)).left) → ∀ (c : ℂ) (v : epsR ℂ ⟶ A),
    v.left = tan (curve Λ Ω) c ≫ f → IsTangent v ∧ u.IsDiff ((c / Ω) • β₁) v := by
  intro A _ L n u Λ Ω hΩ f β₁ hf c v hv
  have he0 : (u.ex 0).left = pt Λ Ω 0 ≫ f := by simpa using (hf 0).symm
  have hT : IsTangent v := by
    change spMap fstC ≫ v.left = _
    rw [hv, ← Category.assoc, spMap_fst_tan hΩ c, ← he0]
    exact GlobalTheory.TangentOrigin.ex_zero_left u
  refine ⟨hT, fun U h F => ?_⟩
  have hTV : ⊤ ≤ tan (curve Λ Ω) c ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← hv]; exact h
  have hL : ∀ (y : Sp (DualNumber ℂ) ⟶ A.left) (hy : ⊤ ≤ y ⁻¹ᵁ U), y = tan (curve Λ Ω) c ≫ f →
      evalPt y U hy F = evalPt (tan (curve Λ Ω) c) _ hTV ((f.app U).hom F) := by
    rintro _ hy rfl; exact evalPt_comp _ f U hy hTV F
  obtain ⟨d, hd, hsnd⟩ := exists_deriv hΩ c (f ⁻¹ᵁ U) hTV ((f.app U).hom F)
  change (evalPt v.left U h F).snd = _
  rw [hL _ h hv, hsnd]
  have hU0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
    rw [he0, Scheme.Hom.comp_preimage, ← spMap_fst_tan hΩ c]
    exact (GlobalTheory.TangentOrigin.top_le_preimage_iff _ _).1 hTV
  have hdiff := GlobalTheory.TangentOrigin.differentiableAt_val u hU0 F
  have hchain : HasDerivAt (fun s : ℂ => valAt' (u.ex (s • β₁)).left U F)
      (fderiv ℂ (fun z => valAt' (u.ex z).left U F) 0 β₁) 0 := by
    have hl : HasDerivAt (fun s : ℂ => s • β₁) β₁ 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const β₁
    have h4 : HasFDerivAt (fun z => valAt' (u.ex z).left U F) (fderiv ℂ (fun z => valAt' (u.ex z).left U F) 0)
        ((0 : ℂ) • β₁) := by rw [zero_smul]; exact hdiff.hasFDerivAt
    exact h4.comp_hasDerivAt (0 : ℂ) hl
  have heq : (fun s : ℂ => valAt' (u.ex (s • β₁)).left U F) =
      fun s => valAt' (pt Λ Ω s) (f ⁻¹ᵁ U) ((f.app U).hom F) := by
    funext s; rw [← hf s, GlobalTheory.valAt'_comp]
  rw [heq] at hchain
  have := hchain.unique hd
  rw [map_smul, this, smul_eq_mul]
  field_simp

end GlobalTheory.CMTorsionTangent
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_map_tangent_differential : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (n : ℕ) (u : HolUnif A L n) (Λ : PeriodPair) (Ω : ℂ), Ω ≠ 0 → ∀ (f : scheme (curve Λ Ω) ⟶ A.left) (β₁ : Fin n → ℂ), (∀ z, pt Λ Ω z ≫ f = (u.ex (z • β₁)).left) → ∀ (c : ℂ) (v : epsR ℂ ⟶ A), v.left = tan (curve Λ Ω) c ≫ f → IsTangent v ∧ u.IsDiff ((c / Ω) • β₁) v := by
  atlas_forward_decl GlobalTheory.CMTorsionTangent.isTangent_and_isDiff
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_approximation_upward_idele : ∀ (K : Type) [Field K] [NumberField K] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (t : (Af K)ˣ) (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c → ∃ (m : ℕ) (b : Fin m → E) (a a' : Fin m → K), (∀ k (r : 𝓞 K), algebraMap K E (r : K) * b k ∈ lattice c y) ∧ x' = ∑ k, algebraMap K E (a' k) * b k ∧ x - ∑ k, algebraMap K E (a k) * b k ∈ lattice c y ∧ ∀ k (v : HeightOneSpectrum (𝓞 K)), Valued.v (((t : Af K) * algebraMap K (Af K) (a' k) - algebraMap K (Af K) (a k)) v) ≤ 1 := by
  first | exact @GlobalTheory.LatDecomp.exists_decomp | exact GlobalTheory.LatDecomp.exists_decomp | (intros; apply GlobalTheory.LatDecomp.exists_decomp <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

theorem GlobalTheory.cmTorsionConj : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left),
        X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p →
        ∀ u' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E)),
 (∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
            v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
              u'.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v') → (∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            (u'.ex (fun j ↦ g (φ (T.U.e j) x'))).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) x)).left) := by
  intro hPC hAD hDC K _ _ d δ io hK hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hTT E _ _ _ _ I _ φ hCM hres c y hc 𝔠 T X' p hpb u' htan
    x x' hxx'
  have hTT' := hTT
  obtain ⟨hΩ₀, hΩ₁, hgio, hΛ₀, -, hg₂, hg₃, -⟩ := hTT'
  have hW : (curve Λ₀ Ω₀).map (g : ℂ →+* ℂ) = curve Λ₁ Ω₁ := curve_map (g : ℂ →+* ℂ) hg₂ hg₃
  obtain ⟨hU1, hE2, hE3⟩ := GlobalTheory.T.conjugate_group_points_injective_mul T.X.A X'.A g p hpb.grp
  obtain ⟨m, b, a, a', hbL, hx', hxL, hint⟩ := GlobalTheory.T.lattice_approximation_upward_idele K E t c y hc x x' hxx'
  have hlat : ∀ z ∈ lattice c y, (fun j ↦ φ (T.U.e j) z) ∈ T.U.u.Λ := fun z hz =>
    (T.U.lat _).2 ⟨z, hz, funext fun j => by simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]⟩
  have hφK : ∀ i (r : K), φ i (algebraMap K E r) = io r := fun i r => by rw [← RingHom.comp_apply, hres i]
  have hpt : ∀ z, pt Λ₁ Ω₁ z ≫ toSpec (curve Λ₁ Ω₁) = 𝟙 _ := fun z => by
    rw [pt, GlobalTheory.WeierstrassCurve.ptHom_toSpec]; simp
  have key : ∀ k, (u'.ex (fun j ↦ g (φ (T.U.e j) (algebraMap K E (a' k) * b k)))).left ≫ p =
      spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) (algebraMap K E (a k) * b k))).left := by
    intro k
    set β : Fin (Module.finrank ℚ (FR E)) → ℂ := fun j ↦ φ (T.U.e j) (b k) with hβdef
    have hβ : ∀ l ∈ Λ₀.lattice, l • β ∈ T.U.u.Λ := by
      intro l hl
      obtain ⟨r, hr, rfl⟩ := ((GlobalTheory.LatVal.CurveTransport.isLatOf_iff).1 hΛ₀ l).1 hl
      obtain ⟨r', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hr
      have h1 := hlat _ (hbL k r')
      convert h1 using 1
      funext j
      simp [β, hφK]
    obtain ⟨f, hfo, hf⟩ := GlobalTheory.T.elliptic_curve_map_to_abelian (FR E) 𝔠 T.X T.U.c _ T.U.u Λ₀ Ω₀ hΩ₀ β hβ
    have hsq : (mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) hW ≫ f) ≫ T.X.A.hom =
        toSpec (curve Λ₁ Ω₁) ≫ spMap (g : ℂ →+* ℂ) := by
      rw [Category.assoc, hfo, GlobalTheory.WeierstrassCurve.mapHom_toSpec]
    let f' := hpb.grp.1.lift _ _ hsq
    have hf'p : f' ≫ p = mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) hW ≫ f := hpb.grp.1.lift_fst _ _ _
    have hf'o : f' ≫ X'.A.hom = toSpec (curve Λ₁ Ω₁) := hpb.grp.1.lift_snd _ _ _
    let e' : ℂ → (𝟙_ (Over (Sp ℂ)) ⟶ X'.A) := fun z => Over.homMk (pt Λ₁ Ω₁ z ≫ f') (by
      rw [Category.assoc, hf'o, hpt]; rfl)
    have hD3 := GlobalTheory.T.conjugate_curve_point_addition_compat Λ₀ Λ₁ Ω₀ Ω₁ g hΩ₀ hΩ₁ hW
    have hover : ∀ z z', pt Λ₁ Ω₁ z' ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) hW = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ z →
        (e' z').left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (z • β)).left := by
      intro z z' hzz
      show (pt Λ₁ Ω₁ z' ≫ f') ≫ p = _
      rw [Category.assoc, hf'p, ← Category.assoc, hzz, Category.assoc, hf]
    have hadd : ∀ z' w', e' (z' + w') = e' z' * e' w' := by
      intro z' w'
      obtain ⟨z, hz⟩ := hD3.1 z'
      obtain ⟨w, hw⟩ := hD3.1 w'
      apply hU1
      rw [hover _ _ (hD3.2 z w z' w' hz hw), hE2 _ _ _ _ (hover _ _ hz) (hover _ _ hw), add_smul, T.U.u.ex_add]
    obtain ⟨β₁, hβ₁⟩ := GlobalTheory.T.elliptic_map_uniformization_line (FR E) 𝔠 X' T.U.c _ u' Λ₁ Ω₁ hΩ₁ f' hf'o e' hadd (fun z => rfl)
    let v : epsR ℂ ⟶ T.X.A := Over.homMk (tan (curve Λ₀ Ω₀) Ω₀ ≫ f) (by
      rw [Category.assoc, hfo, tan, GlobalTheory.WeierstrassCurve.ptHom_toSpec]; rfl)
    let v' : epsR ℂ ⟶ X'.A := Over.homMk (tan (curve Λ₁ Ω₁) ((g : ℂ →+* ℂ) Ω₀) ≫ f') (by
      rw [Category.assoc, hf'o, tan, GlobalTheory.WeierstrassCurve.ptHom_toSpec]; rfl)
    obtain ⟨-, hv⟩ := GlobalTheory.T.elliptic_map_tangent_differential T.X.A _ _ T.U.u Λ₀ Ω₀ hΩ₀ f β hf Ω₀ v rfl
    obtain ⟨hv't, hv'⟩ := GlobalTheory.T.elliptic_map_tangent_differential X'.A _ _ u' Λ₁ Ω₁ hΩ₁ f' β₁ hβ₁ ((g : ℂ →+* ℂ) Ω₀) v' rfl
    rw [div_self hΩ₀, one_smul] at hv
    have hvv : v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left := by
      show (tan (curve Λ₁ Ω₁) ((g : ℂ →+* ℂ) Ω₀) ≫ f') ≫ p = _ ≫ (tan (curve Λ₀ Ω₀) Ω₀ ≫ f)
      rw [Category.assoc, hf'p, ← Category.assoc, GlobalTheory.T.conjugate_curve_tangent_compat _ _ (g : ℂ →+* ℂ) hW Ω₀, Category.assoc]
    have h1 := htan β v v' hvv hv
    have heq := GlobalTheory.T.tangent_differential_unique X'.A _ _ u' v' _ _ hv't hv' h1
    have hgΩ : g Ω₀ ≠ 0 := (map_ne_zero g).2 hΩ₀
    have hβ₁eq : β₁ = fun j ↦ g (β j) := by
      funext j
      have h2 := congrFun heq j
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.coe_toRingHom] at h2
      field_simp at h2
      exact h2
    have hd1 := GlobalTheory.T.conjugate_torsion_point_compat K io g t Λ₀ Λ₁ Ω₀ Ω₁ hTT hW (a k) (a' k) (hint k)
    have e1 : (fun j ↦ g (φ (T.U.e j) (algebraMap K E (a' k) * b k))) = io (a' k) • β₁ := by
      rw [hβ₁eq]; funext j; simp [β, hφK, hgio]
    have e2 : (fun j ↦ φ (T.U.e j) (algebraMap K E (a k) * b k)) = io (a k) • β := by
      funext j; simp [β, hφK]
    rw [e1, e2, ← hβ₁, Category.assoc, hf'p, ← Category.assoc, hd1, Category.assoc, hf]
  have exsum : ∀ {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A] {L : LB A.left} {n : ℕ} (uu : HolUnif A L n)
      (w : Fin m → Fin n → ℂ), uu.ex (∑ k, w k) = ∏ k, uu.ex (w k) := by
    intro A _ _ L n uu w
    induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
    | empty => simpa using (uu.ker 0).2 (zero_mem _)
    | insert k s hk ih => rw [Finset.sum_insert hk, Finset.prod_insert hk, uu.ex_add, ih]
  have hsum' : (fun j ↦ g (φ (T.U.e j) x')) = ∑ k, (fun j ↦ g (φ (T.U.e j) (algebraMap K E (a' k) * b k))) := by
    rw [hx']; funext j; simp [map_sum]
  have hsum : (fun j ↦ φ (T.U.e j) (∑ k, algebraMap K E (a k) * b k)) =
      ∑ k, (fun j ↦ φ (T.U.e j) (algebraMap K E (a k) * b k)) := by
    funext j; simp [map_sum]
  have hxm : T.U.u.ex (fun j ↦ φ (T.U.e j) x) =
      T.U.u.ex (fun j ↦ φ (T.U.e j) (∑ k, algebraMap K E (a k) * b k)) := by
    have h1 := hlat _ hxL
    have e3 : (fun j ↦ φ (T.U.e j) x) = (fun j ↦ φ (T.U.e j) (∑ k, algebraMap K E (a k) * b k)) +
        (fun j ↦ φ (T.U.e j) (x - ∑ k, algebraMap K E (a k) * b k)) := by
      funext j; simp
    rw [e3, T.U.u.ex_add, (T.U.u.ker _).2 h1, _root_.mul_one]
  rw [hxm, hsum', hsum, exsum, exsum]
  exact hE3 (Fin m) Finset.univ _ _ (fun k _ => key k)
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_transport_cm_uniformization : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left),
        X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p →
        ∀ u' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E)),
 (∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
            v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
              u'.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v') → (∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            (u'.ex (fun j ↦ g (φ (T.U.e j) x'))).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) x)).left) := by
  atlas_forward_decl GlobalTheory.cmTorsionConj
end
