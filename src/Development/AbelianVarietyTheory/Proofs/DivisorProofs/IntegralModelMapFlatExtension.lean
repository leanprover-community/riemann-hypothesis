import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSectionIntegralFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrOverHeightOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelDomainOverInclusion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFlagBaseHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointModelOverDvr

section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_over_height_one : ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A] [CharZero A] (𝔭 : PrimeSpectrum A), 𝔭.asIdeal.height = 1 → ∃ (T : CDVR) (iT : Localization.AtPrime 𝔭.asIdeal →+* T.V), Function.Injective iT ∧ IsLocalHom iT := by
  first | exact @GlobalTheory.HeightOneCompletion.exists_cdvr_of_height_eq_one | exact GlobalTheory.HeightOneCompletion.exists_cdvr_of_height_eq_one | (intros; apply GlobalTheory.HeightOneCompletion.exists_cdvr_of_height_eq_one <;> assumption)
end

section
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.CoeffUnit

theorem mem_of_isIntegral_int {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {x : Ω} (hx : IsIntegral ℤ x) : x ∈ A := by
  have h1 : IsIntegral A x := hx.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp h1
  rw [← hy]
  exact y.2

theorem isUnit_of_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l' : Level H) (c' : Coeff l') (W : ValuationSubring ℂ) (p : ℕ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (A : Type) [CommRing A] (β : c'.V W →+* A), IsUnit (p : A) → ∀ a : c'.V W, a ≠ 0 → IsUnit (β a) := by
  intro E _ _ _ H l' c' W p hp hpW A _ β hpA a ha
  haveI := c'.fin

  set x : c'.F := (a : c'.F) with hxdef
  have hx0 : x ≠ 0 := by
    intro h; apply ha; exact Subtype.ext h
  have halg : IsAlgebraic ℤ (x⁻¹ : c'.F) := by
    have h1 : IsAlgebraic ℚ (x⁻¹ : c'.F) := Algebra.IsAlgebraic.isAlgebraic _
    exact (IsFractionRing.isAlgebraic_iff ℤ ℚ c'.F).mpr h1
  obtain ⟨d, hd0, hdint⟩ := halg.exists_integral_multiple

  obtain ⟨n, hn0, hnint⟩ : ∃ n : ℕ, n ≠ 0 ∧ IsIntegral ℤ ((n : c'.F) * x⁻¹) := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg d
    · refine ⟨n, by exact_mod_cast hd0, ?_⟩
      rw [zsmul_eq_mul] at hdint; exact_mod_cast hdint
    · refine ⟨n, by simpa using hd0, ?_⟩
      have := hdint.neg
      rw [zsmul_eq_mul] at this
      convert this using 1; push_cast; ring
  obtain ⟨k, m, hpm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.ne_one

  have hpmax : ((p : W)) ∈ IsLocalRing.maximalIdeal W := by
    obtain ⟨h1, h2⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hpW
    convert h2 using 1
    ext; simp
  have hmunit : IsUnit ((m : W)) := by
    by_contra hm
    have hmmax : ((m : W)) ∈ IsLocalRing.maximalIdeal W := hm
    have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
    have hbez : ((1 : ℤ)) = (p : ℤ) * Nat.gcdA p m + (m : ℤ) * Nat.gcdB p m := by
      have := Nat.gcd_eq_gcd_ab p m
      rw [hcop] at this
      exact_mod_cast this
    have h1 : ((1 : W)) ∈ IsLocalRing.maximalIdeal W := by
      have : ((1 : W)) = (p : W) * (Nat.gcdA p m : W) + (m : W) * (Nat.gcdB p m : W) := by
        have := congrArg (fun t : ℤ => (t : W)) hbez
        push_cast at this
        exact this
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hpmax) (Ideal.mul_mem_right _ _ hmmax)
    exact (IsLocalRing.maximalIdeal.isMaximal W).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  obtain ⟨u, hu⟩ := hmunit

  have hnW : (((n : c'.F) * x⁻¹ : c'.F) : ℂ) ∈ W := by
    apply mem_of_isIntegral_int W
    exact hnint.map (c'.F.val.restrictScalars ℤ)
  have hum : (((u⁻¹ : Wˣ) : W) : ℂ) * (m : ℂ) = 1 := by
    have h1 : ((u⁻¹ : Wˣ) : W) * (m : W) = 1 := by rw [← hu]; exact u.inv_mul
    have h2 := congrArg (fun t : W => (t : ℂ)) h1
    simpa using h2
  have hinv : (((u⁻¹ : Wˣ) : W) : ℂ) = (m : ℂ)⁻¹ := eq_inv_of_mul_eq_one_left hum
  have hbW : ((((p : c'.F) ^ k * x⁻¹ : c'.F)) : ℂ) ∈ W := by
    have heq : ((((p : c'.F) ^ k * x⁻¹ : c'.F)) : ℂ)
        = (((u⁻¹ : Wˣ) : W) : ℂ) * ((((n : c'.F) * x⁻¹ : c'.F)) : ℂ) := by
      have hm0 : (m : ℂ) ≠ 0 := by
        have : m ≠ 0 := by rintro rfl; simp at hnm; exact hn0 hnm
        exact_mod_cast this
      rw [hinv, hnm]; push_cast; field_simp
    rw [heq]; exact W.mul_mem _ _ (SetLike.coe_mem _) hnW
  let b : c'.V W := ⟨(p : c'.F) ^ k * x⁻¹, ValuationSubring.mem_comap.mpr hbW⟩
  have hab : a * b = (p : c'.V W) ^ k := by
    apply Subtype.ext
    show (a : c'.F) * ((p : c'.F) ^ k * x⁻¹) = (((p : c'.V W) ^ k : c'.V W) : c'.F)
    rw [← hxdef]; push_cast; field_simp
  have hu' : IsUnit (β a * β b) := by
    rw [← map_mul, hab, map_pow, map_natCast]; exact hpA.pow k
  exact isUnit_of_mul_isUnit_left hu'

end GlobalTheory.CoeffUnit
end

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_ring_units_invert_p : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l' : Level H) (c' : Coeff l') (W : ValuationSubring ℂ) (p : ℕ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (A : Type) [CommRing A] (β : c'.V W →+* A), IsUnit (p : A) → ∀ a : c'.V W, a ≠ 0 → IsUnit (β a) := by
  atlas_forward_decl GlobalTheory.CoeffUnit.isUnit_of_ne_zero
end

section
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

noncomputable section

namespace GlobalTheory.FlatModel.GenPt

theorem exists_lift_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ), p.Prime → (p : ℂ) ∈ W.nonunits → (p : c'.F) ∈ (c'.V W).nonunits → ∀ (A : Type) [CommRing A] [IsDomain A] (ξ : Sp A ⟶ Y.X), ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Set.range Y.j → ∀ (K : Type) [Field K] (ψ : A →+* K), Function.Injective ψ → ∃ yy : Sp K ⟶ Xo'.XF c', yy ≫ Y.j = spMap ψ ≫ ξ := by
  intro E _ _ _ H Dw l' Xo' c' W Y p hp hW _ A _ _ ξ hξ K _ ψ hψ
  haveI : IsOpenImmersion Y.j := GlobalTheory.LocM.BaseMdl.isOpenImmersion_j hp hW Y
  have hr : Set.range (spMap ψ ≫ ξ) ⊆ Set.range Y.j := by
    rintro _ ⟨x, rfl⟩
    have hx : x = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) := Subsingleton.elim _ _
    subst hx
    rw [bot_map hψ]
    exact hξ
  exact ⟨IsOpenImmersion.lift Y.j (spMap ψ ≫ ξ) hr, IsOpenImmersion.lift_fac _ _ _⟩

end GlobalTheory.FlatModel.GenPt

end
end

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_fibre_point_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ), p.Prime → (p : ℂ) ∈ W.nonunits → (p : c'.F) ∈ (c'.V W).nonunits → ∀ (A : Type) [CommRing A] [IsDomain A] (ξ : Sp A ⟶ Y.X), ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Set.range Y.j → ∀ (K : Type) [Field K] (ψ : A →+* K), Function.Injective ψ → ∃ yy : Sp K ⟶ Xo'.XF c', yy ≫ Y.j = spMap ψ ≫ ξ := by
  atlas_forward_decl GlobalTheory.FlatModel.GenPt.exists_lift_genericFibre
end

section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_domain_over_inclusion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → ∀ (A : Type) [CommRing A] [IsDomain A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β → (∀ a : c'.V W, a ≠ 0 → IsUnit (β a)) → ∀ (T₀ : CDVR) (α : A →+* T₀.V), Function.Injective α → ∀ yy₀ : Sp T₀.Fr ⟶ Xo'.XF c', yy₀ ≫ Y.j = spMap ((algebraMap T₀.V T₀.Fr).comp α) ≫ ξ → ∃ (T : CDVR) (i : T₀.V →+* T.V) (iF : T₀.Fr →+* T.Fr), (∀ a, algebraMap T.V T.Fr (i a) = iF (algebraMap T₀.V T₀.Fr a)) ∧ Function.Injective i ∧ IsLocalHom i ∧ ∃ (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) ∧ (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = spMap iF ≫ yy₀ ≫ r) := by
  first | exact @GlobalTheory.ModelIntFr.exists_intFr_of_modelPt | exact GlobalTheory.ModelIntFr.exists_intFr_of_modelPt | (intros; apply GlobalTheory.ModelIntFr.exists_intFr_of_modelPt <;> assumption)
end

section
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel.LiftComb

theorem lift_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (K : Type) [CommRing K] (yy : Sp K ⟶ Xo'.XF c') (g : ℕ) (e : Fin g → (Sp (DualNumber K) ⟶ Y.t.G.left)), (∀ i, IsTanAtG Y.t (yy ≫ Y.j) (e i)) → ∀ (cf : Fin g → K), ∃ w : Sp (DualNumber K) ⟶ Y.oF.t.G.left, IsCombAtG Y.t (yy ≫ Y.j) e cf (w ≫ Y.m.φ) := by
  intro E _ _ _ H Dw l' Xo' c' W Y K _ yy g e he cf
  have hε : ∀ c : K, spMap (epsMul c) ≫ spMap (algebraMap K (DualNumber K)) = spMap (algebraMap K (DualNumber K)) := by
    intro c
    unfold spMap
    rw [← Spec.map_comp]
    congr 1
    ext a
    · simp [epsMul]
    · simp [epsMul]
  let u : Fin g → (tEpsG (yy ≫ Y.j) ⟶ Y.t.G) := fun i => Over.homMk (spMap (epsMul (cf i)) ≫ e i) (by
      simp only [tEpsG, Over.mk_hom, Category.assoc]
      rw [(he i).1]
      simp only [← Category.assoc]
      rw [hε])
  have hv : ((List.ofFn u).prod).left ≫ Y.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ yy ≫ Y.j :=
    Over.w ((List.ofFn u).prod)
  have hc := Y.m.cart.1
  refine ⟨hc.lift ((List.ofFn u).prod).left (spMap (algebraMap K (DualNumber K)) ≫ yy) (by rw [Category.assoc]; exact hv), u, fun i => rfl, ?_⟩
  rw [hc.lift_fst]

end GlobalTheory.FlatModel.LiftComb
end

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tangent_lift_coefficients : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (K : Type) [CommRing K] (yy : Sp K ⟶ Xo'.XF c') (g : ℕ) (e : Fin g → (Sp (DualNumber K) ⟶ Y.t.G.left)), (∀ i, IsTanAtG Y.t (yy ≫ Y.j) (e i)) → ∀ (cf : Fin g → K), ∃ w : Sp (DualNumber K) ⟶ Y.oF.t.G.left, IsCombAtG Y.t (yy ≫ Y.j) e cf (w ≫ Y.m.φ) := by
  atlas_forward_decl GlobalTheory.FlatModel.LiftComb.lift_comb
end

section
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel.EigLift

theorem one_left_comp {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
  have hw : ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk (T.hom ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    rfl
  let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk _ hw
  have h2 := h.2 T 1 1 x₀ x₀ rfl rfl
  have h3 : x₀ * x₀ = x₀ := by
    apply Over.OverMorphism.ext
    rw [h2, _root_.mul_one]
    rfl
  have h4 : x₀ = 1 := by simpa using h3
  exact congrArg CommaMorphism.left h4

theorem comp_prod {B : Scheme.{0}} {G : Over B} [GrpObj G] {X Y : Over B} (z : X ⟶ Y) (L : List (Y ⟶ G)) :
    z ≫ L.prod = (L.map (z ≫ ·)).prod := by
  induction L with
  | nil => exact MonObj.comp_one z
  | cons a L ih => rw [List.prod_cons, MonObj.comp_mul, ih, List.map_cons, List.prod_cons]

theorem sp_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, ← Spec.map_comp]

theorem sp_fst_alg (K : Type) [CommRing K] :
    spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 _ := by
  rw [← sp_comp]
  have : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (algebraMap K (DualNumber K)) = RingHom.id K := by
    ext x; simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [this]
  simp [spMap]

theorem sp_fst_eps {K : Type} [CommRing K] (q : K) :
    spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (epsMul q) = spMap (TrivSqZeroExt.fstHom K K K).toRingHom := by
  rw [← sp_comp]
  have : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (epsMul q) = (TrivSqZeroExt.fstHom K K K).toRingHom := by
    apply RingHom.ext; intro x
    show (epsMul q x).fst = x.fst
    simp [epsMul]
  rw [this]

theorem sp_eps_alg {K : Type} [CommRing K] (q : K) :
    spMap (epsMul q) ≫ spMap (algebraMap K (DualNumber K)) = spMap (algebraMap K (DualNumber K)) := by
  rw [← sp_comp]
  have : (epsMul q).comp (algebraMap K (DualNumber K)) = algebraMap K (DualNumber K) := by
    apply RingHom.ext; intro x
    show epsMul q (algebraMap K (DualNumber K) x) = _
    ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  rw [this]

end GlobalTheory.FlatModel.EigLift

namespace GlobalTheory.FlatModel.EigLift

theorem char_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l l' : Level H}
    {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} {W : ValuationSubring ℂ}
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (hle : c.F ≤ c'.F) (hI : OverIncl r hle)
    (σ : E →+* ℂ) {A : Type} [CommRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A) (hβ : ξ ≫ Y.s = spMap β)
    {K : Type} [CommRing K] (φ : A →+* K) (io : c.F →+* K) (yy : Sp K ⟶ Xo'.XF c')
    (hyy : yy ≫ Y.j = spMap φ ≫ ξ) (hio : yy ≫ r ≫ pullback.snd _ _ = spMap io) (a : 𝓞 E) :
    φ (β (embV c' W σ a)) = io (embK c σ a) := by
  set κ : c'.F →+* K := (Spec.preimage (yy ≫ pullback.snd _ _)).hom with hκdef
  have hκ : spMap κ = yy ≫ pullback.snd _ _ := by
    simp only [spMap, hκdef, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hjs : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (c'.V W).subtype := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
  have h1 : spMap (κ.comp (c'.V W).subtype) = spMap (φ.comp β) := by
    rw [sp_comp, sp_comp, hκ, Category.assoc, ← hjs, ← Category.assoc, hyy, Category.assoc, hβ]
  have h2 : spMap (κ.comp (IntermediateField.inclusion hle).toRingHom) = spMap io := by
    rw [sp_comp, hκ, Category.assoc, ← hI, hio]
  have k1 : κ.comp (c'.V W).subtype = φ.comp β := by
    have := congrArg CommRingCat.Hom.hom (Spec.map_inj.1 h1)
    simpa using this
  have k2 : κ.comp (IntermediateField.inclusion hle).toRingHom = io := by
    have := congrArg CommRingCat.Hom.hom (Spec.map_inj.1 h2)
    simpa using this
  calc φ (β (embV c' W σ a)) = κ ((embV c' W σ a : c'.V W) : c'.F) := (RingHom.congr_fun k1 _).symm
    _ = κ (IntermediateField.inclusion hle (embK c σ a)) := congrArg κ (Subtype.ext rfl)
    _ = io (embK c σ a) := RingHom.congr_fun k2 _

end GlobalTheory.FlatModel.EigLift

namespace GlobalTheory.FlatModel

open EigLift in

theorem lift_tan_eig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → ∀ (σ : E →+* ℂ) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β → ∀ (g m : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U : Fin m → Fin g → A), IsTanBasis Y.t ξ e → (∀ (S : Type) [CommRing S] (φ : A →+* S), EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W σ))) (bcV Y.t φ e) (fun k b => φ (U k b))) → ∀ (K : Type) [CommRing K] (φ : A →+* K) (io : c.F →+* K) (y : letI := io.toAlgebra; FrPt Xo c K) (yy : Sp K ⟶ Xo'.XF c'), yy ≫ Y.j = spMap φ ≫ ξ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y = yy ≫ r) → ∀ (k : Fin m) (w : Sp (DualNumber K) ⟶ Y.oF.t.G.left), IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t φ e) (fun b => φ (U k b)) (w ≫ Y.m.φ) → (letI := io.toAlgebra; IsTanAt y.x (w ≫ ν.φ) ∧ IsEigAt c σ (w ≫ ν.φ)) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle hI σ A _ ξ β hβ g m e U hB hEig K _ φ io y yy hyy hpt k w hw
  letI := io.toAlgebra
  haveI : IsOpenImmersion Y.j := GlobalTheory.TriplesAlong.isOpenImmersion_j W Y
  have hc := Y.m.cart.1
  have hcw : Y.m.φ ≫ Y.t.G.hom = Y.oF.t.G.hom ≫ Y.j := hc.w
  have hνw : ν.φ ≫ Xo.univ.t.G.hom = Y.oF.t.G.hom ≫ r ≫ pullback.fst _ _ := ν.cart.1.w
  have hx : y.x = yy ≫ r ≫ pullback.fst _ _ := by
    rw [← Category.assoc, ← hpt, GlobalTheory.AllWt.ptF, pullback.lift_fst]
  have hio : yy ≫ r ≫ pullback.snd _ _ = spMap io := by
    rw [← Category.assoc, ← hpt, GlobalTheory.AllWt.ptF, pullback.lift_snd]
  have hχ : ∀ a, φ (β (embV c' W σ a)) = io (embK c σ a) := fun a =>
    char_eq Y r hle hI σ ξ β hβ φ io yy hyy hio a
  obtain ⟨u, hu, hwu⟩ := hw
  have hwb : w ≫ Y.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ yy := by
    rw [← cancel_mono Y.j, Category.assoc, ← hcw, ← Category.assoc, ← hwu, Over.w, Category.assoc]
    rfl
  have hT : ∀ i, IsTanAtG Y.t (yy ≫ Y.j) (bcV Y.t φ e i) := by
    rw [hyy]
    exact (isTanBasis_bc hB φ).1
  have hz : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ (tEpsG (yy ≫ Y.j)).hom = (Over.mk (yy ≫ Y.j)).hom := by
    show spMap _ ≫ spMap (algebraMap K (DualNumber K)) ≫ yy ≫ Y.j = yy ≫ Y.j
    rw [← Category.assoc, sp_fst_alg, Category.id_comp]
  let z : Over.mk (yy ≫ Y.j) ⟶ tEpsG (yy ≫ Y.j) := Over.homMk _ hz
  have hzu : ∀ i, z ≫ u i = 1 := fun i => by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hu i, ← Category.assoc]
    show (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (epsMul _)) ≫ _ = _
    rw [sp_fst_eps]
    exact (hT i).2
  have hprod : z ≫ (List.ofFn u).prod = 1 := by
    rw [comp_prod, List.map_ofFn]
    have : ((z ≫ ·) ∘ u) = fun _ => 1 := funext hzu
    rw [this]
    simp
  have h0 : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w ≫ Y.m.φ = (1 : Over.mk (yy ≫ Y.j) ⟶ Y.t.G).left := by
    rw [← hwu, ← hprod]
    rfl
  have hw0 : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w = (1 : Over.mk yy ⟶ Y.oF.t.G).left := by
    apply hc.hom_ext
    · rw [Category.assoc, h0, one_left_comp Y.m.cart (Over.mk yy)]
      rfl
    · rw [Category.assoc, hwb, ← Category.assoc, sp_fst_alg, Category.id_comp, Over.w]
      rfl
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, hνw, ← Category.assoc, hwb, hx]
    simp only [Category.assoc]
  · rw [← Category.assoc, hw0, one_left_comp ν.cart (Over.mk yy), hx]
  · intro a
    have hE : IsEigG Y.t (φ.comp (β.comp (embV c' W σ))) (w ≫ Y.m.φ) :=
      hEig K φ k (w ≫ Y.m.φ) (by rw [← hyy]; exact ⟨u, hu, hwu⟩)
    have key : w ≫ (Y.oF.t.act.act a).left = spMap (epsMul (io (embK c σ a))) ≫ w := by
      apply hc.hom_ext
      · rw [Category.assoc, Category.assoc, Y.m.act a, ← Category.assoc, hE a]
        simp only [RingHom.comp_apply, hχ a, Category.assoc]
      · rw [Category.assoc, Category.assoc, Over.w, hwb, ← Category.assoc, sp_eps_alg]
    show w ≫ ν.φ ≫ _ = spMap (epsMul (io (embK c σ a))) ≫ w ≫ ν.φ
    rw [← ν.act a, ← Category.assoc, key, Category.assoc]

end GlobalTheory.FlatModel
end

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_embedding_first : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → ∀ (σ : E →+* ℂ) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β → ∀ (g m : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U : Fin m → Fin g → A), IsTanBasis Y.t ξ e → (∀ (S : Type) [CommRing S] (φ : A →+* S), EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W σ))) (bcV Y.t φ e) (fun k b => φ (U k b))) → ∀ (K : Type) [CommRing K] (φ : A →+* K) (io : c.F →+* K) (y : letI := io.toAlgebra; FrPt Xo c K) (yy : Sp K ⟶ Xo'.XF c'), yy ≫ Y.j = spMap φ ≫ ξ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y = yy ≫ r) → ∀ (k : Fin m) (w : Sp (DualNumber K) ⟶ Y.oF.t.G.left), IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t φ e) (fun b => φ (U k b)) (w ≫ Y.m.φ) → (letI := io.toAlgebra; IsTanAt y.x (w ≫ ν.φ) ∧ IsEigAt c σ (w ≫ ν.φ)) := by
  atlas_forward_decl GlobalTheory.FlatModel.lift_tan_eig
end

section
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem eigChar_model_eq_frPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (hle : c.F ≤ c'.F), OverIncl r hle → ∀ (σ : E →+* ℂ) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β → ∀ (K : Type) [CommRing K] (φ : A →+* K) (io : c.F →+* K) (y : letI := io.toAlgebra; FrPt Xo c K) (yy : Sp K ⟶ Xo'.XF c'), yy ≫ Y.j = spMap φ ≫ ξ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y = yy ≫ r) → ∀ a : 𝓞 E, φ (β (embV c' W σ a)) = io (embK c σ a) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r hle hOI σ A _ ξ β hξ K _ φ io y yy hyy hy a
  have e : ∀ {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T),
      spMap (g.comp f) = spMap g ≫ spMap f := by
    intro R S T _ _ _ f g
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]; rfl
  have inj : ∀ {R S : Type} [CommRing R] [CommRing S] (f g : R →+* S), spMap f = spMap g → f = g := by
    intro R S _ _ f g h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  have h1 : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (c'.V W).subtype := by
    show (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]
  obtain ⟨ι', hι⟩ : ∃ ι' : c'.F →+* K, spMap ι' = yy ≫ pullback.snd _ _ :=
    ⟨(Spec.preimage (yy ≫ pullback.snd _ _)).hom, Spec.map_preimage _⟩
  have h2 : φ.comp β = ι'.comp (c'.V W).subtype := by
    apply inj
    rw [e, e, ← hξ, ← Category.assoc, ← hyy, Category.assoc, h1, ← Category.assoc, hι]
  have h3 : io = ι'.comp (IntermediateField.inclusion hle).toRingHom := by
    apply inj
    have h0 : (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y) ≫ pullback.snd _ _ = spMap io := pullback.lift_snd _ _ _
    rw [e, hι, ← h0, hy, Category.assoc, hOI, Category.assoc]
  have h4 : (IntermediateField.inclusion hle) (embK c σ a) = embK c' σ a := Subtype.ext rfl
  calc φ (β (embV c' W σ a)) = ι' ((c'.V W).subtype (embV c' W σ a)) := RingHom.congr_fun h2 _
    _ = ι' (embK c' σ a) := rfl
    _ = io (embK c σ a) := by rw [h3, RingHom.comp_apply]; exact congrArg ι' h4.symm

end GlobalTheory.FlatModel
end

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.overInclusion_base_change_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (hle : c.F ≤ c'.F), OverIncl r hle → ∀ (σ : E →+* ℂ) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β → ∀ (K : Type) [CommRing K] (φ : A →+* K) (io : c.F →+* K) (y : letI := io.toAlgebra; FrPt Xo c K) (yy : Sp K ⟶ Xo'.XF c'), yy ≫ Y.j = spMap φ ≫ ξ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y = yy ≫ r) → ∀ a : 𝓞 E, φ (β (embV c' W σ a)) = io (embK c σ a) := by
  atlas_forward_decl GlobalTheory.FlatModel.eigChar_model_eq_frPt
end

section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_point_model_over_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (σ : E →+* ℂ) (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (xV : Sp T.V ⟶ Y.X) (yy : Sp T.Fr ⟶ Xo'.XF c'), yy ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ xV → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = yy ≫ r) → ∃ v : Fin (Dw.mult σ) → (Sp (DualNumber T.V) ⟶ Y.t.G.left), (∀ j, IsTanAtG Y.t xV (v j)) ∧ (∀ u : Sp (DualNumber T.V) ⟶ Y.t.G.left, IsTanAtG Y.t xV u → (∀ (a : 𝓞 E) (z : T.V), algebraMap T.V T.Fr z = io (embK c σ a) → u ≫ (Y.t.act.act a).left = spMap (epsMul z) ≫ u) → ∃ cf : Fin (Dw.mult σ) → T.V, IsCombAtG Y.t xV v cf u) ∧ ∀ (cf : Fin (Dw.mult σ) → T.V) (u : Sp (DualNumber T.V) ⟶ Y.t.G.left) (w : Sp (DualNumber T.Fr) ⟶ Y.oF.t.G.left), IsCombAtG Y.t xV v cf u → w ≫ Y.m.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ u → (letI := io.toAlgebra; IsCombAt y₀.1.x (y₀.1.u σ) (fun j => algebraMap T.V T.Fr (cf j)) (w ≫ ν.φ)) := by
  first | exact @GlobalTheory.ModelFrameCompare.images_eigenBasis | exact GlobalTheory.ModelFrameCompare.images_eigenBasis | (intros; apply GlobalTheory.ModelFrameCompare.images_eigenBasis <;> assumption)
end

section
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel.DetUnit

theorem isUnit_det_of_factor {R : Type} [CommRing R] {m g : ℕ} (h U : Fin m → Fin g → R)
    (M : Matrix (Fin m) (Fin m) R) (C : Fin m → Fin g → R) (hU : ∀ k b, U k b = ∑ j, M k j * C j b)
    (hP : IsUnit (pairDet h U)) : IsUnit M.det := by
  have e : (Matrix.of fun k k' : Fin m => ∑ b, h k' b * U k b) =
      M * Matrix.of (fun j k' => ∑ b, C j b * h k' b) := by
    ext k k'
    simp only [Matrix.of_apply, Matrix.mul_apply, hU, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => by ring
  rw [pairDet, e, Matrix.det_mul] at hP
  exact isUnit_of_mul_isUnit_left hP

theorem det_isUnit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → ∀ (σ : E →+* ℂ) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U h : Fin (Dw.mult σ) → Fin g → A), IsTanBasis Y.t ξ e → (∀ (S : Type) [CommRing S] (φ : A →+* S), EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W σ))) (bcV Y.t φ e) (fun k b => φ (U k b))) → IsUnit (pairDet h U) → ∀ (T : CDVR) (α : A →+* T.V) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (yy : Sp T.Fr ⟶ Xo'.XF c'), yy ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp α) ≫ ξ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = yy ≫ r) → ∀ (w : Fin (Dw.mult σ) → (Sp (DualNumber T.Fr) ⟶ Y.oF.t.G.left)) (gm : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr), (∀ i, IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t ((algebraMap T.V T.Fr).comp α) e) (fun b => (algebraMap T.V T.Fr).comp α (U i b)) (w i ≫ Y.m.φ)) → (letI := io.toAlgebra; ∀ i, IsCombAt y₀.1.x (y₀.1.u σ) (gm i) (w i ≫ ν.φ)) → ∃ u : T.Vˣ, algebraMap T.V T.Fr u = gm.det := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle hOI σ A _ ξ β hξ g e U h he hU hP T α io y₀ yy hyy hpt w gm hw hgmC
  letI := io.toAlgebra
  have hyV : yy ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ (spMap α ≫ ξ) := by rw [hyy, sp_sp]
  obtain ⟨v, hvt, hvb, hvg⟩ := GlobalTheory.T.integral_point_model_over_dvr E H Dw l l' Xo Xo' c c' W Y r ν σ T io y₀ (spMap α ≫ ξ) yy hyV hpt
  have he' := isTanBasis_bc he α
  have hchar := GlobalTheory.T.overInclusion_base_change_model E H Dw l l' Xo Xo' c c' W Y r hle hOI σ A ξ β hξ T.Fr ((algebraMap T.V T.Fr).comp α) io y₀.1 yy
    hyy hpt
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  choose u hut hu using fun k : Fin (Dw.mult σ) =>
    GlobalTheory.ShFam.Pad.Guard.exists_comb he'.1 (fun b => α (U k b))
  have hue : ∀ k (a : 𝓞 E) (z : T.V), algebraMap T.V T.Fr z = io (embK c σ a) →
      u k ≫ (Y.t.act.act a).left = spMap (epsMul z) ≫ u k := by
    intro k a z hz
    have hz' : z = α (β (embV c' W σ a)) := hinj (by rw [hz, ← hchar a]; rfl)
    subst hz'
    exact (hU T.V α) k (u k) (hu k) a
  choose M hM using fun k => hvb (u k) (hut k) (hue k)
  choose C hC using fun j => (he.2 T.V α (v j) (hvt j)).exists
  have hrel : ∀ k b, α (U k b) = ∑ j, M k j * C j b := by
    intro k b
    have h1 : IsCombAtG Y.t (spMap α ≫ ξ) (bcV Y.t α e) ((Matrix.of fun b j => C j b).mulVec (M k)) (u k) :=
      tanLinG (bcV Y.t α e) he'.1 v (Matrix.of fun b j => C j b) (M k) (u k) (fun j => hC j) (hM k)
    have h2 := congrFun ((he.2 T.V α (u k) (hut k)).unique (hu k) h1) b
    rw [h2]
    simp [Matrix.mulVec, dotProduct, mul_comm]
  have hwu : ∀ k, w k ≫ Y.m.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ u k := by
    intro k
    have h2 := GlobalTheory.LocM.Cht.FlagBase.isCombAtG_bc Y.t (algebraMap T.V T.Fr) (hu k)
    have h3 := hw k
    rw [hyV] at h3
    have e1 : (fun j => spMap (dualMap (algebraMap T.V T.Fr)) ≫ bcV Y.t α e j) =
        bcV Y.t ((algebraMap T.V T.Fr).comp α) e := bcV_bcV (t := Y.t) α (algebraMap T.V T.Fr) e
    rw [e1] at h2
    exact GlobalTheory.FlatModel.LiftBC.isCombAtG_unique Y.t h3 h2
  have hgm : ∀ k, gm k = fun j => algebraMap T.V T.Fr (M k j) := by
    intro k
    have hte := GlobalTheory.T.integral_model_embedding_first E H Dw l l' Xo Xo' c c' W Y r ν hle hOI σ A ξ β hξ g (Dw.mult σ) e U he hU T.Fr
      ((algebraMap T.V T.Fr).comp α) io y₀.1 yy hyy hpt k (w k) (hw k)
    exact (y₀.1.basis σ (w k ≫ ν.φ) hte.1 hte.2).unique (hgmC k) (hvg (M k) (u k) (w k) (hM k) (hwu k))
  have hP' : IsUnit (pairDet (fun k b => α (h k b)) (fun k b => α (U k b))) := by
    have e2 : α (pairDet h U) = pairDet (fun k b => α (h k b)) (fun k b => α (U k b)) := by
      rw [pairDet, pairDet, RingHom.map_det]
      congr 1
      ext k k'
      simp [map_sum]
    exact e2 ▸ hP.map α
  have hMu : IsUnit (Matrix.of M).det :=
    isUnit_det_of_factor _ _ (Matrix.of M) C (fun k b => hrel k b) hP'
  refine ⟨hMu.unit, ?_⟩
  rw [IsUnit.unit_spec, RingHom.map_det]
  congr 1
  ext k j
  simp [hgm k]

end GlobalTheory.FlatModel.DetUnit
end

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_embedding_second : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → ∀ (σ : E →+* ℂ) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U h : Fin (Dw.mult σ) → Fin g → A), IsTanBasis Y.t ξ e → (∀ (S : Type) [CommRing S] (φ : A →+* S), EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W σ))) (bcV Y.t φ e) (fun k b => φ (U k b))) → IsUnit (pairDet h U) → ∀ (T : CDVR) (α : A →+* T.V) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (yy : Sp T.Fr ⟶ Xo'.XF c'), yy ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp α) ≫ ξ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = yy ≫ r) → ∀ (w : Fin (Dw.mult σ) → (Sp (DualNumber T.Fr) ⟶ Y.oF.t.G.left)) (gm : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr), (∀ i, IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t ((algebraMap T.V T.Fr).comp α) e) (fun b => (algebraMap T.V T.Fr).comp α (U i b)) (w i ≫ Y.m.φ)) → (letI := io.toAlgebra; ∀ i, IsCombAt y₀.1.x (y₀.1.u σ) (gm i) (w i ≫ ν.φ)) → ∃ u : T.Vˣ, algebraMap T.V T.Fr u = gm.det := by
  atlas_forward_decl GlobalTheory.FlatModel.DetUnit.det_isUnit
end

section
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem frames_changeOfBasis_det_isUnit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → ∀ (τ : E →+* ℂ) (A : Type) [CommRing A] [IsDomain A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ) → Fin g → A) (U₂ h₂ : Fin (Dw.mult (conjEmb τ)) → Fin g → A), IsTanBasis Y.t ξ e → (∀ (S : Type) [CommRing S] (φ : A →+* S), EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧ EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) → IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) → ∀ (T : CDVR) (α : A →+* T.V) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (yy : Sp T.Fr ⟶ Xo'.XF c'), yy ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp α) ≫ ξ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = yy ≫ r) → ∃ (w₁ : Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Y.oF.t.G.left)) (w₂ : Fin (Dw.mult (conjEmb τ)) → (Sp (DualNumber T.Fr) ⟶ Y.oF.t.G.left)) (g₁ : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.Fr) (g₂ : Matrix (Fin (Dw.mult (conjEmb τ))) (Fin (Dw.mult (conjEmb τ))) T.Fr), (∀ i, IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t ((algebraMap T.V T.Fr).comp α) e) (fun b => (algebraMap T.V T.Fr).comp α (U₁ i b)) (w₁ i ≫ Y.m.φ)) ∧ (∀ i, IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t ((algebraMap T.V T.Fr).comp α) e) (fun b => (algebraMap T.V T.Fr).comp α (U₂ i b)) (w₂ i ≫ Y.m.φ)) ∧ (letI := io.toAlgebra; (∀ i, IsCombAt y₀.1.x (y₀.1.u τ) (g₁ i) (w₁ i ≫ ν.φ)) ∧ (∀ i, IsCombAt y₀.1.x (y₀.1.u (conjEmb τ)) (g₂ i) (w₂ i ≫ ν.φ))) ∧ (∃ u : T.Vˣ, algebraMap T.V T.Fr u = g₁.det) ∧ ∃ u : T.Vˣ, algebraMap T.V T.Fr u = g₂.det := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle hOI τ A _ _ ξ β hξ g e U₁ h₁ U₂ h₂ he hU hP₁ hP₂ T α io y₀ yy hyy hpt
  letI := io.toAlgebra
  set φ₀ : A →+* T.Fr := (algebraMap T.V T.Fr).comp α with hφ₀
  have hbc := isTanBasis_bc he φ₀
  have htan : ∀ i, IsTanAtG Y.t (yy ≫ Y.j) (bcV Y.t φ₀ e i) := fun i => hyy ▸ hbc.1 i
  choose w₁ hw₁ using fun i : Fin (Dw.mult τ) =>
    GlobalTheory.T.exists_tangent_lift_coefficients E H Dw l' Xo' c' W Y T.Fr yy g (bcV Y.t φ₀ e) htan (fun b => φ₀ (U₁ i b))
  choose w₂ hw₂ using fun i : Fin (Dw.mult (conjEmb τ)) =>
    GlobalTheory.T.exists_tangent_lift_coefficients E H Dw l' Xo' c' W Y T.Fr yy g (bcV Y.t φ₀ e) htan (fun b => φ₀ (U₂ i b))
  have hE₁ := fun i => GlobalTheory.T.integral_model_embedding_first E H Dw l l' Xo Xo' c c' W Y r ν hle hOI τ A ξ β hξ g (Dw.mult τ) e U₁ he
    (fun S _ φ => (hU S φ).1) T.Fr φ₀ io y₀.1 yy hyy hpt i (w₁ i) (hw₁ i)
  have hE₂ := fun i => GlobalTheory.T.integral_model_embedding_first E H Dw l l' Xo Xo' c c' W Y r ν hle hOI (conjEmb τ) A ξ β hξ g (Dw.mult (conjEmb τ)) e U₂ he
    (fun S _ φ => (hU S φ).2) T.Fr φ₀ io y₀.1 yy hyy hpt i (w₂ i) (hw₂ i)
  choose g₁ hg₁ using fun i => (y₀.1.basis τ (w₁ i ≫ ν.φ) (hE₁ i).1 (hE₁ i).2).exists
  choose g₂ hg₂ using fun i => (y₀.1.basis (conjEmb τ) (w₂ i ≫ ν.φ) (hE₂ i).1 (hE₂ i).2).exists
  refine ⟨w₁, w₂, Matrix.of g₁, Matrix.of g₂, hw₁, hw₂, ⟨hg₁, hg₂⟩, ?_, ?_⟩
  · exact GlobalTheory.T.integral_model_embedding_second E H Dw l l' Xo Xo' c c' W Y r ν hle hOI τ A ξ β hξ g e U₁ h₁ he (fun S _ φ => (hU S φ).1) hP₁ T α io y₀ yy hyy hpt
      w₁ (Matrix.of g₁) hw₁ hg₁
  · exact GlobalTheory.T.integral_model_embedding_second E H Dw l l' Xo Xo' c c' W Y r ν hle hOI (conjEmb τ) A ξ β hξ g e U₂ h₂ he (fun S _ φ => (hU S φ).2) hP₂ T α io y₀ yy
      hyy hpt w₂ (Matrix.of g₂) hw₂ hg₂

end GlobalTheory.FlatModel
end

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_conjugate_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → ∀ (τ : E →+* ℂ) (A : Type) [CommRing A] [IsDomain A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ) → Fin g → A) (U₂ h₂ : Fin (Dw.mult (conjEmb τ)) → Fin g → A), IsTanBasis Y.t ξ e → (∀ (S : Type) [CommRing S] (φ : A →+* S), EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧ EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) → IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) → ∀ (T : CDVR) (α : A →+* T.V) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (yy : Sp T.Fr ⟶ Xo'.XF c'), yy ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp α) ≫ ξ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = yy ≫ r) → ∃ (w₁ : Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Y.oF.t.G.left)) (w₂ : Fin (Dw.mult (conjEmb τ)) → (Sp (DualNumber T.Fr) ⟶ Y.oF.t.G.left)) (g₁ : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.Fr) (g₂ : Matrix (Fin (Dw.mult (conjEmb τ))) (Fin (Dw.mult (conjEmb τ))) T.Fr), (∀ i, IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t ((algebraMap T.V T.Fr).comp α) e) (fun b => (algebraMap T.V T.Fr).comp α (U₁ i b)) (w₁ i ≫ Y.m.φ)) ∧ (∀ i, IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t ((algebraMap T.V T.Fr).comp α) e) (fun b => (algebraMap T.V T.Fr).comp α (U₂ i b)) (w₂ i ≫ Y.m.φ)) ∧ (letI := io.toAlgebra; (∀ i, IsCombAt y₀.1.x (y₀.1.u τ) (g₁ i) (w₁ i ≫ ν.φ)) ∧ (∀ i, IsCombAt y₀.1.x (y₀.1.u (conjEmb τ)) (g₂ i) (w₂ i ≫ ν.φ))) ∧ (∃ u : T.Vˣ, algebraMap T.V T.Fr u = g₁.det) ∧ ∃ u : T.Vˣ, algebraMap T.V T.Fr u = g₂.det := by
  atlas_forward_decl GlobalTheory.FlatModel.frames_changeOfBasis_det_isUnit
end

section
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel.BdryGeo

theorem unit_of_vV (T : CDVR) {x : T.Fr} (hx : x ≠ 0) (h0 : vV T.V x = 0) :
    ∃ u : T.Vˣ, algebraMap T.V T.Fr (u : T.V) = x := by
  have hne : valV T.V x ≠ 0 := valV_ne_zero hx
  have h1 : valV T.V x = 1 := by
    have h2 : WithZero.log (valV T.V x) = 0 := by simpa [vV] using h0
    rw [← WithZero.exp_log hne, h2, WithZero.exp_zero]
  have hunit : ∀ z : T.V, (IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr (algebraMap T.V T.Fr z) = 1 →
      IsUnit z := fun z hz => by
    have hzn := (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem _).1 hz
    by_contra hn
    exact hzn ((IsLocalRing.mem_maximalIdeal z).2 hn)
  rcases ValuationRing.isInteger_or_isInteger T.V x with ⟨z, hz⟩ | ⟨z, hz⟩
  · obtain ⟨u, rfl⟩ := hunit z (by rw [hz]; exact h1)
    exact ⟨u, hz⟩
  · obtain ⟨u, rfl⟩ := hunit z (by
      rw [hz, map_inv₀]
      change (valV T.V x)⁻¹ = 1
      rw [h1, inv_one])
    refine ⟨u⁻¹, ?_⟩
    rw [map_units_inv, hz, inv_inv]

theorem descend (T₀ T : CDVR) (i : T₀.V →+* T.V) (iF : T₀.Fr →+* T.Fr)
    (hiF : ∀ a, algebraMap T.V T.Fr (i a) = iF (algebraMap T₀.V T₀.Fr a)) (hi : Function.Injective i)
    (hil : IsLocalHom i) (v : T₀.Fr) (u : T.Vˣ) (hv : iF v = algebraMap T.V T.Fr (u : T.V)) :
    ∃ w : T₀.Vˣ, algebraMap T₀.V T₀.Fr w = v := by
  have hinjT : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  rcases ValuationRing.isInteger_or_isInteger T₀.V v with ⟨z, hz⟩ | ⟨z, hz⟩
  · have h1 : i z = u := hinjT (by rw [hiF, hz, hv])
    have : IsUnit z := (isUnit_map_iff i z).1 (h1 ▸ u.isUnit)
    obtain ⟨w, rfl⟩ := this
    exact ⟨w, hz⟩
  · have h1 : i z = ((u⁻¹ : T.Vˣ) : T.V) := hinjT (by rw [hiF, hz, map_inv₀, hv, map_units_inv])
    have : IsUnit z := (isUnit_map_iff i z).1 (h1 ▸ (u⁻¹).isUnit)
    obtain ⟨w, rfl⟩ := this
    refine ⟨w⁻¹, ?_⟩
    rw [map_units_inv, hz, inv_inv]

theorem secVal_isUnit : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F)
    (r₀ : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀) (x : ℝ), Laws U x →
    ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ)
      (Xw : Y.X.Opens), p.Prime → IsCover Y r hle Z la p Xw →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A),
      IsOpenImmersion ξ → ξ ≫ Y.s = spMap β → IsUnit (p : A) → ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Xw →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ.1) → Fin g → A)
      (U₂ h₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → A), IsTanBasis Y.t ξ e →
      (∀ (S : Type) [CommRing S] (φ : A →+* S),
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ.1))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ.1)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) →
      IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) →
    ∀ 𝔭 : PrimeSpectrum A, 𝔭.asIdeal.height = 1 → ξ 𝔭 ∉ Set.range Y.j →
    ∃ (T : CDVR) (iT : Localization.AtPrime 𝔭.asIdeal →+* T.V), Function.Injective iT ∧ IsLocalHom iT ∧
      ∀ v : T.Fr, (∀ (k : Type) [Field k] (φ : T.Fr →+* k),
        SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂ k (φ.comp ((algebraMap T.V T.Fr).comp (iT.comp (algebraMap A _)))) (φ v)) →
        ∃ w : T.Vˣ, algebraMap T.V T.Fr w = v := by
  intro hP1 hP2 hP3 E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw hp hcov A _ _ _ _ ξ β hξo hξβ
    hpA hgen g e U₁ h₁ U₂ h₂ htan heig hd1 hd2 𝔭 h𝔭 _
  obtain ⟨hover, -, hpW, hpc, hXw, -, hZ, -, -⟩ := hcov
  have hβu := GlobalTheory.T.base_ring_units_invert_p E H l' c' W p hp hpW A β hpA
  haveI : CharZero A := by
    refine ⟨fun m n hmn => ?_⟩
    have hinjβ : Function.Injective β := by
      rw [injective_iff_map_eq_zero]
      intro a ha
      by_contra h0
      exact (hβu a h0).ne_zero ha
    have h := hinjβ (show β m = β n by rw [map_natCast, map_natCast]; exact hmn)
    exact_mod_cast congrArg (fun t : c'.V W => ((t : c'.F) : ℂ)) h
  obtain ⟨T₀, iT, hinj, hloc⟩ := GlobalTheory.T.exists_dvr_over_height_one A 𝔭 h𝔭
  let α₀ : A →+* T₀.V := iT.comp (algebraMap A (Localization.AtPrime 𝔭.asIdeal))
  have hα₀ : Function.Injective α₀ :=
    hinj.comp (IsLocalization.injective _ 𝔭.asIdeal.primeCompl_le_nonZeroDivisors)
  have hψ : Function.Injective ((algebraMap T₀.V T₀.Fr).comp α₀) :=
    (IsFractionRing.injective T₀.V T₀.Fr).comp hα₀
  obtain ⟨yy₀, hyy₀⟩ := GlobalTheory.T.generic_fibre_point_field E H Dw l' Xo' c' W Y p hp hpW hpc A ξ (hXw hgen) T₀.Fr _ hψ
  obtain ⟨T, i, iF, hiF, hi, hil, io, y₀, hio, hpt⟩ :=
    GlobalTheory.T.integral_model_domain_over_inclusion E H Dw l l' Xo Xo' c c' W Y r ν hle hover A ξ β hξβ hβu T₀ α₀ hα₀ yy₀ hyy₀
  refine ⟨T₀, iT, hinj, hloc, fun v hv => ?_⟩
  let α : A →+* T.V := i.comp α₀
  have hφeq : iF.comp ((algebraMap T₀.V T₀.Fr).comp (iT.comp (algebraMap A _))) = (algebraMap T.V T.Fr).comp α :=
    RingHom.ext fun a => (hiF _).symm
  let yy : Sp T.Fr ⟶ Xo'.XF c' := spMap iF ≫ yy₀
  have hyy : yy ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp α) ≫ ξ := by
    rw [← hφeq, Category.assoc, hyy₀, sp_sp]
  have hpt' : (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = yy ≫ r) := by
    rw [hpt, Category.assoc]
  obtain ⟨w₁, w₂, g₁, g₂, hc1, hc2, ⟨hc3, hc4⟩, ⟨u₁, hu₁⟩, ⟨u₂, hu₂⟩⟩ :=
    GlobalTheory.T.integral_model_conjugate_embedding E H Dw l l' Xo Xo' c c' W Y r ν hle hover τ.1 A ξ β hξβ g e U₁ h₁ U₂ h₂ htan heig hd1 hd2 T α io y₀ yy
      hyy hpt'
  letI := io.toAlgebra
  have hv' := hv T.Fr iF
  rw [hφeq] at hv'
  have key := hv' io.toAlgebra yy hyy y₀.1 y₀.2.1 hpt' w₁ w₂ g₁ g₂ hc1 hc2 hc3 hc4
  have hLies : GlobalTheory.AllWt.LiesOn Z y₀.1 := by
    intro s'
    rw [hpt']
    apply hZ
    have hs' : s' = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.Fr) := Subsingleton.elim _ _
    have e1 : (yy ≫ Y.j) s' ∈ Xw := by
      rw [hyy, hs', bot_map (φ := (algebraMap T.V T.Fr).comp α) ((IsFractionRing.injective T.V T.Fr).comp (hi.comp hα₀))]
      exact hgen
    exact e1
  have hn := GlobalTheory.T.archimedean_section_integral_frame hP1 hP2 hP3 E H Dw l Xo c r₀ U x hL Z τ s T io y₀ hio hLies
  have hev0 : evI y₀ s.sig ≠ 0 := by
    intro h0
    rw [h0, nval_zero] at hn
    exact EReal.top_ne_zero hn
  have hvv : vV T.V (evI y₀ s.sig) = 0 := by
    rw [nval_of_ne hev0] at hn
    have : ((vV T.V (evI y₀ s.sig) : ℝ) / ((1 : ℕ) : ℝ) : ℝ) = 0 := by exact_mod_cast hn
    simpa using this
  obtain ⟨u₃, hu₃⟩ := unit_of_vV T hev0 hvv
  have hkey : iF v = algebraMap T.V T.Fr ((u₂ * u₃ * u₁⁻¹ : T.Vˣ) : T.V) := by
    have hne : algebraMap T.V T.Fr (u₁ : T.V) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 u₁.ne_zero
    rw [Units.val_mul, Units.val_mul, map_mul, map_mul, hu₂, hu₃, map_units_inv, hu₁]
    have : iF v * g₁.det = g₂.det * evI y₀ s.sig := key
    rw [← hu₁] at this ⊢
    field_simp
    linear_combination this
  exact descend T₀ T i iF hiF hi hil v _ hkey

end GlobalTheory.FlatModel.BdryGeo
end

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_value_unit_at_boundary_height_one_prime : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F)
    (r₀ : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀) (x : ℝ), Laws U x →
    ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ)
      (Xw : Y.X.Opens), p.Prime → IsCover Y r hle Z la p Xw →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A),
      IsOpenImmersion ξ → ξ ≫ Y.s = spMap β → IsUnit (p : A) → ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Xw →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ.1) → Fin g → A)
      (U₂ h₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → A), IsTanBasis Y.t ξ e →
      (∀ (S : Type) [CommRing S] (φ : A →+* S),
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ.1))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ.1)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) →
      IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) →
    ∀ 𝔭 : PrimeSpectrum A, 𝔭.asIdeal.height = 1 → ξ 𝔭 ∉ Set.range Y.j →
    ∃ (T : CDVR) (iT : Localization.AtPrime 𝔭.asIdeal →+* T.V), Function.Injective iT ∧ IsLocalHom iT ∧
      ∀ v : T.Fr, (∀ (k : Type) [Field k] (φ : T.Fr →+* k),
        SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂ k (φ.comp ((algebraMap T.V T.Fr).comp (iT.comp (algebraMap A _)))) (φ v)) →
        ∃ w : T.Vˣ, algebraMap T.V T.Fr w = v := by
  atlas_forward_decl GlobalTheory.FlatModel.BdryGeo.secVal_isUnit
end
