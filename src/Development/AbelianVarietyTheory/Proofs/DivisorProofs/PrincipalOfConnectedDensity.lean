import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverLocallyOfFiniteTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensityStatementHolds
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsIntegralCoeffZeroMulOfAevalInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartsNormalProjectiveCovering

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.UnifNorm

theorem norm_le_one_of_mem (p : ℕ) [Fact p.Prime] (x : 𝓞_ℂ_[p]) : ‖(x : ℂ_[p])‖ ≤ 1 := by
  have hv : ((Valued.v (x : ℂ_[p]) : NNReal) : ℝ) = ‖(x : ℂ_[p])‖ := by
    rw [PadicComplex.norm_eq_norm, Valued.v.norm_def, PadicComplex.RankOne.hom_eq_embedding,
      Valuation.embedding_restrict]
  rw [← hv]
  have : Valued.v (x : ℂ_[p]) ≤ 1 := x.2
  exact_mod_cast this

theorem norm_eq_one_of_isUnit (p : ℕ) [Fact p.Prime] {x : 𝓞_ℂ_[p]} (hx : IsUnit x) :
    ‖(x : ℂ_[p])‖ = 1 := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have h1 : (x : ℂ_[p]) * (y : ℂ_[p]) = 1 := by
    have := congrArg (fun z : 𝓞_ℂ_[p] => (z : ℂ_[p])) hy
    simpa using this
  have h3 := congrArg norm h1
  rw [norm_mul, norm_one] at h3
  have ha := norm_le_one_of_mem p x
  have hb := norm_le_one_of_mem p y
  nlinarith [norm_nonneg (x : ℂ_[p]), norm_nonneg (y : ℂ_[p])]

theorem norm_pow_eq (p : ℕ) [Fact p.Prime] {V : Type} [CommRing V] {ϖ : V} {n : ℕ}
    (hn : Associated (p : V) (ϖ ^ n)) (φ : V →+* 𝓞_ℂ_[p]) :
    ‖((φ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖ ^ n = ‖(p : ℂ_[p])‖ := by
  obtain ⟨u, hu⟩ := hn
  have h1 := congrArg (fun z : V => ‖((φ z : 𝓞_ℂ_[p]) : ℂ_[p])‖) hu
  have hu1 : ‖((φ (u : V) : 𝓞_ℂ_[p]) : ℂ_[p])‖ = 1 :=
    norm_eq_one_of_isUnit p ((u.isUnit).map φ)
  simp only [map_mul, map_pow, map_natCast] at h1
  simp [norm_mul, norm_pow, hu1] at h1
  exact h1.symm

end GlobalTheory.UnifNorm

theorem GlobalTheory.unif_norm_indep : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ ϖ : V, Irreducible ϖ → ∃ r : ℝ, ∀ φ : V →+* 𝓞_ℂ_[p], ‖((φ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖ = r := by
  intro F _ _ V _ p _ hp ϖ hϖ
  classical
  have hp0 : (p : V) ≠ 0 := by
    intro h
    have h' := congrArg (fun z : V => (z : F)) h
    simp only [ZeroMemClass.coe_zero] at h'
    push_cast at h'
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h'
  have hpnu : ¬ IsUnit (p : V) := by
    intro hu
    rw [ValuationSubring.mem_nonunits_iff] at hp
    rw [ValuationSubring.valuation_eq_one_iff] at hu
    have : V.valuation ((p : V) : F) < 1 := by simpa using hp
    exact (ne_of_lt this) hu
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hp0 hϖ
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hpnu (associated_one_iff_isUnit.mp hn)
  by_cases hne : Nonempty (V →+* 𝓞_ℂ_[p])
  · obtain ⟨φ₀⟩ := hne
    refine ⟨‖((φ₀ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖, fun φ => ?_⟩
    have e1 := GlobalTheory.UnifNorm.norm_pow_eq p hn φ
    have e0 := GlobalTheory.UnifNorm.norm_pow_eq p hn φ₀
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hn0).mp (e1.trans e0.symm)
  · exact ⟨0, fun φ => (hne ⟨φ⟩).elim⟩
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_uniformizer_constant : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ ϖ : V, Irreducible ϖ → ∃ r : ℝ, ∀ φ : V →+* 𝓞_ℂ_[p], ‖((φ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖ = r := by
  atlas_forward_decl GlobalTheory.unif_norm_indep
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem isTest_base_generic : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → ∀ yb : Sp 𝓞_ℂ_[p] ⟶ X, IsTest p Xw yb → ∃ φ : V →+* 𝓞_ℂ_[p], Function.Injective φ ∧ IsLocalHom φ ∧ yb ≫ s = Spec.map (CommRingCat.ofHom φ) ∧ ∃ y : Spec (.of ℂ_[p]) ⟶ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericFibre s, y ≫ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericι s = Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ yb := by
  intro F _ _ V _ p _ hp X s Xw _ yb _

  obtain ⟨φ, hφ⟩ : ∃ φ : V →+* 𝓞_ℂ_[p], yb ≫ s = Spec.map (CommRingCat.ofHom φ) :=
    ⟨(Spec.preimage (yb ≫ s)).hom, (Spec.map_preimage (yb ≫ s)).symm⟩

  have hpV0 : ((p : V) : F) ≠ 0 := by
    push_cast; exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpV : (p : V) ∈ IsLocalRing.maximalIdeal V := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 := (V.valuation_eq_one_iff (p : V)).1 hu
    have h2 := (V.mem_nonunits_iff).1 hp
    have : ((p : V) : F) = (p : F) := by push_cast; rfl
    rw [this] at h1
    exact (ne_of_lt h2) h1
  have hpV0' : (p : V) ≠ 0 := fun h => hpV0 (by rw [h]; rfl)
  have hφp : φ (p : V) = (p : 𝓞_ℂ_[p]) := map_natCast φ p
  have hpO : ¬ IsUnit (p : 𝓞_ℂ_[p]) := Formalism.BasicNotions.Loc.OC_l_not_unit p
  have hpO0 : (p : 𝓞_ℂ_[p]) ≠ 0 := by
    intro h
    have : ((p : 𝓞_ℂ_[p]) : ℂ_[p]) = 0 := by rw [h]; rfl
    push_cast at this
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast this)

  have hmax : ∀ P : Ideal V, P.IsPrime → P ≠ ⊥ → P = IsLocalRing.maximalIdeal V := fun P hP hne =>
    IsLocalRing.eq_maximalIdeal (hP.isMaximal hne)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    by_contra hne
    push_neg at hne
    obtain ⟨a, ha, ha0⟩ := hne
    have hker : RingHom.ker φ ≠ ⊥ := fun h => ha0 (by
      have : a ∈ RingHom.ker φ := ha
      rw [h] at this; exact this)
    have := hmax _ (RingHom.ker_isPrime φ) hker
    have hp' : (p : V) ∈ RingHom.ker φ := this ▸ hpV
    exact hpO0 (hφp ▸ hp')
  have hloc : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hP := hmax (Ideal.comap φ (IsLocalRing.maximalIdeal 𝓞_ℂ_[p])) (Ideal.comap_isPrime _ _) (by
      intro h
      have : (p : V) ∈ Ideal.comap φ (IsLocalRing.maximalIdeal 𝓞_ℂ_[p]) := by
        rw [Ideal.mem_comap, hφp, IsLocalRing.mem_maximalIdeal]; exact hpO
      rw [h, Ideal.mem_bot] at this
      exact hpV0' this)
    have : a ∈ Ideal.comap φ (IsLocalRing.maximalIdeal 𝓞_ℂ_[p]) := by
      rw [hP, IsLocalRing.mem_maximalIdeal]; exact hna
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal] at this
    exact this ha
  refine ⟨φ, hinj, hloc, hφ, ?_⟩

  have hg : Function.Injective ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ) :=
    (FaithfulSMul.algebraMap_injective _ _).comp hinj
  obtain ⟨ψ, hψ⟩ : ∃ ψ : FractionRing V →+* ℂ_[p],
      ψ.comp (algebraMap V (FractionRing V)) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ :=
    ⟨IsFractionRing.lift (K := FractionRing V) hg,
      RingHom.ext fun x => IsFractionRing.lift_algebraMap (K := FractionRing V) hg x⟩
  have w : (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ yb) ≫ s =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) := by
    rw [Category.assoc, hφ, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hψ]
  let y : Spec (.of ℂ_[p]) ⟶ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericFibre s := pullback.lift _ _ w
  refine ⟨y, ?_⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericι
  exact pullback.lift_fst _ _ w

end GlobalTheory.FlatModel
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_point_generic_fibre : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → ∀ yb : Sp 𝓞_ℂ_[p] ⟶ X, IsTest p Xw yb → ∃ φ : V →+* 𝓞_ℂ_[p], Function.Injective φ ∧ IsLocalHom φ ∧ yb ≫ s = Spec.map (CommRingCat.ofHom φ) ∧ ∃ y : Spec (.of ℂ_[p]) ⟶ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericFibre s, y ≫ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericι s = Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ yb := by
  atlas_forward_decl GlobalTheory.FlatModel.isTest_base_generic
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem unit_ratio_norm_sub_le_max {p : ℕ} [Fact p.Prime] (x y : ℂ_[p]) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

theorem unit_ratio_close : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]), (∀ yb, IsTest p Xw yb → (K yb).Nonempty) → ∀ (R1 R2 A : Type) [CommRing R1] [CommRing R2] [CommRing A] (ξ1 : Sp R1 ⟶ X) (ξ2 : Sp R2 ⟶ X) (w : Sp A ⟶ X) (c1 : (Localization.Away (p : R1))ˣ) (c2 : (Localization.Away (p : R2))ˣ) (a1 : R1 →+* A) (a2 : R2 →+* A), spMap a1 ≫ ξ1 = w → spMap a2 ≫ ξ2 = w → (∀ φ : R1 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ1) → ∀ ψ : Localization.Away (p : R1) →+* ℂ_[p], ψ.comp (algebraMap R1 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ1), ‖ψ (c1 : Localization.Away (p : R1)) - κ‖ < ‖κ‖) → (∀ φ : R2 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ2) → ∀ ψ : Localization.Away (p : R2) →+* ℂ_[p], ψ.comp (algebraMap R2 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ2), ‖ψ (c2 : Localization.Away (p : R2)) - κ‖ < ‖κ‖) → ∀ (χ1 : Localization.Away (p : R1) →+* Localization.Away (p : A)) (χ2 : Localization.Away (p : R2) →+* Localization.Away (p : A)), χ1.comp (algebraMap R1 _) = (algebraMap A _).comp a1 → χ2.comp (algebraMap R2 _) = (algebraMap A _).comp a2 → ∀ φ : A →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ w) → ∀ ψ : Localization.Away (p : A) →+* ℂ_[p], ψ.comp (algebraMap A _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ‖ψ (χ1 (c1 : Localization.Away (p : R1))) - ψ (χ2 (c2 : Localization.Away (p : R2)))‖ < ‖ψ (χ2 (c2 : Localization.Away (p : R2)))‖ := by
  intro p _ X Xw K hK R1 R2 A _ _ _ ξ1 ξ2 w c1 c2 a1 a2 h1 h2 H1 H2 χ1 χ2 hχ1 hχ2 φ hφ ψ hψ
  have e1 : spMap (φ.comp a1) ≫ ξ1 = spMap φ ≫ w := by rw [← sp_sp, h1]
  have e2 : spMap (φ.comp a2) ≫ ξ2 = spMap φ ≫ w := by rw [← sp_sp, h2]
  have hψ1 : (ψ.comp χ1).comp (algebraMap R1 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (φ.comp a1) := by
    rw [RingHom.comp_assoc, hχ1, ← RingHom.comp_assoc, hψ, RingHom.comp_assoc]
  have hψ2 : (ψ.comp χ2).comp (algebraMap R2 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (φ.comp a2) := by
    rw [RingHom.comp_assoc, hχ2, ← RingHom.comp_assoc, hψ, RingHom.comp_assoc]
  obtain ⟨κ, hκ⟩ := hK _ hφ
  have k1 := H1 (φ.comp a1) (by rw [e1]; exact hφ) (ψ.comp χ1) hψ1 κ (by rw [e1]; exact hκ)
  have k2 := H2 (φ.comp a2) (by rw [e2]; exact hφ) (ψ.comp χ2) hψ2 κ (by rw [e2]; exact hκ)
  simp only [RingHom.comp_apply] at k1 k2
  set a := ψ (χ1 (c1 : Localization.Away (p : R1)))
  set b := ψ (χ2 (c2 : Localization.Away (p : R2)))
  have hab : ‖a - b‖ < ‖κ‖ := by
    have : a - b = (a - κ) - (b - κ) := by ring
    rw [this]
    exact lt_of_le_of_lt (unit_ratio_norm_sub_le_max _ _) (max_lt k1 k2)
  have hb : ‖b‖ = ‖κ‖ := by
    apply le_antisymm
    · have : b = (b - κ) + κ := by ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le k2.le le_rfl)
    · have : κ = b - (b - κ) := by ring
      calc ‖κ‖ = ‖b - (b - κ)‖ := by rw [← this]
        _ ≤ max ‖b‖ ‖b - κ‖ := unit_ratio_norm_sub_le_max _ _
        _ ≤ ‖b‖ := by
            refine max_le le_rfl ?_
            by_contra hc
            push_neg at hc
            have h3 : ‖κ‖ ≤ max ‖b‖ ‖b - κ‖ := by
              calc ‖κ‖ = ‖b - (b - κ)‖ := by rw [← this]
                _ ≤ max ‖b‖ ‖b - κ‖ := unit_ratio_norm_sub_le_max _ _
            rw [max_eq_right hc.le] at h3
            linarith
  rw [hb]; exact hab

end GlobalTheory.FlatModel
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_ratio_on_overlap : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]), (∀ yb, IsTest p Xw yb → (K yb).Nonempty) → ∀ (R1 R2 A : Type) [CommRing R1] [CommRing R2] [CommRing A] (ξ1 : Sp R1 ⟶ X) (ξ2 : Sp R2 ⟶ X) (w : Sp A ⟶ X) (c1 : (Localization.Away (p : R1))ˣ) (c2 : (Localization.Away (p : R2))ˣ) (a1 : R1 →+* A) (a2 : R2 →+* A), spMap a1 ≫ ξ1 = w → spMap a2 ≫ ξ2 = w → (∀ φ : R1 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ1) → ∀ ψ : Localization.Away (p : R1) →+* ℂ_[p], ψ.comp (algebraMap R1 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ1), ‖ψ (c1 : Localization.Away (p : R1)) - κ‖ < ‖κ‖) → (∀ φ : R2 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ2) → ∀ ψ : Localization.Away (p : R2) →+* ℂ_[p], ψ.comp (algebraMap R2 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ2), ‖ψ (c2 : Localization.Away (p : R2)) - κ‖ < ‖κ‖) → ∀ (χ1 : Localization.Away (p : R1) →+* Localization.Away (p : A)) (χ2 : Localization.Away (p : R2) →+* Localization.Away (p : A)), χ1.comp (algebraMap R1 _) = (algebraMap A _).comp a1 → χ2.comp (algebraMap R2 _) = (algebraMap A _).comp a2 → ∀ φ : A →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ w) → ∀ ψ : Localization.Away (p : A) →+* ℂ_[p], ψ.comp (algebraMap A _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ‖ψ (χ1 (c1 : Localization.Away (p : R1))) - ψ (χ2 (c2 : Localization.Away (p : R2)))‖ < ‖ψ (χ2 (c2 : Localization.Away (p : R2)))‖ := by
  atlas_forward_decl GlobalTheory.FlatModel.unit_ratio_close
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory

theorem dvd_of_norm_le_of_padicComplexInt (p : ℕ) [Fact p.Prime] (V' : Type) [CommRing V'] [IsDomain V']
    [IsDiscreteValuationRing V'] (kO : V' →+* 𝓞_ℂ_[p]) (hkO : Function.Injective kO)
    (hpT : (p : V') ∈ IsLocalRing.maximalIdeal V') (a b : V') (hb : b ≠ 0)
    (hle : ‖algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a)‖ ≤ ‖algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO b)‖) : b ∣ a := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpC : ‖(p : ℂ_[p])‖ < 1 := by
    have h3 : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
    rw [h3, norm_algebraMap', Padic.norm_p]
    have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    exact inv_lt_one_of_one_lt₀ this
  let N : V' → ℝ := fun y => ‖algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO y)‖
  have hNmul : ∀ y z, N (y * z) = N y * N z := fun y z => by
    simp only [N, map_mul, norm_mul]
  have hN0 : ∀ y, 0 ≤ N y := fun y => norm_nonneg _
  have hOC : ∀ z : ℂ_[p], z ∈ 𝓞_ℂ_[p] → ‖z‖ ≤ 1 := by
    intro z hz
    have h : z ∈ 𝓞_ℂ_[p] ↔ ‖z‖ ≤ 1 := by
      rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm]
      exact (Valued.toNormedField.norm_le_one_iff).symm
    exact h.1 hz
  have hN1 : ∀ y, N y ≤ 1 := fun y => hOC _ (kO y).2
  have hNpos : ∀ y, y ≠ 0 → 0 < N y := fun y hy => by
    apply norm_pos_iff.2
    intro h0
    exact hy (hkO (Subtype.val_injective (by simpa using h0)))
  have hNone : N 1 = 1 := by simp only [N, map_one, norm_one]
  have hNu : ∀ w : V'ˣ, N w = 1 := fun w => by
    have h1 : N (w : V') * N ((w⁻¹ : V'ˣ) : V') = 1 := by
      rw [← hNmul, Units.mul_inv, hNone]
    have := hN1 (w : V'); have := hN1 ((w⁻¹ : V'ˣ) : V')
    nlinarith [hN0 (w : V'), hN0 ((w⁻¹ : V'ˣ) : V')]
  have hNpow : ∀ y (m : ℕ), N (y ^ m) = N y ^ m := fun y m => by
    simp only [N, map_pow, norm_pow]
  have hNp : N (p : V') < 1 := by
    have : N (p : V') = ‖(p : ℂ_[p])‖ := by simp only [N, map_natCast]
    rw [this]; exact hpC
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible V'
  have hNϖ : N ϖ' < 1 := by
    have hp0' : (p : V') ≠ 0 := by
      intro h
      have : (kO (p : V') : ℂ_[p]) = 0 := by rw [h, map_zero]; rfl
      rw [map_natCast] at this
      exact hp0 (by exact_mod_cast this)
    obtain ⟨m, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0' hϖ'
    have hm : m ≠ 0 := by
      rintro rfl
      rw [pow_zero, _root_.mul_one] at hw
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hpT
      exact hpT (hw ▸ w.isUnit)
    have hNpm : N (p : V') = N ϖ' ^ m := by
      rw [hw, hNmul, hNu, _root_.one_mul, hNpow]
    by_contra hge
    have h1 : N ϖ' = 1 := le_antisymm (hN1 _) (not_lt.1 hge)
    rw [hNpm, h1, one_pow] at hNp
    exact lt_irrefl _ hNp
  rcases ValuationRing.dvd_total b a with h | ⟨d, hd⟩
  · exact h
  · by_cases hdu : IsUnit d
    · obtain ⟨w, rfl⟩ := hdu
      exact ⟨((w⁻¹ : V'ˣ) : V'), by rw [hd, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩
    · exfalso
      have hdm : d ∈ IsLocalRing.maximalIdeal V' := (IsLocalRing.mem_maximalIdeal _).2 hdu
      rw [hϖ'.maximalIdeal_eq, Ideal.mem_span_singleton'] at hdm
      obtain ⟨d', rfl⟩ := hdm
      have hNd : N (d' * ϖ') < 1 := by
        rw [hNmul]
        calc N d' * N ϖ' ≤ 1 * N ϖ' := mul_le_mul_of_nonneg_right (hN1 _) (hN0 _)
          _ < 1 := by rw [_root_.one_mul]; exact hNϖ
      have hb0 := hNpos _ hb
      have h2 : N b = N a * N (d' * ϖ') := by rw [hd, hNmul]
      have hle' : N a ≤ N b := hle
      have h4 := mul_le_mul_of_nonneg_right hle' (hN0 (d' * ϖ'))
      have h5 := mul_lt_mul_of_pos_left hNd hb0
      linarith

end GlobalTheory

namespace GlobalTheory

theorem mem_range_of_norm_le_one_at_points_away : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra V A] [Algebra.FiniteType V A], Function.Injective (algebraMap V A) → ∀ e : A, e ≠ 0 → ∀ x : Localization.Away (p : A), (∀ (T : CDVR) (kO : T.V →+* 𝓞_ℂ_[p]) (φ : A →+* T.V), T.FinRes → Function.Injective kO → φ e ≠ 0 → ∀ ψ : Localization.Away (p : A) →+* ℂ_[p], ψ.comp (algebraMap A _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (kO.comp φ) → ‖ψ x‖ ≤ 1) → ∃ a : A, algebraMap A (Localization.Away (p : A)) a = x := by
  intro F _ _ V _ p _ hp A _ _ _ _ _ hinj e he x hx
  classical
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hfin : Finite (IsLocalRing.ResidueField V) :=
    (GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField V hp0 hp).2
  have hpV : ((p : V)) ∈ IsLocalRing.maximalIdeal V := by
    rw [ValuationSubring.valuation_lt_one_iff]
    rw [ValuationSubring.mem_nonunits_iff] at hp
    simpa using hp
  have hpV0 : ((p : V)) ≠ 0 := by
    intro h
    have : ((p : V) : F) = 0 := by rw [h]; rfl
    exact hp0 (by exact_mod_cast this)
  let O' := AdicCompletion (IsLocalRing.maximalIdeal V) V
  have hinj0 : Function.Injective (algebraMap V O') := GlobalTheory.algebraMap_adicCompletion_injective_of_dvr V
  haveI : CharZero O' := charZero_of_injective_algebraMap hinj0
  haveI : IsLocalHom (algebraMap V O') := inferInstance
  have hfinO' : Finite (IsLocalRing.ResidueField O') :=
    Finite.of_surjective _ (AdicCompletion.residueField_map_bijective V).2
  let L := Localization.Away (p : A)
  have hpA0 : (p : A) ≠ 0 := by
    intro h
    apply hpV0
    apply hinj
    rw [map_natCast, h, map_zero]
  let Ω := FractionRing A
  have hu : IsUnit (algebraMap A Ω (p : A)) :=
    IsUnit.mk0 _ (fun h => hpA0 (IsFractionRing.injective A Ω (by rw [h, map_zero])))
  let j : L →+* Ω := IsLocalization.Away.lift (p : A) hu
  have hj : ∀ a, j (algebraMap A L a) = algebraMap A Ω a := fun a => IsLocalization.lift_eq _ a
  have hjinj : Function.Injective j := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (p : A) y
    have h1 : algebraMap A Ω a = 0 := by rw [← hj, ← ha, map_mul, hy, zero_mul]
    have h2 : a = 0 := IsFractionRing.injective A Ω (by rw [h1, map_zero])
    have h3 : IsUnit (algebraMap A L (p : A) ^ n) := (IsLocalization.Away.algebraMap_isUnit (p : A)).pow n
    rw [h2, map_zero] at ha
    exact h3.mul_left_eq_zero.1 ha
  obtain ⟨s, hs1, hsint⟩ := GlobalTheory.isIntegral_mul_of_bounded_at_points V O' hinj0
    (GlobalTheory.exists_integral_point_of_complete_case
      (fun O B _ _ _ _ _ _ _ _ _ _ M hM hsp e he => GlobalTheory.exists_integral_point_through O B M hM hsp e he)
      V O' hinj0)
    A Ω hinj e he (j x) (fun V' _ _ _ _ _ φ hφ hφe a b hab hb => by
      obtain ⟨-, hloc', hcpl, hch, hfin'⟩ := GlobalTheory.dvr_finite_over_complete_dvr O' V'
      let T : CDVR := { V := V' }
      have hT : T.FinRes := hfin' hfinO'
      obtain ⟨q, hq, k, kO, hk⟩ := GlobalTheory.CompleteDvrEmbedding.exists_embedding_padicComplexInt T hT
      have hpT : (p : V') ∈ IsLocalRing.maximalIdeal V' := by
        have h1 : (p : V') = algebraMap O' V' (algebraMap V O' (p : V)) := by
          rw [map_natCast, map_natCast]
        rw [h1, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu'
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hpV
        exact hpV (isUnit_of_map_unit _ _ (isUnit_of_map_unit _ _ hu'))
      obtain rfl := GlobalTheory.FlatModel.eq_of_mem_maximalIdeal_of_padicComplexInt T p q hpT kO
      have hkO : Function.Injective kO := fun a b hab => by
        apply IsFractionRing.injective T.V T.Fr
        apply k.injective
        rw [← hk, ← hk, hab]
      let g : A →+* ℂ_[p] := (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (kO.comp φ)
      have hgu : IsUnit (g (p : A)) := by
        rw [map_natCast]
        exact IsUnit.mk0 _ (by exact_mod_cast hp0)
      let ψ : L →+* ℂ_[p] := IsLocalization.Away.lift (p : A) hgu
      have hψ : ψ.comp (algebraMap A L) = g := IsLocalization.Away.lift_comp (p : A) hgu
      have hxle : ‖ψ x‖ ≤ 1 := hx T kO φ hT hkO hφe ψ hψ
      have hxb : x * algebraMap A L b = algebraMap A L a := by
        apply hjinj
        rw [map_mul, hj, hj, hab]
      have hgab : ψ x * g b = g a := by
        rw [← hψ, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, hxb]
      refine GlobalTheory.dvd_of_norm_le_of_padicComplexInt p V' kO hkO hpT (φ a) (φ b) hb ?_
      change ‖g a‖ ≤ ‖g b‖
      rw [← hgab, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hxle
      )
  obtain ⟨c, hc⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1 hsint
  have hsc : algebraMap A L s * x = algebraMap A L c := by
    apply hjinj
    rw [map_mul, hj, hj, hc]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hs1' : s - 1 ∈ Ideal.span {algebraMap V A ϖ} := by
    rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] at hs1
    exact hs1
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hs1'
  have hcop : IsCoprime s (algebraMap V A ϖ) := ⟨1, -t, by linear_combination (-1 : A) * ht⟩
  obtain ⟨k, u, hpu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hpV0 hϖ
  obtain ⟨n, a0, ha0⟩ := IsLocalization.Away.surj (p : A) x
  have hpA : ((p : A)) ^ n = algebraMap V A ((u ^ n : Vˣ) : V) * algebraMap V A ϖ ^ (k * n) := by
    rw [← map_natCast (algebraMap V A), hpu, ← map_pow, ← map_pow, ← map_mul, mul_pow, ← pow_mul,
      Units.val_pow_eq_pow_val]
  have hcopU : IsCoprime s (algebraMap V A ((u ^ n : Vˣ) : V)) := by
    obtain ⟨w, hw⟩ := ((u ^ n).isUnit.map (algebraMap V A))
    exact ⟨0, ((w⁻¹ : Aˣ) : A), by rw [← hw]; simp⟩
  have hcopP : IsCoprime s ((p : A) ^ n) := by
    rw [hpA]
    exact hcopU.mul_right (hcop.pow_right)
  obtain ⟨α, β, hαβ⟩ := hcopP
  refine ⟨α * c + β * a0, ?_⟩
  have hαβ' : algebraMap A L α * algebraMap A L s + algebraMap A L β * algebraMap A L (p : A) ^ n = 1 := by
    rw [← map_pow, ← map_mul, ← map_mul, ← map_add, hαβ, map_one]
  rw [map_add, map_mul, map_mul]
  linear_combination (-(algebraMap A L α)) * hsc + (-(algebraMap A L β)) * ha0 + x * hαβ'

end GlobalTheory
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.element_of_dvr_test_points : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra V A] [Algebra.FiniteType V A], Function.Injective (algebraMap V A) → ∀ e : A, e ≠ 0 → ∀ x : Localization.Away (p : A), (∀ (T : CDVR) (kO : T.V →+* 𝓞_ℂ_[p]) (φ : A →+* T.V), T.FinRes → Function.Injective kO → φ e ≠ 0 → ∀ ψ : Localization.Away (p : A) →+* ℂ_[p], ψ.comp (algebraMap A _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (kO.comp φ) → ‖ψ x‖ ≤ 1) → ∃ a : A, algebraMap A (Localization.Away (p : A)) a = x := by
  atlas_forward_decl GlobalTheory.mem_range_of_norm_le_one_at_points_away
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem chart_normal_domain_testPoints : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → Flat s → LocallyOfFiniteType s → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (Xw : Set X).Nonempty → ∀ (A : Type) [CommRing A] (w : Sp A ⟶ X), IsOpenImmersion w → Nonempty (Sp A) → ∃ (_ : IsDomain A) (_ : IsIntegrallyClosed A) (_ : Algebra V A) (_ : Algebra.FiniteType V A), Function.Injective (algebraMap V A) ∧ ∃ e : A, e ≠ 0 ∧ ∀ (T : CDVR) (kO : T.V →+* 𝓞_ℂ_[p]) (φ : A →+* T.V), T.FinRes → Function.Injective kO → φ e ≠ 0 → IsTest p Xw (spMap (kO.comp φ) ≫ w) := by
  intro F _ _ V p _ hp X s Xw hX hN hflat hlft hXw hne A _ w hw hA
  haveI : IsIntegral (Sp A) := isIntegral_of_isOpenImmersion w
  haveI : IsDomain A := (affine_isIntegral_iff (CommRingCat.of A)).1 inferInstance
  haveI : GlobalTheory.IsNormalScheme X := GlobalTheory.IsNormalScheme.of_pred hN
  haveI : GlobalTheory.IsNormalScheme (Sp A) := GlobalTheory.IsNormalScheme.of_isOpenImmersion w
  have hic : IsIntegrallyClosed A :=
    (GlobalTheory.IsNormalScheme.spec_iff_of_isDomain (CommRingCat.of A)).1 inferInstance
  let f : V →+* A := (Spec.preimage (w ≫ s)).hom
  letI : Algebra V A := f.toAlgebra
  haveI hft : Algebra.FiniteType V A := by
    have h : LocallyOfFiniteType (w ≫ s) := inferInstance
    rw [← Spec.map_preimage (w ≫ s)] at h
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h
  have hinj : Function.Injective (algebraMap V A) := by
    have h : Flat (w ≫ s) := inferInstance
    rw [← Spec.map_preimage (w ≫ s)] at h
    haveI : Module.Flat V A := (HasRingHomProperty.Spec_iff (P := @Flat)).1 h
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := A) (mem_nonZeroDivisors_of_ne_zero h0)
    have h1 : a • (1 : A) = a • (0 : A) := by rw [Algebra.smul_def, _root_.mul_one, ha, smul_zero]
    exact one_ne_zero (hreg h1)
  obtain ⟨y⟩ := hA
  have hopen : IsOpen (Set.range w) := w.isOpenEmbedding.isOpen_range
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ := nonempty_preirreducible_inter hopen Xw.isOpen ⟨_, y, rfl⟩ hne
  have hzO : z ∈ w ⁻¹ᵁ Xw := hz
  obtain ⟨_, ⟨e, rfl⟩, hze, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    hzO (w ⁻¹ᵁ Xw).isOpen
  have he : e ≠ 0 := by
    rintro rfl
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hze (Ideal.zero_mem _)
  refine ⟨inferInstance, hic, this, hft, hinj, e, he, ?_⟩
  intro T kO φ hT hkO hφe
  refine ⟨⟨T, kO, spMap φ ≫ w, hT, hkO, sp_sp _ _ _⟩, ?_⟩
  rintro _ ⟨u, rfl⟩
  have hu : u = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ_[p]) := by
    apply PrimeSpectrum.ext
    haveI := (u : PrimeSpectrum ℂ_[p]).isPrime
    exact Ideal.eq_bot_of_prime _
  subst hu
  have hinj2 : Function.Injective ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO) := Subtype.val_injective.comp hkO
  rw [← sp_sp φ kO w, sp_sp kO (algebraMap 𝓞_ℂ_[p] ℂ_[p]) (spMap φ ≫ w), bot_map hinj2 (spMap φ ≫ w)]
  have hq : (spMap φ) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.V) ∈ PrimeSpectrum.basicOpen e := by
    show e ∉ Ideal.comap φ ⊥
    simpa using hφe
  exact hsub hq

end GlobalTheory.FlatModel

end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_affine_integrally_closed_domain : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → Flat s → LocallyOfFiniteType s → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (Xw : Set X).Nonempty → ∀ (A : Type) [CommRing A] (w : Sp A ⟶ X), IsOpenImmersion w → Nonempty (Sp A) → ∃ (_ : IsDomain A) (_ : IsIntegrallyClosed A) (_ : Algebra V A) (_ : Algebra.FiniteType V A), Function.Injective (algebraMap V A) ∧ ∃ e : A, e ≠ 0 ∧ ∀ (T : CDVR) (kO : T.V →+* 𝓞_ℂ_[p]) (φ : A →+* T.V), T.FinRes → Function.Injective kO → φ e ≠ 0 → IsTest p Xw (spMap (kO.comp φ) ≫ w) := by
  atlas_forward_decl GlobalTheory.FlatModel.chart_normal_domain_testPoints
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem norm_coe_of_isUnit_padicComplexInt (p : ℕ) [Fact p.Prime] (x : 𝓞_ℂ_[p]) (hx : IsUnit x) :
    ‖(x : ℂ_[p])‖ = 1 := by
  have h1 := (PadicComplexInt.integers p).isUnit_iff_valuation_eq_one.1 hx
  rw [← coe_valued]
  change ((Valued.v ((algebraMap 𝓞_ℂ_[p] ℂ_[p]) x) : ℝ≥0) : ℝ) = 1
  rw [h1]; rfl

theorem sub_one_mem_radical_of_isTest : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → DensSt → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → Flat s → LocallyOfFiniteType s → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (Xw : Set X).Nonempty → ∀ (A : Type) [CommRing A] (w : Sp A ⟶ X), IsOpenImmersion w → ∀ u : A, (∀ φ : A →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ w) → ‖(φ u : ℂ_[p]) - 1‖ < 1) → u - 1 ∈ (Ideal.span {(p : A)}).radical := by
  intro F _ _ V p _ hp hD X s Xw hX hflat hlft hXw hne A _ w hw u hu
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  rintro 𝔮 ⟨hle, h𝔮⟩
  by_contra hf
  let f : A := u - 1
  let B := Localization.Away f
  haveI : IsOpenImmersion (spMap (algebraMap A B)) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))
  let ξ : Sp B ⟶ X := spMap (algebraMap A B) ≫ w
  have hpq : (p : A) ∈ 𝔮 := hle (Ideal.subset_span rfl)
  have hdisj : Disjoint (Submonoid.powers f : Set A) (𝔮 : Set A) :=
    (Ideal.disjoint_powers_iff_notMem _ h𝔮.isRadical).2 hf
  let Q : Ideal B := Ideal.map (algebraMap A B) 𝔮
  haveI hQ : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) B 𝔮 h𝔮 hdisj
  have hpQ : (p : B) ∈ Q := by
    rw [← map_natCast (algebraMap A B)]; exact Ideal.mem_map_of_mem _ hpq
  let y : Sp B := (⟨Q, hQ⟩ : PrimeSpectrum B)
  have hx : ξ y ∉ X.basicOpen (p : Γ(X, ⊤)) := by
    have h1 : y ∉ ξ ⁻¹ᵁ X.basicOpen (p : Γ(X, ⊤)) := by
      rw [Scheme.preimage_basicOpen_top, map_natCast]
      have h2 : ((p : Γ(Sp B, ⊤))) = (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (p : B) := (map_natCast _ _).symm
      rw [h2, basicOpen_eq_of_affine]
      intro h3
      exact ((PrimeSpectrum.mem_basicOpen _ _).1 h3) hpQ
    exact h1
  obtain ⟨φ, hφ⟩ := hD F V p hp X s Xw hX hflat hlft hXw hne B ξ inferInstance ⟨ξ y, ⟨y, rfl⟩, hx⟩
  have hφ' : IsTest p Xw (spMap (φ.comp (algebraMap A B)) ≫ w) := by
    rw [← sp_sp]; exact hφ
  have h1 := hu _ hφ'
  have hunit : IsUnit ((φ.comp (algebraMap A B)) f) :=
    (IsLocalization.Away.algebraMap_isUnit (S := B) f).map φ
  have h2 : ((φ.comp (algebraMap A B) u : 𝓞_ℂ_[p]) : ℂ_[p]) - 1 = (((φ.comp (algebraMap A B)) f : 𝓞_ℂ_[p]) : ℂ_[p]) := by
    simp [f, map_sub]
  rw [h2, norm_coe_of_isUnit_padicComplexInt p _ hunit] at h1
  exact lt_irrefl _ h1

end GlobalTheory.FlatModel
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_of_test_point_estimate : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → DensSt → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → Flat s → LocallyOfFiniteType s → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (Xw : Set X).Nonempty → ∀ (A : Type) [CommRing A] (w : Sp A ⟶ X), IsOpenImmersion w → ∀ u : A, (∀ φ : A →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ w) → ‖(φ u : ℂ_[p]) - 1‖ < 1) → u - 1 ∈ (Ideal.span {(p : A)}).radical := by
  atlas_forward_decl GlobalTheory.FlatModel.sub_one_mem_radical_of_isTest
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem exists_unit_ratio_of_close : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → DensSt → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsProjOver s → Flat s → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (Xw : Set X).Nonempty → ∀ (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]), (∀ yb, IsTest p Xw yb → (K yb).Nonempty) → ∀ (R1 R2 A : Type) [CommRing R1] [CommRing R2] [CommRing A] (ξ1 : Sp R1 ⟶ X) (ξ2 : Sp R2 ⟶ X) (w : Sp A ⟶ X) (c1 : (Localization.Away (p : R1))ˣ) (c2 : (Localization.Away (p : R2))ˣ) (a1 : R1 →+* A) (a2 : R2 →+* A), IsOpenImmersion ξ1 → IsOpenImmersion ξ2 → IsOpenImmersion w → spMap a1 ≫ ξ1 = w → spMap a2 ≫ ξ2 = w → (∀ φ : R1 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ1) → ∀ ψ : Localization.Away (p : R1) →+* ℂ_[p], ψ.comp (algebraMap R1 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ1), ‖ψ (c1 : Localization.Away (p : R1)) - κ‖ < ‖κ‖) → (∀ φ : R2 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ2) → ∀ ψ : Localization.Away (p : R2) →+* ℂ_[p], ψ.comp (algebraMap R2 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ2), ‖ψ (c2 : Localization.Away (p : R2)) - κ‖ < ‖κ‖) → ∃ u : Aˣ, (u : A) - 1 ∈ (Ideal.span {(p : A)}).radical ∧ ∀ (χ1 : Localization.Away (p : R1) →+* Localization.Away (p : A)) (χ2 : Localization.Away (p : R2) →+* Localization.Away (p : A)), χ1.comp (algebraMap R1 _) = (algebraMap A _).comp a1 → χ2.comp (algebraMap R2 _) = (algebraMap A _).comp a2 → algebraMap A (Localization.Away (p : A)) (u : A) * χ2 (c2 : Localization.Away (p : R2)) = χ1 (c1 : Localization.Away (p : R1)) := by
  intro F _ _ V _ p _ hp hD X s Xw hXi hXn hproj hflat hXw hne K hK R1 R2 A _ _ _ ξ1 ξ2 w c1 c2 a1 a2 hξ1 hξ2 hw e1 e2 hc1 hc2
  classical
  have hlft : LocallyOfFiniteType s := GlobalTheory.T.locallyOfFiniteType_of_isProjOver V X s hproj
  have hu1 : IsUnit (((algebraMap A (Localization.Away (p : A))).comp a1) (p : R1)) := by
    simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (p : A)) (p : A)
  have hu2 : IsUnit (((algebraMap A (Localization.Away (p : A))).comp a2) (p : R2)) := by
    simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (p : A)) (p : A)
  let χ1 : Localization.Away (p : R1) →+* Localization.Away (p : A) := IsLocalization.Away.lift (p : R1) hu1
  let χ2 : Localization.Away (p : R2) →+* Localization.Away (p : A) := IsLocalization.Away.lift (p : R2) hu2
  have hχ1 : χ1.comp (algebraMap R1 _) = (algebraMap A _).comp a1 := RingHom.ext fun x => IsLocalization.lift_eq _ x
  have hχ2 : χ2.comp (algebraMap R2 _) = (algebraMap A _).comp a2 := RingHom.ext fun x => IsLocalization.lift_eq _ x
  have hcl := GlobalTheory.T.chart_ratio_on_overlap p X Xw K hK R1 R2 A ξ1 ξ2 w c1 c2 a1 a2 e1 e2 hc1 hc2 χ1 χ2 hχ1 hχ2
  let r : (Localization.Away (p : A))ˣ := Units.map (χ1 : _ →* _) c1 * (Units.map (χ2 : _ →* _) c2)⁻¹
  have hr : (r : Localization.Away (p : A)) * χ2 (c2 : Localization.Away (p : R2)) = χ1 (c1 : Localization.Away (p : R1)) := by
    have h0 : r * Units.map (χ2 : _ →* _) c2 = Units.map (χ1 : _ →* _) c1 := by simp [r]
    have h0' := congrArg Units.val h0
    simpa using h0'
  have hnorm : ∀ φ : A →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ w) → ∀ ψ : Localization.Away (p : A) →+* ℂ_[p],
      ψ.comp (algebraMap A _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ →
      ‖ψ (r : Localization.Away (p : A)) - 1‖ < 1 ∧ ‖ψ (r : Localization.Away (p : A))‖ = 1 ∧
        ‖ψ ((r⁻¹ : (Localization.Away (p : A))ˣ) : Localization.Away (p : A))‖ = 1 := by
    intro φ hφ ψ hψ
    have h := hcl φ hφ ψ hψ
    set b := ψ (χ2 (c2 : Localization.Away (p : R2)))
    have hb : b ≠ 0 := ((c2.isUnit.map χ2).map ψ).ne_zero
    have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb
    have hrb : ψ (r : Localization.Away (p : A)) * b = ψ (χ1 (c1 : Localization.Away (p : R1))) := by
      rw [← map_mul, hr]
    have h1 : ‖ψ (r : Localization.Away (p : A)) - 1‖ < 1 := by
      have : (ψ (r : Localization.Away (p : A)) - 1) * b = ψ (χ1 (c1 : Localization.Away (p : R1))) - b := by
        rw [sub_mul, hrb, _root_.one_mul]
      have h2 : ‖ψ (r : Localization.Away (p : A)) - 1‖ * ‖b‖ < 1 * ‖b‖ := by
        rw [← norm_mul, this, _root_.one_mul]; exact h
      exact lt_of_mul_lt_mul_right h2 hbn.le
    have h3 : ‖ψ (r : Localization.Away (p : A))‖ = 1 := by
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (1 : ℂ_[p])) (y := ψ (r : Localization.Away (p : A)) - 1) (by rw [norm_one]; exact h1.ne')
      rw [add_sub_cancel, norm_one, max_eq_left h1.le] at this
      exact this
    refine ⟨h1, h3, ?_⟩
    have h4 : ψ (r : Localization.Away (p : A)) * ψ ((r⁻¹ : (Localization.Away (p : A))ˣ) : Localization.Away (p : A)) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h5 := congrArg norm h4
    rw [norm_mul, h3, _root_.one_mul, norm_one] at h5
    exact h5
  have hfin : ∀ χ1' : Localization.Away (p : R1) →+* Localization.Away (p : A), ∀ χ2' : Localization.Away (p : R2) →+* Localization.Away (p : A),
      χ1'.comp (algebraMap R1 _) = (algebraMap A _).comp a1 → χ2'.comp (algebraMap R2 _) = (algebraMap A _).comp a2 →
      χ1' = χ1 ∧ χ2' = χ2 := fun χ1' χ2' h1 h2 =>
    ⟨IsLocalization.ringHom_ext (Submonoid.powers (p : R1)) (h1.trans hχ1.symm),
      IsLocalization.ringHom_ext (Submonoid.powers (p : R2)) (h2.trans hχ2.symm)⟩
  by_cases hA : Nonempty (Sp A)
  swap
  · have hsub : Subsingleton A := by
      by_contra h
      rw [not_subsingleton_iff_nontrivial] at h
      exact hA inferInstance
    have hsubL : Subsingleton (Localization.Away (p : A)) := by
      refine ⟨fun x y => ?_⟩
      rw [← _root_.mul_one x, ← _root_.mul_one y, ← map_one (algebraMap A (Localization.Away (p : A))), Subsingleton.elim (1 : A) 0, map_zero, mul_zero, mul_zero]
    refine ⟨1, by simp, fun χ1' χ2' _ _ => Subsingleton.elim _ _⟩
  obtain ⟨hdom, hic, alg, hft, hinjV, e, he0, htest⟩ := GlobalTheory.T.open_affine_integrally_closed_domain F V p hp X s Xw hXi hXn hflat hlft hXw hne A w hw hA
  have hbdd : ∀ x : (Localization.Away (p : A))ˣ, (x = r ∨ x = r⁻¹) → ∃ a : A, algebraMap A _ a = (x : Localization.Away (p : A)) := by
    intro x hx
    refine GlobalTheory.T.element_of_dvr_test_points F V p hp A hinjV e he0 _ fun T kO φ hT hkO hφe ψ hψ => ?_
    have := hnorm (kO.comp φ) (htest T kO φ hT hkO hφe) ψ hψ
    rcases hx with rfl | rfl
    · exact this.2.1.le
    · exact this.2.2.le
  obtain ⟨a, ha⟩ := hbdd r (Or.inl rfl)
  obtain ⟨b, hb⟩ := hbdd r⁻¹ (Or.inr rfl)
  have hp0 : (p : A) ≠ 0 := by
    intro h0
    have : algebraMap V A (p : V) = algebraMap V A 0 := by rw [map_natCast, map_zero, h0]
    have h1 := hinjV this
    have h2 := congrArg (fun x : V => (x : F)) h1
    simp at h2
    exact (Fact.out : p.Prime).ne_zero h2
  have hinjL : Function.Injective (algebraMap A (Localization.Away (p : A))) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hp0)
  have hab : a * b = 1 := hinjL (by rw [map_mul, ha, hb, Units.mul_inv, map_one])
  let u : Aˣ := ⟨a, b, hab, by rw [mul_comm]; exact hab⟩
  refine ⟨u, ?_, fun χ1' χ2' h1 h2 => ?_⟩
  · refine GlobalTheory.T.unit_of_test_point_estimate F V p hp hD X s Xw hXi hflat hlft hXw hne A w hw a fun φ hφ => ?_
    have hpu : IsUnit (((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ) (p : A)) := by
      rw [map_natCast]
      exact IsUnit.mk0 _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
    let ψ : Localization.Away (p : A) →+* ℂ_[p] := IsLocalization.Away.lift (p : A) hpu
    have hψ : ψ.comp (algebraMap A _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ := IsLocalization.lift_comp _
    have := (hnorm φ hφ ψ hψ).1
    rw [← ha] at this
    have e3 : ψ (algebraMap A _ a) = (φ a : ℂ_[p]) := RingHom.congr_fun hψ a
    rw [e3] at this
    exact this
  · obtain ⟨rfl, rfl⟩ := hfin χ1' χ2' h1 h2
    change algebraMap A _ a * _ = _
    rw [ha, hr]

end GlobalTheory.FlatModel
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_charts_normal_projective : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → DensSt → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsProjOver s → Flat s → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (Xw : Set X).Nonempty → ∀ (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]), (∀ yb, IsTest p Xw yb → (K yb).Nonempty) → ∀ (R1 R2 A : Type) [CommRing R1] [CommRing R2] [CommRing A] (ξ1 : Sp R1 ⟶ X) (ξ2 : Sp R2 ⟶ X) (w : Sp A ⟶ X) (c1 : (Localization.Away (p : R1))ˣ) (c2 : (Localization.Away (p : R2))ˣ) (a1 : R1 →+* A) (a2 : R2 →+* A), IsOpenImmersion ξ1 → IsOpenImmersion ξ2 → IsOpenImmersion w → spMap a1 ≫ ξ1 = w → spMap a2 ≫ ξ2 = w → (∀ φ : R1 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ1) → ∀ ψ : Localization.Away (p : R1) →+* ℂ_[p], ψ.comp (algebraMap R1 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ1), ‖ψ (c1 : Localization.Away (p : R1)) - κ‖ < ‖κ‖) → (∀ φ : R2 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ2) → ∀ ψ : Localization.Away (p : R2) →+* ℂ_[p], ψ.comp (algebraMap R2 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ2), ‖ψ (c2 : Localization.Away (p : R2)) - κ‖ < ‖κ‖) → ∃ u : Aˣ, (u : A) - 1 ∈ (Ideal.span {(p : A)}).radical ∧ ∀ (χ1 : Localization.Away (p : R1) →+* Localization.Away (p : A)) (χ2 : Localization.Away (p : R2) →+* Localization.Away (p : A)), χ1.comp (algebraMap R1 _) = (algebraMap A _).comp a1 → χ2.comp (algebraMap R2 _) = (algebraMap A _).comp a2 → algebraMap A (Localization.Away (p : A)) (u : A) * χ2 (c2 : Localization.Away (p : R2)) = χ1 (c1 : Localization.Away (p : R1)) := by
  atlas_forward_decl GlobalTheory.FlatModel.exists_unit_ratio_of_close
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem princSt_of_connSt_propZ_densSt : ConnSt → GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.PropZ → DensSt → PrincSt := by
  intro hConn hZ hDens F _ _ V p _ hp X s Xw hXi hXn hproj hflat hXw hirr K hK hU
  by_cases hT : ∃ yb, IsTest p Xw yb
  swap
  · exact ⟨0, fun yb h => absurd ⟨yb, h⟩ hT⟩
  obtain ⟨yb₀, hyb₀⟩ := hT
  have hne : (Xw : Set X).Nonempty := (Set.range_nonempty _).mono hyb₀.2
  haveI : IsDiscreteValuationRing V :=
    (GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField V (Fact.out : p.Prime).ne_zero hp).1
  obtain ⟨D, hD, ht, sig, hsig, hval⟩ := GlobalTheory.T.exists_charts_normal_projective_covering GlobalTheory.T.exists_charts_normal_projective hDens F V p hp X s Xw hXi hXn hproj hflat hXw hne K hK hU
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hprop : IsProper s := by
    obtain ⟨N, i, hi, hs⟩ := hproj
    have := isProper_str V N
    rw [← hs]
    infer_instance
  have hHyp : GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.Hyp s D :=
    ⟨hXi, fun z => (hXn z).2, hprop, hflat, hConn F V X s Xw hXi hXn hproj hflat hirr, hD, ht⟩
  obtain ⟨M, n, hM, -, hVC⟩ := hZ V ϖ hϖ X s D hHyp sig hsig
  obtain ⟨r, hr⟩ := GlobalTheory.T.norm_uniformizer_constant F V p hp ϖ hϖ
  refine ⟨(r ^ n) ^ ((M : ℝ)⁻¹), fun yb hyb κ hκ => ?_⟩
  obtain ⟨φ, hφi, hφl, hφs, y, hy⟩ := GlobalTheory.T.test_point_generic_fibre F V p hp X s Xw hXw yb hyb
  obtain ⟨⟨e, cc, he, hco⟩, hall⟩ := hVC 𝓞_ℂ_[p] ℂ_[p] ℝ≥0 (Valued.v : Valuation ℂ_[p] ℝ≥0)
    (PadicComplexInt.integers p) φ hφi hφl yb hφs y hy
  have h1 := hall e cc he hco
  have h2 := hval yb hyb y hy e cc he hco κ hκ
  have h3 : ‖(cc : ℂ_[p])‖ ^ M = r ^ n := by
    have := congrArg (fun t : ℝ≥0 => (t : ℝ)) h1
    simp only [NNReal.coe_pow, NNReal.coe_zpow, coe_valued] at this
    rw [this, ← hr φ]
    rfl
  rw [← h2, ← h3, Real.pow_rpow_inv_natCast (norm_nonneg _) (by omega)]

end GlobalTheory.FlatModel
end
end

open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_of_connected_density : ConnSt → GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.PropZ → DensSt → PrincSt := by
  atlas_forward_decl GlobalTheory.FlatModel.princSt_of_connSt_propZ_densSt
end
