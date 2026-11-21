import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSectionsMonoReductionAffineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltrationIdealLeMapOfIsDPMorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersOfCompOnGenerators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPreDividedPowersOfGenerators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCechDeRhamRelationsTotalDetectZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedPre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedMapsAgreeCohomologyZeroOneInstances
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedMapsAgreeCohomologyTwoInstances
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomSpecPointsLevels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineForgetFormsBijectiveSiteAndPairs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFormsBijectiveDegreeOneTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormsMapOfDividedPowerDerivation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleFormsCochainsEqDeRhamCochainsSmoothLifStatement

section
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isPreDividedPowers_of_generators : ∀ (B ι : Type) [CommRing B] (x : ι → B) (g : ι → ℕ → B), (∀ i, g i 0 = 1) → (∀ i, g i 1 = x i) → (∀ i n, n ≠ 0 → g i n ∈ Ideal.span (Set.range x)) → (∀ i m n, g i m * g i n = ((m + n).choose m : B) * g i (m + n)) → (∀ c : ι →₀ B, (c.sum fun i a ↦ a * x i) = 0 → (c.prod fun i a ↦ PowerSeries.mk fun n ↦ a ^ n * g i n) = 1) → ∃ γ : ℕ → B → B, IsPreDP (Ideal.span (Set.range x)) γ ∧ ∀ i n, γ n (x i) = g i n := by
  first | exact @GlobalTheory.PDA.exists_isPreDividedPowers_of_generators₂ | exact GlobalTheory.PDA.exists_isPreDividedPowers_of_generators₂ | (intros; apply GlobalTheory.PDA.exists_isPreDividedPowers_of_generators₂ <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.DPFlat

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R} (κ : DividedPowers I)

def expS (z : R) (y : A) : PowerSeries A :=
  PowerSeries.mk fun n ↦ y ^ n * algebraMap R A (κ.dpow n z)

theorem expS_add_right {z : R} (hz : z ∈ I) (y y' : A) :
    expS κ z (y + y') = expS κ z y * expS κ z y' := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  have h : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n, y ^ p.1 * algebraMap R A (κ.dpow p.1 z) *
      (y' ^ p.2 * algebraMap R A (κ.dpow p.2 z)) =
      y ^ p.1 * y' ^ p.2 * (n.choose p.1 : A) * algebraMap R A (κ.dpow n z) := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h := κ.mul_dpow (m := p.1) (n := p.2) hz
    rw [hp] at h
    calc _ = y ^ p.1 * y' ^ p.2 * algebraMap R A (κ.dpow p.1 z * κ.dpow p.2 z) := by
            rw [map_mul]; ring
      _ = _ := by rw [h, map_mul, map_natCast]; ring
  rw [Finset.sum_congr rfl h, ← Finset.sum_mul, add_pow, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem expS_add_left {z z' : R} (hz : z ∈ I) (hz' : z' ∈ I) (y : A) :
    expS κ (z + z') y = expS κ z y * expS κ z' y := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_mul, κ.dpow_add hz hz', map_sum, map_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, pow_add]; ring

theorem expS_smul {z : R} (hz : z ∈ I) (a : R) (y : A) :
    expS κ z (algebraMap R A a * y) = expS κ (a * z) y := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, κ.dpow_mul hz, map_mul, map_pow]
  ring

theorem expS_zero_left (y : A) : expS κ 0 y = 1 := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [κ.dpow_zero I.zero_mem]
  · simp [κ.dpow_eval_zero hn, hn]

theorem expS_zero_right (z : R) (hz : z ∈ I) : expS κ z (0 : A) = 1 := by
  ext n
  simp only [expS, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [κ.dpow_zero hz]
  · simp [hn]

theorem expS_sum_right {z : R} (hz : z ∈ I) {K : Type} (s : Finset K) (f : K → A) :
    expS κ z (∑ k ∈ s, f k) = ∏ k ∈ s, expS κ z (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expS_zero_right κ z hz]
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.prod_insert hk, expS_add_right κ hz, ih]

theorem expS_sum_left {K : Type} (s : Finset K) (f : K → R) (hf : ∀ k ∈ s, f k ∈ I) (y : A) :
    expS κ (∑ k ∈ s, f k) y = ∏ k ∈ s, expS κ (f k) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expS_zero_left κ y]
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.prod_insert hk,
      expS_add_left κ (hf k (Finset.mem_insert_self k s))
        (Ideal.sum_mem _ fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)]

theorem prod_expS_eq_one [Module.Flat R A] (c : I →₀ A)
    (hc : (c.sum fun i a ↦ a * algebraMap R A i) = 0) :
    (c.prod fun i a ↦ PowerSeries.mk fun n ↦ a ^ n * algebraMap R A (κ.dpow n i)) = 1 := by
  have h : ∑ i : ↥c.support, ((i : I) : R) • (c (i : I) : A) = (0 : A) := by
    rw [Finset.sum_coe_sort c.support (fun i : I ↦ ((i : R)) • (c i : A)), ← hc, Finsupp.sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, mul_comm]
  obtain ⟨k, a, y, hx, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := A) h
  simp only at hx ha
  change (∏ i ∈ c.support, expS κ (i : R) (c i)) = 1
  rw [← Finset.prod_coe_sort]
  calc ∏ i : c.support, expS κ ((i.1 : I) : R) (c i.1)
      = ∏ i : c.support, ∏ j, expS κ (a i j * ((i.1 : I) : R)) (y j) := by
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        rw [hx i, expS_sum_right κ (i.1 : I).2]
        refine Finset.prod_congr rfl fun j _ ↦ ?_
        rw [Algebra.smul_def, expS_smul κ (i.1 : I).2]
    _ = ∏ j, ∏ i : c.support, expS κ (a i j * ((i.1 : I) : R)) (y j) := Finset.prod_comm
    _ = ∏ j, expS κ (∑ i : c.support, a i j * ((i.1 : I) : R)) (y j) := by
        refine Finset.prod_congr rfl fun j _ ↦ ?_
        rw [expS_sum_left κ _ _ fun i _ ↦ I.mul_mem_left _ (i.1 : I).2]
    _ = 1 := by
        refine Finset.prod_eq_one fun j _ ↦ ?_
        have : ∑ i : c.support, a i j * ((i.1 : I) : R) = 0 := by
          rw [← ha j]; exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
        rw [this, expS_zero_left]

theorem exists_isDPMorphism_of_flat : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] (I : Ideal R) (κ : DividedPowers I),
    ∃ δ : DividedPowers (I.map (algebraMap R A)), IsDPMorphism κ δ (algebraMap R A) := by
  intro R A _ _ _ _ I κ
  let x : I → A := fun i ↦ algebraMap R A i
  have hspan : Ideal.span (Set.range x) = I.map (algebraMap R A) := by
    rw [Ideal.map]; congr 1; ext b; simp [x]
  obtain ⟨γ, hγ, hγx⟩ := GlobalTheory.T.exists_isPreDividedPowers_of_generators A I x (fun i n ↦ algebraMap R A (κ.dpow n i))
    (fun i ↦ by simp [κ.dpow_zero i.2]) (fun i ↦ by simp [x, κ.dpow_one i.2])
    (fun i n hn ↦ Ideal.subset_span ⟨⟨κ.dpow n i, κ.dpow_mem hn i.2⟩, rfl⟩)
    (fun i m n ↦ by rw [← map_mul, κ.mul_dpow i.2, map_mul, map_natCast])
    (prod_expS_eq_one κ)
  rw [hspan] at hγ
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.exists_dividedPowers_of_comp_on_generators A _ γ (Set.range x) hγ hspan.symm (by
    rintro _ ⟨i, rfl⟩ m n hn
    rw [hγx, show algebraMap R A (κ.dpow n i) = x ⟨κ.dpow n i, κ.dpow_mem hn i.2⟩ from rfl, hγx]
    simp only [κ.dpow_comp hn i.2, map_mul, map_natCast]
    rw [← hγx])
  exact ⟨δ, ⟨le_rfl, fun a ha ↦ by rw [hδ]; exact hγx ⟨a, ha⟩ _⟩⟩

end GlobalTheory.DPFlat
end
end

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isDPMorphism_of_flat_algebra : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A] (I : Ideal R) (κ : DividedPowers I), ∃ δ : DividedPowers (I.map (algebraMap R A)), IsDPMorphism κ δ (algebraMap R A) := by
  atlas_forward_decl GlobalTheory.DPFlat.exists_isDPMorphism_of_flat
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.SmoothLift.LiftEx

theorem isPDNilpotent_map {R A : Type} [CommRing R] [CommRing A] {I : Ideal R} {κ : DividedPowers I} (f : R →+* A)
    {δ : DividedPowers (I.map f)} (h : IsDPMorphism κ δ f) (hκ : IsNilDP κ) : IsNilDP δ := by
  obtain ⟨N, hN⟩ := (isDPNilpotent_iff_exists_isLevel κ).1 hκ
  refine (isDPNilpotent_iff_exists_isLevel δ).2 ⟨N, ?_⟩
  have := fil_le_map_fil R I κ A _ δ f h rfl N
  rw [show fil κ N = ⊥ from hN, Ideal.map_bot] at this
  exact le_bot_iff.1 this

theorem isDPMorphism_algHom {R A A' : Type} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
    {I : Ideal R} {κ : DividedPowers I} {δ : DividedPowers (I.map (algebraMap R A))}
    {δ' : DividedPowers (I.map (algebraMap R A'))} (h : IsDPMorphism κ δ (algebraMap R A))
    (h' : IsDPMorphism κ δ' (algebraMap R A')) (φ : A →ₐ[R] A') : IsDPMorphism δ δ' (φ : A →+* A') := by
  refine IsDPMorphism.on_span δ δ' (S := algebraMap R A '' I) rfl ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    rw [RingHom.coe_coe, φ.commutes]
    exact Ideal.mem_map_of_mem _ ha
  · rintro n _ ⟨a, ha, rfl⟩
    rw [h.2 a ha, RingHom.coe_coe, φ.commutes, φ.commutes, h'.2 a ha]

abbrev ext (D : Data) (U : D.X.affineOpens) : Ideal (Sec D.s U.1) := D.I.map (algebraMap D.R (Sec D.s U.1))

theorem exists_pt (D : Data) (U : D.X.affineOpens) : ∃ x : Sp (Sec D.s U.1 ⧸ ext D U) ⟶ D.X₀,
    x ≫ D.i = spMap (Ideal.Quotient.mk (ext D U)) ≫ affPt D.s U ∧
    x ≫ D.t = spMap ((Ideal.Quotient.mk (ext D U)).comp (algebraMap D.R (Sec D.s U.1))) := by
  obtain ⟨s₀, hpb, ht⟩ := D.red
  let q : D.R ⧸ D.I →+* Sec D.s U.1 ⧸ ext D U :=
    Ideal.quotientMap (ext D U) (algebraMap D.R (Sec D.s U.1)) Ideal.le_comap_map
  have hq : spMap q ≫ spMap (Ideal.Quotient.mk D.I) =
      spMap ((Ideal.Quotient.mk (ext D U)).comp (algebraMap D.R (Sec D.s U.1))) := by
    rw [← Cris.spMap_comp]; rfl
  refine ⟨hpb.lift (spMap (Ideal.Quotient.mk (ext D U)) ≫ affPt D.s U) (spMap q) ?_, hpb.lift_fst _ _ _, ?_⟩
  · rw [hq, Category.assoc, affPt_w, Cris.spMap_comp]
  · rw [ht, ← Category.assoc, hpb.lift_snd, hq]

theorem exists_dp (D : Data) (U : D.X.affineOpens) :
    ∃ δ : DividedPowers (ext D U), IsDPMorphism D.κ δ (algebraMap D.R (Sec D.s U.1)) := by
  haveI := D.sec_smooth U
  exact GlobalTheory.T.exists_isDPMorphism_of_flat_algebra D.R (Sec D.s U.1) D.I D.κ

theorem nonempty_lift : ∀ D : Data, Nonempty (Lift D) := by
  intro D
  choose δ hδ using exists_dp D
  choose x hx hw using exists_pt D
  haveI := D.mono_i
  let T : D.X.affineOpens → Thick D.κ D.t := fun U ↦
    { B := Sec D.s U.1
      J := ext D U
      δ := δ U
      nil := isPDNilpotent_map _ (hδ U) D.nil
      dp := hδ U
      B₀ := Sec D.s U.1 ⧸ ext D U
      π := Ideal.Quotient.mk _
      surj := Ideal.Quotient.mk_surjective
      ker := fun _ ↦ Ideal.Quotient.eq_zero_iff_mem
      x := x U
      w := hw U }
  let m : ∀ {U V : D.X.affineOpens}, V.1 ≤ U.1 → (T U ⟶ T V) := fun {U V} h ↦
    { φ := Sec.res D.s h
      φ₀ := Ideal.quotientMap (ext D V) (Sec.res D.s h : Sec D.s U.1 →+* Sec D.s V.1)
        (Ideal.map_le_iff_le_comap.1 (isDPMorphism_algHom (hδ U) (hδ V) (Sec.res D.s h)).1)
      comm := fun _ ↦ rfl
      dp := isDPMorphism_algHom (hδ U) (hδ V) (Sec.res D.s h)
      pt := by
        rw [← cancel_mono D.i, Category.assoc]
        change spMap _ ≫ x U ≫ D.i = x V ≫ D.i
        rw [hx, hx, ← affPt_res D.s h, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
        rfl }
  refine ⟨{ L := { obj := fun U ↦ T U.unop
                   map := fun a ↦ m (leOfHom a.unop)
                   map_id := fun U ↦ Thick.hom_ext fun b ↦ mp_id (OAff D.s) U b
                   map_comp := fun a b ↦ Thick.hom_ext fun c ↦ mp_comp (OAff D.s) a b c }
            e := fun _ ↦ AlgEquiv.refl
            nat := fun _ _ ↦ rfl
            gen := fun _ ↦ rfl
            pt := fun U ↦ (hx U.unop).symm
            mem := fun U ↦ ?_ }⟩
  change ⊤ ≤ (x U.unop ≫ D.i) ⁻¹ᵁ U.unop.1
  rw [hx, Scheme.Hom.comp_preimage]
  have : affPt D.s U.unop ⁻¹ᵁ U.unop.1 = ⊤ := U.unop.2.fromSpec_preimage_self
  rw [this]
  exact le_rfl

end GlobalTheory.SmoothLift.LiftEx
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_smoothLiftAffineThickenings : ∀ D : Data, Nonempty (Lift D) := by
  atlas_forward_decl GlobalTheory.SmoothLift.LiftEx.nonempty_lift
end

section
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

section Ring

variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B] {J : Ideal B} {δ : DividedPowers J}

theorem divPowerCompatFunctionDifferential_smul (r : R) (b : B) : kd0 R δ (r • b) = r • kd0 R δ b := by
  rw [divPowerCompatFunctionDifferential_apply, divPowerCompatFunctionDifferential_apply, Derivation.map_smul, Submodule.Quotient.mk_smul]

theorem divPowerCompatOneFormDerivative_smul (r : R) (x : K1 R δ) : kd1 R δ (r • x) = r • kd1 R δ x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, divPowerCompatOneFormDerivative_mk, divPowerCompatOneFormDerivative_mk, map_smul, Submodule.Quotient.mk_smul]

theorem divPowerCompatTwoFormDerivative_smul (r : R) (x : K R δ 2) : kd2 R δ (r • x) = r • kd2 R δ x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, divPowerCompatTwoFormDerivative_mk, divPowerCompatTwoFormDerivative_mk, map_smul, Submodule.Quotient.mk_smul]

variable {R' B' : Type} [CommRing R'] [CommRing B'] [Algebra R' B'] {J' : Ideal B'} {δ' : DividedPowers J'}
  {σ : R →+* R'} {α : B →+* B'} (h : SemiHom σ α) (hd : IsDPMorphism δ δ' α)

theorem divPowerCompatOneFormMap_smul (r : R) (x : K1 R δ) : km1 h hd (r • x) = σ r • km1 h hd x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, divPowerCompatOneFormMap_mk, divPowerCompatOneFormMap_mk, map_smulₛₗ, Submodule.Quotient.mk_smul]

theorem km_smul (j : ℕ) (r : R) (x : K R δ j) : km h hd j (r • x) = σ r • km h hd j x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, km_mk, km_mk, map_smulₛₗ, Submodule.Quotient.mk_smul]

end Ring

section Site

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}} {κ : DividedPowers I} {t : X ⟶ Sp R}

theorem crystallineCompatibleFormsComplex_functionMap_smul {T T' : Thick κ t} (φ : T ⟶ T') (r : R) (x : (KK κ t).M0.obj T) :
    (KK κ t).M0.map φ (r • x) = r • (KK κ t).M0.map φ x := map_smul (mp (O κ t) φ) r x

theorem crystallineCompatibleFormsComplex_oneFormMap_smul {T T' : Thick κ t} (φ : T ⟶ T') (r : R) (x : (KK κ t).M1.obj T) :
    (KK κ t).M1.map φ (r • x) = r • (KK κ t).M1.map φ x := divPowerCompatOneFormMap_smul (SemiHom.of_algHom φ.φ) φ.dp r x

theorem crystallineCompatibleFormsComplex_twoFormMap_smul {T T' : Thick κ t} (φ : T ⟶ T') (r : R) (x : (KK κ t).M2.obj T) :
    (KK κ t).M2.map φ (r • x) = r • (KK κ t).M2.map φ x := km_smul (SemiHom.of_algHom φ.φ) φ.dp 2 r x

theorem crystallineCompatibleFormsComplex_functionDifferential_smul (T : Thick κ t) (r : R) (x : (KK κ t).M0.obj T) :
    (KK κ t).d0 T (r • x) = r • (KK κ t).d0 T x := divPowerCompatFunctionDifferential_smul r x

theorem crystallineCompatibleFormsComplex_oneFormDifferential_smul (T : Thick κ t) (r : R) (x : (KK κ t).M1.obj T) :
    (KK κ t).d1 T (r • x) = r • (KK κ t).d1 T x := divPowerCompatOneFormDerivative_smul r x

theorem crystallineCompatibleFormsComplex_twoFormDifferential_smul (T : Thick κ t) (r : R) (x : (KK κ t).M2.obj T) :
    (KK κ t).d2 T (r • x) = r • (KK κ t).d2 T x := divPowerCompatTwoFormDerivative_smul r x

theorem crystallineCompatibleFormsComplex_totalDifferentialOne_smul (r : R) (c : (KK κ t).T1) : (KK κ t).D1 (r • c) = r • (KK κ t).D1 c := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext T T' T'' φ ψ
    show (KK κ t).M0.map ψ (r • c.1 T T' φ) - r • c.1 T T'' (φ ≫ ψ) + r • c.1 T' T'' ψ =
      r • ((KK κ t).M0.map ψ (c.1 T T' φ) - c.1 T T'' (φ ≫ ψ) + c.1 T' T'' ψ)
    rw [crystallineCompatibleFormsComplex_functionMap_smul, smul_add, smul_sub]
  · funext T T' φ
    show r • c.2 T' - (KK κ t).M1.map φ (r • c.2 T) - (KK κ t).d0 T' (r • c.1 T T' φ) =
      r • (c.2 T' - (KK κ t).M1.map φ (c.2 T) - (KK κ t).d0 T' (c.1 T T' φ))
    rw [crystallineCompatibleFormsComplex_oneFormMap_smul, crystallineCompatibleFormsComplex_functionDifferential_smul, smul_sub, smul_sub]
  · funext T
    exact crystallineCompatibleFormsComplex_oneFormDifferential_smul T r (c.2 T)

theorem crystallineCompatibleFormsComplex_cocyclesOne_smul_mem (r : R) {c : (KK κ t).T1} (hc : c ∈ (KK κ t).Z1) : r • c ∈ (KK κ t).Z1 := by
  have h0 : (KK κ t).D1 c = 0 := hc
  show (KK κ t).D1 (r • c) = 0
  rw [crystallineCompatibleFormsComplex_totalDifferentialOne_smul, h0, smul_zero]

theorem crystallineCompatibleFormsComplex_cocyclesTwo_smul_mem (r : R) {c : (KK κ t).T2} (hc : c ∈ (KK κ t).Z2) : r • c ∈ (KK κ t).Z2 := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  refine ⟨fun T T' T'' T''' φ ψ χ ↦ ?_, fun T T' T'' φ ψ ↦ ?_, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
  · show (KK κ t).M0.map χ (r • c.1 T T' T'' φ ψ) + r • c.1 T T'' T''' (φ ≫ ψ) χ =
      r • c.1 T T' T''' φ (ψ ≫ χ) + r • c.1 T' T'' T''' ψ χ
    rw [crystallineCompatibleFormsComplex_functionMap_smul, ← smul_add, ← smul_add, h1]
  · show r • c.2.1 T T'' (φ ≫ ψ) = (KK κ t).M1.map ψ (r • c.2.1 T T' φ) + r • c.2.1 T' T'' ψ +
      (KK κ t).d0 T'' (r • c.1 T T' T'' φ ψ)
    rw [crystallineCompatibleFormsComplex_oneFormMap_smul, crystallineCompatibleFormsComplex_functionDifferential_smul, ← smul_add, ← smul_add, h2]
  · show r • c.2.2 T' = (KK κ t).M2.map φ (r • c.2.2 T) + (KK κ t).d1 T' (r • c.2.1 T T' φ)
    rw [crystallineCompatibleFormsComplex_twoFormMap_smul, crystallineCompatibleFormsComplex_oneFormDifferential_smul, ← smul_add, h3]
  · show (KK κ t).d2 T (r • c.2.2 T) = 0
    rw [crystallineCompatibleFormsComplex_twoFormDifferential_smul, h4, smul_zero]

end Site

theorem rel_add_smul : ∀ (D : Data) (Λ : Lift D),
    (∀ a b h h', Λ.Rel1 a h → Λ.Rel1 b h' → Λ.Rel1 (a + b) (h + h')) ∧
    (∀ (r : D.R) a h, Λ.Rel1 a h → Λ.Rel1 (r • a) (r • h)) ∧
    (∀ a b h h', Λ.Rel2 a h → Λ.Rel2 b h' → Λ.Rel2 (a + b) (h + h')) ∧
    ∀ (r : D.R) a h, Λ.Rel2 a h → Λ.Rel2 (r • a) (r • h) := by
  intro D Λ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro a b h h' ⟨k, f, w, hf, hw, hk, hr⟩ ⟨k', f', w', hf', hw', hk', hr'⟩
    refine ⟨k + k', f + f', w + w', by rw [map_add, hf, hf'], by rw [map_add, hw, hw'], ?_, ?_⟩
    · show k.1.1 + k'.1.1 = f.1 + f'.1
      rw [hk, hk']
    · refine ⟨fun U V c ↦ (congrArg₂ (· + ·) (hr.1 U V c) (hr'.1 U V c)).trans (map_add (Λ.e V) _ _).symm,
        fun U ↦ (congrArg₂ (· + ·) (hr.2 U) (hr'.2 U)).trans ?_⟩
      show _ = Submodule.Quotient.mk ((Λ.semi U).m1 (w.1.2 U + w'.1.2 U))
      rw [map_add, Submodule.Quotient.mk_add]
  · rintro r a h ⟨k, f, w, hf, hw, hk, hr⟩
    refine ⟨⟨r • k.1, crystallineCompatibleFormsComplex_cocyclesOne_smul_mem r k.2⟩, r • f, r • w, by rw [map_smul, hf], by rw [map_smul, hw], ?_, ?_⟩
    · show r • k.1.1 = r • f.1
      rw [hk]
    · refine ⟨fun U V c ↦ (congrArg (r • ·) (hr.1 U V c)).trans (map_smul (Λ.e V) r _).symm,
        fun U ↦ (congrArg (r • ·) (hr.2 U)).trans ?_⟩
      show _ = Submodule.Quotient.mk ((Λ.semi U).m1 (r • w.1.2 U))
      rw [map_smulₛₗ, RingHom.id_apply, Submodule.Quotient.mk_smul]
  · rintro a b h h' ⟨k, f, w, hf, hw, hk, hr⟩ ⟨k', f', w', hf', hw', hk', hr'⟩
    refine ⟨k + k', f + f', w + w', by rw [map_add, hf, hf'], by rw [map_add, hw, hw'], ?_, ?_⟩
    · show k.1.1 + k'.1.1 = f.1 + f'.1
      rw [hk, hk']
    · refine ⟨fun U V W c d ↦ (congrArg₂ (· + ·) (hr.1 U V W c d) (hr'.1 U V W c d)).trans (map_add (Λ.e W) _ _).symm,
        fun U V c ↦ (congrArg₂ (· + ·) (hr.2.1 U V c) (hr'.2.1 U V c)).trans ?_,
        fun U ↦ (congrArg₂ (· + ·) (hr.2.2 U) (hr'.2.2 U)).trans ?_⟩
      · show _ = Submodule.Quotient.mk ((Λ.semi V).m1 (w.1.2.1 U V c + w'.1.2.1 U V c))
        rw [map_add, Submodule.Quotient.mk_add]
      · show _ = Submodule.Quotient.mk ((Λ.semi U).mOm 2 (w.1.2.2 U + w'.1.2.2 U))
        rw [map_add, Submodule.Quotient.mk_add]
  · rintro r a h ⟨k, f, w, hf, hw, hk, hr⟩
    refine ⟨⟨r • k.1, crystallineCompatibleFormsComplex_cocyclesTwo_smul_mem r k.2⟩, r • f, r • w, by rw [map_smul, hf], by rw [map_smul, hw], ?_, ?_⟩
    · show r • k.1.1 = r • f.1
      rw [hk]
    · refine ⟨fun U V W c d ↦ (congrArg (r • ·) (hr.1 U V W c d)).trans (map_smul (Λ.e W) r _).symm,
        fun U V c ↦ (congrArg (r • ·) (hr.2.1 U V c)).trans ?_,
        fun U ↦ (congrArg (r • ·) (hr.2.2 U)).trans ?_⟩
      · show _ = Submodule.Quotient.mk ((Λ.semi V).m1 (r • w.1.2.1 U V c))
        rw [map_smulₛₗ, RingHom.id_apply, Submodule.Quotient.mk_smul]
      · show _ = Submodule.Quotient.mk ((Λ.semi U).mOm 2 (r • w.1.2.2 U))
        rw [map_smulₛₗ, RingHom.id_apply, Submodule.Quotient.mk_smul]

end GlobalTheory.PDForm
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothLift_comparisonRelations_add_smul : ∀ (D : Data) (Λ : Lift D), (∀ a b h h', Λ.Rel1 a h → Λ.Rel1 b h' → Λ.Rel1 (a + b) (h + h')) ∧ (∀ (r : D.R) a h, Λ.Rel1 a h → Λ.Rel1 (r • a) (r • h)) ∧ (∀ a b h h', Λ.Rel2 a h → Λ.Rel2 b h' → Λ.Rel2 (a + b) (h + h')) ∧ ∀ (r : D.R) a h, Λ.Rel2 a h → Λ.Rel2 (r • a) (r • h) := by
  atlas_forward_decl GlobalTheory.PDForm.rel_add_smul
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

section Ring

variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B] {J : Ideal B} (δ : DividedPowers J)

theorem sgn_mem_rel_of_mem {x : DR R B} (hx : x ∈ rel R δ) : sgn x ∈ rel R δ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, a, ha, rfl⟩ := hx
    rw [sgn_ι]; exact neg_mem (Ideal.subset_span ⟨n, a, ha, rfl⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ ih => rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ ih

theorem mul_ι_mem_rel {x : DR R B} (hx : x ∈ rel R δ) (ω : Ω[B⁄R]) : x * ι1 ω ∈ rel R δ := by
  have h := ι_mul ω (sgn x)
  rw [sgn_sgn] at h
  rw [← h]; exact Ideal.mul_mem_left _ _ (sgn_mem_rel_of_mem δ hx)

theorem mem_divPowerCompatFormRelSubmodule_two_iff {x : Om R B 2} : x ∈ N R δ 2 ↔ (x : DR R B) ∈ rel R δ := Iff.rfl

theorem wedge_mem_N {x y : Ω[B⁄R]} (h : x ∈ N1 R δ ∨ y ∈ N1 R δ) : wedge R B x y ∈ N R δ 2 := by
  rw [mem_divPowerCompatFormRelSubmodule_two_iff, coe_wedge]
  rcases h with h | h
  · exact mul_ι_mem_rel δ h y
  · exact Ideal.mul_mem_left _ _ h

variable (R) in

def kwedge : K1 R δ →ₗ[B] K1 R δ →ₗ[B] K R δ 2 :=
  LinearMap.liftQ₂ _ _ ((wedge R B).compr₂ (N R δ 2).mkQ)
    (fun x hx ↦ LinearMap.ext fun y ↦ (Submodule.Quotient.mk_eq_zero _).2 (wedge_mem_N δ (Or.inl hx)))
    (fun y hy ↦ LinearMap.ext fun x ↦ (Submodule.Quotient.mk_eq_zero _).2 (wedge_mem_N δ (Or.inr hy)))

theorem kwedge_mk (x y : Ω[B⁄R]) :
    kwedge R δ (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = Submodule.Quotient.mk (wedge R B x y) := rfl

end Ring

section Ring2

variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B] {J : Ideal B} (δ : DividedPowers J)

theorem kwedge_swap (x y : K1 R δ) : kwedge R δ x y = -kwedge R δ y x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [kwedge_mk, kwedge_mk, wedge_swap, Submodule.Quotient.mk_neg]

theorem divPowerCompatFunctionDifferential_mul (a b : B) : kd0 R δ (a * b) = a • kd0 R δ b + b • kd0 R δ a := by
  rw [divPowerCompatFunctionDifferential_apply, divPowerCompatFunctionDifferential_apply, divPowerCompatFunctionDifferential_apply, Derivation.leibniz, Submodule.Quotient.mk_add,
    Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul]

theorem divPowerCompatOneFormDerivative_smul_eq_wedge_add (b : B) (x : K1 R δ) : kd1 R δ (b • x) = kwedge R δ (kd0 R δ b) x + b • kd1 R δ x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, divPowerCompatOneFormDerivative_mk, divPowerCompatOneFormDerivative_mk, divPowerCompatFunctionDifferential_apply, kwedge_mk, dOne_smul, Submodule.Quotient.mk_add,
    Submodule.Quotient.mk_smul]

theorem divPowerCompatTwoFormDerivative_wedge_of_closed {x y : K1 R δ} (hx : kd1 R δ x = 0) (hy : kd1 R δ y = 0) : kd2 R δ (kwedge R δ x y) = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [divPowerCompatOneFormDerivative_mk, Submodule.Quotient.mk_eq_zero, mem_divPowerCompatFormRelSubmodule_two_iff, coe_dOne] at hx hy
  rw [kwedge_mk, divPowerCompatTwoFormDerivative_mk, Submodule.Quotient.mk_eq_zero]
  change dDR R B (ι1 x * ι1 y) ∈ rel R δ
  rw [dDR_mul, sgn_ι, neg_mul]
  exact add_mem (neg_mem (Ideal.mul_mem_left _ _ hy)) (mul_ι_mem_rel δ hx y)

variable {δ} {R' B' : Type} [CommRing R'] [CommRing B'] [Algebra R' B'] {J' : Ideal B'} {δ' : DividedPowers J'}
  {σ : R →+* R'} {α : B →+* B'} (h : SemiHom σ α) (hd : IsDPMorphism δ δ' α)

theorem divPowerCompatOneFormMap_smul_function (b : B) (x : K1 R δ) : km1 h hd (b • x) = α b • km1 h hd x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, divPowerCompatOneFormMap_mk, divPowerCompatOneFormMap_mk, h.oneFormMap_smul_semilinear, Submodule.Quotient.mk_smul]

theorem km_kwedge (x y : K1 R δ) : km h hd 2 (kwedge R δ x y) = kwedge R' δ' (km1 h hd x) (km1 h hd y) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [kwedge_mk, km_mk, divPowerCompatOneFormMap_mk, divPowerCompatOneFormMap_mk, kwedge_mk, h.mOm_wedge]

end Ring2

section Site

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}} {κ : DividedPowers I} {t : X ⟶ Sp R}

def cupK (a b : (KK κ t).T1) : (KK κ t).T2 :=
  (fun _ T' T'' φ ψ ↦ (show T''.B from (KK κ t).M0.map ψ (a.1 _ T' φ)) * (show T''.B from b.1 T' T'' ψ),
    fun T T' φ ↦ (show T'.B from a.1 T T' φ) • b.2 T' - (show T'.B from b.1 T T' φ) • (KK κ t).M1.map φ (a.2 T),
    fun T ↦ kwedge R T.δ (a.2 T) (b.2 T))

theorem crystallineCompatibleFormsComplex_cocycleOne_components (k : (KK κ t).Z1) :
    (∀ {T T' T'' : Thick κ t} (φ : T ⟶ T') (ψ : T' ⟶ T''),
      (k.1.1 T T'' (φ ≫ ψ) : T''.B) = ψ.φ (k.1.1 T T' φ) + k.1.1 T' T'' ψ) ∧
    (∀ {T T' : Thick κ t} (φ : T ⟶ T'), k.1.2 T' = (KK κ t).M1.map φ (k.1.2 T) + kd0 R T'.δ (k.1.1 T T' φ)) ∧
    ∀ T : Thick κ t, kd1 R T.δ (k.1.2 T) = 0 := by
  have h : (KK κ t).D1 k.1 = 0 := k.2
  refine ⟨fun {T T' T''} φ ψ ↦ ?_, fun {T T'} φ ↦ ?_, fun T ↦ ?_⟩
  · have := congrFun (congrFun (congrFun (congrFun (congrFun (congrArg Prod.fst h) T) T') T'') φ) ψ
    change ψ.φ (k.1.1 T T' φ) - k.1.1 T T'' (φ ≫ ψ) + k.1.1 T' T'' ψ = 0 at this
    linear_combination -this
  · have := congrFun (congrFun (congrFun (congrArg (fun c ↦ c.2.1) h) T) T') φ
    change k.1.2 T' - (KK κ t).M1.map φ (k.1.2 T) - kd0 R T'.δ (k.1.1 T T' φ) = 0 at this
    rw [sub_sub, sub_eq_zero] at this
    exact this
  · exact congrFun (congrArg (fun c ↦ c.2.2) h) T

end Site

section Site2

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}} {κ : DividedPowers I} {t : X ⟶ Sp R}

theorem cupK_mem (a b : (KK κ t).Z1) : cupK a.1 b.1 ∈ (KK κ t).Z2 := by
  obtain ⟨ha1, ha2, ha3⟩ := crystallineCompatibleFormsComplex_cocycleOne_components a
  obtain ⟨hb1, hb2, hb3⟩ := crystallineCompatibleFormsComplex_cocycleOne_components b
  refine ⟨fun T T' T'' T''' φ ψ χ ↦ ?_, fun T T' T'' φ ψ ↦ ?_, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
  · change χ.φ (ψ.φ (a.1.1 T T' φ) * b.1.1 T' T'' ψ) + χ.φ (a.1.1 T T'' (φ ≫ ψ)) * b.1.1 T'' T''' χ =
      (ψ ≫ χ).φ (a.1.1 T T' φ) * b.1.1 T' T''' (ψ ≫ χ) + χ.φ (a.1.1 T' T'' ψ) * b.1.1 T'' T''' χ
    rw [ha1 φ ψ, hb1 ψ χ, Thick.comp_φ, map_mul, map_add]
    ring
  · have hs : ∀ {T T' : Thick κ t} (φ : T ⟶ T') (r : T.B) (x : K1 R T.δ),
        (KK κ t).M1.map φ (r • x) = φ.φ r • (KK κ t).M1.map φ x := fun φ r x ↦ divPowerCompatOneFormMap_smul_function (SemiHom.of_algHom φ.φ) φ.dp r x
    have hd : ∀ {T T' : Thick κ t} (φ : T ⟶ T') (r : T.B),
        (KK κ t).M1.map φ (kd0 R T.δ r) = kd0 R T'.δ (φ.φ r) := fun φ r ↦ divPowerCompatOneFormMap_functionDifferential (SemiHom.of_algHom φ.φ) φ.dp r
    change (a.1.1 T T'' (φ ≫ ψ) : T''.B) • b.1.2 T'' - (b.1.1 T T'' (φ ≫ ψ) : T''.B) • (KK κ t).M1.map (φ ≫ ψ) (a.1.2 T) =
      (KK κ t).M1.map ψ ((a.1.1 T T' φ : T'.B) • b.1.2 T' - (b.1.1 T T' φ : T'.B) • (KK κ t).M1.map φ (a.1.2 T)) +
      ((a.1.1 T' T'' ψ : T''.B) • b.1.2 T'' - (b.1.1 T' T'' ψ : T''.B) • (KK κ t).M1.map ψ (a.1.2 T')) +
      kd0 R T''.δ (ψ.φ (a.1.1 T T' φ) * b.1.1 T' T'' ψ)
    rw [ha1 φ ψ, hb1 φ ψ, (KK κ t).M1.map_comp, hb2 ψ, ha2 φ]
    simp only [map_add, map_sub, hs, hd, divPowerCompatFunctionDifferential_mul, smul_add, smul_sub, add_smul]
    module
  · have hd1 : kd1 R T'.δ ((KK κ t).M1.map φ (a.1.2 T)) = 0 :=
      ((KK κ t).diffOne_natural φ _).trans (by rw [show (KK κ t).d1 T (a.1.2 T) = 0 from ha3 T, map_zero])
    change kwedge R T'.δ (a.1.2 T') (b.1.2 T') = (KK κ t).M2.map φ (kwedge R T.δ (a.1.2 T) (b.1.2 T)) +
      kd1 R T'.δ ((a.1.1 T T' φ : T'.B) • b.1.2 T' - (b.1.1 T T' φ : T'.B) • (KK κ t).M1.map φ (a.1.2 T))
    rw [map_sub, divPowerCompatOneFormDerivative_smul_eq_wedge_add, divPowerCompatOneFormDerivative_smul_eq_wedge_add, hb3 T', hd1, smul_zero, smul_zero, add_zero, add_zero]
    change _ = km (SemiHom.of_algHom φ.φ) φ.dp 2 _ + _
    rw [km_kwedge]
    change kwedge R T'.δ (a.1.2 T') (b.1.2 T') = kwedge R T'.δ ((KK κ t).M1.map φ (a.1.2 T)) ((KK κ t).M1.map φ (b.1.2 T)) + _
    rw [ha2 φ, hb2 φ]
    simp only [map_add, LinearMap.add_apply]
    rw [kwedge_swap T'.δ (kd0 R T'.δ (b.1.1 T T' φ))]
    abel
  · exact divPowerCompatTwoFormDerivative_wedge_of_closed T.δ (ha3 T) (hb3 T)

end Site2

section Main

variable {D : Data} (Λ : Lift D)

theorem Lift.lift_res2_cup {k k' : (KK D.κ D.t).T1} {w w' : Tot1 (OAff D.s)}
    (hk : Λ.Res1 (((KK D.κ D.t).resMap Λ.L).p1 k) w) (hk' : Λ.Res1 (((KK D.κ D.t).resMap Λ.L).p1 k') w') :
    Λ.Res2 (((KK D.κ D.t).resMap Λ.L).p2 (cupK k k')) (cupTot (OAff D.s) w w') := by
  have e1 : ∀ U V a, (k.1 _ _ (Λ.L.map a) : (Λ.L.obj V).B) = Λ.e V (w.1 U V a) := hk.1
  have e1' : ∀ U V a, (k'.1 _ _ (Λ.L.map a) : (Λ.L.obj V).B) = Λ.e V (w'.1 U V a) := hk'.1
  have e2 : ∀ U, k.2 (Λ.L.obj U) = Submodule.Quotient.mk ((Λ.semi U).m1 (w.2 U)) := hk.2
  have e2' : ∀ U, k'.2 (Λ.L.obj U) = Submodule.Quotient.mk ((Λ.semi U).m1 (w'.2 U)) := hk'.2
  refine ⟨fun U V W a b ↦ ?_, fun U V a ↦ ?_, fun U ↦ ?_⟩
  · change (Λ.L.map b).φ (k.1 _ _ (Λ.L.map a)) * (k'.1 _ _ (Λ.L.map b) : (Λ.L.obj W).B) =
      Λ.e W (mp (OAff D.s) b (w.1 U V a) * w'.1 V W b)
    rw [e1, e1', map_mul, Λ.nat]
  · have key : ∀ x, (SemiHom.of_algHom (Λ.L.map a).φ).m1 ((Λ.semi U).m1 x) = (Λ.semi V).m1 (p1 (OAff D.s) a x) :=
      fun x ↦ (SemiHom.oneFormMap_comp_oneFormMap (Λ.semi U) (SemiHom.of_algHom _) ((semiHom_mp (OAff D.s) a).comp (Λ.semi V))
        (fun b ↦ (Λ.nat a b).symm) x).trans
        (SemiHom.oneFormMap_comp_oneFormMap (semiHom_mp (OAff D.s) a) (Λ.semi V) ((semiHom_mp (OAff D.s) a).comp (Λ.semi V))
          (fun _ ↦ rfl) x).symm
    change (k.1 _ _ (Λ.L.map a) : (Λ.L.obj V).B) • k'.2 (Λ.L.obj V) -
        (k'.1 _ _ (Λ.L.map a) : (Λ.L.obj V).B) • km1 (SemiHom.of_algHom (Λ.L.map a).φ) (Λ.L.map a).dp (k.2 (Λ.L.obj U)) =
      Submodule.Quotient.mk ((Λ.semi V).m1 (w.1 U V a • w'.2 V - w'.1 U V a • p1 (OAff D.s) a (w.2 U)))
    rw [e1, e1', e2' V, e2 U, divPowerCompatOneFormMap_mk, key, map_sub, SemiHom.oneFormMap_smul_semilinear, SemiHom.oneFormMap_smul_semilinear, Submodule.Quotient.mk_sub,
      Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul]
    rfl
  · change kwedge D.R (Λ.L.obj U).δ (k.2 (Λ.L.obj U)) (k'.2 (Λ.L.obj U)) =
      Submodule.Quotient.mk ((Λ.semi U).mOm 2 (wedge D.R _ (w.2 U) (w'.2 U)))
    rw [e2, e2', kwedge_mk, SemiHom.mOm_wedge]

theorem Lift.lift_rel2_cup : ∀ (D : Data) (Λ : Lift D) a b h h', Λ.Rel1 a h → Λ.Rel1 b h' →
    Λ.Rel2 (cup _ a b) (cupHH D.s h h') := by
  intro D Λ a b h h' ha hb
  obtain ⟨k, f, w, hf, hw, hkf, hr⟩ := ha
  obtain ⟨k', g, w', hg, hw', hkg, hr'⟩ := hb
  refine ⟨⟨cupK k.1 k'.1, cupK_mem k k'⟩, cupZ _ f g, cupZZ _ w w', ?_, ?_, ?_, Λ.lift_res2_cup hr hr'⟩
  · rw [← hf, ← hg]; rfl
  · rw [← hw, ← hw']; rfl
  · funext T T' T'' φ ψ
    change ψ.φ (k.1.1 T T' φ) * (k'.1.1 T' T'' ψ : T''.B) = ψ.φ (f.1 T T' φ) * g.1 T' T'' ψ
    rw [hkf, hkg]

end Main

end GlobalTheory.PDForm
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparison_relations_respect_cup : ∀ (D : Data) (Λ : Lift D) a b h h', Λ.Rel1 a h → Λ.Rel1 b h' → Λ.Rel2 (cup _ a b) (cupHH D.s h h') := by
  atlas_forward_decl GlobalTheory.PDForm.Lift.lift_rel2_cup
end

section
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem exists_lift_pair_hom (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X)
    (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀)
    (hi : φ₀ ≫ D.i = D'.i ≫ φ) (p : Pair φ) :
    ∃ θ : Λ.L.obj (Opposite.op p.1.2) ⟶ m.obj (Λ'.L.obj (Opposite.op p.1.1)),
      ∀ a, θ.φ (Λ.e (Opposite.op p.1.2) a) = Λ'.e (Opposite.op p.1.1) (CechDR.secPull D.s D'.s p a) := by
  let T' := Λ'.L.obj (Opposite.op p.1.1)
  let e' : Sec D'.s p.1.1.1 →+* T'.B := Λ'.e (Opposite.op p.1.1)
  let y₀ : Sec D.s p.1.2.1 →+* (m.obj T').B := e'.comp (CechDR.secPull D.s D'.s p)
  have hy : ∀ r : D.R, y₀ (algebraMap D.R _ r) = algebraMap D.R (m.obj T').B r := by
    intro r
    have h1 := semiHom_secPull hφ p r 1
    rw [map_one, ← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one] at h1
    change e' (CechDR.secPull D.s D'.s p (algebraMap D.R _ r)) = algebraMap D'.R T'.B (σ r)
    rw [h1]
    exact (Λ'.e (Opposite.op p.1.1)).commutes _
  let y : Sec D.s p.1.2.1 →ₐ[D.R] (m.obj T').B := { y₀ with commutes' := hy }
  refine ((GlobalTheory.T.hom_spec_points_levels D Λ).1 (Opposite.op p.1.2) (m.obj T') y).1 ?_
  change spMap ((T'.π.comp e').comp (CechDR.secPull D.s D'.s p)) ≫ affPt D.s p.1.2 = (T'.x ≫ φ₀) ≫ D.i
  rw [Cris.spMap_comp, Category.assoc, secPull_affPt, ← Category.assoc, Category.assoc T'.x, hi, ← Category.assoc]
  exact congrArg (· ≫ φ) (Λ'.pt (Opposite.op p.1.1))

end GlobalTheory.PDForm
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smoothLift_hom_affinePair : ∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀), φ₀ ≫ D.i = D'.i ≫ φ → ∀ p : Pair φ, ∃ θ : Λ.L.obj (Opposite.op p.1.2) ⟶ m.obj (Λ'.L.obj (Opposite.op p.1.1)), ∀ a, θ.φ (Λ.e (Opposite.op p.1.2) a) = Λ'.e (Opposite.op p.1.1) (secPull D.s D'.s p a) := by
  atlas_forward_decl GlobalTheory.PDForm.exists_lift_pair_hom
end

section
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem exists_lift_pair_natTrans (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R)
    (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ)
    (m : IsMor D.κ D.t D'.κ D'.t σ φ₀) (hi : φ₀ ≫ D.i = D'.i ≫ φ) :
    ∃ θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G, ∀ (p : (Pair φ)ᵒᵖ) a,
      (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) =
        Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a) := by
  choose θ hθ using GlobalTheory.T.exists_smoothLift_hom_affinePair D D' Λ Λ' σ φ φ₀ hφ m hi
  refine ⟨⟨fun p ↦ θ p.unop, fun p q a ↦ ?_⟩, fun p a ↦ hθ p.unop a⟩
  apply Thick.hom_ext
  intro b
  obtain ⟨x, rfl⟩ := (Λ.e (Opposite.op p.unop.1.2)).surjective b
  have h1 := Λ.nat ((pairSnd φ).map a) x
  have h2 := hθ q.unop (mp (OAff D.s) ((pairSnd φ).map a) x)
  have h3 := hθ p.unop x
  have h4 := Λ'.nat ((pairFst φ).map a) (GlobalTheory.CechDR.secPull D.s D'.s p.unop x)
  have h5 := (pairPull hφ).naturality a x
  exact ((congrArg (θ q.unop).φ h1.symm).trans h2).trans
    ((congrArg (Λ'.e (Opposite.op q.unop.1.1)) h5).trans
      (h4.trans (congrArg (Λ'.L.map ((pairFst φ).map a)).φ h3.symm)))

end GlobalTheory.PDForm
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_natTrans_lifts_over_affine_pairs : ∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀), φ₀ ≫ D.i = D'.i ≫ φ → ∃ θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G, ∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) = Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a) := by
  atlas_forward_decl GlobalTheory.PDForm.exists_lift_pair_natTrans
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem compatibleForms_cocycles_differ_by_coboundary : ∀ (R R' : Type) [CommRing R] [CommRing R'] (I : Ideal R) (I' : Ideal R') (κ : DividedPowers I) (κ' : DividedPowers I') (X X' : Scheme.{0}) (t : X ⟶ Sp R) (t' : X' ⟶ Sp R') (σ : R →+* R') (φ₀ : X' ⟶ X) (m : IsMor κ t κ' t' σ φ₀) (k : (KK κ t).Z1) (k' : (KK κ' t').Z1) (f : Z1 (O κ t)) (f' : Z1 (O κ' t')), k.1.1 = f.1 → k'.1.1 = f'.1 → H1.mk _ f' = m.pull1 (H1.mk _ f) → ∃ g, (KK κ' t').D0 g = (morMap m).p1 k.1 - k'.1 := by
  intro R R' _ _ I I' κ κ' X X' t t' σ φ₀ m k k' f f' hk hk' h
  have h' : H1.mk _ (m.coef.pullbackOneCocycle f) = H1.mk _ f' := h.symm
  obtain ⟨g, hg⟩ := H1.mk_eq_mk.1 h'
  have hinj := (GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res R' I' κ' X' t' X' (𝟙 X')).1.1.injective
  have hz : (morMap m).p1 k.1 - k'.1 ∈ (KK κ' t').Z1 :=
    sub_mem ((morMap m).z1 k).2 k'.2
  have h0 : (KK κ' t').fnMap.h1 (QuotientAddGroup.mk ⟨_, hz⟩ : (KK κ' t').H1) = 0 := by
    change (QuotientAddGroup.mk ((KK κ' t').fnMap.z1 ⟨_, hz⟩) : Cx.H1 _) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    refine ⟨g, ?_⟩
    refine Prod.ext ?_ ?_
    · funext T T' φ
      have e := congrFun (congrFun (congrFun hg T) T') φ
      have e1 := congrFun (congrFun (congrFun hk (m.obj T)) (m.obj T')) (m.functor.map φ)
      have e2 := congrFun (congrFun (congrFun hk' T) T') φ
      refine e.trans ?_
      exact congrArg₂ (fun u v : T'.B ↦ u - v) e1.symm e2.symm
    · funext T
      rfl
  have h1 := hinj (h0.trans (map_zero (KK κ' t').fnMap.h1).symm)
  rw [QuotientAddGroup.eq_zero_iff] at h1
  exact h1

end GlobalTheory.PDForm
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatibleFormsCocycles_degreeOne_differ_coboundary : ∀ (R R' : Type) [CommRing R] [CommRing R'] (I : Ideal R) (I' : Ideal R') (κ : DividedPowers I) (κ' : DividedPowers I') (X X' : Scheme.{0}) (t : X ⟶ Sp R) (t' : X' ⟶ Sp R') (σ : R →+* R') (φ₀ : X' ⟶ X) (m : IsMor κ t κ' t' σ φ₀) (k : (KK κ t).Z1) (k' : (KK κ' t').Z1) (f : Z1 (O κ t)) (f' : Z1 (O κ' t')), k.1.1 = f.1 → k'.1.1 = f'.1 → H1.mk _ f' = m.pull1 (H1.mk _ f) → ∃ g, (KK κ' t').D0 g = (morMap m).p1 k.1 - k'.1 := by
  atlas_forward_decl GlobalTheory.PDForm.compatibleForms_cocycles_differ_by_coboundary
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.ClsTwo

universe u

theorem cob_of_fn_cob {C : Type u} [Category.{0} C] (K : Cx C) (h : Function.Injective K.fnMap.h2)
    (z : K.T2) (hz : z ∈ K.Z2) (e : K.M0.c1)
    (he : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''),
      K.M0.map ψ (e T T' φ) - e T T'' (φ ≫ ψ) + e T' T'' ψ = z.1 T T' T'' φ ψ) :
    ∃ g, K.D1 g = z := by
  have h0 : K.fnMap.h2 (QuotientAddGroup.mk ⟨z, hz⟩) = 0 := by
    change (QuotientAddGroup.mk (K.fnMap.z2 ⟨z, hz⟩) : (Cx.single K.M0).H2) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    refine ⟨(e, 0), ?_⟩
    refine Prod.ext ?_ rfl
    funext T T' T'' φ ψ
    exact he T T' T'' φ ψ
  have h1 : (QuotientAddGroup.mk ⟨z, hz⟩ : K.H2) = 0 := h (h0.trans (map_zero _).symm)
  rw [QuotientAddGroup.eq_zero_iff] at h1
  exact h1

theorem cob_of_class_eq : ∀ (R R' : Type) [CommRing R] [CommRing R'] (I : Ideal R) (I' : Ideal R') (κ : DividedPowers I) (κ' : DividedPowers I') (X X' : Scheme.{0}) (t : X ⟶ Sp R) (t' : X' ⟶ Sp R') (σ : R →+* R') (φ₀ : X' ⟶ X) (m : IsMor κ t κ' t' σ φ₀) (k : (KK κ t).Z2) (k' : (KK κ' t').Z2) (f : Z2 (O κ t)) (f' : Z2 (O κ' t')), k.1.1 = f.1 → k'.1.1 = f'.1 → H2.mk _ f' = m.pull2 (H2.mk _ f) → ∃ g, (KK κ' t').D1 g = (morMap m).p2 k.1 - k'.1 := by
  intro R R' _ _ I I' κ κ' X X' t t' σ φ₀ m k k' f f' hk hk' h
  have h' : H2.mk _ (m.coef.pullbackTwoCocycle f) = H2.mk _ f' := h.symm
  obtain ⟨e, he⟩ := H2.mk_eq_mk.1 h'
  refine cob_of_fn_cob (KK κ' t') (GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res R' I' κ' X' t' X' (𝟙 X')).1.2.injective _
    (AddSubgroup.sub_mem _ ((morMap m).p2_mem_Z2_of_mem_Z2 k.2) k'.2) e ?_
  intro T T' T'' φ ψ
  have h1 := congrFun (congrFun (congrFun (congrFun (congrFun he T) T') T'') φ) ψ
  refine h1.trans ?_
  have h2 : (m.coef.pullbackTwoCocycle f).1 T T' T'' φ ψ = ((morMap m).p2 k.1).1 T T' T'' φ ψ :=
    (congrFun (congrFun (congrFun (congrFun (congrFun hk _) _) _) (m.functor.map φ)) (m.functor.map ψ)).symm
  have h3 := congrFun (congrFun (congrFun (congrFun (congrFun hk' T) T') T'') φ) ψ
  exact congrArg₂ (fun a b : (O κ' t').obj T'' ↦ a - b) h2 h3.symm

end GlobalTheory.PDForm.ClsTwo
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatibleFormsCocycles_degreeTwo_differ_coboundary : ∀ (R R' : Type) [CommRing R] [CommRing R'] (I : Ideal R) (I' : Ideal R') (κ : DividedPowers I) (κ' : DividedPowers I') (X X' : Scheme.{0}) (t : X ⟶ Sp R) (t' : X' ⟶ Sp R') (σ : R →+* R') (φ₀ : X' ⟶ X) (m : IsMor κ t κ' t' σ φ₀) (k : (KK κ t).Z2) (k' : (KK κ' t').Z2) (f : Z2 (O κ t)) (f' : Z2 (O κ' t')), k.1.1 = f.1 → k'.1.1 = f'.1 → H2.mk _ f' = m.pull2 (H2.mk _ f) → ∃ g, (KK κ' t').D1 g = (morMap m).p2 k.1 - k'.1 := by
  atlas_forward_decl GlobalTheory.PDForm.ClsTwo.cob_of_class_eq
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem kaehlerDifferential_map_commutative_pentagon {R₁ R₂ A₁ A₂ A₃ A₄ A₅ : Type} [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂]
    [CommRing A₃] [CommRing A₄] [CommRing A₅] [Algebra R₁ A₁] [Algebra R₁ A₂] [Algebra R₁ A₃] [Algebra R₂ A₄]
    [Algebra R₂ A₅] {σ₁ σ₂ : R₁ →+* R₁} {σ₃ σ₄ : R₁ →+* R₂} {σ₅ : R₂ →+* R₂} {a : A₁ →+* A₂} {b : A₂ →+* A₃}
    {c : A₃ →+* A₄} {d : A₁ →+* A₅} {e : A₅ →+* A₄} (ha : SemiHom σ₁ a) (hb : SemiHom σ₂ b) (hc : SemiHom σ₃ c)
    (hd : SemiHom σ₄ d) (he : SemiHom σ₅ e) (h : ∀ x, c (b (a x)) = e (d x)) (x : Ω[A₁⁄R₁]) :
    hc.m1 (hb.m1 (ha.m1 x)) = he.m1 (hd.m1 x) := by
  rw [SemiHom.oneFormMap_comp_oneFormMap _ _ (hd.comp he) (fun _ ↦ rfl), SemiHom.oneFormMap_comp_oneFormMap _ _ (ha.comp hb) (fun _ ↦ rfl)]
  exact SemiHom.oneFormMap_comp_oneFormMap _ _ (hd.comp he) h x

theorem isPull1_of_pair_coboundary : ∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀) (θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G), (∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) = Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a)) → ∀ (k : (KK D.κ D.t).Z1) (k' : (KK D'.κ D'.t).Z1) (w : cechDeRhamTotalCocyclesOne (OAff D.s)) (w' : cechDeRhamTotalCocyclesOne (OAff D'.s)), Λ.Res1 (((KK D.κ D.t).resMap Λ.L).p1 k.1) w.1 → Λ'.Res1 (((KK D'.κ D'.t).resMap Λ'.L).p1 k'.1) w'.1 → ∀ g, ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).D0 g = ((pairB Λ' φ m).pre θ).p1 k.1 - ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p1 k'.1 → IsPull1 hφ (Hyp1.mk _ w) (Hyp1.mk _ w') := by
  intro D D' Λ Λ' σ φ φ₀ hφ m θ hθ k k' w w' hw hw' g hg
  unfold IsPull1
  rw [pullHyp1_mk, pullHyp1_mk, Hyp1.mk_eq_mk]
  refine ⟨fun p ↦ (Λ'.e (Opposite.op p.unop.1.1)).symm (g p), Tot1.ext (fun p q a ↦ ?_) fun p ↦ ?_⟩
  · let B : Type := (Λ'.L.obj (Opposite.op q.unop.1.1)).B
    have e : @HSub.hSub B B B _ (g q) ((Λ'.L.map ((pairFst φ).map a)).φ (g p)) =
        @HSub.hSub B B B _ ((θ.app q).φ (k.1.1 _ _ (Λ.L.map ((pairSnd φ).map a))))
          (k'.1.1 _ _ (Λ'.L.map ((pairFst φ).map a))) :=
      congrArg (fun c ↦ c.1 p q a) hg
    have h1 : k.1.1 _ _ (Λ.L.map ((pairSnd φ).map a)) =
        Λ.e (Opposite.op q.unop.1.2) (w.1.1 _ _ ((pairSnd φ).map a)) := hw.1 _ _ _
    have h2 : k'.1.1 _ _ (Λ'.L.map ((pairFst φ).map a)) =
        Λ'.e (Opposite.op q.unop.1.1) (w'.1.1 _ _ ((pairFst φ).map a)) := hw'.1 _ _ _
    have h3 := Λ'.nat ((pairFst φ).map a) ((Λ'.e (Opposite.op p.unop.1.1)).symm (g p))
    have h4 := hθ q (w.1.1 _ _ ((pairSnd φ).map a))
    apply (Λ'.e (Opposite.op q.unop.1.1)).injective
    refine ((map_sub _ _ _).trans ?_).trans (map_sub _ _ _).symm
    refine (congrArg₂ (fun x y : B ↦ x - y) (AlgEquiv.apply_symm_apply _ _) (h3.trans
      (congrArg _ (AlgEquiv.apply_symm_apply _ _)))).trans (e.trans ?_)
    exact congrArg₂ (fun x y : B ↦ x - y) ((congrArg (θ.app q).φ h1).trans h4) h2
  · let B : Type := K1 D'.R (Λ'.L.obj (Opposite.op p.unop.1.1)).δ
    have e : kd0 D'.R (Λ'.L.obj (Opposite.op p.unop.1.1)).δ (g p) =
        @HSub.hSub B B B _ (km1 (morSemi m (Λ'.L.obj (Opposite.op p.unop.1.1))) (morDP m _)
          (km1 (SemiHom.of_algHom (θ.app p).φ) (θ.app p).dp
          (k.1.2 (Λ.L.obj (Opposite.op p.unop.1.2))))) (k'.1.2 (Λ'.L.obj (Opposite.op p.unop.1.1))) :=
      congrArg (fun c ↦ c.2 p) hg
    have h1 : k.1.2 (Λ.L.obj (Opposite.op p.unop.1.2)) =
        Submodule.Quotient.mk ((Λ.semi _).m1 (w.1.2 (Opposite.op p.unop.1.2))) := hw.2 _
    have h2 : k'.1.2 (Λ'.L.obj (Opposite.op p.unop.1.1)) =
        Submodule.Quotient.mk ((Λ'.semi _).m1 (w'.1.2 (Opposite.op p.unop.1.1))) := hw'.2 _
    rw [h1, h2] at e
    apply (GlobalTheory.T.liftForms_bijective_degree_one_two D' Λ' (Opposite.op p.unop.1.1)).1.1
    have h3 : (Λ'.semi (Opposite.op p.unop.1.1)).m1 (KaehlerDifferential.D D'.R _
        ((Λ'.e (Opposite.op p.unop.1.1)).symm (g p))) = KaehlerDifferential.D D'.R _ (g p) :=
      (SemiHom.m1_D _ _).trans (congrArg _ ((Λ'.e _).apply_symm_apply _))
    have h4 := kaehlerDifferential_map_commutative_pentagon (Λ.semi (Opposite.op p.unop.1.2)) (SemiHom.of_algHom (θ.app p).φ)
      (morSemi m (Λ'.L.obj (Opposite.op p.unop.1.1))) (semiHom_secPull hφ p.unop)
      (Λ'.semi (Opposite.op p.unop.1.1)) (hθ p) (w.1.2 (Opposite.op p.unop.1.2))
    have h5 : q1 (pairRes φ D'.s) p (w'.1.2 (Opposite.op p.unop.1.1)) = w'.1.2 (Opposite.op p.unop.1.1) :=
      cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff D'.s) (pairFst φ) p _
    refine (congrArg Submodule.Quotient.mk h3).trans (e.trans ?_)
    refine (Submodule.Quotient.mk_sub _).symm.trans (congrArg Submodule.Quotient.mk ?_)
    refine Eq.trans ?_ (map_sub _ _ _).symm
    exact congrArg₂ (· - ·) h4 (congrArg (Λ'.semi (Opposite.op p.unop.1.1)).m1 h5.symm)

end GlobalTheory.PDForm
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_degree_one_class_pullback_of_coboundary : ∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀) (θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G), (∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) = Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a)) → ∀ (k : (KK D.κ D.t).Z1) (k' : (KK D'.κ D'.t).Z1) (w : cechDeRhamTotalCocyclesOne (OAff D.s)) (w' : cechDeRhamTotalCocyclesOne (OAff D'.s)), Λ.Res1 (((KK D.κ D.t).resMap Λ.L).p1 k.1) w.1 → Λ'.Res1 (((KK D'.κ D'.t).resMap Λ'.L).p1 k'.1) w'.1 → ∀ g, ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).D0 g = ((pairB Λ' φ m).pre θ).p1 k.1 - ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p1 k'.1 → IsPull1 hφ (Hyp1.mk _ w) (Hyp1.mk _ w') := by
  atlas_forward_decl GlobalTheory.PDForm.isPull1_of_pair_coboundary
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.PullTwo

section Lift

variable {D : Data} (Λ : Lift D)

def j1 (U : AffOp D.X) : Ω[Sec D.s U.unop.1⁄D.R] →+ K1 D.R (Λ.L.obj U).δ where
  toFun ω := Submodule.Quotient.mk ((Λ.semi U).m1 ω)
  map_zero' := by rw [map_zero, Submodule.Quotient.mk_zero]
  map_add' a b := by rw [map_add, Submodule.Quotient.mk_add]

def j2 (U : AffOp D.X) : Om D.R (Sec D.s U.unop.1) 2 →+ K D.R (Λ.L.obj U).δ 2 where
  toFun ω := Submodule.Quotient.mk ((Λ.semi U).mOm 2 ω)
  map_zero' := by rw [map_zero, Submodule.Quotient.mk_zero]
  map_add' a b := by rw [map_add, Submodule.Quotient.mk_add]

theorem compatibleOneFormClass_restriction_natural {U V : AffOp D.X} (a : U ⟶ V) (ω : Ω[Sec D.s U.unop.1⁄D.R]) :
    j1 Λ V (p1 (OAff D.s) a ω) = km1 (SemiHom.of_algHom (Λ.L.map a).φ) (Λ.L.map a).dp (j1 Λ U ω) := by
  show (Submodule.Quotient.mk ((Λ.semi V).m1 ((semiHom_mp (OAff D.s) a).m1 ω)) : K1 D.R (Λ.L.obj V).δ) =
    km1 (SemiHom.of_algHom (Λ.L.map a).φ) (Λ.L.map a).dp (Submodule.Quotient.mk ((Λ.semi U).m1 ω))
  rw [divPowerCompatOneFormMap_mk]
  congr 1
  rw [SemiHom.oneFormMap_comp_oneFormMap (semiHom_mp (OAff D.s) a) (Λ.semi V) ((semiHom_mp (OAff D.s) a).comp (Λ.semi V))
      (fun _ ↦ rfl),
    SemiHom.oneFormMap_comp_oneFormMap (Λ.semi U) (SemiHom.of_algHom (Λ.L.map a).φ) ((semiHom_mp (OAff D.s) a).comp (Λ.semi V))
      (fun b ↦ (Λ.nat a b).symm)]

theorem compatibleOneFormClass_kaehler_differential (U : AffOp D.X) (b : Sec D.s U.unop.1) :
    j1 Λ U (KaehlerDifferential.D D.R _ b) = kd0 D.R (Λ.L.obj U).δ (Λ.e U b) := by
  show (Submodule.Quotient.mk ((Λ.semi U).m1 (KaehlerDifferential.D D.R _ b)) : K1 D.R (Λ.L.obj U).δ) = _
  rw [SemiHom.m1_D, divPowerCompatFunctionDifferential_apply]
  all_goals rfl

theorem compatibleTwoFormClass_exterior_derivative (U : AffOp D.X) (ω : Ω[Sec D.s U.unop.1⁄D.R]) :
    j2 Λ U (dOne D.R _ ω) = kd1 D.R (Λ.L.obj U).δ (j1 Λ U ω) := by
  show (Submodule.Quotient.mk ((Λ.semi U).mOm 2 (dOne D.R _ ω)) : K D.R (Λ.L.obj U).δ 2) =
    kd1 D.R (Λ.L.obj U).δ (Submodule.Quotient.mk ((Λ.semi U).m1 ω))
  rw [SemiHom.mOm_dOne, divPowerCompatOneFormDerivative_mk]

end Lift

section Pull

variable {D D' : Data} (Λ : Lift D) (Λ' : Lift D') {σ : D.R →+* D'.R} {φ : D'.X ⟶ D.X} {φ₀ : D'.X₀ ⟶ D.X₀}
  (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀) (θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G)
  (hθ : ∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) =
    Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a))

include hθ

theorem movedDatum_compatibleOneFormClass (p : (Pair φ)ᵒᵖ) (ω : Ω[Sec D.s p.unop.1.2.1⁄D.R]) :
    ((pairB Λ' φ m).pre θ).a1 p (j1 Λ (Opposite.op p.unop.1.2) ω) =
      j1 Λ' (Opposite.op p.unop.1.1) ((semiHom_secPull hφ p.unop).m1 ω) := by
  exact congrArg Submodule.Quotient.mk
    (((congrArg (morSemi m ((pairFst φ ⋙ Λ'.L).obj p)).m1 (SemiHom.oneFormMap_comp_oneFormMap (Λ.semi (Opposite.op p.unop.1.2)) (SemiHom.of_algHom (θ.app p).φ)
      ((Λ.semi (Opposite.op p.unop.1.2)).comp (SemiHom.of_algHom (θ.app p).φ)) (fun _ ↦ rfl) ω)).trans
      (SemiHom.oneFormMap_comp_oneFormMap ((Λ.semi (Opposite.op p.unop.1.2)).comp (SemiHom.of_algHom (θ.app p).φ)) (morSemi m ((pairFst φ ⋙ Λ'.L).obj p))
        ((semiHom_secPull hφ p.unop).comp (Λ'.semi (Opposite.op p.unop.1.1))) (fun b ↦ hθ p b) ω)).trans
      (SemiHom.oneFormMap_comp_oneFormMap (semiHom_secPull hφ p.unop) (Λ'.semi (Opposite.op p.unop.1.1)) ((semiHom_secPull hφ p.unop).comp (Λ'.semi (Opposite.op p.unop.1.1)))
        (fun _ ↦ rfl) ω).symm)

theorem movedDatum_compatibleTwoFormClass (p : (Pair φ)ᵒᵖ) (ω : Om D.R (Sec D.s p.unop.1.2.1) 2) :
    ((pairB Λ' φ m).pre θ).a2 p (j2 Λ (Opposite.op p.unop.1.2) ω) =
      j2 Λ' (Opposite.op p.unop.1.1) ((semiHom_secPull hφ p.unop).mOm 2 ω) := by
  exact congrArg Submodule.Quotient.mk
    (((congrArg ((morSemi m ((pairFst φ ⋙ Λ'.L).obj p)).mOm 2) (SemiHom.mOm_mOm (Λ.semi (Opposite.op p.unop.1.2)) (SemiHom.of_algHom (θ.app p).φ)
      ((Λ.semi (Opposite.op p.unop.1.2)).comp (SemiHom.of_algHom (θ.app p).φ)) (fun _ ↦ rfl) ω)).trans
      (SemiHom.mOm_mOm ((Λ.semi (Opposite.op p.unop.1.2)).comp (SemiHom.of_algHom (θ.app p).φ)) (morSemi m ((pairFst φ ⋙ Λ'.L).obj p))
        ((semiHom_secPull hφ p.unop).comp (Λ'.semi (Opposite.op p.unop.1.1))) (fun b ↦ hθ p b) ω)).trans
      (SemiHom.mOm_mOm (semiHom_secPull hφ p.unop) (Λ'.semi (Opposite.op p.unop.1.1)) ((semiHom_secPull hφ p.unop).comp (Λ'.semi (Opposite.op p.unop.1.1)))
        (fun _ ↦ rfl) ω).symm)

end Pull

section Pairs

variable {D D' : Data} (Λ' : Lift D') (φ : D'.X ⟶ D.X)

abbrev Kp : Cx (Pair φ)ᵒᵖ := (KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)

def i0 (p : (Pair φ)ᵒᵖ) : (OPair φ D'.s).obj p →+ (Kp Λ' φ).M0.obj p :=
  (Λ'.e ((pairFst φ).obj p)).toAddEquiv.toAddMonoidHom

def i1 (p : (Pair φ)ᵒᵖ) : Ω[(OPair φ D'.s).obj p⁄D'.R] →+ (Kp Λ' φ).M1.obj p := j1 Λ' ((pairFst φ).obj p)

def i2 (p : (Pair φ)ᵒᵖ) : Om D'.R ((OPair φ D'.s).obj p) 2 →+ (Kp Λ' φ).M2.obj p := j2 Λ' ((pairFst φ).obj p)

variable {φ}

theorem pairFirstOpenFunctionSections_natural {p q : (Pair φ)ᵒᵖ} (a : p ⟶ q) (x : (OPair φ D'.s).obj p) :
    i0 Λ' φ q (mp (OPair φ D'.s) a x) = (Kp Λ' φ).M0.map a (i0 Λ' φ p x) := Λ'.nat ((pairFst φ).map a) x

theorem pairFirstOpenOneForms_natural {p q : (Pair φ)ᵒᵖ} (a : p ⟶ q) (x : Ω[(OPair φ D'.s).obj p⁄D'.R]) :
    i1 Λ' φ q (p1 (OPair φ D'.s) a x) = (Kp Λ' φ).M1.map a (i1 Λ' φ p x) := compatibleOneFormClass_restriction_natural Λ' ((pairFst φ).map a) x

theorem pairFirstOpenOneForms_kaehler_differential (p : (Pair φ)ᵒᵖ) (x : (OPair φ D'.s).obj p) :
    i1 Λ' φ p (KaehlerDifferential.D D'.R _ x) = (Kp Λ' φ).d0 p (i0 Λ' φ p x) := compatibleOneFormClass_kaehler_differential Λ' _ x

theorem pairFirstOpenTwoForms_exterior_derivative (p : (Pair φ)ᵒᵖ) (x : Ω[(OPair φ D'.s).obj p⁄D'.R]) :
    i2 Λ' φ p (dOne D'.R _ x) = (Kp Λ' φ).d1 p (i1 Λ' φ p x) := compatibleTwoFormClass_exterior_derivative Λ' _ x

def Cor (k : (Kp Λ' φ).T2) (w : Tot2 (OPair φ D'.s)) : Prop :=
  (∀ p q r a b, i0 Λ' φ r (w.1 p q r a b) = k.1 p q r a b) ∧ (∀ p q a, i1 Λ' φ q (w.2.1 p q a) = k.2.1 p q a) ∧
    ∀ p, i2 Λ' φ p (w.2.2 p) = k.2.2 p

theorem Cor.sub {k k' : (Kp Λ' φ).T2} {w w' : Tot2 (OPair φ D'.s)} (h : Cor Λ' k w) (h' : Cor Λ' k' w') :
    Cor Λ' (k - k') (w - w') := by
  unfold Cor at h h' ⊢
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨fun p q r a b ↦ ?_, fun p q a ↦ ?_, fun p ↦ ?_⟩
  · simp only [Prod.fst_sub, Pi.sub_apply, map_sub, h1, h1']
  · simp only [Prod.snd_sub, Prod.fst_sub, Pi.sub_apply, map_sub, h2, h2']
  · simp only [Prod.snd_sub, Pi.sub_apply, map_sub, h3, h3']

theorem deRhamCochainCorrespondence_degree_one_coboundary {g : (Kp Λ' φ).T1} {c : Tot1 (OPair φ D'.s)} (hf : ∀ p q a, i0 Λ' φ q (c.1 p q a) = g.1 p q a)
    (hω : ∀ p, i1 Λ' φ p (c.2 p) = g.2 p) : Cor Λ' ((Kp Λ' φ).D1 g) (dTot1 _ c) := by
  unfold Cor
  refine ⟨fun p q r a b ↦ ?_, fun p q a ↦ ?_, fun p ↦ ?_⟩
  · rw [cechDeRhamTotalDifferentialOne_functionPart, map_add, map_sub, pairFirstOpenFunctionSections_natural, hf, hf, hf]
    all_goals rfl
  · rw [dTot1_a, map_sub, map_sub, hω, pairFirstOpenOneForms_natural, hω, pairFirstOpenOneForms_kaehler_differential, hf]
    all_goals rfl
  · rw [dTot1_η, pairFirstOpenTwoForms_exterior_derivative, hω]
    all_goals rfl

theorem Cor.unique {k : (Kp Λ' φ).T2} {w w' : Tot2 (OPair φ D'.s)} (h : Cor Λ' k w) (h' : Cor Λ' k w') : w = w' := by
  unfold Cor at h h'
  have e0 : ∀ p, Function.Injective (i0 Λ' φ p) := fun p ↦ (Λ'.e _).injective
  have e1 : ∀ p, Function.Injective (i1 Λ' φ p) := fun p ↦ (GlobalTheory.T.liftForms_bijective_degree_one_two D' Λ' _).1.1
  have e2 : ∀ p, Function.Injective (i2 Λ' φ p) := fun p ↦ (GlobalTheory.T.liftForms_bijective_degree_one_two D' Λ' _).2.1
  exact Tot2.ext (fun p q r a b ↦ e0 r ((h.1 p q r a b).trans (h'.1 p q r a b).symm))
    (fun p q a ↦ e1 q ((h.2.1 p q a).trans (h'.2.1 p q a).symm))
    (fun p ↦ e2 p ((h.2.2 p).trans (h'.2.2 p).symm))

theorem cor_res {k' : (KK D'.κ D'.t).T2} {w' : Tot2 (OAff D'.s)}
    (hw' : Λ'.Res2 (((KK D'.κ D'.t).resMap Λ'.L).p2 k') w') :
    Cor Λ' (((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p2 k') (pullTot2 (pairRes φ D'.s) w') := by
  unfold Cor
  refine ⟨fun p q r a b ↦ ?_, fun p q a ↦ ?_, fun p ↦ ?_⟩
  · rw [cechDeRhamPullbackTotalDegreeTwo_function_part]
    exact (hw'.1 _ _ _ _ _).symm
  · rw [pullTot2_a]
    exact (congrArg (i1 Λ' φ q) (cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff D'.s) (pairFst φ) q _)).trans (hw'.2.1 _ _ _).symm
  · rw [pullTot2_η]
    exact (congrArg (i2 Λ' φ p) (qOm_restrict (OAff D'.s) (pairFst φ) p _)).trans (hw'.2.2 _).symm

theorem cor_pull (Λ : Lift D) {σ : D.R →+* D'.R} {φ₀ : D'.X₀ ⟶ D.X₀}
    (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀) (θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G)
    (hθ : ∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) =
      Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a))
    {k : (KK D.κ D.t).T2} {w : Tot2 (OAff D.s)} (hw : Λ.Res2 (((KK D.κ D.t).resMap Λ.L).p2 k) w) :
    Cor Λ' (((pairB Λ' φ m).pre θ).p2 k) (pullTot2 (pairPull hφ) w) := by
  unfold Cor
  refine ⟨fun p q r a b ↦ ?_, fun p q a ↦ ?_, fun p ↦ ?_⟩
  · rw [cechDeRhamPullbackTotalDegreeTwo_function_part]
    refine (hθ r _).symm.trans ?_
    exact congrArg (fun y ↦ (θ.app r).φ y) (hw.1 _ _ _ _ _).symm
  · rw [pullTot2_a]
    refine (movedDatum_compatibleOneFormClass (Λ := Λ) (Λ' := Λ') (hφ := hφ) (m := m) (θ := θ) (hθ := hθ) q _).symm.trans ?_
    exact congrArg _ (hw.2.1 _ _ _).symm
  · rw [pullTot2_η]
    refine (movedDatum_compatibleTwoFormClass (Λ := Λ) (Λ' := Λ') (hφ := hφ) (m := m) (θ := θ) (hθ := hθ) p _).symm.trans ?_
    exact congrArg _ (hw.2.2 _).symm

theorem exists_deRhamCochainCorrespondence_degree_one (g : (Kp Λ' φ).T1) : ∃ c : Tot1 (OPair φ D'.s), Cor Λ' ((Kp Λ' φ).D1 g) (dTot1 _ c) := by
  obtain ⟨c1, hc1⟩ : ∃ c1 : ∀ (p q : (Pair φ)ᵒᵖ) (_ : p ⟶ q), (OPair φ D'.s).obj q,
      ∀ p q a, i0 Λ' φ q (c1 p q a) = g.1 p q a :=
    ⟨fun p q a ↦ (Λ'.e _).symm (g.1 p q a), fun p q a ↦ (Λ'.e _).apply_symm_apply _⟩
  choose c2 hc2 using fun p ↦ (GlobalTheory.T.liftForms_bijective_degree_one_two D' Λ' ((pairFst φ).obj p)).1.2 (g.2 p)
  exact ⟨(c1, c2), deRhamCochainCorrespondence_degree_one_coboundary Λ' (c := (c1, c2)) hc1 hc2⟩

set_option maxHeartbeats 1000000 in
private theorem isPull2_aux_lemma (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X)
    (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀)
    (θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G)
    (hθ : ∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) =
      Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a))
    (k : (KK D.κ D.t).Z2) (k' : (KK D'.κ D'.t).Z2) (w : cechDeRhamTotalCocyclesTwo (OAff D.s)) (w' : cechDeRhamTotalCocyclesTwo (OAff D'.s))
    (hw : Λ.Res2 (((KK D.κ D.t).resMap Λ.L).p2 k.1) w.1)
    (hw' : Λ'.Res2 (((KK D'.κ D'.t).resMap Λ'.L).p2 k'.1) w'.1)
    (g : ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).T1)
    (hg : ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).D1 g = ((pairB Λ' φ m).pre θ).p2 k.1 -
      ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p2 k'.1) :
    IsPull2 hφ (Hyp2.mk _ w) (Hyp2.mk _ w') := by
  have h1 := cor_pull Λ' Λ hφ m θ hθ hw
  have h2 := cor_res Λ' (φ := φ) hw'
  obtain ⟨c, hc⟩ := exists_deRhamCochainCorrespondence_degree_one Λ' g
  rw [hg] at hc
  have h3 := Cor.unique Λ' hc (Cor.sub Λ' h1 h2)
  unfold IsPull2
  rw [pullHyp2_mk, pullHyp2_mk, Hyp2.mk_eq_mk]
  refine ⟨c, ?_⟩
  rw [coe_pullZZ2, coe_pullZZ2]
  exact h3

end Pairs

theorem isPull2_of_coboundary (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X)
    (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀)
    (θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G)
    (hθ : ∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) =
      Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a))
    (k : (KK D.κ D.t).Z2) (k' : (KK D'.κ D'.t).Z2) (w : cechDeRhamTotalCocyclesTwo (OAff D.s)) (w' : cechDeRhamTotalCocyclesTwo (OAff D'.s))
    (hw : Λ.Res2 (((KK D.κ D.t).resMap Λ.L).p2 k.1) w.1)
    (hw' : Λ'.Res2 (((KK D'.κ D'.t).resMap Λ'.L).p2 k'.1) w'.1)
    (g : ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).T1)
    (hg : ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).D1 g = ((pairB Λ' φ m).pre θ).p2 k.1 -
      ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p2 k'.1) :
    IsPull2 hφ (Hyp2.mk _ w) (Hyp2.mk _ w') := isPull2_aux_lemma D D' Λ Λ' σ φ φ₀ hφ m θ hθ k k' w w' hw hw' g hg

end GlobalTheory.PDForm.PullTwo
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_degree_two_class_pullback_of_coboundary : ∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀) (θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G), (∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) = Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a)) → ∀ (k : (KK D.κ D.t).Z2) (k' : (KK D'.κ D'.t).Z2) (w : cechDeRhamTotalCocyclesTwo (OAff D.s)) (w' : cechDeRhamTotalCocyclesTwo (OAff D'.s)), Λ.Res2 (((KK D.κ D.t).resMap Λ.L).p2 k.1) w.1 → Λ'.Res2 (((KK D'.κ D'.t).resMap Λ'.L).p2 k'.1) w'.1 → ∀ g, ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).D1 g = ((pairB Λ' φ m).pre θ).p2 k.1 - ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p2 k'.1 → IsPull2 hφ (Hyp2.mk _ w) (Hyp2.mk _ w') := by
  atlas_forward_decl GlobalTheory.PDForm.PullTwo.isPull2_of_coboundary
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.LiftNat

set_option maxHeartbeats 2000000 in

theorem main : (∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀), φ₀ ≫ D.i = D'.i ≫ φ → ∀ c h h', Λ.Rel1 c h → Λ'.Rel1 (m.pull1 c) h' → IsPull1 hφ h h') ∧ ∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀), φ₀ ≫ D.i = D'.i ≫ φ → ∀ c h h', Λ.Rel2 c h → Λ'.Rel2 (m.pull2 c) h' → IsPull2 hφ h h' := by
  refine ⟨?_, ?_⟩
  · intro D D' Λ Λ' σ φ φ₀ hφ m hi c h h' ⟨k, f, w, hc, hh, hk, hw⟩ ⟨k', f', w', hc', hh', hk', hw'⟩
    subst hh hh'
    obtain ⟨g0, hg0⟩ := GlobalTheory.T.compatibleFormsCocycles_degreeOne_differ_coboundary _ _ _ _ _ _ _ _ _ _ _ _ m k k' f f' hk hk' (by rw [hc', ← hc])
    obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_natTrans_lifts_over_affine_pairs D D' Λ Λ' σ φ φ₀ hφ m hi
    have e1 : (morMap m).h1 (QuotientAddGroup.mk k) = QuotientAddGroup.mk k' := by
      change (QuotientAddGroup.mk ((morMap m).z1 k) : (KK D'.κ D'.t).H1) = QuotientAddGroup.mk k'
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      refine ⟨-g0, ?_⟩
      rw [map_neg, hg0]
      change -((morMap m).p1 k.1 - k'.1) = -((morMap m).p1 k.1) + k'.1
      abel
    have e2 : ((pairB Λ' φ m).pre θ).h1 (QuotientAddGroup.mk k) =
        ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).h1 (QuotientAddGroup.mk k') := by
      rw [(GlobalTheory.CxCoh.joinedOne_inst.2.1 _ _ θ (CxMap.joined_pre _ θ)).2, pairB, CxMap.cohomOne_pullback_comp, e1]
    change (QuotientAddGroup.mk (((pairB Λ' φ m).pre θ).z1 k) : ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).H1) =
      QuotientAddGroup.mk (((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).z1 k') at e2
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at e2
    obtain ⟨g, hg⟩ := e2
    refine GlobalTheory.T.deRham_degree_one_class_pullback_of_coboundary D D' Λ Λ' σ φ φ₀ hφ m θ hθ k k' w w' hw hw' (-g) ?_
    rw [map_neg, hg]
    change -(-(((pairB Λ' φ m).pre θ).p1 k.1) + ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p1 k'.1) = _
    abel
  · intro D D' Λ Λ' σ φ φ₀ hφ m hi c h h' hr hr'
    obtain ⟨k, f, w, hc, hh, hk, hw⟩ := hr
    obtain ⟨k', f', w', hc', hh', hk', hw'⟩ := hr'
    subst hh hh'
    obtain ⟨g0, hg0⟩ := GlobalTheory.T.compatibleFormsCocycles_degreeTwo_differ_coboundary _ _ _ _ _ _ _ _ _ _ _ _ m k k' f f' hk hk' (by rw [hc', ← hc])
    obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_natTrans_lifts_over_affine_pairs D D' Λ Λ' σ φ φ₀ hφ m hi
    have e1 : (morMap m).h2 (QuotientAddGroup.mk k) = QuotientAddGroup.mk k' := by
      change (QuotientAddGroup.mk ((morMap m).z2 k) : (KK D'.κ D'.t).H2) = QuotientAddGroup.mk k'
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      refine ⟨-g0, ?_⟩
      rw [map_neg, hg0]
      change -((morMap m).p2 k.1 - k'.1) = -((morMap m).p2 k.1) + k'.1
      abel
    have e2 : ((pairB Λ' φ m).pre θ).h2 (QuotientAddGroup.mk k) =
        ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).h2 (QuotientAddGroup.mk k') := by
      have j := GlobalTheory.CxCoh.JoinedTwoProof.main ((pairB Λ' φ m).pre θ) (pairB Λ' φ m) θ (CxMap.joined_pre _ θ)
        (QuotientAddGroup.mk k)
      refine j.trans ?_
      have j2 := CxMap.cohomTwo_pullback_comp (morMap m) ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)) (QuotientAddGroup.mk k)
      refine j2.trans ?_
      exact congrArg _ e1
    change (QuotientAddGroup.mk (((pairB Λ' φ m).pre θ).z2 k) : ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).H2) =
      QuotientAddGroup.mk (((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).z2 k') at e2
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at e2
    obtain ⟨g, hg⟩ := e2
    refine GlobalTheory.T.deRham_degree_two_class_pullback_of_coboundary D D' Λ Λ' σ φ φ₀ hφ m θ hθ k k' w w' hw hw' (-g) ?_
    rw [map_neg, hg]
    change -(-(((pairB Λ' φ m).pre θ).p2 k.1) + ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p2 k'.1) = _
    abel

end GlobalTheory.PDForm.LiftNat
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineDeRhamRelation_natural_smoothLift_morphism : (∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀), φ₀ ≫ D.i = D'.i ≫ φ → ∀ c h h', Λ.Rel1 c h → Λ'.Rel1 (m.pull1 c) h' → IsPull1 hφ h h') ∧ ∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀), φ₀ ≫ D.i = D'.i ≫ φ → ∀ c h h', Λ.Rel2 c h → Λ'.Rel2 (m.pull2 c) h' → IsPull2 hφ h h' := by
  atlas_forward_decl GlobalTheory.PDForm.LiftNat.main
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.ConnCocycle

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

theorem divPowerCompatDeRhamRelIdeal_zero_dividedPowers (R B : Type) [CommRing R] [CommRing B] [Algebra R B] : rel R (dp0 B) = ⊥ := by
  refine le_bot_iff.1 (Ideal.span_le.2 ?_)
  rintro _ ⟨n, a, ha, rfl⟩
  rw [Ideal.mem_bot.1 ha]
  simp [dpow_eval_zero]

theorem cocyc {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (k : (KK (dp0 R) s).Z1)
    {T T' : Thick (dp0 R) s} (φ : T ⟶ T') :
    k.1.2 T' = km1 (SemiHom.of_algHom φ.φ) φ.dp (k.1.2 T) + kd0 R T'.δ (k.1.1 T T' φ) := by
  have h := congrArg (fun c ↦ c.2.1 T T' φ) (AddMonoidHom.mem_ker.1 k.2)
  change k.1.2 T' - _ - _ = 0 at h
  rw [sub_sub, sub_eq_zero] at h
  exact h

section
variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]

def sndK : (diagExt R B).C →+ K1 R (dp0 B) :=
  AddMonoidHom.mk' (fun c ↦ Submodule.Quotient.mk (TrivSqZeroExt.snd c)) fun a b ↦ by
    rw [TrivSqZeroExt.snd_add, Submodule.Quotient.mk_add]

theorem sndK_apply (c : (diagExt R B).C) : sndK R B c = Submodule.Quotient.mk (TrivSqZeroExt.snd c) := rfl

theorem sndK_mul (x y : (diagExt R B).C) :
    sndK R B (x * y) = (diagExt R B).π x • sndK R B y + (diagExt R B).π y • sndK R B x := by
  show Submodule.Quotient.mk (x * y).snd = x.fst • Submodule.Quotient.mk (p := N1 R (dp0 B)) y.snd +
    y.fst • Submodule.Quotient.mk (p := N1 R (dp0 B)) x.snd
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  congr 1

theorem sndK_alg (r : R) : sndK R B (algebraMap R (diagExt R B).C r) = 0 := by
  rw [sndK_apply, TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.snd_inl, Submodule.Quotient.mk_zero]

theorem sndK_dpow (n : ℕ) (a : (diagExt R B).C) (ha : a ∈ RingHom.ker ((diagExt R B).π : (diagExt R B).C →+* B)) :
    sndK R B ((divided₂ (diagExt R B).sq).dpow (n + 1) a) =
      (diagExt R B).π ((divided₂ (diagExt R B).sq).dpow n a) • sndK R B a := by
  rcases n with _ | m
  · rw [(divided₂ (diagExt R B).sq).dpow_one ha, (divided₂ (diagExt R B).sq).dpow_zero ha, map_one, one_smul]
  · have h0 : (diagExt R B).π ((divided₂ (diagExt R B).sq).dpow (m + 1) a) = 0 :=
      (divided₂ (diagExt R B).sq).dpow_mem (Nat.succ_ne_zero m) ha
    rw [squareZeroDividedPowers_dpow _ (by omega), map_zero, h0, zero_smul]

end

section
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

theorem deRhamAlgebraMap_sends_sectionOneForm (ρ : DR R (diagExt R B).C →+ DR R B) (hmul : ∀ x y, ρ (x * y) = ρ x * ρ y)
    (halg : ∀ c, ρ (algebraMap _ (DR R (diagExt R B).C) c) = algebraMap B (DR R B) ((diagExt R B).π c))
    (hD : ∀ c, ρ (ι1 (D R (diagExt R B).C c)) = ι1 (TrivSqZeroExt.snd c))
    (α : B →ₐ[R] (diagExt R B).C) (hα : ∀ b, (diagExt R B).π (α b) = b)
    (g : Ω[B⁄R] →+ Ω[B⁄R]) (hg : ∀ b c : B, g (b • D R B c) = b • TrivSqZeroExt.snd (α c))
    (κ : Ω[B⁄R]) : ρ (ι1 ((SemiHom.of_algHom α).m1 κ)) = ι1 (g κ) := by
  induction κ using ind1 with
  | h b c =>
    rw [SemiHom.oneFormMap_smul_semilinear, SemiHom.m1_D, map_smul, Algebra.smul_def, hmul, halg, hD, hg, map_smul,
      Algebra.smul_def]
    congr 2
    exact hα b
  | h0 => simp
  | ha x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add, map_add]

end

theorem form_eq_connForm : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (k : (KK (dp0 R) s).Z1)
    (f : Z1 (O (dp0 R) s)), k.1.1 = f.1 → ∀ (B : Type) [CommRing B] [Algebra R B] (x : Sp B ⟶ X)
    (hx : x ≫ s = spMap (algebraMap R B)),
    k.1.2 (Thick.triv B x hx) = Submodule.Quotient.mk (connForm f x hx) := by
  intro R _ X s k f hk B _ _ x hx
  obtain ⟨ρ, hadd, hmul, halg, hD, hrel, -, -⟩ := GlobalTheory.T.exists_formsMap_of_dividedPowerDerivation R B ⊥ (dp0 B) (diagExt R B).C
    (RingHom.ker ((diagExt R B).π : (diagExt R B).C →+* B)) (divided₂ (diagExt R B).sq) (diagExt R B).π
    (sndK R B) (sndK_mul R B) (sndK_alg R B) (sndK_dpow R B)
  have h0 := divPowerCompatDeRhamRelIdeal_zero_dividedPowers R B
  simp only [h0, Ideal.mem_bot, sub_sub, sub_eq_zero] at hadd hmul halg hD hrel
  let ρh : DR R (diagExt R B).C →+ DR R B := AddMonoidHom.mk' ρ hadd
  have hD' : ∀ c, ρh (ι1 (D R (diagExt R B).C c)) = ι1 (TrivSqZeroExt.snd c) := fun c ↦ hD c _ rfl
  let a := (diagExt R B).secHom hx (diagExt R B).i fun _ ↦ rfl
  let a' := (diagExt R B).secHom hx (diagSec R B) (fst_derSec _)
  have c1 := cocyc k a
  have c2 := cocyc k a'
  rw [hk] at c1 c2
  obtain ⟨κ, hκ⟩ := Submodule.Quotient.mk_surjective _ (k.1.2 (Thick.triv B x hx))
  obtain ⟨θ, hθ⟩ := Submodule.Quotient.mk_surjective _ (k.1.2 ((diagExt R B).thick x hx))
  rw [← hκ, ← hθ, divPowerCompatOneFormMap_mk, divPowerCompatFunctionDifferential_apply, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq] at c1 c2
  have e1 : ρh (ι1 (θ - ((SemiHom.of_algHom a.φ).m1 κ + D R _ (f.1 _ _ a)))) = 0 := hrel _ c1
  have e2 : ρh (ι1 (θ - ((SemiHom.of_algHom a'.φ).m1 κ + D R _ (f.1 _ _ a')))) = 0 := hrel _ c2
  have r1 := deRhamAlgebraMap_sends_sectionOneForm ρh hmul halg hD' a.φ (fun _ ↦ rfl) 0 (fun b c ↦ by
    show (0 : Ω[B⁄R]) = b • TrivSqZeroExt.snd (TrivSqZeroExt.inl c : TrivSqZeroExt B Ω[B⁄R])
    rw [TrivSqZeroExt.snd_inl, smul_zero])
  have r2 := deRhamAlgebraMap_sends_sectionOneForm ρh hmul halg hD' a'.φ (fst_derSec _) (AddMonoidHom.id _) (fun b c ↦ by
    show b • D R B c = b • TrivSqZeroExt.snd (diagSec R B c)
    rw [snd_derSec])
  simp only [map_sub, map_add, r1, r2, hD', AddMonoidHom.zero_apply, AddMonoidHom.id_apply, map_zero,
    zero_add] at e1 e2
  rw [← hκ, Submodule.Quotient.eq]
  change ι1 _ ∈ rel R (dp0 B)
  rw [h0, Ideal.mem_bot, map_sub, sub_eq_zero]
  simp only [connForm, TrivSqZeroExt.snd_sub, map_sub]
  change ι1 κ = ι1 (TrivSqZeroExt.snd (f.1 _ _ a)) - ι1 (TrivSqZeroExt.snd (f.1 _ _ a'))
  linear_combination (norm := abel1) e1 - e2

end GlobalTheory.ConnCocycle
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatibleFormsCocycle_form_eq_connectionForm : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (k : (KK (dp0 R) s).Z1) (f : Z1 (O (dp0 R) s)), k.1.1 = f.1 → ∀ (B : Type) [CommRing B] [Algebra R B] (x : Sp B ⟶ X) (hx : x ≫ s = spMap (algebraMap R B)), k.1.2 (Thick.triv B x hx) = Submodule.Quotient.mk (connForm f x hx) := by
  atlas_forward_decl GlobalTheory.ConnCocycle.form_eq_connForm
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.CrysCmp

theorem exists_compatibleFormsCocycle_deRhamClass {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (c : FirstDeRham s) :
    ∃ (f₀ : Z1 (O (dp0 R) s)) (k₀ : (KK (dp0 R) s).Z1), k₀.1.1 = f₀.1 ∧ H1.mk _ f₀ = c := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  have hb := (GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res R ⊥ (dp0 R) X s X (𝟙 X)).1.1.2
  have hfe : ((f.1, fun _ ↦ PUnit.unit) : (Cx.single (KK (dp0 R) s).M0).T1) ∈ (Cx.single (KK (dp0 R) s).M0).Z1 := by
    refine AddMonoidHom.mem_ker.2 (Prod.ext ?_ (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)))
    funext T T' T'' φ ψ
    change mp (O (dp0 R) s) ψ (f.1 _ _ φ) - f.1 _ _ (φ ≫ ψ) + f.1 _ _ ψ = 0
    rw [f.2 φ ψ]; abel
  obtain ⟨q, hq⟩ := hb (QuotientAddGroup.mk ⟨_, hfe⟩)
  obtain ⟨k₀, rfl⟩ := QuotientAddGroup.mk_surjective q
  have hq' := QuotientAddGroup.eq.1 ((QuotientAddGroup.map_mk _ _ _ _ k₀).symm.trans hq)
  rw [AddSubgroup.mem_addSubgroupOf] at hq'
  obtain ⟨g, hg⟩ := hq'
  have hk := AddMonoidHom.mem_ker.1 k₀.2
  let f₀ : Z1 (O (dp0 R) s) := ⟨k₀.1.1, fun T T' T'' φ ψ ↦ by
    have := congrFun (congrFun (congrFun (congrFun (congrFun (congrArg Prod.fst hk) T) T') T'') φ) ψ
    change mp (O (dp0 R) s) ψ (k₀.1.1 _ _ φ) - k₀.1.1 _ _ (φ ≫ ψ) + k₀.1.1 _ _ ψ = 0 at this
    change k₀.1.1 _ _ (φ ≫ ψ) = mp (O (dp0 R) s) ψ (k₀.1.1 _ _ φ) + k₀.1.1 _ _ ψ
    linear_combination (norm := abel1) -this⟩
  refine ⟨f₀, k₀, rfl, ?_⟩
  rw [H1.mk_eq_mk]
  refine ⟨-g, ?_⟩
  funext T T' φ
  have := congrFun (congrFun (congrFun (congrArg Prod.fst hg) T) T') φ
  change g T' - mp (O (dp0 R) s) φ (g T) = -(k₀.1.1 T T' φ) + f.1 T T' φ at this
  change -g T' - mp (O (dp0 R) s) φ (-g T) = k₀.1.1 T T' φ - f.1 T T' φ
  rw [map_neg]
  linear_combination (norm := abel1) -this

section Theta

variable {D : Data} (Λ : Lift D) (m : IsMor (dp0 D.R) D.s D.κ D.t (RingHom.id D.R) D.i)

def thAlg (U : AffOp D.X) : Sec D.s U.unop.1 →ₐ[D.R] (m.obj (Λ.L.obj U)).B :=
  { (Λ.e U : Sec D.s U.unop.1 →+* (Λ.L.obj U).B) with commutes' := fun r ↦ (Λ.e U).commutes r }

def theta (U : AffOp D.X) :
    Thick.triv (Sec D.s U.unop.1) (affPt D.s U.unop) (affPt_w D.s U.unop) ⟶ m.obj (Λ.L.obj U) :=
  Thick.trivHom (thAlg Λ m U) (Λ.pt U)

end Theta

theorem key4 {G : Type} [AddCommGroup G] (A B C E : G) (h : A + B = C + E) : E - A = B - C := by
  rw [sub_eq_sub_iff_add_eq_add, add_comm E C, ← h, add_comm]

theorem lift_rel1_pull1_cmp1 : ∀ (D : Data) (Λ : Lift D) (m : IsMor (dp0 D.R) D.s D.κ D.t (RingHom.id D.R) D.i) (c : FirstDeRham D.s), Λ.Rel1 (m.pull1 c) (cmp1 D.s c) := by
  intro D Λ m c
  obtain ⟨f₀, k₀, hk, rfl⟩ := exists_compatibleFormsCocycle_deRhamClass D.s c
  let k := (morMap m).z1 k₀
  let k' := ((KK D.κ D.t).resMap Λ.L).p1 k.1
  have hk' : k' ∈ ((KK D.κ D.t).res Λ.L).Z1 := (((KK D.κ D.t).resMap Λ.L).z1 k).2
  obtain ⟨w, hw, -⟩ := ((GlobalTheory.T.compatibleFormsCochains_eq_deRhamCochains_smoothLift).1 D Λ).1 k'
  have hwZ : w ∈ cechDeRhamTotalCocyclesOne (OAff D.s) := ((((GlobalTheory.T.compatibleFormsCochains_eq_deRhamCochains_smoothLift).1 D Λ).2.2 k' w hw).1.1 hk')
  refine ⟨k, m.coef.pullbackOneCocycle f₀, ⟨w, hwZ⟩, rfl, ?_, ?_, hw⟩

  · rw [comparison_mk, Hyp1.mk_eq_mk]
    refine ⟨fun U ↦ (Λ.e U).symm (ev f₀ (theta Λ m U)), Tot1.ext (fun U V a ↦ ?_) (fun U ↦ ?_)⟩
    · change (Λ.e V).symm (ev f₀ (theta Λ m V)) - Sec.res D.s (leOfHom a.unop) ((Λ.e U).symm (ev f₀ (theta Λ m U))) =
        w.1 U V a - (cmpZZ D.s f₀).1.1 U V a
      apply (Λ.e V).injective
      have h1 : Λ.e V (w.1 U V a) = ev f₀ (m.functor.map (Λ.L.map a)) := by
        refine (hw.1 U V a).symm.trans ?_
        change k₀.1.1 _ _ _ = _
        rw [hk]; rfl
      have h2 := Λ.nat a ((Λ.e U).symm (ev f₀ (theta Λ m U)))
      erw [AlgEquiv.apply_symm_apply] at h2
      have sq := ev_sq f₀ (theta Λ m U) (m.functor.map (Λ.L.map a))
          (Thick.trivHom (hx := affPt_w D.s U.unop) (T := Thick.triv _ _ (affPt_w D.s V.unop))
            (Sec.res D.s (leOfHom a.unop)) (affPt_res D.s (leOfHom a.unop))) (theta Λ m V)
          (by intro c; exact (Λ.nat a c).symm)
      rw [map_sub, map_sub, h1, cmpZZ_f]
      erw [AlgEquiv.apply_symm_apply]
      change _ - Λ.e V (mp (OAff D.s) a _) = _
      rw [h2]
      exact key4 _ _ _ _ sq
    · change KaehlerDifferential.D D.R (Sec D.s U.unop.1) ((Λ.e U).symm (ev f₀ (theta Λ m U))) =
        w.2 U - connForm f₀ (affPt D.s U.unop) (affPt_w D.s U.unop)
      have hrel : rel D.R (Λ.L.obj U).δ = ⊥ :=
        (GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base).2 D.R (Λ.L.obj U).B (Λ.L.obj U).J (Λ.L.obj U).δ D.I D.κ (Λ.L.obj U).dp (Λ.gen U).le
      have inj : ∀ x y : Ω[(Λ.L.obj U).B⁄D.R],
          (Submodule.Quotient.mk x : K1 D.R (Λ.L.obj U).δ) = Submodule.Quotient.mk y → x = y := by
        intro x y h
        rw [Submodule.Quotient.eq] at h
        have h' : ι1 (x - y) ∈ rel D.R (Λ.L.obj U).δ := h
        rw [hrel, Ideal.mem_bot, map_sub, sub_eq_zero] at h'
        exact (ExteriorAlgebra.ι_inj _ _ _).1 h'
      have hk0 := AddMonoidHom.mem_ker.1 k₀.2
      have hcoc := congrFun (congrFun (congrFun (congrArg (fun x ↦ x.2.1) hk0) _) _) (theta Λ m U)
      have hc := GlobalTheory.T.compatibleFormsCocycle_form_eq_connectionForm D.R D.X D.s k₀ f₀ hk (Sec D.s U.unop.1) (affPt D.s U.unop) (affPt_w D.s U.unop)
      have e1 : k₀.1.2 (m.obj (Λ.L.obj U)) = km1 (SemiHom.of_algHom (theta Λ m U).φ) (theta Λ m U).dp (k₀.1.2 _) +
          kd0 D.R (m.obj (Λ.L.obj U)).δ (ev f₀ (theta Λ m U)) := by
        have : k₀.1.2 (m.obj (Λ.L.obj U)) - km1 (SemiHom.of_algHom (theta Λ m U).φ) (theta Λ m U).dp (k₀.1.2 _) -
            kd0 D.R (m.obj (Λ.L.obj U)).δ (k₀.1.1 _ _ (theta Λ m U)) = 0 := hcoc
        rw [hk] at this
        exact sub_eq_zero.1 ((sub_sub _ _ _).symm.trans this)
      rw [hc, divPowerCompatOneFormMap_mk, divPowerCompatFunctionDifferential_apply, ← Submodule.Quotient.mk_add] at e1
      have e2 := hw.2 U
      change km1 (morSemi m (Λ.L.obj U)) (morDP m (Λ.L.obj U)) (k₀.1.2 (m.obj (Λ.L.obj U))) = _ at e2
      rw [e1] at e2
      erw [divPowerCompatOneFormMap_mk] at e2
      have e3 := inj _ _ e2
      have e3' : (Λ.semi U).m1 (w.2 U) = (Λ.semi U).m1 (connForm f₀ (affPt D.s U.unop) (affPt_w D.s U.unop)) +
          KaehlerDifferential.D D.R (Λ.L.obj U).B (ev f₀ (theta Λ m U)) := by
        rw [← e3, map_add]
        congr 1
        · exact SemiHom.oneFormMap_comp_oneFormMap _ _ _ (fun _ ↦ rfl) _
        · exact SemiHom.m1_D _ _
      have semiInv : SemiHom (RingHom.id D.R) ((Λ.e U).symm : (Λ.L.obj U).B →+* Sec D.s U.unop.1) :=
        fun r b ↦ map_smul (Λ.e U).symm r b
      have linv : ∀ ω, semiInv.m1 ((Λ.semi U).m1 ω) = ω := fun ω ↦
        (SemiHom.oneFormMap_comp_oneFormMap (Λ.semi U) semiInv (SemiHom.of_algHom (AlgHom.id D.R (Sec D.s U.unop.1)))
          (fun b ↦ (Λ.e U).symm_apply_apply b) ω).trans (SemiHom.oneFormMap_eq_self_of_id _ (fun _ ↦ rfl) ω)
      have e5 := congrArg semiInv.m1 e3'
      rw [map_add, linv, linv] at e5
      rw [e5, add_sub_cancel_left]
      exact (SemiHom.m1_D semiInv _).symm
  · funext T T' φ
    change k₀.1.1 _ _ (m.functor.map φ) = f₀.1 _ _ (m.functor.map φ)
    rw [hk]

end GlobalTheory.PDForm.CrysCmp
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothLift_degreeOne_comparisonRelation : ∀ (D : Data) (Λ : Lift D) (m : IsMor (dp0 D.R) D.s D.κ D.t (RingHom.id D.R) D.i) (c : FirstDeRham D.s), Λ.Rel1 (m.pull1 c) (cmp1 D.s c) := by
  atlas_forward_decl GlobalTheory.PDForm.CrysCmp.lift_rel1_pull1_cmp1
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.SmoothLift

theorem exists_linearEquiv_of_rel {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (p : M → N → Prop) (h1 : ∀ c, ∃ h, p c h) (h2 : ∀ h, ∃ c, p c h)
    (h0 : ∀ c h, p c h → (c = 0 ↔ h = 0)) (hadd : ∀ a b h h', p a h → p b h' → p (a + b) (h + h'))
    (hsmul : ∀ (r : R) a h, p a h → p (r • a) (r • h)) : ∃ e : M ≃ₗ[R] N, ∀ c h, e c = h ↔ p c h := by
  choose f hf using h1
  have uniq : ∀ c h h', p c h → p c h' → h' = h := by
    intro c h h' ph ph'
    have q := hadd _ _ _ _ ph' (hsmul (-1) _ _ ph)
    rw [neg_one_smul, neg_one_smul, add_neg_cancel] at q
    exact add_neg_eq_zero.1 ((h0 _ _ q).1 rfl)
  let g : M →ₗ[R] N :=
    { toFun := f
      map_add' := fun a b ↦ uniq _ _ _ (hadd _ _ _ _ (hf a) (hf b)) (hf (a + b))
      map_smul' := fun r a ↦ uniq _ _ _ (hsmul r _ _ (hf a)) (hf (r • a)) }
  have inj : Function.Injective g := by
    intro a b hab
    have q := hadd _ _ _ _ (hf a) (hsmul (-1) _ _ (hf b))
    rw [neg_one_smul, neg_one_smul] at q
    have hab' : f a = f b := hab
    rw [hab', add_neg_cancel] at q
    exact add_neg_eq_zero.1 ((h0 _ _ q).2 rfl)
  have surj : Function.Surjective g := by
    intro h
    obtain ⟨c, hc⟩ := h2 h
    exact ⟨c, uniq _ _ _ hc (hf c)⟩
  refine ⟨LinearEquiv.ofBijective g ⟨inj, surj⟩, fun c h ↦ ⟨?_, fun ph ↦ uniq _ _ _ ph (hf c)⟩⟩
  rintro rfl
  exact hf c

end GlobalTheory.SmoothLift

namespace GlobalTheory.SmoothLift

theorem crystallineSmoothLift_of_relations : GlobalTheory.Published.CrystallineSmoothLift := by
  have Λ : ∀ D : Data, Lift D := fun D ↦ Classical.choice (GlobalTheory.T.nonempty_smoothLiftAffineThickenings D)
  obtain ⟨hr1, hr2⟩ := GlobalTheory.T.crystallineCechDeRham_relations_total_detect_zero
  have E1 : ∀ D : Data, ∃ e : CatCoh.H1 (O D.κ D.t) ≃ₗ[D.R] HH1 D.s, ∀ c h, e c = h ↔ (Λ D).Rel1 c h := fun D ↦
    exists_linearEquiv_of_rel _ (hr1 D (Λ D)).1 (hr1 D (Λ D)).2.1 (hr1 D (Λ D)).2.2
      (GlobalTheory.T.smoothLift_comparisonRelations_add_smul D (Λ D)).1 (GlobalTheory.T.smoothLift_comparisonRelations_add_smul D (Λ D)).2.1
  have E2 : ∀ D : Data, ∃ e : CatCoh.H2 (O D.κ D.t) ≃ₗ[D.R] HH2 D.s, ∀ c h, e c = h ↔ (Λ D).Rel2 c h := fun D ↦
    exists_linearEquiv_of_rel _ (hr2 D (Λ D)).1 (hr2 D (Λ D)).2.1 (hr2 D (Λ D)).2.2
      (GlobalTheory.T.smoothLift_comparisonRelations_add_smul D (Λ D)).2.2.1 (GlobalTheory.T.smoothLift_comparisonRelations_add_smul D (Λ D)).2.2.2
  choose e₁ he₁ using E1
  choose e₂ he₂ using E2
  have r1 : ∀ D c, (Λ D).Rel1 c (e₁ D c) := fun D c ↦ (he₁ D c _).1 rfl
  have r2 : ∀ D c, (Λ D).Rel2 c (e₂ D c) := fun D c ↦ (he₂ D c _).1 rfl
  refine ⟨e₁, e₂, ?_, ?_, ?_⟩
  · intro D a b
    exact (he₂ D _ _).2 (GlobalTheory.T.comparison_relations_respect_cup D (Λ D) a b _ _ (r1 D a) (r1 D b))
  · intro D m c
    exact (he₁ D _ _).2 (GlobalTheory.T.smoothLift_degreeOne_comparisonRelation D (Λ D) m c)
  · intro D D' σ φ φ₀ h m hc
    exact ⟨fun c ↦ GlobalTheory.T.crystallineDeRhamRelation_natural_smoothLift_morphism.1 D D' (Λ D) (Λ D') σ φ φ₀ h m hc c _ _ (r1 D c) (r1 D' _),
      fun c ↦ GlobalTheory.T.crystallineDeRhamRelation_natural_smoothLift_morphism.2 D D' (Λ D) (Λ D') σ φ φ₀ h m hc c _ _ (r2 D c) (r2 D' _)⟩

end GlobalTheory.SmoothLift
end
end
