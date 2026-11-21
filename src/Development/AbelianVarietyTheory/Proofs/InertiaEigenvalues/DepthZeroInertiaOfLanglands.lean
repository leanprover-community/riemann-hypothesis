import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroTypeInertia
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIneOfUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionUnramifiedAtOnePlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinInertiaIsUnitAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerApproxUnitAdicCompletion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalCharExistsOfGreen

section
section
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT

namespace GlobalTheory.KummerAb

theorem kummer_char_eq_of_toAb_eq : ∀ (E' Ω : Type) [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    (m : ℕ) (hm : 0 < m) (ζ : E') (hζ : IsPrimitiveRoot ζ m) (c : E') (hc : c ≠ 0) (y : Ω)
    (hy : y ^ m = algebraMap E' Ω c) (σ τ : G E' Ω) (he : toAb E' Ω σ = toAb E' Ω τ), σ y / y = τ y / y := by
  intro E' Ω _ _ _ _ _ m hm ζ hζ c hc y hy σ τ he
  have hc' : algebraMap E' Ω c ≠ 0 := (map_ne_zero_iff _ (algebraMap E' Ω).injective).mpr hc
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hy
    exact hc' hy.symm
  haveI : NeZero m := ⟨hm.ne'⟩
  have hζ' : IsPrimitiveRoot (algebraMap E' Ω ζ) m := hζ.map_of_injective (algebraMap E' Ω).injective
  have key : ∀ ρ : G E' Ω, ∃ e : E', ρ y = algebraMap E' Ω e * y := by
    intro ρ
    have h1 : (ρ y / y) ^ m = 1 := by
      rw [div_pow, ← map_pow, hy, AlgEquiv.commutes, div_self hc']
    obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one h1
    refine ⟨ζ ^ i, ?_⟩
    rw [map_pow, hi, div_mul_cancel₀ _ hy0]
  let φ : G E' Ω →* Ωˣ := MonoidHom.mk' (fun ρ => Units.mk0 (ρ y / y)
      (div_ne_zero ((map_ne_zero_iff _ ρ.injective).mpr hy0) hy0)) (by
    intro a b
    ext
    obtain ⟨e, he⟩ := key b
    simp only [Units.val_mul, Units.val_mk0, AlgEquiv.mul_apply, he, map_mul, AlgEquiv.commutes]
    field_simp)
  have hφ : ∀ ρ, (φ ρ : Ω) = ρ y / y := fun ρ => rfl
  have hint : IsIntegral E' y := Algebra.IsIntegral.isIntegral y
  haveI : FiniteDimensional E' (IntermediateField.adjoin E' {y}) := IntermediateField.adjoin.finiteDimensional hint
  have hopen : IsOpen (φ.ker : Set (G E' Ω)) := by
    refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin E' {y}).fixingSubgroup) ?_ (IntermediateField.fixingSubgroup_isOpen _)
    intro ρ hρ
    have : ρ y = y := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hρ y
      (IntermediateField.subset_adjoin E' {y} rfl)
    rw [MonoidHom.mem_ker]
    ext
    rw [hφ, this, div_self hy0, Units.val_one]
  have hclosed : IsClosed (φ.ker : Set (G E' Ω)) := Subgroup.isClosed_of_isOpen _ hopen
  have hle : (commutator (G E' Ω)).topologicalClosure ≤ φ.ker :=
    Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker φ) hclosed
  have hmem : σ⁻¹ * τ ∈ (commutator (G E' Ω)).topologicalClosure := QuotientGroup.eq.mp he
  have h2 := hle hmem
  rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h2
  rw [← hφ, ← hφ, h2]

end GlobalTheory.KummerAb
end

open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerCharacter_factors_absoluteGaloisAbelianization : ∀ (E' Ω : Type) [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    (m : ℕ) (hm : 0 < m) (ζ : E') (hζ : IsPrimitiveRoot ζ m) (c : E') (hc : c ≠ 0) (y : Ω)
    (hy : y ^ m = algebraMap E' Ω c) (σ τ : G E' Ω) (he : toAb E' Ω σ = toAb E' Ω τ), σ y / y = τ y / y := by
  atlas_forward_decl GlobalTheory.KummerAb.kummer_char_eq_of_toAb_eq
end

section
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localArtin_inertia_isUnitAt : ∀ {E' Ω : Type} [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    {A : ValuationSubring Ω} {w' : HeightOneSpectrum (𝓞 E')} (h' : IsPlaceOver A w')
    (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha : IsLocalArtin h' a') (t : Ine (F := E') A),
    IsUnitAt w' (a' (ineIncl h' t)) := by
  first | exact @GlobalTheory.ArtinInertia.isUnitAt_artin_ine | exact GlobalTheory.ArtinInertia.isUnitAt_artin_ine | (intros; apply GlobalTheory.ArtinInertia.isUnitAt_artin_ine <;> assumption)
end

section
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_approx_unit_adicCompletion : ∀ {E' : Type} [Field E'] [NumberField E'] (w' : HeightOneSpectrum (𝓞 E'))
    (u : (w'.adicCompletion E')ˣ) (hu : IsUnitAt w' u),
    ∃ x : 𝓞 E', Valued.v ((u : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 := by
  first | exact @GlobalTheory.unit_completion_approx_integer | exact GlobalTheory.unit_completion_approx_integer | (intros; apply GlobalTheory.unit_completion_approx_integer <;> assumption)
end

section
section
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT

theorem GlobalTheory.residue_ringOfIntegers_to_place : ∀ (E' Ω : Type) [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g),
    ∃ ι : 𝓞 E' ⧸ w'.asIdeal →+* Formalism.CyclotomicNorms.Fbar g,
      ∀ x : 𝓞 E', ι (Ideal.Quotient.mk _ x) = redThrough A κ (algebraMap E' Ω (x : E')) := by
  intro E' Ω _ _ _ _ g _ A w' h' κ
  classical
  have hmem : ∀ x : 𝓞 E', algebraMap E' Ω (x : E') ∈ A := by
    intro x
    have hi : IsIntegral ℤ (algebraMap E' Ω (x : E')) :=
      (RingOfIntegers.isIntegral_coe x).map (IsScalarTower.toAlgHom ℤ E' Ω)
    have h2 : IsIntegral A.valuation.integer (algebraMap E' Ω (x : E')) := hi.tower_top
    have h3 := (Valuation.integer.integers A.valuation).mem_of_integral h2
    obtain ⟨y, hy⟩ := h3
    rw [← hy]
    exact (A.valuation_le_one_iff _).1 (by simpa [Algebra.smul_def] using y.2)
  let φ : 𝓞 E' →+* A :=
    { toFun := fun x => ⟨algebraMap E' Ω (x : E'), hmem x⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  let ψ : 𝓞 E' →+* Formalism.CyclotomicNorms.Fbar g := κ.toRingHom.comp ((IsLocalRing.residue A).comp φ)
  have hker : ∀ x ∈ w'.asIdeal, ψ x = 0 := by
    intro x hx
    have hlt : A.valuation (algebraMap E' Ω (x : E')) < 1 := (h' x).2 hx
    have hm : φ x ∈ IsLocalRing.maximalIdeal A := (A.valuation_lt_one_iff (φ x)).2 hlt
    simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [(IsLocalRing.residue_eq_zero_iff (φ x)).2 hm, map_zero]
  refine ⟨Ideal.Quotient.lift _ ψ hker, fun x => ?_⟩
  rw [Ideal.Quotient.lift_mk]
  unfold redThrough
  rw [dif_pos (hmem x)]
  rfl
end

open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residueField_embedding_place_over : ∀ (E' Ω : Type) [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g),
    ∃ ι : 𝓞 E' ⧸ w'.asIdeal →+* Formalism.CyclotomicNorms.Fbar g,
      ∀ x : 𝓞 E', ι (Ideal.Quotient.mk _ x) = redThrough A κ (algebraMap E' Ω (x : E')) := by
  atlas_forward_decl GlobalTheory.residue_ringOfIntegers_to_place
end

section
section
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT

noncomputable section

namespace GlobalTheory.RegLabelChar

open Polynomial GlobalTheory.GLq

variable {g : ℕ} [Fact g.Prime]

theorem pow_congr (L : LabelDatum g) {n : ℕ} (hn : 0 < n) {t : ℂ} (ht : t ^ (g ^ n - 1) = 1) {a b : ℕ}
    (h : L.gen n ^ a = L.gen n ^ b) : t ^ a = t ^ b := by
  have hN := L.gen_order n hn
  have hq1 : 0 < g ^ n - 1 := by
    have := Nat.one_lt_pow hn.ne' (Fact.out : g.Prime).one_lt
    omega
  have hpos : 0 < orderOf (L.gen n) := hN ▸ hq1
  have h2 : L.gen n ^ (a % orderOf (L.gen n)) = L.gen n ^ (b % orderOf (L.gen n)) := by
    rw [pow_mod_orderOf, pow_mod_orderOf, h]
  have h3 := pow_injOn_Iio_orderOf (Set.mem_Iio.2 (Nat.mod_lt a hpos)) (Set.mem_Iio.2 (Nat.mod_lt b hpos)) h2
  rw [hN] at h3
  rw [← Nat.mod_add_div a (g ^ n - 1), ← Nat.mod_add_div b (g ^ n - 1), pow_add, pow_add, pow_mul, pow_mul, ht,
    one_pow, one_pow, h3]

theorem thetaOf_eq (L : LabelDatum g) {n : ℕ} (hn : 0 < n) {x : Formalism.CyclotomicNorms.Fbar g}
    (hx : L.teich x ^ (g ^ n - 1) = 1) {z : Formalism.CyclotomicNorms.Fbar g} {k : ℕ} (hz : z = L.gen n ^ k) :
    thetaOf L n x z = L.teich x ^ k := by
  have he : ∃ m : ℕ, z = L.gen n ^ m := ⟨k, hz⟩
  unfold thetaOf
  rw [dif_pos he]
  exact pow_congr L hn hx ((Exists.choose_spec he).symm.trans hz)

theorem exists_regularChar :
    ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (hn : 0 < n) (P : (ZMod g)[X])
    (hP : IsPrimeLab n P) (K : Type) [Field K] [Finite K] (hK : Nat.card K = g ^ n) (ι : K →+* Formalism.CyclotomicNorms.Fbar g),
    ∃ θ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ ∧
      (∃ x ∈ Formalism.CyclotomicNorms.rootsBar P, ∀ u : Kˣ, ((θ u : ℂˣ) : ℂ) = thetaOf L n x (ι u)) ∧
      ∀ u : Kˣ, ι u = L.gen n →
        ∏ j ∈ Finset.range n, (X - C ((θ (u ^ g ^ j) : ℂˣ) : ℂ)) = GlobalTheory.SerSys.TameGen.liftPoly L.teich P := by
  intro g _ L n hn P hP K _ _ hK ι
  classical
  haveI := Fintype.ofFinite K
  have hg1 : 1 < g := (Fact.out : g.Prime).one_lt
  have hq : 1 < g ^ n := Nat.one_lt_pow hn.ne' hg1
  have hq1 : 0 < g ^ n - 1 := by omega
  haveI : NeZero (g ^ n - 1) := ⟨hq1.ne'⟩
  have hdegP : P.natDegree = n := hP.2.2.2
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero (Formalism.CyclotomicNorms.Fbar g) P (degree_pos_of_irreducible hP.2.1).ne'
  have hxmem : x ∈ Formalism.CyclotomicNorms.rootsBar P := by
    simpa [Formalism.CyclotomicNorms.rootsBar, hP.2.1.ne_zero, aeval_def, eval_map] using hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [← coeff_zero_eq_aeval_zero'] at hx
    exact hP.2.2.1 ((map_eq_zero_iff _ (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective).1 hx)
  have hxq : x ^ (g ^ n - 1) = 1 := by
    have h1 : x ^ g ^ n = x := (GlobalTheory.GreenExists.pow_eq_self_iff hP.2.1 hx n).2 (hdegP ▸ dvd_refl _)
    have h2 : x ^ (g ^ n - 1) * x = 1 * x := by
      rw [← pow_succ, Nat.sub_add_cancel hq.le, h1, one_mul]
    exact mul_right_cancel₀ hx0 h2
  have ht1 : L.teich x ^ (g ^ n - 1) = 1 := by rw [← map_pow, hxq, map_one]
  have hgo : orderOf (L.gen n) = g ^ n - 1 := L.gen_order n hn
  have hprim : IsPrimitiveRoot (L.gen n) (g ^ n - 1) := hgo ▸ IsPrimitiveRoot.orderOf _
  have hcardK : Fintype.card K = g ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  have hpow : ∀ u : Kˣ, ∃ k : ℕ, ι u = L.gen n ^ k := fun u => by
    have h1 : (ι u) ^ (g ^ n - 1) = 1 := by
      rw [← map_pow, ← hcardK, FiniteField.pow_card_sub_one_eq_one (u : K) u.ne_zero, map_one]
    obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one h1
    exact ⟨i, hi.symm⟩
  let f : Kˣ →* ℂ :=
    { toFun := fun u => thetaOf L n x (ι u)
      map_one' := by
        rw [thetaOf_eq L hn ht1 (k := 0) (by rw [Units.val_one, map_one, pow_zero]), pow_zero]
      map_mul' := fun u v => by
        obtain ⟨a, ha⟩ := hpow u
        obtain ⟨b, hb⟩ := hpow v
        rw [thetaOf_eq L hn ht1 ha, thetaOf_eq L hn ht1 hb,
          thetaOf_eq L hn ht1 (k := a + b) (by rw [Units.val_mul, map_mul, ha, hb, pow_add]), pow_add] }
  have hf : ∀ u : Kˣ, ((f.toHomUnits u : ℂˣ) : ℂ) = thetaOf L n x (ι u) := fun u => rfl
  have hfpow : ∀ (u : Kˣ) (m : ℕ), ι u = L.gen n → ((f.toHomUnits (u ^ m) : ℂˣ) : ℂ) = L.teich x ^ m :=
    fun u m hu => by
      rw [hf]
      exact thetaOf_eq L hn ht1 (by rw [Units.val_pow_eq_pow_val, map_pow, hu])

  have hroots := GlobalTheory.GreenExists.rootsBar_eq hP.2.1 hx
  rw [hdegP] at hroots
  have hnd : (Formalism.CyclotomicNorms.rootsBar P).Nodup := by
    unfold Formalism.CyclotomicNorms.rootsBar
    exact nodup_roots ((PerfectField.separable_of_irreducible hP.2.1).map)
  rw [hroots] at hnd
  refine ⟨f.toHomUnits, ?_, ⟨x, hxmem, hf⟩, ?_⟩
  ·
    intro i j hi hj h
    obtain ⟨w, hw⟩ := IsCyclic.exists_generator (α := Kˣ)
    have hwo : orderOf w = g ^ n - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hw, Nat.card_eq_fintype_card, Fintype.card_units, hcardK]
    have hιw : orderOf (ι (w : K)) = g ^ n - 1 := by
      have h := orderOf_injective ι.toMonoidHom ι.injective (w : K)
      rw [orderOf_units, hwo] at h
      exact h
    have hwp : IsPrimitiveRoot (ι (w : K)) (g ^ n - 1) := hιw ▸ IsPrimitiveRoot.orderOf _
    obtain ⟨k, -, hk⟩ := hwp.eq_pow_of_pow_eq_one (hgo ▸ pow_orderOf_eq_one (L.gen n))
    have hu0 : ι ((w ^ k : Kˣ) : K) = L.gen n := by rw [Units.val_pow_eq_pow_val, map_pow, hk]
    have h1 := congrArg (fun φ : Kˣ →* ℂˣ => ((φ (w ^ k) : ℂˣ) : ℂ)) h
    simp only [MonoidHom.pow_apply, Units.val_pow_eq_pow_val] at h1
    have hθ0 : ((f.toHomUnits (w ^ k) : ℂˣ) : ℂ) = L.teich x := by
      rw [hf]
      exact (thetaOf_eq L hn ht1 (k := 1) (by rw [hu0, pow_one])).trans (pow_one _)
    rw [hθ0, ← map_pow, ← map_pow] at h1
    have h2 := L.teich_inj _ _ (pow_ne_zero _ hx0) (pow_ne_zero _ hx0) h1
    exact Multiset.inj_on_of_nodup_map hnd i (Finset.mem_range.2 hi) j
      (Finset.mem_range.2 hj) h2
  · intro u hu
    rw [GlobalTheory.SerSys.TameGen.liftPoly, hroots, Multiset.map_map, Finset.prod_eq_multiset_prod]
    congr 1
    refine Multiset.map_congr rfl fun j _ => ?_
    rw [Function.comp_apply, hfpow u _ hu, map_pow L.teich]

end GlobalTheory.RegLabelChar

end
end

open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regularCharacter_labelRoot_product : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (hn : 0 < n) (P : (ZMod g)[X])
    (hP : IsPrimeLab n P) (K : Type) [Field K] [Finite K] (hK : Nat.card K = g ^ n) (ι : K →+* Formalism.CyclotomicNorms.Fbar g),
    ∃ θ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ ∧
      (∃ x ∈ Formalism.CyclotomicNorms.rootsBar P, ∀ u : Kˣ, ((θ u : ℂˣ) : ℂ) = thetaOf L n x (ι u)) ∧
      ∀ u : Kˣ, ι u = L.gen n →
        ∏ j ∈ Finset.range n, (X - C ((θ (u ^ g ^ j) : ℂˣ) : ℂ)) = GlobalTheory.SerSys.TameGen.liftPoly L.teich P := by
  atlas_forward_decl GlobalTheory.RegLabelChar.exists_regularChar
end

section
noncomputable section

open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT

namespace GlobalTheory.DepthZeroBridge

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem redThrough_eq_of_val_sub_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {l : ℕ} [Fact l.Prime]
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar l) {a b : Ω} (ha : a ∈ A) (hab : A.valuation (a - b) < 1) :
    redThrough A κ a = redThrough A κ b := by
  have hab' : a - b ∈ A := (A.valuation_le_one_iff _).mp hab.le
  have hb : b ∈ A := by
    have : b = a - (a - b) := by ring
    rw [this]; exact A.sub_mem ha hab'
  unfold redThrough
  rw [dif_pos ha, dif_pos hb]
  congr 1
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  show (⟨a, ha⟩ - ⟨b, hb⟩ : A) ∈ IsLocalRing.maximalIdeal A
  exact (A.valuation_lt_one_iff _).mpr hab

open scoped Pointwise in

theorem depthZeroInertia_of_depthZeroTypeInertia : GlobalTheory.Published.DepthZeroTypeInertia → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.LocalLanglandsGL →
    GlobalTheory.Published.DepthZeroInertia := by
  intro HT HG HL
  intro E Ω _ _ _ _ _ g _ A w h rc hrc i hi κ L t ht hTC n σ _ τ P hP hinf
  have hn : 0 < n := hP.2.1.1
  obtain ⟨E', _, _, _, _, _, _, _, w', h', hg0, hg1, hN, ⟨ζ, hζ⟩, hfix⟩ := GlobalTheory.T.exists_unramified_totallyComplex_ext_with_unity_roots E Ω g A w h i hi n hn
  let t' : Ω ≃ₐ[E'] Ω := { t with commutes' := fun e => hfix t ht e }
  have htt : ∀ z, t' z = t z := fun _ => rfl
  have hdec : t' • A = A := by
    have h0 : t • A = A := ht.1
    ext z
    rw [ValuationSubring.mem_smul_pointwise_iff_exists]
    conv_rhs => rw [← h0]
    rw [ValuationSubring.mem_smul_pointwise_iff_exists]
    rfl
  have ht' : t' ∈ Ine (F := E') A := ⟨hdec, fun z hz => ht.2 z hz⟩
  have hres : AlgEquiv.restrictScalars E t' = t := by ext z; rfl
  obtain ⟨a', ha'⟩ : ∃ a' : Weil h' →* (w'.adicCompletion E')ˣ, IsLocalArtin h' a' := by
    obtain ⟨rc', hrc', -⟩ := HL.1 E' Ω A w' h'
    obtain ⟨a', ha', -⟩ := hrc'
    exact ⟨a', ha'⟩
  obtain ⟨art, hart⟩ := HG E' Ω
  set u := a' (ineIncl h' ⟨t', ht'⟩) with hu_def
  have hu : IsUnitAt w' u := GlobalTheory.T.localArtin_inertia_isUnitAt h' a' ha' ⟨t', ht'⟩
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_integer_approx_unit_adicCompletion w' u hu
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hg2 : 2 ≤ g := (Fact.out : g.Prime).two_le
  have hq : 0 < g ^ n - 1 := by
    have : 2 ≤ g ^ n := le_trans hg2 (Nat.le_self_pow hn.ne' g)
    omega
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq ((g : ℕ) : Ω) hq
  have hy' : y ^ (normV w' - 1) = algebraMap E' Ω ((((g : ℕ) : 𝓞 E')) : E') := by
    rw [hN, hy]; simp
  obtain ⟨σ', hσ'I, hσ'ab, hσ'v⟩ :=
    GlobalTheory.TameRecip.exists_ine_of_unit HG E' Ω art hart w' A h' ((g : ℕ) : 𝓞 E') hg0 hg1 y hy' u x hu hx
  have hab : toAb E' Ω σ' = toAb E' Ω t' := by
    rw [hσ'ab]; exact ha'.glob art hart _
  have hgE : ((g : ℕ) : E') ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero
  have hkum := GlobalTheory.T.kummerCharacter_factors_absoluteGaloisAbelianization E' Ω (g ^ n - 1) hq ζ hζ ((g : ℕ) : E') hgE y (by rw [hy, map_natCast]) σ' t' hab
  have hgΩ : ((g : ℕ) : Ω) ≠ 0 := by
    rw [← map_natCast (algebraMap E' Ω)]; exact (_root_.map_ne_zero _).mpr hgE
  have h1 := hTC n hn y hy
  have h2 : redThrough A κ (algebraMap E' Ω ((x : 𝓞 E') : E')) = L.gen n := by
    rw [← h1]
    have e : t y / y = σ' y / y := by rw [hkum]; rfl
    rw [e]
    exact (redThrough_eq_of_val_sub_lt_one A κ (tameQuot_mem A σ' hq hgΩ hy) hσ'v).symm
  haveI := w'.isMaximal
  letI : Field (𝓞 E' ⧸ w'.asIdeal) := Ideal.Quotient.field _
  have hgK : (((g : ℕ) : 𝓞 E' ⧸ w'.asIdeal)) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w'.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact hg0
  haveI : CharP (𝓞 E' ⧸ w'.asIdeal) g := (CharP.charP_iff_prime_eq_zero (Fact.out : g.Prime)).mpr hgK
  letI : Algebra (ZMod g) (𝓞 E' ⧸ w'.asIdeal) := ZMod.algebra _ g
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_residueField_embedding_place_over E' Ω g A w' h' κ
  have hcard : Nat.card (𝓞 E' ⧸ w'.asIdeal) = g ^ n := hN
  haveI : Finite (𝓞 E' ⧸ w'.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨θ, hreg, ⟨x0, hx0, hθ⟩, hprod⟩ := GlobalTheory.T.exists_regularCharacter_labelRoot_product g L n hn P hP.1 _ hcard ι
  have hιz : ι (Ideal.Quotient.mk _ x) = L.gen n := by rw [hι]; exact h2
  have hgen0 : L.gen n ≠ 0 := by
    intro e
    have ho := L.gen_order n hn
    rw [e, orderOf_eq_zero_iff'.mpr (fun k hk => by simp [zero_pow hk.ne'])] at ho
    omega
  have hz0 : (Ideal.Quotient.mk w'.asIdeal x) ≠ 0 := by
    intro e; rw [e, map_zero] at hιz; exact hgen0 hιz.symm
  set z : (𝓞 E' ⧸ w'.asIdeal)ˣ := Units.mk0 _ hz0 with hz
  have hform : ∀ y' : Gn g n, Irreducible (y' : Mt g n).charpoly → ∀ z' : (𝓞 E' ⧸ w'.asIdeal)ˣ,
      aeval (z' : 𝓞 E' ⧸ w'.asIdeal) (y' : Mt g n).charpoly = 0 →
      τ.character y' = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ (z' ^ g ^ j) : ℂˣ) : ℂ) := by
    intro y' hy' z' hz'
    have hmem : ι z' ∈ Formalism.CyclotomicNorms.rootsBar (y' : Mt g n).charpoly := by
      unfold Formalism.CyclotomicNorms.rootsBar
      rw [Polynomial.mem_roots (Polynomial.map_ne_zero (Matrix.charpoly_monic _).ne_zero), Polynomial.IsRoot.def,
        Polynomial.eval_map]
      have hc : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) = ι.comp (algebraMap (ZMod g) (𝓞 E' ⧸ w'.asIdeal)) :=
        RingHom.ext_zmod _ _
      rw [hc, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hz', map_zero]
    rw [hP.2.2 x0 hx0 y' hy' (ι z') hmem]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hθ, Units.val_pow_eq_pow_val, map_pow]
  have H := (HT E E' Ω g A w h w' h' rc hrc i hi n hn hg1 hN a' ha' (𝓞 E' ⧸ w'.asIdeal) (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective (Ideal.mk_ker) θ hreg τ hP.2.1 hform σ hinf).2 ⟨t', ht'⟩ x z rfl hx
  rw [← hres, H]
  exact hprod z hιz
end GlobalTheory.DepthZeroBridge

end
end
