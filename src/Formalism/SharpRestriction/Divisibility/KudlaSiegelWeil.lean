module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SharpRestriction.ParConsts
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Decomp
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscriminantRealSubfield
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
public import Lemmata.GeneralBFactRightVariant.Imports

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.KudlaSiegelWeil

open NumberField IsDedekindDomain MeasureTheory
open Formalism.BasicNotions (D7 ThetaX)
open Formalism.BasicNotions.TH (tauE)
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev FF (D : D7) : Type := ↥D.host.F

abbrev FinF (D : D7) : Type := HeightOneSpectrum (𝓞 (FF D))

abbrev FinE (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E)

abbrev Pl (D : D7) : Type := FinF D ⊕ D.what₂.Tau

def Over (D : D7) (w : FinE D) (v : FinF D) : Prop :=
  w.asIdeal.comap (algebraMap (𝓞 (FF D)) (𝓞 D.host.E)) = v.asIdeal

def Split (D : D7) (v : FinF D) : Prop :=
  ∃ w w' : FinE D, w ≠ w' ∧ Over D w v ∧ Over D w' v

def InertPlaceConditions (D : D7) : Prop :=
  ∀ v : FinF D, ¬ Split D v →
    (2 : 𝓞 (FF D)) ∉ v.asIdeal ∧ 3 < Ideal.absNorm v.asIdeal ∧
    ¬ differentIdeal ℤ (𝓞 (FF D)) ≤ v.asIdeal ∧
    ∀ w : FinE D, Over D w v → w.valuation D.host.E D.host.xi0 = 1

namespace InertConditionsOfHost

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open scoped Pointwise

section

variable {L : Type} [Field L]

def thP (ζ : L) (m : ℕ) : L := ζ ^ (2 ^ m) + (ζ ^ (2 ^ m))⁻¹

theorem pow_two_pow_add_inv_succ (ζ : L) (hζ : ζ ≠ 0) (m : ℕ) : thP ζ (m + 1) = thP ζ m ^ 2 - 2 := by
  unfold thP
  have h : ζ ^ (2 ^ m) ≠ 0 := pow_ne_zero _ hζ
  rw [pow_succ 2 m, pow_mul]
  field_simp
  ring

theorem pow_two_pow_add_inv_sq_eq_two [CharZero L] (ζ : L) (e : ℕ) (he : 1 ≤ e) (h : IsPrimitiveRoot ζ (2 ^ (e + 2))) :
    thP ζ (e - 1) ^ 2 = 2 := by
  have hζ : ζ ≠ 0 := h.ne_zero (by positivity)
  have h1 : ζ ^ (2 ^ (e + 1)) = -1 := by
    have hsq : (ζ ^ (2 ^ (e + 1))) ^ 2 = 1 := by
      rw [← pow_mul, ← pow_succ]; exact h.pow_eq_one
    have hne : ζ ^ (2 ^ (e + 1)) ≠ 1 := by
      intro h0
      have := h.dvd_of_pow_eq_one _ h0
      have h2 : 2 ^ (e + 2) ≤ 2 ^ (e + 1) := Nat.le_of_dvd (by positivity) this
      have h3 : 2 ^ (e + 1) < 2 ^ (e + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    rcases mul_self_eq_one_iff.mp ((sq _).symm.trans hsq) with h | h
    · exact absurd h hne
    · exact h
  have h2 : thP ζ (e + 1) = -2 := by
    unfold thP; rw [h1]; norm_num
  have h3 : thP ζ e ^ 2 = 0 := by
    have := pow_two_pow_add_inv_succ ζ hζ e
    rw [h2] at this; linear_combination -this
  have h4 : thP ζ e = 0 := by simpa using h3
  have h5 := pow_two_pow_add_inv_succ ζ hζ (e - 1)
  rw [Nat.sub_add_cancel he, h4] at h5
  linear_combination -h5

end

private theorem cycRat (m : ℕ) : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) := by
  convert (inferInstance : @IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) _ _ (CyclotomicField.algebra m ℚ))
  exact Subsingleton.elim _ _

private theorem fix_or_inv {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ)
    (τ : CyclotomicField H.condN ℚ ≃ₐ[ℚ] CyclotomicField H.condN ℚ) (hτ : ∀ x, τ (H.cycEmb x) = H.cycEmb x)
    (ζ : CyclotomicField H.condN ℚ) (hζ : ζ ^ 2 ^ (φ.e + 2) = 1) : τ ζ = ζ ∨ τ ζ = ζ⁻¹ := by
  have : NeZero H.condN := ⟨by have := H.QS_pos; have := H.hyp.1.pos; have := H.hyp.2.1.pos; positivity⟩
  have := cycRat H.condN
  have hdvd : 2 ^ (φ.e + 2) ∣ H.condN := (H.tower_dvd.mul_right _).mul_right _
  have hroot := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq H.condN (CyclotomicField H.condN ℚ) τ
    (x := ζ) (orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_iff_pow_eq_one.2 hζ).trans hdvd))
  have hz := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq H.condN (CyclotomicField H.condN ℚ) τ
    (x := H.cycZeta) H.cycZeta_prim.pow_eq_one
  set u := IsCyclotomicExtension.Rat.galEquivZMod H.condN (CyclotomicField H.condN ℚ) τ
  have h1 : H.art u = 1 := by
    rw [← H.gal.symm.map_eq_one_iff]
    exact AlgEquiv.ext fun x => H.cycEmb.injective ((H.art_spec u τ hz x).trans (hτ x))
  have hv : ((ZMod.unitsMap hdvd u : (ZMod (2 ^ (φ.e + 2)))ˣ) : ZMod (2 ^ (φ.e + 2))) =
      (((u : ZMod H.condN).val : ℕ) : ZMod (2 ^ (φ.e + 2))) := by
    rw [ZMod.unitsMap_val, ZMod.cast_eq_val]
  have h2 := H.art_h u _ hv
  rw [h1, Prod.snd_one, map_one] at h2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ((QuotientGroup.eq_one_iff _).mp h2.symm)
  rw [← hk] at hv
  rw [hroot]
  rcases Int.even_or_odd k with h3 | h3
  · left
    rw [h3.neg_one_zpow, Units.val_one, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff] at hv
    rw [← pow_eq_pow_of_modEq hv hζ, pow_one]
  · right
    rw [h3.neg_one_zpow] at hv
    have h4 : (((u : ZMod H.condN).val + 1 : ℕ) : ZMod (2 ^ (φ.e + 2))) = 0 := by
      rw [Nat.cast_add, ← hv]; simp
    obtain ⟨m, hm⟩ := (ZMod.natCast_eq_zero_iff _ _).1 h4
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, hm, pow_mul, hζ, one_pow]

private theorem exists_sqrt_two_E {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) : ∃ s : H.E, s ^ 2 = 2 := by
  have hN : H.condN ≠ 0 := by have := H.QS_pos; have := H.hyp.1.pos; have := H.hyp.2.1.pos; positivity
  have : NeZero H.condN := ⟨hN⟩
  have := cycRat H.condN
  have : IsGalois ℚ (CyclotomicField H.condN ℚ) := IsCyclotomicExtension.isGalois {H.condN} ℚ _
  obtain ⟨k, hk⟩ : 2 ^ (φ.e + 2) ∣ H.condN := (H.tower_dvd.mul_right _).mul_right _
  have hζ : IsPrimitiveRoot (H.cycZeta ^ k) (2 ^ (φ.e + 2)) :=
    H.cycZeta_prim.pow (Nat.pos_of_ne_zero hN) (hk.trans (mul_comm _ _))
  have he : 1 ≤ φ.e := le_trans (by norm_num) H.two_le_e
  have h2 := pow_two_pow_add_inv_sq_eq_two _ _ he hζ
  let _ : Algebra H.E (CyclotomicField H.condN ℚ) := H.cycEmb.toRingHom.toAlgebra
  have : IsScalarTower ℚ H.E (CyclotomicField H.condN ℚ) :=
    IsScalarTower.of_algebraMap_eq fun x => (H.cycEmb.commutes x).symm
  have : IsGalois H.E (CyclotomicField H.condN ℚ) := IsGalois.tower_top_of_isGalois ℚ H.E _
  have : FiniteDimensional H.E (CyclotomicField H.condN ℚ) := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨s, hs⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := H.E) (thP (H.cycZeta ^ k) (φ.e - 1))).2 (by
    intro τ
    have h3 : τ (H.cycZeta ^ k) = H.cycZeta ^ k ∨ τ (H.cycZeta ^ k) = (H.cycZeta ^ k)⁻¹ :=
      fix_or_inv H (τ.restrictScalars ℚ) (fun x => τ.commutes x) _ hζ.pow_eq_one
    generalize H.cycZeta ^ k = z at h3 ⊢
    rw [thP, map_add (f := _), map_inv₀, map_pow]
    rcases h3 with h | h
    · rw [h]
    · rw [h, inv_pow, inv_inv, add_comm])
  refine ⟨s, (algebraMap H.E (CyclotomicField H.condN ℚ)).injective ?_⟩
  rw [map_pow, map_ofNat, hs, h2]

theorem exists_sqrt_two (D : D7) : ∃ s : 𝓞 (FF D), s ^ 2 = 2 := by
  obtain ⟨t, htE⟩ := exists_sqrt_two_E D.host.toHostRaw
  have hF : t ∈ D.host.F := by
    rw [mem_maximalRealSubfield_iff]
    intro ψ
    have h1 : (ψ t) ^ 2 = ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 := by
      rw [← map_pow, htE, map_ofNat, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; rfl
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h <;> rw [h] <;> simp
  have htF : (⟨t, hF⟩ : FF D) ^ 2 = 2 := by
    apply D.host.F.subtype.injective
    rw [map_pow, map_ofNat]; exact htE
  have hint : IsIntegral ℤ (⟨t, hF⟩ : FF D) :=
    ⟨Polynomial.X ^ 2 - 2, by monicity!, by simp [htF]⟩
  refine ⟨IsIntegralClosure.mk' (𝓞 (FF D)) _ hint, ?_⟩
  apply RingOfIntegers.coe_injective
  rw [map_pow, map_ofNat, IsIntegralClosure.algebraMap_mk']; exact htF

theorem three_lt_absNorm (D : D7) (v : FinF D) (h2 : (2 : 𝓞 (FF D)) ∉ v.asIdeal) :
    3 < Ideal.absNorm v.asIdeal := by
  by_contra hle
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  have hm := Ideal.absNorm_mem v.asIdeal
  have h2' : Ideal.absNorm v.asIdeal ≠ 2 := by
    intro h; rw [h] at hm; exact h2 (by exact_mod_cast hm)
  have h3 : Ideal.absNorm v.asIdeal = 3 := by omega
  rw [h3] at hm
  obtain ⟨s, hs⟩ := exists_sqrt_two D
  have hcard : Nat.card (𝓞 (FF D) ⧸ v.asIdeal) = 3 := by
    rw [← h3, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : v.asIdeal.IsMaximal := v.isMaximal
  let _ := Ideal.Quotient.field v.asIdeal
  have : Finite (𝓞 (FF D) ⧸ v.asIdeal) := Nat.finite_of_card_ne_zero (by omega)
  let _ := Fintype.ofFinite (𝓞 (FF D) ⧸ v.asIdeal)
  have hx3 := FiniteField.pow_card (Ideal.Quotient.mk v.asIdeal s)
  rw [← Nat.card_eq_fintype_card, hcard] at hx3
  have hx2 : (Ideal.Quotient.mk v.asIdeal s) ^ 2 = 2 := by
    rw [← map_pow, hs, map_ofNat]
  have h3K : (3 : 𝓞 (FF D) ⧸ v.asIdeal) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.mpr hm
    rw [Nat.cast_ofNat, map_ofNat] at this
    exact this
  have hx0 : Ideal.Quotient.mk v.asIdeal s = 0 := by
    linear_combination hx3 - (Ideal.Quotient.mk v.asIdeal s) * hx2
  have : (1 : 𝓞 (FF D) ⧸ v.asIdeal) = 0 := by
    linear_combination h3K + hx2 - (Ideal.Quotient.mk v.asIdeal s) * hx0
  exact one_ne_zero this

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [D.host.conjE_apply, D.host.conjE_apply]
  simp

theorem conj_b (D : D7) : D.host.conj (D.host.sqd) = -D.host.sqd := by
  rw [D.host.galE_bE, D.host.galE_conjE]
  simp [Formalism.HC.Frame.cc, c0]

theorem b_sq (D : D7) : D.host.sqd ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq

def sgO (D : D7) : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom D.host.conj

theorem sgO_coe (D : D7) (x : 𝓞 D.host.E) : ((sgO D x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := rfl

theorem sgO_sgO (D : D7) (x : 𝓞 D.host.E) : sgO D (sgO D x) = x := by
  apply RingOfIntegers.ext; rw [sgO_coe, sgO_coe, conj_conj]

theorem sgO_F (D : D7) (x : 𝓞 (FF D)) :
    sgO D (algebraMap (𝓞 (FF D)) (𝓞 D.host.E) x) = algebraMap (𝓞 (FF D)) (𝓞 D.host.E) x := by
  apply RingOfIntegers.ext; rw [sgO_coe]
  exact (D.host.conjE_mem_hostF_iff (x : FF D).1).1 (x : FF D).2

theorem algFE_inj (D : D7) : Function.Injective (algebraMap (𝓞 (FF D)) (𝓞 D.host.E)) :=
  FaithfulSMul.algebraMap_injective _ _

theorem exists_over (D : D7) (v : FinF D) : ∃ w : FinE D, Over D w v := by
  obtain ⟨Q, -, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal
    (⊥ : Ideal (𝓞 D.host.E)) (by rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ (algFE_inj D))]; exact bot_le)
  have hQne : Q ≠ ⊥ := by
    intro h; rw [h, (show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ (algFE_inj D))] at hQ; exact v.ne_bot hQ.symm
  exact ⟨⟨Q, hQp, hQne⟩, hQ⟩

theorem fixed_of_not_split (D : D7) (v : FinF D) (hv : ¬ Split D v) (w : FinE D) (hw : Over D w v) :
    w.asIdeal.comap (sgO D) = w.asIdeal := by
  by_contra hne
  apply hv
  have hne' : w.asIdeal.comap (sgO D) ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    intro h
    have h1 : sgO D x ∈ w.asIdeal.comap (sgO D) := by rw [Ideal.mem_comap, sgO_sgO]; exact hx
    rw [h, Ideal.mem_bot] at h1
    apply hx0; rw [← sgO_sgO D x, h1, map_zero]
  have := w.isPrime
  refine ⟨w, ⟨w.asIdeal.comap (sgO D), Ideal.comap_isPrime (sgO D) w.asIdeal, hne'⟩, ?_, hw, ?_⟩
  · intro h
    exact hne (congrArg HeightOneSpectrum.asIdeal h).symm
  · show (w.asIdeal.comap (sgO D)).comap (algebraMap (𝓞 (FF D)) (𝓞 D.host.E)) = v.asIdeal
    rw [Ideal.comap_comap, show (sgO D).comp (algebraMap (𝓞 (FF D)) (𝓞 D.host.E)) = algebraMap _ _ from
      RingHom.ext (sgO_F D)]
    exact hw

theorem one_mem_of_coprime {R : Type*} [CommRing R] (P : Ideal R) {m n : ℕ} (h : Nat.Coprime m n)
    (hm : (m : R) ∈ P) (hn : (n : R) ∈ P) : (1 : R) ∈ P := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr h
  have : ((a : R) * m + (b : R) * n) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → R) hab
  rw [← this]
  exact P.add_mem (P.mul_mem_left _ hm) (P.mul_mem_left _ hn)

theorem exists_prime_mem {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime] (n : ℕ) :
    n ≠ 0 → (n : R) ∈ P → ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : R) ∈ P := by
  first | exact Bl.general_b_fact_right_variant.goal1 .. | (apply Bl.general_b_fact_right_variant.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_variant.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_variant.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right_variant.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_variant.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_right_variant.goal1 R ‹_› P hP n ‹_› ‹_› | exact @Bl.general_b_fact_right_variant.goal1 R ‹_› P hP n ‹_› | exact @Bl.general_b_fact_right_variant.goal1 R ‹_› P hP n | exact @Bl.general_b_fact_right_variant.goal1 R ‹_› P hP | exact @Bl.general_b_fact_right_variant.goal1 R ‹_› P | exact @Bl.general_b_fact_right_variant.goal1 R ‹_› | exact @Bl.general_b_fact_right_variant.goal1 R

theorem not_fixed_condN (D : D7) (w : FinE D) (p : ℕ) (hpp : p.Prime) (hp : p ∣ D.host.condN)
    (hpw : (p : 𝓞 D.host.E) ∈ w.asIdeal) : w.asIdeal.comap (sgO D) ≠ w.asIdeal := by
  intro hfix
  have := w.isPrime
  have hlo : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
    constructor
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hpp).irreducible
    refine hmax.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) ?_
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    simpa using hpw
  apply D.host.der.decompConj p hpp hp w.asIdeal
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have hx : ((D.host.conj)⁻¹ • x : 𝓞 D.host.E) = sgO D x := by
    apply RingOfIntegers.ext
    rw [sgO_coe]
    show (D.host.conj).symm (x : D.host.E) = D.host.conj (x : D.host.E)
    rw [AlgEquiv.symm_apply_eq, conj_conj]
  rw [hx, ← Ideal.mem_comap, hfix]

theorem not_fixed_ram (D : D7) (w : FinE D) (p : ℕ) (hp : p = 2 ∨ p = D.host.q ∨ p = D.host.d)
    (hpw : (p : 𝓞 D.host.E) ∈ w.asIdeal) : w.asIdeal.comap (sgO D) ≠ w.asIdeal := by
  rcases hp with h | h | h <;> subst h
  · exact not_fixed_condN D w 2 Nat.prime_two
      ((((dvd_pow_self 2 (by omega)).trans D.host.tower_dvd).mul_right _).mul_right _) hpw
  · exact not_fixed_condN D w _ D.host.hyp.1 ((dvd_mul_left _ _).mul_right _) hpw
  · exact not_fixed_condN D w _ D.host.hyp.2.1 (dvd_mul_left _ _) hpw

theorem exists_bO (D : D7) : ∃ β : 𝓞 D.host.E,
    algebraMap (𝓞 D.host.E) D.host.E β = D.host.sqd ∧
    β ^ 2 = -(D.host.d : 𝓞 D.host.E) ∧ sgO D β = -β := by
  have hint : IsIntegral ℤ (D.host.sqd) :=
    ⟨Polynomial.X ^ 2 + Polynomial.C (D.host.d : ℤ), by monicity!, by simp [b_sq D]⟩
  have hβ : algebraMap (𝓞 D.host.E) D.host.E (IsIntegralClosure.mk' (𝓞 D.host.E) _ hint) =
      D.host.sqd := IsIntegralClosure.algebraMap_mk' _ _ _
  refine ⟨IsIntegralClosure.mk' (𝓞 D.host.E) _ hint, hβ, ?_, ?_⟩
  · apply RingOfIntegers.coe_injective
    rw [map_pow, map_neg, map_natCast, hβ, b_sq]
  · apply RingOfIntegers.coe_injective
    rw [map_neg, hβ, ← conj_b]
    exact (sgO_coe D _).trans (congrArg D.host.conj hβ)

theorem not_fixed_splitK (D : D7) (w : FinE D) (p : ℕ) (hpp : p.Prime) (hp2 : p ≠ 2)
    (hj : jacobiSym (-(D.host.d : ℤ)) p = 1) (hpw : (p : 𝓞 D.host.E) ∈ w.asIdeal) :
    w.asIdeal.comap (sgO D) ≠ w.asIdeal := by
  intro hfix
  have hone : (1 : 𝓞 D.host.E) ∉ w.asIdeal := fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have : Fact p.Prime := ⟨hpp⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym] at hj
  have h0 : ((-(D.host.d : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    intro h; rw [(legendreSym.eq_zero_iff p _).2 h] at hj; exact zero_ne_one hj
  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff p h0).1 hj
  obtain ⟨x, rfl⟩ := ZMod.intCast_surjective r
  have hdvd : (p : ℤ) ∣ x * x + D.host.d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hr ⊢
    linear_combination -hr
  obtain ⟨m, hm⟩ := hdvd
  obtain ⟨β, hβ, hβ2, hσβ⟩ := exists_bO D
  have hprod : ((x : 𝓞 D.host.E) + β) * ((x : 𝓞 D.host.E) - β) ∈ w.asIdeal := by
    have : ((x : 𝓞 D.host.E) + β) * ((x : 𝓞 D.host.E) - β) = (p : 𝓞 D.host.E) * (m : 𝓞 D.host.E) := by
      have h1 : ((x * x + D.host.d : ℤ) : 𝓞 D.host.E) = ((p * m : ℤ) : 𝓞 D.host.E) := congrArg _ hm
      push_cast at h1
      linear_combination h1 - hβ2
    rw [this]; exact w.asIdeal.mul_mem_right _ hpw
  have hswap : ∀ y, y ∈ w.asIdeal → sgO D y ∈ w.asIdeal := by
    intro y hy; rw [← hfix] at hy; exact hy
  have hσ1 : sgO D ((x : 𝓞 D.host.E) + β) = (x : 𝓞 D.host.E) - β := by
    rw [map_add (f := _), map_intCast, hσβ]; ring
  have hσ2 : sgO D ((x : 𝓞 D.host.E) - β) = (x : 𝓞 D.host.E) + β := by
    rw [map_sub, map_intCast, hσβ]; ring
  have hboth : (x : 𝓞 D.host.E) + β ∈ w.asIdeal ∧ (x : 𝓞 D.host.E) - β ∈ w.asIdeal := by
    rcases w.isPrime.mem_or_mem hprod with h | h
    · exact ⟨h, hσ1 ▸ hswap _ h⟩
    · exact ⟨hσ2 ▸ hswap _ h, h⟩
  have h2β : ((2 : ℕ) : 𝓞 D.host.E) * β ∈ w.asIdeal := by
    have : ((2 : ℕ) : 𝓞 D.host.E) * β = ((x : 𝓞 D.host.E) + β) - ((x : 𝓞 D.host.E) - β) := by
      push_cast; ring
    rw [this]; exact w.asIdeal.sub_mem hboth.1 hboth.2
  rcases w.isPrime.mem_or_mem h2β with h | h
  · exact hone (one_mem_of_coprime _ ((Nat.coprime_primes hpp Nat.prime_two).2 hp2) hpw h)
  · have hd : (D.host.d : 𝓞 D.host.E) ∈ w.asIdeal := by
      have : (D.host.d : 𝓞 D.host.E) = -(β * β) := by linear_combination hβ2
      rw [this]; exact w.asIdeal.neg_mem (w.asIdeal.mul_mem_left _ h)
    refine hone (one_mem_of_coprime _ ((Nat.coprime_primes hpp D.host.hyp.2.1).2 ?_) hpw hd)
    intro hpd
    apply h0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hpd]
    exact dvd_neg.2 dvd_rfl

theorem mem_of_over (D : D7) {w : FinE D} {v : FinF D} (hw : Over D w v) (n : ℕ) :
    (n : 𝓞 (FF D)) ∈ v.asIdeal → (n : 𝓞 D.host.E) ∈ w.asIdeal := by
  intro h
  rw [← hw, Ideal.mem_comap, map_natCast] at h
  exact h

theorem val_eq_one (D : D7) (w : FinE D) (x : 𝓞 D.host.E) (hx : x ∉ w.asIdeal) :
    w.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E x) = 1 := by
  refine le_antisymm (w.valuation_le_one x) (not_lt.1 ?_)
  rw [HeightOneSpectrum.valuation_lt_one_iff_mem]; exact hx

end InertConditionsOfHost

open InertConditionsOfHost Formalism.FrobeniusOrbits in
theorem inert_conditions_hold (D : D7) : InertPlaceConditions D := by
  intro v hv
  obtain ⟨w0, hw0⟩ := exists_over D v
  have hfix0 := fixed_of_not_split D v hv w0 hw0
  have h2 : (2 : 𝓞 (FF D)) ∉ v.asIdeal := by
    intro h
    exact not_fixed_ram D w0 2 (Or.inl rfl) (mem_of_over D hw0 2 (by exact_mod_cast h)) hfix0
  refine ⟨h2, three_lt_absNorm D v h2, ?_, ?_⟩
  · intro hle
    have hdv : Ideal.absNorm v.asIdeal ∣ (discr (FF D)).natAbs := by
      rw [← absNorm_differentIdeal (K := FF D) (𝒪 := 𝓞 (FF D))]
      exact Ideal.absNorm_dvd_absNorm_of_le hle
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    have := v.isPrime
    obtain ⟨p, hpp, hpd, hpv⟩ := exists_prime_mem v.asIdeal _ h0 (Ideal.absNorm_mem v.asIdeal)
    have hp3 : p ∣ D.host.condN := by
      refine D.host.der.discr_primes.1 p hpp ?_
      rw [D.host.der.discr_sq]
      exact (Int.natCast_dvd.2 (hpd.trans hdv)).trans (dvd_pow_self _ two_ne_zero)
    exact not_fixed_condN D w0 p hpp hp3 (mem_of_over D hw0 p hpv) hfix0
  · intro w hw
    have hfix := fixed_of_not_split D v hv w hw
    obtain ⟨β, hβ, hβ2, -⟩ := exists_bO D
    have hβw : β ∉ w.asIdeal := by
      intro h
      have hd : (D.host.d : 𝓞 D.host.E) ∈ w.asIdeal := by
        have : (D.host.d : 𝓞 D.host.E) = -(β * β) := by linear_combination hβ2
        rw [this]; exact w.asIdeal.neg_mem (w.asIdeal.mul_mem_left _ h)
      exact not_fixed_ram D w _ (Or.inr (Or.inr rfl)) hd hfix
    have hNw : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
      intro h
      have hN0 : Ideal.absNorm D.host.ccK ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
      have := w.isPrime
      obtain ⟨p, hpp, hpd, hpw⟩ := exists_prime_mem w.asIdeal _ hN0 h
      have hp2 : p ≠ 2 := by
        intro h2'
        have hc := D.host.ccK_coprime 2 (by simp)
        rw [h2'] at hpd
        exact absurd (Nat.Coprime.eq_one_of_dvd hc.symm hpd) (by norm_num)
      obtain ⟨P, hP, hPle, hpP⟩ : ∃ P : Ideal (𝓞 D.host.K), P.IsPrime ∧ D.host.ccK ≤ P ∧ p ∣ Ideal.absNorm P := by
        have hfac := Ideal.prod_normalizedFactors_eq_self D.host.ccK_ne_bot
        rw [← hfac, map_multiset_prod] at hpd
        obtain ⟨n, hn, hpn⟩ := (Nat.prime_iff.1 hpp).exists_mem_multiset_dvd hpd
        obtain ⟨P, hPm, rfl⟩ := Multiset.mem_map.1 hn
        exact ⟨P, Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_normalized_factor P hPm),
          Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hPm), hpn⟩
      obtain ⟨hNp, hj⟩ := D.host.ccK_split P hP hPle
      have hpe : p = Ideal.absNorm P := (Nat.prime_dvd_prime_iff_eq hpp hNp).1 hpP
      rw [← hpe] at hj
      exact not_fixed_splitK D w p hpp hp2 hj hpw hfix
    have e1 := val_eq_one D w β hβw
    have e2 := val_eq_one D w _ hNw
    rw [hβ] at e1
    rw [map_natCast] at e2
    rw [Formalism.BasicNotions.Host.xi0, Formalism.BasicNotions.Host.sqrtMinusD, map_div₀, Valuation.map_neg, map_one, map_mul, e2, e1]
    simp

def Restr {ι : Type} {M : ι → Type} (s : ∀ i, M i) (φ : ∀ i, M i) : Prop := {i | φ i ≠ s i}.Finite

attribute [instance] LocW.chrFG LocW.gG LocW.gM LocW.hL LocW.schLA LocW.schLM

variable {D : D7} {T : ThetaX D}

attribute [instance] LocP.piA LocP.piM LocP.piGA LocP.piGM

namespace Sett

variable {Lc : Loc D T} (S : Sett D T Lc)

end Sett

namespace Sett

variable {Lc : Loc D T} (S : Sett D T Lc)

end Sett

end Formalism.MainNotions.KudlaSiegelWeil
