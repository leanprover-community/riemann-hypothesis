import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrobFixOfEisenstein
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets

section
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory

theorem frob_inv_mul_mem_inertia : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ τ τ' : G E Ω, IsFrob (F := E) A (normV v) τ →
    IsFrob (F := E) A (normV v) τ' → τ'⁻¹ * τ ∈ Ine (F := E) A := by
  intro E Ω _ _ _ _ v A hA τ τ' hτ hτ'
  obtain ⟨hτD, hτF⟩ := hτ
  obtain ⟨hτ'D, hτ'F⟩ := hτ'

  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 E ⧸ v.asIdeal) := inferInstance
  letI : Fintype (𝓞 E ⧸ v.asIdeal) := Fintype.ofFinite _
  set p := ringChar (𝓞 E ⧸ v.asIdeal) with hpdef
  haveI : CharP (𝓞 E ⧸ v.asIdeal) p := ringChar.charP _
  obtain ⟨n, hp, hcard⟩ := FiniteField.card (𝓞 E ⧸ v.asIdeal) p
  have hq : normV v = p ^ (n : ℕ) := by
    simp only [normV, Nat.card_eq_fintype_card, hcard]

  have hpv : ((p : 𝓞 E)) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ p
  have hpA : A.valuation (p : Ω) < 1 := by
    have := (hA (p : 𝓞 E)).mpr hpv
    simpa using this

  have hpk : ((p : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff]
    simpa using hpA
  haveI : CharP (IsLocalRing.ResidueField A) p := by
    have h := CharP.ringChar_of_prime_eq_zero (R := IsLocalRing.ResidueField A) hp hpk
    rw [← h]; exact ringChar.charP _
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : ExpChar (IsLocalRing.ResidueField A) p := ExpChar.prime hp
  refine ⟨(Dec (F := E) A).mul_mem ((Dec (F := E) A).inv_mem hτ'D) hτD, fun x hx => ?_⟩
  have hxA : x ∈ A := A.valuation_le_one_iff x |>.mp hx
  set z := (τ'⁻¹ : G E Ω) (τ x) with hz
  have hzA : z ∈ A := by
    rw [hz, apply_mem_iff_of_mem_Dec ((Dec (F := E) A).inv_mem hτ'D), apply_mem_iff_of_mem_Dec hτD]
    exact hxA
  have hτ'z : τ' z = τ x := mul_inv_apply (τ x)
  have h1 := hτ'F z ((A.valuation_le_one_iff z).mpr hzA)
  rw [hτ'z] at h1
  have h2 := hτF x hx
  have h3 : A.valuation (z ^ normV v - x ^ normV v) < 1 := by
    have e : z ^ normV v - x ^ normV v = (τ x - x ^ normV v) - (τ x - z ^ normV v) := by ring
    rw [e]; exact Valuation.map_sub_lt _ h2 h1

  have hres : IsLocalRing.residue A ⟨z, hzA⟩ ^ (p ^ (n : ℕ)) = IsLocalRing.residue A ⟨x, hxA⟩ ^ (p ^ (n : ℕ)) := by
    rw [← sub_eq_zero, ← map_pow, ← map_pow, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff]
    rw [← hq]
    simpa using h3
  have hinj := iterateFrobenius_inj (IsLocalRing.ResidueField A) p (n : ℕ)
  have heq : IsLocalRing.residue A ⟨z, hzA⟩ = IsLocalRing.residue A ⟨x, hxA⟩ := by
    apply hinj
    rw [iterateFrobenius_def, iterateFrobenius_def]
    exact hres
  have hzx : (⟨z, hzA⟩ - ⟨x, hxA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, heq, sub_self]
  have := (ValuationSubring.valuation_lt_one_iff A _).mp hzx
  have e2 : (τ'⁻¹ * τ) x = z := rfl
  rw [e2]
  simpa using this

end GlobalTheory
end

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_inv_mul_mem_inertia : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ τ τ' : G E Ω, IsFrob (F := E) A (normV v) τ →
    IsFrob (F := E) A (normV v) τ' → τ'⁻¹ * τ ∈ Ine (F := E) A := by
  atlas_forward_decl GlobalTheory.frob_inv_mul_mem_inertia
end

section
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.TameRatio

theorem ratio_cong : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ u : 𝓞 E, u ∉ v.asIdeal → ∀ π t : Ω, π ≠ 0 →
    t ^ (normV v - 1) = algebraMap E Ω (u : E) → ∀ τ τ' : G E Ω, IsFrob (F := E) A (normV v) τ →
    IsFrob (F := E) A (normV v) τ' → τ π = π → τ' (π * t) = π * t →
    A.valuation ((τ'⁻¹ * τ) π / π - algebraMap E Ω (u : E)) < 1 := by
  intro E Ω _ _ _ _ v A hA u hu π t hπ ht τ τ' _hτ hτ' h1 h2
  have hq1 : 1 < normV v := by
    unfold normV
    have : Nontrivial (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top
    have : Finite (𝓞 E ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
    exact Finite.one_lt_card
  set U : Ω := algebraMap E Ω (u : E) with hUdef
  have hint : IsIntegral ℤ U := (RingOfIntegers.isIntegral_coe u).map ((algebraMap E Ω).toIntAlgHom)
  have hUle : A.valuation U ≤ 1 :=
    (Valuation.valuationSubring.integers A.valuation).isIntegral_iff_v_le_one.mp (IsIntegral.tower_top hint)
  have hU1 : A.valuation U = 1 := le_antisymm hUle (not_lt.mp fun h => hu ((hA u).mp h))
  set s : Ω := τ'⁻¹ t with hsdef
  have hs : τ' s = t := by
    show τ' (τ'⁻¹ t) = t
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have hsn : s ^ (normV v - 1) = U := by
    show (τ'⁻¹ t) ^ (normV v - 1) = U
    rw [← map_pow, ht, hUdef, AlgEquiv.commutes]
  have hvs : A.valuation s = 1 := by
    have h : A.valuation s ^ (normV v - 1) = 1 := by rw [← map_pow, hsn, hU1]
    exact (pow_eq_one_iff.mp h).resolve_right (by omega)
  have hs0 : s ≠ 0 := by
    intro h; rw [h, map_zero] at hvs; exact zero_ne_one hvs
  have hF : A.valuation (t - s ^ normV v) < 1 := by
    have := hτ'.2 s hvs.le
    rwa [hs] at this
  have hinv : τ'⁻¹ π * s = π * t := by
    rw [hsdef, ← map_mul]
    calc τ'⁻¹ (π * t) = τ'⁻¹ (τ' (π * t)) := by rw [h2]
      _ = π * t := by rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hrat : (τ'⁻¹ * τ) π = τ'⁻¹ π := by rw [AlgEquiv.mul_apply, h1]
  have hqs : s ^ normV v = U * s := by
    rw [← hsn, ← pow_succ]; congr 1; omega
  have key : (τ'⁻¹ * τ) π / π - U = (t - s ^ normV v) / s := by
    rw [hrat, hqs]
    have e : τ'⁻¹ π = π * t / s := by rw [eq_div_iff hs0, hinv]
    rw [e]
    field_simp
  rw [key, map_div₀, hvs, div_one]
  exact hF

end GlobalTheory.TameRatio
end

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_ratio_pi_congr_tame_unit : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ u : 𝓞 E, u ∉ v.asIdeal → ∀ π t : Ω, π ≠ 0 →
    t ^ (normV v - 1) = algebraMap E Ω (u : E) → ∀ τ τ' : G E Ω, IsFrob (F := E) A (normV v) τ →
    IsFrob (F := E) A (normV v) τ' → τ π = π → τ' (π * t) = π * t →
    A.valuation ((τ'⁻¹ * τ) π / π - algebraMap E Ω (u : E)) < 1 := by
  atlas_forward_decl GlobalTheory.TameRatio.ratio_cong
end

section
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.OneUnitRoot

open IsDedekindDomain.HeightOneSpectrum IsLocalRing Polynomial

theorem exists_unit_pow_normV_sub_one (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E))
    (y : (v.adicCompletion E)ˣ) (hy : Valued.v ((y : v.adicCompletion E) - 1) < 1) :
    ∃ z : (v.adicCompletion E)ˣ, Valued.v (z : v.adicCompletion E) = 1 ∧ z ^ (normV v - 1) = y := by
  have hc := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  set n := normV v - 1 with hn
  have hcard : Nat.card (ResidueField (v.adicCompletionIntegers E)) = normV v :=
    Formalism.UG.P.tjcosets_card_residue v
  haveI : Finite (ResidueField (v.adicCompletionIntegers E)) :=
    GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  haveI := Fintype.ofFinite (ResidueField (v.adicCompletionIntegers E))
  have hq0 : ((normV v : ℕ) : ResidueField (v.adicCompletionIntegers E)) = 0 := by
    rw [← hcard, Nat.card_eq_fintype_card]; exact FiniteField.cast_card_eq_zero _
  have hq1 : 2 ≤ normV v := by
    rw [← hcard]; exact Finite.one_lt_card
  have hnres : ((n : ℕ) : ResidueField (v.adicCompletionIntegers E)) = -1 := by
    rw [hn, Nat.cast_sub (by omega), hq0]; simp
  have hnpos : 0 < n := by omega

  have hy1 : Valued.v (y : v.adicCompletion E) = 1 := by
    have e : (y : v.adicCompletion E) = ((y : v.adicCompletion E) - 1) + 1 := by ring
    rw [e, Valuation.map_add_eq_of_lt_right]
    · exact map_one _
    · rwa [map_one]
  set y' : v.adicCompletionIntegers E := ⟨y, by
    show Valued.v (y : v.adicCompletion E) ≤ 1; exact hy1.le⟩
  have hm : (X ^ n - C y' : (v.adicCompletionIntegers E)[X]).Monic := monic_X_pow_sub_C y' hnpos.ne'
  have hev : eval 1 (X ^ n - C y' : (v.adicCompletionIntegers E)[X]) ∈ maximalIdeal (v.adicCompletionIntegers E) := by
    simp only [eval_sub, eval_pow, eval_X, one_pow, eval_C]
    rw [← neg_sub, Ideal.neg_mem_iff, mem_maximalIdeal, mem_nonunits_iff,
      adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact ne_of_lt hy
  have hder : IsUnit (eval 1 (derivative (X ^ n - C y' : (v.adicCompletionIntegers E)[X]))) := by
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
    rw [← isUnit_map_iff (residue (v.adicCompletionIntegers E)), map_natCast, hnres]
    exact isUnit_one.neg
  obtain ⟨r, hr, hr1⟩ := HenselianRing.is_henselian (I := maximalIdeal (v.adicCompletionIntegers E))
    _ hm 1 hev (hder.map _)
  have hrn : r ^ n = y' := by
    have := hr
    simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C] at this
    exact sub_eq_zero.1 this
  have hrv : Valued.v (r : v.adicCompletion E) = 1 := by
    have h1 : Valued.v ((r : v.adicCompletion E) - 1) < 1 := by
      have := hr1
      rw [mem_maximalIdeal, mem_nonunits_iff, adicCompletionIntegers.isUnit_iff_valued_eq_one] at this
      exact lt_of_le_of_ne (r - 1).2 this
    have e : (r : v.adicCompletion E) = ((r : v.adicCompletion E) - 1) + 1 := by ring
    rw [e, Valuation.map_add_eq_of_lt_right]
    · exact map_one _
    · rwa [map_one]
  have hr0 : (r : v.adicCompletion E) ≠ 0 := by
    intro h; rw [h, map_zero] at hrv; exact zero_ne_one hrv
  refine ⟨Units.mk0 _ hr0, hrv, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.val_mk0]
  exact congrArg Subtype.val hrn

end GlobalTheory.OneUnitRoot
end
end

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_pow_normV_sub_one' : ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (y : (v.adicCompletion E)ˣ),
    Valued.v ((y : v.adicCompletion E) - 1) < 1 →
    ∃ z : (v.adicCompletion E)ˣ, Valued.v (z : v.adicCompletion E) = 1 ∧ z ^ (normV v - 1) = y := by
  atlas_forward_decl GlobalTheory.OneUnitRoot.exists_unit_pow_normV_sub_one
end

section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory

theorem eq_one_of_pow_eq_one_of_val_sub_lt {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {n : ℕ}
    (hn : A.valuation (n : Ω) = 1) {ξ : Ω} (hξ : ξ ^ n = 1) (h1 : A.valuation (ξ - 1) < 1) : ξ = 1 := by
  by_contra hne
  have hξA : A.valuation ξ ≤ 1 := by
    have : ξ = (ξ - 1) + 1 := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le h1.le (by simp))
  have hS : (∑ k ∈ Finset.range n, ξ ^ k) = 0 := by
    have h := geom_sum_mul ξ n
    rw [hξ, sub_self] at h
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hne
  have hsum : (n : Ω) = ∑ k ∈ Finset.range n, (1 - ξ ^ k) := by
    rw [Finset.sum_sub_distrib, hS]; simp
  have hlt : A.valuation (n : Ω) < 1 := by
    rw [hsum]
    refine Valuation.map_sum_lt _ one_ne_zero fun k _ => ?_
    have e : 1 - ξ ^ k = -((∑ j ∈ Finset.range k, ξ ^ j) * (ξ - 1)) := by
      rw [geom_sum_mul]; ring
    rw [e, Valuation.map_neg, Valuation.map_mul]
    have hs : A.valuation (∑ j ∈ Finset.range k, ξ ^ j) ≤ 1 :=
      Valuation.map_sum_le _ fun j _ => by rw [Valuation.map_pow]; exact pow_le_one' hξA j
    calc A.valuation (∑ j ∈ Finset.range k, ξ ^ j) * A.valuation (ξ - 1)
        ≤ 1 * A.valuation (ξ - 1) := by gcongr
      _ < 1 := by rw [one_mul]; exact h1
  rw [hn] at hlt
  exact lt_irrefl _ hlt

theorem val_eq_one_of_pow_eq_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {n : ℕ} (hn0 : n ≠ 0)
    {ζ : Ω} (hζ : ζ ^ n = 1) : A.valuation ζ = 1 := by
  have h : A.valuation ζ ^ n = 1 := by rw [← Valuation.map_pow, hζ, Valuation.map_one]
  exact valuation_eq_one_of_pow_eq_one A hn0 hζ

theorem ine_pow_normV_sub_one_apply_of_pow_mem : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (w : E) (π : Ω), π ^ (normV v - 1) = algebraMap E Ω w →
    ∀ ρ ∈ Ine (F := E) A, (ρ ^ (normV v - 1)) π = π := by
  intro E Ω _ _ _ _ v A hA w π hπ ρ hρ
  set n := normV v - 1 with hn_def
  rcases eq_or_ne n 0 with hn0 | hn0
  · rw [hn0, pow_zero]; rfl
  rcases eq_or_ne π 0 with hπ0 | hπ0
  · rw [hπ0, map_zero]

  have hq1 : 1 ≤ normV v := by omega
  have hqv : ((normV v : ℕ) : 𝓞 E) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    show ((Nat.card (𝓞 E ⧸ v.asIdeal) : ℕ) : 𝓞 E ⧸ v.asIdeal) = 0
    rcases finite_or_infinite (𝓞 E ⧸ v.asIdeal) with hf | hf
    · haveI := Fintype.ofFinite (𝓞 E ⧸ v.asIdeal)
      rw [Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _
    · rw [Nat.card_eq_zero_of_infinite]; simp
  have hqA : A.valuation ((normV v : ℕ) : Ω) < 1 := by
    have := (hA _).mpr hqv
    simpa using this
  have hnA : A.valuation (n : Ω) = 1 := by
    rw [hn_def, Nat.cast_sub hq1, Nat.cast_one, Valuation.map_sub_swap]
    exact Valuation.map_one_sub_of_lt _ hqA

  have hρπ : (ρ π) ^ n = π ^ n := by
    rw [← map_pow, hπ]; exact ρ.commutes w
  set ζ := ρ π * π⁻¹ with hζ_def
  have hζn : ζ ^ n = 1 := by
    rw [hζ_def, mul_pow, hρπ, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hπ0)]
  have hρπ' : ρ π = ζ * π := by rw [hζ_def, mul_assoc, inv_mul_cancel₀ hπ0, mul_one]
  have hζ1 : A.valuation ζ = 1 := valuation_eq_one_of_pow_eq_one A hn0 hζn
  have hζ0 : ζ ≠ 0 := by intro h; rw [h, zero_pow hn0] at hζn; exact zero_ne_one hζn
  have hρζn : (ρ ζ) ^ n = 1 := by rw [← map_pow, hζn, map_one]
  have hclose : A.valuation (ρ ζ - ζ) < 1 := hρ.2 ζ hζ1.le
  have hξ : ρ ζ * ζ⁻¹ = 1 := by
    refine eq_one_of_pow_eq_one_of_val_sub_lt A hnA ?_ ?_
    · rw [mul_pow, hρζn, inv_pow, hζn, inv_one, one_mul]
    · have e : ρ ζ * ζ⁻¹ - 1 = (ρ ζ - ζ) * ζ⁻¹ := by field_simp
      rw [e, Valuation.map_mul, map_inv₀, hζ1, inv_one, mul_one]; exact hclose
  have hρζ : ρ ζ = ζ := by
    have := congrArg (· * ζ) hξ
    simpa [mul_assoc, inv_mul_cancel₀ hζ0] using this
  have key : ∀ k : ℕ, (ρ ^ k) π = ζ ^ k * π := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, hρζ, hρπ', pow_succ]; ring
  rw [key, hζn, one_mul]

end GlobalTheory
end

section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_pow_residueCard_sub_one_apply_of_pow_mem : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (w : E) (π : Ω), π ^ (normV v - 1) = algebraMap E Ω w →
    ∀ ρ ∈ Ine (F := E) A, (ρ ^ (normV v - 1)) π = π := by
  first | exact @GlobalTheory.ine_pow_normV_sub_one_apply_of_pow_mem | exact GlobalTheory.ine_pow_normV_sub_one_apply_of_pow_mem | (intros; apply GlobalTheory.ine_pow_normV_sub_one_apply_of_pow_mem <;> assumption)
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

theorem GlobalTheory.TameRecip.exists_ine_of_unit : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ ϖ : 𝓞 E, ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ∀ π : Ω, π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) → ∀ (x : (v.adicCompletion E)ˣ) (u : 𝓞 E), IsUnitAt v x → Valued.v ((x : v.adicCompletion E) - algebraMap E (v.adicCompletion E) (u : E)) < 1 → ∃ σ ∈ Ine (F := E) A, toAb E Ω σ = art (localIdele E v x) ∧ A.valuation (σ π / π - algebraMap E Ω (u : E)) < 1 := by
  intro H E Ω _ _ _ _ _ _ art ha v A hA ϖ hϖ1 hϖ2 π hπ x u hx hxu
  have hq : 1 < normV v := by
    unfold normV
    have : Finite (𝓞 E ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
    have : Nontrivial (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top
    exact Finite.one_lt_card
  have hn : 0 < normV v - 1 := by omega
  have hvE : ∀ a : 𝓞 E, Valued.v (algebraMap E (v.adicCompletion E) (a : E)) = v.valuation E (a : E) :=
    fun a => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  have hu1 : Valued.v (algebraMap E (v.adicCompletion E) (u : E)) = 1 := by
    rw [hvE]
    refine le_antisymm (v.valuation_le_one u) (not_lt.mp fun h => ?_)
    have hm : u ∈ v.asIdeal := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) v u).mp h
    have hlt : Valued.v (x : v.adicCompletion E) < 1 := by
      have e : (x : v.adicCompletion E) = ((x : v.adicCompletion E) - algebraMap E (v.adicCompletion E) (u : E)) +
          algebraMap E (v.adicCompletion E) (u : E) := by ring
      rw [e]
      refine Valuation.map_add_lt _ hxu ?_
      rw [hvE]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) v u).mpr hm
    have hx' : Valued.v (x : v.adicCompletion E) = 1 := hx
    rw [hx'] at hlt
    exact lt_irrefl _ hlt
  have hu : u ∉ v.asIdeal := by
    intro hm
    have h := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) v u).mpr hm
    rw [← hvE, hu1] at h
    exact lt_irrefl _ h
  have hu0 : algebraMap E (v.adicCompletion E) (u : E) ≠ 0 := by
    intro h; rw [h, map_zero] at hu1; exact zero_ne_one hu1
  let uc : (v.adicCompletion E)ˣ := Units.mk0 _ hu0
  have hy : Valued.v (((x * uc⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) - 1) < 1 := by
    have e : ((x * uc⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) - 1 =
        ((x : v.adicCompletion E) - algebraMap E (v.adicCompletion E) (u : E)) *
          (algebraMap E (v.adicCompletion E) (u : E))⁻¹ := by
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, uc, Units.val_mk0]
      field_simp
    rw [e, map_mul, map_inv₀, hu1, inv_one, mul_one]
    exact hxu
  obtain ⟨z, hz1, hz⟩ := GlobalTheory.T.exists_unit_pow_normV_sub_one' E v (x * uc⁻¹) hy
  obtain ⟨ρ, hρ, hρz⟩ := (ha.ine v A hA _).mp ⟨z, hz1, rfl⟩
  obtain ⟨τ, hτF, hτπ, hτc⟩ := GlobalTheory.T.exists_frob_of_eisenstein_root H E Ω art ha v A hA ϖ hϖ1 hϖ2 π hπ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (u : E)) hn
  have h1' : u * ϖ ∈ v.asIdeal := Ideal.mul_mem_left _ _ hϖ1
  have h2' : u * ϖ ∉ v.asIdeal ^ 2 := by
    intro h
    rcases Ideal.IsPrime.mul_mem_pow v.asIdeal h with h3 | h3
    · exact hu h3
    · exact hϖ2 h3
  have hπ' : (π * t) ^ (normV v - 1) = algebraMap E Ω ((u * ϖ : 𝓞 E) : E) := by
    rw [mul_pow, hπ, ht, ← map_mul]
    push_cast
    ring_nf
  obtain ⟨τ', hτ'F, hτ'π, hτ'c⟩ := GlobalTheory.T.exists_frob_of_eisenstein_root H E Ω art ha v A hA (u * ϖ) h1' h2' (π * t) hπ'
  have hσ0 : τ'⁻¹ * τ ∈ Ine (F := E) A := GlobalTheory.T.frobenius_inv_mul_mem_inertia E Ω v A hA τ τ' hτF hτ'F
  have hϖ0 : (ϖ : E) ≠ 0 := by
    intro h
    apply hϖ2
    have : ϖ = 0 := by exact_mod_cast h
    rw [this]; exact Ideal.zero_mem _
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne', eq_comm, map_eq_zero] at hπ
    exact hϖ0 hπ
  have hval := GlobalTheory.T.frobenius_ratio_pi_congr_tame_unit E Ω v A hA u hu π t hπ0 ht τ τ' hτF hτ'F hτπ hτ'π
  have hc0 : (-1) ^ normV v * algebraMap E (v.adicCompletion E) (ϖ : E) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) ((map_ne_zero _).mpr hϖ0)
  have huE : (u : E) ≠ 0 := by
    intro h
    apply hu
    have : u = 0 := by exact_mod_cast h
    rw [this]; exact Ideal.zero_mem _
  have hcast : ((u * ϖ : 𝓞 E) : E) = (u : E) * (ϖ : E) := by push_cast; ring
  have hs0 : ((-1) ^ normV v : v.adicCompletion E) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hϖc : algebraMap E (v.adicCompletion E) (ϖ : E) ≠ 0 := (map_ne_zero _).mpr hϖ0
  have hc0' : (-1) ^ normV v * algebraMap E (v.adicCompletion E) (((u * ϖ : 𝓞 E)) : E) ≠ 0 := by
    rw [hcast, map_mul]
    exact mul_ne_zero hs0 (mul_ne_zero hu0 hϖc)
  have ec := hτc (Units.mk0 _ hc0) rfl
  have ec' := hτ'c (Units.mk0 _ hc0') rfl
  have hmain : toAb E Ω (τ'⁻¹ * τ) = art (localIdele E v uc) := by
    have e1 : toAb E Ω τ = (art (localIdele E v (Units.mk0 _ hc0)))⁻¹ := by
      rw [← ec, map_inv, inv_inv]
    rw [map_mul, ec', e1, ← map_inv, ← map_inv, ← map_mul, ← map_mul]
    congr 2
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, uc]
    rw [hcast, map_mul]
    field_simp
  refine ⟨τ'⁻¹ * τ * ρ ^ (normV v - 1), mul_mem hσ0 (pow_mem hρ _), ?_, ?_⟩
  · rw [map_mul, map_pow, hmain, hρz, ← map_pow, ← map_pow, ← map_mul, ← map_mul, hz]
    congr 1
    rw [mul_comm x, mul_inv_cancel_left]
  · have e : (τ'⁻¹ * τ * ρ ^ (normV v - 1)) π = (τ'⁻¹ * τ) π := by
      rw [AlgEquiv.mul_apply, GlobalTheory.T.inertia_pow_residueCard_sub_one_apply_of_pow_mem E Ω v A hA (ϖ : E) π hπ ρ hρ]
    rw [e]
    exact hval

end
end
