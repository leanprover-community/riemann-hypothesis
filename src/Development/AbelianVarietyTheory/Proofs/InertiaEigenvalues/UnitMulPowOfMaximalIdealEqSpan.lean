import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ProjectionSurjective

section
namespace GlobalTheory.PowMulUnit

theorem exists_eq_pow_mul_unit {S : Type} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    {π : S} (hπ : IsLocalRing.maximalIdeal S = Ideal.span {π}) {x : S} (hx : x ≠ (0 : S)) :
    ∃ (k : ℕ) (u : S), IsUnit u ∧ x = π ^ k * u := by
  classical
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal S)
    (IsLocalRing.maximalIdeal.isMaximal S).ne_top
  have hex : ∃ n : ℕ, ¬ (π ^ n ∣ x) := by
    by_contra h0
    have h : ∀ n : ℕ, π ^ n ∣ x := fun n => not_not.mp (not_exists.mp h0 n)
    apply hx
    have hmem : x ∈ ⨅ n : ℕ, IsLocalRing.maximalIdeal S ^ n := by
      refine Ideal.mem_iInf.mpr fun n => ?_
      rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact h n
    rw [hK] at hmem
    exact hmem
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    have h1 := Nat.find_spec hex
    rw [h0, pow_zero] at h1
    exact h1 (one_dvd x)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hdk : π ^ k ∣ x := by
    have := Nat.find_min hex (show k < Nat.find hex by omega)
    exact not_not.mp this
  obtain ⟨u, rfl⟩ := hdk
  refine ⟨k, u, ?_, rfl⟩
  by_contra hu
  have hum : u ∈ IsLocalRing.maximalIdeal S := (IsLocalRing.mem_maximalIdeal u).mpr hu
  rw [hπ, Ideal.mem_span_singleton] at hum
  obtain ⟨w, rfl⟩ := hum
  apply Nat.find_spec hex
  rw [hk, pow_succ]
  exact ⟨w, by ring⟩

end GlobalTheory.PowMulUnit
end

section
open IsLocalRing GlobalTheory.Pat

namespace GlobalTheory.Pat

theorem unit_mul_pow_of_maximalIdeal_eq_span {S : Type} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    {π : S} (hm : maximalIdeal S = Ideal.span {π}) {x : S} (hx : x ≠ 0) :
    ∃ (k : ℕ) (u : S), IsUnit u ∧ x = π ^ k * u := by
  first
  | exact @_root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit
  | exact _root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit
  | (apply _root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowMulUnit.exists_eq_pow_mul_unit ..)

theorem dvr_of_maximalIdeal_eq_span {S : Type} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    {π : S} (hm : maximalIdeal S = Ideal.span {π}) (hreg : ∀ a : S, π * a = 0 → a = 0) :
    ∃ _ : IsDomain S, IsDiscreteValuationRing S ∧ Irreducible π := by
  have hpow : ∀ (k : ℕ) (a : S), π ^ k * a = 0 → a = 0 := by
    intro k
    induction k with
    | zero => intro a h; simpa using h
    | succ k ih => intro a h; exact ih a (hreg _ (by rw [← h, pow_succ]; ring))
  have hnzd : NoZeroDivisors S := by
    refine ⟨fun {x y} hxy => ?_⟩
    by_contra h
    push_neg at h
    obtain ⟨a, u, hu, rfl⟩ := unit_mul_pow_of_maximalIdeal_eq_span hm h.1
    obtain ⟨b, v, hv, rfl⟩ := unit_mul_pow_of_maximalIdeal_eq_span hm h.2
    have : π ^ (a + b) * (u * v) = 0 := by rw [← hxy, pow_add]; ring
    exact (hu.mul hv).ne_zero (hpow _ _ this)
  haveI : IsDomain S := NoZeroDivisors.to_isDomain S
  have hπ0 : π ≠ 0 := fun h => one_ne_zero (hreg 1 (by rw [h, zero_mul]))
  have hnf : ¬ IsField S := by
    rw [isField_iff_maximalIdeal_eq, hm, Ideal.span_singleton_eq_bot]
    exact hπ0
  have hpr : (maximalIdeal S).IsPrincipal := ⟨⟨π, hm⟩⟩
  have hdvr : IsDiscreteValuationRing S :=
    ((IsDiscreteValuationRing.TFAE S hnf).out 0 4).2 hpr
  exact ⟨inferInstance, hdvr, (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2 hm⟩

end GlobalTheory.Pat
end
