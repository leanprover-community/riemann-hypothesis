import Mathlib
import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup Topology Filter
open scoped GroundTheory.LocalField.Abstract

noncomputable section

namespace DirichletHecke

open _root_.GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract RationalSymbol

theorem absNorm_span_natCast (m : ℕ) : Ideal.absNorm (Ideal.span {(m : 𝓞 ℚ)}) = m := by
  rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 ℚ)) m, Algebra.norm_algebraMap,
    NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one, Int.natAbs_natCast]

theorem exists_eq_span_natCast (I : Ideal (𝓞 ℚ)) : ∃ m : ℕ, I = Ideal.span {(m : 𝓞 ℚ)} := by
  obtain ⟨k, hk⟩ := (IsPrincipalIdealRing.principal (I.map Rat.ringOfIntegersEquiv)).principal
  refine ⟨k.natAbs, ?_⟩
  have hI : I = (I.map Rat.ringOfIntegersEquiv).map Rat.ringOfIntegersEquiv.symm :=
    (Ideal.map_of_equiv _).symm
  rw [hI, hk, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton,
    show Rat.ringOfIntegersEquiv.symm k = (k : 𝓞 ℚ) from
      eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) k]
  rcases Int.natAbs_eq k with h | h
  · rw [h, Int.cast_natCast, Int.natAbs_natCast]
  · rw [h, Int.natAbs_neg, Int.natAbs_natCast, Int.cast_neg, Int.cast_natCast, Ideal.span_singleton_neg]

theorem eq_span_of_absNorm_eq {I : Ideal (𝓞 ℚ)} {n : ℕ} (h : Ideal.absNorm I = n) :
    I = Ideal.span {(n : 𝓞 ℚ)} := by
  obtain ⟨m, rfl⟩ := exists_eq_span_natCast I
  rw [absNorm_span_natCast] at h
  rw [h]

theorem absNorm_asIdeal (v : HeightOneSpectrum (𝓞 ℚ)) : Ideal.absNorm v.asIdeal = prime v := by
  rw [asIdeal_eq_span, absNorm_span_natCast]

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

theorem coeff_asIdeal (hχ : χ.IsPrimitive) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (heckeCharacter χ).coeff v.asIdeal = χ (prime v) := by
  by_cases hv : prime v ∣ N
  · rw [(heckeCharacter χ).coeff_asIdeal_of_dvd (dvd_conductor_of_dvd χ hχ hv)]
    refine (MulChar.map_nonunit χ fun hu ↦ ?_).symm
    rw [ZMod.isUnit_iff_coprime] at hu
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hu hv
  · rw [(heckeCharacter χ).coeff_asIdeal_of_not_dvd (not_dvd_conductor_of_not_dvd χ hv)]
    exact coe_idealCharacter_primeIdealUnit χ hv

theorem coeff_span_natCast (hχ : χ.IsPrimitive) {n : ℕ} (hn : n ≠ 0) :
    (heckeCharacter χ).coeff (Ideal.span {(n : 𝓞 ℚ)}) = χ n := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one => rw [Nat.cast_one, Ideal.span_singleton_one, (heckeCharacter χ).coeff_top, Nat.cast_one, map_one]
  | prime p hp =>
    have hv : prime (placeOf ⟨p, hp⟩) = p := prime_placeOf ⟨p, hp⟩
    have h := coeff_asIdeal χ hχ (placeOf ⟨p, hp⟩)
    rw [asIdeal_eq_span, hv] at h
    exact h
  | mul a b ha hb =>
    have ha0 : a ≠ 0 := left_ne_zero_of_mul hn
    have hb0 : b ≠ 0 := right_ne_zero_of_mul hn
    rw [Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton, (heckeCharacter χ).coeff_mul, ha ha0,
      hb hb0, Nat.cast_mul, map_mul]

theorem LCoeff_eq (hχ : χ.IsPrimitive) {n : ℕ} (hn : n ≠ 0) : (heckeCharacter χ).LCoeff n = χ n := by
  rw [HeckeCharacter.LCoeff, tsum_eq_single (⟨Ideal.span {(n : 𝓞 ℚ)}, absNorm_span_natCast n⟩ :
      {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n}) fun I hI ↦
      absurd (Subtype.ext (eq_span_of_absNorm_eq I.2)) hI]
  exact coeff_span_natCast χ hχ hn

theorem LFunction_heckeCharacter (hχ : χ.IsPrimitive) {s : ℂ} (hs : 1 < s.re) :
    (heckeCharacter χ).LFunction s = DirichletCharacter.LFunction χ s := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs, HeckeCharacter.LFunction]
  exact LSeries_congr (fun hn ↦ LCoeff_eq χ hχ hn) s



theorem isPreconnected_compl_of_countable {S : Set ℂ} (hS : S.Countable) : IsPreconnected Sᶜ :=
  (hS.isPathConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)).isConnected.isPreconnected


end DirichletHecke

end

end GroundTheory.Global
