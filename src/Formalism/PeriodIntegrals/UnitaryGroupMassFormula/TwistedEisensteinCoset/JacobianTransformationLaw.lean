import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.IaDivDown
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.UnitCongruentToInteger
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedNormLattice.UniformContinuityGaloisGroup
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedCharacterOne.IsIntegralAtSuperdiagonalSum

section
open NumberField IsDedekindDomain

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

namespace NTA

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem iMul {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a * b) := by
  obtain ⟨r1, s1, hs1, h1⟩ := ha
  obtain ⟨r2, s2, hs2, h2⟩ := hb
  refine ⟨r1 * r2, s1 * s2, fun h => ?_, ?_⟩
  · rcases P.isPrime.mem_or_mem h with h | h
    exacts [hs1 h, hs2 h]
  · simp only [map_mul]
    rw [← h1, ← h2]
    ring
theorem iAdd {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a + b) := by
  obtain ⟨r1, s1, hs1, h1⟩ := ha
  obtain ⟨r2, s2, hs2, h2⟩ := hb
  refine ⟨r1 * s2 + r2 * s1, s1 * s2, fun h => ?_, ?_⟩
  · rcases P.isPrime.mem_or_mem h with h | h
    exacts [hs1 h, hs2 h]
  · simp only [map_mul, map_add]
    rw [← h1, ← h2]
    ring
theorem iSub {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a - b) := by
  obtain ⟨r1, s1, hs1, h1⟩ := ha
  obtain ⟨r2, s2, hs2, h2⟩ := hb
  refine ⟨r1 * s2 - r2 * s1, s1 * s2, fun h => ?_, ?_⟩
  · rcases P.isPrime.mem_or_mem h with h | h
    exacts [hs1 h, hs2 h]
  · simp only [map_mul, map_sub]
    rw [← h1, ← h2]
    ring
theorem iNat (m : ℕ) : IntAt P (m : E) := ⟨(m : 𝓞 E), 1, (Ideal.ne_top_iff_one _).mp P.isPrime.ne_top, by simp⟩
theorem iPow {a : E} (ha : IntAt P a) (m : ℕ) : IntAt P (a ^ m) := by
  induction m with
  | zero => simpa using iNat P 1
  | succ m ih => rw [pow_succ]; exact iMul P ih ha
theorem iAlg (x : 𝓞 E) : IntAt P (algebraMap (𝓞 E) E x) := ⟨x, 1, (Ideal.ne_top_iff_one _).mp P.isPrime.ne_top, by simp⟩

theorem qO_mem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem P.asIdeal

theorem q_ne (hp : (Ideal.absNorm P.asIdeal).Prime) : (qOf P : E) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr hp.ne_zero

theorem one_nm : (1 : 𝓞 E) ∉ P.asIdeal := (Ideal.ne_top_iff_one _).mp P.isPrime.ne_top

theorem not_int_inv_q (hp : (Ideal.absNorm P.asIdeal).Prime) : ¬ IntAt P ((qOf P : E)⁻¹) := by
  rintro ⟨r, s, hs, h⟩
  apply hs
  have hq := q_ne P hp
  have e : algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E (r * ((qOf P : ℕ) : 𝓞 E)) := by
    rw [map_mul, ← h, map_natCast, mul_assoc, inv_mul_cancel₀ hq, mul_one]
  rw [IsFractionRing.injective (𝓞 E) E e]
  exact Ideal.mul_mem_left _ _ (qO_mem P)

theorem natCast_notMem (hp : (Ideal.absNorm P.asIdeal).Prime) {m : ℕ} (hm : ¬ qOf P ∣ m) :
    (m : 𝓞 E) ∉ P.asIdeal := by
  intro hmP
  have hcop : IsCoprime ((qOf P : ℕ) : ℤ) (m : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
  obtain ⟨u, v, huv⟩ := hcop
  apply one_nm P
  have e : (((u * ((qOf P : ℕ) : ℤ) + v * (m : ℤ) : ℤ)) : 𝓞 E) = 1 := by
    rw [huv]
    simp
  rw [← e]
  push_cast
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (qO_mem P)) (Ideal.mul_mem_left _ _ hmP)

theorem int_inv_nat (hp : (Ideal.absNorm P.asIdeal).Prime) {m : ℕ} (hm : ¬ qOf P ∣ m) : IntAt P ((m : E)⁻¹) := by
  have hm0 : (m : E) ≠ 0 := by
    have : m ≠ 0 := fun h => hm (h ▸ dvd_zero _)
    exact_mod_cast this
  refine ⟨1, (m : 𝓞 E), natCast_notMem P hp hm, ?_⟩
  rw [map_natCast, map_one, mul_inv_cancel₀ hm0]

theorem res_surj (hp : (Ideal.absNorm P.asIdeal).Prime) (x : 𝓞 E ⧸ P.asIdeal) :
    ∃ d : ℕ, d < qOf P ∧ Ideal.Quotient.mk P.asIdeal (d : 𝓞 E) = x := by
  have hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = qOf P := by
    unfold qOf
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ P.asIdeal) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  let f : Fin (qOf P) → 𝓞 E ⧸ P.asIdeal := fun d => Ideal.Quotient.mk P.asIdeal ((d : ℕ) : 𝓞 E)
  have hinj : Function.Injective f := by
    intro d d' h
    have h' : ((d : ℕ) : 𝓞 E) - ((d' : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.Quotient.eq.mp h
    have hd := d.isLt
    have hd' := d'.isLt
    apply Fin.ext
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have hm : ((d'.val - d.val : ℕ) : 𝓞 E) ∈ P.asIdeal := by
        rw [Nat.cast_sub hlt.le]
        have := P.asIdeal.neg_mem h'
        rwa [neg_sub] at this
      exact natCast_notMem P hp (fun hdvd => by
        have := Nat.le_of_dvd (by omega) hdvd
        omega) hm
    · have hm : ((d.val - d'.val : ℕ) : 𝓞 E) ∈ P.asIdeal := by
        rw [Nat.cast_sub hlt.le]
        exact h'
      exact natCast_notMem P hp (fun hdvd => by
        have := Nat.le_of_dvd (by omega) hdvd
        omega) hm
  have hbij := hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin])
  obtain ⟨d, hd⟩ := hbij.2 x
  exact ⟨d.val, d.isLt, hd⟩

private theorem intAt_div_qOf_of_mem (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {α : 𝓞 E} (hα : α ∈ P.asIdeal) :
    IntAt P (algebraMap (𝓞 E) E α / (qOf P : E)) := by
  have hle : Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)} ≤ P.asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).mpr (qO_mem P)
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
  have hJP : ¬ J ≤ P.asIdeal := by
    intro h
    apply hq
    have h2 : Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)} ≤ P.asIdeal ^ 2 := by
      rw [hJ, pow_two]
      exact Ideal.mul_mono_right h
    exact h2 (Ideal.mem_span_singleton_self _)
  obtain ⟨t, htJ, htP⟩ := SetLike.not_le_iff_exists.mp hJP
  have hmem : α * t ∈ Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E)} := by
    rw [hJ]
    exact Ideal.mul_mem_mul hα htJ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have hq0 := q_ne P hp
  refine ⟨c, t, htP, ?_⟩
  have e := congrArg (algebraMap (𝓞 E) E) hc
  simp only [map_mul, map_natCast] at e
  rw [mul_div_assoc', div_eq_iff hq0]
  unfold qOf
  linear_combination -e

theorem approx1 (hp : (Ideal.absNorm P.asIdeal).Prime) (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
    {y : E} (hy : IntAt P y) : ∃ d : ℕ, d < qOf P ∧ IntAt P ((y - d) / (qOf P : E)) := by
  haveI : P.asIdeal.IsMaximal := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  obtain ⟨r, s, hs, hy'⟩ := hy
  have hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
  obtain ⟨d, hdq, hd⟩ :=
    res_surj P hp (Ideal.Quotient.mk P.asIdeal r * (Ideal.Quotient.mk P.asIdeal s)⁻¹)
  have hmem : r - (d : 𝓞 E) * s ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hd, mul_assoc, inv_mul_cancel₀ hs0,
      mul_one, sub_self]
  obtain ⟨c, t, ht, hct⟩ := intAt_div_qOf_of_mem P hp hq hmem
  have hs' : algebraMap (𝓞 E) E s ≠ 0 := by
    intro h
    apply hs
    rw [IsFractionRing.injective (𝓞 E) E (h.trans (map_zero _).symm)]
    exact P.asIdeal.zero_mem
  have hq0 := q_ne P hp
  refine ⟨d, hdq, c, t * s, fun h => ?_, ?_⟩
  · rcases P.isPrime.mem_or_mem h with h | h
    exacts [ht h, hs h]
  · have hy2 : y = algebraMap (𝓞 E) E r / algebraMap (𝓞 E) E s := by
      rw [eq_div_iff hs', mul_comm]
      exact hy'
    rw [← hct, hy2, map_mul, map_sub, map_mul, map_natCast]
    field_simp

theorem mem_pow_of (hp : (Ideal.absNorm P.asIdeal).Prime) {α : 𝓞 E} {K : ℕ}
    (h : IntAt P (algebraMap (𝓞 E) E α / (qOf P : E) ^ K)) : α ∈ P.asIdeal ^ K := by
  haveI := P.isPrime
  obtain ⟨r, s, hs, h⟩ := h
  have hq0 := q_ne P hp
  have e : algebraMap (𝓞 E) E (s * α) = algebraMap (𝓞 E) E (r * ((qOf P : ℕ) : 𝓞 E) ^ K) := by
    rw [map_mul, map_mul, map_pow, map_natCast, ← h]
    field_simp
  have hsα : s * α ∈ P.asIdeal ^ K := by
    rw [IsFractionRing.injective (𝓞 E) E e]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (qO_mem P) K)
  exact (Ideal.IsPrime.mul_mem_pow P.asIdeal hsα).resolve_left hs

theorem exists_not_int (hp : (Ideal.absNorm P.asIdeal).Prime) {α : 𝓞 E} (hα : α ≠ 0) :
    ∃ K : ℕ, ¬ IntAt P (algebraMap (𝓞 E) E α / (qOf P : E) ^ K) := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ K, α ∈ P.asIdeal ^ K := fun K => mem_pow_of P hp (hcon K)
  have hbot := Ideal.iInf_pow_eq_bot_of_isDomain P.asIdeal P.isPrime.ne_top
  have hin : α ∈ (⨅ i, P.asIdeal ^ i) := Ideal.mem_iInf.mpr hall
  rw [hbot, Ideal.mem_bot] at hin
  exact hα hin

theorem decomp (hp : (Ideal.absNorm P.asIdeal).Prime) (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
    {α : 𝓞 E} (hα : α ≠ 0) : ∃ (k : ℕ) (u : E), algebraMap (𝓞 E) E α = (qOf P : E) ^ k * u ∧ u ≠ 0 ∧
      IntAt P u ∧ IntAt P u⁻¹ := by
  classical
  have hex := exists_not_int P hp hα
  have hK : ¬ IntAt P (algebraMap (𝓞 E) E α / (qOf P : E) ^ Nat.find hex) := Nat.find_spec hex
  have hK0 : Nat.find hex ≠ 0 := by
    intro h0
    apply hK
    rw [h0, pow_zero, div_one]
    exact iAlg P α
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hint : IntAt P (algebraMap (𝓞 E) E α / (qOf P : E) ^ k) :=
    not_not.mp (Nat.find_min hex (by omega : k < Nat.find hex))
  rw [hk] at hK
  have hq0 := q_ne P hp
  have hα' : algebraMap (𝓞 E) E α ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hα
  have hu0 : algebraMap (𝓞 E) E α / (qOf P : E) ^ k ≠ 0 := div_ne_zero hα' (pow_ne_zero _ hq0)
  refine ⟨k, algebraMap (𝓞 E) E α / (qOf P : E) ^ k, ?_, hu0, hint, ?_⟩
  · field_simp
  · obtain ⟨r, s, hs, hrs⟩ := hint
    have hrP : r ∉ P.asIdeal := by
      intro hr
      apply hK
      obtain ⟨c, t, ht, hct⟩ := intAt_div_qOf_of_mem P hp hq hr
      refine ⟨c, t * s, fun h => ?_, ?_⟩
      · rcases P.isPrime.mem_or_mem h with h | h
        exacts [ht h, hs h]
      · rw [← hct, ← hrs, map_mul]
        field_simp
        ring
    refine ⟨s, r, hrP, ?_⟩
    rw [← hrs, mul_assoc, mul_inv_cancel₀ hu0, mul_one]

theorem no_shift (hp : (Ideal.absNorm P.asIdeal).Prime) (d : ℕ) {w w' : E} (hw : w ≠ 0) (hwi : IntAt P w⁻¹)
    (hw' : IntAt P w') (h : w = (qOf P : E) ^ (d + 1) * w') : False := by
  have hq0 := q_ne P hp
  have hw'0 : w' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h
    exact hw h
  have hint : IntAt P (w⁻¹ * w' * (qOf P : E) ^ d) :=
    iMul P (iMul P hwi hw') (iPow P (iNat P _) d)
  have e : w⁻¹ * w' * (qOf P : E) ^ d = (qOf P : E)⁻¹ := by
    rw [h]
    field_simp
    ring
  rw [e] at hint
  exact not_int_inv_q P hp hint

end NTA

open NTA in
theorem integer_integral_iff_dvd : IntegerIntegralIffDvd := by
  intro E _ _ P hp hq i e
  have hq0 := q_ne P hp
  constructor
  · intro hI
    by_contra hnd
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hnd (dvd_zero _)
    obtain ⟨f, j, hj, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hi0 (qOf P) hp.one_lt.ne'
    have hfe : f < e := by
      by_contra hfe
      push_neg at hfe
      exact hnd (Dvd.dvd.mul_right (pow_dvd_pow _ hfe) _)
    have h1 : IntAt P ((((qOf P ^ f * j : ℕ) : E) / (qOf P : E) ^ e) * (j : E)⁻¹ *
        (qOf P : E) ^ (e - f - 1)) :=
      iMul P (iMul P hI (int_inv_nat P hp hj)) (iPow P (iNat P _) _)
    have hj0 : (j : E) ≠ 0 := by
      have : j ≠ 0 := fun h => hj (h ▸ dvd_zero _)
      exact_mod_cast this
    have e2 : (((qOf P ^ f * j : ℕ) : E) / (qOf P : E) ^ e) * (j : E)⁻¹ * (qOf P : E) ^ (e - f - 1) =
        (qOf P : E)⁻¹ := by
      obtain ⟨g, rfl⟩ : ∃ g, e = f + g + 1 := ⟨e - f - 1, by omega⟩
      have hg : f + g + 1 - f - 1 = g := by omega
      rw [hg]
      push_cast
      field_simp
      ring
    rw [e2] at h1
    exact not_int_inv_q P hp h1
  · rintro ⟨k, rfl⟩
    have e2 : (((qOf P ^ e * k : ℕ) : E) / (qOf P : E) ^ e) = (k : E) := by
      push_cast
      field_simp
    rw [e2]
    exact iNat P k

open NTA in
theorem integral_approximation_by_integer : IntegralApproximationByInteger := by
  intro E _ _ P hp hq x N hx
  have hq0 := q_ne P hp
  induction N with
  | zero => exact ⟨0, by simp, by simpa using hx⟩
  | succ N ih =>
    obtain ⟨i, hi, hz⟩ := ih
    obtain ⟨d, hd, hzd⟩ := approx1 P hp hq hz
    refine ⟨i + d * qOf P ^ N, ?_, ?_⟩
    · calc i + d * qOf P ^ N < qOf P ^ N + d * qOf P ^ N := Nat.add_lt_add_right hi _
        _ = (d + 1) * qOf P ^ N := by ring
        _ ≤ qOf P * qOf P ^ N := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hd)
        _ = qOf P ^ (N + 1) := by ring
    · have e : (x - ((i + d * qOf P ^ N : ℕ) : E)) / (qOf P : E) ^ (N + 1) =
          ((x - i) / (qOf P : E) ^ N - d) / (qOf P : E) := by
        push_cast
        field_simp
        ring
      rw [e]
      exact hzd

open NTA in
theorem element_eq_prime_power_mul_unit : ElementEqPrimePowerMulUnit := by
  intro E _ _ P hp hq a ha
  have hq0 := q_ne P hp
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (𝓞 E) a
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at ha
  obtain ⟨k, u, hu, hu0, hui, huii⟩ := decomp P hp hq hx0
  obtain ⟨k', u', hu', hu0', hui', huii'⟩ := decomp P hp hq hy0
  refine ⟨(k : ℤ) - k', u / u', ?_, div_ne_zero hu0 hu0', ?_, ?_⟩
  · rw [hu, hu', zpow_sub₀ hq0, zpow_natCast, zpow_natCast]
    field_simp
  · rw [div_eq_mul_inv]
    exact iMul P hui huii'
  · rw [inv_div, div_eq_mul_inv]
    exact iMul P hui' huii

open NTA in
theorem valuation_exponent_unique : ValuationExponentUnique := by
  intro E _ _ P hp hq e e' w w' hw hwi hwii hw'i hw'ii h
  have hq0 := q_ne P hp
  have hw' : w' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h
    exact hw ((mul_eq_zero.mp h).resolve_left (zpow_ne_zero _ hq0))
  rcases lt_trichotomy e e' with hlt | heq | hgt
  · exfalso
    obtain ⟨d, hd⟩ : ∃ d : ℕ, e' - e = (d : ℤ) + 1 := ⟨(e' - e - 1).toNat, by omega⟩
    apply no_shift P hp d hw hwii hw'i
    have hpw : (qOf P : E) ^ (d + 1) = (qOf P : E) ^ (e' - e) := by
      rw [hd, ← Nat.cast_succ, zpow_natCast]
    rw [hpw, zpow_sub₀ hq0, div_mul_eq_mul_div, eq_div_iff (zpow_ne_zero _ hq0)]
    linear_combination h
  · exact heq
  · exfalso
    obtain ⟨d, hd⟩ : ∃ d : ℕ, e - e' = (d : ℤ) + 1 := ⟨(e - e' - 1).toNat, by omega⟩
    apply no_shift P hp d hw' hw'ii hwi
    have hpw : (qOf P : E) ^ (d + 1) = (qOf P : E) ^ (e - e') := by
      rw [hd, ← Nat.cast_succ, zpow_natCast]
    rw [hpw, zpow_sub₀ hq0, div_mul_eq_mul_div, eq_div_iff (zpow_ne_zero _ hq0)]
    linear_combination -h

open NTA in
theorem unit_congruent_to_integer : UnitCongruentToInteger := by
  intro E _ _ P hp hq w N hw hwi hwii
  have hq0 := q_ne P hp
  cases N with
  | zero => exact ⟨1, Nat.coprime_one_left _, by simpa using iSub P hwi (iNat P 1)⟩
  | succ N =>
    obtain ⟨i, hi, hI⟩ := integral_approximation_by_integer E P hp hq w (N + 1) hwi
    refine ⟨i, ?_, hI⟩
    rw [Nat.coprime_comm]
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr ?_
    rintro ⟨j, rfl⟩
    apply not_int_inv_q P hp
    have h1 : IntAt P (w / (qOf P : E)) := by
      have e : w / (qOf P : E) = (w - ((qOf P * j : ℕ) : E)) / (qOf P : E) ^ (N + 1) *
          (qOf P : E) ^ N + (j : E) := by
        push_cast
        field_simp
        ring
      rw [e]
      exact iAdd P (iMul P hI (iPow P (iNat P _) N)) (iNat P j)
    have e2 : (qOf P : E)⁻¹ = w / (qOf P : E) * w⁻¹ := by
      field_simp
    rw [e2]
    exact iMul P h1 hwii

end PI.TwistedEisensteinNonvanishing.W
end
end

section
open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

open Loc LocE

section Red

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

private lemma mk_mul_reduction_eq_mk {a : E} {r s : 𝓞 E} (hs : s ∉ P.asIdeal)
    (h : algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r) :
    redP P a * Ideal.Quotient.mk P.asIdeal s = Ideal.Quotient.mk P.asIdeal r := by
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  have hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := fun h0 => hs (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  have hex : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧
      algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r :=
    ⟨Ideal.Quotient.mk P.asIdeal r * (Ideal.Quotient.mk P.asIdeal s)⁻¹, r, s, hs, h, by
      field_simp⟩
  unfold redP
  rw [dif_pos hex]
  obtain ⟨r', s', hs', h', hc'⟩ := hex.choose_spec
  have hs'0 : Ideal.Quotient.mk P.asIdeal s' ≠ 0 :=
    fun h0 => hs' (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  have hE : algebraMap (𝓞 E) E (s' * r) = algebraMap (𝓞 E) E (s * r') := by
    rw [map_mul, map_mul, ← h, ← h']
    ring
  have hO : s' * r = s * r' := FaithfulSMul.algebraMap_injective (𝓞 E) E hE
  have hQ : Ideal.Quotient.mk P.asIdeal s' * Ideal.Quotient.mk P.asIdeal r =
      Ideal.Quotient.mk P.asIdeal s * Ideal.Quotient.mk P.asIdeal r' := by
    rw [← map_mul, ← map_mul, hO]
  apply mul_left_cancel₀ hs'0
  rw [hQ, ← hc']
  ring

theorem reduction_mul' {a b : E} (ha : IntAt P a) (hb : IntAt P b) : redP P (a * b) = redP P a * redP P b := by
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  obtain ⟨r, s, hs, h⟩ := ha
  obtain ⟨r', s', hs', h'⟩ := hb
  have hss : s * s' ∉ P.asIdeal := fun hm => (P.isPrime.mem_or_mem hm).elim hs hs'
  have hab : algebraMap (𝓞 E) E (s * s') * (a * b) = algebraMap (𝓞 E) E (r * r') := by
    rw [map_mul, map_mul, ← h, ← h']
    ring
  have h1 := mk_mul_reduction_eq_mk P hss hab
  have ha' := mk_mul_reduction_eq_mk P hs h
  have hb' := mk_mul_reduction_eq_mk P hs' h'
  have hss0 : Ideal.Quotient.mk P.asIdeal (s * s') ≠ 0 :=
    fun h0 => hss (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  apply mul_right_cancel₀ hss0
  rw [h1, map_mul, map_mul, ← ha', ← hb']
  ring

theorem reduction_one' : redP P (1 : E) = 1 := by
  have h1 : (1 : 𝓞 E) ∉ P.asIdeal := fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have h := mk_mul_reduction_eq_mk P (a := 1) (r := 1) h1 (by simp)
  simpa using h

theorem isUnit_redP {w : E} (hw : UnitAt P w) : IsUnit (redP P w) := by
  obtain ⟨hw0, hi, hi'⟩ := hw
  have h := reduction_mul' P hi hi'
  rw [mul_inv_cancel₀ hw0, reduction_one'] at h
  exact IsUnit.of_mul_eq_one (b := redP P w⁻¹) h.symm

end Red

theorem muNe_of (hN : NTAll) : MuNeP := by
  intro E K _ _ _ _ P hp hq cq χ hcq a ha
  obtain ⟨e, w, hae, hw0, hw1, hw2⟩ := hN.2.2.1 E P hp hq a ha
  have hex : ∃ z : ℤ, IsUnit (redP P (a / (qOf P : E) ^ z)) := by
    refine ⟨e, ?_⟩
    have : a / (qOf P : E) ^ e = w := by
      rw [hae]
      field_simp [zpow_ne_zero e (qE_ne P hp)]
    rw [this]
    exact isUnit_redP P ⟨hw0, hw1, hw2⟩
  have hspec : IsUnit (redP P (a / (qOf P : E) ^ vP P (qOf P) a)) := Classical.epsilon_spec hex
  unfold locChar
  refine mul_ne_zero (zpow_ne_zero _ hcq) ?_
  unfold unitV
  rw [dif_pos hspec]
  exact Units.ne_zero _

theorem omStep_of (hJ : JLawP) (hM : MuNeP) : OmStepP := by
  intro E K _ _ _ _ P hp hq sq cq hsq hcq ξ k₀ r c' n' c n kj h1 h2 h3 h4 h5 g₀ h ρ κ hκ
  obtain ⟨lam, hlam, hlaw⟩ := hJ E K P hp hq ξ k₀ r c' n' c n kj h1 h2 h3 h4 h5 κ hκ
  have hdet : ∀ f : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E), locChar (qOf P) cq ξ⁻¹ (LinearEquiv.det f : E) ≠ 0 :=
    fun f => hM E K P hp hq cq ξ⁻¹ hcq _ (Units.ne_zero _)
  refine ⟨(locChar (qOf P) cq ξ⁻¹ (LinearEquiv.det (ρ * h * κ) : E))⁻¹ * sq ^ (vP P (qOf P) (LinearEquiv.det (ρ * h * κ) : E) * ((n' + c' : ℕ) : ℤ)) * lam /
      ((locChar (qOf P) cq ξ⁻¹ (LinearEquiv.det h : E))⁻¹ * sq ^ (vP P (qOf P) (LinearEquiv.det h : E) * ((n' + c' : ℕ) : ℤ))), ?_, fun x => ?_⟩
  · have := hdet (ρ * h * κ)
    have := hdet h
    refine div_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero ‹_›) (zpow_ne_zero _ hsq)) hlam)
      (mul_ne_zero (inv_ne_zero ‹_›) (zpow_ne_zero _ hsq))
  · have ey : (ρ * h * κ).symm.toLinearMap ∘ₗ x ∘ₗ g₀.toLinearMap =
        κ.symm.toLinearMap ∘ₗ (h.symm.toLinearMap ∘ₗ ((ρ⁻¹).toLinearMap ∘ₗ x) ∘ₗ g₀.toLinearMap) := by
      apply LinearMap.ext
      intro v
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [LinearEquiv.symm_apply_eq]
      show _ = ρ (h (κ (κ.symm _)))
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      show _ = (ρ * ρ⁻¹) _
      rw [mul_inv_cancel]
      rfl
    unfold om
    rw [ey, hlaw]
    have a1 := hdet (ρ * h * κ)
    have a0 := hdet h
    have s0 : sq ^ (vP P (qOf P) (LinearEquiv.det h : E) * ((n' + c' : ℕ) : ℤ)) ≠ 0 := zpow_ne_zero _ hsq
    field_simp

end PI.TwistedEisensteinNonvanishing.W
end
end

section
open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

open Loc LocE

section F

theorem fIdx_lt {k₀ c n p : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) : fIdx k₀ c n p < n + c := by
  unfold fIdx
  split_ifs <;> omega

theorem fIdx_inj {k₀ c n p p' : ℕ} (hp : p < n + c) (hp' : p' < n + c) (hk : k₀ ≤ n)
    (h : fIdx k₀ c n p = fIdx k₀ c n p') : p = p' := by
  unfold fIdx at h
  split_ifs at h <;> omega

theorem fIdx_notD {k₀ c n kj p : ℕ} (hk : k₀ ≤ kj) (hp : p < kj + c) :
    ¬(kj ≤ fIdx k₀ c n p ∧ fIdx k₀ c n p < n) := by
  unfold fIdx
  split_ifs <;> omega

theorem fIdx_D {k₀ c n kj p : ℕ} (hk : k₀ ≤ kj) (hp1 : kj + c ≤ p) (hp2 : p < n + c) :
    kj ≤ fIdx k₀ c n p ∧ fIdx k₀ c n p < n := by
  unfold fIdx
  split_ifs <;> omega

end F

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem mem_stdAt' {n : ℕ} (v : Sp E n) : v ∈ stdAt E n P ↔ ∀ l, IntAt P (v l) := by
  exact PI.TwNormLat.W.mem_stdAt P v

theorem eN_mem' (n j : ℕ) : eN E n j ∈ stdAt E n P := by
  rw [mem_stdAt']
  intro l
  unfold eN
  split_ifs
  · exact ia_one (P := P)
  · exact ia_zero (P := P)

theorem jq_int {q kj n c : ℕ} {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ JQ P q kj n c) (j : ℕ)
    (l : Fin (n + c)) : IntAt P (g (eN E (n + c) j) l) := by
  have h1 : ∀ x, g x ∈ stdAt E (n + c) P ↔ x ∈ stdAt E (n + c) P := (Subgroup.mem_inf.mp hg).1
  exact (mem_stdAt' _).mp ((h1 _).mpr (eN_mem' _ _)) l

theorem mem_parL' {q kj n c : ℕ} (x : Sp E (n + c)) :
    x ∈ parL P q kj n c ↔ ∀ l : Fin (n + c), IntAt P (((q : E) ^ (if kj ≤ l.1 ∧ l.1 < n then (1 : ℤ) else 0))⁻¹ * x l) := by
  unfold parL sclLat
  rw [Submodule.mem_comap, mem_stdAt']
  simp only [LinearMap.coe_restrictScalars, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.coe_proj,
    Function.eval, smul_eq_mul]

theorem jq_DA {q kj n c : ℕ} {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ JQ P q kj n c) (j : ℕ)
    (hj : ¬(kj ≤ j ∧ j < n)) (l : Fin (n + c)) (hl : kj ≤ l.1 ∧ l.1 < n) :
    IntAt P (g (eN E (n + c) j) l / (q : E)) := by
  have h2 : ∀ x, g x ∈ parL P q kj n c ↔ x ∈ parL P q kj n c := (Subgroup.mem_inf.mp hg).2
  have hej : eN E (n + c) j ∈ parL P q kj n c := by
    rw [mem_parL']
    intro l'
    unfold eN
    by_cases hl' : l'.1 = j
    · rw [if_neg (by rw [hl']; exact hj), if_pos hl']
      simpa using ia_one (P := P)
    · rw [if_neg hl', mul_zero]
      exact ia_zero (P := P)
  have h3 := (mem_parL' _).mp ((h2 _).mpr hej) l
  rw [if_pos hl, zpow_one] at h3
  rwa [div_eq_inv_mul]

theorem apply_sum' {N : ℕ} (f : Sp E N ≃ₗ[E] Sp E N) (v : Sp E N) (i : Fin N) :
    f v i = ∑ m : Fin N, v m * f (eN E N m.1) i := by
  have hv : v = ∑ m : Fin N, v m • eN E N m.1 := by
    funext l
    simp [eN, Finset.sum_apply, Fin.val_inj]
  conv_lhs => rw [hv]
  rw [map_sum]
  simp [Finset.sum_apply, map_smul]

theorem atN_of_lt {N : ℕ} (v : Fin N → E) {i : ℕ} (hi : i < N) : atN v i = v ⟨i, hi⟩ := by
  unfold atN
  rw [dif_pos hi]

theorem row_tr {N' n c k₀ : ℕ} (hk : k₀ ≤ n) (g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (y : HomE E N' (n + c))
    (s p : ℕ) (hp : p < n + c) :
    atN ((g.toLinearMap ∘ₗ y) (eN E N' s)) (fIdx k₀ c n p) =
      ∑ p'' ∈ Finset.range (n + c), atN (g (eN E (n + c) (fIdx k₀ c n p''))) (fIdx k₀ c n p) *
        atN (y (eN E N' s)) (fIdx k₀ c n p'') := by
  have himg : (Finset.range (n + c)).image (fIdx k₀ c n) = Finset.range (n + c) := by
    apply Finset.eq_of_subset_of_card_le
    · intro m hm
      obtain ⟨p'', hp'', rfl⟩ := Finset.mem_image.mp hm
      exact Finset.mem_range.mpr (fIdx_lt hk (Finset.mem_range.mp hp''))
    · rw [Finset.card_image_of_injOn]
      intro a ha b hb hab
      exact fIdx_inj (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hk hab
  have hsum : ∑ p'' ∈ Finset.range (n + c), atN (g (eN E (n + c) (fIdx k₀ c n p''))) (fIdx k₀ c n p) *
        atN (y (eN E N' s)) (fIdx k₀ c n p'') =
      ∑ m ∈ Finset.range (n + c), atN (g (eN E (n + c) m)) (fIdx k₀ c n p) * atN (y (eN E N' s)) m := by
    conv_rhs => rw [← himg]
    rw [Finset.sum_image (fun a ha b hb hab => fIdx_inj (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hk hab)]
  have hA : ∀ {M : ℕ} (v : Fin M → E) (m : Fin M), atN v m.1 = v m := fun v m => by
    rw [atN_of_lt v m.isLt]
  have hB : ∀ (v : Fin (n + c) → E), atN v (fIdx k₀ c n p) = v ⟨_, fIdx_lt hk hp⟩ := fun v => atN_of_lt v _
  rw [hsum, Finset.sum_range (fun m => atN (g (eN E (n + c) m)) (fIdx k₀ c n p) * atN (y (eN E N' s)) m)]
  simp only [hA, hB, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [apply_sum' g]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [mul_comm]

theorem reduction_absNorm_mul_eq_zero {z : E} (hz : IntAt P z) : redP P ((qOf P : E) * z) = 0 := by
  obtain ⟨r, s, hs, hsz⟩ := hz
  refine PI.TwChrOne.Pf.reduction_eq_zero P (p := (Ideal.absNorm P.asIdeal : 𝓞 E)) (r := r) (s := s)
    (Ideal.absNorm_mem P.asIdeal) hs ?_
  rw [← hsz, map_natCast]
  unfold qOf
  ring

theorem reduction_eq_zero_of_integral_inv_mul {z : E} (hp : (Ideal.absNorm P.asIdeal).Prime) (hz : IntAt P (z / (qOf P : E))) :
    redP P z = 0 := by
  have hq := NTA.q_ne (P := P) hp
  have e : z = (qOf P : E) * (z / (qOf P : E)) := by field_simp
  rw [e]
  exact reduction_absNorm_mul_eq_zero hz

theorem reduction_det' {m : ℕ} (M : Matrix (Fin m) (Fin m) E) (hM : ∀ s t, IntAt P (M s t)) :
    redP P M.det = (M.map (redP P)).det := by
  exact PI.TwChrOne.Pf.reduction_det P M hM

theorem redP_sum' {ι : Type} (s : Finset ι) (f : ι → E) (hf : ∀ i, IntAt P (f i)) :
    redP P (∑ i ∈ s, f i) = ∑ i ∈ s, redP P (f i) := by
  exact PI.TwChrOne.Pf.reduction_sum₂ P s f hf

theorem block_entry_zero_zero {N' N : ℕ} (q k₀ c' n' c n : ℕ) (x : HomE E N' N) (p p' : ℕ) :
    entB q k₀ c' n' c n 0 0 x p p' = atN (x (eN E N' (fIdx k₀ c' n' p'))) (fIdx k₀ c n p) := by
  simp [entB, scE]

section Law

variable (P)

def CondQ (q k₀ r c' n' c n : ℕ) (x : HomE E (n' + c') (n + c)) : Prop :=
  (∀ p p', p < n + c → p' < n' + c' → IntAt P (entB q k₀ c' n' c n 0 0 x p p')) ∧
  (∀ p p', r ≤ p → p < n + c → p' < r → IntAt P (entB q k₀ c' n' c n 0 0 x p p' / (q : E)))

def AYm (q k₀ r c' n' c n : ℕ) (x : HomE E (n' + c') (n + c)) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun s t : Fin r => entB q k₀ c' n' c n 0 0 x s.1 t.1

variable {P}

def GA (k₀ r c n : ℕ) (g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun s p : Fin r => atN (g (eN E (n + c) (fIdx k₀ c n p.1))) (fIdx k₀ c n s.1)

open Classical in
theorem phi_eq (q : ℕ) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ) (x : HomE E (n' + c') (n + c)) :
    PhiQ q ξ k₀ r c' n' c n x =
      if CondQ P q k₀ r c' n' c n x then unitV ξ (AYm q k₀ r c' n' c n x).det else 0 := by
  unfold PhiQ CondQ AYm
  split_ifs with ha hb hb <;> first | rfl | exact absurd ha hb | exact absurd hb ha

theorem redP_zero' : redP P (0 : E) = 0 := by
  exact PI.TwChrOne.Pf.reduction_zero P

theorem reduction_add' {a b : E} (ha : IntAt P a) (hb : IntAt P b) : redP P (a + b) = redP P a + redP P b := by
  have h := redP_sum' (P := P) (Finset.univ : Finset (Fin 2)) ![a, b] (by intro i; fin_cases i <;> simpa)
  simpa [Fin.sum_univ_two] using h

theorem reduction_sum' {ι : Type} (s : Finset ι) (f : ι → E) (hf : ∀ i ∈ s, IntAt P (f i)) :
    redP P (∑ i ∈ s, f i) = ∑ i ∈ s, redP P (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [redP_zero']
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      reduction_add' (hf i (Finset.mem_insert_self i s))
        (ia_sum (P := P) s f (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

variable {q k₀ r c' n' c n kj : ℕ} (hqq : q = qOf P) (h1 : r = kj + c) (h2 : k₀ ≤ kj) (h3 : kj ≤ n)
  (h4 : r ≤ n' + c') (h5 : k₀ ≤ n')
include hqq h1 h2 h3 h4 h5

theorem ent_comp (g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (y : HomE E (n' + c') (n + c)) (p p' : ℕ) (hp : p < n + c) :
    entB q k₀ c' n' c n 0 0 (g.toLinearMap ∘ₗ y) p p' =
      ∑ p'' ∈ Finset.range (n + c), atN (g (eN E (n + c) (fIdx k₀ c n p''))) (fIdx k₀ c n p) *
        entB q k₀ c' n' c n 0 0 y p'' p' := by
  rw [block_entry_zero_zero, row_tr (le_trans h2 h3) g y _ p hp]
  refine Finset.sum_congr rfl (fun p'' _ => ?_)
  rw [block_entry_zero_zero]

theorem gm_int {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ JQ P q kj n c) (p p'' : ℕ) (hp : p < n + c) :
    IntAt P (atN (g (eN E (n + c) (fIdx k₀ c n p''))) (fIdx k₀ c n p)) := by
  unfold atN
  split_ifs with hlt
  · exact jq_int hg _ _
  · exact ia_zero (P := P)

theorem supp_comp {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ JQ P q kj n c) {y : HomE E (n' + c') (n + c)}
    (hy : CondQ P q k₀ r c' n' c n y) : CondQ P q k₀ r c' n' c n (g.toLinearMap ∘ₗ y) := by
  obtain ⟨hyA, hyB⟩ := hy
  refine ⟨fun p p' hp hp' => ?_, fun p p' hrp hp hp' => ?_⟩
  · rw [ent_comp hqq h1 h2 h3 h4 h5 g y p p' hp]
    exact ia_sum (P := P) _ _ (fun p'' hp'' => ia_mul (P := P)
      (gm_int hqq h1 h2 h3 h4 h5 hg p p'' hp) (hyA p'' p' (Finset.mem_range.mp hp'') hp'))
  · rw [ent_comp hqq h1 h2 h3 h4 h5 g y p p' hp, Finset.sum_div]
    refine ia_sum (P := P) _ _ (fun p'' hp'' => ?_)
    have hp''' := Finset.mem_range.mp hp''
    by_cases hr : r ≤ p''
    · rw [mul_div_assoc]
      exact ia_mul (P := P) (gm_int hqq h1 h2 h3 h4 h5 hg p p'' hp) (hyB p'' p' hr hp''' hp')
    · push_neg at hr
      rw [mul_div_right_comm]
      refine ia_mul (P := P) ?_ (hyA p'' p' hp''' (by omega))
      rw [atN_of_lt _ (fIdx_lt (le_trans h2 h3) hp)]
      have hD := fIdx_D (k₀ := k₀) (c := c) (n := n) (kj := kj) h2 (by omega) hp
      have hnD := fIdx_notD (k₀ := k₀) (c := c) (n := n) (kj := kj) (p := p'') h2 (by omega)
      exact jq_DA hg _ hnD ⟨_, fIdx_lt (le_trans h2 h3) hp⟩ hD

theorem val_comp (hp : (Ideal.absNorm P.asIdeal).Prime) {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ JQ P q kj n c)
    {y : HomE E (n' + c') (n + c)} (hy : CondQ P q k₀ r c' n' c n y) :
    (AYm q k₀ r c' n' c n (g.toLinearMap ∘ₗ y)).map (redP P) =
      (GA k₀ r c n g).map (redP P) * (AYm q k₀ r c' n' c n y).map (redP P) := by
  subst hqq
  obtain ⟨hyA, hyB⟩ := hy
  ext s t
  have hs : s.1 < n + c := by have := s.isLt; omega
  have ht : t.1 < n' + c' := by have := t.isLt; omega
  simp only [Matrix.map_apply, Matrix.mul_apply, AYm, GA, Matrix.of_apply]
  rw [ent_comp rfl h1 h2 h3 h4 h5 g y s.1 t.1 hs,
    reduction_sum' _ _ (fun p'' hp'' => ia_mul (P := P) (gm_int rfl h1 h2 h3 h4 h5 hg s.1 p'' hs)
      (hyA p'' t.1 (Finset.mem_range.mp hp'') ht)),
    ← Finset.sum_range_add_sum_Ico _ (show r ≤ n + c by omega)]
  have hzero : ∑ p'' ∈ Finset.Ico r (n + c), redP P (atN (g (eN E (n + c) (fIdx k₀ c n p''))) (fIdx k₀ c n s.1) *
      entB (qOf P) k₀ c' n' c n 0 0 y p'' t.1) = 0 := by
    refine Finset.sum_eq_zero (fun p'' hp'' => ?_)
    obtain ⟨h6, h7⟩ := Finset.mem_Ico.mp hp''
    rw [reduction_mul' (P := P) (gm_int rfl h1 h2 h3 h4 h5 hg s.1 p'' hs) (hyA p'' t.1 h7 ht),
      reduction_eq_zero_of_integral_inv_mul hp (hyB p'' t.1 h6 h7 t.isLt), mul_zero]
  rw [hzero, add_zero, Finset.sum_range]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [reduction_mul' (P := P) (gm_int rfl h1 h2 h3 h4 h5 hg s.1 x.1 hs) (hyA x.1 t.1 (by have := x.isLt; omega) ht)]

theorem det_comp (hp : (Ideal.absNorm P.asIdeal).Prime) {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ JQ P q kj n c)
    {y : HomE E (n' + c') (n + c)} (hy : CondQ P q k₀ r c' n' c n y) :
    redP P (AYm q k₀ r c' n' c n (g.toLinearMap ∘ₗ y)).det =
      redP P (GA k₀ r c n g).det * redP P (AYm q k₀ r c' n' c n y).det := by
  have hgy := supp_comp hqq h1 h2 h3 h4 h5 hg hy
  rw [reduction_det' (AYm q k₀ r c' n' c n (g.toLinearMap ∘ₗ y))
      (fun s t => hgy.1 s.1 t.1 (by have := s.isLt; omega) (by have := t.isLt; omega)),
    val_comp hqq h1 h2 h3 h4 h5 hp hg hy, Matrix.det_mul,
    reduction_det' (GA k₀ r c n g) (fun s t => gm_int hqq h1 h2 h3 h4 h5 hg s.1 t.1 (by have := s.isLt; omega)),
    reduction_det' (AYm q k₀ r c' n' c n y)
      (fun s t => hy.1 s.1 t.1 (by have := s.isLt; omega) (by have := t.isLt; omega))]

end Law

private theorem unitV_eq_mul_of_redP_eq_mul (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a b d : E} (ha : IsUnit (redP P a))
    (hd : redP P d = redP P a * redP P b) : unitV ξ d = unitV ξ a * unitV ξ b := by
  by_cases hb : IsUnit (redP P b)
  · have hd' : IsUnit (redP P d) := by rw [hd]; exact ha.mul hb
    unfold unitV
    rw [dif_pos hd', dif_pos ha, dif_pos hb, ← Units.val_mul, ← map_mul]
    congr 2
    ext
    simp [hd]
  · have hd' : ¬ IsUnit (redP P d) := by
      rw [hd]
      intro h
      exact hb (isUnit_of_mul_isUnit_right h)
    unfold unitV
    rw [dif_neg hd', dif_neg hb, mul_zero]

theorem jacobian_transformation_law : JLawP := by
  intro E K _ _ _ _ P hp hq ξ k₀ r c' n' c n kj h1 h2 h3 h4 h5 κ hκ
  classical
  have hk : k₀ ≤ n := le_trans h2 h3
  have hg : κ.symm ∈ JQ P (qOf P) kj n c := (JQ P (qOf P) kj n c).inv_mem hκ
  have hcomp : ∀ y : HomE E (n' + c') (n + c), κ.toLinearMap ∘ₗ (κ.symm.toLinearMap ∘ₗ y) = y := by
    intro y
    ext x i
    simp

  obtain ⟨M0, hM0⟩ : ∃ M0 : Matrix (Fin (n + c)) (Fin (n' + c')) E, M0 = fun i j =>
      if ∃ t, t < r ∧ i.1 = fIdx k₀ c n t ∧ j.1 = fIdx k₀ c' n' t then 1 else 0 := ⟨_, rfl⟩
  have hent0 : ∀ p p', p < n + c → p' < n' + c' →
      entB (qOf P) k₀ c' n' c n 0 0 (Matrix.toLin' M0) p p' = if p' < r ∧ p = p' then 1 else 0 := by
    intro p p' hp hp'
    have hfp := fIdx_lt hk hp
    have hfp' := fIdx_lt (c := c') h5 hp'
    rw [block_entry_zero_zero, atN_of_lt _ hfp, Matrix.toLin'_apply]
    rw [show (Matrix.mulVec M0 (eN E (n' + c') (fIdx k₀ c' n' p'))) ⟨fIdx k₀ c n p, hfp⟩ =
        M0 ⟨fIdx k₀ c n p, hfp⟩ ⟨fIdx k₀ c' n' p', hfp'⟩ by
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single ⟨fIdx k₀ c' n' p', hfp'⟩]
      · simp [eN]
      · intro b _ hb
        simp only [eN]
        rw [if_neg (fun h => hb (Fin.ext h)), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h]
    rw [hM0]
    beta_reduce
    by_cases hc : p' < r ∧ p = p'
    · rw [if_pos hc, if_pos ⟨p', hc.1, by show fIdx k₀ c n p = fIdx k₀ c n p'; rw [hc.2], rfl⟩]
    · rw [if_neg hc, if_neg]
      rintro ⟨t, ht, e1, e2⟩
      have i1 := fIdx_inj hp (by omega : t < n + c) hk e1
      have i2 := fIdx_inj hp' (by omega : t < n' + c') h5 e2
      exact hc ⟨by omega, by omega⟩
  have hy0 : CondQ P (qOf P) k₀ r c' n' c n (Matrix.toLin' M0) := by
    refine ⟨fun p p' hp hp' => ?_, fun p p' hrp hp hp' => ?_⟩
    · rw [hent0 p p' hp hp']
      split_ifs
      · exact ia_one (P := P)
      · exact ia_zero (P := P)
    · rw [hent0 p p' hp (by omega), if_neg (by omega), zero_div]
      exact ia_zero (P := P)
  have hA0 : AYm (qOf P) k₀ r c' n' c n (Matrix.toLin' M0) = 1 := by
    ext s t
    simp only [AYm, Matrix.of_apply, Matrix.one_apply]
    rw [hent0 _ _ (by have := s.isLt; omega) (by have := t.isLt; omega)]
    by_cases hst : s = t
    · subst hst
      simp
    · rw [if_neg, if_neg hst]
      rintro ⟨-, h⟩
      exact hst (Fin.ext h)
  have hr1 : redP P (1 : E) = 1 := PI.TwChrOne.Pf.reduction_one₂ P

  have hd1 := det_comp rfl h1 h2 h3 h4 h5 hp hg hy0
  have hd2 := det_comp rfl h1 h2 h3 h4 h5 hp hκ (supp_comp rfl h1 h2 h3 h4 h5 hg hy0)
  rw [hcomp, hd1, hA0, Matrix.det_one, hr1, mul_one] at hd2
  have hGA : IsUnit (redP P (GA k₀ r c n κ.symm).det) :=
    ⟨⟨_, _, by rw [mul_comm]; exact hd2.symm, hd2.symm⟩, rfl⟩
  refine ⟨unitV ξ (GA k₀ r c n κ.symm).det, ?_, fun y => ?_⟩
  · unfold unitV
    rw [dif_pos hGA]
    exact Units.ne_zero _
  rw [phi_eq, phi_eq]
  by_cases hy : CondQ P (qOf P) k₀ r c' n' c n y
  · have hgy := supp_comp rfl h1 h2 h3 h4 h5 hg hy
    rw [if_pos hgy, if_pos hy]
    exact unitV_eq_mul_of_redP_eq_mul ξ hGA (det_comp rfl h1 h2 h3 h4 h5 hp hg hy)
  · have hgy : ¬ CondQ P (qOf P) k₀ r c' n' c n (κ.symm.toLinearMap ∘ₗ y) := by
      intro h'
      apply hy
      have h6 := supp_comp rfl h1 h2 h3 h4 h5 hκ h'
      rwa [hcomp y] at h6
    rw [if_neg hgy, if_neg hy, mul_zero]

end PI.TwistedEisensteinNonvanishing.W
end
end
