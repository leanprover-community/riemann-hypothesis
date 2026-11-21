import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussGLZero

section
namespace GlobalTheory.NatCastNotMemPrimeIdeal

theorem natCast_notMem_of_prime_ne {L : Type} [Field L] [NumberField L]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : q ≠ p)
    (hqw : (q : NumberField.RingOfIntegers L) ∈ w.asIdeal) :
    (p : NumberField.RingOfIntegers L) ∉ w.asIdeal := by
  intro hpw
  have hc : IsCoprime (q : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hq hp).mpr hne)
  obtain ⟨a, b, hab⟩ := hc
  have h1 : (a : NumberField.RingOfIntegers L) * (q : NumberField.RingOfIntegers L)
      + (b : NumberField.RingOfIntegers L) * (p : NumberField.RingOfIntegers L) = 1 := by
    have := congrArg (Int.cast : ℤ → NumberField.RingOfIntegers L) hab
    push_cast at this
    exact this
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← h1]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hqw) (w.asIdeal.mul_mem_left _ hpw)

end GlobalTheory.NatCastNotMemPrimeIdeal
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.ChiUnit

open GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing

theorem unitOff_mul {N : ℕ} {u v : ℂ} (hu : UnitOff N u) (hv : UnitOff N v) : UnitOff N (u * v) := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  obtain ⟨hv0, m, hm1, hm2⟩ := hv
  refine ⟨mul_ne_zero hu0 hv0, n + m, ?_, ?_⟩
  · have e : (N : ℂ) ^ (n + m) * (u * v) = ((N : ℂ) ^ n * u) * ((N : ℂ) ^ m * v) := by rw [pow_add]; ring
    rw [e]; exact hn1.mul hm1
  · have e : (N : ℂ) ^ (n + m) * (u * v)⁻¹ = ((N : ℂ) ^ n * u⁻¹) * ((N : ℂ) ^ m * v⁻¹) := by rw [pow_add, mul_inv]; ring
    rw [e]; exact hn2.mul hm2

theorem unitOff_inv {N : ℕ} {u : ℂ} (hu : UnitOff N u) : UnitOff N u⁻¹ := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  exact ⟨inv_ne_zero hu0, n, hn2, by rw [inv_inv]; exact hn1⟩

theorem unitOff_one (N : ℕ) : UnitOff N 1 :=
  ⟨one_ne_zero, 0, by simpa using isIntegral_one, by simpa using isIntegral_one⟩

theorem unitOff_pow {N : ℕ} {u : ℂ} (hu : UnitOff N u) (k : ℕ) : UnitOff N (u ^ k) := by
  induction k with
  | zero => simpa using unitOff_one N
  | succ k ih => rw [pow_succ]; exact unitOff_mul ih hu

theorem unitOff_zpow {N : ℕ} {u : ℂ} (hu : UnitOff N u) (k : ℤ) : UnitOff N (u ^ k) := by
  rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast]; exact unitOff_pow hu m
  · rw [_root_.zpow_neg, zpow_natCast]; exact unitOff_inv (unitOff_pow hu m)

theorem unitOff_prod {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, UnitOff N (f i)) :
    UnitOff N (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using unitOff_one N
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact unitOff_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem unitOff_conj {N : ℕ} {u : ℂ} (hu : UnitOff N u) : UnitOff N (starRingEnd ℂ u) := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  refine ⟨(map_ne_zero _).2 hu0, n, ?_, ?_⟩
  · have := hn1.map (RingHom.toIntAlgHom (starRingEnd ℂ))
    simpa [map_mul, map_pow, map_natCast] using this
  · have := hn2.map (RingHom.toIntAlgHom (starRingEnd ℂ))
    simpa [map_mul, map_pow, map_natCast, map_inv₀] using this

theorem unitOff_of_pow {N : ℕ} {u : ℂ} {k : ℕ} (hk : 0 < k) (hu : UnitOff N (u ^ k)) : UnitOff N u := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  have hN : IsIntegral ℤ ((N : ℂ) ^ (n * (k - 1))) := by
    have : IsIntegral ℤ (N : ℂ) := by simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (N : ℤ))
    exact this.pow _
  refine ⟨fun h => hu0 (by rw [h, zero_pow hk.ne']), n, ?_, ?_⟩
  · refine IsIntegral.of_pow hk ?_
    have e : ((N : ℂ) ^ n * u) ^ k = (N : ℂ) ^ (n * (k - 1)) * ((N : ℂ) ^ n * u ^ k) := by
      rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]
      congr 2
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
      simp only [Nat.add_sub_cancel, zero_add]
      ring
    rw [e]; exact hN.mul hn1
  · refine IsIntegral.of_pow hk ?_
    have e : ((N : ℂ) ^ n * u⁻¹) ^ k = (N : ℂ) ^ (n * (k - 1)) * ((N : ℂ) ^ n * (u ^ k)⁻¹) := by
      rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add, inv_pow]
      congr 2
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
      simp only [Nat.add_sub_cancel, zero_add]
      ring
    rw [e]; exact hN.mul hn2

theorem unitOff_of_pow_eq_one (N : ℕ) {u : ℂ} {k : ℕ} (hk : 0 < k) (hu : u ^ k = 1) : UnitOff N u :=
  unitOff_of_pow hk (by rw [hu]; exact unitOff_one N)

theorem unitOff_of_mul_eq {N m : ℕ} {a b : ℂ} (ha : IsIntegral ℤ a) (hb : IsIntegral ℤ b)
    (hab : a * b = (N : ℂ) ^ m) (hN : N ≠ 0) : UnitOff N a := by
  have hNm : (N : ℂ) ^ m ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hN)
  have ha0 : a ≠ 0 := fun h => hNm (by rw [← hab, h, zero_mul])
  refine ⟨ha0, m, ?_, ?_⟩
  · have : IsIntegral ℤ ((N : ℂ) ^ m) := by
      have : IsIntegral ℤ (N : ℂ) := by simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (N : ℤ))
      exact this.pow _
    exact this.mul ha
  · have e : (N : ℂ) ^ m * a⁻¹ = b := by rw [← hab]; field_simp
    rw [e]; exact hb

end GlobalTheory.ChiUnit

namespace GlobalTheory.ChiUnit
open GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing

theorem LR {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (n : ℕ) (h : χ ^ n = 1)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (k : Lˣ) : (χ.locK w k) ^ n = 1 := by
  have e : (χ ^ n).locK w k = (χ.locK w k) ^ n := by
    simp [Formalism.L2.Host.HChar.locK, Formalism.L2.Host.HChar.loc]
  rw [← e, h]
  simp [Formalism.L2.Host.HChar.locK, Formalism.L2.Host.HChar.loc]

theorem locK_eq_val {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L)
    {w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)} (hw : χ.UnrAt w) (k : Lˣ) (a : 𝓞 L) (hk : (k : L) = a)
    (h1 : a ∈ w.asIdeal) (h2 : a ∉ w.asIdeal ^ 2) : χ.locK w k = χ.val w :=
  χ.val_eq hw _ (by
    unfold Formalism.L2.Host.IsUnifAt
    rw [GlobalTheory.TypeValues.val_atFin w k a hk, GlobalTheory.TypeValues.intValuation_eq_of_mem h1 h2])

end GlobalTheory.ChiUnit

namespace GlobalTheory.ChiUnit
open GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing

theorem finite_ramified_places_hecke_character {D : D7} (χ : Formalism.L2.Host.HChar D.host.E)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E), (∀ k : Fin 2, ¬Formalism.L2.Host.OverP D.host (D.host.g k) v) → χ.UnrAt v) :
    {w | ¬ χ.UnrAt w}.Finite := by
  have hm : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hI : Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  refine (Ideal.finite_factors hI).subset fun w hw => ?_
  simp only [Set.mem_setOf_eq] at hw ⊢
  rw [Ideal.dvd_span_singleton]
  by_contra hc
  refine hw (h w fun k hk => hc ?_)
  unfold Formalism.L2.Host.OverP at hk
  rw [Nat.cast_mul]
  fin_cases k
  · exact Ideal.mul_mem_right _ _ hk
  · exact Ideal.mul_mem_left _ _ hk

theorem not_mem_of_prime_ne {L : Type} [Field L] [NumberField L] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : q ≠ p) (hqw : (q : 𝓞 L) ∈ w.asIdeal) : (p : 𝓞 L) ∉ w.asIdeal := by
  first
  | exact @_root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne
  | exact _root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne
  | (apply _root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne ..)

end GlobalTheory.ChiUnit
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.ValUnit
open GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing GlobalTheory.ChiUnit Formalism.L2.Host

private theorem exists_pow_eq_span_lemma {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) :
    ∃ h : ℕ, 0 < h ∧ (v.asIdeal ^ h).IsPrincipal := by
  have hv0 : v.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 L)) := mem_nonZeroDivisors_of_ne_zero v.ne_bot
  refine ⟨orderOf (ClassGroup.mk0 ⟨v.asIdeal, hv0⟩), orderOf_pos _, ?_⟩
  rw [← ClassGroup.mk0_eq_one_iff (pow_mem hv0 _)]
  have h1 := pow_orderOf_eq_one (ClassGroup.mk0 ⟨v.asIdeal, hv0⟩)
  rwa [← map_pow, SubmonoidClass.mk_pow] at h1

theorem exists_pow_eq_span {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) :
    ∃ (h : ℕ) (a : 𝓞 L), 0 < h ∧ a ≠ 0 ∧ v.asIdeal ^ h = Ideal.span {a} := by
  obtain ⟨h, hh, hp⟩ := exists_pow_eq_span_lemma v
  obtain ⟨a, ha⟩ := hp.principal
  have hne : v.asIdeal ^ h ≠ ⊥ :=
    nonZeroDivisors.ne_zero (pow_mem (mem_nonZeroDivisors_of_ne_zero v.ne_bot) h)
  refine ⟨h, a, hh, ?_, ha⟩
  rintro rfl
  exact hne (by rw [ha]; exact Ideal.span_singleton_eq_bot.2 rfl)

private theorem exists_pow_sub_one_lemma {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))
    (a : 𝓞 L) (hw : a ∉ w.asIdeal) : ∃ m : ℕ, 0 < m ∧ ∀ k : ℕ, a ^ (m * k) - 1 ∈ w.asIdeal := by
  haveI := w.isMaximal
  letI : Field (𝓞 L ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  haveI : Finite (𝓞 L ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  letI : Fintype (𝓞 L ⧸ w.asIdeal) := Fintype.ofFinite _
  have hne : Ideal.Quotient.mk w.asIdeal a ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨Fintype.card (𝓞 L ⧸ w.asIdeal) - 1, Nat.sub_pos_of_lt Fintype.one_lt_card, fun k => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, pow_mul,
    FiniteField.pow_card_sub_one_eq_one _ hne, one_pow, sub_self]

theorem exists_pow_sub_one {L : Type} [Field L] [NumberField L] (S : Finset (HeightOneSpectrum (𝓞 L))) (a : 𝓞 L)
    (ha : ∀ w ∈ S, a ∉ w.asIdeal) : ∃ M : ℕ, 0 < M ∧ ∀ w ∈ S, a ^ M - 1 ∈ w.asIdeal := by
  have key : ∀ w : HeightOneSpectrum (𝓞 L), a ∉ w.asIdeal →
      ∃ m : ℕ, 0 < m ∧ ∀ k : ℕ, a ^ (m * k) - 1 ∈ w.asIdeal :=
    fun w hw => exists_pow_sub_one_lemma w a hw
  choose! m hm0 hmk using key
  refine ⟨∏ w ∈ S, m w, Finset.prod_pos fun w hw => hm0 w (ha w hw), fun w hw => ?_⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m hw
  rw [hk]
  exact hmk w (ha w hw) k

private theorem isIntegral_natCast_lemma (q : ℕ) : IsIntegral ℤ (q : ℂ) := by
  have h := (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℂ (q : ℤ)))
  simpa using h

private theorem unitOff_one_lemma {q : ℕ} : UnitOff q 1 := by
  unfold UnitOff
  refine ⟨one_ne_zero, 0, ?_, ?_⟩
  · rw [pow_zero, mul_one]
    exact isIntegral_one
  · rw [pow_zero, inv_one, mul_one]
    exact isIntegral_one

private theorem unitOff_mul_lemma {q : ℕ} {u w : ℂ} (hu : UnitOff q u) (hw : UnitOff q w) :
    UnitOff q (u * w) := by
  unfold UnitOff at hu hw ⊢
  obtain ⟨hu0, m, hu1, hu2⟩ := hu
  obtain ⟨hw0, n, hw1, hw2⟩ := hw
  refine ⟨mul_ne_zero hu0 hw0, m + n, ?_, ?_⟩
  · have e : (q : ℂ) ^ (m + n) * (u * w) = ((q : ℂ) ^ m * u) * ((q : ℂ) ^ n * w) := by ring
    rw [e]
    exact hu1.mul hw1
  · have e : (q : ℂ) ^ (m + n) * (u * w)⁻¹ = ((q : ℂ) ^ m * u⁻¹) * ((q : ℂ) ^ n * w⁻¹) := by
      rw [mul_inv]
      ring
    rw [e]
    exact hu2.mul hw2

private theorem unitOff_inv_lemma {q : ℕ} {u : ℂ} (hu : UnitOff q u) : UnitOff q u⁻¹ := by
  unfold UnitOff at hu ⊢
  obtain ⟨hu0, m, hu1, hu2⟩ := hu
  exact ⟨inv_ne_zero hu0, m, hu2, by rwa [inv_inv]⟩

private theorem unitOff_of_pow_lemma {q : ℕ} {u : ℂ} {N : ℕ} (hN : 0 < N) (hu : UnitOff q (u ^ N)) :
    UnitOff q u := by
  unfold UnitOff at hu ⊢
  obtain ⟨hu0, m, hu1, hu2⟩ := hu
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  have hu0' : u ≠ 0 := fun h => hu0 (by rw [h, zero_pow (Nat.succ_ne_zero N')])
  refine ⟨hu0', m, ?_, ?_⟩
  · apply IsIntegral.of_pow (Nat.succ_pos N')
    have e : ((q : ℂ) ^ m * u) ^ (N' + 1) = (q : ℂ) ^ (m * N') * ((q : ℂ) ^ m * u ^ (N' + 1)) := by ring
    rw [e]
    exact ((isIntegral_natCast_lemma q).pow _).mul hu1
  · apply IsIntegral.of_pow (Nat.succ_pos N')
    have e : ((q : ℂ) ^ m * u⁻¹) ^ (N' + 1) =
        (q : ℂ) ^ (m * N') * ((q : ℂ) ^ m * (u ^ (N' + 1))⁻¹) := by
      rw [← inv_pow]
      ring
    rw [e]
    exact ((isIntegral_natCast_lemma q).pow _).mul hu2

private theorem unitOff_conj_lemma {q : ℕ} {u : ℂ} (hu : UnitOff q u) : UnitOff q (starRingEnd ℂ u) := by
  unfold UnitOff at hu ⊢
  obtain ⟨hu0, m, hu1, hu2⟩ := hu
  refine ⟨(map_ne_zero _).2 hu0, m, ?_, ?_⟩
  · have h := map_isIntegral_int (starRingEnd ℂ) hu1
    simpa [map_mul, map_pow, map_natCast] using h
  · have h := map_isIntegral_int (starRingEnd ℂ) hu2
    simpa [map_mul, map_pow, map_natCast, map_inv₀] using h

private theorem unitOff_norm_lemma {q : ℕ} {u : ℂ} (hu : UnitOff q u) : UnitOff q ((‖u‖ : ℝ) : ℂ) := by
  have hsq : ((‖u‖ : ℝ) : ℂ) ^ 2 = u * starRingEnd ℂ u := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have h2 : UnitOff q (((‖u‖ : ℝ) : ℂ) ^ 2) := by
    rw [hsq]
    exact unitOff_mul_lemma hu (unitOff_conj_lemma hu)
  exact unitOff_of_pow_lemma (by norm_num) h2

theorem unitOff_div_norm {q : ℕ} {z : ℂ} (hz : UnitOff q z) : UnitOff q (z / (‖z‖ : ℂ)) := by
  rw [div_eq_mul_inv]
  exact unitOff_mul_lemma hz (unitOff_inv_lemma (unitOff_norm_lemma hz))

private theorem unitOff_zpow_lemma {q : ℕ} {u : ℂ} (hu : UnitOff q u) (k : ℤ) : UnitOff q (u ^ k) := by
  have hpow : ∀ n : ℕ, UnitOff q (u ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero]; exact unitOff_one_lemma
    | succ n ih => rw [pow_succ]; exact unitOff_mul_lemma ih hu
  cases k with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast]; exact hpow n
  | negSucc n => rw [zpow_negSucc]; exact unitOff_inv_lemma (hpow _)

private theorem unitOff_prod_lemma {q : ℕ} {I : Type} (s : Finset I) (f : I → ℂ)
    (hf : ∀ i ∈ s, UnitOff q (f i)) : UnitOff q (∏ i ∈ s, f i) :=
  Finset.prod_induction f (UnitOff q) (fun _ _ => unitOff_mul_lemma) unitOff_one_lemma hf

private theorem unitOff_val_lemma {L : Type} [Field L] [NumberField L] (φ : L →+* ℂ) (b c : 𝓞 L) (q N : ℕ)
    (hb : b ≠ 0) (hc : c * b = (q : 𝓞 L) ^ N) : UnitOff q (φ (algebraMap (𝓞 L) L b)) := by
  have hφb : φ (algebraMap (𝓞 L) L b) ≠ 0 := by
    rw [Ne, map_eq_zero_iff φ φ.injective, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 L) L)]
    exact hb
  have hint : ∀ x : 𝓞 L, IsIntegral ℤ (φ (algebraMap (𝓞 L) L x)) := fun x =>
    map_isIntegral_int φ (RingOfIntegers.isIntegral_coe x)
  have hrel : φ (algebraMap (𝓞 L) L c) * φ (algebraMap (𝓞 L) L b) = (q : ℂ) ^ N := by
    rw [← map_mul, ← map_mul, hc, map_pow, map_pow, map_natCast, map_natCast]
  unfold UnitOff
  refine ⟨hφb, N, ((isIntegral_natCast_lemma q).pow N).mul (hint b), ?_⟩
  rw [← hrel, mul_assoc, mul_inv_cancel₀ hφb, mul_one]
  exact hint c

theorem unitOff_val : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (I : Type) [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (q : ℕ), χ.HasInf φ n → {w | ¬ χ.UnrAt w}.Finite → (∀ w, χ.TameAt w) → χ.UnrAt v → (q : 𝓞 L) ∈ v.asIdeal → GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing.UnitOff q ((χ.val v : ℂˣ) : ℂ) := by
  intro L _ _ χ I _ φ n v q hinf hfin htame hunr hq
  classical
  obtain ⟨S, hSmem⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 L)), ∀ w, w ∈ S ↔ ¬ χ.UnrAt w :=
    ⟨hfin.toFinset, fun w => by simp⟩
  have hS : ∀ w, w ∉ S → χ.UnrAt w := fun w hw => by
    by_contra hc
    exact hw ((hSmem w).2 hc)
  have hvS : v ∉ S := fun hv => (hSmem v).1 hv hunr
  obtain ⟨h, a, hh, ha0, hspan⟩ := exists_pow_eq_span v
  have hav : ∀ w : HeightOneSpectrum (𝓞 L), a ∈ w.asIdeal → w = v := by
    intro w haw
    have h1 : v.asIdeal ^ h ≤ w.asIdeal := by
      rw [hspan, Ideal.span_singleton_le_iff_mem]
      exact haw
    have h2 : v.asIdeal ≤ w.asIdeal := fun x hx =>
      w.isPrime.mem_of_pow_mem h (h1 (Ideal.pow_mem_pow hx h))
    exact (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top h2)).symm
  have haS : ∀ w ∈ S, a ∉ w.asIdeal := fun w hw haw => hvS (hav w haw ▸ hw)
  obtain ⟨M, hM, hMS⟩ := exists_pow_sub_one S a haS
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 L, b = a ^ M := ⟨_, rfl⟩
  have hb0 : b ≠ 0 := by
    rw [hb]
    exact pow_ne_zero _ ha0
  have hbL : algebraMap (𝓞 L) L b ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 L) L)]
    exact hb0
  obtain ⟨k, hkL⟩ : ∃ k : Lˣ, (k : L) = algebraMap (𝓞 L) L b := ⟨Units.mk0 _ hbL, rfl⟩
  have hbw : ∀ w : HeightOneSpectrum (𝓞 L), w ≠ v → b ∉ w.asIdeal := fun w hw hbw' =>
    hw (hav w (w.isPrime.mem_of_pow_mem M (hb ▸ hbw')))
  have hord : ∀ w : HeightOneSpectrum (𝓞 L), w ≠ v → ordF w k = 0 := by
    intro w hw
    unfold ordF
    rw [hkL, (HeightOneSpectrum.valuation_eq_one_iff_notMem (v := w) (K := L)).2 (hbw w hw)]
    simp
  have hbv : b ∈ v.asIdeal := by
    have hav' : a ∈ v.asIdeal := by
      have h3 : a ∈ v.asIdeal ^ h := by
        rw [hspan]
        exact Ideal.mem_span_singleton_self a
      exact Ideal.pow_le_self hh.ne' h3
    rw [hb]
    exact Ideal.pow_mem_of_mem _ hav' _ hM
  have hordv : 0 < ordF v k := by
    unfold ordF
    rw [hkL]
    have hlt : v.valuation L (algebraMap (𝓞 L) L b) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem (v := v) (K := L) b).2 hbv
    have hne : v.valuation L (algebraMap (𝓞 L) L b) ≠ 0 := (Valuation.ne_zero_iff _).2 hbL
    have hlog : WithZero.log (v.valuation L (algebraMap (𝓞 L) L b)) < 0 := by
      rw [WithZero.log_lt_iff_lt_exp hne]
      simpa using hlt
    omega
  have hfp : (∏ᶠ (w : HeightOneSpectrum (𝓞 L)) (_ : w ∉ S), χ.val w ^ ordF w k) =
      χ.val v ^ ordF v k := by
    rw [finprod_eq_single _ v (fun w hw => by simp only [hord w hw, zpow_zero, finprod_one]),
      finprod_eq_if, if_pos hvS]
  have e1 : ∀ (w : HeightOneSpectrum (𝓞 L)) (x : L),
      Valued.v (algebraMap L (w.adicCompletion L) x) = w.valuation L x := fun w x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) x
  have hloc : ∏ w ∈ S, χ.locK w k = 1 := by
    apply Finset.prod_eq_one
    intro w hw
    have hwv : w ≠ v := fun e => hvS (e ▸ hw)
    have hunit : Valued.v ((atFin w k : (w.adicCompletion L)ˣ) : w.adicCompletion L) = 1 := by
      have e2 : ((atFin w k : (w.adicCompletion L)ˣ) : w.adicCompletion L) =
          algebraMap L _ (algebraMap (𝓞 L) L b) := by
        rw [← hkL]
        rfl
      rw [e2, e1, HeightOneSpectrum.valuation_eq_one_iff_notMem (v := w) (K := L)]
      exact hbw w hwv
    have hsub : Valued.v (((atFin w k : (w.adicCompletion L)ˣ) : w.adicCompletion L) - 1) ≤
        WithZero.exp (-((1 : ℕ) : ℤ)) := by
      have e3 : ((atFin w k : (w.adicCompletion L)ˣ) : w.adicCompletion L) - 1 =
          algebraMap L _ (algebraMap (𝓞 L) L (b - 1)) := by
        rw [map_sub, map_one, map_sub, map_one, ← hkL]
        rfl
      rw [e3, e1, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.intValuation_le_pow_iff_mem, pow_one, hb]
      exact hMS w hw
    exact htame w (atFin w k) hunit hsub
  have hPR : χ.inf k * (∏ w ∈ S, χ.locK w k) *
      (∏ᶠ (w : HeightOneSpectrum (𝓞 L)) (_ : w ∉ S), χ.val w ^ ordF w k) = 1 := by
    first
      | exact GlobalTheory.HeckeProduct.productRule χ S hS k
      | exact hecke_product_rule L χ S hS k
      | exact PI.HeckeProdW.productRule χ S hS k
      | exact GlobalTheory.TypeValues.productRule χ S hS k
      | exact GlobalTheory.HeckeProduct.hchar_productRule L χ S hS k
  rw [hfp, hloc, mul_one] at hPR
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ordF v k = N := ⟨(ordF v k).toNat, (Int.toNat_of_nonneg hordv.le).symm⟩
  have hNpos : 0 < N := by omega
  rw [hN, zpow_natCast] at hPR
  have hPR2 := eq_inv_of_mul_eq_one_right hPR
  have hValPow : ((χ.val v : ℂˣ) : ℂ) ^ N = ((χ.inf k : ℂˣ) : ℂ)⁻¹ := by
    rw [← Units.val_pow_eq_pow_val, hPR2, Units.val_inv_eq_inv_val]
  have hqb : (q : 𝓞 L) ^ (h * M) ∈ Ideal.span {b} := by
    have e4 : Ideal.span {b} = v.asIdeal ^ (h * M) := by
      rw [hb, ← Ideal.span_singleton_pow, ← hspan, pow_mul]
    rw [e4]
    exact Ideal.pow_mem_pow hq _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hqb
  apply unitOff_of_pow_lemma hNpos
  rw [hValPow]
  apply unitOff_inv_lemma
  rw [hinf k]
  refine unitOff_prod_lemma Finset.univ _ (fun i _ => ?_)
  apply unitOff_zpow_lemma
  apply unitOff_div_norm
  rw [hkL]
  exact unitOff_val_lemma (φ i) b c q (h * M) hb0 hc

end GlobalTheory.ValUnit
end
