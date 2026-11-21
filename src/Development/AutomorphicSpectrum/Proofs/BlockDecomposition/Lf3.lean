import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasProdMoebiusConvOfNormLe
import BuildAid.ForwardExisting

section
section
namespace GlobalTheory.CompanionTheory.DivisorCount

private lemma two_mul_add_one_le_three_pow (k : ℕ) : 2 * k + 1 ≤ 3 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

private lemma two_mul_add_one_le_two_mul_two_pow (k : ℕ) : 2 * k + 1 ≤ 2 * 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [pow_succ]; omega

private lemma card_divisors_sq_prime_pow {p k : ℕ} (hp : p.Prime) :
    (((p ^ k) ^ 2).divisors).card = 2 * k + 1 := by
  rw [← pow_mul, Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]
  ring

theorem card_divisors_sq_le_strong (n : ℕ) :
    (n ^ 2).divisors.card ≤ 2 * n ∧ (Odd n → (n ^ 2).divisors.card ≤ n) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    rw [card_divisors_sq_prime_pow hp]
    rcases hp.eq_two_or_odd' with rfl | hodd
    · refine ⟨?_, fun h => ?_⟩
      · exact two_mul_add_one_le_two_mul_two_pow k
      · exact absurd h (by
          rw [Nat.not_odd_iff_even]
          exact (Nat.even_pow.mpr ⟨even_two, hk.ne'⟩))
    · have h3 : 3 ≤ p := by
        have := hp.two_le
        rcases hodd with ⟨m, rfl⟩
        omega
      have h : 2 * k + 1 ≤ p ^ k :=
        (two_mul_add_one_le_three_pow k).trans (Nat.pow_le_pow_left h3 k)
      exact ⟨by omega, fun _ => h⟩
  | zero => simp
  | one => simp
  | coprime a b ha hb hab iha ihb =>
    have hcop : Nat.Coprime (a ^ 2) (b ^ 2) := Nat.Coprime.pow 2 2 hab
    have hcard : ((a * b) ^ 2).divisors.card
        = (a ^ 2).divisors.card * (b ^ 2).divisors.card := by
      rw [mul_pow, hcop.card_divisors_mul]
    rw [hcard]
    have hodd : Odd a ∨ Odd b := by
      by_contra h
      rw [not_or] at h
      have h1 : Even a := Nat.not_odd_iff_even.mp h.1
      have h2 : Even b := Nat.not_odd_iff_even.mp h.2
      have : 2 ∣ Nat.gcd a b := Nat.dvd_gcd h1.two_dvd h2.two_dvd
      rw [hab] at this
      omega
    constructor
    · rcases hodd with h | h
      · calc _ ≤ a * (2 * b) := Nat.mul_le_mul (iha.2 h) ihb.1
          _ = 2 * (a * b) := by ring
      · calc _ ≤ (2 * a) * b := Nat.mul_le_mul iha.1 (ihb.2 h)
          _ = 2 * (a * b) := by ring
    · intro h
      obtain ⟨h1, h2⟩ := Nat.odd_mul.mp h
      exact Nat.mul_le_mul (iha.2 h1) (ihb.2 h2)

theorem card_divisors_sq_le_two_mul (n : ℕ) :
    (((n ^ 2).divisors.card : ℕ) : ℝ) ≤ 2 * n := by
  exact_mod_cast (card_divisors_sq_le_strong n).1

end GlobalTheory.CompanionTheory.DivisorCount
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_divisors_sq_le_two_mul' : ∀ n : ℕ, (((n ^ 2).divisors.card : ℕ) : ℝ) ≤ 2 * n := by
  atlas_forward_decl GlobalTheory.CompanionTheory.DivisorCount.card_divisors_sq_le_two_mul
end

section
section
open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.HeckeSq

theorem norm_char_prime {N : ℕ} (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) :
    ‖χ (p : ZMod N)‖ = 1 := by
  haveI : NeZero N := ⟨by rintro rfl; exact hpN (dvd_zero p)⟩
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime p N).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpN)
  rw [← hu]
  exact DirichletCharacter.unit_norm_eq_one χ u

theorem norm_prime_sq_pow {k N : ℕ} {χ : DirichletCharacter ℂ N} {a : ℕ → ℂ} {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ N) {α β : ℂ} (hm : α * β = χ p * (p : ℂ) ^ (k - 1)) (hn : ‖α‖ = ‖β‖)
    (hpow : ∀ j, a (p ^ j) = ∑ i ∈ Finset.range (j + 1), α ^ i * β ^ (j - i)) (j : ℕ) :
    ‖a (p ^ (2 * j))‖ ≤ ((2 * j + 1 : ℕ) : ℝ) * ((p ^ j : ℕ) : ℝ) ^ (k - 1) := by
  have hsq : ‖α‖ ^ 2 = (p : ℝ) ^ (k - 1) := by
    have h := congrArg norm hm
    rw [norm_mul, norm_mul, norm_char_prime χ hp hpN, one_mul, norm_pow, Complex.norm_natCast, ← hn] at h
    rw [sq]; exact h
  rw [hpow]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ i ∈ Finset.range (2 * j + 1),
      ‖α ^ i * β ^ (2 * j - i)‖ = ((p ^ j : ℕ) : ℝ) ^ (k - 1) := by
    intro i hi
    have hi' : i ≤ 2 * j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [norm_mul, norm_pow, norm_pow, ← hn, ← pow_add, Nat.add_sub_cancel' hi', pow_mul, hsq]
    push_cast
    rw [← pow_mul, ← pow_mul, mul_comm]
  rw [Finset.sum_congr rfl hterm]
  simp

theorem card_divisors_prime_sq {p : ℕ} (hp : p.Prime) (j : ℕ) :
    ((p ^ j) ^ 2).divisors.card = 2 * j + 1 := by
  rw [← pow_mul, mul_comm j 2, Nat.divisors_prime_pow hp]
  simp

theorem norm_sq_le : ∀ (k N : ℕ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ), IsEig k N χ a → E2a →
    (∀ p : ℕ, p.Prime → ¬ p ∣ N → ∃ α β : ℂ, α + β = a p ∧ α * β = χ p * (p : ℂ) ^ (k - 1) ∧ ‖α‖ = ‖β‖) →
    ∀ n : ℕ, Nat.Coprime n N → ‖a (n ^ 2)‖ ≤ (((n ^ 2).divisors.card : ℕ) : ℝ) * (n : ℝ) ^ (k - 1) := by
  intro k N χ a he hE hS n
  obtain ⟨hmul, hpp⟩ := hE k N χ a he
  obtain ⟨h0, h1, -⟩ := he
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p j hp hj =>
    intro hc
    have hpN : ¬ p ∣ N := fun hd =>
      hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc (dvd_pow_self p hj.ne') hd)
    obtain ⟨α, β, hs, hm, hn⟩ := hS p hp hpN
    have hb := norm_prime_sq_pow hp hpN hm hn (hpp p hp α β hs hm) j
    rw [card_divisors_prime_sq hp j, ← pow_mul, mul_comm j 2]
    exact hb
  | zero =>
    intro _
    simp [h0]
  | one =>
    intro _
    simp [h1]
  | coprime m n hm hn hmn ihm ihn =>
    intro hc
    have hcm : Nat.Coprime m N := Nat.Coprime.coprime_mul_right hc
    have hcn : Nat.Coprime n N := Nat.Coprime.coprime_mul_left hc
    have hsq : Nat.Coprime (m ^ 2) (n ^ 2) := Nat.Coprime.pow 2 2 hmn
    rw [mul_pow, hmul _ _ hsq, norm_mul, hsq.card_divisors_mul]
    push_cast
    rw [mul_pow]
    calc ‖a (m ^ 2)‖ * ‖a (n ^ 2)‖
        ≤ (((m ^ 2).divisors.card : ℝ) * (m : ℝ) ^ (k - 1)) *
            (((n ^ 2).divisors.card : ℝ) * (n : ℝ) ^ (k - 1)) :=
          mul_le_mul (ihm hcm) (ihn hcn) (norm_nonneg _) (le_trans (norm_nonneg _) (ihm hcm))
      _ = _ := by ring

end GlobalTheory.CompanionTheory.HeckeSq
end

open Ad3 Ad3.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_square_coefficient_le_divisor_bound : ∀ (k N : ℕ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ), IsEig k N χ a → E2a → (∀ p : ℕ, p.Prime → ¬ p ∣ N → ∃ α β : ℂ, α + β = a p ∧ α * β = χ p * (p : ℂ) ^ (k - 1) ∧ ‖α‖ = ‖β‖) → ∀ n : ℕ, Nat.Coprime n N → ‖a (n ^ 2)‖ ≤ (((n ^ 2).divisors.card : ℕ) : ℝ) * (n : ℝ) ^ (k - 1) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.HeckeSq.norm_sq_le
end

section
section
open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.LocalSeries

theorem good_prime_local_series : E2a → E2b → ∀ (k N : ℕ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ), IsEig k N χ a → 1 ≤ k → ∀ p : ℕ, p.Prime → ∀ α β y s : ℂ, α ≠ 0 → β ≠ 0 → α + β = a p → α * β = χ p * (p : ℂ) ^ (k - 1) → ‖α / β‖ = 1 → ‖y‖ ≤ 1 → 0 < s.re → HasSum (fun j : ℕ => (χ p)⁻¹ ^ j * a (p ^ (2 * j)) * (y * (p : ℂ) ^ (-(s + k - 1))) ^ j) ((1 - (y * (p : ℂ) ^ (-s)) ^ 2) * ((1 - α / β * (y * (p : ℂ) ^ (-s)))⁻¹ * (1 - y * (p : ℂ) ^ (-s))⁻¹ * (1 - (α / β)⁻¹ * (y * (p : ℂ) ^ (-s)))⁻¹)) := by
  intro hE2a hE2b k N χ a hEig hk p hp α β y s hα hβ hsum hprod hr hy hs
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpos : 0 < p := hp.pos
  set c : ℂ := χ p with hc
  set P : ℂ := (p : ℂ) ^ (k - 1) with hP
  have hcP : c * P ≠ 0 := by rw [← hprod]; exact mul_ne_zero hα hβ
  have hc0 : c ≠ 0 := left_ne_zero_of_mul hcP
  have hP0 : P ≠ 0 := right_ne_zero_of_mul hcP

  have hX : ‖y * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hpos]
    have h1 : (p : ℝ) ^ (-s).re < 1 := by
      apply Real.rpow_lt_one_of_one_lt_of_neg
      · exact_mod_cast hp.one_lt
      · simpa using hs
    have h2 : 0 ≤ (p : ℝ) ^ (-s).re := by positivity
    calc ‖y‖ * (p : ℝ) ^ (-s).re ≤ 1 * (p : ℝ) ^ (-s).re := by gcongr
      _ < 1 := by simpa using h1

  have hpow : (p : ℂ) ^ (-(s + k - 1)) = (p : ℂ) ^ (-s) * P⁻¹ := by
    have hk1 : ((k : ℂ) - 1) = ((k - 1 : ℕ) : ℂ) := by
      rw [Nat.cast_sub hk]; simp
    have : -(s + k - 1) = -s + -(((k - 1 : ℕ) : ℂ)) := by
      rw [← hk1]; ring
    rw [this, Complex.cpow_add _ _ hp0, Complex.cpow_neg (p : ℂ) ((k - 1 : ℕ) : ℂ), Complex.cpow_natCast]
  have hmain := hE2b (α / β) (y * (p : ℂ) ^ (-s)) hr hX
  have hinv : c⁻¹ * β ^ 2 * P⁻¹ = (α / β)⁻¹ := by
    have h1 : c⁻¹ * P⁻¹ = (α * β)⁻¹ := by rw [hprod, mul_inv]
    calc c⁻¹ * β ^ 2 * P⁻¹ = (c⁻¹ * P⁻¹) * β ^ 2 := by ring
      _ = (α / β)⁻¹ := by rw [h1]; field_simp
  have hterm : ∀ j : ℕ, c⁻¹ ^ j * a (p ^ (2 * j)) * (y * (p : ℂ) ^ (-(s + k - 1))) ^ j =
      (∑ i ∈ Finset.range (2 * j + 1), (α / β) ^ i) * ((α / β)⁻¹ * (y * (p : ℂ) ^ (-s))) ^ j := by
    intro j
    have hcoef : a (p ^ (2 * j)) = β ^ (2 * j) * ∑ i ∈ Finset.range (2 * j + 1), (α / β) ^ i := by
      rw [(hE2a k N χ a hEig).2 p hp α β hsum hprod (2 * j), Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ 2 * j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hb : β ^ (2 * j) = β ^ (2 * j - i) * β ^ i := by
        rw [← pow_add, Nat.sub_add_cancel hi']
      rw [hb, div_pow]
      field_simp
    rw [hcoef, hpow, ← hinv, pow_mul β 2 j]
    simp only [mul_pow]
    ring
  rw [funext hterm]
  exact hmain

end GlobalTheory.CompanionTheory.LocalSeries
end

open Ad3 Ad3.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_square_coefficient_local_series : E2a → E2b → ∀ (k N : ℕ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ), IsEig k N χ a → 1 ≤ k → ∀ p : ℕ, p.Prime → ∀ α β y s : ℂ, α ≠ 0 → β ≠ 0 → α + β = a p → α * β = χ p * (p : ℂ) ^ (k - 1) → ‖α / β‖ = 1 → ‖y‖ ≤ 1 → 0 < s.re → HasSum (fun j : ℕ => (χ p)⁻¹ ^ j * a (p ^ (2 * j)) * (y * (p : ℂ) ^ (-(s + k - 1))) ^ j) ((1 - (y * (p : ℂ) ^ (-s)) ^ 2) * ((1 - α / β * (y * (p : ℂ) ^ (-s)))⁻¹ * (1 - y * (p : ℂ) ^ (-s))⁻¹ * (1 - (α / β)⁻¹ * (y * (p : ℂ) ^ (-s)))⁻¹)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LocalSeries.good_prime_local_series
end

section
section
namespace GlobalTheory.CompanionTheory.LSeriesBound

theorem lseriesSummable_twist_squares (M N k : ℕ) [NeZero M] (hM : N ∣ M)
    (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ) (hk : 1 ≤ k)
    (hb : ∀ n : ℕ, Nat.Coprime n N → ‖a (n ^ 2)‖ ≤ 2 * (n : ℝ) * (n : ℝ) ^ (k - 1))
    (s : ℂ) (hs : 2 < s.re) :
    LSeriesSummable (fun n : ℕ => DirichletCharacter.changeLevel hM χ⁻¹ (n : ZMod M) * a (n ^ 2))
      (s + k - 1) := by
  have hre : (s + (k : ℂ) - 1).re = s.re + (k : ℝ) - 1 := by simp
  have hsum : Summable (fun n : ℕ => 2 * (n : ℝ) ^ (1 - s.re)) :=
    (Real.summable_nat_rpow.mpr (by linarith)).mul_left 2
  refine Summable.of_norm_bounded hsum (fun n => ?_)
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hf : ‖DirichletCharacter.changeLevel hM χ⁻¹ (n : ZMod M) * a (n ^ 2)‖
      ≤ 2 * (n : ℝ) ^ k := by
    by_cases hu : IsUnit (n : ZMod M)
    · have hcop : Nat.Coprime n M := (ZMod.isUnit_iff_coprime n M).mp hu
      have hcopN : Nat.Coprime n N := Nat.Coprime.coprime_dvd_right hM hcop
      have h1 : ‖DirichletCharacter.changeLevel hM χ⁻¹ (n : ZMod M)‖ ≤ 1 :=
        DirichletCharacter.norm_le_one _ _
      have h2 := hb n hcopN
      have h3 : 2 * (n : ℝ) * (n : ℝ) ^ (k - 1) = 2 * (n : ℝ) ^ k := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        simp only [Nat.add_sub_cancel, pow_succ]
        ring
      rw [norm_mul]
      calc _ ≤ 1 * ‖a (n ^ 2)‖ := by gcongr
        _ ≤ 2 * (n : ℝ) ^ k := by rw [one_mul, ← h3]; exact h2
    · rw [MulChar.map_nonunit _ hu]
      simp only [zero_mul, norm_zero]
      positivity
  rw [hre, div_le_iff₀ (Real.rpow_pos_of_pos hn0 _)]
  have hpow : (n : ℝ) ^ (1 - s.re) * (n : ℝ) ^ (s.re + (k : ℝ) - 1) = (n : ℝ) ^ k := by
    rw [← Real.rpow_add hn0, ← Real.rpow_natCast]
    congr 1
    ring
  calc _ ≤ 2 * (n : ℝ) ^ k := hf
    _ = _ := by rw [← hpow]; ring

end GlobalTheory.CompanionTheory.LSeriesBound
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_twisted_square_coefficients : ∀ (M N k : ℕ) [NeZero M] (hM : N ∣ M) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ), 1 ≤ k → (∀ n : ℕ, Nat.Coprime n N → ‖a (n ^ 2)‖ ≤ 2 * (n : ℝ) * (n : ℝ) ^ (k - 1)) → ∀ s : ℂ, 2 < s.re → LSeriesSummable (fun n : ℕ => DirichletCharacter.changeLevel hM χ⁻¹ (n : ZMod M) * a (n ^ 2)) (s + k - 1) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LSeriesBound.lseriesSummable_twist_squares
end

section
open Ad3 Ad3.S
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped LSeries.notation

noncomputable section

namespace GlobalTheory.CompanionTheory.UnramifiedEisensteinCoefficients

theorem unr_mul (v : Pl) {μ₁ μ₂ : (Qv v)ˣ →* ℂˣ} (h1 : IsUnramifiedChar μ₁) (h2 : IsUnramifiedChar μ₂) :
    IsUnramifiedChar (μ₁ * μ₂) := by
  intro u hu
  have a1 := h1 hu
  have a2 := h2 hu
  simp only [MonoidHom.mem_ker, MonoidHom.mul_apply] at a1 a2 ⊢
  rw [a1, a2, mul_one]

theorem unr_inv (v : Pl) {μ : (Qv v)ˣ →* ℂˣ} (h : IsUnramifiedChar μ) : IsUnramifiedChar μ⁻¹ := by
  intro u hu
  have a1 := h hu
  simp only [MonoidHom.mem_ker, MonoidHom.inv_apply] at a1 ⊢
  rw [a1, inv_one]

theorem e2 : faceMap_comp_succAbove_castSucc → E2a → E2b → E2 := by
  intro h1b h2a h2b N M _ _ hM χ D a ha hsat c δ T hadm hT c' hc' s hs
  obtain ⟨⟨e, he⟩, hL⟩ := h1b
  have hk : 1 ≤ D.k := le_trans (by norm_num) D.three
  set ψ : DirichletCharacter ℂ M := DirichletCharacter.changeLevel hM χ⁻¹ with hψ
  set Nf : ℕ → ℂ := fun n => ψ (n : ZMod M) * a (n ^ 2) with hNf
  have hpure : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∃ α β : ℂ, α + β = a p ∧
      α * β = χ p * (p : ℂ) ^ (D.k - 1) ∧ ‖α‖ = ‖β‖ := by
    intro p hp hpN
    obtain ⟨q, hq⟩ : ∃ q : Nat.Primes, (q : ℕ) = p := ⟨⟨p, hp⟩, rfl⟩
    set v : Pl := e.symm q with hvdef
    have hv : pOf v = p := by rw [← he v, hvdef, Equiv.apply_symm_apply, hq]
    have hvb : v ∉ D.bad := by rw [hsat.1, hv]; exact hpN
    obtain ⟨α, β, h1, h2, h3⟩ := hsat.2 _ hvb
    refine ⟨α, β, by rw [← hv]; exact h1, by rw [← hv]; exact h2, ?_⟩
    have hu := (D.unit v).2 (unifUnit (Qv v))
    rw [h3, Units.val_div_eq_div_val, norm_div] at hu
    have hβ : ‖(β : ℂ)‖ ≠ 0 := by simp
    field_simp at hu
    exact hu
  have hb : ∀ n : ℕ, Nat.Coprime n N → ‖a (n ^ 2)‖ ≤ 2 * (n : ℝ) * (n : ℝ) ^ (D.k - 1) := by
    intro n hn
    refine (GlobalTheory.T.norm_square_coefficient_le_divisor_bound D.k N χ a ha h2a hpure n hn).trans ?_
    exact mul_le_mul_of_nonneg_right (GlobalTheory.T.card_divisors_sq_le_two_mul' n) (by positivity)
  have hsumm : LSeriesSummable Nf (s + D.k - 1) := GlobalTheory.T.summable_twisted_square_coefficients M N D.k hM χ a hk hb s hs
  have hN1 : Nf 1 = 1 := by simp [Nf, ha.2.1]
  have hNmul : ∀ {m n : ℕ}, m.Coprime n → Nf (m * n) = Nf m * Nf n := by
    intro m n h
    simp only [Nf, Nat.cast_mul, map_mul, mul_pow]
    rw [(h2a D.k N χ a ha).1 _ _ (Nat.Coprime.pow 2 2 h)]
    ring
  have hA := GlobalTheory.CompanionTheory.SquareEuler.hasProd_twist c' hN1 hNmul hsumm
  have h2s : 1 < (2 * s).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have hB := DirichletCharacter.LSeries_eulerProduct_hasProd (c' ^ 2) h2s
  have hP := hB.mul hA
  have hfac : ∀ v : Pl, (fun p : Nat.Primes => (1 - (c' ^ 2) ((p : ℕ) : ZMod M) * ((p : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ *
      ∑' j : ℕ, Nf ((p : ℕ) ^ j) * (c' ((p : ℕ) : ZMod M) * ((p : ℕ) : ℂ) ^ (-(s + D.k - 1))) ^ j) (e v) =
      Set.mulIndicator {v | v ∉ T} (fun v => lf3 (D.ν v) (localChar c v) s) v := by
    intro v
    dsimp only
    have hp : (pOf v).Prime := by rw [← he v]; exact (e v).2
    rw [he v]
    have hp0 : ((pOf v : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    by_cases hvT : v ∈ T
    · have hpM : pOf v ∣ M := (hT v).1 hvT
      have hnu : ¬ IsUnit ((pOf v : ℕ) : ZMod M) := by
        rw [ZMod.isUnit_iff_coprime]
        intro hc
        exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc hpM)
      have hc0 : c' ((pOf v : ℕ) : ZMod M) = 0 := MulChar.map_nonunit _ hnu
      have hc20 : (c' ^ 2) ((pOf v : ℕ) : ZMod M) = 0 := MulChar.map_nonunit _ hnu
      rw [Set.mulIndicator_of_notMem (by simpa using hvT), hc20, hc0]
      simp only [zero_mul, sub_zero, inv_one, one_mul]
      rw [tsum_eq_single 0]
      · simp [hN1]
      · intro j hj
        simp [hj]
    · rw [Set.mulIndicator_of_mem (by simpa using hvT)]
      have hvb : v ∉ D.bad := fun h => hvT (hadm.bad h)
      obtain ⟨α, β, hsum, hprod, hν⟩ := hsat.2 v hvb
      have hpM : ¬ pOf v ∣ M := fun h => hvT ((hT v).2 h)
      have hcp := hc' v hpM
      have hunit : IsUnit ((pOf v : ℕ) : ZMod M) :=
        (ZMod.isUnit_iff_coprime _ _).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM)
      have hψp : ψ ((pOf v : ℕ) : ZMod M) = (χ (pOf v))⁻¹ := by
        have h0 := DirichletCharacter.changeLevel_eq_cast_of_dvd χ⁻¹ hM hunit.unit
        rw [IsUnit.unit_spec] at h0
        rw [hψ, h0, ZMod.cast_natCast hM, MulChar.inv_apply_eq_inv']
      have hNfp : ∀ j, Nf (pOf v ^ j) = (χ (pOf v))⁻¹ ^ j * a (pOf v ^ (2 * j)) := by
        intro j
        simp only [Nf, Nat.cast_pow, map_pow, hψp]
        rw [← pow_mul, mul_comm j 2]
      have hu1 := D.unr v hvb
      have hu2 := hadm.unr v hvT
      have hα : (α : ℂ) ≠ 0 := α.ne_zero
      have hβ : (β : ℂ) ≠ 0 := β.ne_zero
      have hν' : ((D.ν v (unifUnit (Qv v)) : ℂˣ) : ℂ) = (α : ℂ) / β := by rw [hν, Units.val_div_eq_div_val]
      have hr : ‖(α : ℂ) / β‖ = 1 := by rw [← hν']; exact (D.unit v).2 _
      have hloc := GlobalTheory.T.hasSum_square_coefficient_local_series h2a h2b D.k N χ a ha hk (pOf v) hp α β (c' ((pOf v : ℕ) : ZMod M)) s hα hβ hsum hprod hr
        (DirichletCharacter.norm_le_one _ _) (by linarith)
      rw [tsum_congr (fun j => by rw [hNfp j]), hloc.tsum_eq]
      rw [lf3, hL v _ (unr_mul v hu1 hu2), hL v _ hu2, hL v _ (unr_mul v (unr_inv v hu1) hu2)]
      simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, hν', ← hcp]
      have hX2 : (c' ^ 2) ((pOf v : ℕ) : ZMod M) * ((pOf v : ℕ) : ℂ) ^ (-(2 * s)) =
          (c' ((pOf v : ℕ) : ZMod M) * ((pOf v : ℕ) : ℂ) ^ (-s)) ^ 2 := by
        rw [show -(2 * s) = -s + -s by ring, Complex.cpow_add _ _ hp0, MulChar.pow_apply' _ two_ne_zero]
        ring
      have hXn := GlobalTheory.CompanionTheory.SquareEuler.norm_X_lt_one c' (s := s) (by linarith) hp
      have h1X2 : 1 - (c' ((pOf v : ℕ) : ZMod M) * ((pOf v : ℕ) : ℂ) ^ (-s)) ^ 2 ≠ 0 := by
        intro h
        have h' : ‖c' ((pOf v : ℕ) : ZMod M) * ((pOf v : ℕ) : ℂ) ^ (-s)‖ ^ 2 = 1 := by
          rw [← norm_pow, show (c' ((pOf v : ℕ) : ZMod M) * ((pOf v : ℕ) : ℂ) ^ (-s)) ^ 2 = 1 by
            linear_combination -h, norm_one]
        nlinarith [norm_nonneg (c' ((pOf v : ℕ) : ZMod M) * ((pOf v : ℕ) : ℂ) ^ (-s))]
      rw [hX2, ← mul_assoc, inv_mul_cancel₀ h1X2, one_mul]
      ring
  have hP2 : HasProd (Set.mulIndicator {v | v ∉ T} (fun v => lf3 (D.ν v) (localChar c v) s))
      (L ↗(c' ^ 2) (2 * s) * L (↗c' * Nf) (s + D.k - 1)) := by
    have := (e.hasProd_iff).2 hP
    convert this using 1
    funext v
    exact (hfac v).symm
  rw [← hasProd_subtype_iff_mulIndicator] at hP2
  have hfun : (fun n : ℕ => (c' * DirichletCharacter.changeLevel hM χ⁻¹) (n : ZMod M) * a (n ^ 2)) =
      ↗c' * Nf := by
    funext n
    simp only [Pi.mul_apply, Nf, hψ, MulChar.coeToFun_mul]
    ring
  rw [DirichletCharacter.LFunction_eq_LSeries _ h2s, hfun]
  exact hP2.tprod_eq

end GlobalTheory.CompanionTheory.UnramifiedEisensteinCoefficients
end
end
