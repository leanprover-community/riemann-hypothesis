import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHcParamCodeWord
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelevelCoprimeOfModOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModulusBbDisjoint
import Development.AbelianVarietyTheory.Definitions.Foundations.AuxiliaryFrameNormalizedSpaces
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormNonnegOfImagQuadratic
import Development.AutomorphicArithmetic.PrimeDiscriminants.ExistsHost
import Development.AutomorphicArithmetic.PrimeDiscriminants.MuParallel

noncomputable section

namespace GlobalTheory.Mem.PreXModel

open Formalism.BasicNotions NumberField IsDedekindDomain

def NormPrimes : Prop :=
  ∀ (R : Ranks) (H : Host R) (M a N : ℕ), M ≠ 0 → Nat.Coprime a M → ∃ (π : 𝓞 H.E) (p : ℕ), p.Prime ∧ N < p ∧ (π : H.E) ∈ H.K ∧
    (π : H.E) * H.conj (π : H.E) = (p : H.E) ∧ π - (a : 𝓞 H.E) ∈ Ideal.span {(M : 𝓞 H.E)} ∧ p ≡ a ^ 2 [MOD M]

def SpacesExist : Prop :=
  ∀ (R : Ranks) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (_ : CMData F E)
    (T : ℕ) (_ : T.Prime) (pz : E) (_ : star pz * pz = T),
    ∃ S : Spaces R F E, S.T = T ∧ (∀ j, j ≤ R.m → ∀ τ : E →+* ℂ, (S.Y j).sig τ = sigYD R j) ∧
      (∀ j, 0 < j → j < R.m → HasHyperbolicAuxiliaryFrame S j) ∧ (∀ j, 1 ≤ j → j ≤ R.m → S.Vneg j = false) ∧
      (S.X R.m).hT S.z S.z = (S.T : E)


theorem mod_of_modEq {p c M : ℕ} (hc : 1 < c) (hcM : c ∣ M) (h : p ≡ 1 [MOD M]) : p % c = 1 := by
  have h1 : p ≡ 1 [MOD c] := h.of_dvd hcM
  unfold Nat.ModEq at h1
  rw [h1, Nat.mod_eq_of_lt hc]


theorem win_eq (T : ℝ) (hT : 0 < T) (n : ℝ) (hn : 0 < n) :
    (T ^ n * 4 / ((1 : ℕ) : ℝ)) ^ ((1 : ℝ) / n) * (2 : ℝ) ^ (-(2 : ℝ) / n) = T := by
  have h4 : (4 : ℝ) = 2 ^ (2 : ℝ) := by norm_num
  rw [Nat.cast_one, div_one, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hT.le, h4,
    ← Real.rpow_mul (by norm_num), mul_assoc, ← Real.rpow_add (by norm_num)]
  have h1 : n * (1 / n) = 1 := by field_simp
  have h2 : 2 * (1 / n) + -2 / n = 0 := by ring
  rw [h1, h2, Real.rpow_one, Real.rpow_zero, mul_one]

theorem exists_primes (hP : NormPrimes) (R : Ranks) (H : Host R) :
    ∃ (g : Fin 2 → ℕ) (π : Fin 2 → 𝓞 H.E) (p p' : ℕ), (∀ i, (g i).Prime) ∧ g 0 < g 1 ∧ g 1 < p ∧ p < p' ∧ p.Prime ∧ p'.Prime ∧
      p % 15 = 1 ∧ p' % 15 = 1 ∧ p % (H.QS * H.q * H.d) = 1 ∧ p' % (H.QS * H.q * H.d) = 1 ∧
      (∀ i, g i % (H.QS * H.q * H.d) = 1) ∧ (∀ i, (π i : H.E) ∈ H.K) ∧
      (∀ i, (π i : H.E) * H.conj (π i : H.E) = (g i : H.E)) ∧
      (∀ i, ((H.QS * H.q * H.d : ℕ) : 𝓞 H.E) ∣ π i - 1) ∧ 2 * R.f * R.k + 1 < g 0 ∧
      Disjoint (Formalism.CyclotomicNorms.BB R.r (g 0)) (Formalism.CyclotomicNorms.BB R.r (g 1)) ∧ 1 < H.QS * H.q * H.d := by
  set c := H.QS * H.q * H.d with hc
  have hc1 : 1 < c := by
    have h1 := H.QS_pos
    have h2 := H.hyp.1.pos
    have h3 := H.hyp.2.1.one_lt
    have : 0 < H.QS * H.q := by positivity
    rw [hc]; nlinarith
  have hc0 : c ≠ 0 := by omega
  obtain ⟨π0, g0, hg0, hg0N, hK0, hn0, hcg0, hm0⟩ := hP R H c 1 (2 * R.f * R.k + 1) hc0 (Nat.coprime_one_left _)
  obtain ⟨M, N, hM0, hcM, hBB⟩ := exists_modulus_bb_disjoint R.r g0 c hg0 hc0
  have hcop : Nat.Coprime (1 + M) (M ^ 2) := Nat.Coprime.pow_right _ (by simp)
  obtain ⟨π1, g1, hg1, hg1N, hK1, hn1, hcg1, hm1⟩ := hP R H (M ^ 2) (1 + M) (N + g0) (pow_ne_zero _ hM0) hcop
  obtain ⟨p, hp, hpN, hpm⟩ := Nat.exists_prime_gt_modEq_one g1 (k := 15 * c) (by omega)
  obtain ⟨p', hp', hpN', hpm'⟩ := Nat.exists_prime_gt_modEq_one p (k := 15 * c) (by omega)
  refine ⟨![g0, g1], ![π0, π1], p, p', ?_, ?_, hpN, hpN', hp, hp', mod_of_modEq (by norm_num) (dvd_mul_right _ _) hpm,
    mod_of_modEq (by norm_num) (dvd_mul_right _ _) hpm', mod_of_modEq hc1 (dvd_mul_left _ _) hpm,
    mod_of_modEq hc1 (dvd_mul_left _ _) hpm', ?_, ?_, ?_, ?_, hg0N, hBB g1 hg1 (by omega) hm1, hc1⟩
  · intro i; fin_cases i; exacts [hg0, hg1]
  · show g0 < g1; omega
  · intro i; fin_cases i
    · exact mod_of_modEq hc1 dvd_rfl (by simpa using hm0)
    · refine mod_of_modEq hc1 hcM ?_
      have h1 : g1 ≡ (1 + M) ^ 2 [MOD M] := hm1.of_dvd (dvd_pow_self _ two_ne_zero)
      refine h1.trans ?_
      have h2 : 1 + M ≡ 1 [MOD M] := by simp [Nat.ModEq]
      simpa using h2.pow 2
  · intro i; fin_cases i; exacts [hK0, hK1]
  · intro i; fin_cases i; exacts [hn0, hn1]
  · intro i; fin_cases i
    · simpa using Ideal.mem_span_singleton.1 hcg0
    · have h1 := Ideal.mem_span_singleton.1 hcg1
      have h2 : (c : 𝓞 H.E) ∣ (M : 𝓞 H.E) := Nat.cast_dvd_cast hcM
      have h3 : (M : 𝓞 H.E) ∣ ((M ^ 2 : ℕ) : 𝓞 H.E) := Nat.cast_dvd_cast (dvd_pow_self _ two_ne_zero)
      have h4 : π1 - 1 = (π1 - ((1 + M : ℕ) : 𝓞 H.E)) + (M : 𝓞 H.E) := by push_cast; ring
      show (c : 𝓞 H.E) ∣ π1 - 1
      rw [h4]
      exact dvd_add (h2.trans (h3.trans h1)) h2






theorem embLL_tauLL (B : Base) (τ : Tau B.R) : B.embLL.comp (B.tauLL τ) = B.host.emb τ := by
  unfold Base.tauLL Host.emb
  rw [← RingHom.comp_assoc, B.embE_φ₀]

theorem T_big (B : Pre) (X : PreX B) (u : B.Word) : 2 * B.R.f * B.R.N B.R.m + 1 < B.T u := by
  exact_mod_cast X.a_gt.trans (X.T_gt u)

theorem T_ne_g (B : Pre) (X : PreX B) (u : B.Word) (i : Fin 2) : B.T u ≠ B.host.g i := by
  intro h
  have h0 : B.host.g i ∣ B.host.QS * B.host.q * B.host.d * (B.host.g 0 * B.host.g 1) ^ 2 := by
    refine Dvd.dvd.mul_left (Dvd.dvd.trans ?_ (dvd_pow_self _ two_ne_zero)) _
    fin_cases i
    exacts [dvd_mul_right _ _, dvd_mul_left _ _]
  obtain ⟨y, hy⟩ := (Nat.cast_dvd_cast (α := 𝓞 B.host.E) h0).trans (X.piT_cong u)
  let yb : 𝓞 B.host.E := RingOfIntegers.mapRingHom (B.host.conj : B.host.E →+* B.host.E) y
  have hyE : (X.piT u : B.host.E) = 1 + (B.host.g i : B.host.E) * (y : B.host.E) := by
    have h1 := congrArg (fun z : 𝓞 B.host.E => (z : B.host.E)) (sub_eq_iff_eq_add'.1 hy)
    simpa using h1
  have hn := X.piT_norm u
  rw [hyE, h, map_add, map_one, map_mul, map_natCast] at hn
  have hyb : (yb : B.host.E) = B.host.conj (y : B.host.E) := rfl
  have h2 : ((B.host.g i : ℕ) : 𝓞 B.host.E) ∣ ((1 : ℤ) : 𝓞 B.host.E) := by
    refine ⟨1 - y - yb - (B.host.g i : 𝓞 B.host.E) * y * yb, RingOfIntegers.ext ?_⟩
    push_cast
    rw [← hyb] at hn
    show (1 : B.host.E) = (B.host.g i : B.host.E) * (1 - (y : B.host.E) - (yb : B.host.E) - (B.host.g i : B.host.E) * (y : B.host.E) * (yb : B.host.E))
    linear_combination hn
  have h3 := Formalism.L2.Col.Primes.natCast_dvd_intCast h2
  have h4 : B.host.g i ∣ 1 := by exact_mod_cast h3
  exact (B.host.g_prime i).one_lt.ne' (Nat.dvd_one.1 h4)

theorem normPrimes : NormPrimes := GlobalTheory.Mem.ImaginaryQuadraticNorm.exists_norm_prime






end GlobalTheory.Mem.PreXModel

end
