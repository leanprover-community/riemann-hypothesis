import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumValsQOfInvariant
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumPiFinsetFinSuccCons

section
open NumberField IsDedekindDomain Formalism.L2.Col

namespace GlobalTheory

theorem pow_dvd_of_mul_natCast_eq_of_notMem_prime {R : Type} [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R)
    (hI : I.IsPrime) {q : ℕ} (hq : q.Prime) (hqI : (q : R) ∈ I) {s : R} (hs : s ∉ I) :
    ∀ (d i : ℕ) (r : R), s * (i : R) = (q : R) ^ d * r → q ^ d ∣ i := by
  intro d
  induction d with
  | zero => intro i r _; simp
  | succ d ih =>
    intro i r h
    have hiI : (i : R) ∈ I := by
      have : s * (i : R) ∈ I := by
        rw [h, pow_succ', mul_assoc]
        exact I.mul_mem_right _ hqI
      exact (hI.mem_or_mem this).resolve_left hs
    have hdvd : q ∣ i := by
      by_contra hn
      have hc : IsCoprime (q : R) (i : R) := by
        have := (Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hq).2 hn)).map (Int.castRingHom R)
        simpa using this
      obtain ⟨a, b, hab⟩ := hc
      exact hI.one_notMem (hab ▸ I.add_mem (I.mul_mem_left a hqI) (I.mul_mem_left b hiI))
    obtain ⟨j, rfl⟩ := hdvd
    have hq0 : (q : R) ≠ 0 := by exact_mod_cast hq.ne_zero
    have h' : s * (j : R) = (q : R) ^ d * r := by
      apply mul_left_cancel₀ hq0
      push_cast at h
      linear_combination h
    rw [pow_succ']
    exact Nat.mul_dvd_mul_left q (ih j r h')

theorem sum_valsQ_eq_of_support_intAt : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)), (qOf P).Prime → ∀ (K : Type) [Field K] (f : E → K) (A₀ : ℕ), (∀ a, f a ≠ 0 → IntAt P ((qOf P : E) ^ A₀ * a)) → ∀ A B : ℕ, A₀ ≤ A → ∑ a ∈ LocE.valsQ E (qOf P) A B, f a = ∑ a ∈ LocE.valsQ E (qOf P) A₀ B, f a := by
  intro E _ _ P hq K _ f A₀ hf A B hA
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hA
  have hqP : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem _
  generalize qOf P = q at *
  have hq0 : (q : E) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hpos : 0 < q ^ d := pow_pos hq.pos d
  symm
  apply Finset.sum_subset
  · intro a ha
    simp only [LocE.valsQ, Finset.mem_image, Finset.mem_range] at ha ⊢
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨q ^ d * i, ?_, ?_⟩
    · have : q ^ (A₀ + d + B) = q ^ d * q ^ (A₀ + B) := by ring
      rw [this]
      exact Nat.mul_lt_mul_of_pos_left hi hpos
    · push_cast
      field_simp
      ring
  · intro a ha hna
    by_contra hfa
    apply hna
    simp only [LocE.valsQ, Finset.mem_image, Finset.mem_range] at ha ⊢
    obtain ⟨i, hi, rfl⟩ := ha
    obtain ⟨r, s, hs, hrs⟩ := hf _ hfa
    have h1 : s * (i : 𝓞 E) = (q : 𝓞 E) ^ d * r := by
      apply FaithfulSMul.algebraMap_injective (𝓞 E) E
      simp only [map_mul, map_pow, map_natCast]
      rw [← hrs]
      field_simp
      ring
    obtain ⟨j, rfl⟩ := pow_dvd_of_mul_natCast_eq_of_notMem_prime P.asIdeal P.isPrime hq hqP hs d i r h1
    refine ⟨j, ?_, ?_⟩
    · have : q ^ (A₀ + d + B) = q ^ d * q ^ (A₀ + B) := by ring
      rw [this] at hi
      exact Nat.lt_of_mul_lt_mul_left hi
    · push_cast
      field_simp
      ring

end GlobalTheory
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory

theorem boxSum_eq_of_funBdd : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (P : HeightOneSpectrum (𝓞 E)), (qOf P).Prime → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) (N : ℕ), FunBdd P N f → ∀ A B : ℕ, N ≤ A → N ≤ B → boxSum P A B f = boxSum P N N f := by
  intro E _ _ K _ _ P hq ι _ _ f N hf A B hA hB
  have hqK : (qOf P : K) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  unfold boxSum
  refine weighted_sum_piFinset ι E K
    (fun g => (∀ a, g a ≠ 0 → IntAt P ((qOf P : E) ^ N * a)) ∧
      ∀ a u, IntAt P u → g (a + (qOf P : E) ^ N * u) = g a) _ _ _ _ ?_ f ?_
  · rintro g ⟨h1, h2⟩
    rw [sum_valsQ_of_invariant E P K g N h2 A B hB,
      sum_valsQ_eq_of_support_intAt E P hq K g N h1 A N hA]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hB
    rw [Nat.add_sub_cancel_left, pow_add]
    field_simp
  · intro t i
    refine ⟨fun a ha => ?_, fun a u hu => ?_⟩
    · simpa using hf.1 _ ha i
    · have e : Function.update t i (a + (qOf P : E) ^ N * u)
          = Function.update t i a + ((qOf P : E) ^ N) • (Pi.single i u : ι → E) := by
        funext j
        by_cases hj : j = i
        · subst hj; simp
        · simp [hj]
      simp only [e]
      refine hf.2 _ _ fun j => ?_
      by_cases hj : j = i
      · subst hj; simpa using hu
      · simpa [hj] using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

end GlobalTheory
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightedBoxSumAtPrime_eq_of_boundedSchwartz : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (P : HeightOneSpectrum (𝓞 E)), (qOf P).Prime → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) (N : ℕ), FunBdd P N f → ∀ A B : ℕ, N ≤ A → N ≤ B → boxSum P A B f = boxSum P N N f := by
  first | exact @GlobalTheory.boxSum_eq_of_funBdd | exact GlobalTheory.boxSum_eq_of_funBdd | (intros; apply GlobalTheory.boxSum_eq_of_funBdd <;> assumption)
end
