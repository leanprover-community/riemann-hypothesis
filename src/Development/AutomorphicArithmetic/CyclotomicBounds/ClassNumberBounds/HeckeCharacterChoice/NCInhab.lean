import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.NCField
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.LevelEqThreeFiveIff

open NumberField

namespace KStar.Choice

theorem ramLE_one_of_not_dvd (E L : Type*) [Field E] [NumberField E] [Field L]
    [NumberField L] [Algebra E L] {M l : ℕ} [NeZero M] [IsCyclotomicExtension {M} ℚ L]
    (hl : l.Prime) (h : ¬ l ∣ M) : RamLE E l 1 := by
  have := Fact.mk hl
  have hprime : (Ideal.span {(l : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hl.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hl
  obtain ⟨⟨P, h1, h2⟩⟩ := (Ideal.span {(l : ℤ)}).nonempty_primesOver (S := 𝓞 E)
  obtain ⟨⟨Q, hQ1, hQ2⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 L) P
  have hQ3 : Q.LiesOver (Ideal.span {(l : ℤ)}) := Ideal.LiesOver.trans Q P _
  have h3 := Ideal.ramificationIdx_below_dvd (R := ℤ) P Q
  rw [IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd l L Q h] at h3
  exact ⟨P, h1, h2, (Nat.dvd_one.1 h3).le⟩

theorem rootData_of_cyclotomic (E Ω : Type*) [Field E] [NumberField E] [Field Ω]
    [NumberField Ω] [Algebra E Ω] {M : ℕ} [NeZero M] [IsCyclotomicExtension {M} ℚ Ω]
    {S L : Finset ℕ} (hS : ∀ l ∈ S, l.Prime)
    (hM : ∀ l, l.Prime → l ≠ 2 → l ∣ M → l ∈ S ∨ l ∈ L)
    (hL : ∀ l ∈ L, l.Prime ∧ 3 < l ∧ RamLE E l 2) : RootData S L (rootNu E) (rootDeg E) :=
  rootData_field E hS (fun l hl h2 h3 h4 => ramLE_one_of_not_dvd E Ω hl fun h =>
    (hM l hl h2 h).elim h3 h4) hL

example (M : ℕ) [NeZero M] : RootData M.primeFactors ∅ (rootNu (CyclotomicField M ℚ))
    (rootDeg (CyclotomicField M ℚ)) :=
  haveI : IsCyclotomicExtension {M} ℚ (CyclotomicField M ℚ) :=
    CyclotomicField.isCyclotomicExtension M ℚ
  rootData_of_cyclotomic _ (CyclotomicField M ℚ) (M := M)
    (fun _ h => Nat.prime_of_mem_primeFactors h)
    (fun _ hl _ h => Or.inl (Nat.mem_primeFactors.2 ⟨hl, h, NeZero.ne M⟩)) (by simp)


end KStar.Choice
