import Mathlib

section
namespace Formalism.MainNotions.N.Lit.RayLarger

open NumberField IsDedekindDomain

abbrev Qb : Type := AlgebraicClosure ℚ

abbrev Fld : Type := IntermediateField ℚ Qb

def primesOver (L : Fld) (p : ℕ) : Set (HeightOneSpectrum (𝓞 L)) :=
  {v | ((p : ℕ) : 𝓞 L) ∈ v.asIdeal}

def SplitsCompletely (L : Fld) (p : ℕ) : Prop :=
  (primesOver L p).ncard = Module.finrank ℚ L

def IsRayPrime (K : Fld) (m p : ℕ) : Prop :=
  p.Prime ∧ ∃ π : Qb, π ∈ K ∧ IsIntegral ℤ π ∧ IsIntegral ℤ ((π - 1) / (m : Qb)) ∧
    ∃ σ : Qb →ₐ[ℚ] Qb, π * σ π = (p : Qb)

def Admissible (K : Fld) (m : ℕ) (L : Fld) : Prop :=
  K ≤ L ∧ FiniteDimensional ℚ L ∧ ∀ p, IsRayPrime K m p → SplitsCompletely L p

def Stmt : Prop :=
  ∀ (K : Fld) (d m : ℕ), Module.finrank ℚ K = 2 → 0 < d → 0 < m → 4 * d ∣ m →
    (∃ z ∈ K, z ^ 2 = -(d : Qb)) →
    ∃ (p : ℕ) (L : Fld), p.Prime ∧ ¬ p ∣ m ∧
      (∃ π : Qb, π ∈ K ∧ IsIntegral ℤ π ∧ ∃ σ : Qb →ₐ[ℚ] Qb, π * σ π = (p : Qb)) ∧
      Admissible K m L ∧ ¬ SplitsCompletely L p

example : 0 < (1 : ℕ) ∧ 0 < (4 : ℕ) ∧ 4 * 1 ∣ (4 : ℕ) := by decide

end Formalism.MainNotions.N.Lit.RayLarger
end

section
namespace Formalism.MainNotions.N.Lit.RayPrimeCount

open Formalism.MainNotions.N.Lit.RayLarger

noncomputable def count (K : Fld) (m : ℕ) (Y : ℝ) : ℕ :=
  Nat.card {p : ℕ // IsRayPrime K m p ∧ Y ≤ p ∧ (p : ℝ) ≤ 2 * Y}

def Stmt : Prop :=
  ∃ C'' C' : ℝ, ∀ (K : Fld) (d m : ℕ), Module.finrank ℚ K = 2 → 0 < d → 0 < m → 4 * d ∣ m →
    (∃ z ∈ K, z ^ 2 = -(d : Qb)) →
    ∀ X : ℝ, (m : ℝ) ^ (C'' + C') ≤ X →
      ∃ Y : ℝ, X * (m : ℝ) ^ (-C') ≤ Y ∧ Y ≤ X ∧ Y * (m : ℝ) ^ (-C'') / Real.log Y ≤ (count K m Y : ℝ)

end Formalism.MainNotions.N.Lit.RayPrimeCount
end

section
namespace Formalism.MainNotions.N.Lit.RayPrimeCountQ

open Formalism.MainNotions.N.Lit.RayLarger Formalism.MainNotions.N.Lit.RayPrimeCount

def Stmt : Prop :=
  ∀ ε' : ℝ, 0 < ε' → ε' < 1 / 4 →
    ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C →
      ∀ (K : Fld) (d m : ℕ), Module.finrank ℚ K = 2 → 0 < d → 0 < m → 4 * d ∣ m →
        (∃ z ∈ K, z ^ 2 = -(d : Qb)) →
        ∀ Y : ℝ, 1 ≤ Y → C * Real.log (m : ℝ) ^ 2 ≤ Real.log Y →
          Y ^ (1 - ε') ≤ (count K m Y : ℝ)

example : 0 < (1 : ℕ) ∧ 0 < (4 : ℕ) ∧ 4 * 1 ∣ (4 : ℕ) := by decide

end Formalism.MainNotions.N.Lit.RayPrimeCountQ
end

section
namespace Formalism.MainNotions.N.Lit.RayClassPrimeCountSquarefree

open Formalism.MainNotions.N.Lit.RayLarger Formalism.MainNotions.N.Lit.RayPrimeCount

def Stmt : Prop :=
  ∀ ε' : ℝ, 0 < ε' → ε' < 1 / 4 →
    ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C →
      ∀ (K : Fld) (d m : ℕ), Module.finrank ℚ K = 2 → 0 < d → d.Prime → d % 4 = 3 → 0 < m → 4 * d ∣ m →
        (∃ z ∈ K, z ^ 2 = -(d : Qb)) →
        ∀ Y : ℝ, 1 ≤ Y → C * Real.log (m : ℝ) ^ 2 ≤ Real.log Y →
          Y ^ (1 - ε') ≤ (count K m Y : ℝ)

example : (3 : ℕ).Prime ∧ 3 % 4 = 3 ∧ 4 * 3 ∣ (12 : ℕ) := ⟨Nat.prime_three, rfl, dvd_refl _⟩

end Formalism.MainNotions.N.Lit.RayClassPrimeCountSquarefree
end
