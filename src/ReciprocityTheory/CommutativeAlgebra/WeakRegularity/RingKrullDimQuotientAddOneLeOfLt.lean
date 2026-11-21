import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.RingKrullDimQuotientOfMemAssociatedPrimes

section
namespace ReciprocityTheory.CA.Link

open IsLocalRing

universe u

def IsGorZero (A : Type*) [CommRing A] [IsLocalRing A] : Prop :=
  IsArtinianRing A ∧
    ∃ s : A, s ≠ 0 ∧ (⊥ : Ideal A).colon (maximalIdeal A : Set A) = Ideal.span {s}

def IsGor (R : Type*) [CommRing R] [IsLocalRing R] : Prop :=
  IsNoetherianRing R ∧ ∃ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) ∧
    RingTheory.Sequence.IsRegular R rs ∧
    ∃ _ : IsLocalRing (R ⧸ Ideal.ofList rs), IsGorZero (R ⧸ Ideal.ofList rs)

def FullCM {R : Type*} [CommRing R] (I : Ideal R) : Prop :=
  ∃ _ : IsLocalRing (R ⧸ I), IsCM (R ⧸ I) ∧ ringKrullDim (R ⧸ I) = ringKrullDim R

def ann {R : Type*} [CommRing R] (I : Ideal R) : Ideal R := (⊥ : Ideal R).colon (I : Set R)

def LinkageStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R], IsGor R → ∀ I : Ideal R, I ≠ ⊥ → FullCM I →
    FullCM (ann I) ∧ ann (ann I) = I ∧
    (∀ φ : I →ₗ[R] R, ∃ b : R, ∀ i : I, φ i = b * i) ∧
    ∀ p : Ideal R, p ∈ (ann I).minimalPrimes ↔
      p ∈ minimalPrimes R ∧
        ∃ _ : p.IsPrime, I.map (algebraMap R (Localization.AtPrime p)) ≠ ⊥

def GorIndepStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R], IsGor R → ∀ rs : List R,
    (∀ r ∈ rs, r ∈ maximalIdeal R) → RingTheory.Sequence.IsRegular R rs →
    IsArtinianRing (R ⧸ Ideal.ofList rs) →
    ∃ _ : IsLocalRing (R ⧸ Ideal.ofList rs), IsGorZero (R ⧸ Ideal.ofList rs)

def CIGorStatement : Prop :=
  ∀ (P : Type u) [CommRing P] [IsRegularLocalRing P], ∀ fs : List P,
    (∀ f ∈ fs, f ∈ maximalIdeal P) → RingTheory.Sequence.IsRegular P fs →
    ∃ _ : IsLocalRing (P ⧸ Ideal.ofList fs), IsGor (P ⧸ Ideal.ofList fs)

def GorCMStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R], IsGor R → IsCM R

end ReciprocityTheory.CA.Link
end

section
namespace ReciprocityTheory.CA.Link

open IsLocalRing

variable {R : Type*} [CommRing R]

theorem ringKrullDim_quotient_add_one_le_of_lt {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    (h : q < p) : ringKrullDim (R ⧸ p) + 1 ≤ ringKrullDim (R ⧸ q) := by
  obtain ⟨r, hrp, hrq⟩ := SetLike.exists_of_lt h
  have hr : Ideal.Quotient.mk q r ∈ nonZeroDivisors (R ⧸ q) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem])
  exact ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor h.le)
    (Ideal.Quotient.factor_surjective h.le) hr
    (by rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]; exact hrp)

end ReciprocityTheory.CA.Link
end
