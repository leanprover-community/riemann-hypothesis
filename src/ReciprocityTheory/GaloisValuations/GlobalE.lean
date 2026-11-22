module

public import ReciprocityTheory.GaloisValuations.Global
public import Formalism.ConjugateSelfDual.StatementRest

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Pointwise Polynomial

namespace ReciprocityTheory.Gal

open Formalism.ConjugateSelfDual ReciprocityTheory.Hyp

section split

variable {F L Ω : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω] [Algebra F L]
  [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] {A : ValuationSubring Ω}

theorem one_lt_normV (v : HeightOneSpectrum (𝓞 F)) : 1 < normV v := by
  have e : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  rw [e]
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

end split

section frob

variable {F L Ω : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω] [Algebra F L]
  [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] {A : ValuationSubring Ω}

end frob

section conj

variable {L Ω : Type*} [Field L] [NumberField L] [Field Ω] [Algebra L Ω]

variable (s : L ≃+* L) (τ : Ω ≃+* Ω) (hτ : ∀ x : L, τ (algebraMap L Ω x) = algebraMap L Ω (s x))

end conj

end ReciprocityTheory.Gal
