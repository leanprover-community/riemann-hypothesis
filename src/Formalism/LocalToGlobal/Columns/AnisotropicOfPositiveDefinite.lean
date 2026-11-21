import Formalism.LocalToGlobal.Columns.WmpNatCardQuotEqPowFinrank
import Formalism.LocalToGlobal.Columns.NonDeg
import Formalism.LocalToGlobal.Columns.PathCountSymmetricHolds

noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module

section Adj

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def conjugateSplitOff {S0 : Set (HeightOneSpectrum (𝓞 E))} (P : SplitOff S0) : SplitOff S0 :=
  ⟨conjPrime₂ P.1, by
    obtain ⟨h1, h2, h3⟩ := P.2
    refine ⟨?_, ?_, ?_⟩
    · rw [conjIdeal_asIdeal, conjugatePrime_conjugatePrime]
      intro e
      exact h1 (by rw [conjIdeal_asIdeal, e])
    · intro hm
      exact h3 _ hm (conjIdeal_asIdeal P.1).symm
    · intro Q hQ e
      rw [conjIdeal_asIdeal, conjugatePrime_conjugatePrime] at e
      have hQP : Q = P.1 := HeightOneSpectrum.ext e
      exact h2 (hQP ▸ hQ)⟩

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : GSD K}




end Adj

section Aniso

open ComplexOrder

variable {K : Type} [Field K] [NumberField K] [StarRing K]

end Aniso

section ThZero

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
  {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

end ThZero

section Final2

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

variable {X : Fields} {Pr : Primes X} {R : Formalism.BasicNotions.Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

end Final2

end Formalism.L2.Col
