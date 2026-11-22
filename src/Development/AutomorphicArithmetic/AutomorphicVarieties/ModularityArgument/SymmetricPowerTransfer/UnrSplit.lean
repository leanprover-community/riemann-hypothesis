module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.DescUse

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
open UpperTheory.V.W (Plc Lp)

namespace UpperTheory.V.Z.Sym

structure UnrSplit (L : Type) [Field L] [NumberField L] [IsCMField L] (M : ℕ) : Prop where
  unr : ∀ w : Plc L, Algebra.IsUnramifiedAt (𝓞 (Lp L)) w.asIdeal
  split : ∀ w : Plc L, (M : 𝓞 L) ∈ w.asIdeal → IsSplitAt w

def TwEx : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra L Ω] (l : ℕ) [Fact l.Prime],
    l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω), Sd.IsCC c → ∀ M : ℕ, M ≠ 0 → l ∣ M → UnrSplit L M →
    ∀ (χ : G ℚ Ω →* (Qbar l)ˣ) (a : ℤ), IsOpen (χ.ker : Set (G ℚ Ω)) → χ c = (-1) ^ a →
    (∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → ∀ s ∈ Ine (F := L) A, χ (galEmb ℚ L Ω s) = 1) →
    ∃ κ : G L Ω →* (Qbar l)ˣ, Sd.IsAlgChar ι κ ∧
      (∀ s s' : G L Ω, galEmb ℚ L Ω s' = c * galEmb ℚ L Ω s * c⁻¹ → κ s * κ s' = cycBar L Ω l s ^ a * χ (galEmb ℚ L Ω s)) ∧
      (∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → ∀ s ∈ Ine (F := L) A, κ s = 1) ∧
      ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ (b : ℤ) (k : ℕ), 0 < k ∧
        ∀ s ∈ Ine (F := L) A, κ s ^ k = (cycBar L Ω l s ^ b) ^ k

end UpperTheory.V.Z.Sym

end
