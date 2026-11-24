module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnrSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Sd

namespace UpperTheory.V.Z.Sym.Pl

def LemTWM : Prop :=
  ∀ (F L Ω : Type) [Field F] [NumberField F] [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra F L] [Algebra F Ω]
    [Algebra L Ω] [IsScalarTower F L Ω] [IsAlgClosure F Ω] [IsAlgClosure L Ω], IsTotallyReal F → Module.finrank F L = 2 →
    ∀ (l : ℕ) [Fact l.Prime] (M : ℕ), 3 ≤ M → ∀ Φ : Set (HeightOneSpectrum (𝓞 L)), Af.Tw.IsType F M Φ →
    ∀ ν : G F Ω →* (Qbar l)ˣ, Continuous ν → (∀ c, IsConjEl c → ν c = 1) →
      (∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v → ((M : ℕ) : 𝓞 F) ∉ v.asIdeal →
        ∀ s ∈ Ine (F := F) A, ν s = 1) →
      ∃ κ : G L Ω →* (Qbar l)ˣ, Continuous κ ∧ VerEq κ ν ∧ ∃ k : ℕ, 0 < k ∧
        ∀ (w : HeightOneSpectrum (𝓞 L)) (A : ValuationSubring Ω), IsPlaceOver A w → ∀ s ∈ Ine (F := L) A,
          (((M : ℕ) : 𝓞 L) ∉ w.asIdeal → κ s = 1) ∧ (w ∉ Φ → κ s ^ k = 1)

def LinkUnr : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ)
    (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] (Φ : Fr.Frame l (ResidueField O)),
    Pr.GalLink η Ψ σ g₁ B M L Φ → UnrSplit L M

def ChiUnr : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ)
    (ψ : DirichletCharacter c.O N) (χ' : G ℚ Ω →* (Qbar l)ˣ) (j : ℕ), ¬ l ∣ orderOf χ' →
    (∀ s, ‖((cycBar ℚ Ω l ^ j * χ') s).val - (Chr.Psi l e (Chr.dirG ℚ Ω ψ) s).val.1‖ < 1) →
    ∀ M : ℕ, l * N ∣ M → ∀ (L : Type) [Field L] [NumberField L] [Algebra L Ω] (A : ValuationSubring Ω), ¬ A.valuation (M : Ω) < 1 →
      ∀ s ∈ Ine (F := L) A, χ' (galEmb ℚ L Ω s) = 1

end UpperTheory.V.Z.Sym.Pl

end
