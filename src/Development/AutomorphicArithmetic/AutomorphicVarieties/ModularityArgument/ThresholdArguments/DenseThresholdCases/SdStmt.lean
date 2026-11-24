module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsSeed
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

@[expose] public section




section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published
open scoped Matrix
namespace UpperTheory.V.Sd
def Seed2Alt : Prop :=
  ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [IsCMField L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    [Algebra K Ω] [Algebra L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω) (N w : ℕ) (χ' η θ : G ℚ Ω →* (Qbar l)ˣ) (j : ℕ),
    FieldPairCharacterTripleConditions K L c N w χ' η θ j → ∀ (κ : G K Ω →* (Qbar l)ˣ) (ka : G L Ω →* (Qbar l)ˣ), IsTwist ι c κ →
    (∀ (s : G L Ω) (s' : G K Ω), galEmb ℚ L Ω s = galEmb ℚ K Ω s' → ka s = κ s') →
    ∀ B : ℕ, ∃ m ≥ B, m ≡ j [MOD l - 1] ∧ ∃ σ : G ℚ Ω →* GL (Fin 2) (Qbar l), Continuous σ ∧
      Matrix.GeneralLinearGroup.det.comp σ = η * θ ∧ ResSum σ ![cycBar ℚ Ω l ^ j * χ' * η, (cycBar ℚ Ω l ^ j * χ')⁻¹] ∧
      _root_.UpperTheory.V.Sd.IsSeedAlt ι c (fun i => (![cycBar ℚ Ω l ^ j * χ', (cycBar ℚ Ω l ^ j * χ')⁻¹] i).comp (galEmb ℚ L Ω))
        (fun i => (![χ', χ'⁻¹] i).comp (galEmb ℚ L Ω)) ![(m : ℤ), -(m : ℤ)] ka (σ.comp (galEmb ℚ L Ω))
end UpperTheory.V.Sd
end
end
