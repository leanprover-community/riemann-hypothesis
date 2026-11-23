module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
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
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

def PotOfFlag : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (m : Fin n → ℤ), (∀ i j, m i ≠ m j + 1) → ∀ v : HeightOneSpectrum (𝓞 F),
    ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → (∀ A : ValuationSubring Ω, IsPlaceOver A v →
      ∃ (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ) (a : ℕ), 0 < a ∧ IsFlagOn r (Dec (F := F) A) κ ∧
        ∀ i (s : ↥(Dec (F := F) A)), (s : G F Ω) ∈ Ine (F := F) A → κ i s ^ a = (cycBar F Ω l s ^ m i) ^ a) → Win.PotUnl r v

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
