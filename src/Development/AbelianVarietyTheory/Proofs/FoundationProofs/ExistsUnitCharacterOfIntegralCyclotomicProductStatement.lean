module

public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitCharacterOfIntegralCyclotomicProduct
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_unitCharacter_of_integral_cyclotomic_product : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (A : ValuationSubring Ω) (k k' : G ℚ Ω → Qbar l), ContinuousOn k (Dec (F := ℚ) A) → (∀ s ∈ Dec (F := ℚ) A, k s ∈ c.O ∧ k' s ∈ c.O ∧ k s * k' s = eps l s) → (∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, k (s * t) = k s * k t) → ∃ θ : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ g : c.Oˣ) : c.O)) ∧ ∀ g, (((θ g : c.Oˣ) : c.O) : Qbar l) = k g := by
  first | exact @GlobalTheory.LocChar.unit_of_integral | exact GlobalTheory.LocChar.unit_of_integral | (intros; apply GlobalTheory.LocChar.unit_of_integral <;> assumption)
