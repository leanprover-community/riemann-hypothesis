module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain

namespace Neutral.HilbertClassField

variable {E : Type*} [Field E] [NumberField E] {Ω : Type*} [Field Ω] [Algebra E Ω]

def LiesAbove (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ x : 𝓞 E, algebraMap E Ω (x : E) ∈ A.nonunits ↔ x ∈ v.asIdeal

def IsArithFrobenius (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)) (φ : Ω ≃ₐ[E] Ω) : Prop :=
  φ ∈ A.decompositionSubgroup E ∧ ∀ x ∈ A, φ x - x ^ Nat.card (𝓞 E ⧸ v.asIdeal) ∈ A.nonunits

def IsComplexConjugation (c : Ω ≃ₐ[E] Ω) : Prop :=
  ∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)


variable (E Ω) in
def hilbertSubgroup : Subgroup (Ω ≃ₐ[E] Ω) :=
  (Subgroup.closure ((commutator (Ω ≃ₐ[E] Ω) : Set (Ω ≃ₐ[E] Ω)) ∪
    {σ | ∃ A : ValuationSubring Ω, σ ∈ (A.inertiaSubgroup E).map (A.decompositionSubgroup E).subtype} ∪
    {c | IsComplexConjugation c})).topologicalClosure

def Statement : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω],
    ∃ art : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E), Function.Surjective art ∧
      art.ker = hilbertSubgroup (E := E) (Ω := Ω) ∧
      ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω), LiesAbove A v → IsArithFrobenius A v φ →
        art φ = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩

end Neutral.HilbertClassField
