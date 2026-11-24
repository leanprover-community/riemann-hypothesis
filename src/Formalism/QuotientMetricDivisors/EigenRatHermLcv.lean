module

public import Formalism.QuotientMetricDivisors.RatHermLcvTwist
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

def extSpan {K Ω : Type} [Field K] [Field Ω] {n : ℕ} (j : K →+* Ω) (Z : Submodule K (Fin n → K)) :
    Submodule Ω (Fin n → Ω) :=
  Submodule.span Ω ((fun z i => j (z i)) '' (Z : Set (Fin n → K)))

def IsAdjStable {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (𝒯 : Set (Matrix (Fin n) (Fin n) K)) : Prop :=
  ∀ T ∈ 𝒯, ∃ T' ∈ 𝒯, ∀ x y : Fin n → K, hform H (T.mulVec x) y = hform H x (T'.mulVec y)

def IsCommStable {K : Type} [Field K] {n : ℕ} (𝒯 : Set (Matrix (Fin n) (Fin n) K))
    (Z : Submodule K (Fin n → K)) : Prop :=
  ∀ B : Matrix (Fin n) (Fin n) K, (∀ T ∈ 𝒯, B * T = T * B) → ∀ z ∈ Z, B.mulVec z ∈ Z

def CommTwist : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K), IsCMSub K0 →
    ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ i j, H i j ∈ K0) →
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ 𝒯 : Set (Matrix (Fin n) (Fin n) K), (∀ T ∈ 𝒯, ∀ i j, T i j ∈ K0) →
    (∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T * T' = T' * T) → IsAdjStable H 𝒯 →
    ∀ Z : Submodule K (Fin n → K), IsCommStable 𝒯 Z →
    ∀ σ : K →+* ℂ, embSpan σ Z = embSpan (twist σ) Z

end Formalism.DivisionValues
