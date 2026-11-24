module

public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Ideal Finset
open scoped Pointwise

noncomputable section

namespace Formalism.Q3

def IsMQ {k : ℕ} {E : Type*} [Field E] [Algebra ℚ E] (a : Fin k → ℤ) (α : Fin k → E) : Prop :=
  (∀ i, α i ^ 2 = (a i : E)) ∧ IntermediateField.adjoin ℚ (Set.range α) = ⊤


open Classical in
def galSign {k : ℕ} {E : Type*} [Field E] [Algebra ℚ E] (α : Fin k → E) (σ : Gal(E/ℚ)) :
    Fin k → ℤˣ :=
  by
    classical
    exact fun i => if σ (α i) = α i then 1 else -1

def MQGalois : Prop :=
  ∀ (k : ℕ) (E : Type) [Field E] [NumberField E] (a : Fin k → ℤ) (α : Fin k → E),
    IsMQ a α → (∀ i, a i ≠ 0) →
    IsGalois ℚ E ∧
    (∀ (σ : Gal(E/ℚ)) (i : Fin k), σ (α i) = (((galSign α σ i : ℤˣ) : ℤ) : E) * α i) ∧
    (∀ σ τ : Gal(E/ℚ), galSign α (σ * τ) = galSign α σ * galSign α τ) ∧
    Function.Injective (galSign α)

def MQKummer : Prop :=
  ∀ (k : ℕ) (E : Type) [Field E] [NumberField E] (a : Fin k → ℤ) (α : Fin k → E),
    IsMQ a α → (∀ S : Finset (Fin k), S.Nonempty → ¬ IsSquare (∏ i ∈ S, (a i : ℚ))) →
    Module.finrank ℚ E = 2 ^ k ∧ Function.Bijective (galSign α) ∧
    ∀ d : ℚ, IsSquare (algebraMap ℚ E d) ↔
      ∃ S : Finset (Fin k), IsSquare (d * ∏ i ∈ S, (a i : ℚ))


end Formalism.Q3
