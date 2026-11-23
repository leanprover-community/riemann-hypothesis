module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.Ideal.Span
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.ZetaNonvanishing.LIFTV

def LagrangeIdealSg : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (R : Type) [CommRing R] [IsDomain R] (sg : ℕ) (S₁ S₂ : Finset ℤ)
    (c : ℤ → R), Disjoint S₁ S₂ →
    (∀ a ∈ S₁, ∀ b ∈ S₁ ∪ S₂, a ≠ b →
      Associated (c a - c b) ((ℓ : R) ^ (sg + padicValInt ℓ (a - b)))) →
    Polynomial.C ((ℓ : R) ^ (S₁.sup fun a =>
        (∑ b ∈ S₂, (sg + padicValInt ℓ (a - b))) + ∑ a' ∈ S₁.erase a, (sg + padicValInt ℓ (a - a')))) ∈
      Ideal.span ({∏ a ∈ S₁, (Polynomial.X - Polynomial.C (c a)),
        ∏ b ∈ S₂, (Polynomial.X - Polynomial.C (c b))} : Set (Polynomial R))

end Formalism.ZetaNonvanishing.LIFTV
