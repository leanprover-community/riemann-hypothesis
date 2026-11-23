module

public import Mathlib.RingTheory.OrderOfVanishing.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

noncomputable section

universe u

def FiniteAlgebraLengthSum.Statement : Prop :=
  ∀ (A B : Type u) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    (ι : Type u) [Fintype ι] (𝔪 : ι → Ideal B) (h𝔪 : ∀ i, (𝔪 i).IsMaximal),
    Function.Injective 𝔪 → (∀ M : Ideal B, M.IsMaximal → ∃ i, M = 𝔪 i) →
    ∀ (C : ι → Type u) [∀ i, CommRing (C i)] [∀ i, Algebra B (C i)],
      (∀ i, haveI := (h𝔪 i).isPrime
        IsLocalization.AtPrime (C i) (𝔪 i)) →
      ∀ α : A,
        Module.length A (B ⧸ LinearMap.range (LinearMap.lsmul A B α)) =
          ∑ i, Ring.ord (C i) (algebraMap B (C i) (algebraMap A B α)) *
            Module.length A (B ⧸ 𝔪 i)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
