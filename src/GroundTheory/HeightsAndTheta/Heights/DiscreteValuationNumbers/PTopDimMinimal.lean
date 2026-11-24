module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem TopDimMinimal.proof (h1 : DimStrictDrop.Statement.{u}) : TopDimMinimal.Statement.{u} := by
  intro A _ J Q _ N hJQ hJ hQ
  by_contra hmin
  obtain ⟨W, hW, hWQ⟩ := Ideal.exists_minimalPrimes_le hJQ
  have hWne : W ≠ Q := fun h => hmin (h ▸ hW)
  have hWlt : W < Q := lt_of_le_of_ne hWQ hWne
  have : W.IsPrime := hW.1.1
  have hJW : J ≤ W := hW.1.2
  have h2 : ringKrullDim (A ⧸ Q) + 1 ≤ ringKrullDim (A ⧸ W) := h1 A W Q hWlt
  have h3 : ringKrullDim (A ⧸ W) ≤ ringKrullDim (A ⧸ J) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hJW) (Ideal.Quotient.factor_surjective hJW)
  have h4 : ((N : ℕ) : WithBot ℕ∞) + 1 ≤ ringKrullDim (A ⧸ Q) + 1 :=
    add_le_add (not_lt.mp hQ) le_rfl
  have h5 : ((N + 1 : ℕ) : WithBot ℕ∞) = ((N : ℕ) : WithBot ℕ∞) + 1 := Nat.cast_succ N
  exact lt_irrefl _ (lt_of_le_of_lt (h5 ▸ h4.trans (h2.trans h3)) hJ)

end GroundTheory.Heights₂.Heights.NumbersDVR
