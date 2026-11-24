module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsSegreComponent
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsChartDimBound
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsChartFiniteIrrel
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

theorem SegreComponent.proof (h₁ : ChartDimBound.Statement.{u, v, w})
    (h₂ : ChartFiniteIrrel.Statement.{u, v, w}) : SegreComponent.Statement.{u, v, w} := by
  intro K _ ι _ F _ V n f hV hf
  by_contra hne
  have hirr : ∀ W ∈ (V ⊔ Ideal.span {f}).minimalPrimes, ¬ IsRelevant W :=
    fun W hW hrel => hne ⟨W, hW, hrel⟩
  obtain ⟨i, hi⟩ : ∃ i, IsChart V i :=
    ⟨fun k => (hV.1.2.2 k).choose, fun k => (hV.1.2.2 k).choose_spec⟩
  have := h₂ K ι F V f i hV.1.2.1 hf hirr
  have : IsArtinianRing (MRingOver F ι ⧸ chartIdeal V i) :=
    IsArtinianRing.of_finite F (MRingOver F ι ⧸ chartIdeal V i)
  have hA : ringKrullDim (MRingOver F ι ⧸ chartIdeal V i) ≤ ((0 : ℕ) : WithBot ℕ∞) :=
    Ring.krullDimLE_iff.mp inferInstance
  have hdim := h₁ K ι F V i hV.1 hi
  rw [hV.2] at hdim
  have h := hdim.trans (add_le_add hA le_rfl)
  rw [Nat.cast_zero, zero_add] at h
  have h' : n + 1 + Fintype.card K ≤ Fintype.card K := by exact_mod_cast h
  omega

end GroundTheory.Heights₂.Heights.Targets
