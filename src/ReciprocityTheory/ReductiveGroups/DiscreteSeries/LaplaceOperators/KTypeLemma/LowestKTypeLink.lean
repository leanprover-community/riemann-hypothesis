module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.TensorActionApplyDual
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.LiftHighestWeightVector

@[expose] public section

noncomputable section

open Finset
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem lift_highestWeightVector {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) (hV : IsKStableSub ε E V)
    [FiniteDimensional ℂ V] (hE : IsGlRep E)
    (hU : ∀ a b, ε a = ε b → ∀ x y : M, ⟪E a b x, y⟫_ℂ = ⟪x, E b a y⟫_ℂ)
    (μ : Fin n → ℝ) (f : Fin n → M) (hf : ∀ c, f c ∈ genSub E V) (hμ : IsKHWVec ε (tensV E) μ f) :
    ∃ u, IsKHWVec ε (sA ε E V hV) μ u ∧ sT E V u = f := by
  apply ReciprocityTheory.ChartRestriction.DS.Lap.LemK.LowestWeightLiftLemmas.lift_highestWeightVector <;> assumption

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
