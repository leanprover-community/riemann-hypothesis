module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
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

set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing div_mem_chartRing exists_pow_mul_mem_chartRing)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord restrictChart IsPull SameGeneric)

namespace JoinPullbackAlt

section Charts

variable {Ω : Type*} [Field Ω] {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}

def zChart (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : ∀ k, ι' k :=
  fun k => s (.inr k)

def combChart (t : ∀ k, ι k) (u : ∀ k, ι' k) : ∀ k : K ⊕ K', Sum.elim ι ι' k
  | .inl k => t k
  | .inr k => u k

theorem restrictChart_combChart (t : ∀ k, ι k) (u : ∀ k, ι' k) :
    restrictChart (combChart t u) = t :=
  rfl

theorem zChart_combChart (t : ∀ k, ι k) (u : ∀ k, ι' k) : zChart (combChart t u) = u :=
  rfl

theorem mseg_joinCoord (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (joinCoord x z) s = mseg x (restrictChart s) * mseg z (zChart s) := by
  simp only [mseg, Fintype.prod_sum_type]
  rfl

variable (O : Type*) [CommRing O] [Algebra O Ω]

theorem chartRing_le_join (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k)
    (hs : mseg (joinCoord x z) s ≠ 0) :
    chartRing O (mseg x) (restrictChart s) ≤ chartRing O (mseg (joinCoord x z)) s := by
  have hz : mseg z (zChart s) ≠ 0 := by
    rw [mseg_joinCoord] at hs
    exact right_ne_zero_of_mul hs
  unfold chartRing
  apply Algebra.adjoin_le
  rintro _ ⟨t', rfl⟩
  have h : mseg x t' / mseg x (restrictChart s) =
      mseg (joinCoord x z) (combChart t' (zChart s)) / mseg (joinCoord x z) s := by
    rw [mseg_joinCoord x z (combChart t' (zChart s)), mseg_joinCoord x z s, restrictChart_combChart,
      zChart_combChart, mul_div_mul_right _ _ hz]
  simp only
  rw [h]
  exact div_mem_chartRing (o := O) _ _ _

end Charts

section Pull

variable (O : Type*) [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]

end Pull

end JoinPullbackAlt


end GroundTheory.Heights₂.Heights.NumbersDVR
