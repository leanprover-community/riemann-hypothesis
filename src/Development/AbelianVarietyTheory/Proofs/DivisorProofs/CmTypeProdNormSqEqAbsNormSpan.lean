module

import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsValuedHeckeCharRamified
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField MeasureTheory

namespace GlobalTheory.CMTypeNorm

theorem place_bijective {K : Type} [Field K] [NumberField K] {I : Type} {φ : I → K →+* ℂ} (h : GlobalTheory.CMVal.IsCMType φ) :
    Function.Bijective fun i => InfinitePlace.mk (φ i) := by
  apply GlobalTheory.CMVal.Model.IsCMType.bijective <;> assumption

theorem prod_norm_sq_eq_absNorm :
    ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ),
      GlobalTheory.CMVal.IsCMType φ → ∀ α : 𝓞 K,
        ∏ i, ‖φ i (α : K)‖ ^ 2 = ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℝ) := by
  intro K _ _ _ I _ φ h α
  have h1 : ∏ i, ‖φ i (α : K)‖ ^ 2 = ∏ w : InfinitePlace K, w (α : K) ^ w.mult := by
    refine Fintype.prod_bijective _ (place_bijective h) _ _ fun i => ?_
    rw [InfinitePlace.apply, IsTotallyComplex.mult_eq]
  rw [h1, InfinitePlace.prod_eq_abs_norm, Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int, Nat.cast_natAbs]
  push_cast
  rfl

end GlobalTheory.CMTypeNorm
