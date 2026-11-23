module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Development.WeilBound.ThetaLifts.CartanFactorisation.SpanOrbitStab
public import Mathlib.Analysis.InnerProductSpace.Defs

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKF

open scoped InnerProductSpace
open Abs

section

variable {Q : Type} [AddCommGroup Q] [Module ℂ Q] (β : Q →ₗ⋆[ℂ] Q →ₗ[ℂ] ℂ)

theorem rad_of_zero (hs : ∀ x y, β x y = starRingEnd ℂ (β y x)) (hp : ∀ x, 0 ≤ (β x x).re) {x : Q} (h : β x x = 0) :
    β x = 0 := by
  let c : PreInnerProductSpace.Core ℂ Q :=
    { inner := fun x y => β x y
      conj_inner_symm := fun x y => (hs x y).symm
      re_inner_nonneg := hp
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp }
  ext y
  have := InnerProductSpace.Core.inner_mul_inner_self_le (c := c) x y
  change ‖β x y‖ * ‖β y x‖ ≤ RCLike.re (β x x) * RCLike.re (β y y) at this
  rw [h, map_zero, zero_mul, hs y x, RCLike.norm_conj] at this
  have h2 : ‖β x y‖ = 0 := by nlinarith [norm_nonneg (β x y)]
  simpa using h2

end

end PositivityTheory.ThKF

end
