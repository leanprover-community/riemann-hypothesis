module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsIsoGrCechMapPolyToGamma
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic

namespace GlobalTheory.NefNumericsModel

section General
variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]

end General

section Space
open ProjSpace
variable (k : Type) [Field k]

theorem selfIntersection_O1 (N : ℕ) : topSelfIntersection k (O1 k N) N = 1 := by
  have hc : ∀ j : ℕ, chi k (twistZ (structureModule (PSpace k N)) (O1 k N) (-(j : ℤ))) =
      Ring.choose (-(j : ℤ) + N) N := fun j => ProjCoh.chi_sheafO k N _
  rw [topSelf_def, interNum_const_eq_sum k _ (O1_isLB k N) N, Finset.sum_eq_single 0]
  · rw [hc]
    simp [Ring.choose_natCast]
  · intro j hj hj0
    have hjN : j ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hn : -(j : ℤ) + N = ((N - j : ℕ) : ℤ) := by
      rw [Nat.cast_sub hjN]; ring
    rw [hc, hn, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (show N - j < N by omega)]
    simp
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.succ_pos N)) h

end Space

end GlobalTheory.NefNumericsModel
