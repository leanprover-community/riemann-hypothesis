module

public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloContDiffStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ExistsClmOfI

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.C

open Metric Set Filter Topology Complex
open scoped ContDiff

theorem holoContDiff : HoloContDiffStatement := by
  intro n Ω f hΩ hf
  rw [contDiffOn_infty]
  intro k
  induction k generalizing f with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero]
    exact hf.continuousOn
  | succ k ih =>
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
    refine ⟨hf, fun h => absurd h (by simp), ?_⟩
    rw [contDiffOn_clm_apply]
    intro v
    exact ih _ (holoDeriv n Ω f hΩ hf v)

theorem holo_contDiffOn_complex {n : ℕ} {Ω : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hΩ : IsOpen Ω) (hf : DifferentiableOn ℂ f Ω) :
    ContDiffOn ℂ ∞ f Ω := holoContDiff _ Ω f hΩ hf

theorem holo_contDiffAt_complex {n : ℕ} {Ω : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hΩ : IsOpen Ω) (hf : DifferentiableOn ℂ f Ω)
    {x : EuclideanSpace ℂ (Fin n)} (hx : x ∈ Ω) (k : ℕ) : ContDiffAt ℂ k f x := (contDiffOn_infty.1 (holoContDiff _ Ω f hΩ hf) k).contDiffAt (hΩ.mem_nhds hx)

end ReciprocityTheory.L2DbarEstimates.C
