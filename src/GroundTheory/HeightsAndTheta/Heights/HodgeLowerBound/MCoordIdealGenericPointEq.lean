module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCurveComplexPoint
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree.ComponentDataEquivalence

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Boundary

theorem mcPts_torus {B : Ideal (MRing ι)} (hB : IsMultiHomogIdeal B) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts B)
    {c : K → ℂ} (hc : ∀ k, c k ≠ 0) : torusSmul c z ∈ mcPts B := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, mul_ne_zero (hc k) hi⟩
  obtain ⟨S, hS, rfl⟩ := hB
  induction hf using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨a, ha⟩ := hS s hs
    rw [eval_map]
    unfold torusSmul
    rw [IndefiniteRowSideFullHecke.HeightsSet.CurveComplexPoint.eval₂_smul_homog s a ha, ← eval_map, hz.2 s (Ideal.subset_span hs),
      mul_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), eval_add, hx, hy, add_zero]
  | smul r x _ hx => rw [smul_eq_mul, map_mul, eval_mul, hx, mul_zero]

end Boundary

section Ample

end Ample

end GroundTheory.Heights₂.Heights.LowerBoundFree.ComponentDataEquivalence
