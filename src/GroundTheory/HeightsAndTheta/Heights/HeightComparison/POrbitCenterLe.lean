module

public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterLe
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FinitePlaceSumLe
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

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField MvPolynomial

theorem OrbitCenterLe.proof : OrbitCenterLe.Statement := by
  intro ι _ _ n x v F d hF
  classical
  have hle : ∀ k i, v (coordVec x k i) ≤ ⨆ j, v (coordVec x k j) := fun k i ↦
    le_ciSup (f := fun j ↦ v (coordVec x k j)) (Set.finite_range _).bddAbove i
  have hM0 : ∀ k, 0 ≤ ⨆ j, v (coordVec x k j) := fun k ↦ (apply_nonneg v _).trans (hle k 0)
  have hna : IsNonarchimedean (v : coordField x → ℝ) := fun a b ↦ v.add_le a b
  have hW : IsWeightedHomogeneous (coordDeg n) F d := (geoMultiHomog_iff F d).mp hF
  unfold evalCone
  rw [eval₂_eq']
  refine _root_.UpperTheory.Reformulated.B.FinitePlaceSumBound.finitePlace_sum_le v _ _
    (Finset.prod_nonneg fun k _ ↦ pow_nonneg (hM0 k) _) fun m hm ↦ ?_
  have hw : ∀ k, ∑ i, m ⟨k, i⟩ = d k := fun k ↦ by
    rw [← weight_coordDeg_apply, hW (mem_support_iff.mp hm)]
  have hc : v ((Int.castRingHom (coordField x)) (F.coeff m)) ≤ 1 := by
    simpa using hna.apply_intCast_le_one (map_zero_le v 1) (map_one v)
      (map_neg_eq_map v) (n := F.coeff m)
  rw [map_mul, map_prod]
  calc v ((Int.castRingHom (coordField x)) (F.coeff m)) * ∏ p, v (coordVec x p.1 p.2 ^ m p)
      ≤ 1 * ∏ p : Coord n, (⨆ j, v (coordVec x p.1 j)) ^ m p := by
        gcongr with p
        rw [map_pow]; exact pow_le_pow_left₀ (apply_nonneg v _) (hle _ _) _
    _ = ∏ k, (⨆ j, v (coordVec x k j)) ^ d k := by
        rw [one_mul, Fintype.prod_sigma]
        refine Finset.prod_congr rfl fun k _ ↦ ?_
        dsimp only
        rw [Finset.prod_pow_eq_pow_sum, hw k]

end GroundTheory.Heights₂.Heights
