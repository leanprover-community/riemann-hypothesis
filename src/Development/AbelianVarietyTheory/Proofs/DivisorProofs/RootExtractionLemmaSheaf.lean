module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.RootStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnimodularMatrixForDepthStatement
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame

@[expose] public section

namespace GlobalTheory.RootTrick

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

theorem root_statement : RootStatement := by
  intro C _ _ _ v p hp hv d h m ty i G γ hγ hty n j _hn V _ _ La hdim
  obtain ⟨x, hxi, hxd, hxk⟩ := GlobalTheory.T.exists_integral_unimodular_matrix_for_depth C v V (p ^ n) (pow_pos hp.pos n) j m
    (fun u => La (G.lc p (γ u) n)) hdim
  refine ⟨x, hxi, hxd, ?_⟩
  have h6 := fun w => pt6' C v p hp hv d m G γ (x w) hγ (hxi w)
  dsimp only at h6 ⊢
  refine ⟨fun w => (h6 w).2.1, fun w => ⟨(h6 w).2.2.2 (fun u => (hty u).1), fun k a hk => ?_⟩,
    fun w hw => ?_⟩
  · rw [(h6 w).2.2.1 k]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, (hty _).2 k a hk, mul_zero,
      Finset.sum_const_zero]

  · rw [(h6 w).2.2.1 n, map_sum]
    simp only [map_smul]
    exact hxk w hw

end GlobalTheory.RootTrick
