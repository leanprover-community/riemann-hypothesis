module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankSB

@[expose] public section

open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

theorem eq_one_of_mem_slice_of_mul_mem_slice (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a d : ℕ) (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k) :
    Z ∈ slice (k := k) a d → g.val * Z ∈ slice (k := k) a d → g = 1 := by
  rintro ⟨J, hJ, hZ⟩ ⟨J', hJ', hgZ⟩
  have m1 : minor Z J = 1 := by rw [minor, hJ, det_one]
  have m1' : minor (g.val * Z) J' = 1 := by rw [minor, hJ', det_one]
  have e1 : valuation k (g.val.det) * valuation k (minor Z J') = 1 := by
    rw [← map_mul, ← minor_mul, m1', map_one]
  have hg : valuation k (g.val.det) ≤ 1 := by
    have := (hgZ J).1
    rwa [minor_mul, m1, mul_one] at this
  have hZJ' : valuation k (minor Z J') = 1 := by
    refine le_antisymm (hZ J').1 ?_
    calc (1 : ValueGroupWithZero k) = valuation k (g.val.det) * valuation k (minor Z J') := e1.symm
      _ ≤ 1 * valuation k (minor Z J') := mul_le_mul_of_nonneg_right hg zero_le
      _ = valuation k (minor Z J') := one_mul _
  have hg1 : valuation k (g.val.det) = 1 := by rwa [hZJ', mul_one] at e1
  have hJJ : J = J' := by
    rcases lt_trichotomy (idx J') (idx J) with h | h | h
    · exact absurd ((hZ J').2 h) (by rw [hZJ']; exact lt_irrefl _)
    · exact (idx.injective h).symm
    · have := (hgZ J).2 h
      rw [minor_mul, m1, mul_one, hg1] at this
      exact absurd this (lt_irrefl _)
  subst hJJ
  have hsub : (g.val * Z).submatrix id J = g.val * Z.submatrix id J := by
    ext i j; simp [Matrix.mul_apply, submatrix_apply]
  rw [hsub, hJ, Matrix.mul_one] at hJ'
  exact Units.ext hJ'

end GlobalTheory.RankFibreKer
