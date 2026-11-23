module

public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.HoloSectionStatement
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
public import Mathlib.RingTheory.Polynomial.Vieta

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

theorem esymmZero : esymmZeroStatement := by
  intro s hs a ha
  have h := Multiset.prod_X_add_C_eq_sum_esymm s
  have hR : ∑ j ∈ Finset.range (s.card + 1), Polynomial.C (s.esymm j) * Polynomial.X ^ (s.card - j)
      = Polynomial.X ^ s.card := by
    rw [Finset.sum_eq_single 0]
    · simp [Multiset.esymm, Multiset.powersetCard_zero_left]
    · intro j _ hj
      rw [hs j (Nat.one_le_iff_ne_zero.mpr hj)]
      simp
    · intro h0
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h0
  rw [hR] at h
  have h2 := congrArg (Polynomial.eval (-a)) h
  rw [Polynomial.eval_multiset_prod, Polynomial.eval_pow, Polynomial.eval_X] at h2
  have h3 : (Multiset.map (Polynomial.eval (-a))
      (Multiset.map (fun r => Polynomial.X + Polynomial.C r) s)).prod = 0 := by
    apply Multiset.prod_eq_zero
    rw [Multiset.map_map]
    exact Multiset.mem_map.mpr ⟨a, ha, by simp⟩
  rw [h3] at h2
  exact neg_eq_zero.mp (pow_eq_zero_iff'.mp h2.symm).1

end ReciprocityTheory.L2DbarEstimates.Norm
