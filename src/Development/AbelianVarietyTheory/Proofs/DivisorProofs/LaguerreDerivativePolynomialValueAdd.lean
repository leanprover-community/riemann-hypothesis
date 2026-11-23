module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaguerreSignedBinomCoeffMulStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem lag_add : ∀ (k n : ℕ) (c s y : ℂ), lag k n (c + s) y =
    ∑ m ∈ Finset.range (n + 1), (rco k n m : ℂ) * s ^ (n - m) * lag k m c y := by
  intro k n c s y
  have hR : ∑ m ∈ Finset.range (n + 1), (rco k n m : ℂ) * s ^ (n - m) * lag k m c y
      = ∑ j ∈ Finset.range (n + 1), ∑ m ∈ Finset.Ico j (n + 1),
        (rco k n m : ℂ) * s ^ (n - m) * ((rco k m j : ℂ) * c ^ (m - j) * y ^ j) := by
    simp only [lag, Finset.mul_sum, Finset.range_eq_Ico]
    exact (Finset.sum_Ico_Ico_comm 0 (n + 1) (fun j m ↦
      (rco k n m : ℂ) * s ^ (n - m) * ((rco k m j : ℂ) * c ^ (m - j) * y ^ j))).symm
  rw [hR, lag]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [Finset.sum_Ico_eq_sum_range, add_pow, show n + 1 - j = n - j + 1 by omega,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hp' : p ≤ n - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
  have h := GlobalTheory.T.laguerreSignedBinomCoeff_mul k n (j + p) j (by omega) (by omega)
  have e1 : j + p - j = p := by omega
  have e2 : n - (j + p) = n - j - p := by omega
  rw [e1] at h
  have h' : (rco k n (j + p) : ℂ) * (rco k (j + p) j : ℂ)
      = (rco k n j : ℂ) * ((n - j).choose p : ℂ) := by exact_mod_cast h
  rw [e1, e2]
  linear_combination (-(s ^ (n - j - p) * c ^ p * y ^ j)) * h'

end GlobalTheory.HilbFam
