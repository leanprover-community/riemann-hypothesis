module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallMemFilt
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply

@[expose] public section

open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory.FormalOrigin.Extend

theorem filt_mul_filt_le (σ R : Type) [CommRing R] (I : Ideal R) (j k : ℕ) :
    filt (σ := σ) I j * filt I k ≤ filt I (j + k) := by
  classical
  refine Ideal.mul_le.2 fun F hF G hG => ?_
  rw [mem_filt] at hF hG ⊢
  intro α
  rw [MvPowerSeries.coeff_mul]
  refine Ideal.sum_mem _ fun p hp => ?_
  have hα : p.1 + p.2 = α := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hd : α.degree = p.1.degree + p.2.degree := by rw [← hα, map_add (f := _)]
  have h := Ideal.mul_mem_mul (hF p.1) (hG p.2)
  rw [← pow_add] at h
  exact Ideal.pow_le_pow_right (by omega) h

end GlobalTheory.FormalOrigin.Extend
