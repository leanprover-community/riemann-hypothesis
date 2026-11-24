module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

open IsLocalRing GlobalTheory.FormalOrigin

namespace GlobalTheory.FormalOrigin.Extend

def filt {σ R : Type} [CommRing R] (I : Ideal R) (k : ℕ) : Ideal (MvPowerSeries σ R) where
  carrier := {F | ∀ α, MvPowerSeries.coeff α F ∈ I ^ (k - α.degree)}
  add_mem' {F G} hF hG α := by simpa using Ideal.add_mem _ (hF α) (hG α)
  zero_mem' α := by simp
  smul_mem' c F hF α := by
    classical
    rw [smul_eq_mul, MvPowerSeries.coeff_mul]
    refine Ideal.sum_mem _ fun p hp => Ideal.mul_mem_left _ _ ?_
    have h := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    have : p.2.degree ≤ α.degree := by rw [← h, map_add (f := _)]; omega
    exact Ideal.pow_le_pow_right (by omega) (hF p.2)

theorem mem_filt {σ R : Type} [CommRing R] (I : Ideal R) (k : ℕ) (F : MvPowerSeries σ R) :
    F ∈ filt I k ↔ ∀ α, MvPowerSeries.coeff α F ∈ I ^ (k - α.degree) := Iff.rfl

theorem eq_zero_of_forall_mem_filt {σ R : Type} [CommRing R] (I : Ideal R) [IsHausdorff I R]
    (F : MvPowerSeries σ R) (h : ∀ k, F ∈ filt I k) : F = 0 := by
  ext α
  rw [map_zero]
  refine IsHausdorff.haus (I := I) inferInstance _ fun m => ?_
  have := h (m + α.degree) α
  rw [Nat.add_sub_cancel] at this
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact this

end GlobalTheory.FormalOrigin.Extend
