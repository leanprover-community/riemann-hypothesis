module

public import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.WeightedOrderGePrimePowOfSumPurePowersAdd
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

@[expose] public section

open ReciprocityTheory.PGsh

theorem _root_.GlobalTheory.T.weightedOrderGe_prime_pow_of_sum_pure_powers_add : (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → ∀ (M N k : ℕ) (r w w₂ : ℝ) (a : Fin M → C) (ν : MvPowerSeries (Fin M) C), w ≤ w₂ → (∀ j, ((w - r * N : ℝ) : WithTop ℝ) ≤ v (a j)) →
    OrdGe v (fun _ => r) ν w₂ → OrdGe v (fun _ => r) ((∑ j, MvPowerSeries.C (R := C) (a j) * (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ N + ν) ^ (l ^ k) -
      ∑ j, MvPowerSeries.C (R := C) (a j ^ (l ^ k)) * (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ (N * l ^ k)) (min (1 + (l : ℝ) ^ k * w) ((l : ℝ) ^ k * w₂))) := by
  first | exact @GlobalTheory.WeightFrobenius.main | exact GlobalTheory.WeightFrobenius.main | (intros; apply GlobalTheory.WeightFrobenius.main <;> assumption)
