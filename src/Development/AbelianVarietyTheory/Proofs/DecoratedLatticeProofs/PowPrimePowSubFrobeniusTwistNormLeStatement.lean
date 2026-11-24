module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PowPrimePowSubFrobeniusTwistNormLe
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PowerSeries GlobalTheory.Honda

theorem _root_.GlobalTheory.T.pow_prime_pow_sub_frobeniusTwist_norm_le : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ (s : Type) (A : MvPowerSeries s K), (∀ m, ‖MvPowerSeries.coeff m A‖ ≤ 1) → ∀ (i : ℕ) (h : l ^ i ≠ 0) (m : s →₀ ℕ), ‖MvPowerSeries.coeff m (A ^ (l ^ i) - MvPowerSeries.expand (l ^ i) h (MvPowerSeries.map (σ ^ i) A))‖ ≤ ‖(l : K)‖ := by
  first | exact @GlobalTheory.Honda.pow_frob_sub_le | exact GlobalTheory.Honda.pow_frob_sub_le | (intros; apply GlobalTheory.Honda.pow_frob_sub_le <;> assumption)
