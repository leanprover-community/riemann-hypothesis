module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bcoef
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_raabe :
    ∀ (N m k a : ℕ), 0 < N → 0 < m → bcoef N k a = ∑ j ∈ range m, bcoef (N * m) k (a + j * N) := by
  intro N m k a hN hm
  let F : ℕ → ℕ → PowerSeries ℚ := fun M c => PowerSeries.mk fun i => bcoef M i c / (i.factorial : ℚ)
  let y : PowerSeries ℚ := PowerSeries.rescale (N : ℚ) (PowerSeries.exp ℚ)
  let E : PowerSeries ℚ := PowerSeries.rescale ((N * m : ℕ) : ℚ) (PowerSeries.exp ℚ) - 1
  have hpow : ∀ j : ℕ, y ^ j = PowerSeries.rescale ((j : ℚ) * N) (PowerSeries.exp ℚ) := by
    intro j
    simp only [y]
    rw [← map_pow, PowerSeries.exp_pow_eq_rescale_exp, PowerSeries.rescale_rescale]
  have hE : E = (∑ j ∈ range m, y ^ j) * (y - 1) := by
    rw [geom_sum_mul, hpow]
    simp only [E]
    push_cast
    rw [mul_comm (m : ℚ)]
  have hE0 : E ≠ 0 := by
    intro h
    have h1 := congrArg (PowerSeries.coeff 1) h
    simp [E, PowerSeries.coeff_rescale, PowerSeries.coeff_exp] at h1
    rcases h1 with h1 | h1
    · exact hN.ne' h1
    · exact hm.ne' h1
  suffices h : F N a = ∑ j ∈ range m, F (N * m) (a + j * N) by
    have h2 := congrArg (PowerSeries.coeff k) h

    rw [map_sum] at h2
    simp only [F, PowerSeries.coeff_mk] at h2
    rw [← Finset.sum_div, div_left_inj' (by positivity)] at h2
    exact h2
  apply mul_right_cancel₀ hE0
  calc F N a * E = F N a * (y - 1) * ∑ j ∈ range m, y ^ j := by rw [hE]; ring
    _ = PowerSeries.X * PowerSeries.rescale (a : ℚ) (PowerSeries.exp ℚ) * ∑ j ∈ range m, y ^ j := by
        rw [b_egf N a hN]
    _ = ∑ j ∈ range m, PowerSeries.X * PowerSeries.rescale ((a + j * N : ℕ) : ℚ) (PowerSeries.exp ℚ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hpow, mul_assoc, PowerSeries.exp_mul_exp_eq_exp_add]
        push_cast
        rfl
    _ = ∑ j ∈ range m, F (N * m) (a + j * N) * E := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [b_egf (N * m) (a + j * N) (Nat.mul_pos hN hm)]
    _ = (∑ j ∈ range m, F (N * m) (a + j * N)) * E := by rw [Finset.sum_mul]
