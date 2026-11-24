module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_egf :
    ∀ (N a : ℕ), 0 < N → (PowerSeries.mk fun k => bcoef N k a / (k.factorial : ℚ)) * (PowerSeries.rescale (N : ℚ) (PowerSeries.exp ℚ) - 1) = PowerSeries.X * PowerSeries.rescale (a : ℚ) (PowerSeries.exp ℚ) := by
  intro N a hN
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have h := congrArg (PowerSeries.rescale (N : ℚ)) (Polynomial.bernoulli_generating_function ((a : ℚ) / N))
  rw [map_mul, map_mul, map_sub, map_one, PowerSeries.rescale_mk, PowerSeries.rescale_X,
    PowerSeries.rescale_rescale] at h
  have hc : ((a : ℚ) / N) * N = a := by field_simp
  rw [hc] at h
  beta_reduce at h
  have hmk : (PowerSeries.mk fun k => bcoef N k a / (k.factorial : ℚ)) =
      PowerSeries.C (1 / (N : ℚ)) * PowerSeries.mk (fun n => (N : ℚ) ^ n *
        (Polynomial.aeval ((a : ℚ) / N)) ((1 / (n.factorial : ℚ)) • Polynomial.bernoulli n)) := by
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    simp only [bcoef, map_smul, Polynomial.coe_aeval_eq_eval, smul_eq_mul]
    rw [zpow_sub_one₀ hN', zpow_natCast]
    have hf : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
    field_simp
  rw [hmk, mul_assoc, h, ← mul_assoc, ← mul_assoc, ← map_mul, one_div_mul_cancel hN', map_one, one_mul]
