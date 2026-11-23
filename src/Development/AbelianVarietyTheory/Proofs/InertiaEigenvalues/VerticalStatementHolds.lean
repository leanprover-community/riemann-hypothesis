module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import GroundTheory.AutomorphicForms.FourierWhittaker.IsAddFundamentalDomainImageOfMapVecLattice
public import GroundTheory.AutomorphicForms.FourierWhittaker.PartialCoeffDiagonalBlockGLEqVecCoeff

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

namespace GlobalTheory

theorem continuous_mul_norm_rpow_neg_half :
    Continuous fun z : ℂ => z * ((‖z‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    rw [ContinuousAt, zero_mul, tendsto_zero_iff_norm_tendsto_zero]
    have hfun : (fun z : ℂ => ‖z * ((‖z‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖)
        = fun z => ‖z‖ ^ (1 / 2 : ℝ) := by
      funext z
      rcases eq_or_ne z 0 with rfl | hz
      · simp [Real.zero_rpow (show (1 / 2 : ℝ) ≠ 0 by norm_num)]
      · have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        have h2 : ‖z‖ ^ (1 / 2 : ℝ) = ‖z‖ ^ (1 : ℝ) * ‖z‖ ^ (-(1 / 2) : ℝ) := by
          rw [← Real.rpow_add hp]; norm_num
        rw [h2, Real.rpow_one]
    rw [hfun]
    have hc : Continuous fun z : ℂ => ‖z‖ ^ (1 / 2 : ℝ) :=
      continuous_norm.rpow_const (fun _ => Or.inr (by norm_num))
    simpa [Real.zero_rpow (show (1 / 2 : ℝ) ≠ 0 by norm_num)] using hc.tendsto 0
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    apply ContinuousAt.mul continuousAt_id
    apply Complex.continuous_ofReal.continuousAt.comp
    exact continuous_norm.continuousAt.rpow_const (Or.inl hn)

end GlobalTheory
