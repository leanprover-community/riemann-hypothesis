module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartB
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.FormalGroupWitt.FormalGroupWittProofs.IntegralSubstVector
public import Formalism.GaussJetBounds.Statement
public import Formalism.GaussJetBounds.StatementI
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TheoremSFromKOneOf

@[expose] public section

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp jetPair mfact)
open Formalism.FG.IntegralSubstitution (integral_mul integralSubstV)
open TwoS

theorem norm_unif_pow {K : Type} [NormedField K] {p : ℕ} (hp : p.Prime)
    (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) {ϖ : K} (hϖ : ϖ ^ (p ^ 2 - 1) = (p : K)) :
    ‖ϖ ^ (p + 1)‖ = (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by linarith
  have h1 : (p : ℝ) - 1 ≠ 0 := by intro h; linarith
  have h2 : (p : ℝ) + 1 ≠ 0 := by intro h; linarith
  have h3 : (p : ℝ) ^ 2 - 1 ≠ 0 := by
    have : (p : ℝ) ^ 2 - 1 = ((p : ℝ) - 1) * ((p : ℝ) + 1) := by ring
    rw [this]
    exact mul_ne_zero h1 h2
  rw [norm_pow, norm_unif hp hn hϖ, ← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.2 hp0),
    Real.inv_rpow hp0, Real.rpow_neg hp0]
  congr 2
  push_cast
  field_simp
  ring

namespace MPl

section Alg

variable {K Pl : Type} [Field K] {ι : Pl → Type}

variable [Fintype Pl]

variable [DecidableEq Pl]

end Alg

end MPl

open MPl

end Formalism.InvariantFactorPaths.G7
