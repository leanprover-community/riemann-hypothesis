module

public import Formalism.HermitianCurvature.StatementNF
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
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
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumPairAtStarMul

@[expose] public section

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate InnerProductSpace ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Bump

theorem dZ_contDiff {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (NF.dZ f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.1 hf).2
  have h1 : ContDiff ℝ ∞ (fun w => fderiv ℝ f w 1) := hd.clm_apply contDiff_const
  have hI : ContDiff ℝ ∞ (fun w => fderiv ℝ f w Complex.I) := hd.clm_apply contDiff_const
  show ContDiff ℝ ∞ (fun w => (1 / 2 : ℂ) * (fderiv ℝ f w 1 - Complex.I * fderiv ℝ f w Complex.I))
  exact contDiff_const.mul (h1.sub (contDiff_const.mul hI))

theorem dZb_contDiff {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (NF.dZb f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.1 hf).2
  have h1 : ContDiff ℝ ∞ (fun w => fderiv ℝ f w 1) := hd.clm_apply contDiff_const
  have hI : ContDiff ℝ ∞ (fun w => fderiv ℝ f w Complex.I) := hd.clm_apply contDiff_const
  show ContDiff ℝ ∞ (fun w => (1 / 2 : ℂ) * (fderiv ℝ f w 1 + Complex.I * fderiv ℝ f w Complex.I))
  exact contDiff_const.mul (h1.add (contDiff_const.mul hI))

end Bump

end Formalism.FourierDecayAlt.P5.HerB
