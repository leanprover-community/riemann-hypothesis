module

public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.StatementsZonalReduction
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.StatementsZonalPairing
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

theorem ZonalBilinearFormula.proof (hB : ZonalHeightReduction.Statement)
    (hC : ZonalKernelPairing.Statement) : ZonalBilinearFormula.Statement := by
  refine ⟨fun F H => (hB F H).2.trans (hC F H), ?_⟩
  have h := (hB Polynomial.X Polynomial.X).2.trans (hC Polynomial.X Polynomial.X)
  simp only [Polynomial.eval_X] at h
  rw [h]
  have hm : uniformMean (fun x : ℝ => x) = 0 := by
    simp [uniformMean, integral_id]
  have hg : ∀ c : ℝ, centredPrimitive Polynomial.X c = (c ^ 2 - 1) / 2 := by
    intro c
    simp only [centredPrimitive, Polynomial.eval_X]
    rw [hm]
    simp only [sub_zero, integral_id]
    ring
  have hq : ∀ c : ℝ, centredPrimitive Polynomial.X c * centredPrimitive Polynomial.X c / (1 - c ^ 2)
      = (1 - c ^ 2) / 4 := by
    intro c
    rw [hg]
    rcases eq_or_ne (1 - c ^ 2) 0 with h0 | h0
    · have : c ^ 2 - 1 = 0 := by linarith
      rw [h0, this]; simp
    · field_simp
      ring
  rw [hm]
  simp only [hq]
  simp [intervalIntegral.integral_div, integral_pow]
  norm_num

end

end GroundTheory.Heights₂.Heights.FlagBundles
