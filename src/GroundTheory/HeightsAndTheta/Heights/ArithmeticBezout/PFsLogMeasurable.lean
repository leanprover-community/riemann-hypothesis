module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Matrix

theorem FsLogMeasurable.proof : FsLogMeasurable.Statement := by
  intro n h
  have hn : Continuous h.norm := by
    unfold HermNorm.norm
    fun_prop
  have hd : Continuous h.dualNorm := by
    unfold HermNorm.dualNorm
    fun_prop
  have hp : Continuous h.pointOf := by
    unfold HermNorm.pointOf
    fun_prop
  have hinv : Measurable fun v : Fin n → ℂ => ((h.norm v : ℝ) : ℂ)⁻¹ :=
    (Complex.continuous_ofReal.comp hn).measurable.inv
  have hv : Measurable fun p : (Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => nrmv h p.1 := by
    unfold nrmv
    refine Measurable.of_eval fun j => ?_
    exact (hinv.comp measurable_fst).mul ((measurable_pi_apply j).comp measurable_fst)
  have hy : Measurable fun p : (Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => h.pointOf p.2 :=
    hp.measurable.comp measurable_snd
  unfold fsLog
  refine Real.measurable_log.comp (Measurable.div ?_ (hd.measurable.comp hy))
  refine Measurable.norm ?_
  refine Finset.measurable_sum _ fun j _ => ?_
  exact ((measurable_pi_apply j).comp hv).mul ((measurable_pi_apply j).comp hy)

end GroundTheory.Heights₂.Heights
