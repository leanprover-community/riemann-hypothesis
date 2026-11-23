module

public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric

noncomputable section

theorem PolyMaxOscillation.proof (h0 : ReciprocityTheory.AnForm.A.PolyMaxLogConvexStatement) :
    PolyMaxOscillation.Statement := by
  intro D U u z δ t C₁ hU hu hδ ht hC hCt
  have hC0 : 0 < C₁ := by linarith
  have hb0 : 0 < C₁ * t := mul_pos hC0 ht
  have hδ0 : 0 < δ := hb0.trans hCt
  have hconv := (h0 D U u z δ hU hu hδ0 hδ).1
  have ha0 : 0 < t / (4 * C₁) := by positivity
  have hab : t / (4 * C₁) < C₁ * t := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have key := hconv.slope_mono_adjacent
    (Set.mem_Iic.2 (Real.log_le_log ha0 (hab.trans hCt).le)) (Set.mem_Iic.2 le_rfl)
    (Real.log_lt_log ha0 hab) (Real.log_lt_log hb0 hCt)
  simp only [Real.exp_log ha0, Real.exp_log hb0, Real.exp_log hδ0] at key
  have h1 : Real.log (C₁ * t) - Real.log (t / (4 * C₁)) = Real.log (4 * C₁ ^ 2) := by
    rw [← Real.log_div hb0.ne' ha0.ne']
    congr 1
    field_simp
  have h2 : Real.log δ - Real.log (C₁ * t) = Real.log (δ / (C₁ * t)) :=
    (Real.log_div hδ0.ne' hb0.ne').symm
  have hL1 : 0 < Real.log (4 * C₁ ^ 2) := by
    rw [← h1]
    exact sub_pos.2 (Real.log_lt_log ha0 hab)
  rw [h1, h2, div_le_iff₀ hL1] at key
  rw [mul_div_assoc, mul_comm (Real.log (4 * C₁ ^ 2))]
  exact key

theorem PolyMaxOscillation.proof_closed : PolyMaxOscillation.Statement :=
  PolyMaxOscillation.proof ReciprocityTheory.AnForm.A.polyMaxLogConvex_thm

end

end GroundTheory.Heights₂.Heights.Regular
