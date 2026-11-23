module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
public import Mathlib.Topology.Separation.CompletelyRegular
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory
open scoped ENNReal

noncomputable section

def VarietyLelongMono.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    ∀ z ∈ zeroSetEuc J, ∀ r s : ℝ, 0 < r → r ≤ s →
      ENNReal.ofReal (s ^ (2 * d)) * μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball z r) ≤
        ENNReal.ofReal (r ^ (2 * d)) * μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball z s)

theorem VarietyLelongMono.euclBall_measure (d : ℕ) (z : EuclideanSpace ℂ (Fin d)) {r : ℝ} (hr : 0 < r) :
    μH[((2 * d : ℕ) : ℝ)] (Metric.ball z r) =
      ENNReal.ofReal (r ^ (2 * d)) * μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) := by
  have hf : Module.finrank ℝ (EuclideanSpace ℂ (Fin d)) = 2 * d := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin d)), Complex.finrank_real_complex,
      finrank_euclideanSpace_fin]
  have h : ((2 * d : ℕ) : ℝ) = ((Module.finrank ℝ (EuclideanSpace ℂ (Fin d)) : ℕ) : ℝ) := by rw [hf]
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have hb : ∀ (x : EuclideanSpace ℂ (Fin 0)) (t : ℝ), 0 < t → Metric.ball x t = Set.univ := fun x t ht =>
      Set.eq_univ_of_forall fun y => Metric.mem_ball.2 (by rw [Subsingleton.elim y x, dist_self]; exact ht)
    rw [hb z r hr, hb 0 1 one_pos]
    simp
  · have : Nontrivial (EuclideanSpace ℂ (Fin d)) :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hf]; omega)
    rw [h, Measure.addHaar_ball _ _ hr.le, hf]

end

end GroundTheory.Heights₂.Heights
