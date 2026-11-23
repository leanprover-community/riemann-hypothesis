module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Characterised
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
public import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem ConeAverage.proof (h1 : ConeIntegralMass.Statement) (h2 : ChowDegreePos.Statement)
    (h3 : ConeFubini.Statement) (h4 : FsLogAverage.Statement) (h5 : FsLogMeasurable.Statement) :
    ConeAverage.Statement := by
  intro n e δ h W g hW hg hδ
  set S : Set (EuclideanSpace ℂ (Fin n)) :=
    {y | ‖y‖ < 1 ∧ ∀ q ∈ W, eval (h.pointOf y) q = 0} with hS
  set ν : Measure (EuclideanSpace ℂ (Fin n)) := Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) with hν
  set D : ℝ := (ν {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0}).toReal
    with hD
  have hδ1 : 1 ≤ δ := h2 n (e + 1) δ W g (Nat.succ_pos e) hW hg hδ
  have hmass : (ν S).toReal / D = δ := by
    have hm := h1 n e δ h W g hW hg hδ
    unfold coneIntegral at hm
    rw [setIntegral_const, measureReal_def, smul_eq_mul, mul_one] at hm
    exact hm
  have hfin : ν S ≠ ⊤ := by
    intro hinf
    rw [hinf, ENNReal.toReal_top, zero_div] at hmass
    have : (δ : ℝ) ≠ 0 := by exact_mod_cast (omega : δ ≠ 0)
    exact this hmass.symm
  have : IsFiniteMeasure (ν.restrict S) := isFiniteMeasure_restrict.2 hfin
  have hcone : ∀ φ : (Fin n → ℂ) → ℝ,
      coneIntegral h W e φ = (∫ y, φ (h.pointOf y) ∂(ν.restrict S)) / D := fun _ => rfl
  have hzero : ν.restrict S {(0 : EuclideanSpace ℂ (Fin n))} = 0 := by
    refine nonpos_iff_eq_zero.mp ((Measure.restrict_apply_le S _).trans_eq ?_)
    have hd : (((2 * (e + 1) : ℕ) : ℝ)) = (((2 * (e + 1) : ℕ) : NNReal) : ℝ) := by simp
    rw [hν, hd]
    apply hausdorffMeasure_of_dimH_lt
    rw [dimH_singleton]
    exact_mod_cast (omega : 0 < 2 * (e + 1))
  have hae : ∀ᵐ y ∂(ν.restrict S), y ≠ 0 := by
    rw [ae_iff]
    simpa using hzero
  have hF := h3 n h (ν.restrict S) (fun v y => fsLog h (nrmv h v) (h.pointOf y))
    (-(harmonic (n - 1) : ℝ) / 2)
    ((harmonic (n - 1) : ℝ) / 2 * (volume (ballH h)).toReal) (h5 n h)
    (hae.mono fun y hy => by
      obtain ⟨hi, habs, hmean⟩ := h4 n h y hy
      exact ⟨hi, habs.le, hmean⟩)
  obtain ⟨hFi, hFm⟩ := hF
  have hfun : (fun v => coneIntegral h W e (fsLog h (nrmv h v))) =
      fun v => (∫ y, fsLog h (nrmv h v) (h.pointOf y) ∂(ν.restrict S)) / D := by
    funext v
    exact hcone _
  rw [hfun]
  refine ⟨hFi.div_const D, ?_⟩
  rw [setAverage_eq, integral_div, ← smul_div_assoc, ← setAverage_eq, hFm,
    Measure.restrict_apply_univ, mul_div_assoc, hmass]
  ring

end

end GroundTheory.Heights₂.Heights
