module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Mathlib.NumberTheory.NumberField.ClassNumber
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ClassMeanPeriods

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric
open scoped nonZeroDivisors

def period (D : D7) (c : (Ideal (𝓞 D.host.K))⁰) : ℝ :=
  ‖discr (lamOf D (c : Ideal (𝓞 D.host.K)) 1)‖ ^ ((1 : ℝ) / 6) *
    area (lamOf D (c : Ideal (𝓞 D.host.K)) 1) / Real.pi

def IsReps (D : D7) (r : ClassGroup (𝓞 D.host.K) → (Ideal (𝓞 D.host.K))⁰) : Prop :=
  ∀ C, ClassGroup.mk0 (r C) = C

def meanLogPeriod (D : D7) (r : ClassGroup (𝓞 D.host.K) → (Ideal (𝓞 D.host.K))⁰) : ℝ :=
  (∑ C : ClassGroup (𝓞 D.host.K), Real.log (period D (r C))) / (classNumber D.host.K : ℝ)

def classMeanValue (D : D7) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (2 * Real.pi / Real.sqrt (D.host.d : ℝ)) - logDerivativeAtOne D

def ClassMeanAt (D : D7) : Prop :=
  ∀ r : ClassGroup (𝓞 D.host.K) → (Ideal (𝓞 D.host.K))⁰, IsReps D r →
    meanLogPeriod D r = classMeanValue D

def ClassMean : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ),
    IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ClassMeanAt D

theorem exists_curveIdeal_delta (D : D7) :
    ∃ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc ∧ IsDiscriminantTwelfthRootOfIdealLattice D cc δ := by
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (discr (lamOf D ⊤ 1)) (n := 12) (by norm_num)
  exact ⟨⊤, δ, ⟨top_ne_bot, by simp⟩, hδ⟩

theorem classMean_iff : ClassMean ↔ ∀ D : D7, ClassMeanAt D := by
  refine ⟨fun h D => ?_, fun h D _ _ _ _ => h D⟩
  obtain ⟨cc, δ, h1, h2⟩ := exists_curveIdeal_delta D
  exact h D cc δ h1 h2

end GlobalTheory.IndefiniteRowSideFullHecke.ClassMeanPeriods
