module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

section Graded

variable {σ τ R M : Type*} [CommRing R] [AddCommMonoid M]

theorem aeval_weightedHomogeneousComponent_of_weights (w : σ → M) (ω : τ → M)
    (e : σ → MvPolynomial τ R) (he : ∀ v, IsWeightedHomogeneous ω (e v) (w v)) (m : M)
    (p : MvPolynomial σ R) :
    aeval e (weightedHomogeneousComponent w m p) = weightedHomogeneousComponent ω m (aeval e p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    have hmon : IsWeightedHomogeneous ω (aeval e (monomial d c)) (Finsupp.weight w d) := by
      rw [aeval_monomial, Finsupp.weight_apply, algebraMap_eq]
      have := (isWeightedHomogeneous_C ω c).mul (IsWeightedHomogeneous.prod d.support
        (fun v => e v ^ d v) (fun v => d v • w v) (fun v _ => (he v).pow (d v)))
      rw [zero_add] at this
      exact this
    by_cases hdm : Finsupp.weight w d = m
    · have hmon' : IsWeightedHomogeneous ω (aeval e (monomial d c)) m := hdm ▸ hmon
      rw [(isWeightedHomogeneous_monomial _ d c hdm).weightedHomogeneousComponent_same,
        hmon'.weightedHomogeneousComponent_same]
    · rw [(isWeightedHomogeneous_monomial w d c
        (m := Finsupp.weight w d) rfl).weightedHomogeneousComponent_ne m
        (Ne.symm hdm), hmon.weightedHomogeneousComponent_ne m (Ne.symm hdm), map_zero]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]

end Graded

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
