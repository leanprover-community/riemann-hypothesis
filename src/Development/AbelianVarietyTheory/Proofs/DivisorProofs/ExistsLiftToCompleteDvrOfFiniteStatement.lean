module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftToCompleteDvrOfFinite
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

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_lift_to_complete_dvr_of_finite' : ∀ (A R : Type) [CommRing A] [CommRing R] [Algebra A R], Function.Injective (algebraMap A R) →
    Module.Finite A R → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (maximalIdeal V) V → ∀ h : A →+* V,
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V')
      (f : V →+* V') (ρ : R →+* V'), IsAdicComplete (maximalIdeal V') V' ∧
      Function.Injective f ∧ IsLocalHom f ∧ ρ.comp (algebraMap A R) = f.comp h := by
  first | exact @GlobalTheory.exists_lift_to_complete_dvr_of_finite | exact GlobalTheory.exists_lift_to_complete_dvr_of_finite | (intros; apply GlobalTheory.exists_lift_to_complete_dvr_of_finite <;> assumption)
