module

public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CompInv
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

def CompInvSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (s : R⟦X⟧), constantCoeff s = 0 → IsUnit (coeff 1 s) →
    constantCoeff (compInv s) = 0 ∧ s.subst (compInv s) = X ∧ (compInv s).subst s = X ∧
    coeff 1 (compInv s) * coeff 1 s = 1 ∧
    (∀ t : R⟦X⟧, constantCoeff t = 0 → s.subst t = X → t = compInv s) ∧
    (∀ t : R⟦X⟧, constantCoeff t = 0 → t.subst s = X → t = compInv s)

def CompInvMap : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (s : R⟦X⟧),
    constantCoeff s = 0 → IsUnit (coeff 1 s) →
    PowerSeries.map φ (compInv s) = compInv (PowerSeries.map φ s)

def IntegSpec : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (f : K⟦X⟧),
    constantCoeff (integ f) = 0 ∧ derivative (integ f) = f ∧
    ∀ g : K⟦X⟧, constantCoeff g = 0 → derivative g = f → g = integ f

end Formalism.L2.Th1.A
