module

public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
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

namespace ReciprocityTheory.AnForm.P

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas

noncomputable section

def PullPshStatement : Prop :=
  ∀ {e e' : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X'] (A : FinHolAtlas e X)
    (A' : FinHolAtlas e' X') (h : X' → X) (hh : HoloMap A' A h) (P : LocPot X) (U : Set X)
    (f : X → ℝ), IsOpen U → IsPotential A P →
      (A.SmoothOn U f → A'.SmoothOn (h ⁻¹' U) (f ∘ h)) ∧
      (IsPsh A P → IsPsh A' (P.pullback h hh.1)) ∧
      (A.SmoothOn U f → IsPshOn A U (P + LocPot.ofFun f) →
        IsPshOn A' (h ⁻¹' U) (P.pullback h hh.1 + LocPot.ofFun (f ∘ h)))

end

end ReciprocityTheory.AnForm.P
