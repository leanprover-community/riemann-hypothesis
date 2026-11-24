module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.DI

def IsLifted (p : ℕ) {X : Scheme.{0}} [IsIntegral X] (Z : Set X) {ι : Type} (U : ι → X.Opens) {n : ℕ}
    (x : ι → Fin n → X.functionFieldˣ) : Prop :=
  ∃ (Kt : Type) (_ : CommRing Kt) (π : Kt →+* X.functionField) (F : ι → Kt →+* Kt),
    IsFlatLift p π ∧ (∀ i, IsFrob p π (F i)) ∧
    (∀ i l, ∃ z, π z = (x i l : X.functionField) ∧ F i z = z ^ p) ∧
    ∀ (y : X) (s : Finset ι), (∀ i ∈ s, y ∈ U i) → ∀ g : X.functionFieldˣ, LogDR.LogUnit Z y g →
      LogLift p π F s (LogDR.locRing y : Set X.functionField) (g : X.functionField)

def stalkIm {Y : Scheme.{0}} {η y : Y} (h : η ⤳ y) : Subring (Y.presheaf.stalk η) :=
  (Y.presheaf.stalkSpecializes h).hom.range

end GlobalTheory.DI
