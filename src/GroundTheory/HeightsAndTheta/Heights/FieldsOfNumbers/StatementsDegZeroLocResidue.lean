module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLoc
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

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DegZeroLocResidue.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [DecidableEq K] (ι : K → Type) (P : Ideal (MRing ι F))
    [P.IsPrime] (W : Ideal (MRing ι F)) [W.IsPrime], P ≤ W →
    ∃ ρ : degZeroLoc P {W} →+* FractionRing (MRing ι F ⧸ W),
      (∀ (x : degZeroLoc P {W}) (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b →
        IsMultiHomog g b → g ∉ W →
        (x : FractionRing (MRing ι F ⧸ P)) =
          algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P f) /
            algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) →
        ρ x = algebraMap (MRing ι F ⧸ W) _ (Ideal.Quotient.mk W f) /
            algebraMap (MRing ι F ⧸ W) _ (Ideal.Quotient.mk W g)) ∧
      (∀ x : degZeroLoc P {W},
        ρ x = 0 ↔ ¬ ∃ y ∈ degZeroLoc P {W}, (x : FractionRing (MRing ι F ⧸ P)) * y = 1) ∧
      ∀ z : FractionRing (MRing ι F ⧸ W), z ∈ homFracDegZero W ↔ ∃ x, ρ x = z

end

end GroundTheory.Heights₂.Heights.FieldNumbers
