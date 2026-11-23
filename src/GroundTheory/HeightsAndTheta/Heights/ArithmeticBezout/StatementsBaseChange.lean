module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def RadicalBaseChange.Statement : Prop :=
  ∀ (K L : Type) [Field K] [PerfectField K] [Field L] (σ : K →+* L) (ι : Type)
    (I : Ideal (MvPolynomial ι K)), I.IsRadical → (I.map (MvPolynomial.map σ)).IsRadical

def ChowFormExtend.Statement : Prop :=
  ∀ (K L : Type) [Field K] [PerfectField K] [Field L] (σ : K →+* L) (n k : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin k × Fin n) K),
    IsChowForm I k f → IsChowForm (I.map (MvPolynomial.map σ)) k (MvPolynomial.map σ f)

def ChowFormReduced.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) F))
    (h : MvPolynomial (Fin k × Fin n) F),
    IsHomogIdeal J → J.IsRadical → IsChowForm J k h → IsChowFormCycle (fundCycle J) k h

end

end GroundTheory.Heights₂.Heights
