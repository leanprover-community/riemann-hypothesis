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

open MvPolynomial MeasureTheory NumberField

noncomputable section

def ConeIntegralMass.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
      coneIntegral h W e (fun _ => 1) = δ

def ChowFormBaseChange.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n k : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin k × Fin n) K) (σ : K →+* ℂ),
    IsProjPrime I → IsChowForm I k f →
      (∀ W ∈ (fundCycle (I.map (MvPolynomial.map σ))).support, IsProjPrime W) ∧
        IsChowFormCycle (fundCycle (I.map (MvPolynomial.map σ))) k (MvPolynomial.map σ f)

end

end GroundTheory.Heights₂.Heights
