module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

def BaseChangeAvoid.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (u : Fin n → K) (σ : K →+* ℂ), IsProjPrime I → linForm u ∉ I →
      ∀ W ∈ (fundCycle (I.map (MvPolynomial.map σ))).support, linForm (fun j => σ (u j)) ∉ W

def coneBall {n : ℕ} (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) :
    Set (EuclideanSpace ℂ (Fin n)) :=
  {y | ‖y‖ < 1 ∧ ∀ q ∈ W, eval (h.pointOf y) q = 0}

def ConeBallFinite.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f →
      Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) < ⊤

def ConeFsLogIntegrable.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → linForm u ∉ W →
      IntegrableOn (fun y => fsLog h u (h.pointOf y)) (coneBall h W)
        (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))

def ConeHyperplaneNull.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → linForm u ∉ W →
      Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
        (coneBall h W ∩ {y | ∑ j, u j * h.pointOf y j = 0}) = 0

end

end GroundTheory.Heights₂.Heights
