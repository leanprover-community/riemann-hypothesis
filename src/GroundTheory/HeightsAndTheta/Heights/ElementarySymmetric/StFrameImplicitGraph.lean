module

public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StFrameJacobianGeneric
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial

def FrameImplicitGraph.Statement : Prop :=
  ∀ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) (z : EuclideanSpace ℂ (Fin n)),
    (∀ k, eval (fun i => z i) (f k) = 0) → eval (fun i => z i) (frameJacobianDet b I f) ≠ 0 →
    ∀ U : Set (EuclideanSpace ℂ (Fin n)), IsOpen U → z ∈ U →
      ∃ (Ω : Set (I → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n))) (g : (I → ℂ) → EuclideanSpace ℂ (Fin n)),
        IsOpen Ω ∧ IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧ DifferentiableOn ℂ g Ω ∧
          (∀ w ∈ Ω, frameProj b I (g w) = w) ∧
          {x : EuclideanSpace ℂ (Fin n) | ∀ k, eval (fun i => x i) (f k) = 0} ∩ V = g '' Ω

end

end GroundTheory.Heights₂.Heights
