module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.RingTheory.KrullDimension.Basic
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

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial

def frameDeriv {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (j : Fin n)
    (f : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  ∑ l, C (b j l) * pderiv l f

def frameJacobianDet {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  Matrix.det (Matrix.of fun k j : {j // j ∉ I} => frameDeriv b j (f k))

def FrameJacobianGeneric.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    ∀ b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)),
      ∃ (I₀ : Finset (Fin n)) (f : {j // j ∉ I₀} → MvPolynomial (Fin n) ℂ) (s : MvPolynomial (Fin n) ℂ),
        I₀.card = d ∧ (∀ k, f k ∈ J) ∧ s ∉ J ∧ frameJacobianDet b I₀ f ∉ J ∧
          ∀ p ∈ J, s * p ∈ Ideal.span (Set.range f)

end

end GroundTheory.Heights₂.Heights
