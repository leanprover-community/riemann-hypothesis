module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Ideal.Maps
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Polynomial.Basic

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ker_fibreMap {σ ι : Type*} (t : σ → ℂ) :
    RingHom.ker (MvPolynomial.map (eval t) : MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ) =
      (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) :=
  MvPolynomial.ker_map _

def GenericFibreTor.Statement : Prop :=
  ∀ (σ : Type) [Finite σ] (ι : Type) [Finite ι] (L : Ideal (MvPolynomial ι (MvPolynomial σ ℂ))),
    ∃ F : MvPolynomial σ ℂ, F ≠ 0 ∧ ∀ t : σ → ℂ, eval t F ≠ 0 →
      L ⊓ RingHom.ker (MvPolynomial.map (eval t) : MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ) ≤
        RingHom.ker (MvPolynomial.map (eval t) : MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ) * L

end

end GroundTheory.Heights₂.Heights
