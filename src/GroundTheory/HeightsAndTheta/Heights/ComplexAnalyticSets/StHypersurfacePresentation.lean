module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Ideal.Prime
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

open MvPolynomial

noncomputable section

def HypersurfacePresentation.Statement : Prop :=
  ∀ (σ : Type) [Finite σ] (ι : Type) [Finite ι] (K : Ideal (MvPolynomial ι (MvPolynomial σ ℂ))),
    K.IsPrime → (∀ s : MvPolynomial σ ℂ, C s ∈ K → s = 0) →
    ∃ (d : ℕ) (y : Fin d → MvPolynomial ι (MvPolynomial σ ℂ)) (θ : MvPolynomial ι (MvPolynomial σ ℂ))
      (m : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))) (D : MvPolynomial (Fin d) (MvPolynomial σ ℂ))
      (q : ι → Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)))
      (u v : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))),
      m.Monic ∧ D ≠ 0 ∧ u * m + v * Polynomial.derivative m = Polynomial.C D ∧
      (∀ H : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)),
        Polynomial.eval₂ (aeval y).toRingHom θ H ∈ K ↔ m ∣ H) ∧
      ∀ i, aeval y D * X i - Polynomial.eval₂ (aeval y).toRingHom θ (q i) ∈ K

end

end GroundTheory.Heights₂.Heights
