module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Objects
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

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def StepTwo.Filt.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E]
    [IsScalarTower S Ω E] (M₁ M₂ : FinGradedSub (S := S) (x := x) E), (∀ c, M₂.piece c ≤ M₁.piece c) →
    ∀ J : Ideal (Poly S N), (∀ (f : Poly S N) (e : ℕ), f ∈ J → f.IsHomogeneous e → ∀ (a : ℤ),
      ∀ z ∈ M₁.piece a, aeval x f • z ∈ M₂.piece (a + e)) →
    ∃ (n : ℕ) (Nf : Fin (n + 1) → FinGradedSub (S := S) (x := x) E) (g : Fin n → E) (deg : Fin n → ℤ)
      (pr : Fin n → Ideal (Poly S N)),
      Nf 0 = M₂ ∧ Nf (Fin.last n) = M₁ ∧
      ∀ k : Fin n, (pr k).IsPrime ∧ (∀ p ∈ pr k, ∀ d : ℕ, homogeneousComponent d p ∈ pr k) ∧
        primeOf (S := S) x ≤ pr k ∧
        (∀ (f : Poly S N) (e : ℕ), f ∈ J → f.IsHomogeneous e → f ∈ pr k) ∧
        g k ∈ (Nf k.succ).piece (deg k) ∧
        (∀ c, (Nf k.succ).piece c = (Nf k.castSucc).piece c ⊔ Submodule.span S
          {z | ∃ (f : Poly S N) (d : ℕ), f.IsHomogeneous d ∧ deg k + d = c ∧ z = aeval x f • g k}) ∧
        ∀ (f : Poly S N) (d : ℕ), f.IsHomogeneous d →
          (f ∈ pr k ↔ aeval x f • g k ∈ (Nf k.castSucc).piece (deg k + d))

end

end GroundTheory.Heights₂.Heights.Kleiman
