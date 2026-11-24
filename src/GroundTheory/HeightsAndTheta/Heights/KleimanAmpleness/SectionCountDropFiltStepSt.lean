module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
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

universe u w

def SectionCount.Drop.Filt.Step.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Q : LineBundle S x) (J₁ pp : Ideal (Poly S N)) (g : Poly S N) (e : ℕ),
    (∀ f ∈ J₁, ∀ d : ℕ, homogeneousComponent d f ∈ J₁) → primeOf (S := S) x ≤ J₁ →
    g.IsHomogeneous e → (∀ f, f ∈ pp ↔ f * g ∈ J₁) →
    ∃ φ : (Q.twist (idealSys x (J₁ ⊔ Ideal.span {g}))).secs →ₗ[S]
        SubSystem.quotH (Q.twist (twistSys S x (-(e : ℤ))))
          ((Q.twist (twistSys S x (-(e : ℤ)))).twist (idealSys x pp)) 0,
      ∀ s, φ s = 0 → (s : Ω) ∈ (Q.twist (idealSys x J₁)).secs

end

end GroundTheory.Heights₂.Heights.Kleiman
