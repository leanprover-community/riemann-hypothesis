module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
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

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def PairNumberRelabel.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (K₁ : Type) [Fintype K₁] [DecidableEq K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)]
    (K₂ : Type) [Fintype K₂] [DecidableEq K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)), (∀ v, (σ v).1 = e v.1) →
    ∀ P : Ideal (MRing ι₁ O),
      (∀ d : ℕ, IsModelOver P d → IsModelOver (P.map (rename σ)) d) ∧
      (∀ (b : K₂ → ℤ) (f g : MRing ι₁ O), IsVerticalDivisor P ϖ (b ∘ e) f g →
        IsVerticalDivisor (P.map (rename σ)) ϖ b (rename σ f) (rename σ g)) ∧
      (∀ (n : ℕ) (x x' : Fin n → K₂ → ℤ) (f g : Fin n → MRing ι₁ O)
        (Gs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ) (Q : List (K₂ → ℤ)),
        pairNum (P.map (rename σ)) x x' (fun i => rename σ (f i)) (fun i => rename σ (g i)) Gs Q =
          pairNum P (fun i => x i ∘ e) (fun i => x' i ∘ e) f g Gs (Q.map (· ∘ e)))

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
