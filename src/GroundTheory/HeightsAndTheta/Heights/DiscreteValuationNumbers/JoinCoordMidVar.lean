module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type}

def midDeg (a : K ⊕ K' → ℤ) : K ⊕ (K₂ ⊕ K') → ℤ :=
  Sum.elim (fun k => a (.inl k)) (Sum.elim 0 (fun k => a (.inr k)))

def midVar (ι₂ : K₂ → Type) :
    (Σ k : K ⊕ K', Sum.elim ι ι' k) → (Σ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k)
  | ⟨.inl k, i⟩ => ⟨.inl k, i⟩
  | ⟨.inr k, i⟩ => ⟨.inr (.inr k), i⟩

theorem joinCoord_midVar {Ω : Type*} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) {ι₂ : K₂ → Type}
    (w : (Σ k, ι₂ k) → Ω) (p : Σ k : K ⊕ K', Sum.elim ι ι' k) :
    joinCoord x (joinCoord w z) (midVar ι₂ p) = joinCoord x z p := by
  obtain ⟨k | k, i⟩ := p <;> rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
