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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type}

def assocDeg (a : K ⊕ K' → ℤ) : K ⊕ (K' ⊕ K₂) → ℤ :=
  Sum.elim (fun k => a (.inl k)) (Sum.elim (fun k => a (.inr k)) 0)

def assocVar (ι₂ : K₂ → Type) :
    (Σ k : K ⊕ K', Sum.elim ι ι' k) → (Σ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k)
  | ⟨.inl k, i⟩ => ⟨.inl k, i⟩
  | ⟨.inr k, i⟩ => ⟨.inr (.inl k), i⟩

theorem joinCoord_assocVar {Ω : Type*} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) {ι₂ : K₂ → Type}
    (w : (Σ k, ι₂ k) → Ω) (p : Σ k : K ⊕ K', Sum.elim ι ι' k) :
    joinCoord x (joinCoord z w) (assocVar ι₂ p) = joinCoord x z p := by
  obtain ⟨k | k, i⟩ := p <;> rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
