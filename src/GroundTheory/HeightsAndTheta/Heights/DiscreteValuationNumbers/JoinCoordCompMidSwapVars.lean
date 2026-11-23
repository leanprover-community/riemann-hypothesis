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
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ScaledRankOneLeStandardRankOne

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

variable {K K' K₂ : Type}

def midSwapBlocks : K ⊕ (K₂ ⊕ K') ≃ K ⊕ (K' ⊕ K₂) :=
  Equiv.sumCongr (Equiv.refl K) (Equiv.sumComm K₂ K')

def midSwapVars (ι : K → Type) (ι' : K' → Type) (ι₂ : K₂ → Type) :
    (Σ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k) ≃
      (Σ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k) where
  toFun
    | ⟨.inl k, i⟩ => ⟨.inl k, i⟩
    | ⟨.inr (.inl k), i⟩ => ⟨.inr (.inr k), i⟩
    | ⟨.inr (.inr k), i⟩ => ⟨.inr (.inl k), i⟩
  invFun
    | ⟨.inl k, i⟩ => ⟨.inl k, i⟩
    | ⟨.inr (.inl k), i⟩ => ⟨.inr (.inr k), i⟩
    | ⟨.inr (.inr k), i⟩ => ⟨.inr (.inl k), i⟩
  left_inv := by
    rintro ⟨k | k | k, i⟩ <;> rfl
  right_inv := by
    rintro ⟨k | k | k, i⟩ <;> rfl

theorem midSwapVars_fst {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}
    (v : Σ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k) :
    (midSwapVars ι ι' ι₂ v).1 = midSwapBlocks v.1 := by
  obtain ⟨k | k | k, i⟩ := v <;> rfl

theorem joinCoord_comp_midSwapVars {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type} {Ω : Type*}
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω) :
    joinCoord x (joinCoord z w) ∘ midSwapVars ι ι' ι₂ = joinCoord x (joinCoord w z) := by
  funext v
  obtain ⟨k | k | k, i⟩ := v <;> rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord fnField pairNum midSwapBlocks midSwapVars
  ptCoord ptIdx unif)

def PairNumberRelabelAlt.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)]
    (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)), (∀ v, (σ v).1 = e v.1) →
    ∀ (y : (Σ k, ι₂ k) → Ω) (d : ℕ),
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (y ∘ σ)) d →
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O y) d ∧ fnField O y = fnField O (y ∘ σ) ∧
        (∀ (b : K₂ → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι₁),
          IsVertDiv O (mcIdeal O (y ∘ σ)) (b ∘ e) f g →
            IsVertDiv O (mcIdeal O y) b (rename σ f) (rename σ g)) ∧
        ∀ (I₁ : IFamily (IsLocalRing.ResidueField O) ι₁) (I : IFamily (IsLocalRing.ResidueField O) ι₂),
          IsFieldIntersection I₁ → IsFieldIntersection I →
        ∀ (n : ℕ) (a a' : Fin n → K₂ → ℤ) (f g : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι₁),
          (∀ i, IsVertDiv O (mcIdeal O (y ∘ σ)) (a i ∘ e - a' i ∘ e) (f i) (g i)) →
        ∀ H : MvPolynomial (Fin n) ℤ, H.IsHomogeneous (d + 1) →
          pairNum O I₁ (mcIdeal O (y ∘ σ)) d (fun i => a i ∘ e) (fun i => a' i ∘ e) f g H =
            pairNum O I (mcIdeal O y) d a a' (fun i => rename σ (f i)) (fun i => rename σ (g i)) H

end GroundTheory.Heights₂.Heights.NumbersDVR
