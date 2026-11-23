module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InductionInStagesTwoFactorsEquiv
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

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

theorem _root_.GlobalTheory.T.inductionInStages_twoFactors_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {β₀ β₁ a b n V W U : Type} [Fintype β₀] [LinearOrder β₀] [Fintype β₁] [LinearOrder β₁] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U] {m : β₀ ⊕ₗ β₁ → Type} [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)] (E : (Σ c, m c) ≃ n) (h : a ⊕ b ≃ n) (ψ₀ : (Σ i, m (toLex (Sum.inl i))) ≃ a) (ψ₁ : (Σ j, m (toLex (Sum.inr j))) ≃ b), (∀ i x, h (.inl (ψ₀ ⟨i, x⟩)) = E ⟨toLex (.inl i), x⟩) → (∀ j x, h (.inr (ψ₁ ⟨j, x⟩)) = E ⟨toLex (.inr j), x⟩) → ∀ (ρ₀ : Representation ℂ (Levi k fun i => m (toLex (Sum.inl i))) V) (ρ₁ : Representation ℂ (Levi k fun j => m (toLex (Sum.inr j))) W) (σ : Representation ℂ (Levi k m) U) (κ : V ⊗[ℂ] W ≃ₗ[ℂ] U), (∀ g x, σ g (κ x) = κ (TensorProduct.map (ρ₀ fun i => g (toLex (.inl i))) (ρ₁ fun j => g (toLex (.inr j))) x)) → Nonempty ((ind₂ h (extTensor (parInd ψ₀ ρ₀) (parInd ψ₁ ρ₁))).Equiv (parInd E σ)) := by
  first | exact @GlobalTheory.SmGL.StagesTwo.ind₂_parInd_parInd_equiv | exact GlobalTheory.SmGL.StagesTwo.ind₂_parInd_parInd_equiv | (intros; apply GlobalTheory.SmGL.StagesTwo.ind₂_parInd_parInd_equiv <;> assumption)
