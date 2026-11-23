module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricChainLastTwoStepsRootOfUnity
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

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

theorem _root_.GlobalTheory.T.parahoricChain_last_two_steps_root_of_unity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s : ℕ) (κ t : Type) [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t] (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ), (∀ j, IsUnram (η j)) → ∀ g : GL (XIx κ t (s + 1) ⊕ Fin 0) k, g ∈ ((twistChain s t κ δ hδ η).lev (s + 1) 0 rfl).J → ∃ c : ℂ, (∃ n : ℕ, 0 < n ∧ c ^ n = 1) ∧ (∀ h x₀ y, (twistChain s t κ δ hδ η).Psi h (g.val.toBlocks₁₁ * x₀) (g.val.toBlocks₁₁ *ᵥ y) = c * (twistChain s t κ δ hδ η).Psi h x₀ y) ∧ ∀ (ψ : AddChar k Circle) (ε : k) (w : kˣ) (y : XIx κ t (s + 1) → k) x, (twistChain s t κ δ hδ η).xiTop (box _ w) ψ ν ε (Submodule.Quotient.mk y) (x * g.val.toBlocks₁₁) = c * (twistChain s t κ δ hδ η).xiTop (box _ w) ψ ν ε (Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y)) x := by
  exact @GlobalTheory.LevelLaw.last_steps_law
