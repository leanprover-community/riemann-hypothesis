module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvAboveTop
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvAboveTopGeneral
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvIdealComponent
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvIdealRepresentation
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvMonomialReduction
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvPolynomialReduction
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvStaircaseComponent
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvStaircaseDegree
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvStepReduction
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PHomogeneousComponentMul
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

open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top


open GroundTheory.Heights₂.Heights.RestTerms in
theorem RootFieldNumerics.coinv_above_top : CoinvAboveTopGeneral.Statement :=
  CoinvAboveTopGeneral.proof (CoinvAboveTop.proof
    (CoinvPolynomialReduction.proof (CoinvMonomialReduction.proof CoinvStepReduction.proof))
    (CoinvIdealComponent.proof CoinvIdealRepresentation.proof HomogeneousComponentMul.proof)
    (CoinvStaircaseComponent.proof CoinvStaircaseDegree.proof))

theorem RootFieldNumerics.decomposition_power_sums_top_degree : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (F : RP Ψ N), 2 ≤ N → F.IsHomogeneous (dimFl Ψ N + 1) → ∃ Q : Ψ → ℕ → RP Ψ N, (∀ τ k, 1 ≤ k → k ≤ N → (Q τ k).IsHomogeneous (dimFl Ψ N + 1 - k)) ∧ F = ∑ τ, ∑ k ∈ Finset.Icc 1 N, pk τ k * Q τ k := by
  intro Ψ _ _ N F _ hF
  have hlt : Fintype.card Ψ * (Fintype.card (Fin N) * (Fintype.card (Fin N) - 1) / 2) < dimFl Ψ N + 1 := by
    simp [dimFl]
  obtain ⟨Q, hQ, hFQ⟩ := RootFieldNumerics.coinv_above_top ℝ Ψ (Fin N) (dimFl Ψ N + 1) F hF hlt
  refine ⟨fun τ k => Q k τ, fun τ k _ _ => hQ k τ, ?_⟩
  rw [hFQ, Fintype.card_fin, Finset.sum_comm]
  rfl
