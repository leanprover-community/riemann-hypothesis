module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EmbeddingCompatibleWithWeilAndDenominator
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.embedding_compatible_with_weil_and_denominator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∃ ι : M2 E N → M2 E (N + 1), (∀ γ ∈ UU E N, ι γ ∈ UU E (N + 1) ∧ (∀ a, (ι γ).toBlocks₂₁ a 0 = 0) ∧ (∀ (Z : CM Ψ (N + 1) (N + 1)) τ, (hDen Ψ (ι γ) Z τ).det = (hDen Ψ γ (dropZ Ψ Z) τ).det) ∧ (∀ φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ, IsSB φ → dropF (weil Ψ (ι γ) φ) = weil Ψ γ (dropF φ)) ∧ ∀ γ' ∈ UU E N, (botSpan (ι γ) = botSpan (ι γ') ↔ botSpan γ = botSpan γ')) ∧ ∀ g ∈ UU E (N + 1), (∀ a, g.toBlocks₂₁ a 0 = 0) → ∃ γ ∈ UU E N, botSpan g = botSpan (ι γ) := by
  first | exact @GlobalTheory.SW.Emb.exists_embedding | exact GlobalTheory.SW.Emb.exists_embedding | (intros; apply GlobalTheory.SW.Emb.exists_embedding <;> assumption)
