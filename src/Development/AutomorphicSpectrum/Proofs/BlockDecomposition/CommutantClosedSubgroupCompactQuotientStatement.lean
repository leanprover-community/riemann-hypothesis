module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutantClosedSubgroupCompactQuotient
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipMinSubsetMinParOne

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.commutant_closed_subgroup_compact_quotient : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (M : Type) [Finite M] (S : M → Matrix (Fin n) (Fin n) E) (L : Subgroup (GAd σ J)), IsClosed (L : Set (GAd σ J)) → (∀ g ∈ L, ∀ k, (matHom _ σ J g).1 * (S k).map (inclR (F := F) (AF F)) = (S k).map (inclR (F := F) (AF F)) * (matHom _ σ J g).1) → (∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ L, ∀ ξ : Fin n → E, ξ ≠ 0 → ε ≤ hgt σ J g ξ) → (∀ γ ∈ ratPts σ J, (∀ k, (matHom _ σ J γ).1 * (S k).map (inclR (F := F) (AF F)) = (S k).map (inclR (F := F) (AF F)) * (matHom _ σ J γ).1) → γ ∈ L) → ∃ Ω : Set (GAd σ J), IsCompact Ω ∧ Ω ⊆ L ∧ ∀ g ∈ L, ∃ δ ∈ ratPts σ J, δ ∈ L ∧ δ⁻¹ * g ∈ Ω := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.exists_isCompact_of_centralizer_height | exact GlobalTheory.CompanionTheory.ParCocompact.exists_isCompact_of_centralizer_height | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.exists_isCompact_of_centralizer_height <;> assumption)
