module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverSkewHermitianAdelicMatricesShrunkCompact
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)


theorem _root_.GlobalTheory.T.cover_skewHermitianAdelicMatrices_shrunkCompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ j : ℕ, ∃ (Ω : Set (AF F ⊗[F] E)) (B : ℝ), IsCompact Ω ∧ ∀ μ : Fin j → ℕ, ∃ Y : Finset (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), (Y.card : ℝ) ≤ B * ∏ i, bse F ^ (j * μ i) ∧ (∀ y ∈ Y, cT (sigR (AF F) σ) y = -y) ∧ ∀ x : Matrix (Fin j) (Fin j) (AF F ⊗[F] E), cT (sigR (AF F) σ) x = -x → ∃ x₀ : Matrix (Fin j) (Fin j) E, cT (σ : E →+* E) x₀ = -x₀ ∧ ∃ y ∈ Y, ∃ ω : Matrix (Fin j) (Fin j) (AF F ⊗[F] E), cT (sigR (AF F) σ) ω = -ω ∧ (∀ i k, ω i k ∈ Ω) ∧ x = adMat F x₀ + (y + (tor F E fun i => (μ i : ℤ)).1 * ω * cT (sigR (AF F) σ) (tor F E fun i => (μ i : ℤ)).1) := by
  first | exact @GlobalTheory.SkewAdCover.cover | exact GlobalTheory.SkewAdCover.cover | (intros; apply GlobalTheory.SkewAdCover.cover <;> assumption)
