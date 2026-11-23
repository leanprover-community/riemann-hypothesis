module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittFrameReduceRank
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

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.witt_frame_reduce_rank : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∃ (n' : ℕ) (J' : Matrix (Fin n') (Fin n') E) (X' Y' : Matrix (Fin n') (Fin r) E) (ι : GAd σ J' →* GAd σ J), IsHermND σ J' ∧ IsWittFrame σ J' X' Y' ∧ Continuous ι ∧ (∀ γ ∈ ratPts σ J', ι γ ∈ ratPts σ J) ∧ (∀ g', Sends σ J (ι g') (Xᵀ 0) (Xᵀ 0)) ∧ (∀ q ∈ minParOne σ J' X', ι q ∈ minParOne σ J X) ∧ ∀ a, IsTorus σ J X Y a → (∀ a', IsTorus σ J' X' Y' a' → ∀ s', ι (a' s') = a (Fin.cons 0 s')) ∧ (∀ (s₁ : ℝ) g', Commute (a (Fin.cons s₁ 0)) (ι g')) ∧ ∀ p ∈ minPar σ J X, ∃ g', ∃ q₀ ∈ minParOne σ J X, ∃ s₁ : ℝ, p = q₀ * a (Fin.cons s₁ 0) * ι g' ∧ ∀ h', (ι h')⁻¹ * q₀ * ι h' ∈ minParOne σ J X := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.Levi.exists_levi | exact GlobalTheory.CompanionTheory.RedCov.Levi.exists_levi | (intros; apply GlobalTheory.CompanionTheory.RedCov.Levi.exists_levi <;> assumption)
