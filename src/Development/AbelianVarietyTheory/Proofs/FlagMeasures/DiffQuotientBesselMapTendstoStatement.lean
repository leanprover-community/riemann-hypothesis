module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiffQuotientBesselMapTendsto
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.diffQuotient_besselMap_tendsto : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (z : Fin (2 * r + k + 1) → ℂ) (ψ : Mat k r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (l : H → Wp) (x : H) (X : Mat k r), IsURepOn (GG k r) σ → IsBesselMapSm z ψ σ π l → IsSmoothVec σ x → InLieHpk k r X → Filter.Tendsto (fun t : ℝ => l ((t : ℂ)⁻¹ • (σ (NormedSpace.exp ((t : ℂ) • X)) x - x))) (nhdsWithin 0 {0}ᶜ) (nhds (l (dsig σ X x))) ∧ ContinuousOn (fun g => l (σ g x)) (GG k r) ∧ ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ GG k r ∧ σ (NormedSpace.exp ((t : ℂ) • X)) x - x = ∫ u in (0 : ℝ)..t, σ (NormedSpace.exp ((u : ℂ) • X)) (dsig σ X x) := by
  first | exact @GlobalTheory.diffQuot_bessel | exact GlobalTheory.diffQuot_bessel | (intros; apply GlobalTheory.diffQuot_bessel <;> assumption)
