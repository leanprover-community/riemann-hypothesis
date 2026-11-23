module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselAmplitudeIndependentOfQuotientMeasure
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.SnMass
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.besselAmplitude_eq_smul_of_rescaled_stabilizerHaar : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (z z' : Fin (2 * r + k + 1) → ℂ) (ψ ψ' : Mat k r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (cN : ℝ), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsURepOn (UWset k r z) π → IsURepOn (UWset k r z') π' → (∀ n ∈ Nset k r, ‖ψ n‖ = 1 ∧ ‖ψ' n‖ = 1) → IsSPsiEquiv z ψ π Φ → IsSPsiEquiv z' ψ' π' Φ' → ContinuousOn Φ (GG k r) → ContinuousOn Φ' (GG k r) → ∀ (γ : Mat k r) (μG μR ν ν' : Measure (Mt k r)) (t : ℝ), γ ∈ GG k r → (∀ ρ ∈ Rset k r γ, ψ (γ * ρ * γ⁻¹) = ψ' ρ) → IsHaarOn (GG k r) μG → IsHaarOn (Rset k r γ) μR → 0 < t → IsQuotMeas μG μR ν → IsQuotMeas μG (ENNReal.ofReal t • μR) ν' → ampJ ν cN Φ Φ' γ = (t : ℂ) • ampJ ν' cN Φ Φ' γ := by
  first | exact @GlobalTheory.SnMass.AmpUniq.amp_uniq | exact GlobalTheory.SnMass.AmpUniq.amp_uniq | (intros; apply GlobalTheory.SnMass.AmpUniq.amp_uniq <;> assumption)
