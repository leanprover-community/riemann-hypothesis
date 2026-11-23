module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeDegenerateOperatorNormLeRealPlace
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

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.amplitude_degenerate_operatorNorm_le_realPlace : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (ψ ψ' : Mat k r → ℂ) (μG μW μW' νS νS' μR νR : Measure (Mt k r)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (γ : Mat k r) (c κ s H₁ De : ℝ) (q : ℕ), 1 ≤ j → j + 2 ≤ k → 16 * r ^ 3 + 4 * r + 2 ≤ q → 0 < κ → 0 < s → 1 ≤ H₁ → OneSide z π ψ μG μW (ENNReal.ofReal κ • lebN k r) νS Φ c → OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c → TailBd z νS Φ q H₁ → TailBd z' νS' Φ' q H₁ → DeOK k r z z' γ De → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → IsQuotMeas μG μR νR → Integrable (fun x => (innerSL ℂ (Φ' (Matrix.of x))).smulRight (Φ (γ * Matrix.of x))) νR ∧ ‖(haveI := FiniteDimensional.complete ℂ Wp; ampJ νR c Φ Φ' γ)‖ ≤ κ / s * degBd k r j q H₁ De (Dj k r hj z z' γ) (sgV k r z z' γ H₁) := by
  first | exact @GlobalTheory.Amp.DegConv.deg_core | exact GlobalTheory.Amp.DegConv.deg_core | (intros; apply GlobalTheory.Amp.DegConv.deg_core <;> assumption)
