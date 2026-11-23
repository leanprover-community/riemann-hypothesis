module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CutoffComputesBesselQuotientIntegral
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

theorem _root_.GlobalTheory.T.cutoff_computes_besselQuotientIntegral : ∀ (k r : ℕ) (R : Set (Mat k r)) (μG μR ν : Measure (Mt k r)), IsClosedSub k r R → IsHaarOn (GG k r) μG → IsHaarOn R μR → IsUnimod R μR → IsQuotMeas μG μR ν → ν {x | Matrix.of x ∉ GG k r} = 0 ∧ (∀ A : Set (Mt k r), MeasurableSet A → (∀ ρ ∈ R, ∀ x, Matrix.of x ∈ GG k r → (lmulM ρ x ∈ A ↔ x ∈ A)) → μG A = 0 → ν A = 0) ∧ ∃ φ, SubCut (GG k r) μR φ ∧ ∀ F : Mt k r → ℝ≥0∞, Measurable F → (∀ ρ ∈ R, ∀ x, Matrix.of x ∈ GG k r → F (lmulM ρ x) = F x) → ∫⁻ x, F x ∂ν = ∫⁻ x, φ x * F x ∂μG := by
  first | exact @GlobalTheory.Amp.CutQuot.cut_quotient | exact GlobalTheory.Amp.CutQuot.cut_quotient | (intros; apply GlobalTheory.Amp.CutQuot.cut_quotient <;> assumption)
