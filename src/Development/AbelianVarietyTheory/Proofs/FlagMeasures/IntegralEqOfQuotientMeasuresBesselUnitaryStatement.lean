module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralEqOfQuotientMeasuresBesselUnitary
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

theorem _root_.GlobalTheory.T.integral_eq_of_quotientMeasures_besselUnitary : ∀ (k r : ℕ) (R : Set (Mat k r)) (μG μR ν ν' : Measure (Mt k r)), IsClosedSub k r R → IsHaarOn (GG k r) μG → IsHaarOn R μR → IsUnimod R μR → IsQuotMeas μG μR ν → IsQuotMeas μG μR ν' → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (F : Mat k r → V), ContinuousOn F (GG k r) → (∀ ρ ∈ R, ∀ x ∈ GG k r, F (ρ * x) = F x) → (Integrable (fun x : Mt k r => F (Matrix.of x)) ν ↔ Integrable (fun x : Mt k r => F (Matrix.of x)) ν') ∧ ∫ x, F (Matrix.of x) ∂ν = ∫ x, F (Matrix.of x) ∂ν' := by
  first | exact @GlobalTheory.SnMass.QuotUniq.quot_uniq | exact GlobalTheory.SnMass.QuotUniq.quot_uniq | (intros; apply GlobalTheory.SnMass.QuotUniq.quot_uniq <;> assumption)
