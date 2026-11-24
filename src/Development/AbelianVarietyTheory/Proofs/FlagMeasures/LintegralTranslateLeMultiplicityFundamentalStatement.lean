module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralTranslateLeMultiplicityFundamental
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

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.lintegral_translate_le_multiplicity_fundamental : ∀ (B : RowsAut) (S : Set B.I.Ginf) (y : B.I.GA) (Φ : B.I.GA → ENNReal), 1 ≤ B.I.n → 1 ≤ B.g → MeasurableSet S → (∀ a ∈ S, ∀ a' ∈ S, ∀ v, dOp (uMat ((a * a'⁻¹) v)) ≤ Real.log 2) → Measurable Φ → (∀ γ ∈ B.I.GFset, ∀ z, Φ (γ * z) = Φ z) → (∀ k ∈ B.I.Kg B.g, ∀ z, Φ (z * (1, k)) = Φ z) → B.μf (B.I.Kg B.g) * ∫⁻ a in S, Φ (y * (a, 1)) ∂(muInf B.I) ≤ ENNReal.ofReal ((1 + 4 * Real.sqrt B.I.n / tau1 B.I y ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f))) * ∫⁻ z in B.fund, Φ z ∂(B.I.muA B.μf) := by
  first | exact @GlobalTheory.BoundedUnfold.lintegral_le_multiplicity | exact GlobalTheory.BoundedUnfold.lintegral_le_multiplicity | (intros; apply GlobalTheory.BoundedUnfold.lintegral_le_multiplicity <;> assumption)
