module

public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselBigCellCoordinatesUnique
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.besselBigCell_coordinates_unique : ∀ (k r : ℕ) (x y : Fin r → ℂ), (∀ a, x a ≠ 0) → (∀ a, y a ≠ 0) → ∀ n₁ ∈ Nset k r, ∀ n₂ ∈ Nset k r, ∀ n₁' ∈ Nset k r, ∀ n₂' ∈ Nset k r, ∀ m₁ ∈ Formalism.FourierDecayAlt.B2.UWb k r, ∀ m₂ ∈ Formalism.FourierDecayAlt.B2.UWb k r, n₁⁻¹ * bigCell k r x 1 * m₁ * n₁' = n₂⁻¹ * bigCell k r y 1 * m₂ * n₂' → n₁ = n₂ ∧ x = y ∧ m₁ = m₂ ∧ n₁' = n₂' := by
  first | exact @GlobalTheory.CellDens.bigCell_coords_unique | exact GlobalTheory.CellDens.bigCell_coords_unique | (intros; apply GlobalTheory.CellDens.bigCell_coords_unique <;> assumption)
