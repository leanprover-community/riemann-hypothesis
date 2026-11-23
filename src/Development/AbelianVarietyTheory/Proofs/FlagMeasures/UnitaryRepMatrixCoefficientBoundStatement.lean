module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRepMatrixCoefficientBound
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
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.unitary_rep_matrix_coefficient_bound : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → ∀ β : UJ ε → ENNReal, Measurable β → (∀ y, β y ≠ ⊤) → (∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1) → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d c : ℝ) (u v v' : H), IsURepOn (UJset ε) σ → IsFdeg (muG ε) σ d → 8 * n * rkR ε < c → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) u⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v', σ (umat g) u⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) v'⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → Continuous (fun g : UJ ε => (∫ m, ⟪v, σ (umat (m * g)) u⟫_ℂ ∂ν)) ∧ Integrable (fun g : UJ ε => ((β g).toReal : ℂ) * ((∫ m, ⟪v, σ (umat (m * g)) u⟫_ℂ ∂ν) * star (∫ m, ⟪v', σ (umat (m * g)) u⟫_ℂ ∂ν))) (muG ε) ∧ ∫ g : UJ ε, ((β g).toReal : ℂ) * ((∫ m, ⟪v, σ (umat (m * g)) u⟫_ℂ ∂ν) * star (∫ m, ⟪v', σ (umat (m * g)) u⟫_ℂ ∂ν)) ∂(muG ε) = (∫ m, ⟪v, σ (umat m) v'⟫_ℂ ∂ν) * ((‖u‖ ^ 2 / d : ℝ) : ℂ) := by
  first | exact @GlobalTheory.Dec.ConstTermNorm.constTerm_inner | exact GlobalTheory.Dec.ConstTermNorm.constTerm_inner | (intros; apply GlobalTheory.Dec.ConstTermNorm.constTerm_inner <;> assumption)
