module

public import Formalism.FormalDegreeBessel.StatementBF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellQuotientNormalisesUnipotent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

theorem _root_.GlobalTheory.T.bigCell_quotient_normalises_unipotent : ∀ (k r : ℕ) (c : Fin r → ℂ) (μ₁ μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) → μ₁ᴴ * Formalism.QuantumDeterminants.Hb k * μ₁ = Formalism.QuantumDeterminants.Hb k → μᴴ * Formalism.QuantumDeterminants.Hb k * μ = Formalism.QuantumDeterminants.Hb k → ∀ n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, n ∈ Formalism.QuantumDeterminants.Nset k r ↔ (Formalism.QuantumDeterminants.bigCell k r c μ₁)⁻¹ * Formalism.QuantumDeterminants.bigCell k r c μ * n * ((Formalism.QuantumDeterminants.bigCell k r c μ₁)⁻¹ * Formalism.QuantumDeterminants.bigCell k r c μ)⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r := by
  first | exact @GlobalTheory.BigConvLevi.levi_conj_mem_iff | exact GlobalTheory.BigConvLevi.levi_conj_mem_iff | (intros; apply GlobalTheory.BigConvLevi.levi_conj_mem_iff <;> assumption)
