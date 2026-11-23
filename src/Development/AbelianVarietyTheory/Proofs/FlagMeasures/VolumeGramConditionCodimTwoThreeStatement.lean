module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeGramConditionCodimTwoThree
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

theorem _root_.GlobalTheory.T.volume_gramCondition_codim_two_three : ∀ (k r : ℕ), 1 ≤ r → 2 * r + 6 ≤ k → ∀ m ∈ UH (Hb k), ∀ P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))), (Module.finrank ℂ P₀ = k - 2 ∨ Module.finrank ℂ P₀ = k - 1) → volume {B : Fin r → Fin (k + 1) → ℂ | gramProj P₀ (fun b => m⁻¹ *ᵥ B b) = 0} = 0 ∧ ∀ R' y : ℝ, 1 ≤ R' → 0 < y → volume {B : Fin r → Fin (k + 1) → ℂ | (∀ b, eucl (m⁻¹ *ᵥ B b) ≤ R') ∧ y < gramProj P₀ (fun b => m⁻¹ *ᵥ B b) ∧ gramProj P₀ (fun b => m⁻¹ *ᵥ B b) ≤ 2 * y} ≤ ENNReal.ofReal ((Real.pi * R' ^ 2) ^ (3 * r) * 4 * R' ^ (2 * r ^ 2 + 2 * r) * Real.pi ^ (r ^ 2) * (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) * (2 * y) ^ (2 * (k - 2 - r))) := by
  first | exact @GlobalTheory.Amp.GramVol.vol_gram_codim_three | exact GlobalTheory.Amp.GramVol.vol_gram_codim_three | (intros; apply GlobalTheory.Amp.GramVol.vol_gram_codim_three <;> assumption)
