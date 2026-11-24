module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoFlagsGramNumberNormalFormEqGramProjection
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

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.twoFlagsGramNumber_normalForm_eq_gram_projection : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ), 2 ≤ k → TwoFl k r z z' g₀ → IsNormal k r β g₀ → ∀ m ∈ UH (Hb k), ∃ P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))), (Module.finrank ℂ P₀ = k - 2 ∨ Module.finrank ℂ P₀ = k - 1) ∧ ∀ (u : UT r → ℂ) (q : PPar k r) (a : Fin r → ℝ), (∀ b, 0 < a b) → Yv k r z z' g₀ (uEmb k r (upper u) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) = gramProj P₀ fun b => m⁻¹ *ᵥ q.1 b := by
  first | exact @GlobalTheory.Amp.NormGram.Yv_normal | exact GlobalTheory.Amp.NormGram.Yv_normal | (intros; apply GlobalTheory.Amp.NormGram.Yv_normal <;> assumption)
