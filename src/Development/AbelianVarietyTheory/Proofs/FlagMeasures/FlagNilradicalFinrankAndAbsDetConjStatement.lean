module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagNilradicalFinrankAndAbsDetConj
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

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.flagNilradical_finrank_and_abs_det_conj : ∀ (n : ℕ) (f g : Matrix (Fin n) (Fin n) ℂ) (r : ℕ) (F : ℕ → Submodule ℂ (Fin n → ℂ)) (N : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)), f * g = 1 → ‖f.det‖ = 1 → Monotone F → F 0 = ⊥ → F r = ⊤ → (∀ s, ∀ y ∈ F s, f *ᵥ y ∈ F s) → (∀ X, X ∈ N ↔ ∀ s, s < r → ∀ y ∈ F (s + 1), X *ᵥ y ∈ F s) → Module.finrank ℂ N = ∑ s ∈ Finset.range r, (Module.finrank ℂ (F (s + 1)) - Module.finrank ℂ (F s)) * Module.finrank ℂ (F s) ∧ ∀ φ : N →ₗ[ℂ] N, (∀ X : N, ((φ X : N) : Matrix (Fin n) (Fin n) ℂ) = f * (X : Matrix (Fin n) (Fin n) ℂ) * g) → ‖LinearMap.det φ‖ = ∏ s ∈ Finset.range r, detOn f (F s) ^ Module.finrank ℂ (F (s + 1)) / detOn f (F (s + 1)) ^ Module.finrank ℂ (F s) := by
  first | exact @GlobalTheory.FlagModulus.flag_finrank_det | exact GlobalTheory.FlagModulus.flag_finrank_det | (intros; apply GlobalTheory.FlagModulus.flag_finrank_det <;> assumption)
