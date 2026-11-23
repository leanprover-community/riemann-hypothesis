module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormEqOwnRealLieSmoothingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingGrowthExponentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordEqSmoothingOfReproducedStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.ReductionBlock
import GroundTheory.GlobalFields.KummerTheory.LocalIndex

@[expose] public section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

theorem GlobalTheory.AutGrowth.uniform_growth_of_autForm : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E]
    [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → ∃ N : ℕ, ∀ l : List (Lie E a),
    ∃ C : ℝ, ∀ y, ‖((l.map (lie E a)).prod φ).1 (infGL E a y)‖ ≤ C * height y ^ N := by
  intro hP E _ _ _ a φ hφ
  let ν : Measure (Lie E a) := Measure.addHaar
  obtain ⟨C, N, hC⟩ := hφ.growth 1
  simp only [one_mul] at hC
  obtain ⟨α, hα, hconv⟩ := GlobalTheory.T.automorphicForm_eq_own_realLieSmoothing hP E a ν φ hφ
  refine ⟨N, fun l => ?_⟩
  obtain ⟨β, hβ, hw⟩ := GlobalTheory.T.exists_test_word_eq_smoothing E a ν α hα φ hconv l
  obtain ⟨C', hC'⟩ := GlobalTheory.T.exists_smoothing_norm_le_height_pow E a ν β hβ φ.1 C N hC
  exact ⟨C', fun y => by rw [hw]; exact hC' y⟩
