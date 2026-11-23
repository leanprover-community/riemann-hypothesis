module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModerateGrowthOfFirstMinimumAndFlowBounds
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom

theorem _root_.GlobalTheory.T.moderate_growth_of_firstMinimum_and_flow_bounds : FlowMajSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (w : ℝ) (φ : Frame X.Ψ r → ℝ), 0 ≤ w → (∀ x ∈ X.dom, 0 ≤ φ x) → ThickBdd X φ → StepBound X w φ → ∃ C A : ℝ, ∀ x ∈ X.dom, φ x ≤ C * X.la1 x ^ (-(A * w)) := by
  first | exact @GlobalTheory.CuspDescent.moderate_of_stepBound | exact GlobalTheory.CuspDescent.moderate_of_stepBound | (intros; apply GlobalTheory.CuspDescent.moderate_of_stepBound <;> assumption)
