module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieAlgebraOfIsCutOutByRealMatrixAlgebra
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

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

theorem _root_.GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → (∀ X ∈ Submodule.span ℝ (Set.range E), ∀ t : ℝ, ∃ g ∈ S, uMat g = NormedSpace.exp ((t : ℂ) • X)) ∧ (∀ T : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), (∀ g ∈ S, uMat g - 1 ∈ T) → ∀ i, E i ∈ T) ∧ ∀ X : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.inG ε X → (∀ (t : ℝ) (g : Formalism.REAL.UJ ε), uMat g = NormedSpace.exp ((t : ℂ) • X) → g ∈ S) → X ∈ Submodule.span ℝ (Set.range E) := by
  first | exact @GlobalTheory.IwTangent.lie_algebra_of_isCut | exact GlobalTheory.IwTangent.lie_algebra_of_isCut | (intros; apply GlobalTheory.IwTangent.lie_algebra_of_isCut <;> assumption)
