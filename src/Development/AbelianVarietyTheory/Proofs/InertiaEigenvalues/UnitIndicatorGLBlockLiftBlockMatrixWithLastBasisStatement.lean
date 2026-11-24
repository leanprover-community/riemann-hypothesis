module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorGLBlockLiftBlockMatrixWithLastBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.unitIndicatorGLBlock_liftBlockMatrixWithLastBasis : ∀ (F : Type) [NormedField F] (r : ℕ) (Z : Gl r F) (μ l : F), ‖μ‖ ≤ 1 → unitG (r + 1) F (GlobalTheory.JR.Step.lift Z μ l) = (if ‖l‖ ≤ 1 then 1 else 0) * unitG r F Z := by
  first | exact @GlobalTheory.JR.UnitGLift.unitG_lift | exact GlobalTheory.JR.UnitGLift.unitG_lift | (intros; apply GlobalTheory.JR.UnitGLift.unitG_lift <;> assumption)
