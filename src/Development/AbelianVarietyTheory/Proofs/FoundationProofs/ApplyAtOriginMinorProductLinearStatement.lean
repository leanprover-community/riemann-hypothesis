module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApplyAtOriginMinorProductLinear
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

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.applyAtOrigin_minorProduct_linear : ∀ (D : D7) (a d : ℕ) (n : D.what₂.Tau → ℕ) (G : VC D a d → ℂ), Differentiable ℂ G → (∀ (u : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ) (t : Tup D a d n), GL3Theta.applyAt0 D (minorPol D t) (fun z => G (fun τ => (Matrix.of (z τ) * u τ : Matrix _ _ ℂ))) = (∏ τ, (u τ).det ^ n τ) * GL3Theta.applyAt0 D (minorPol D t) G) ∧ (∀ (u : D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ), (∀ τ, u τ ∈ Matrix.unitaryGroup (Fin d) ℂ) → ∑ t : Tup D a d n, ‖GL3Theta.applyAt0 D (minorPol D t) (fun z => G (fun τ => (u τ * Matrix.of (z τ) : Matrix _ _ ℂ)))‖ ^ 2 = ∑ t : Tup D a d n, ‖GL3Theta.applyAt0 D (minorPol D t) G‖ ^ 2) ∧ (∀ (c : ℂ) P, GL3Theta.applyAt0 D P (c • G) = c * GL3Theta.applyAt0 D P G) ∧ ∀ G' P, Differentiable ℂ G' → GL3Theta.applyAt0 D P (G + G') = GL3Theta.applyAt0 D P G + GL3Theta.applyAt0 D P G' := by
  first | exact @GlobalTheory.NormSum.applyAt0_minorPol_linear | exact GlobalTheory.NormSum.applyAt0_minorPol_linear | (intros; apply GlobalTheory.NormSum.applyAt0_minorPol_linear <;> assumption)
