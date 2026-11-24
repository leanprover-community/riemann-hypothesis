module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInvertibleFamilyEvalSpan
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

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_invertibleFamily_eval_span : ∀ (ι : Type) [Fintype ι] (a : ℕ) (lam : ι → DomWeight a) (n : ι → ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (T : PY ι a →ₗ[ℂ] W), ∃ (m : ℕ) (y : Fin m → ι → Matrix (Fin a) (Fin a) ℂ) (P : Fin m → W), (∀ j, IsInv (y j)) ∧ ∀ F ∈ Vn lam n, T F = ∑ j, evalAt (y j) F • P j := by
  first | exact @GlobalTheory.KJInf.exists_evalAt_span | exact GlobalTheory.KJInf.exists_evalAt_span | (intros; apply GlobalTheory.KJInf.exists_evalAt_span <;> assumption)
