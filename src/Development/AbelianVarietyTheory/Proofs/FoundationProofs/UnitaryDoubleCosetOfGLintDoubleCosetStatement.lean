module

public import Formalism.SatakeDualWeyl.StatementF
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetOfGLintDoubleCoset
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

@[expose] public section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

theorem _root_.GlobalTheory.T.unitaryDoubleCoset_of_GLintDoubleCoset : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (g g' : GU σ n) (a b : GL (Fin n) L), a ∈ GLint (Fin n) (intL L) → b ∈ GLint (Fin n) (intL L) → (g' : GL (Fin n) L) = a * g * b → ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g' = k₁ * g * k₂ := by
  first | exact @GlobalTheory.UnramDoubleCoset.doubleCoset_GU_of_GL | exact GlobalTheory.UnramDoubleCoset.doubleCoset_GU_of_GL | (intros; apply GlobalTheory.UnramDoubleCoset.doubleCoset_GU_of_GL <;> assumption)
