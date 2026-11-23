module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
public import Mathlib.Algebra.MvPolynomial.Variables
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupOperatorDepthMulDisjointColumns
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtOrderProdSub

@[expose] public section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

theorem _root_.GlobalTheory.T.formalGroupOperatorDepth_mul_disjoint_columns : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (κ : Type) [Fintype κ] [DecidableEq κ] (d : κ → ℕ) (G : ∀ b, LogFGL v (d b)) (ι : κ → Type) [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (S : Set κ) (P Q : MvPolynomial (Σ b, ι b) C), (∀ x ∈ P.vars, x.1 ∈ S) → (∀ x ∈ Q.vars, x.1 ∉ S) → depth G u (P * Q) = depth G u P + depth G u Q := by
  first | exact @GlobalTheory.FGDepth.depth_mul_of_disjoint_columns | exact GlobalTheory.FGDepth.depth_mul_of_disjoint_columns | (intros; apply GlobalTheory.FGDepth.depth_mul_of_disjoint_columns <;> assumption)
