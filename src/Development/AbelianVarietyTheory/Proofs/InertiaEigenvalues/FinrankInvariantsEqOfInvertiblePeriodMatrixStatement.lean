module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankInvariantsEqOfInvertiblePeriodMatrix
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

open TensorProduct Module

theorem _root_.GlobalTheory.T.finrank_invariants_eq_of_invertible_periodMatrix : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (B : Type) [CommRing B] [Nontrivial B] [Algebra F B] [Algebra E B] [IsScalarTower F E B] (G : Type) (act : G → B →+* B) (n : Type) [Fintype n] [DecidableEq n] (A : G → Matrix n n B), (∀ b : B, (∀ g, act g b = b) ↔ ∃ c : E, algebraMap E B c = b) → ∀ Q : GL n B, (∀ g, A g * (Q : Matrix n n B).map (act g) = Q) → ∀ W : Submodule F (n → B), (∀ x, x ∈ W ↔ ∀ g, (A g).mulVec (fun i => act g (x i)) = x) → finrank F ↥W = finrank F E * Fintype.card n := by
  first | exact @GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix | exact GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix | (intros; apply GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix <;> assumption)
