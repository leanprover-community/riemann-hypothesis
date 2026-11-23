module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockTriVecMulEqSinglePred
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigCongr

@[expose] public section

open GlobalTheory.FinGL GlobalTheory.FinGL.LeviWh Formalism.L2.DIV Module

theorem _root_.GlobalTheory.T.exists_blockTri_vecMul_eq_single_pred : ∀ (F : Type) [Field F] (r : ℕ) (b : Fin r → ℕ), Monotone b → ∀ (k k' : Fin r), k'.val + 1 = k.val → ∀ l : Fin r → F, l ≠ 0 → (∀ i, l i ≠ 0 → i < k ∧ b i = b k) → ∃ h : blockTri (κ := F) b, (∀ i j, ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → i < k ∧ j < k) ∧ Matrix.vecMul l ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = Pi.single k' 1 := by
  first | exact @GlobalTheory.FinGL.LeviWh.exists_blockTri_vecMul_eq_single | exact GlobalTheory.FinGL.LeviWh.exists_blockTri_vecMul_eq_single | (intros; apply GlobalTheory.FinGL.LeviWh.exists_blockTri_vecMul_eq_single <;> assumption)
