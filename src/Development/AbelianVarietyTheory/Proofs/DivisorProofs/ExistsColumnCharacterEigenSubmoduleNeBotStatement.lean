module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigCongr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColumnCharacterEigenSubmoduleNeBot
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

open GlobalTheory.FinGL GlobalTheory.FinGL.LeviWh Formalism.L2.DIV Module

theorem _root_.GlobalTheory.T.exists_columnCharacter_eigenSubmodule_ne_bot : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), Monotone b → (∀ p : blockTri (κ := F) b, (∀ i j, b i = b j → ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) → σ p = 1) → ∀ k : Fin r, eig σ (colSet F b (k.val + 1)) (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F))) ≠ ⊥ → ∃ l : Fin r → F, (∀ i, l i ≠ 0 → i < k ∧ b i = b k) ∧ eig σ (colSet F b k.val) (colChar ψ b k l) ≠ ⊥ := by
  first | exact @GlobalTheory.FinGL.LeviWh.exists_colChar_eig_ne_bot | exact GlobalTheory.FinGL.LeviWh.exists_colChar_eig_ne_bot | (intros; apply GlobalTheory.FinGL.LeviWh.exists_colChar_eig_ne_bot <;> assumption)
