module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockProductIsomorphism
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermOfBlockSizeBijection
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions

@[expose] public section

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

theorem _root_.GlobalTheory.T.exists_perm_of_blockSize_bijection : ∀ (r : ℕ) (b b' : Fin r → ℕ) (R : ℕ → ℕ → Prop), (∀ c ∈ Set.range b, ∃! c', c' ∈ Set.range b' ∧ R c c') → (∀ c' ∈ Set.range b', ∃! c, c ∈ Set.range b ∧ R c c') → (∀ c ∈ Set.range b, ∀ c' ∈ Set.range b', R c c' → (block b c).card = (block b' c').card) → ∃ w : Equiv.Perm (Fin r), (∀ i, R (b i) (b' (w i))) ∧ ∀ i j : Fin r, b i = b j ↔ b' (w i) = b' (w j) := by
  first | exact @GlobalTheory.exists_perm_of_block_bijection | exact GlobalTheory.exists_perm_of_block_bijection | (intros; apply GlobalTheory.exists_perm_of_block_bijection <;> assumption)
