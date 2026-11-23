module

public import Formalism.LocalToGlobal.CharacterGerms.Interface
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsUnimodularMulEqNegOfIndependentModMaximal
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
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd

@[expose] public section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

theorem _root_.GlobalTheory.T.exists_unimodular_mul_eq_neg_of_independent_mod_maximal : ∀ (C : Type) [Field C] (V : VF C) (n n0 : ℕ) (Φ : Fin n → Fin n0 → C), (∀ b c, V.Ge 0 (Φ b c)) → IndepMod V (fun c b => Φ b c) → n0 ≤ n ∧ ∃ Y : Matrix (Fin n) (Fin n) C, (∀ b b', V.Ge 0 (Y b b')) ∧ V.v Y.det = 0 ∧ ∀ (b : Fin n) (c : Fin n0), b.val < n0 → ∑ b', Y b b' * Φ b' c = if b.val = c.val then -1 else 0 := by
  first | exact @GlobalTheory.exists_unimodular_mul_eq_neg_of_indepMod | exact GlobalTheory.exists_unimodular_mul_eq_neg_of_indepMod | (intros; apply GlobalTheory.exists_unimodular_mul_eq_neg_of_indepMod <;> assumption)
