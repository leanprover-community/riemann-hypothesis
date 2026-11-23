module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PatternGroupSubgroupOrderCharacter
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

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem _root_.GlobalTheory.T.patternGroup_subgroup_order_character : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ) (Φ : Fin N → Fin N → Prop), (∀ a, ¬ Φ a a) → (∀ a b c, Φ a b → Φ b c → Φ a c) → (∃ H : Subgroup (Gn g N), (∀ x, x ∈ H ↔ InPat Φ (x : Mt g N)) ∧ Nat.card H = g ^ (Finset.univ.filter fun p : Fin N × Fin N => Φ p.1 p.2).card) ∧ (∀ M : Mt g N, InPat Φ M → IsUnit M) ∧ ∀ E : Fin N → Fin N → Prop, (∀ a b c, Φ a b → Φ b c → ¬ E a c) → (∀ a, ¬ E a a) → ∀ M M' : Mt g N, InPat Φ M → InPat Φ M' → sumAt E (M * M') = sumAt E M + sumAt E M' := by
  first | exact @GlobalTheory.GLm.Pattern.pattern_group | exact GlobalTheory.GLm.Pattern.pattern_group | (intros; apply GlobalTheory.GLm.Pattern.pattern_group <;> assumption)
