module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockProductIsomorphism
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivOfNeZeroMapIsotypicSumOfCopies
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

theorem _root_.GlobalTheory.T.equiv_of_ne_zero_map_isotypicSumOfCopies : ∀ (H : Type) [Group H] [Finite H] (V V' W W' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (τ : Representation ℂ H V) (τ' : Representation ℂ H V') (ρ : Representation ℂ H W) (ρ' : Representation ℂ H W'), ρ.IsIrreducible → ρ'.IsIrreducible → IsIsotypicOf τ ρ → IsIsotypicOf τ' ρ' → ∀ T : Representation.IntertwiningMap τ τ', T ≠ 0 → Nonempty (Representation.Equiv ρ ρ') := by
  first | exact @GlobalTheory.IsotypicMap.equiv_of_isotypic_map | exact GlobalTheory.IsotypicMap.equiv_of_isotypic_map | (intros; apply GlobalTheory.IsotypicMap.equiv_of_isotypic_map <;> assumption)
