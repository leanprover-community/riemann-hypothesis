module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockProductIsomorphism
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroIntertwiningOfCommutingIsotypicFacto
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions

@[expose] public section

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

theorem _root_.GlobalTheory.T.exists_ne_zero_intertwining_of_commuting_isotypicFactors : ∀ (M : Type) [Group M] [Finite M] (ι : Type) [Finite ι] (H : ι → Type) [∀ c, Group (H c)] [∀ c, Finite (H c)] (f : ∀ c, H c →* M), (⨆ c, (f c).range) = ⊤ → (∀ c c', c ≠ c' → ∀ (x : H c) (y : H c'), Commute (f c x) (f c' y)) → ∀ (W : ι → Type) [∀ c, AddCommGroup (W c)] [∀ c, Module ℂ (W c)] (ρ : ∀ c, Representation ℂ (H c) (W c)), (∀ c, (ρ c).IsIrreducible) → ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] [Nontrivial V'] (τ : Representation ℂ M V) (τ' : Representation ℂ M V'), (∀ c, IsIsotypicOf (show Representation ℂ (H c) V from τ.comp (f c)) (ρ c)) → (∀ c, IsIsotypicOf (show Representation ℂ (H c) V' from τ'.comp (f c)) (ρ c)) → ∃ T : Representation.IntertwiningMap τ τ', T ≠ 0 := by
  first | exact @GlobalTheory.IsotypicFactors.exists_intertwining_ne_zero | exact GlobalTheory.IsotypicFactors.exists_intertwining_ne_zero | (intros; apply GlobalTheory.IsotypicFactors.exists_intertwining_ne_zero <;> assumption)
