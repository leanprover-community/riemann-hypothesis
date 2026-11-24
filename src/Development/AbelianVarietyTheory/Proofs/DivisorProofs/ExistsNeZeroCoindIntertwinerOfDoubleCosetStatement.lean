module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Coinduced
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroCoindIntertwinerOfDoubleCoset
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockProductIsomorphism
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Formalism.LocalToGlobal.Divisibility.DefGroup

@[expose] public section

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

theorem _root_.GlobalTheory.T.exists_ne_zero_coindIntertwiner_of_doubleCoset : ∀ (G : Type) [Group G] [Finite G] (P P' : Subgroup G) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (σ : Representation ℂ P V) (σ' : Representation ℂ P' V') (x : G) (T : V →ₗ[ℂ] V'), T ≠ 0 → (∀ (p : P) (p' : P'), (p' : G) * x = x * (p : G) → σ' p' ∘ₗ T = T ∘ₗ σ p) → ∃ Φ : Representation.IntertwiningMap (Representation.coind P.subtype σ) (Representation.coind P'.subtype σ'), Φ ≠ 0 := by
  first | exact @GlobalTheory.exists_ne_zero_intertwiningMap_coind_of_doubleCoset | exact GlobalTheory.exists_ne_zero_intertwiningMap_coind_of_doubleCoset | (intros; apply GlobalTheory.exists_ne_zero_intertwiningMap_coind_of_doubleCoset <;> assumption)
