module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharacterEqInducedOfImprimitivitySystem
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

@[expose] public section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.character_eq_induced_of_imprimitivity_system : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (ρ : Representation L G V) (T : Subgroup G) (e : Module.End L V), ρ.IsIrreducible → e ≠ 0 → e * e = e → (∀ t ∈ T, ρ t * e = e * ρ t) → (∀ g ∉ T, e * ρ g * e = 0) → ∃ ψ : T → L, IsChar L L ψ ∧ ∀ g, ρ.character g = ind T ψ g := by
  first | exact @GlobalTheory.BI.character_eq_ind_of_imprimitive | exact GlobalTheory.BI.character_eq_ind_of_imprimitive | (intros; apply GlobalTheory.BI.character_eq_ind_of_imprimitive <;> assumption)
