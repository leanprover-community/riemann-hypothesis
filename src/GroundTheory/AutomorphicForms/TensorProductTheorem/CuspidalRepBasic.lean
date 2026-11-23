module

public import GroundTheory.AutomorphicForms.TensorProductTheorem.CuspidalRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Automorphic

namespace AutomorphicForm

namespace CuspidalAutomorphicRepresentation

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem carrier_ne_bot (π : CuspidalAutomorphicRepresentation K n) : π.carrier ≠ ⊥ := by
  intro h
  have hirr : IsSimpleOrder (Subrepresentation π.toModule.fullRep) := π.isIrreducible
  apply (bot_ne_top : (⊥ : Subrepresentation π.toModule.fullRep) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  show (⊥ : Submodule ℂ π.carrier) = ⊤
  refine eq_top_iff.2 fun x _ => ?_
  have hx : (x : cuspForms K n) ∈ (⊥ : Submodule ℂ (cuspForms K n)) := h ▸ x.2
  rw [Submodule.mem_bot] at hx ⊢
  exact Subtype.ext hx

theorem exists_mem_ne_zero (π : CuspidalAutomorphicRepresentation K n) : ∃ φ ∈ π.carrier, φ ≠ 0 :=
  Submodule.exists_mem_ne_zero_of_ne_bot π.carrier_ne_bot

end CuspidalAutomorphicRepresentation

end AutomorphicForm

end GroundTheory.Automorphic
