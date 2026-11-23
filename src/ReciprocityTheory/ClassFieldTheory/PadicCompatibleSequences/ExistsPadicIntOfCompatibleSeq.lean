module

public import Mathlib.Basic.Finite.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Functor.OfSequence
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Preorder

@[expose] public section

noncomputable section

namespace ReciprocityTheory.DiscreteGroups.PeuVal

open CategoryTheory

theorem exists_compatible_seq {Y : ℕ → Type*} (T : ∀ r, Set (Y r)) (φ : ∀ r, Y (r + 1) → Y r)
    (hne : ∀ r, (T r).Nonempty) (hfin : ∀ r, (T r).Finite) (hφ : ∀ r, ∀ f ∈ T (r + 1), φ r f ∈ T r) :
    ∃ f : ∀ r, Y r, (∀ r, f r ∈ T r) ∧ ∀ r, φ r (f (r + 1)) = f r := by
  let F : ℕᵒᵖ ⥤ Type _ := Functor.ofOpSequence (X := fun r => ↥(T r))
    (fun r => ↾fun f => ⟨φ r f.1, hφ r f.1 f.2⟩)
  have : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => (hfin j.unop).to_subtype
  have : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => (hne j.unop).to_subtype
  obtain ⟨u, hu⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun r => (u ⟨r⟩).1, fun r => (u ⟨r⟩).2, fun r => ?_⟩
  have h := hu (homOfLE (Nat.le_add_right r 1)).op
  rw [Functor.ofOpSequence_map_homOfLE_succ] at h
  exact congrArg Subtype.val h

end ReciprocityTheory.DiscreteGroups.PeuVal
