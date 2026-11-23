module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia Module

theorem UpperTheory.card_global_euler_characteristic_rationals :
    GlobalEulerChar → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset Pl) (ρ : Representation (ZMod (l ^ 1)) (Gam Ω S) M),
            ContainsAbove S l → ContAction ρ → ∀ σ : Formalism.ConjugateSelfDual.G ℚ Ω, IsCC σ →
            Nat.card (H1 ρ) * Nat.card {m : M // ρ (toGS Ω _ σ) m = m} = Nat.card (H0 ρ) * Nat.card (H2 ρ) * Nat.card M := by
  intro hG Ω _ _ _ l _ _ M _ _ _ _ _ S ρ hS hρ σ hσ
  have h := hG ℚ Ω l 1 M S ρ Nat.one_pos hS hρ (fun _ => σ) (by
    intro w _
    obtain ⟨j, hj⟩ := hσ
    exact ⟨j, hj, Subsingleton.elim _ _⟩)
  have hc : NumberField.InfinitePlace.nrComplexPlaces ℚ = 0 :=
    NumberField.InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ)
  simp only [archH0Card, hc, pow_zero, mul_one, Module.finrank_self, pow_one] at h
  rw [Finset.prod_eq_single_of_mem Rat.infinitePlace
    (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact Rat.isReal_infinitePlace)
    (fun b _ hb => absurd (Subsingleton.elim b _) hb)] at h
  exact h.symm
