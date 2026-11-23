module

public import Formalism.FockGram.StatementFock
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset MvPolynomial

namespace Formalism.E

section
variable {R τ : Type*} [CommRing R] [StarRing R]

theorem fock_eq_sum_of_subset (f g : MvPolynomial τ R) (s : Finset (τ →₀ ℕ))
    (h : f.support ⊆ s) :
    fock f g = ∑ m ∈ s, f.coeff m * star (g.coeff m) * (Formalism.A.mfact m : R) := by
  classical
  unfold fock
  refine Finset.sum_subset h ?_
  intro m _ hm
  rw [MvPolynomial.mem_support_iff, not_not] at hm
  simp [hm]

theorem fock_add_left (f f' g : MvPolynomial τ R) : fock (f + f') g = fock f g + fock f' g := by
  classical
  rw [fock_eq_sum_of_subset (f + f') g (f.support ∪ f'.support) MvPolynomial.support_add,
    fock_eq_sum_of_subset f g (f.support ∪ f'.support) Finset.subset_union_left,
    fock_eq_sum_of_subset f' g (f.support ∪ f'.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun m _ => by rw [MvPolynomial.coeff_add]; ring)

end

end Formalism.E
