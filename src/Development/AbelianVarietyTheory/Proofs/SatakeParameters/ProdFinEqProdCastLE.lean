module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
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
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace GlobalTheory.ProdFinCastLE

theorem prod_fin_eq_prod_castLE {a b : ℕ} {M : Type} [CommMonoid M] (h : a ≤ b) (f : Fin b → M)
    (hf : ∀ r : Fin b, a ≤ (r : ℕ) → f r = 1) :
    ∏ r : Fin b, f r = ∏ r : Fin a, f (Fin.castLE h r) := by
  symm
  rw [show (∏ r : Fin a, f (Fin.castLE h r)) =
      ∏ x ∈ Finset.univ.map ⟨Fin.castLE h, Fin.castLE_injective h⟩, f x by
    rw [Finset.prod_map]
    rfl]
  refine Finset.prod_subset (Finset.subset_univ _) fun x _ hx => hf x ?_
  by_contra hlt
  push Not at hlt
  exact hx (Finset.mem_map.2 ⟨⟨x, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

end GlobalTheory.ProdFinCastLE
