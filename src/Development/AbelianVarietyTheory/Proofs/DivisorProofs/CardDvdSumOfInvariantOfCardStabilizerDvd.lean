module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.SetTheory.Cardinal.Finite
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.GroupAction.Quotient

@[expose] public section

namespace GlobalTheory

theorem card_dvd_sum_of_invariant_of_card_stabilizer_dvd (G X : Type) [AddGroup G] [Finite G]
    [Fintype X] [AddAction G X] (h : X → ℤ) (hinv : ∀ (g : G) (x : X), h (g +ᵥ x) = h x)
    (hdvd : ∀ x, (Nat.card (AddAction.stabilizer G x) : ℤ) ∣ h x) :
    (Nat.card G : ℤ) ∣ ∑ x, h x := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ)
    (g := fun x : X => (Quotient.mk (AddAction.orbitRel G X) x)) (f := h)]
  refine Finset.dvd_sum fun q _ => ?_
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  have hconst : ∀ y ∈ Finset.univ.filter
      (fun y : X => Quotient.mk (AddAction.orbitRel G X) y = Quotient.mk (AddAction.orbitRel G X) x),
      h y = h x := by
    intro y hy
    have hy' := Quotient.exact (Finset.mem_filter.mp hy).2
    obtain ⟨g, rfl⟩ : y ∈ AddAction.orbit G x := AddAction.orbitRel_apply.mp hy'
    exact hinv g x
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter
      (fun y : X => Quotient.mk (AddAction.orbitRel G X) y
        = Quotient.mk (AddAction.orbitRel G X) x)).card = Nat.card (AddAction.orbit G x) := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Quotient.eq]
    exact AddAction.orbitRel_apply
  have hG : Nat.card G = Nat.card (AddAction.orbit G x) * Nat.card (AddAction.stabilizer G x) := by
    rw [Nat.card_congr (AddAction.orbitEquivQuotientStabilizer G x)]
    exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  rw [hcard, hG, Nat.cast_mul]
  exact mul_dvd_mul_left _ (hdvd x)

end GlobalTheory
