module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

namespace GlobalTheory.HatProductMembership

open NumberField Formalism.BasicNotions Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.FunObj.SqNum

theorem mul_mem_hat_mul {D : D7} {I J : Ideal (𝓞 D.host.E)} {x y : AE D}
    (hx : x ∈ hatId D I) (hy : y ∈ hatId D J) : x * y ∈ hatId D (I * J) := by
  unfold hatId at hx hy ⊢
  induction hx using AddSubgroup.closure_induction with
  | mem a ha =>
    obtain ⟨u, hu, s, hs, rfl⟩ := ha
    induction hy using AddSubgroup.closure_induction with
    | mem b hb =>
      obtain ⟨v, hv, t, ht, rfl⟩ := hb
      refine AddSubgroup.subset_closure
        ⟨u * v, Ideal.mul_mem_mul hu hv, s * t, (OhE D).mul_mem hs ht, ?_⟩
      have h : ((u * v : 𝓞 D.host.E) : D.host.E) = (u : D.host.E) * (v : D.host.E) := rfl
      rw [h, map_mul]
      ring
    | zero => rw [mul_zero]; exact zero_mem _
    | add b c _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | neg b _ h => rw [mul_neg]; exact neg_mem h
  | zero => rw [zero_mul]; exact zero_mem _
  | add a b _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | neg a _ h => rw [neg_mul]; exact neg_mem h

end GlobalTheory.HatProductMembership
