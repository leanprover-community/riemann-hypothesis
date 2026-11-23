module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
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
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Associated

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Finset

noncomputable section

namespace RootsOfUnityValuation

variable {A : Type*} [CommRing A] [IsDomain A]


omit [IsDomain A] in
theorem associated_sub_comm (a b : A) : Associated (a - b) (b - a) :=
  ⟨-1, by simp⟩

theorem one_sub_pow_associated {l : ℕ} (hl : l.Prime) {ζ : A} (hζ : IsPrimitiveRoot ζ l) :
    Associated ((1 - ζ) ^ (l - 1)) (l : A) := by
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, (Nat.sub_add_cancel hl.one_lt.le).symm⟩
  have h := hζ.prod_one_sub_pow_eq_order
  have h1 : (1 - ζ) ^ n = ∏ _k ∈ range n, (1 - ζ) := by simp
  rw [Nat.add_sub_cancel, h1]
  push_cast
  rw [← h]
  refine Associated.prod _ _ _ fun k hk => ?_
  have hcop : (k + 1).Coprime (n + 1) :=
    (Nat.coprime_of_lt_prime (by omega) (by simpa using Finset.mem_range.1 hk) hl).symm
  exact (associated_sub_comm 1 ζ).trans
    ((hζ.associated_sub_one_pow_sub_one_of_coprime hcop).trans (associated_sub_comm _ _))

end RootsOfUnityValuation

end

end GroundTheory.Heights₂.Heights
