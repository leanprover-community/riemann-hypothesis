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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Mathlib.Algebra.BigOperators.Associated

@[expose] public section

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem primRoot_sub_one_pow_associated {O : Type*} [CommRing O] [IsDomain O] {p : ℕ}
    (hp : p.Prime) {ζ : O} (hζ : IsPrimitiveRoot ζ p) :
    Associated ((ζ - 1) ^ (p - 1)) (p : O) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have h := hζ.prod_one_sub_pow_eq_order
  have h2 : Associated (∏ _k ∈ Finset.range n, (ζ - 1)) (∏ k ∈ Finset.range n, (1 - ζ ^ (k + 1))) := by
    refine Associated.prod _ _ _ fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    have hc : (k + 1).Coprime (n + 1) :=
      (Nat.coprime_of_lt_prime (by omega) (by omega) hp).symm
    have := hζ.associated_sub_one_pow_sub_one_of_coprime hc
    rw [← neg_sub (ζ ^ (k + 1)) 1]
    exact this.neg_right
  rw [h, Finset.prod_const, Finset.card_range] at h2
  simpa using h2

end GlobalTheory.CompanionTheory.Ar.HT
