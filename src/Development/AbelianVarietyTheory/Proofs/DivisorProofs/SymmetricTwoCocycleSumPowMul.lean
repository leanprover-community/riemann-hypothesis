module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace GlobalTheory.TwoCocycle

theorem interchange {Γ D : Type} [CommGroup Γ] [AddCommGroup D] (c : Γ → Γ → D)
    (hs : ∀ x y, c x y = c y x)
    (hc : ∀ x y z, c y z - c (x * y) z + c x (y * z) - c x y = 0) (a b x y : Γ) :
    c (a * b) (x * y) + c x y + c a b = c a x + c b y + c (a * x) (b * y) := by
  have h1 := hc a b (x * y)
  have h2 := hc b y x
  have h3 := hc a x (b * y)
  rw [mul_comm y x, hs y x, hs (b * y) x] at h2
  rw [mul_left_comm x b y] at h3
  linear_combination (norm := abel) h2 + h3 - h1

theorem sum_pow_mul (Γ D : Type) [CommGroup Γ] [AddCommGroup D] (c : Γ → Γ → D)
    (hs : ∀ x y, c x y = c y x)
    (hc : ∀ x y z, c y z - c (x * y) z + c x (y * z) - c x y = 0) (n : ℕ) (x y : Γ) :
    ∑ i ∈ Finset.range n, c ((x * y) ^ i) (x * y) + n • c x y =
      ∑ i ∈ Finset.range n, c (x ^ i) x + ∑ i ∈ Finset.range n, c (y ^ i) y
        + c (x ^ n) (y ^ n) - c 1 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := interchange c hs hc (x ^ n) (y ^ n) x y
    rw [← mul_pow] at h
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, succ_nsmul,
      pow_succ x, pow_succ y]
    linear_combination (norm := abel) ih + h

end GlobalTheory.TwoCocycle
