module

public import Mathlib.NumberTheory.Padics.RingHoms
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.AlgebraMapToZMod

theorem algebraMap_toZMod_eq {l : ℕ} [inst : Fact (Nat.Prime l)] {R : Type} [inst_1 : Field R]
    [inst_2 : Algebra (ZMod l) R] (f : ℤ_[l] →+* R) (hf : f (l : ℤ_[l]) = 0) (x : ℤ_[l]) :
    algebraMap (ZMod l) R (PadicInt.toZMod x) = f x := by
  haveI : NeZero l := ⟨(Fact.out : Nat.Prime l).ne_zero⟩
  have h := PadicInt.toZMod_spec x
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨y, hy⟩ := h
  set z : ZMod l := PadicInt.toZMod x with hz
  have hc : (ZMod.cast z : ℤ_[l]) = ((z.val : ℕ) : ℤ_[l]) := (ZMod.natCast_val z).symm
  have hx : x = y * (l : ℤ_[l]) + ((z.val : ℕ) : ℤ_[l]) := by
    rw [hy, hc]; ring
  have h1 : f x = ((z.val : ℕ) : R) := by
    conv_lhs => rw [hx]
    rw [map_add (f := _), map_mul, hf, mul_zero, zero_add, map_natCast]
  have h2 : algebraMap (ZMod l) R z = ((z.val : ℕ) : R) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    rw [map_natCast]
  rw [h1, h2]

end GlobalTheory.AlgebraMapToZMod
