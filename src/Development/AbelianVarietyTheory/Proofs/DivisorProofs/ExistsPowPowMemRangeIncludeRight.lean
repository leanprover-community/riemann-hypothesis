module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.PowerInRangeTensorRight

open TensorProduct

theorem exists_pow_pow_mem_range_includeRight (k K B : Type) [Field k] [Field K] [Algebra k K]
    [IsPurelyInseparable k K] [CommRing B] [Nontrivial B] [Algebra k B] (q : ℕ) [ExpChar k q]
    (z : TensorProduct k K B) :
    ∃ n : ℕ, z ^ q ^ n ∈
      AlgHom.range (Algebra.TensorProduct.includeRight : B →ₐ[k] TensorProduct k K B) := by
  rcases subsingleton_or_nontrivial (TensorProduct k K B) with hs | hnt
  · exact ⟨0, by rw [Subsingleton.elim (z ^ q ^ 0) 0]; exact zero_mem _⟩
  have : ExpChar (TensorProduct k K B) q :=
    expChar_of_injective_algebraMap (algebraMap k (TensorProduct k K B)).injective q
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul x b =>
    obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem k q x
    refine ⟨n, (AlgHom.mem_range _).mpr ⟨c • b ^ q ^ n, ?_⟩⟩
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_pow, ← hc,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨n1, h1⟩ := hx
    obtain ⟨n2, h2⟩ := hy
    refine ⟨n1 + n2, ?_⟩
    have e1 : x ^ q ^ (n1 + n2) = (x ^ q ^ n1) ^ q ^ n2 := by rw [pow_add, pow_mul]
    have e2 : y ^ q ^ (n1 + n2) = (y ^ q ^ n2) ^ q ^ n1 := by rw [pow_add, mul_comm, pow_mul]
    rw [add_pow_expChar_pow, e1, e2]
    exact add_mem (pow_mem h1 _) (pow_mem h2 _)

end GlobalTheory.PowerInRangeTensorRight
