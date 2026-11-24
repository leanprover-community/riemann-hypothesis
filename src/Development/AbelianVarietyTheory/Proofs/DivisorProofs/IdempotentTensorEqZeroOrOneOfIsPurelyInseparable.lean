module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowPowMemRangeIncludeRight
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory

theorem pow_mem_range_includeRight_of_isPurelyInseparable (k K B : Type) [Field k] [Field K]
    [Algebra k K] [IsPurelyInseparable k K] [CommRing B] [Nontrivial B] [Algebra k B]
    (q : ℕ) [ExpChar k q] (z : K ⊗[k] B) :
    ∃ n : ℕ, z ^ q ^ n ∈
      (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B).range := by
  first
  | exact @_root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight
  | exact _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight
  | (apply _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight ..)

theorem idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable (k K B : Type) [Field k] [Field K]
    [Algebra k K] [IsPurelyInseparable k K] [CommRing B] [IsLocalRing B] [Algebra k B]
    (e : K ⊗[k] B) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective
  obtain ⟨n, b, hb⟩ :=
    pow_mem_range_includeRight_of_isPurelyInseparable k K B (ringExpChar k) e
  have hpos : ringExpChar k ^ n ≠ 0 := (pow_pos (expChar_pos k _) n).ne'
  have h1 : e ^ (ringExpChar k ^ n) = e := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos
    rw [hm]; exact he.pow_succ_eq m
  rw [h1] at hb
  have hb' : (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B) b = e := hb
  have hbi : b * b = b := by
    apply hinj
    rw [map_mul, hb']; exact he
  rcases isUnit_or_isUnit_one_sub_self b with hu | hu
  · right
    have : b = 1 := hu.mul_left_cancel (by rw [hbi, mul_one])
    rw [← hb', this, map_one]
  · left
    have : b = 0 := hu.mul_left_cancel (by rw [sub_mul, hbi, one_mul, sub_self, mul_zero])
    rw [← hb', this, map_zero]

end GlobalTheory
