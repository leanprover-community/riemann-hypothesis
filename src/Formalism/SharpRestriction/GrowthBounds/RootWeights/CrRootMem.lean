module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.V2repExistsHwv
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees

@[expose] public section

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ}

def cr_Pos (n : ℕ) : AddSubmonoid (Fin n → ℤ) :=
  AddSubmonoid.closure {β | ∃ a b : Fin n, a < b ∧ β = rootW a b}

def cr_h (ν : Fin n → ℤ) : ℤ := ∑ a : Fin n, ∑ b : Fin n, if a < b then ν a - ν b else 0

def cr_c (ν : Fin n → ℤ) : ℤ := ∑ a, ν a ^ 2 + cr_h ν

theorem cr_ht_add (x y : Fin n → ℤ) : weightHeight' (x + y) = weightHeight' x + weightHeight' y := by
  simp only [weightHeight', Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem cr_ht_zero : weightHeight' (0 : Fin n → ℤ) = 0 := by simp [weightHeight']

theorem cr_ht_root (a b : Fin n) (h : a < b) : 0 < weightHeight' (rootW a b) := by
  have := v2rep_ht_root (0 : Fin n → ℤ) a b h
  rwa [zero_add, cr_ht_zero] at this

theorem cr_h_eq (ν : Fin n → ℤ) : cr_h ν = ∑ a : Fin n, ((n : ℤ) - 1 - 2 * (a.val : ℤ)) * ν a := by
  classical
  have h1 : ∀ a : Fin n, (∑ b : Fin n, if a < b then ν a else 0) = ((n : ℤ) - 1 - (a.val : ℤ)) * ν a := by
    intro a
    rw [← Finset.sum_filter, Finset.sum_const]
    have : (Finset.univ.filter fun b : Fin n => a < b) = Finset.Ioi a := by ext b; simp
    rw [this, Fin.card_Ioi, nsmul_eq_mul]
    have ha := a.isLt
    congr 1
    omega
  have h2 : ∀ b : Fin n, (∑ a : Fin n, if a < b then ν b else 0) = (b.val : ℤ) * ν b := by
    intro b
    rw [← Finset.sum_filter, Finset.sum_const]
    have : (Finset.univ.filter fun a : Fin n => a < b) = Finset.Iio b := by ext a; simp
    rw [this, Fin.card_Iio, nsmul_eq_mul]
  have h3 : cr_h ν = (∑ a : Fin n, ∑ b : Fin n, if a < b then ν a else 0) -
      ∑ a : Fin n, ∑ b : Fin n, if a < b then ν b else 0 := by
    rw [cr_h, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  rw [h3, Finset.sum_comm (f := fun a b : Fin n => if a < b then ν b else 0), Finset.sum_congr rfl fun a _ => h1 a,
    Finset.sum_congr rfl fun b _ => h2 b, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem cr_h_ht (ν : Fin n → ℤ) : cr_h ν = ((n : ℤ) - 1) * ∑ a, ν a + 2 * weightHeight' ν := by
  rw [cr_h_eq, weightHeight', Finset.mul_sum, mul_neg, Finset.mul_sum, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem cr_Pos_sum {β : Fin n → ℤ} (h : β ∈ cr_Pos n) : ∑ a, β a = 0 := by
  classical
  induction h using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, b, _, rfl⟩ := hx
    simp [rootW, Finset.sum_sub_distrib]
  | zero => simp
  | add x y _ _ hx hy => simp [Finset.sum_add_distrib, hx, hy]

theorem cr_Pos_ht {β : Fin n → ℤ} (h : β ∈ cr_Pos n) : 0 ≤ weightHeight' β := by
  induction h using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, b, hab, rfl⟩ := hx
    exact (cr_ht_root a b hab).le
  | zero => rw [cr_ht_zero]
  | add x y _ _ hx hy => rw [cr_ht_add]; omega

theorem cr_Pos_pair {ν β : Fin n → ℤ} (hν : Dominant ν) (h : β ∈ cr_Pos n) : 0 ≤ ∑ a, ν a * β a := by
  classical
  induction h using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, b, hab, rfl⟩ := hx
    have : ∑ c, ν c * rootW a b c = ν a - ν b := by
      simp [rootW, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
    rw [this]
    have := hν hab.le
    omega
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    omega

theorem cr_root_mem (a b : Fin n) (h : a < b) : rootW a b ∈ cr_Pos n :=
  AddSubmonoid.subset_closure ⟨a, b, h, rfl⟩

theorem cr_c_lt {lam mu : Fin n → ℤ} (hl : Dominant lam) (hm : Dominant mu) (h : lam - mu ∈ cr_Pos n)
    (hpos : 0 < weightHeight' (lam - mu)) : cr_c mu < cr_c lam := by
  have h1 := cr_Pos_pair hl h
  have h2 := cr_Pos_pair hm h
  have h3 := cr_Pos_sum h
  have e1 : cr_h lam - cr_h mu = 2 * weightHeight' (lam - mu) := by
    have hh : cr_h (lam - mu) = 2 * weightHeight' (lam - mu) := by rw [cr_h_ht, h3]; ring
    rw [← hh, cr_h_eq, cr_h_eq, cr_h_eq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.sub_apply]
    ring
  have e2 : ∑ a, lam a ^ 2 - ∑ a, mu a ^ 2 = ∑ a, lam a * (lam - mu) a + ∑ a, mu a * (lam - mu) a := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.sub_apply]
    ring
  unfold cr_c
  omega

end Formalism.MainNotions.G.GLWeightTheory
