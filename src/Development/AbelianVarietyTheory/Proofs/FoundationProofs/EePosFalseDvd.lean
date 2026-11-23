module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Integral
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois.UpSplit

open GlobalTheory.KummerEisensteinGalois

variable {K : Type*} [Field K] [CharZero K]

theorem cmul_vp_vp (p : ℕ) (hp : 0 < p) (f g : ℕ → K) (r : ℕ) :
    cmul (vp p f) (vp p g) (p * r) = cmul f g r := by
  unfold cmul
  symm
  have h1 : ∀ j ∈ range (r + 1), f j * g (r - j) = vp p f (p * j) * vp p g (p * r - p * j) := by
    intro j _
    simp only [vp, dvd_mul_right, if_true, ← Nat.mul_sub, Nat.mul_div_cancel_left _ hp]
  rw [sum_congr rfl h1, ← sum_image (f := fun i => vp p f i * vp p g (p * r - i)) (g := fun j => p * j)
    (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp h)]
  apply sum_subset
  · intro i hi
    simp only [mem_image, mem_range] at hi ⊢
    obtain ⟨j, hj, rfl⟩ := hi
    have : j ≤ r := by omega
    have := Nat.mul_le_mul_left p this
    omega
  · intro i hi hni
    simp only [mem_image, mem_range, not_exists, not_and] at hi hni
    by_cases hpi : p ∣ i
    · obtain ⟨j, rfl⟩ := hpi
      exact absurd rfl (hni j (by
        have : p * j ≤ p * r := by omega
        have := Nat.le_of_mul_le_mul_left this hp
        omega))
    · simp [vp, hpi]

end GlobalTheory.KummerEisensteinGalois.UpSplit

namespace GlobalTheory.KummerEisensteinGalois


end GlobalTheory.KummerEisensteinGalois
