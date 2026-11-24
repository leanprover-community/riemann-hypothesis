module

public import Mathlib.Algebra.Algebra.Hom
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

@[expose] public section

noncomputable section

namespace GlobalTheory.LKTorus

variable (k : Type) [Field k] {A : Type} [CommRing A] [Algebra k A]

def simT (c : A →ₐ[k] A) : Subgroup Aˣ where
  carrier := {x | ∃ t : kˣ, (x : A) * c x = algebraMap k A t}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro x y ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s * t, ?_⟩
    simp only [Units.val_mul, map_mul]
    rw [show (x : A) * y * (c x * c y) = (x * c x) * (y * c y) by ring, hs, ht]
  inv_mem' := by
    rintro x ⟨s, hs⟩
    refine ⟨s⁻¹, ?_⟩
    have h1 : ((x⁻¹ : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A) * algebraMap k A s = 1 := by
      rw [← hs, show ((x⁻¹ : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A) * ((x : A) * c x)
          = (((x⁻¹ : Aˣ) : A) * x) * c (((x⁻¹ : Aˣ) : A) * x) by rw [map_mul]; ring]
      simp
    calc ((x⁻¹ : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A)
        = ((x⁻¹ : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A) * (algebraMap k A s * algebraMap k A ((s⁻¹ : kˣ) : k)) := by
          rw [← map_mul, Units.mul_inv, map_one, mul_one]
      _ = algebraMap k A ((s⁻¹ : kˣ) : k) := by rw [← mul_assoc, h1, one_mul]

end GlobalTheory.LKTorus
