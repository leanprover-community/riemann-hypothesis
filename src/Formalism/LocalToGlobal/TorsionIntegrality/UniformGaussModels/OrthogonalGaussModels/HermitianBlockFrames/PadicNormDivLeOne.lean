module

public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.FrobStep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

theorem sq_conj (d : ℕ) : conj (sq d) = -sq d := by
  simp [sq, Complex.conj_ofReal]

theorem sq_mul_sq (d : ℕ) : sq d * sq d = -(d : ℂ) := by
  rw [← pow_two]
  have h : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  rw [sq, mul_pow, h, Complex.I_sq]; ring

def Kc (d : ℕ) (hd : 0 < d) : Subfield ℂ where
  carrier := {z | ∃ q₁ q₂ : ℚ, z = q₁ + q₂ * sq d}
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, e, rfl⟩
    exact ⟨a + c, b + e, by push_cast; ring⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, e, rfl⟩
    refine ⟨a * c - d * b * e, a * e + b * c, ?_⟩
    have := sq_mul_sq d
    push_cast
    linear_combination (b * e : ℂ) * this
  neg_mem' := by
    rintro _ ⟨a, b, rfl⟩
    exact ⟨-a, -b, by push_cast; ring⟩
  inv_mem' := by
    rintro _ ⟨a, b, rfl⟩
    by_cases h0 : (a : ℂ) + b * sq d = 0
    · exact ⟨0, 0, by rw [h0]; simp⟩
    have hn : (a ^ 2 + d * b ^ 2 : ℚ) ≠ 0 := by
      intro hn
      have hb : b = 0 := by
        by_contra hb
        have : (0 : ℚ) < a ^ 2 + d * b ^ 2 := by
          have : (0 : ℚ) < d := by exact_mod_cast hd
          positivity
        linarith
      have ha : a = 0 := by subst hb; simpa using hn
      apply h0; subst ha; subst hb; simp
    refine ⟨a / (a ^ 2 + d * b ^ 2), -b / (a ^ 2 + d * b ^ 2), ?_⟩
    have hn' : ((a ^ 2 + d * b ^ 2 : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hn
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    have := sq_mul_sq d
    push_cast at hn' ⊢
    field_simp
    linear_combination (-(b:ℂ) ^ 2) * this

theorem conj_mem_Kc {d : ℕ} {hd : 0 < d} {z : ℂ} (hz : z ∈ Kc d hd) : conj z ∈ Kc d hd := by
  obtain ⟨a, b, rfl⟩ := hz
  exact ⟨a, -b, by simp [sq_conj]⟩

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
