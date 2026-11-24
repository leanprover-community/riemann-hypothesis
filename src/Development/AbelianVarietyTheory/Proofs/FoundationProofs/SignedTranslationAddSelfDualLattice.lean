module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableComb
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.GalTheta

theorem al_add (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N'))
    (h1 : ∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) (h2 : ∀ x ∈ A, ∃ m : ℤ, qH D T x = m)
    (h3 : ∀ x ∈ A, w0 D • x ∈ A) : ∀ x ∈ A, ∀ y ∈ A, al D T (x + y) =
      al D T x * al D T y * Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ)) := by
  intro x hx y hy
  obtain ⟨a, ha⟩ := h2 x hx
  obtain ⟨c, hc⟩ := h2 y hy
  obtain ⟨b, hb⟩ := h1 x hx y hy
  obtain ⟨k, hk⟩ := h1 _ (h3 x hx) y hy
  have hal : ∀ z : VC D N N', ∀ m : ℤ, qH D T z = m → al D T z = (-1 : ℂ) ^ m := by
    intro z m hm
    have e : al D T z = (-1 : ℂ) ^ (round (qH D T z)) := rfl
    rw [e, hm, round_intCast]
  have hk' : Real.sqrt D.host.d * (Hf D T x y).re = 2 * k - b := by
    rw [Hf_smul_left] at hk
    rw [← hk, ← hb]
    simp [w0, Complex.mul_im]
    ring
  have hs : qH D T (x + y) = ((a + c + (2 * k - b) : ℤ) : ℝ) := by
    push_cast
    rw [← ha, ← hc, ← hk']
    simp only [qH, Hf_add_left, Hf_add_right, Complex.add_re, Hf_re_swap D T x y]
    ring
  have he : Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ)) = (-1 : ℂ) ^ (-b) := by
    rw [hb, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  have hn : (-1 : ℂ) ≠ 0 := by norm_num
  rw [hal _ _ hs, hal _ _ ha, hal _ _ hc, he, sub_eq_add_neg, zpow_add₀ hn, zpow_add₀ hn, zpow_add₀ hn,
    zpow_mul]
  simp

end GlobalTheory.GalTheta
