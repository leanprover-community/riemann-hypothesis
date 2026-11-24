module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqOneOfStrictMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkInd
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
import Mathlib.Tactic.Linter.Style
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

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem pair_lt {R : Type} [CommRing R] {n : ℕ} {q : R} {H : Type} [Ring H] [Algebra R H] (b : Bern n q H)
    {a c : Fin n} (h : a.val + 1 = c.val) (u : Perm (Fin n)) (hu : u⁻¹ a < u⁻¹ c) :
    (b.T (swap a c) * b.T u - q • b.T u) + (b.T (swap a c) * b.T (swap a c * u) - q • b.T (swap a c * u)) = 0 := by
  have hu : b.T (swap a c * u) = b.T (swap a c) * b.T u := b.T_mul a c h u hu
  have hsq := b.T_sq a c h
  rw [hu, ← mul_assoc, hsq, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
  module

private theorem swap_one {R : Type} [CommRing R] {n : ℕ} {q : R} {H : Type} [Ring H] [Algebra R H] (b : Bern n q H)
    {a c : Fin n} (h : a.val + 1 = c.val) : b.T (swap a c) * b.one = q • b.one := by
  have hac : a ≠ c := by
    intro e
    rw [e] at h
    omega
  have key : ∀ w : Perm (Fin n), (b.T (swap a c) * b.T w - q • b.T w)
      + (b.T (swap a c) * b.T (swap a c * w) - q • b.T (swap a c * w)) = 0 := by
    intro w
    rcases lt_or_gt_of_ne (show w⁻¹ a ≠ w⁻¹ c from fun e => hac (w⁻¹.injective e)) with hw | hw
    · exact pair_lt b h w hw
    · have hu : (swap a c * w)⁻¹ a < (swap a c * w)⁻¹ c := by
        simpa [Perm.mul_apply, mul_inv_rev, swap_inv, swap_apply_left, swap_apply_right] using hw
      have := pair_lt b h (swap a c * w) hu
      rw [← mul_assoc, swap_mul_self, one_mul] at this
      rw [add_comm]
      exact this
  have hsum : ∑ w, (b.T (swap a c) * b.T w - q • b.T w) = 0 := by
    refine Finset.sum_ninvolution (fun w => swap a c * w) key ?_ (fun _ => Finset.mem_univ _) ?_
    · intro w _ e
      apply hac
      have := congrArg (fun x : Perm (Fin n) => (x * w⁻¹) a) e
      simp [mul_assoc] at this
      exact this.symm
    · intro w
      rw [← mul_assoc, swap_mul_self, one_mul]
  unfold Bern.one
  rw [Finset.mul_sum, Finset.smul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  exact hsum

theorem UpperTheory.V.AlgebraTools.hkOne :
    ∀ (R : Type) [CommRing R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H),
      (∀ w, b.T w * b.one = q ^ invN w • b.one) ∧ b.one * b.one = poin (n := n) q • b.one := by
  intro R _ n q H _ _ b
  have hinv := UpperTheory.V.AlgebraTools.hkInv n
  have p1 : ∀ w, b.T w * b.one = q ^ invN w • b.one := by
    refine UpperTheory.V.AlgebraTools.hkInd n _ ?_ ?_
    · rw [b.T_one, one_mul]
      simp [invN, hinv.2.2.1]
    · intro a c h w hw ih
      rw [b.T_mul a c h w hw, mul_assoc, ih, mul_smul_comm, swap_one b h, smul_smul,
        (hinv.1 a c h w hw).2.2, pow_succ]
  refine ⟨p1, ?_⟩
  show (∑ w, b.T w) * b.one = _
  rw [Finset.sum_mul]
  simp_rw [p1]
  rw [← Finset.sum_smul]
  rfl
