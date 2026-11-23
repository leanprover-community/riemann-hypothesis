module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepTwo
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

universe u w

theorem SubvarDrop.proof : SubvarDrop.Statement.{u, w} := by
  intro k _ Ω _ _ N x d pp hx hpp hhom hle hrel hf
  have := hpp
  obtain ⟨f, hfp, hfq⟩ := hf
  obtain ⟨j, hj⟩ := hrel

  have hup : ringKrullDim (Poly k N ⧸ pp) + 1 ≤ ((d + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← hx.dim]
    refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
      (Ideal.Quotient.factor_surjective hle) (r := Ideal.Quotient.mk _ f) ?_ ?_
    · apply mem_nonZeroDivisors_of_ne_zero
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hfp

  have hnf : ¬ IsField (Poly k N ⧸ pp) := by
    intro hF
    obtain ⟨v, hv⟩ := hF.mul_inv_cancel (a := Ideal.Quotient.mk pp (X j))
      (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [← map_mul, ← map_one (Ideal.Quotient.mk pp), Ideal.Quotient.eq] at hv
    have h0 := hhom _ hv 0
    rw [homogeneousComponent_zero] at h0
    have h1 : (1 : Poly k N) ∈ pp := by
      have hc : AddMonoidAlgebra.coeff (X j * g - 1 : Poly k N) 0 = -1 := by
        change constantCoeff (X j * g - 1 : Poly k N) = -1; simp
      rw [hc, map_neg, map_one] at h0
      simpa using pp.neg_mem h0
    exact hpp.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hne0 : ringKrullDim (Poly k N ⧸ pp) ≠ 0 := by
    intro h0
    have : Ring.KrullDimLE 0 (Poly k N ⧸ pp) := (ringKrullDimZero_iff_ringKrullDim_eq_zero).mpr h0
    exact hnf Ring.KrullDimLE.isField_of_isDomain
  have hnn : 0 ≤ ringKrullDim (Poly k N ⧸ pp) := ringKrullDim_nonneg_of_nontrivial

  rw [← WithBot.coe_one, ← WithBot.coe_natCast] at hup
  generalize hD : ringKrullDim (Poly k N ⧸ pp) = D at hup hne0 hnn
  induction D using WithBot.recBotCoe with
  | bot => exact absurd hnn (by simp)
  | coe D =>
    induction D using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_add, WithBot.coe_le_coe, top_add] at hup
      exact absurd hup (by simp)
    | coe n =>
      obtain ⟨e, rfl⟩ : ∃ e, n = e + 1 := ⟨n - 1, by
        have : n ≠ 0 := by rintro rfl; exact hne0 rfl
        omega⟩
      refine ⟨e, ?_, ⟨hpp, hhom, hle, ⟨j, hj⟩, hD⟩⟩
      rw [← WithBot.coe_add, WithBot.coe_le_coe] at hup
      have : ((e + 1 + 1 : ℕ) : ℕ∞) ≤ ((d + 1 + 1 : ℕ) : ℕ∞) := by exact_mod_cast hup
      have := Nat.cast_le.mp this
      omega

end GroundTheory.Heights₂.Heights.Kleiman
