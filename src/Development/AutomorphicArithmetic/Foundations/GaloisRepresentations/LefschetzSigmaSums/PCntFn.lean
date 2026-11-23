module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.SigmaSplit
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.InvPol

@[expose] public section

open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.cntFn_of :
    CntFn := by
  intro Γ _ K K' M h hKK' hMn hidx hconj
  have hrep : ∀ (c m : K'), m ∈ M.subgroupOf K' → ∀ y : Γ,
      (h * ((c * m : K') : Γ) * y ∈ K ↔ h * (c : Γ) * y ∈ K) := by
    intro c m hm y
    have hm' : (m : Γ) ∈ M := Subgroup.mem_subgroupOf.mp hm
    have key : h * ((c * m : K') : Γ) * y = (h * (c : Γ) * m * (h * c)⁻¹) * (h * c * y) := by
      push_cast
      group
    rw [key]
    exact Subgroup.mul_mem_cancel_left K (hconj c c.2 m hm')
  have hnz : ∀ y : Γ, cntFn K K' M h y ≠ 0 →
      ∃ q : K' ⧸ M.subgroupOf K', h * ((Quotient.out q : K') : Γ) * y ∈ K := by
    intro y hy
    unfold cntFn at hy
    obtain ⟨⟨q, hq⟩⟩ := (Nat.card_ne_zero.mp (Nat.cast_ne_zero.mp hy)).1
    exact ⟨q, hq⟩
  refine ⟨?_, ?_, ?_⟩
  · intro k hk y
    constructor
    · haveI : (M.subgroupOf K').Normal := ⟨fun n hn g => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        simpa using hMn g g.2 n hn⟩
      unfold cntFn
      congr 1
      refine Nat.card_congr (Equiv.subtypeEquiv
        (Equiv.mulRight (((⟨k, hKK' hk⟩ : K') : K' ⧸ M.subgroupOf K'))) ?_)
      intro q
      obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (M.subgroupOf K') (Quotient.out q * ⟨k, hKK' hk⟩)
      have hq : q * (((⟨k, hKK' hk⟩ : K') : K' ⧸ M.subgroupOf K')) =
          ((Quotient.out q * ⟨k, hKK' hk⟩ : K') : K' ⧸ M.subgroupOf K') := by
        rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
      simp only [Equiv.coe_mulRight]
      rw [hq, hm, hrep _ _ m.2]
      simp only [Subgroup.coe_mul, mul_assoc]
    · unfold cntFn
      simp only [← mul_assoc, Subgroup.mul_mem_cancel_right K hk]
  · intro y hy
    obtain ⟨q, hq⟩ := hnz y hy
    refine ⟨(h * ((Quotient.out q : K') : Γ) * y)⁻¹, K.inv_mem hq, _, (Quotient.out q).2, ?_⟩
    group
  · haveI : (M.subgroupOf K').FiniteIndex := Subgroup.finiteIndex_iff.mpr hidx
    refine (Set.finite_range (fun q : K' ⧸ M.subgroupOf K' =>
      ((((Quotient.out q : K') : Γ)⁻¹ * h⁻¹ : Γ) : Γ ⧸ K))).subset ?_
    intro y hy
    obtain ⟨q, hq⟩ := hnz _ hy
    refine ⟨q, ?_⟩
    conv_rhs => rw [← QuotientGroup.out_eq' y]
    rw [QuotientGroup.eq]
    simpa [mul_assoc] using hq
