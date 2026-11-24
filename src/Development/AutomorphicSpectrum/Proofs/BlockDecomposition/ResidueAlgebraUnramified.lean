module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens

theorem resAlg_of_isUnrQuad : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ),
    ∀ h : IsUnrQuad R σ ϖ q ε, ResAlg (R ⧸ lev ϖ 1) (barσ σ ϖ h.fix_ϖ 1) q ε := by
  intro R _ σ ϖ q ε h
  have hτ : ∀ a : R, barσ σ ϖ h.fix_ϖ 1 (Ideal.Quotient.mk (lev ϖ 1) a) =
      Ideal.Quotient.mk (lev ϖ 1) (σ a) := fun a => Ideal.Quotient.lift_mk _ _ _
  obtain ⟨u, hu, hdec⟩ := h.basis
  refine ⟨?_, ?_, ?_, h.one_lt, h.card, h.eps⟩
  · intro e
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
    rw [hτ a, hτ (σ a), h.inv]
  · intro e he hne
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
    obtain ⟨x, y, hx, hy, rfl⟩ := hdec a
    rw [hτ] at he
    have hy0 : Ideal.Quotient.mk (lev ϖ 1) y = 0 := by
      have h1 : Ideal.Quotient.mk (lev ϖ 1) (y * (u - σ u)) = 0 := by
        have hxy : y * (u - σ u) = (x + y * u) - σ (x + y * u) := by
          rw [map_add (f := _), map_mul, hx, hy]
          ring
        rw [hxy, map_sub, he, sub_self]
      rw [map_mul] at h1
      exact (IsUnit.mul_left_eq_zero (hu.map (Ideal.Quotient.mk (lev ϖ 1)))).mp h1
    have hxe : Ideal.Quotient.mk (lev ϖ 1) (x + y * u) = Ideal.Quotient.mk (lev ϖ 1) x := by
      rw [map_add (f := _), map_mul, hy0, zero_mul, add_zero]
    rw [hxe] at hne ⊢
    exact (h.fixLocal x hx fun hmem => hne (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)).map _
  · refine ⟨Ideal.Quotient.mk (lev ϖ 1) u, ?_, ?_⟩
    · have hm := hu.map (Ideal.Quotient.mk (lev ϖ 1))
      rwa [map_sub, ← hτ] at hm
    · intro e
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
      obtain ⟨x, y, hx, hy, rfl⟩ := hdec a
      refine ⟨Ideal.Quotient.mk (lev ϖ 1) x, Ideal.Quotient.mk (lev ϖ 1) y, ?_, ?_, ?_⟩
      · rw [hτ, hx]
      · rw [hτ, hy]
      · rw [map_add (f := _), map_mul]

end GlobalTheory.CompanionTheory.UnrDens
