module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DedekindZetaEulerProductMulSubOneEntire
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EulerProductNeZeroOneOfEntire
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeLEntireAndNonzeroAtOneHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal

theorem IsHeckeL.ne_zero_nat {E : Type} [Field E] [NumberField E] {χ : HChar E} {Λ : ℂ → ℂ} (hu : IsUnitary χ)
    (hΛ : IsHeckeL χ Λ) {s : ℕ} (hs : 1 ≤ s) : Λ s ≠ 0 := by
  rcases hs.eq_or_lt with rfl | h
  · obtain ⟨Z, hZd, hZ⟩ := GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire E
    rw [Nat.cast_one]
    exact GlobalTheory.eulerProduct_ne_zero_one_of_entire _ _ (GlobalTheory.HeckeOne.cf χ) GlobalTheory.HeckeOne.two_le_N
      (GlobalTheory.HeckeOne.norm_cf hu) GlobalTheory.HeckeOne.sumN GlobalTheory.HeckeOne.nonemptyN Z Λ hZd hΛ.1 hZ
      fun s hs => (hΛ.2 s hs).unique (GlobalTheory.HeckeOne.hasProd_exp hu hs)
  · have hs' : 1 < (s : ℂ).re := by
      rw [Complex.natCast_re]; exact_mod_cast h
    rw [(hΛ.2 _ hs').unique (GlobalTheory.HeckeOne.hasProd_exp hu hs')]
    exact Complex.exp_ne_zero _

theorem heckeL_ne_zero_nat : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (m : I → ℤ) (χ : HChar E), IsCMType φ → IsUnitary χ → HasInf χ φ m → (∃ i, m i ≠ 0) → ∃ Λ, IsHeckeL χ Λ) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (m : I → ℤ) (χ : HChar E) (Λ : ℂ → ℂ) (s : ℕ), IsUnitary χ → HasInf χ φ m → (∀ i, 0 < m i) → IsHeckeL χ Λ → 1 ≤ s → Λ s ≠ 0 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hu _ _ hΛ hs => hΛ.ne_zero_nat hu hs

end GlobalTheory.CMVal
