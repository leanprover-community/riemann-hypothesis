module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

def archFactor (n : I → ℤ) (s : ℂ) : ℂ :=
  ∏ i, (2 * (2 * (Real.pi : ℂ)) ^ (-(s + ((|n i| : ℤ) : ℂ) / 2)) * Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2))

def IsCompletedL (χ : HChar E) (n : I → ℤ) (Λ : ℂ → ℂ) : Prop :=
  Differentiable ℂ Λ ∧ ∀ s : ℂ, 1 < s.re → ∃ L : ℂ, HasProd (eulerFactor χ s) L ∧ Λ s = archFactor n s * L

def BoundedInStrips (Λ : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, a < b → ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖Λ s‖ ≤ C

def CompletedLBoundedInStrips : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (χ : HChar E) (n : I → ℤ), IsUnitary χ → Formalism.L2.Host.HChar.HasInf χ φ n → (∃ i, n i ≠ 0) →
      ∃ Λ : ℂ → ℂ, IsCompletedL χ n Λ ∧ BoundedInStrips Λ

theorem IsCompletedL.unique {χ : HChar E} {n : I → ℤ} {f g : ℂ → ℂ} (hf : IsCompletedL χ n f) (hg : IsCompletedL χ n g) :
    f = g :=
  entire_eq_of_halfPlane hf.1 hg.1 1 fun s hs => by
    obtain ⟨L, h1, h2⟩ := hf.2 s hs
    obtain ⟨L', h1', h2'⟩ := hg.2 s hs
    rw [h2, h2', h1.unique h1']

theorem IsCompletedL.eq_mul {χ : HChar E} {n : I → ℤ} {Λ L : ℂ → ℂ} (h : IsCompletedL χ n Λ) (hL : IsHeckeL χ L)
    {s : ℂ} (hs : 1 < s.re) : Λ s = archFactor n s * L s := by
  obtain ⟨L', h1, h2⟩ := h.2 s hs
  rw [h2, h1.unique (hL.2 s hs)]

theorem archFactor_two_mul (m : I → ℤ) (s : ℂ) : archFactor (fun i => 2 * m i) s = LInf m s := by
  unfold archFactor LInf
  refine Finset.prod_congr rfl fun i _ => ?_
  have : (((|2 * m i| : ℤ) : ℂ)) / 2 = ((|m i| : ℤ) : ℂ) := by
    rw [abs_mul, abs_two]; push_cast; ring
  rw [this]

end GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds
