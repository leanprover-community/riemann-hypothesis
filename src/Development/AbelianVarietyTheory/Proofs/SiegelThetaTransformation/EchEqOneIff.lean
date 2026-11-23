module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.FourierJ

noncomputable section

variable {κ ι : Type}

def rep (R : ℕ) (n : κ → ι → Fin (R * R)) : Matrix κ ι ℚ :=
  Matrix.of fun k i => ((n k i : ℕ) : ℚ) / R

def zm (m : κ → ι → ℤ) : Matrix κ ι ℚ := Matrix.of fun k i => (m k i : ℚ)

def zv (m : ι → ℤ) : ι → ℚ := fun i => (m i : ℚ)

def ech (t : ℚ) : ℂ := cexp (2 * π * I * (t : ℂ))

def gs [Fintype ι] (τ : Matrix ι ι ℂ) (ζ : ι → ℂ) (v : ι → ℚ) : ℂ :=
  cexp (π * I * (qv v ⬝ᵥ τ *ᵥ qv v + 2 * (qv v ⬝ᵥ ζ)))

theorem ech_add (s t : ℚ) : ech (s + t) = ech s * ech t := by
  unfold ech
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ech_zero : ech 0 = 1 := by
  simp [ech]

theorem ech_eq_one_iff (t : ℚ) : ech t = 1 ↔ ∃ m : ℤ, t = m := by
  unfold ech
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h : (t : ℂ) = ((n : ℚ) : ℂ) := by
      apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
      rw [hn]
      push_cast
      ring
    exact_mod_cast h
  · rintro ⟨m, rfl⟩
    exact ⟨m, by push_cast; ring⟩

theorem norm_ech (t : ℚ) : ‖ech t‖ = 1 := by
  unfold ech
  rw [show (2 : ℂ) * π * I * (t : ℂ) = ((2 * π * t : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem conj_ech (t : ℚ) : conj (ech t) = ech (-t) := by
  unfold ech
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_ratCast]
  push_cast
  ring

theorem ech_sum {α : Type} (s : Finset α) (f : α → ℚ) : ech (∑ a ∈ s, f a) = ∏ a ∈ s, ech (f a) := by
  unfold ech
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum]

theorem intM_iff [Fintype κ] [Fintype ι] (x : Matrix κ ι ℚ) : IntM x ↔ ∃ m : κ → ι → ℤ, x = zm m := by
  constructor
  · intro h
    choose m hm using fun k i => (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp (h k i)
    refine ⟨m, Matrix.ext fun k i => ?_⟩
    rw [← hm k i]
    simp [zm]
  · rintro ⟨m, rfl⟩ k i
    simpa [zm] using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℚ (m k i)))

end

end GlobalTheory.SW.FourierJ
