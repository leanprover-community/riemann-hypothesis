module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.NumberTheory.NumberField.Basic
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
public import Mathlib.NumberTheory.NumberField.House
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Ring.Basic

@[expose] public section

open NumberField

namespace GlobalTheory

theorem ringOfIntegers_eq_zero_of_natCast_dvd_of_norm_embedding_le
    (E : Type) [Field E] [NumberField E] (g₀ : ℕ) (B : ℝ) (t : 𝓞 E)
    (hd : (g₀ : 𝓞 E) ∣ t) (hB : ∀ ι : E →+* ℂ, ‖ι (t : E)‖ ≤ B) (hlt : B < g₀) : t = 0 := by
  by_contra ht
  obtain ⟨s, rfl⟩ := hd
  have hs : s ≠ 0 := by
    rintro rfl
    exact ht (mul_zero _)
  obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hs
  have h1 := hB σ
  have hcast : (((g₀ : 𝓞 E) * s : 𝓞 E) : E) = (g₀ : E) * (s : E) := by
    push_cast
    rfl
  rw [hcast, map_mul, map_natCast, norm_mul, Complex.norm_natCast] at h1
  have h2 : (g₀ : ℝ) ≤ g₀ * ‖σ (s : E)‖ := le_mul_of_one_le_right (Nat.cast_nonneg _) hσ
  linarith

end GlobalTheory
