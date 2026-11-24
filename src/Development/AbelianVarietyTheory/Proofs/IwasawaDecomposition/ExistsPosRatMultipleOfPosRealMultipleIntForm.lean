module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory

theorem posReal_multiple_rat {X : Type} [AddCommGroup X] (x y : LinearMap.BilinForm ℤ X) (d : ℝ)
    (hd : 0 < d) (hy : y ≠ 0) (h : toReal x = d • toReal y) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ (a : ℤ) • x = (b : ℤ) • y := by
  have hpt : ∀ u v, (x u v : ℝ) = d * (y u v : ℝ) := by
    intro u v
    have := congrArg (fun f => f u v) h
    simpa [toReal] using this
  obtain ⟨u, v, huv⟩ : ∃ u v, y u v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hy (LinearMap.ext₂ hc)
  set r : ℚ := (x u v : ℚ) / (y u v : ℚ) with hr_def
  have hy' : (y u v : ℝ) ≠ 0 := by exact_mod_cast huv
  have hdr : d = (r : ℝ) := by
    rw [hr_def]; push_cast; rw [hpt u v]; field_simp
  have hr : 0 < r := by exact_mod_cast (hdr ▸ hd)
  have hnum : 0 < r.num := Rat.num_pos.mpr hr
  have hcast : ((r.num.toNat : ℕ) : ℤ) = r.num := Int.toNat_of_nonneg hnum.le
  refine ⟨r.den, r.num.toNat, r.den_pos, by omega, ?_⟩
  apply LinearMap.ext₂
  intro p q
  simp only [LinearMap.smul_apply, smul_eq_mul]
  rw [hcast]
  apply Int.cast_injective (α := ℝ)
  push_cast
  rw [hpt p q, hdr]
  have hrr : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  rw [hrr]; field_simp

end GlobalTheory
