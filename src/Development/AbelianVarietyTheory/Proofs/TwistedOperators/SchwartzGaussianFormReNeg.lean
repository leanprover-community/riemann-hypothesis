module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory

namespace GlobalTheory

theorem schwartz_gaussian_form_re_neg {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (M : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (g : SchwartzMap V ℂ) (hg : g ≠ 0)
    (hform : ∀ x, g x = g 0 * Complex.exp (M x x)) (v : V) (hv : v ≠ 0) : (M v v).re < 0 := by
  have hg0 : g 0 ≠ 0 := by
    intro h0
    apply hg
    ext x
    rw [hform x, h0]; simp
  by_contra hre
  push_neg at hre
  obtain ⟨C, hC, hdec⟩ := g.decay 1 0
  have hgn : 0 < ‖g 0‖ := norm_pos_iff.mpr hg0
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set s : ℝ := (C + 1) / (‖v‖ * ‖g 0‖) with hs
  have hspos : 0 < s := by positivity
  have key := hdec (s • v)
  rw [norm_iteratedFDeriv_zero, pow_one, hform (s • v)] at key
  have hM : M (s • v) (s • v) = ((s ^ 2 : ℝ) : ℂ) * M v v := by
    simp only [map_smul, LinearMap.smul_apply, smul_smul]
    rw [Complex.real_smul]; push_cast; ring
  rw [hM, norm_mul, Complex.norm_exp] at key
  have hexp : 1 ≤ Real.exp ((((s ^ 2 : ℝ) : ℂ) * M v v).re) := by
    apply Real.one_le_exp
    rw [Complex.re_ofReal_mul]
    positivity
  have hnorm : ‖s • v‖ = s * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
  rw [hnorm] at key
  have h1 : s * ‖v‖ * ‖g 0‖ = C + 1 := by
    rw [hs]; field_simp
  have h2 : s * ‖v‖ * ‖g 0‖ ≤ s * ‖v‖ * (‖g 0‖ * Real.exp ((((s ^ 2 : ℝ) : ℂ) * M v v).re)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  linarith

end GlobalTheory
