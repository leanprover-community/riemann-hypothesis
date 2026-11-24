module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.NewformNormCoeffPrimeLeOfNotDvdLevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps

@[expose] public section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices

theorem hecke_bound_lt (k q : ℕ) (hk : 3 ≤ k) (hq : 2 ≤ q) :
    (q : ℝ) ^ ((k : ℝ) / 2) + (q : ℝ) ^ ((k : ℝ) / 2 - 1) < 1 + (q : ℝ) ^ (k - 1) := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  set x : ℝ := (q : ℝ) ^ ((k : ℝ) / 2) with hx
  set y : ℝ := (q : ℝ) ^ ((k : ℝ) / 2 - 1) with hy
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hx1 : 1 < x := Real.one_lt_rpow hq1 (by linarith)
  have hy1 : 1 < y := Real.one_lt_rpow hq1 (by linarith)
  have hxy : x * y = (q : ℝ) ^ (k - 1) := by
    rw [hx, hy, ← Real.rpow_add hq0, ← Real.rpow_natCast]
    congr 1
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  nlinarith [mul_pos (sub_pos.mpr hx1) (sub_pos.mpr hy1)]

theorem hecke_bound_ne (k : ℕ) (g : UpperTheory.V.Af.Newform k) (q : ℕ) (hk : 3 ≤ k) (hq : q.Prime)
    (hqM : ¬ q ∣ g.M) :
    ‖g.a q‖ ≤ (q : ℝ) ^ ((k : ℝ) / 2) + (q : ℝ) ^ ((k : ℝ) / 2 - 1) ∧
      g.a q ≠ 1 + (q : ℂ) ^ (k - 1) := by
  have hb := GlobalTheory.HeckeBd.norm_a_le k g q hq hqM
  refine ⟨hb, fun h => ?_⟩
  have hlt := hecke_bound_lt k q hk hq.two_le
  have hn : ‖(1 : ℂ) + (q : ℂ) ^ (k - 1)‖ = 1 + (q : ℝ) ^ (k - 1) := by
    have : (1 : ℂ) + (q : ℂ) ^ (k - 1) = (((1 : ℝ) + (q : ℝ) ^ (k - 1) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [h, hn] at hb
  linarith

theorem hecke_bound_main : ∀ (k : ℕ) (g : UpperTheory.V.Af.Newform k) (q : ℕ), 3 ≤ k → q.Prime → ¬ q ∣ g.M →
    ‖g.a q‖ ≤ (q : ℝ) ^ ((k : ℝ) / 2) + (q : ℝ) ^ ((k : ℝ) / 2 - 1) ∧ g.a q ≠ 1 + (q : ℂ) ^ (k - 1) :=
  fun k g q hk hq hqM => hecke_bound_ne k g q hk hq hqM

end GlobalTheory.HeckeFamilyMatrices
