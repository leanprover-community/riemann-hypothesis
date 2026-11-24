module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WordAppendSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateGrowthSpanHarishChandraFiniteForms
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section

namespace GlobalTheory.MSpanDecay

theorem growth_kernel : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ) (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.MSpanDecay.Growth F → GlobalTheory.MSpanDecay.Growth (fun g : GA E a => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) := by
  intro E _ _ _ a F X _ ν _ k γ hk hF g
  obtain ⟨C, N, hC⟩ := hF g
  set I := ∫ x, ‖k x‖ * height (γ x) ^ N ∂ν with hI
  refine ⟨|C| * ((a : ℝ) + 1) ^ N * I, N, fun y => ?_⟩
  have hint := (hk.2.2 N).const_mul (|C| * ((a : ℝ) + 1) ^ N * height y ^ N)
  have hb : ∀ x, ‖k x * F (g * infGL E a y * infGL E a (γ x))‖ ≤
      |C| * ((a : ℝ) + 1) ^ N * height y ^ N * (‖k x‖ * height (γ x) ^ N) := by
    intro x
    rw [mul_assoc g, ← map_mul, norm_mul]
    have h1 := hC (y * γ x)
    have hm := GlobalTheory.HCF.ModGrowth.height_mul_le y (γ x)
    have hy := one_le_height y
    have hg := one_le_height (γ x)
    have hz := one_le_height (y * γ x)
    have e1 : height (y * γ x) ^ N ≤ (((a : ℝ) + 1) * (height y * height (γ x))) ^ N :=
      pow_le_pow_left₀ (by linarith) hm N
    have e2 : ‖F (g * infGL E a (y * γ x))‖ ≤ |C| * ((((a : ℝ) + 1) * (height y * height (γ x))) ^ N) :=
      h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith) N)).trans
        (mul_le_mul_of_nonneg_left e1 (abs_nonneg C)))
    calc ‖k x‖ * ‖F (g * infGL E a (y * γ x))‖ ≤ ‖k x‖ * (|C| * ((((a : ℝ) + 1) * (height y * height (γ x))) ^ N)) :=
          mul_le_mul_of_nonneg_left e2 (norm_nonneg _)
      _ = |C| * ((a : ℝ) + 1) ^ N * height y ^ N * (‖k x‖ * height (γ x) ^ N) := by
          rw [mul_pow, mul_pow]; ring
  refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hb)).trans_eq ?_
  rw [integral_const_mul, hI]
  ring

end GlobalTheory.MSpanDecay
