module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousBlkM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem lintegral_sq_add_sq_rpow_neg :
    ∀ s : ℝ, 1 / 2 < s → ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ a : ℝ, 0 < a → ∀ m : ℝ,
    ∫⁻ d : ℝ, ENNReal.ofReal ((a ^ 2 + (d - m) ^ 2) ^ (-s)) = C * ENNReal.ofReal (a ^ (1 - 2 * s)) := by
  intro s hs
  have hint : Integrable (fun t : ℝ => (1 + t ^ 2) ^ (-s)) := by
    have h0 := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * s)
      (by simp; linarith)
    have e : -(2 * s) / 2 = -s := by ring
    simpa [Real.norm_eq_abs, sq_abs, e] using h0
  refine ⟨∫⁻ t, ENNReal.ofReal ((1 + t ^ 2) ^ (-s)), hint.lintegral_lt_top.ne, ?_⟩
  intro a ha m
  have hF : Measurable fun d : ℝ => ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s)) := by fun_prop
  rw [lintegral_sub_right_eq_self (fun d : ℝ => ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s))) m]
  have hpt : ∀ t : ℝ, ENNReal.ofReal ((a ^ 2 + (a * t) ^ 2) ^ (-s)) =
      ENNReal.ofReal (a ^ ((2 : ℕ) * -s : ℝ)) * ENNReal.ofReal ((1 + t ^ 2) ^ (-s)) := by
    intro t
    rw [← ENNReal.ofReal_mul (by positivity), show a ^ 2 + (a * t) ^ 2 = a ^ 2 * (1 + t ^ 2) by ring,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast a 2,
      ← Real.rpow_mul ha.le]
  have hpow : a ^ (1 - 2 * s) = a * a ^ ((2 : ℕ) * -s : ℝ) := by
    rw [show (1 - 2 * s) = 1 + ((2 : ℕ) * -s : ℝ) by push_cast; ring, Real.rpow_add ha,
      Real.rpow_one]
  calc ∫⁻ d, ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s))
      = ∫⁻ d, ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s))
          ∂(ENNReal.ofReal |a| • Measure.map (a * ·) volume) := by
        rw [Real.smul_map_volume_mul_left ha.ne']
    _ = ENNReal.ofReal |a| * ∫⁻ t, ENNReal.ofReal ((a ^ 2 + (a * t) ^ 2) ^ (-s)) := by
        rw [lintegral_smul_measure, lintegral_map hF (measurable_const_mul a), smul_eq_mul]
    _ = ENNReal.ofReal a * (ENNReal.ofReal (a ^ ((2 : ℕ) * -s : ℝ)) *
          ∫⁻ t, ENNReal.ofReal ((1 + t ^ 2) ^ (-s))) := by
        rw [abs_of_pos ha]
        simp_rw [hpt]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul ha.le, ← hpow, mul_comm]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
