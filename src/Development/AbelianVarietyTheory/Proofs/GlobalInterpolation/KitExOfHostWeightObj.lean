module

public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison
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
import Development.AutomorphicArithmetic.PrimeDiscriminants.Scales
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem fc_large_of_sup {C : FC} {K K' : TransportedAlt} {CH : ℝ} (h : C.Large (K.sup K') CH) : C.Large K CH ∧ C.Large K' CH :=
  ⟨⟨fun c hc => (le_max_left _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_left _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_left _ _).trans (h.2.2.2 c hc)⟩,
    ⟨fun c hc => (le_max_right _ _).trans (h.1 c hc), trivial, fun c hc => (le_max_right _ _).trans (h.2.2.1 c hc),
      fun c hc => (le_max_right _ _).trans (h.2.2.2 c hc)⟩⟩

theorem small_prime_lt (eps C8 : ℝ) (he : 0 < eps) (h8 : 1 ≤ C8) : ∃ x0 : ℝ, ∀ (s : Scale) (N q0 : ℝ), s.eps = eps → x0 ≤ s.x →
    0 < N → Real.log N ≤ 2 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 → q0 ≤ N ^ C8 → q0 < s.X' := by
  obtain ⟨x0, hx0⟩ := GlobalTheory.scale_poly_comparison eps (2 * C8) (1 / 2) he (by norm_num)
  refine ⟨x0, fun s N q0 hs hx hN hlog hq => ?_⟩
  have h := (hx0 s hs hx).2.2.2.2.2.2
  have hx1 := s.one_lt_alt
  have h1 : 1 ≤ s.x ^ (2 * C8) := Real.one_le_rpow hx1.le (by linarith)
  have hX : 1 < s.X' := Real.one_lt_exp_iff.2 (Real.rpow_pos_of_pos (by linarith) _)
  have h2 : s.X' ^ (1 / 2 : ℝ) < s.X' := by
    calc s.X' ^ (1 / 2 : ℝ) < s.X' ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hX (by norm_num)
      _ = s.X' := Real.rpow_one _
  have h3 : N ^ C8 ≤ Real.exp (2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) := by
    rw [Real.rpow_def_of_pos hN]
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right hlog (by linarith : (0 : ℝ) ≤ C8)
    linarith
  have h4 : Real.exp (2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) ≤
      Real.exp (2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) * s.x ^ (2 * C8) :=
    le_mul_of_one_le_right (Real.exp_pos _).le h1
  linarith

theorem X'_le_b (s : Scale) : s.X' ≤ s.b := by
  have := s.eps_pos
  exact Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by linarith))

end GlobalTheory.EX
