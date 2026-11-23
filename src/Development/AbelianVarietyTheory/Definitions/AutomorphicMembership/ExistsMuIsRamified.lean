module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Top.Inh

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

theorem g_big (eps : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) : ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (g : ℕ), s.eps = eps → x0 ≤ s.x →
    RankVal s R → ((R.k : ℝ) * s.b) ^ 8 ≤ g → 2 * R.f * R.k < g - 1 := by
  obtain ⟨x3, hx3⟩ := rank_basic_bounds eps h0 h1
  obtain ⟨x4, hx4⟩ := GlobalTheory.scale_poly_comparison eps 4 1 h0 one_pos
  refine ⟨max x3 (max x4 10), fun s R g he hx hR hg => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨y3, y4, y5⟩ := hx
  obtain ⟨hf, -⟩ := hx3 s R he y3 hR
  obtain ⟨-, -, hb, -⟩ := hx4 s he y4
  have hx0 : 0 < s.x := by linarith
  have hX1 : 1 ≤ s.X' := Real.one_le_exp (by positivity)
  have hk3 := R.m_add_three_le_k
  have pw : ∀ n : ℕ, s.x ^ (n : ℝ) = s.x ^ n := fun n => Real.rpow_natCast _ _
  have hf' : (R.f : ℝ) ≤ s.x ^ 3 := by rw [← pw]; exact_mod_cast hf
  have hb' : s.x ^ 4 ≤ s.b := by
    rw [Real.rpow_one] at hb
    rw [← pw]
    exact le_trans (by exact_mod_cast le_mul_of_one_le_right (by positivity) hX1) hb
  have h3 : 1 ≤ s.x ^ 3 := one_le_pow₀ (by linarith)
  have h4 : 10 * s.x ^ 3 ≤ s.b := by
    calc 10 * s.x ^ 3 ≤ s.x * s.x ^ 3 := mul_le_mul_of_nonneg_right y5 (by positivity)
      _ = s.x ^ 4 := by ring
      _ ≤ s.b := hb'
  have hk1 : (1 : ℝ) ≤ R.k := by exact_mod_cast (by omega : 1 ≤ R.k)
  have c1 : (R.k : ℝ) * s.b ≤ g :=
    (le_self_pow₀ (one_le_mul_of_one_le_of_one_le hk1 (by linarith)) (by norm_num)).trans hg
  have c3 : ((2 * R.f * R.k + 1 : ℕ) : ℝ) < g := by
    have d1 := mul_le_mul_of_nonneg_left h4 (show (0 : ℝ) ≤ R.k by positivity)
    have d2 := mul_le_mul_of_nonneg_left hf' (show (0 : ℝ) ≤ R.k by positivity)
    have d3 := one_le_mul_of_one_le_of_one_le hk1 h3
    push_cast
    nlinarith
  have c4 : 2 * R.f * R.k + 1 < g := by exact_mod_cast c3
  omega


end GlobalTheory.Mem.Top.Inh

end
