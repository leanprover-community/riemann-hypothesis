module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PackingStatement
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmallSectionCountMonoLattice
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem selfIntersection_le_volNm_of_moriwakiBig : MoriwakiBigStatement → BirationalPullbackPushforwardFormula := by
  intro h K _ ι _ Ω _ y D A P0 II hD hII hV hB hP hS hF hC
  have hN : NefOnGeneric (mCoordIdeal y) A :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.NefOnGenericOfSemipos.proof K ι (mCoordIdeal y) P0 A hP hS
  have hb := h K ι Ω y D A P0 II hII hV hB hP hS hC hF hN
  obtain ⟨hfin, C, hC'⟩ := GlobalTheory.T.packing' K ι Ω y D A (chartLatNm y A.a) hV hB hS.1 (fun _ => le_rfl)
  refine hb.trans ?_
  unfold arVolP
  have h0 : ∀ (La : ℕ → AddSubgroup Ω) (τ : ℕ), 0 ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y A) La τ := by
    intro La τ
    unfold smallSectionCount
    exact Real.log_natCast_nonneg _
  have hden : ∀ k : ℕ, (0 : ℝ) ≤ ((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := fun k => by positivity
  refine Filter.limsup_le_limsup ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun k => div_le_div_of_nonneg_right
      (GroundTheory.Heights₂.Heights.HilbertSamuel.smallSectionCount_mono_lattice _ _
        (GroundTheory.Heights₂.Heights.HilbertSamuel.chartLat_le_chartLatNm y A.a _) (hfin _)) (hden k)
  · exact Filter.isCoboundedUnder_le_of_le Filter.atTop (fun k => div_nonneg (h0 _ _) (hden k))
  · refine Filter.isBoundedUnder_of_eventually_le (a := max C 0 * 2 ^ (D + 1) * ((D + 1).factorial : ℝ)) ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hkpos : (0 : ℝ) < ((1 * k : ℕ) : ℝ) := by
      rw [one_mul]
      exact_mod_cast hk
    have hF : (0 : ℝ) < ((D + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hpos : (0 : ℝ) < ((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by positivity
    rw [div_le_iff₀ hpos]
    have h1 := hC' (1 * k)
    have h2 : ((1 * k : ℕ) : ℝ) + 1 ≤ 2 * ((1 * k : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((1 * k : ℕ) : ℝ) := by
        rw [one_mul]
        exact_mod_cast hk
      linarith
    have h3 : (((1 * k : ℕ) : ℝ) + 1) ^ (D + 1) ≤ (2 * ((1 * k : ℕ) : ℝ)) ^ (D + 1) :=
      pow_le_pow_left₀ (by positivity) h2 _
    have h4 : C * (((1 * k : ℕ) : ℝ) + 1) ^ (D + 1) ≤ max C 0 * (((1 * k : ℕ) : ℝ) + 1) ^ (D + 1) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    have hF' := hF.ne'
    calc _ ≤ max C 0 * (2 * ((1 * k : ℕ) : ℝ)) ^ (D + 1) :=
          h1.trans (h4.trans (mul_le_mul_of_nonneg_left h3 (le_max_right _ _)))
      _ = max C 0 * 2 ^ (D + 1) * ((D + 1).factorial : ℝ) *
          (((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
        field_simp
        ring

end GlobalTheory.CompanionTheory.Ar.Small
