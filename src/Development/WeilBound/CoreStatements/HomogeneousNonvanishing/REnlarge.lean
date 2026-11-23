module

public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

theorem r_enlarge : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Θ L L' : LocPot X) (s s' : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C₅ C t₀ : ℝ), 0 ≤ C₅ → 0 ≤ C → t₀ ≤ Real.exp (-1) → (∀ y, logNormSec L s y ≤ 0) → bdry s ⊆ bdry s' → (∀ y, y ∉ bdry s' → rW L s y ≤ rW L' s' y) → IsSingWeight A L s th ph C₅ → IsRegFamily A Θ L s th ph phT C t₀ → IsRegFamilyC2 A s ph phT → IsSingWeight A L' s' th ph C₅ ∧ IsRegFamily A Θ L' s' th ph phT C t₀ ∧ IsRegFamilyC2 A s' ph phT := by
  intro e X _ _ _ A Θ L L' s s' th ph phT C₅ C t₀ hC5 hC ht0 hL hsub hrw hS hR hC2
  have hnb : ∀ y, y ∉ bdry s' → y ∉ bdry s := fun y hy h => hy (hsub h)
  have hpos : ∀ y, 0 < rW L s y := by
    intro y
    unfold rW
    have h1 := hL y
    have h2 := Real.exp_pos 1
    linarith
  obtain ⟨hpot, hsm, hpsh, hb⟩ := hS
  obtain ⟨h0, h1, hf⟩ := hR
  refine ⟨⟨hpot, ?_, ?_, ?_⟩, ⟨h0, h1, ?_⟩, ?_⟩
  · intro j
    exact (hsm j).mono (fun z hz => ⟨hz.1, hnb _ hz.2⟩)
  · intro x j y hy w
    exact hpsh x j y ⟨hy.1, hy.2.1, hnb _ hy.2.2⟩ w
  · intro y hy
    obtain ⟨hlo, hhi⟩ := hb y (hnb y hy)
    refine ⟨?_, hhi⟩
    have hlog : Real.log (rW L s y) ≤ Real.log (rW L' s' y) := Real.log_le_log (hpos y) (hrw y hy)
    nlinarith [mul_le_mul_of_nonneg_left hlog hC5]
  · intro t ht htt
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hf t ht htt
    have hte : t ≤ Real.exp (-1) := le_trans htt ht0
    have h1t : Real.exp 1 ≤ 1 / t := by
      rw [le_div_iff₀ ht]
      calc Real.exp 1 * t ≤ Real.exp 1 * Real.exp (-1) := by gcongr
        _ = 1 := by rw [← Real.exp_add]; simp
    have hL1 : 1 ≤ Real.log (1 / t) := by
      have h := Real.log_le_log (Real.exp_pos 1) h1t
      rwa [Real.log_exp] at h
    have heps : 0 ≤ epsT C t := by
      unfold epsT
      exact div_nonneg (mul_nonneg hC (Real.log_nonneg hL1)) (by linarith)
    refine ⟨a1, a2, fun y hy => a3 y (hnb y hy), a4, a5, ?_, ?_, a8⟩
    · intro y hy hle
      exact a6 y (hnb y hy) (le_trans (hrw y hy) hle)
    · intro y hy
      have h7 := a7 y (hnb y hy)
      nlinarith [mul_le_mul_of_nonneg_left (hrw y hy) heps]
  · intro j K hK hKc
    exact hC2 j K (fun z hz => ⟨(hK hz).1, hnb _ (hK hz).2⟩) hKc

end PositivityTheory.UnitarySelfGeneration
