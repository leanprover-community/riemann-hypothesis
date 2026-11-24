module

public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LoglogQuotNonneg
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

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv.EvPsh

theorem tendsto_epsT_zero (C : ℝ) :
    Tendsto (fun t => epsT C t) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
  have hℓ : Tendsto (fun t : ℝ => Real.log (1 / t)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) atTop := by
    have h := Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
    refine h.congr (fun t => ?_)
    simp [one_div]
  have hq : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using this
  have h2 := (hq.comp hℓ).const_mul C
  rw [mul_zero] at h2
  refine h2.congr (fun t => ?_)
  simp only [Function.comp_apply, epsT]
  ring

theorem isPsh_of_isPosPot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ : LocPot X) (h : IsPosPot A Θ) : IsPsh A Θ := by
  intro x j y hy w
  by_cases hw : w = 0
  · subst hw
    simp [levi]
  · exact (h x j y hy w hw).le

theorem eventually_isPsh_add_pot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ L : LocPot X) (s : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ)
    (C t₀ : ℝ) (hΘ : IsPotential A Θ) (hΘp : IsPosPot A Θ) (hth : IsPotential A th)
    (hF : IsRegFamily A Θ L s th ph phT C t₀) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      A.Smooth (phT t) ∧ IsPsh A (th + LocPot.ofFun (phT t) + Θ) := by
  obtain ⟨ht₀, -, hF⟩ := hF
  have hε : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), epsT C t < 1 :=
    (tendsto_epsT_zero C).eventually (gt_mem_nhds one_pos)
  have hsmall : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Ioo 0 t₀ :=
    Ioo_mem_nhdsGT ht₀
  filter_upwards [hε, hsmall] with t hεt ht
  obtain ⟨h1, -, -, -, h5, -⟩ := hF t ht.1 ht.2.le
  refine ⟨h1, ?_⟩
  have h := GlobalTheory.CompanionTheory.Ar.Giv.isPsh_rsmul_mono A Θ th (phT t) hΘ (isPsh_of_isPosPot A Θ hΘp) hth h1 hεt.le h5
  have e1 : Θ.rsmul 1 = Θ := by
    cases Θ
    simp [LocPot.rsmul]
  rwa [e1] at h

end GlobalTheory.CompanionTheory.Ar.Giv.EvPsh
