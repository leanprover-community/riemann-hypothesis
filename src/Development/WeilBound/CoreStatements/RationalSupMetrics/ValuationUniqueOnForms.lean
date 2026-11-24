module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.WeilBound.CoreStatements.RationalSupMetrics.AevalCoordProd
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

theorem MultiProjectiveCoordinates.valuation_unique_on_forms : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [Field 𝕜] (a : K → ℤ) (s : Ω) (z : (Σ k, ι k) → 𝕜) (w : 𝕜), z ∈ ptsOver 𝕜 (mCoordIdeal y) → HasVal y a s z w → (∀ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + a k) → aeval y g = s * aeval y h → aeval z g = w * aeval z h) ∧ ∀ w', HasVal y a s z w' → w' = w := by
  intro K _ ι _ Ω _ y 𝕜 _ a s z w hz hw
  obtain ⟨dg0, dh0, g0, h0, hg0, hh0, hd0, e0, hne, e1⟩ := hw
  have key : ∀ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg → IsMultiHomog h dh →
      (∀ k, (dg k : ℤ) = dh k + a k) → aeval y g = s * aeval y h → aeval z g = w * aeval z h := by
    intro dg dh g h hg hh hd e
    have hdeg : dg0 + dh = dg + dh0 := by
      funext k
      have h1 := hd k
      have h2 := hd0 k
      simp only [Pi.add_apply]
      omega
    have f1 := MultiProjectiveCoordinates.Val.mh_mul hg hh0
    have f2 := MultiProjectiveCoordinates.Val.mh_mul hg0 hh
    rw [hdeg] at f2
    have h3 := MultiProjectiveCoordinates.Val.form_vanish y hz (MultiProjectiveCoordinates.Val.mh_sub f1 f2) (by
      rw [map_sub, map_mul, map_mul, e, e0]
      ring)
    rw [map_sub, map_mul, map_mul, e1] at h3
    apply mul_right_cancel₀ hne
    linear_combination h3
  refine ⟨key, ?_⟩
  rintro w' ⟨dg, dh, g, h, hg, hh, hd, e, hn, e'⟩
  have := key dg dh g h hg hh hd e
  exact mul_right_cancel₀ hn (e'.symm.trans this)
