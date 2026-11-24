module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartConeComponent
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDivisorComponents
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiProjPrime)
open GroundTheory.Heights₂.Heights (segreChartComponents mem_segreChartComponents)

theorem ChartConeComponent.proof : ChartConeComponent.Statement := by
  intro K _ _ ι _ W m σ i hW W' hW'
  have hmin := mem_segreChartComponents.1 hW'
  have : W'.IsPrime := hmin.1.1
  let φ : MvPolynomial (Σ k, ι k) ℂ →+* MvPolynomial (Fin m) ℂ := chartSubst σ i
  have : (W'.comap φ).IsPrime := Ideal.comap_isPrime φ W'
  have hle : W.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ W'.comap φ := by
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    show φ (MvPolynomial.map (Int.castRingHom ℂ) f) ∈ W'
    have h := ChartDivisorComponents.chartSection_mem hW.2.1 σ i hf
    rw [chartSection_eq_chartSubst] at h
    exact hmin.1.2 h
  obtain ⟨W'', hW'', hW''le⟩ := Ideal.exists_minimalPrimes_le hle
  exact ⟨W'', hW'', Ideal.map_le_iff_le_comap.2 hW''le⟩

end GroundTheory.Heights₂.Heights.Targets
