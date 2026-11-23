module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChartProjObjects
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MemChartComponents
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjChartSetEqSetChartSet
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsWeightedHomogeneousOfIsMultiHomog
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjHomInjective
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
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FinProj

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

open GroundTheory.Heights₂.Heights.ComplexSets

theorem setChartIdeal_le_chartIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {S : Set ((Σ k, ι k) → ℂ)} {e m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ0 : ∀ w, Ψ w 0 = w i) :
    GlobalTheory.CompanionTheory.Ar.Pub.CxChart.setChartIdeal S σ Ψ ≤ GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal S σ i := by
  have hset : GlobalTheory.CompanionTheory.Ar.Pub.CxChart.setChartSet S σ Ψ = GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartSet S σ i := by
    ext x
    simp only [GlobalTheory.CompanionTheory.Ar.Pub.CxChart.setChartSet, GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartSet, hΨ0]
  rw [GlobalTheory.CompanionTheory.Ar.Pub.CxChart.setChartIdeal, GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal, hset]

theorem chartProj_finite : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → (∀ w, Ψ w 0 = w i) →
    (∀ J ∈ chartComponents (conePts Q) σ i, ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ)) →
    ∀ J ∈ chartComponents (conePts Q) σ i,
      GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J (chartProjMatrix σ Ψ) := by
  intro K _ _ ι _ Q e m σ i Ψ hQ hΨ hΨ0 hdim J hJ
  have hJm := GlobalTheory.CompanionTheory.Ar.Pub.CxChart.mem_chartComponents.1 hJ
  have hR : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q := hQ.2.1.2.1
  have hfin : (projHom J (chartProjMatrix σ Ψ)).toRingHom.Finite := by
    have hrad : originIdeal m ≤ (leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ)).radical := by
      refine Ideal.span_le.2 (Set.range_subset_iff.2 fun a => ?_)
      obtain ⟨r, hr⟩ := GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cone_pow_mem hR hΨ
        ((setChartIdeal_le_chartIdeal hΨ0).trans hJm.1.2) a
      exact ⟨r, hr⟩
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg_radical hrad (IsNoetherian.noetherian _)
    exact ConeAvoidsFinite.proof m e N J _ hN
  exact ⟨FiniteProjHomInjective.proof m e J _ hJm.1.1 (hdim J hJ) hfin, hfin⟩

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FinProj
