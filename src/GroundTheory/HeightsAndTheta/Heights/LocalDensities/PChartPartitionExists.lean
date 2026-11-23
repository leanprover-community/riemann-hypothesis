module

public import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsChartPartition
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
public import Mathlib.Geometry.Manifold.PartitionOfUnity
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
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeIntB
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.ContMDiffMap

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open ReciprocityTheory.AnForm.M Set
open scoped ContDiff Manifold

theorem ChartPartitionExists.proof : ChartPartitionExists.Statement := by
  intro e X _ _ A
  classical
  let _ : ChartedSpace (Fin e → ℂ) X :=
    { atlas := Set.range A.chart
      chartAt := fun x => A.chart (A.cover x).choose
      mem_chart_source := fun x => (A.cover x).choose_spec
      chart_mem_atlas := fun x => ⟨_, rfl⟩ }
  have : IsManifold 𝓘(ℝ, Fin e → ℂ) ∞ X := by
    apply isManifold_of_contDiffOn
    rintro _ _ ⟨j, rfl⟩ ⟨k, rfl⟩
    have h := A.holo j k
    have hs : ((A.chart j).symm ≫ₕ A.chart k).source =
        (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source := by
      simp
    have ho : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source) :=
      (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target
        (A.chart k).open_source
    have hc : ContDiffOn ℂ ∞ (A.chart k ∘ (A.chart j).symm)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source) :=
      h.contDiffOn ho.uniqueDiffOn
    simpa [hs] using hc.restrict_scalars ℝ
  have : SecondCountableTopology X := ReciprocityTheory.AnForm.M.dI_secondCountable A
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (Fin e → ℂ) X
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Fin e → ℂ) isClosed_univ
    (fun j => (A.chart j).source) (fun j => (A.chart j).open_source)
    (fun x _ => mem_iUnion.2 (A.cover x))
  refine ⟨⟨fun j => f j, fun k j => ?_, fun j x => f.nonneg j x, fun j => hf j, fun x => ?_⟩⟩
  · have hmem : A.chart j ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin e → ℂ) ∞ X :=
      IsManifold.subset_maximalAtlas ⟨j, rfl⟩
    have h1 : ContMDiffOn 𝓘(ℝ, Fin e → ℂ) 𝓘(ℝ) ∞ (f k) (A.chart j).source :=
      (f k).contMDiff.contMDiffOn
    rw [contMDiffOn_iff_source_of_mem_maximalAtlas hmem subset_rfl,
      contMDiffOn_iff_contDiffOn] at h1
    simpa [(A.chart j).image_source_eq_target] using h1
  · rw [← finsum_eq_sum_of_fintype]
    exact f.sum_eq_one (mem_univ x)

end GroundTheory.Heights₂.Heights.FourB
