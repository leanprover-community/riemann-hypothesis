module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
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
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Partition
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open scoped ContDiff

noncomputable section

theorem BdPartition.proof : BdPartition.Statement := by
  intro X _ _ _ D A R
  set e : Fin R.n → OpenPartialHomeomorph X (Fin D → ℂ) :=
    fun j => (R.ψ j).restrOpen (bdDom R j) (isOpen_bdDom R j) with he
  have hsrc : ∀ j, (e j).source = bdDom R j := by
    intro j
    simp only [he, OpenPartialHomeomorph.restrOpen_source]
    exact Set.inter_eq_right.2 Set.inter_subset_left
  have hc : ∀ j, IsCompatChart A (e j) := fun j =>
    ReciprocityTheory.AnForm.M.pa_compat_restr A (R.ψ j) (R.compat j) _ (isOpen_bdDom R j)
  have hcov : ∀ x, ∃ j, x ∈ (e j).source := fun x =>
    ⟨bdIdx R x, by rw [hsrc]; exact mem_bdDom_bdIdx R x⟩
  have htr : ∀ i j, ContDiffOn ℝ ∞ (e j ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' (e j).source) := fun i j =>
    ReciprocityTheory.AnForm.M.pa_holoSmooth _ _ fun v hv =>
      ReciprocityTheory.AnForm.M.SimpleNormalCrossingSliceCharts.compat_trans A (hc i) (hc j) hv.1 hv.2
  obtain ⟨χ, h0, h1, hs, hsm⟩ := ReciprocityTheory.AnForm.exists_chart_partition e hcov htr
  obtain ⟨B, hAB, -, hB⟩ := ReciprocityTheory.AnForm.M.atlasOfCompat A e hc hcov
  have hBs : ∀ i, B.Smooth (χ i) := by
    intro i j
    obtain ⟨l, hl⟩ := hB j
    rw [hl]
    exact (hsm i l).mono Set.inter_subset_left
  refine ⟨χ, fun i => ReciprocityTheory.AnForm.M.smoothOn_of_compatible hAB.symm' isOpen_univ (hBs i),
    h0, h1, fun i => ?_⟩
  rw [← hsrc]
  exact hs i

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
