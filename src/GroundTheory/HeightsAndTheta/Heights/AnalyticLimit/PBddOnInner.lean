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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData RegCharts)

theorem bdDom_compact_inner {D : ℕ} {X : Type} [TopologicalSpace X] {A : ReciprocityTheory.AnForm.M.FinHolAtlas D X}
    (R : RegChartData A) (j : Fin R.n) :
    IsCompact ((R.ψ j).symm '' closure (R.W'' j)) ∧
      (R.ψ j).symm '' closure (R.W'' j) ⊆ bdDom R j ∧
      R.V'' j ⊆ (R.ψ j).symm '' closure (R.W'' j) := by
  have hW : closure (R.W'' j) ⊆ R.W j :=
    (R.closure_W''_subset j).trans (subset_closure.trans (R.closure_W'_subset j))
  have hT : closure (R.W'' j) ⊆ (R.ψ j).target := hW.trans (R.W_subset j)
  have hc : IsCompact (closure (R.W'' j)) :=
    (R.isCompact_closure_middle j).of_isClosed_subset isClosed_closure
      ((R.closure_W''_subset j).trans subset_closure)
  refine ⟨hc.image_of_continuousOn ((R.ψ j).continuousOn_symm.mono hT), ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨(R.ψ j).map_target (hT hz), ?_⟩
    show R.ψ j ((R.ψ j).symm z) ∈ R.W j
    rw [(R.ψ j).right_inv (hT hz)]
    exact hW hz
  · intro y hy
    exact ⟨R.ψ j y, subset_closure hy.2, (R.ψ j).left_inv hy.1⟩

theorem BddOnInner.proof : BddOnInner.Statement := by
  intro X _ D A R j u hu
  obtain ⟨hK, hKD, hVK⟩ := bdDom_compact_inner R j
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hu.mono hKD)
  exact ⟨B, fun y hy => by simpa [Real.norm_eq_abs] using hB y (hVK hy)⟩

end GroundTheory.Heights₂.Heights.AnalyticLimit
