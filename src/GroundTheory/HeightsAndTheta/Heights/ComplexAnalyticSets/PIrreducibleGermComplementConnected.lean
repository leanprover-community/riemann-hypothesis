module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermComplementConnected
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegularLocusDense
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermRegularConnected
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StManifoldZerosComplementConnected
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Analytic.ChangeOrigin

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem IrreducibleGermComplementConnected.proof (hdense : RegularLocusDense.Statement)
    (hconn : IrreducibleGermRegularConnected.Statement)
    (hzeros : ManifoldZerosComplementConnected.Statement) :
    IrreducibleGermComplementConnected.Statement := by
  intro σ _ X w h hX hirr hh hnot U hU
  obtain ⟨N, hNo, hwN, hN⟩ := hdense σ X w hX
  have hU' : U ∩ N ∩ {z | AnalyticAt ℂ h z} ∈ 𝓝 w :=
    inter_mem (inter_mem hU (hNo.mem_nhds hwN)) hh.eventually_analyticAt
  obtain ⟨B, hBo, hwB, hBU, hR⟩ := hconn σ X w hX hirr _ hU'
  have hBh : ∀ z ∈ B, AnalyticAt ℂ h z := fun z hz => (hBU hz).2
  have hcl : X ∩ B ⊆ closure (regLocus (X ∩ B)) := hN B hBo fun z hz => (hBU hz).1.2

  have hcl' : (X ∩ B) \ {z | h z = 0} ⊆ closure (regLocus (X ∩ B) \ {z | h z = 0}) := by
    rintro z ⟨hzXB, hz0⟩
    rw [mem_closure_iff_nhds]
    intro t ht
    have hne : {y | h y ≠ 0} ∈ 𝓝 z := (hBh z hzXB.2).continuousAt.eventually_ne hz0
    obtain ⟨y, ⟨hyt, hyh⟩, hyR⟩ := mem_closure_iff_nhds.1 (hcl hzXB) _ (inter_mem ht hne)
    exact ⟨y, hyt, hyR, hyh⟩

  have hex : ∃ x ∈ regLocus (X ∩ B), h x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hnot
    filter_upwards [hBo.mem_nhds hwB] with z hzB hzX
    by_contra hz0
    obtain ⟨y, hyR, hyh⟩ := closure_nonempty_iff.1 ⟨z, hcl' ⟨⟨hzX, hzB⟩, hz0⟩⟩
    exact hyh (hcon y hyR)
  have hRc : IsPreconnected (regLocus (X ∩ B) \ {z | h z = 0}) :=
    hzeros σ _ h hR (fun x hx => isRegularPointOf_regLocus hx)
      (fun x hx => hBh x (regLocus_subset _ hx).2) hex
  exact ⟨B, hBo, hwB, fun z hz => (hBU hz).1.1,
    hRc.subset_closure (Set.sdiff_subset_sdiff_left (regLocus_subset _)) hcl'⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
