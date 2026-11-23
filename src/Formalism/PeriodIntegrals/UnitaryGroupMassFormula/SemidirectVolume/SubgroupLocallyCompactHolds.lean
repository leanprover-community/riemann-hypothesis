module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.VolSemiDirect.W

theorem subgroup_locally_compact_holds : SubLCSC := by
  intro X _ _ Γ K hX hK hΓc hΓd
  obtain ⟨hlc, hsc, ht2, htg⟩ := hX
  haveI := hlc
  haveI := hsc
  haveI := ht2
  haveI := htg
  haveI := hΓc
  haveI := hΓd
  let f : ratG Γ K → Γ := fun x => ⟨(x : K).1, (Subgroup.mem_inf.1 ((Subgroup.mem_subgroupOf).1 x.2)).1⟩
  refine ⟨⟨hK.isClosedEmbedding_subtypeVal.locallyCompactSpace, Topology.IsEmbedding.subtypeVal.secondCountableTopology,
    inferInstance, inferInstance⟩, ?_, ?_⟩
  · have hf : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      apply Subtype.ext
      have h' := congrArg (fun y : Γ => (y : X)) h
      exact h'
    exact hf.countable
  · have hcont : Continuous f := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val
    have hemb : Topology.IsEmbedding f := by
      apply Topology.IsEmbedding.of_comp hcont continuous_subtype_val
      show Topology.IsEmbedding (fun x : ratG Γ K => ((x : K) : X))
      exact Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
    exact hemb.discreteTopology

end PI.VolSemiDirect.W
