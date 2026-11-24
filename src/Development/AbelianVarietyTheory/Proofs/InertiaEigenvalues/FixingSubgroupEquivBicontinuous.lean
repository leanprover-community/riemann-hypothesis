module

public import Mathlib.FieldTheory.KrullTopology
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.WeaklyAdmissibleFiltrations.Statement

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

open scoped Topology

theorem fixingSubgroupEquiv_bicontinuous (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k ↥K] :
    Continuous (IntermediateField.fixingSubgroupEquiv K) ∧
      Continuous (IntermediateField.fixingSubgroupEquiv K).symm := by
  refine ⟨continuous_of_continuousAt_one _ ?_, continuous_of_continuousAt_one _ ?_⟩
  · rw [ContinuousAt, map_one, Filter.tendsto_def]
    intro s hs
    obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff K Ω s).1 hs
    have : IsScalarTower k K E := ⟨fun a b x => Subtype.ext (smul_assoc a b (x : Ω))⟩
    have hE' : Module.Finite k E := Module.Finite.trans K E
    have hfin : FiniteDimensional k (E.restrictScalars k) := hE'
    rw [mem_nhds_subtype]
    refine ⟨(E.restrictScalars k).fixingSubgroup,
      (krullTopology_mem_nhds_one_iff k Ω _).2 ⟨E.restrictScalars k, hfin, subset_rfl⟩, ?_⟩
    intro σ hσ
    apply hEs
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x hx
  · rw [ContinuousAt, map_one, Filter.tendsto_def]
    intro s hs
    obtain ⟨u, hu, hus⟩ := (mem_nhds_subtype _ _ _).1 hs
    obtain ⟨E, hE, hEu⟩ := (krullTopology_mem_nhds_one_iff k Ω u).1 hu
    let F : IntermediateField K Ω := IntermediateField.extendScalars (le_sup_right : K ≤ E ⊔ K)
    have hk : FiniteDimensional k (E ⊔ K : IntermediateField k Ω) := inferInstance
    have : Module.Finite k F := hk
    have hF : FiniteDimensional K F := Module.Finite.of_restrictScalars_finite k K F
    refine (krullTopology_mem_nhds_one_iff K Ω _).2 ⟨F, hF, ?_⟩
    intro τ hτ
    apply hus
    apply hEu
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x
      ((IntermediateField.mem_extendScalars _).2 (le_sup_left (a := E) hx))

end GlobalTheory
