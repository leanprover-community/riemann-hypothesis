module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCovolumeRelIndex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MeasureTheory Module ZLattice


open scoped Classical in
theorem CovolumeRelIndex.proof : CovolumeRelIndex.Statement := by
  intro E _ _ _ _ _ μ _ L₁ L₂ _ _ _ _ h
  let f : (Fin (finrank ℝ E) → ℝ) ≃L[ℝ] E := (Module.finBasis ℝ E).equivFunL.symm
  let ν : Measure (Fin (finrank ℝ E) → ℝ) := μ.map f.symm
  have : ν.IsAddHaarMeasure := f.symm.isAddHaarMeasure_map μ
  have hf : MeasurePreserving f ν μ := by
    refine ⟨f.continuous.measurable, ?_⟩
    simp only [ν]
    rw [Measure.map_map f.continuous.measurable f.symm.continuous.measurable]
    have : (⇑f ∘ ⇑f.symm) = id := by ext x; simp
    rw [this, Measure.map_id]
  obtain ⟨c, hν⟩ : ∃ c : NNReal, ν = c • volume := ⟨_, Measure.isAddLeftInvariant_eq_smul ν volume⟩
  have scale : ∀ (L : Submodule ℤ (Fin (finrank ℝ E) → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L],
      covolume L ν = (c : ℝ) * covolume L volume := by
    intro L _ _
    rw [covolume_eq_measure_fundamentalDomain L ν
        (ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L) ν),
      covolume_eq_measure_fundamentalDomain L volume
        (ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L) volume)]
    conv_lhs => rw [hν]
    exact measureReal_nnreal_smul_apply c
  have hidx : ((ZLattice.comap ℝ L₁ f.toLinearMap).toAddSubgroup.relIndex
      (ZLattice.comap ℝ L₂ f.toLinearMap).toAddSubgroup : ℝ) =
      (L₁.toAddSubgroup.relIndex L₂.toAddSubgroup : ℝ) := by
    rw [ZLattice.comap_toAddSubgroup, ZLattice.comap_toAddSubgroup, Nat.cast_inj,
      LinearEquiv.toAddMonoidHom_commutes, AddSubgroup.comap_equiv_eq_map_symm',
      AddSubgroup.comap_equiv_eq_map_symm',
      AddSubgroup.relIndex_map_map_of_injective _ _ f.symm.injective]
  have key := covolume_div_covolume_eq_relIndex (ZLattice.comap ℝ L₁ f.toLinearMap)
    (ZLattice.comap ℝ L₂ f.toLinearMap) (fun _ h' ↦ h h')
  have hne := covolume_ne_zero (ZLattice.comap ℝ L₂ f.toLinearMap) volume
  rw [← covolume_comap L₁ μ ν hf, ← covolume_comap L₂ μ ν hf, scale, scale, ← hidx, ← key]
  field_simp

end GroundTheory.Heights₂.Heights.Targets
