module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.PullHomeoApply
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace PositivityTheory.RgUd.T.Desc.SLF

theorem isUnimod_of_equiv {G₁ G₂ : Type*} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
    [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂] (φ : G₁ ≃ₜ* G₂)
    (h : PositivityTheory.PfBern.Frob.IsUnimod G₂) : PositivityTheory.PfBern.Frob.IsUnimod G₁ := by
  intro g
  have hg : modularCharacterFun (φ g) = 1 := h (φ g)
  show modularCharacterFun g = 1
  borelize G₁ G₂
  let μ₂ : Measure G₂ := haar
  have hme : MeasurableEmbedding (φ.symm : G₂ → G₁) := φ.symm.toHomeomorph.measurableEmbedding
  let μ₁ : Measure G₁ := map (φ.symm : G₂ → G₁) μ₂
  haveI : IsHaarMeasure μ₁ := ContinuousMulEquiv.isHaarMeasure_map μ₂ φ.symm
  rw [modularCharacterFun_eq_haarScalarFactor μ₁ g]
  rw [modularCharacterFun_eq_haarScalarFactor μ₂ (φ g)] at hg
  obtain ⟨f, hfc, hf0, hf1⟩ := exists_continuous_nonneg_pos (1 : G₁)
  let f₂ : G₂ → ℝ := fun y => f (φ.symm y)
  have hf₂c : Continuous f₂ := f.continuous.comp φ.symm.continuous
  have hf₂s : HasCompactSupport f₂ := hfc.comp_homeomorph φ.symm.toHomeomorph
  have I1 : ∫ x, f x ∂μ₁ = ∫ y, f₂ y ∂μ₂ := hme.integral_map _
  have I2 : ∫ x, f x ∂(map (· * g) μ₁) = ∫ y, f₂ y ∂(map (· * φ g) μ₂) := by
    rw [integral_map (measurable_mul_const g).aemeasurable f.continuous.aestronglyMeasurable,
      show μ₁ = map (φ.symm : G₂ → G₁) μ₂ from rfl, hme.integral_map,
      integral_map (measurable_mul_const (φ g)).aemeasurable hf₂c.aestronglyMeasurable]
    congr 1
    funext x
    simp [f₂, map_mul]
  have hpos : ∫ x, f x ∂μ₁ ≠ 0 :=
    (f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc hf0 hf1).ne'
  have hpos₂ : ∫ y, f₂ y ∂μ₂ ≠ 0 := by
    rw [← I1]
    exact hpos
  have hg' : ((haarScalarFactor (map (· * φ g) μ₂) μ₂ : NNReal) : ℝ) = 1 := by
    rw [hg]
    rfl
  rw [haarScalarFactor_eq_integral_div _ _ hf₂c hf₂s hpos₂] at hg'
  apply NNReal.coe_injective
  rw [haarScalarFactor_eq_integral_div _ _ f.continuous hfc hpos, I2, I1, hg', NNReal.coe_one]

end PositivityTheory.RgUd.T.Desc.SLF
