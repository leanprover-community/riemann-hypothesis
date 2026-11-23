module

public import GroundTheory.AutomorphicForms.QuotientMeasure
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Topology Filter Set Function
open scoped ENNReal Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace RightCosetSpace

section Algebra

variable {G : Type*} [Group G]

end Algebra

section Geometric

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ]

variable (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]


omit [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [μ.IsMulRightInvariant] in
theorem setIntegral_smul_set {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : G)
    (s : Set G) (F : G → E) : ∫ x in a • s, F x ∂μ = ∫ x in s, F (a * x) ∂μ := by
  have h := (measurePreserving_mul_left μ a).setIntegral_preimage_emb
    (MeasurableEquiv.mulLeft a).measurableEmbedding F (a • s)
  have hpre : (fun x => a * x) ⁻¹' (a • s) = s := by
    ext x
    simp [Set.mem_smul_set_iff_inv_smul_mem]
  rw [hpre] at h
  exact h.symm

variable [CompactSpace (RightCosetSpace Γ)]






omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [DiscreteTopology Γ] in
theorem mem_smul_set_iff' (a y : G) (s : Set G) : y ∈ a • s ↔ a⁻¹ * y ∈ s := by
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]

omit [LocallyCompactSpace G] [T2Space G] [CompactSpace (RightCosetSpace Γ)] in
theorem eq_of_mul_mem_fundamentalDomain {η₁ η₂ : Γ} {y : G}
    (h₁ : (η₁ : G) * y ∈ fundamentalDomain Γ) (h₂ : (η₂ : G) * y ∈ fundamentalDomain Γ) :
    η₁ = η₂ :=
  (existsUnique_smul_mem_fundamentalDomain Γ y).unique h₁ h₂



end Geometric

end RightCosetSpace

end

end GroundTheory.Automorphic
