module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SameGenusFix
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OrthogonalLatticeSameGenus
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Module
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3

namespace GluedLatticeMass

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V1 : Type} [AddCommGroup V1] [Module K V1] [Module (𝓞 K) V1] [IsScalarTower (𝓞 K) K V1]

theorem z_ne_zero {h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K} {z : V1} (hz0 : h1 z z ≠ 0) : z ≠ 0 := by
  rintro rfl
  simp at hz0

theorem orthK_span (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) :
    Formalism.L2.SG.Pf.Cnt.orthK h1 (Submodule.span K {z}) = wPerp h1 z := by
  ext x
  simp only [Formalism.L2.SG.Pf.Cnt.orthK, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro H
    exact H z (Submodule.mem_span_singleton_self z)
  · intro hx u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
    have hx' : h1 z x = 0 := hx
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hx', smul_zero]

theorem glueSet_iff {h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K} {z : V1} (hz0 : h1 z z ≠ 0) (Λ : Submodule (𝓞 K) V1) :
    Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet h1 (Submodule.span K {z}) (Submodule.span (𝓞 K) {z}) ↔
      IsGlueLat h1 z Λ := by
  have hz : z ≠ 0 := z_ne_zero hz0
  unfold Formalism.L2.SG.Pf.Cnt.GlueSet IsGlueLat
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hl, hu, he⟩
    have hzmem : z ∈ Λ ⊓ (Submodule.span K {z}).restrictScalars (𝓞 K) := by
      rw [he]
      exact Submodule.mem_span_singleton_self z
    refine ⟨hl, hu, hzmem.1, fun c hc => ?_⟩
    have hcz : c • z ∈ Λ ⊓ (Submodule.span K {z}).restrictScalars (𝓞 K) :=
      ⟨hc, Submodule.smul_mem _ c (Submodule.mem_span_singleton_self z)⟩
    rw [he] at hcz
    obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.1 hcz
    refine ⟨o, ?_⟩
    rw [← algebraMap_smul K o z] at ho
    exact (smul_left_injective K hz ho)
  · rintro ⟨hl, hu, hzΛ, hp⟩
    refine ⟨hl, hu, ?_⟩
    ext y
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem]
    constructor
    · rintro ⟨hyΛ, hyU⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hyU
      obtain ⟨o, ho⟩ := hp c hyΛ
      rw [← ho, algebraMap_smul]
      exact Submodule.smul_mem _ o (Submodule.mem_span_singleton_self z)
    · intro hy
      obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hy
      refine ⟨Λ.smul_mem o hzΛ, ?_⟩
      rw [← algebraMap_smul K o z]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)

theorem isomFix_iff (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (g : V1 ≃ₗ[K] V1) :
    g ∈ Formalism.L2.SG.Pf.Cnt.isomFix h1 (Submodule.span K {z}) ↔ g ∈ hz h1 z := by
  constructor
  · rintro ⟨hg, hfix⟩
    exact ⟨hg, hfix z (Submodule.mem_span_singleton_self z)⟩
  · rintro ⟨hg, hfz⟩
    refine ⟨hg, fun u hu => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
    rw [map_smul, hfz]

theorem stabFix_eq (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (Λ : Submodule (𝓞 K) V1) :
    Formalism.L2.SG.Pf.Cnt.stabFix h1 (Submodule.span K {z}) Λ = stabZ h1 z Λ := by
  ext g
  exact and_congr (isomFix_iff h1 z g) Iff.rfl

end GluedLatticeMass

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
