module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKMOne
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsCompactDualHaar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PolyGrowthStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OnbPerp

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

open MeasureTheory
open scoped Pointwise

theorem packing_set_covolume_le :
    ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) (Γ : Subgroup H), Countable Γ → ∃ F : Set H, MeasurableSet F ∧ covolume Γ H ν ≤ ν F ∧ ∀ γ ∈ Γ, ∀ y ∈ F, γ * y ∈ F → γ = 1 := by
  intro H _ _ _ ν Γ _
  classical
  by_cases hF : HasFundamentalDomain Γ H ν
  swap
  · refine ⟨∅, MeasurableSet.empty, ?_, ?_⟩
    · simp [covolume, hF]
    · intro γ _ y hy; exact absurd hy (Set.notMem_empty y)
  · set s := hF.ExistsIsFundamentalDomain.choose with hs_def
    have hs : IsFundamentalDomain Γ s ν := hF.ExistsIsFundamentalDomain.choose_spec
    have hcov : covolume Γ H ν = ν s := by simp [covolume, hF, hs_def]
    obtain ⟨t, hts, htm, hte⟩ := hs.nullMeasurableSet.exists_measurable_subset_ae_eq
    have hsmul : ∀ g : Γ, (g • t : Set H) = (fun y => (g : H)⁻¹ * y) ⁻¹' t := by
      intro g; ext y
      simp [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]
    have hmeas : ∀ g : Γ, MeasurableSet (g • t : Set H) := by
      intro g; rw [hsmul g]; exact (measurable_const_mul _) htm
    let U : Set H := ⋃ g : {g : Γ // g ≠ 1}, (g.1 • t : Set H)
    have hUm : MeasurableSet U := MeasurableSet.iUnion (fun g => hmeas g.1)
    have hnull : ν (t ∩ U) = 0 := by
      rw [Set.inter_iUnion]
      refine measure_iUnion_null (fun g => ?_)
      have h1 := hs.aedisjoint (Ne.symm g.2 : (1 : Γ) ≠ g.1)
      have h2 : ν ((1 : Γ) • s ∩ g.1 • s) = 0 := h1
      rw [one_smul] at h2
      exact measure_mono_null (Set.inter_subset_inter hts (Set.smul_set_mono hts)) h2
    refine ⟨t \ U, htm.diff hUm, ?_, ?_⟩
    · rw [hcov, ← Set.sdiff_self_inter, measure_sdiff_null hnull]
      exact (measure_congr hte).ge
    · intro γ hγ y hy hγy
      by_contra hne
      have hne' : (⟨γ, hγ⟩ : Γ) ≠ 1 := fun h => hne (congrArg Subtype.val h)
      apply hγy.2
      refine Set.mem_iUnion.2 ⟨⟨⟨γ, hγ⟩, hne'⟩, ?_⟩
      exact ⟨y, hy.1, rfl⟩

end GlobalTheory
