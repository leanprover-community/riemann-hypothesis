module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ImmersionBiholo


open Topology in
theorem ker_fderiv_comp_biholo : ∀ (e : ℕ) (X₁ X₂ V : Type) [TopologicalSpace X₁] [TopologicalSpace X₂] [NormedAddCommGroup V] [NormedSpace ℂ V] (A₁ : ReciprocityTheory.AnForm.M.FinHolAtlas e X₁) (A₂ : ReciprocityTheory.AnForm.M.FinHolAtlas e X₂) (π : X₁ → X₂) (inv : X₂ → X₁), ReciprocityTheory.AnForm.M.HoloMap A₁ A₂ π → ReciprocityTheory.AnForm.M.HoloMap A₂ A₁ inv → Function.Bijective π → (∀ x, inv (π x) = x) → ∀ (Φ : X₁ → V) (x : X₂) (j₁ : Fin A₁.n) (j₂ : Fin A₂.n), inv x ∈ (A₁.chart j₁).source → x ∈ (A₂.chart j₂).source → DifferentiableAt ℂ (fun v => Φ ((A₁.chart j₁).symm v)) (A₁.chart j₁ (inv x)) → (fderiv ℂ (fun v => Φ ((A₁.chart j₁).symm v)) (A₁.chart j₁ (inv x))).ker = ⊥ → (fderiv ℂ (fun v => Φ (inv ((A₂.chart j₂).symm v))) (A₂.chart j₂ x)).ker = ⊥ := by
  intro e X₁ X₂ V _ _ _ _ A₁ A₂ π inv hπ hinv hbij hleft Φ x j₁ j₂ hx₁ hx₂ hdiff hker
  have hright : ∀ y, π (inv y) = y := fun y => by
    obtain ⟨w, rfl⟩ := hbij.2 y
    rw [hleft]
  have hy : A₂.chart j₂ x ∈ (A₂.chart j₂).target := (A₂.chart j₂).map_source hx₂
  have hsy : (A₂.chart j₂).symm (A₂.chart j₂ x) = x := (A₂.chart j₂).left_inv hx₂
  have hz : A₁.chart j₁ (inv x) ∈ (A₁.chart j₁).target := (A₁.chart j₁).map_source hx₁
  have hsz : (A₁.chart j₁).symm (A₁.chart j₁ (inv x)) = inv x := (A₁.chart j₁).left_inv hx₁
  have hτ : DifferentiableAt ℂ (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x) := by
    have hmem : A₂.chart j₂ x ∈ (A₂.chart j₂).target ∩
        ⇑(A₂.chart j₂).symm ⁻¹' (inv ⁻¹' (A₁.chart j₁).source) := by
      refine ⟨hy, ?_⟩
      show inv ((A₂.chart j₂).symm (A₂.chart j₂ x)) ∈ (A₁.chart j₁).source
      rw [hsy]
      exact hx₁
    exact (hinv.2 j₂ j₁ _ hmem).differentiableAt
  have hσ : DifferentiableAt ℂ (⇑(A₂.chart j₂) ∘ π ∘ ⇑(A₁.chart j₁).symm) (A₁.chart j₁ (inv x)) := by
    have hmem : A₁.chart j₁ (inv x) ∈ (A₁.chart j₁).target ∩
        ⇑(A₁.chart j₁).symm ⁻¹' (π ⁻¹' (A₂.chart j₂).source) := by
      refine ⟨hz, ?_⟩
      show π ((A₁.chart j₁).symm (A₁.chart j₁ (inv x))) ∈ (A₂.chart j₂).source
      rw [hsz, hright]
      exact hx₂
    exact (hπ.2 j₁ j₂ _ hmem).differentiableAt
  have hev : ∀ᶠ v in 𝓝 (A₂.chart j₂ x),
      v ∈ (A₂.chart j₂).target ∧ inv ((A₂.chart j₂).symm v) ∈ (A₁.chart j₁).source := by
    refine Filter.Eventually.and ((A₂.chart j₂).open_target.mem_nhds hy) ?_
    have hc : ContinuousAt (inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x) :=
      hinv.1.continuousAt.comp ((A₂.chart j₂).continuousAt_symm hy)
    have hs : (A₁.chart j₁).source ∈ 𝓝 ((inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x)) := by
      rw [Function.comp_apply, hsy]
      exact (A₁.chart j₁).open_source.mem_nhds hx₁
    exact hc.preimage_mem_nhds hs
  have hτz : (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x) = A₁.chart j₁ (inv x) := by
    simp only [Function.comp_apply, hsy]
  have hσ' : DifferentiableAt ℂ (⇑(A₂.chart j₂) ∘ π ∘ ⇑(A₁.chart j₁).symm)
      ((⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x)) := by
    rw [hτz]
    exact hσ
  have hid : (⇑(A₂.chart j₂) ∘ π ∘ ⇑(A₁.chart j₁).symm) ∘ (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm)
      =ᶠ[𝓝 (A₂.chart j₂ x)] id := by
    filter_upwards [hev] with v hv
    simp only [Function.comp_apply, id_eq]
    rw [(A₁.chart j₁).left_inv hv.2, hright, (A₂.chart j₂).right_inv hv.1]
  have hcomp : (fderiv ℂ (⇑(A₂.chart j₂) ∘ π ∘ ⇑(A₁.chart j₁).symm)
      ((⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x))).comp
      (fderiv ℂ (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x))
      = ContinuousLinearMap.id ℂ (Fin e → ℂ) := by
    rw [← fderiv_comp _ hσ' hτ, hid.fderiv_eq, fderiv_id]
  have hτinj : ∀ w, fderiv ℂ (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x) w = 0 → w = 0 := by
    intro w hw
    have h := congrArg (fun L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ) => L w) hcomp
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hw, map_zero] at h
    exact h.symm
  have hdiff' : DifferentiableAt ℂ (fun v => Φ ((A₁.chart j₁).symm v))
      ((⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x)) := by
    rw [hτz]
    exact hdiff
  have hker' : (fderiv ℂ (fun v => Φ ((A₁.chart j₁).symm v))
      ((⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x))).ker = ⊥ := by
    rw [hτz]
    exact hker
  have hfeq : (fun v => Φ (inv ((A₂.chart j₂).symm v))) =ᶠ[𝓝 (A₂.chart j₂ x)]
      (fun v => Φ ((A₁.chart j₁).symm v)) ∘ (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) := by
    filter_upwards [hev] with v hv
    simp only [Function.comp_apply]
    rw [(A₁.chart j₁).left_inv hv.2]
  rw [hfeq.fderiv_eq, fderiv_comp _ hdiff' hτ, eq_bot_iff]
  intro w hw
  rw [Submodule.mem_bot]
  apply hτinj
  have h1 : fderiv ℂ (⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x) w ∈
      (fderiv ℂ (fun v => Φ ((A₁.chart j₁).symm v))
        ((⇑(A₁.chart j₁) ∘ inv ∘ ⇑(A₂.chart j₂).symm) (A₂.chart j₂ x))).ker := hw
  rw [hker'] at h1
  exact h1

end GlobalTheory.CompanionTheory.Ar.ImmersionBiholo
