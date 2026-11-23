module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

namespace GlobalTheory.TopForm

theorem isFreeGen_formMap_of_formallyUnramified :
    ∀ {k A B : Type} [CommRing k] [CommRing A] [CommRing B] (α : k →+* A) (β : k →+* B) (ψ : A →+* B) (h : ψ.comp α = β) (n : ℕ), (letI := ψ.toAlgebra; Algebra.FormallyUnramified A B) → ∀ ω : Forms α n, IsFreeGen A ω → (∃ ω' : Forms β n, IsFreeGen B ω') → IsFreeGen B (TopForm.formMap n ψ h ω) := by
  intro k A B _ _ _ α β ψ h n hU ω hω hex
  obtain ⟨ω', hω'⟩ := hex
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ψ.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' h.symm
  haveI : Algebra.FormallyUnramified A B := hU
  have hspan : Submodule.span B (Set.range fun a : A => KaehlerDifferential.D k B (ψ a)) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨y, rfl⟩ :=
      (KaehlerDifferential.exact_mapBaseChange_map k A B x).mp (Subsingleton.elim _ _)
    induction y with
    | add _ _ h1 h2 => simpa only [map_add] using add_mem h1 h2
    | tmul b m =>
      rw [KaehlerDifferential.mapBaseChange_tmul]
      refine Submodule.smul_mem _ b ?_
      have hm : m ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hm using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, rfl⟩ := hx
        rw [KaehlerDifferential.map_D]
        exact Submodule.subset_span ⟨a, rfl⟩
      | zero => simp
      | add _ _ _ _ h1 h2 => simpa only [map_add] using add_mem h1 h2
      | smul a x _ hx =>
        rw [map_smul, ← algebraMap_smul B a]
        exact Submodule.smul_mem _ _ hx
  have hgen : Submodule.span B {formMap n ψ h ω} = ⊤ := by
    rw [eq_top_iff, ← exteriorPower.ιMulti_span_of_span B n (Omega β) hspan, Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    choose v hv using fun i => hw (Set.mem_range_self i)
    have e : exteriorPower.ιMulti B n w = formMap n ψ h (dForm α v) := by
      rw [formMap_dForm, dForm_eq]
      congr 1
      funext i
      exact (hv i).symm
    rw [SetLike.mem_coe, e, ← hω.repr_smul (dForm α v), map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hmem : ω' ∈ Submodule.span B {formMap n ψ h ω} := hgen ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hb := hω'.repr_smul (formMap n ψ h ω)
  rw [← hb] at hc ⊢
  refine hω'.smul_iff.mpr (IsUnit.of_mul_eq_one c ?_)
  refine hω'.1 ?_
  simp only [mul_comm _ c, mul_smul, one_smul]
  exact hc

end GlobalTheory.TopForm
