module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.PointDescentFactorization

theorem exists_finset_factor {R Ω : Type} [CommRing R] [Field Ω] (g : ℚ →+* R) (hg : g.FiniteType)
    (φ : R →+* Ω) :
    ∃ s : Finset Ω, ∀ (k : Type) [Field k] (β : k →+* Ω), (↑s : Set Ω) ⊆ Set.range β →
      ∃ ψ : R →+* k, β.comp ψ = φ := by
  classical
  letI : Algebra ℚ R := g.toAlgebra
  have hft : Algebra.FiniteType ℚ R := hg
  obtain ⟨t, ht⟩ := hft.out
  refine ⟨t.image φ, fun k _ β hs => ?_⟩
  have hq : ∀ q : ℚ, φ (g q) ∈ β.fieldRange := by
    intro q
    have h := map_ratCast (φ.comp g) q
    rw [Rat.cast_id, RingHom.comp_apply] at h
    rw [h]
    exact SubfieldClass.ratCast_mem _ q
  have hall : ∀ x : R, φ x ∈ β.fieldRange := by
    intro x
    have hx : x ∈ Algebra.adjoin ℚ (t : Set R) := ht ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hs (by simpa using ⟨x, hx, rfl⟩)
    | algebraMap q => exact hq q
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨(β.rangeRestrictFieldEquiv.symm.toRingHom).comp (φ.codRestrict β.fieldRange hall), ?_⟩
  ext x
  have h := β.rangeRestrictFieldEquiv.apply_symm_apply ⟨φ x, hall x⟩
  exact congrArg Subtype.val h

theorem point_descends {Ω : Type} [Field Ω] {X : Scheme}
    (p : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℚ) [LocallyOfFiniteType p]
    (a : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp Ω ⟶ X) :
    ∃ s : Finset Ω, ∀ (k : Type) [Field k] (β : k →+* Ω), (↑s : Set Ω) ⊆ Set.range (⇑β : k → Ω) →
      ∃ b : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k ⟶ X, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap β ≫ b = a := by
  let x₀ : (Spec (CommRingCat.of Ω)) := IsLocalRing.closedPoint Ω
  obtain ⟨R, j, hj, hx⟩ : ∃ (R : CommRingCat.{0}) (j : Spec R ⟶ X), IsOpenImmersion j ∧
      a x₀ ∈ Set.range j := by
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := a x₀) (U := ⊤) trivial
    exact ⟨_, hU.fromSpec, inferInstance, by rw [hU.range_fromSpec]; exact hxU⟩
  have hr : Set.range a ⊆ Set.range j := by
    rintro _ ⟨y, rfl⟩
    have : y = x₀ := Subsingleton.elim (α := PrimeSpectrum Ω) _ _
    rw [this]; exact hx
  let a' := IsOpenImmersion.lift j a hr
  have ha' : a' ≫ j = a := IsOpenImmersion.lift_fac j a hr
  obtain ⟨φ, hφ⟩ := Spec.map_surjective a'
  obtain ⟨g, hg⟩ := Spec.map_surjective (j ≫ p)
  have hl : LocallyOfFiniteType (Spec.map g) := by rw [hg]; infer_instance
  have hft : g.hom.FiniteType := HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType).mp hl
  obtain ⟨s, hs⟩ := exists_finset_factor g.hom hft φ.hom
  refine ⟨s, fun k _ β hβ => ?_⟩
  obtain ⟨ψ, hψ⟩ := hs k β hβ
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ j, ?_⟩
  rw [← ha', ← hφ, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext1
  exact hψ

end GlobalTheory.PointDescentFactorization
