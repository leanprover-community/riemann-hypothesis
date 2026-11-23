module

public import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpens
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

universe u

private def affineOpensLePreimageCover {X' X : Scheme.{u}} (φ : X' ⟶ X) {ι : Type u}
    (U : ι → X.Opens) : Set X'.Opens :=
  {W : X'.Opens | IsAffineOpen W ∧ ∃ i, W ≤ φ ⁻¹ᵁ (U i)}

private theorem mem_affineOpensLePreimageCover {X' X : Scheme.{u}} (φ : X' ⟶ X) {ι : Type u}
    (U : ι → X.Opens) {W : X'.Opens} :
    W ∈ affineOpensLePreimageCover φ U ↔ IsAffineOpen W ∧ ∃ i, W ≤ φ ⁻¹ᵁ (U i) :=
  Iff.rfl

theorem exists_finite_affine_cover_subordinate {X' X : Scheme.{u}} [CompactSpace X']
    (φ : X' ⟶ X) {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤) :
    ∃ (κ : Type u) (_ : Finite κ) (V : κ → X'.Opens) (β : κ → ι),
      (∀ a, IsAffineOpen (V a)) ∧ (∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) ∧ iSup V = ⊤ := by
  classical
  have hSmem : ∀ W : affineOpensLePreimageCover φ U,
      IsAffineOpen (W : X'.Opens) ∧ ∃ i, (W : X'.Opens) ≤ φ ⁻¹ᵁ (U i) :=
    fun W => (mem_affineOpensLePreimageCover φ U).mp W.2
  have hcov : ∀ x : X', ∃ W : affineOpensLePreimageCover φ U, x ∈ ((W : X'.Opens) : Set X') := by
    intro x
    obtain ⟨i, hi⟩ : ∃ i, x ∈ (φ ⁻¹ᵁ (U i) : X'.Opens) := by
      have hx : φ.base x ∈ (⊤ : X.Opens) := by simp
      rw [← hU] at hx
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact ⟨i, hi⟩
    obtain ⟨W, hW, hxW, hWle⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X') hi
    have hW' : IsAffineOpen W := hW
    exact ⟨⟨W, (mem_affineOpensLePreimageCover φ U).mpr ⟨hW', i, hWle⟩⟩, hxW⟩
  have hcomp : IsCompact (Set.univ : Set X') := isCompact_univ
  obtain ⟨t, ht⟩ := hcomp.elim_finite_subcover
      (fun W : affineOpensLePreimageCover φ U => ((W : X'.Opens) : Set X'))
      (fun W => (W : X'.Opens).isOpen) (fun x _ => Set.mem_iUnion.mpr (hcov x))
  refine ⟨{W : affineOpensLePreimageCover φ U // W ∈ t}, inferInstance, fun a => (a.1 : X'.Opens),
    fun a => (hSmem a.1).2.choose, fun a => (hSmem a.1).1,
    fun a => (hSmem a.1).2.choose_spec, ?_⟩
  refine SetLike.coe_injective ?_
  rw [TopologicalSpace.Opens.coe_top]
  refine Set.eq_univ_of_forall fun x => ?_
  have hx := ht (Set.mem_univ x)
  simp only [Set.mem_iUnion, exists_prop] at hx
  obtain ⟨W, hWt, hxW⟩ := hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hWt⟩, hxW⟩

noncomputable def opensCoprodMapOfRefinement {X' X : Scheme.{u}} (φ : X' ⟶ X) {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) :
    sigmaOpens X' V ⟶ sigmaOpens X U :=
  Sigma.desc fun a =>
    φ.resLE (U (β a)) (V a) (hβ a) ≫ Sigma.ι (fun i => (U i).toScheme) (β a)

@[simp]
theorem sigmaι_opensCoprodMapOfRefinement {X' X : Scheme.{u}} (φ : X' ⟶ X) {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) (a : κ) :
    Sigma.ι (fun a => (V a).toScheme) a ≫ opensCoprodMapOfRefinement φ U V β hβ =
      φ.resLE (U (β a)) (V a) (hβ a) ≫ Sigma.ι (fun i => (U i).toScheme) (β a) := by
  simp [opensCoprodMapOfRefinement]

theorem opensCoprodMapOfRefinement_comp_sigmaOpensDesc {X' X : Scheme.{u}} (φ : X' ⟶ X) {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X'.Opens) (β : κ → ι)
    (hβ : ∀ a, V a ≤ φ ⁻¹ᵁ (U (β a))) :
    opensCoprodMapOfRefinement φ U V β hβ ≫ sigmaOpensDesc X U = sigmaOpensDesc X' V ≫ φ := by
  refine Limits.Sigma.hom_ext _ _ fun a => ?_
  rw [← Category.assoc, sigmaι_opensCoprodMapOfRefinement, Category.assoc, sigma_ι_sigmaOpensDesc,
    sigma_ι_sigmaOpensDesc_assoc]
  simp

private theorem resLE_eq_homOfLE_comp_restrict {X' X : Scheme.{u}} (φ : X' ⟶ X)
    (U : X.Opens) (V : X'.Opens) (e : V ≤ φ ⁻¹ᵁ U) :
    φ.resLE U V e = X'.homOfLE e ≫ φ ∣_ U := by
  rw [← cancel_mono U.ι]
  simp

private theorem smooth_resLE {X' X : Scheme.{u}} (φ : X' ⟶ X) [Smooth φ]
    (U : X.Opens) (V : X'.Opens) (e : V ≤ φ ⁻¹ᵁ U) :
    Smooth (φ.resLE U V e) := by
  rw [resLE_eq_homOfLE_comp_restrict]
  infer_instance

end FunctorialResolution.EmbeddedResolution
