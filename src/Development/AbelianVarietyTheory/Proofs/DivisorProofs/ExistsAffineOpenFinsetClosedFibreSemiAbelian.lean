module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenDescendingFiniteFreeBaseChangeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSectionOfSmoothClosedFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenTranslationsMovingClosedPointsIntoOpenStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateBaseChangeAffineOpenStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_affine_open_of_finset_closedFibre :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ s : Finset G.left,
    (∀ x ∈ s, G.hom x = closedPoint R) → ∃ O : G.left.Opens, IsAffineOpen O ∧ ∀ x ∈ s, x ∈ O := by
  intro R _ _ _ hR G _ _ hG s hs
  haveI : IsNoetherianRing R := hR.1
  haveI : QuasiCompact G.hom := hG.quasiCompact
  haveI : IsSeparated G.hom := hG.separated
  haveI : Smooth G.hom := hG.smooth
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom

  rcases s.eq_empty_or_nonempty with hs0 | ⟨x₀, hx₀⟩
  · exact ⟨⊥, isAffineOpen_bot _, by simp [hs0]⟩

  have hcl : ∀ x : G.left, ∃ y ∈ closure ({x} : Set G.left), IsClosed ({y} : Set G.left) :=
    fun x => isClosed_closure.exists_closed_singleton ⟨x, subset_closure rfl⟩
  choose f hfx hfc using hcl
  have hsp : ∀ x, x ⤳ f x := fun x => specializes_iff_mem_closure.2 (hfx x)
  have hcp : IsClosed ({closedPoint R} : Set (Sp R)) := isClosed_singleton_closedPoint R
  have hfib : ∀ x ∈ s, G.hom (f x) = closedPoint R := by
    intro x hx
    have h1 : G.hom x ⤳ G.hom (f x) := (hsp x).map G.hom.continuous
    rw [hs x hx] at h1
    have h2 := specializes_iff_mem_closure.1 h1
    exact closure_minimal (subset_refl _) hcp h2
  classical
  let s' : Finset G.left := s.image f
  have hs' : ∀ y ∈ s', G.hom y = closedPoint R ∧ IsClosed ({y} : Set G.left) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨hfib x hx, hfc x⟩
  suffices H : ∃ O : G.left.Opens, IsAffineOpen O ∧ ∀ y ∈ s', y ∈ O by
    obtain ⟨O, hO, hyO⟩ := H
    exact ⟨O, hO, fun x hx => (hsp x).mem_open O.2 (hyO _ (Finset.mem_image_of_mem f hx))⟩

  obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp G.left.isBasis_affineOpens)
    (show x₀ ∈ (⊤ : G.left.Opens) from trivial)

  obtain ⟨O, ⟨u, huO, hu⟩, hmove⟩ :=
    GlobalTheory.T.exists_open_translations_moving_closedPoints_into_open R G hG V ⟨x₀, hxV, hs x₀ hx₀⟩ s' hs'

  obtain ⟨R₁, _, _, _, ρ, a, hfin, het, ha, haO⟩ :=
    GlobalTheory.T.exists_finiteEtale_section_of_smooth_closedFibre R hR G hG.smooth O ⟨u, huO, hu⟩
  letI : Algebra R R₁ := ρ.toAlgebra
  haveI : Module.Finite R R₁ := hfin.2.2
  haveI : Algebra.Etale R R₁ := het
  haveI : Module.Flat R R₁ := inferInstance
  haveI : Module.Free R R₁ := Module.free_of_flat_of_isLocalRing

  let A : Over.mk (spMap ρ) ⟶ G := Over.homMk a ha
  obtain ⟨W, hW, hzW⟩ := GlobalTheory.T.exists_affineOpen_translate_baseChange R R₁ ρ G V hV A

  have hpb : IsPullback (pullback.fst G.hom (spMap ρ)) (pullback.snd G.hom (spMap ρ)) G.hom
      (spMap (algebraMap R R₁)) := IsPullback.of_hasPullback G.hom (spMap ρ)
  refine GlobalTheory.T.exists_affineOpen_descending_finiteFreeBaseChange R R₁ G.left (pullback G.hom (spMap ρ)) G.hom (pullback.snd _ _) (pullback.fst _ _)
    hpb inferInstance inferInstance W hW s' ?_
  intro z hz
  let Ω := (pullback G.hom (spMap ρ)).residueField z
  let z' : Sp Ω ⟶ pullback G.hom (spMap ρ) := (pullback G.hom (spMap ρ)).fromSpecResidueField z
  have hz' : ∀ w, z' w = z := fun w => Scheme.fromSpecResidueField_apply z w
  let t : Sp Ω ⟶ Sp R := z' ≫ pullback.fst _ _ ≫ G.hom
  let x : Over.mk t ⟶ G := Over.homMk (z' ≫ pullback.fst _ _) (by simp [t])
  let a' : Over.mk t ⟶ G := Over.homMk (z' ≫ pullback.snd _ _ ≫ a)
    (by simp only [t, Over.mk_hom, Category.assoc, ha, pullback.condition])
  have hx : ∀ w, x.left w ∈ s' := by
    intro w
    show (z' ≫ pullback.fst _ _) w ∈ s'
    rw [Scheme.Hom.comp_apply, hz']
    exact hz
  have ha' : ∀ w, a'.left w ∈ O := by
    intro w
    show (z' ≫ pullback.snd _ _ ≫ a) w ∈ O
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact haO ⟨_, rfl⟩
  have hV' := hmove Ω t x a' hx ha'
  have := hzW Ω z' t x a' rfl rfl hV' (closedPoint Ω)
  first
    | exact (Scheme.fromSpecResidueField_apply z _) ▸ this
    | simpa only [hz'] using this
    | (convert this using 1; exact (hz' _).symm)

end GlobalTheory.Mum
