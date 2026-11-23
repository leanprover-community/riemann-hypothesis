module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenRangeEqInterPreimageEtaleUnivOpenStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSurjectiveAffineChartBijectiveSectionsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem surjective_of_isProper_of_app_injective : ∀ (X Y : Scheme.{0}) (a : X ⟶ Y), IsProper a → (∀ V : Y.Opens, Function.Injective (a.app V).hom) → Function.Surjective a := by
  intro X Y a ha hinj
  haveI := ha
  by_contra hne
  simp only [Function.Surjective, not_forall] at hne
  obtain ⟨y, hy⟩ := hne
  have hcl : IsClosed (Set.range a) := by
    simpa using a.isClosedMap _ isClosed_univ
  let V : Y.Opens := ⟨(Set.range a)ᶜ, hcl.isOpen_compl⟩
  haveI : Nonempty V := ⟨⟨y, fun ⟨p, hp⟩ => hy ⟨p, hp⟩⟩⟩
  have hV : a ⁻¹ᵁ V = ⊥ := by
    ext p
    simp [V]
  haveI : Subsingleton Γ(X, a ⁻¹ᵁ V) :=
    CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hV)
  have : Subsingleton Γ(Y, V) := (hinj V).subsingleton
  exact not_subsingleton Γ(Y, V) this

theorem isolated_in_coordinate_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∃ O : U.left.Opens, x ∈ O ∧ ∀ u ∈ O, τ u = τ x → u = x := by
  intro R _ _ _ hR S X π U a b g τ c hπp hπs hπΓ hUf hUs hap haV hτ hc1 hc2 hc x hxc hxR hinj hsurj
  set F := pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π with hF
  have hw : (a.fiberι x ≫ c) ≫ F = (a.fiberToSpecResidueField x ≫ Spec.map (τ.residueFieldMap x)) ≫
      (𝔸(Fin g; Sp R)).fromSpecResidueField (τ x) := by
    rw [Category.assoc, hF, hc1, ← Category.assoc, Scheme.Hom.fiber_fac, Category.assoc, Category.assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  let φ : a.fiber x ⟶ F.fiber (τ x) := pullback.lift _ _ hw
  have hφ1 : φ ≫ F.fiberι (τ x) = a.fiberι x ≫ c := pullback.lift_fst _ _ _
  have hφ2 : φ ≫ F.fiberToSpecResidueField (τ x) = a.fiberToSpecResidueField x ≫ Spec.map (τ.residueFieldMap x) :=
    pullback.lift_snd _ _ _
  have hUO := GlobalTheory.T.proper_surjective_affine_chart_bijective_sections R hR S X π U a b g τ c hπp hπs hπΓ hUf hUs hap haV hτ hc1 hc2 hc x hxc hxR hinj hsurj φ hφ1 hφ2
  haveI : IsPreimmersion (F.fiberι (τ x)) := inferInstance
  obtain ⟨W, hW⟩ := GlobalTheory.T.exists_open_range_eq_inter_preimage_etale_univOpen X _ _ _ c (F.fiberι (τ x)) (a.fiberι x) φ hc inferInstance hUO hφ1.symm
  rw [Scheme.Hom.range_fiberι, Scheme.Hom.range_fiberι] at hW
  have hs := surjective_of_isProper_of_app_injective X U.left a hap (fun V => (haV V).1)
  haveI := hap
  refine ⟨⟨(a '' (W : Set X)ᶜ)ᶜ, (a.isClosedMap _ W.isOpen.isClosed_compl).isOpen_compl⟩, ?_, ?_⟩
  · rintro ⟨p, hp, hpx⟩
    have : p ∈ a ⁻¹' {x} := hpx
    rw [hW] at this
    exact hp this.1
  · intro u hu hτu
    obtain ⟨p, rfl⟩ := hs u
    by_cases hp : p ∈ W
    · have : p ∈ (W : Set X) ∩ c ⁻¹' (F ⁻¹' {τ x}) := by
        refine ⟨hp, ?_⟩
        show F (c p) = τ x
        rw [← Scheme.Hom.comp_apply, hF, hc1, Scheme.Hom.comp_apply, hτu]
      rw [← hW] at this
      exact this
    · exact absurd ⟨p, hp, rfl⟩ hu

end GlobalTheory.Mum
