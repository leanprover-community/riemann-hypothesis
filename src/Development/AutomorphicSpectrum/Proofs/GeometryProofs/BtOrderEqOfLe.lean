import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinitePointExtendsSection

section
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem valAt_app_pullback {B : Type} [CommRing B] {X Y : Scheme.{0}}
    (x : Spec (CommRingCat.of B) ⟶ X) (φ : X ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U)) (h' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U) (s : Γ(Y, U)) :
    valAt x (φ ⁻¹ᵁ U) h (φ.app U s) = valAt (x ≫ φ) U h' s := by
  simp only [valAt, Scheme.Hom.comp_appLE]
  rfl

theorem valAt_congr_point {B : Type} [CommRing B] {X : Scheme.{0}}
    {x y : Spec (CommRingCat.of B) ⟶ X} (e : x = y) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt x U h s = valAt y U h' s := by
  subst e
  rfl

theorem QFGroup.regularAt_translate :
    ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T)
      (σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G) (t : T), toUnit (genPt R) ≫ σ = Γ.pt t →
      ∀ (f : T → FractionRing R) (g : Γ.G.left),
        Γ.RegularAt f (((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left g) → Γ.RegularAt (fun h => f (t * h)) g := by
  intro R _ _ T _ _ Γ σ t ht f g ⟨U, hgU, s, hs⟩
  have key : ∀ h : T, Γ.pt h ≫ ((toUnit Γ.G ≫ σ) * 𝟙 Γ.G) = Γ.pt (t * h) := by
    intro h
    rw [MonObj.comp_mul, map_mul, ← ht, Category.comp_id, ← Category.assoc, comp_toUnit]
  refine ⟨((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left ⁻¹ᵁ U, hgU, ((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left.app U s, ?_⟩
  intro h hh
  have e : (Γ.pt h).left ≫ ((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left = (Γ.pt (t * h)).left := by
    rw [← key h]; rfl
  have h' : ⊤ ≤ ((Γ.pt h).left ≫ ((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left) ⁻¹ᵁ U := hh
  have h'' : ⊤ ≤ (Γ.pt (t * h)).left ⁻¹ᵁ U := e ▸ h'
  rw [valAt_app_pullback _ _ U hh h', valAt_congr_point e U h' h'' s]
  exact hs (t * h) h''

end GlobalTheory.CompanionTheory.Ar.BT
end

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_at_translate : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G) (t : T), toUnit (genPt R) ≫ σ = Γ.pt t → ∀ (f : T → FractionRing R) (g : Γ.G.left), Γ.RegularAt f (((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left g) → Γ.RegularAt (fun h => f (t * h)) g := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.BT.QFGroup.regularAt_translate
end

section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_point_extends_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), IsFinite (U.ι ≫ Γ.G.hom) → ∀ t, ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U → ∃ σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G, (∀ z, σ.left z ∈ U) ∧ toUnit (genPt R) ≫ σ = Γ.pt t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.exists_section_of_generic_point | exact GlobalTheory.CompanionTheory.Ar.BT.exists_section_of_generic_point | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.exists_section_of_generic_point <;> assumption)
end

section
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT.Transl

theorem translates_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U U' : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.IsFinOpenSub U' → U' ≤ U → ∀ g ∈ U, ∃ (σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G) (t : T), toUnit (genPt R) ≫ σ = Γ.pt t ∧ ((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left g ∈ U' := by
  intro R _ _ _ T _ _ Γ U U' hU hU' _ g hg
  haveI := Γ.flat
  haveI := Γ.separated
  let p0 : Spec (CommRingCat.of R) := ⟨⊥, Ideal.bot_prime⟩
  have hp0 : p0 ⤳ Γ.G.hom g := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨g', hg'g, hg'⟩ := Flat.generalizingMap Γ.G.hom hp0
  obtain ⟨s, x, hx⟩ := Γ.pt_onto g' (by rw [hg'])
  have hsU : (Γ.pt s).left x ∈ U := by
    rw [hx]; exact hg'g.mem_open U.isOpen hg
  have hsub : ∀ z z' : Spec (CommRingCat.of (FractionRing R)), z = z' := fun z z' =>
    PrimeSpectrum.ext (by
      haveI := z.isPrime
      haveI := z'.isPrime
      rw [Ideal.eq_bot_of_prime z.asIdeal, Ideal.eq_bot_of_prime z'.asIdeal])
  have hsall : ∀ z, (Γ.pt s).left z ∈ U := fun z => hsub x z ▸ hsU
  have hinvU : ∀ z, (Γ.pt s⁻¹).left z ∈ U := by
    rw [map_inv]; exact hU.inv _ _ hsall
  obtain ⟨σ, -, hσ⟩ := GlobalTheory.T.finite_point_extends_section R T Γ U hU.finite s⁻¹ (fun z _ => hinvU z)
  refine ⟨σ, s⁻¹, hσ, ?_⟩
  set τ := (toUnit Γ.G ≫ σ) * 𝟙 Γ.G with hτ
  have hτpt : Γ.pt s ≫ τ = 1 := by
    rw [hτ, Hom.mul_def, ← Category.assoc, comp_lift, ← Category.assoc, comp_toUnit, hσ,
      Category.comp_id, ← Hom.mul_def, ← map_mul, inv_mul_cancel, map_one]
  have hτx : τ.left ((Γ.pt s).left x) = (η[Γ.G]).left ((toUnit (genPt R)).left x) := by
    have h1 : (Γ.pt s ≫ τ).left = (toUnit (genPt R) ≫ η[Γ.G]).left := by
      rw [hτpt, Hom.one_def]
    rw [Over.comp_left, Over.comp_left] at h1
    have h2 := congrArg (fun h => h x) h1
    simpa using h2
  have hw : (η[Γ.G]).left ≫ Γ.G.hom = 𝟙 _ := Over.w _
  haveI : UniversallyClosed ((η[Γ.G]).left ≫ Γ.G.hom) := by rw [hw]; infer_instance
  haveI : UniversallyClosed (η[Γ.G]).left :=
    UniversallyClosed.of_comp_of_isSeparated _ Γ.G.hom
  have hcl : IsClosed (Set.range (η[Γ.G]).left) := by
    have h := (η[Γ.G]).left.isClosedMap _ isClosed_univ
    rwa [Set.image_univ] at h
  have hspec : τ.left ((Γ.pt s).left x) ⤳ τ.left g := by
    rw [hx]; exact hg'g.map τ.left.continuous
  have hsubset : ({τ.left ((Γ.pt s).left x)} : Set Γ.G.left) ⊆ Set.range (η[Γ.G]).left :=
    Set.singleton_subset_iff.2 ⟨_, hτx.symm⟩
  have hmem : τ.left g ∈ Set.range (η[Γ.G]).left :=
    closure_minimal hsubset hcl (specializes_iff_mem_closure.1 hspec)
  obtain ⟨z, hz⟩ := hmem
  rw [← hz]
  exact hU'.one z

end GlobalTheory.CompanionTheory.Ar.BT.Transl
end

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_into_smaller_open : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U U' : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.IsFinOpenSub U' → U' ≤ U → ∀ g ∈ U, ∃ (σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G) (t : T), toUnit (genPt R) ≫ σ = Γ.pt t ∧ ((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left g ∈ U' := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.BT.Transl.translates_cover
end

section
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem QFGroup.btSet_eq_of_le (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U U' : Γ.G.left.Opens)
    (hU : Γ.IsFinOpenSub U) (hU' : Γ.IsFinOpenSub U') (hle : U' ≤ U) :
    Γ.btSet U = Γ.btSet U' := by
  apply Set.Subset.antisymm
  · intro f hf t g hg
    exact hf t g (hle hg)
  · intro f hf s g hg
    obtain ⟨σ, t, hσ, hmem⟩ := GlobalTheory.T.translate_into_smaller_open R T Γ U U' hU hU' hle g hg
    have hreg := hf (s * t⁻¹) _ hmem
    have key := GlobalTheory.T.regular_at_translate R T Γ σ t hσ
      (fun h => algebraMap R (FractionRing R) (f (s * t⁻¹ * h))) g hreg
    have heq : (fun h => algebraMap R (FractionRing R) (f (s * t⁻¹ * (t * h)))) =
        fun h => algebraMap R (FractionRing R) (f (s * h)) := by
      funext h
      congr 2
      rw [_root_.mul_assoc, inv_mul_cancel_left]
    simpa only [heq] using key

theorem QFGroup.btOrder_eq_of_le : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U U' : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.IsFinOpenSub U' → U' ≤ U → Γ.btOrder U = Γ.btOrder U' := by
  intro R _ _ _ T _ _ Γ U U' hU hU' hle
  unfold QFGroup.btOrder
  rw [QFGroup.btSet_eq_of_le R T Γ U U' hU hU' hle]

end GlobalTheory.CompanionTheory.Ar.BT
end

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.btOrder_eq_of_le_of_isFinOpenSub : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U U' : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.IsFinOpenSub U' → U' ≤ U → Γ.btOrder U = Γ.btOrder U' := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.BT.QFGroup.btOrder_eq_of_le
end
