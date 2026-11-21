import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import BuildAid.ForwardExisting

section
open CategoryTheory AlgebraicGeometry Limits

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem isProper_of_finite_cover (X S : Scheme.{0}) (p : X ⟶ S) (n : ℕ) (Y : Fin n → Scheme.{0})
    (π : ∀ i, Y i ⟶ X) (hsep : IsSeparated p) (hft : LocallyOfFiniteType p)
    (hprop : ∀ i, IsProper (π i ≫ p)) (hcov : ∀ x : X, ∃ i, x ∈ Set.range (π i)) :
    IsProper p := by
  have huc : UniversallyClosed p := by
    constructor
    intro X' Y' i₁ i₂ f' hpb Z hZ
    have hW : ∀ i, IsPullback (pullback.fst i₁ (π i) ≫ f') (pullback.snd i₁ (π i)) i₂
        (π i ≫ p) := fun i => (IsPullback.of_hasPullback i₁ (π i)).paste_horiz hpb
    have hc : ∀ i, IsClosedMap ⇑(pullback.fst i₁ (π i) ≫ f') := fun i =>
      @UniversallyClosed.universally_isClosedMap _ _ _ (hprop i).toUniversallyClosed
        _ _ _ _ _ (hW i)
    have key : ⇑f' '' Z =
        ⋃ i, ⇑(pullback.fst i₁ (π i) ≫ f') '' (⇑(pullback.fst i₁ (π i)) ⁻¹' Z) := by
      ext y
      simp only [Set.mem_image, Set.mem_iUnion, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨i, y', hy'⟩ := hcov (i₁ x)
        obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback x y' hy'.symm
        refine ⟨i, w, ?_, ?_⟩
        · rw [hw]
          exact hx
        · show f' (pullback.fst i₁ (π i) w) = f' x
          rw [hw]
      · rintro ⟨i, w, hw, rfl⟩
        exact ⟨pullback.fst i₁ (π i) w, hw, rfl⟩
    convert isClosed_iUnion_of_finite fun i =>
      hc i _ (hZ.preimage (pullback.fst i₁ (π i)).continuous) using 1
  exact @IsProper.mk _ _ _ hsep huc hft

end GlobalTheory.CompanionTheory.Ar.Approx
end

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_of_proper_cover : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (n : ℕ) (Y : Fin n → Scheme.{0}) (π : ∀ i, Y i ⟶ X), IsSeparated p → LocallyOfFiniteType p → (∀ i, IsProper (π i ≫ p)) → (∀ x : X, ∃ i, x ∈ Set.range (π i)) → IsProper p := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Approx.isProper_of_finite_cover
