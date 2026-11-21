import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomLiftOfFormallySmooth
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift

section
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem frobLift_localization :
    ∀ (p : ℕ) [Fact p.Prime] {B Kt : Type} [CommRing B] [CommRing Kt] [Algebra B Kt]
      (S : Submonoid B) [IsLocalization S Kt] (F : B →+* B), (p : B) ^ 2 = 0 →
      (∀ z, ∃ w, F z = z ^ p + p * w) →
      ∃ F' : Kt →+* Kt, (∀ b, F' (algebraMap B Kt b) = algebraMap B Kt (F b)) ∧
        ∀ z, ∃ w, F' z = z ^ p + p * w := by
  intro p _ B Kt _ _ _ S _ F hp2 hF
  have hunit : ∀ s : S, IsUnit ((algebraMap B Kt).comp F s) := by
    intro s
    obtain ⟨w, hw⟩ := hF (s : B)
    have hu : IsUnit (algebraMap B Kt (s : B) ^ p) :=
      (IsLocalization.map_units Kt s).pow p
    have hn : IsNilpotent ((p : Kt) * algebraMap B Kt w) := by
      refine ⟨2, ?_⟩
      have : (p : Kt) ^ 2 = 0 := by
        have := congrArg (algebraMap B Kt) hp2
        simpa using this
      rw [mul_pow, this, zero_mul]
    have := hn.isUnit_add_right_of_commute hu (Commute.all _ _)
    rw [add_comm] at this
    simpa [RingHom.comp_apply, hw, map_add, map_mul, map_pow, map_natCast] using this
  refine ⟨IsLocalization.lift hunit, fun b => by simp [IsLocalization.lift_eq], ?_⟩
  intro z
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective S z
  set z := IsLocalization.mk' Kt b s with hz
  set F' : Kt →+* Kt := IsLocalization.lift hunit
  have hF' : ∀ c, F' (algebraMap B Kt c) = algebraMap B Kt (F c) := fun c => by
    simp [F', IsLocalization.lift_eq]
  have hspec : z * algebraMap B Kt (s : B) = algebraMap B Kt b := IsLocalization.mk'_spec Kt b s
  obtain ⟨v, hv⟩ := hF b
  obtain ⟨u, hu⟩ := hF (s : B)
  have key : F' z * (algebraMap B Kt (s : B) ^ p + p * algebraMap B Kt u) =
      algebraMap B Kt b ^ p + p * algebraMap B Kt v := by
    have := congrArg F' hspec
    rw [map_mul, hF', hF', hu, hv] at this
    simpa [map_add, map_mul, map_pow, map_natCast] using this
  obtain ⟨t, ht⟩ := (IsLocalization.map_units Kt s).pow p
  refine ⟨(algebraMap B Kt v - F' z * algebraMap B Kt u) * ↑t⁻¹, ?_⟩
  have hzs : z ^ p * algebraMap B Kt (s : B) ^ p = algebraMap B Kt b ^ p := by
    rw [← mul_pow, hspec]
  have h1 : (F' z - z ^ p) * (t : Kt) = p * (algebraMap B Kt v - F' z * algebraMap B Kt u) := by
    rw [ht]; linear_combination key - hzs
  calc F' z = z ^ p + (F' z - z ^ p) * (t : Kt) * ↑t⁻¹ := by
        rw [mul_assoc, Units.mul_inv, mul_one]; ring
    _ = _ := by rw [h1]; ring

end GlobalTheory.DI
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI

theorem frobLift_stalk (p : ℕ) [Fact p.Prime] {Y : Scheme.{0}} (U : Y.Opens) (hU : IsAffineOpen U)
    (F₀ : Γ(Y, U) →+* Γ(Y, U)) (hp2 : (p : Γ(Y, U)) ^ 2 = 0) (hF₀ : ∀ z, ∃ w, F₀ z = z ^ p + p * w)
    (y : Y) (hy : y ∈ U) :
    ∃ F : Y.presheaf.stalk y →+* Y.presheaf.stalk y,
      (∀ b, F ((Y.presheaf.germ U y hy).hom b) = (Y.presheaf.germ U y hy).hom (F₀ b)) ∧
        ∀ z, ∃ w, F z = z ^ p + p * w := by
  letI : Algebra Γ(Y, U) (Y.presheaf.stalk y) := Y.presheaf.algebra_section_stalk (⟨y, hy⟩ : U)
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hy⟩
  exact frobLift_localization p (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl F₀ hp2 hF₀

theorem stalk_ringHom_ext {Y : Scheme.{0}} (U : Y.Opens) (hU : IsAffineOpen U) (y : Y) (hy : y ∈ U)
    {C : Type} [CommRing C] (f f' : Y.presheaf.stalk y →+* C)
    (h : ∀ b, f ((Y.presheaf.germ U y hy).hom b) = f' ((Y.presheaf.germ U y hy).hom b)) : f = f' := by
  letI : Algebra Γ(Y, U) (Y.presheaf.stalk y) := Y.presheaf.algebra_section_stalk (⟨y, hy⟩ : U)
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hy⟩
  exact IsLocalization.ringHom_ext (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (RingHom.ext h)

theorem exists_frobLift_stalk_of_etCoord :
    ∀ (p : ℕ) [Fact p.Prime] {Y : Scheme.{0}} (g : Y ⟶ Sp (ZMod (p ^ 2))) (U : Y.Opens) {n : ℕ} (t : Fin n → Γ(Y, U)), IsAffineOpen U → IsEtCoord g U t → ∀ (η : Y) (hη : η ∈ U), ∃ F : Y.presheaf.stalk η →+* Y.presheaf.stalk η, (∀ z, ∃ w, F z = z ^ p + p * w) ∧ (∀ l, F ((Y.presheaf.germ U η hη).hom (t l)) = (Y.presheaf.germ U η hη).hom (t l) ^ p) ∧ ∀ (y : Y), y ∈ U → ∀ (h : η ⤳ y), ∀ z ∈ stalkIm h, ∃ w ∈ stalkIm h, F z = z ^ p + p * w := by
  intro p _ Y g U n t hU ht η hη
  obtain ⟨F₀, hF₀, hFt⟩ := frob_lift_etale_chart p _ ht
  have hp2 : (p : Γ(Y, U)) ^ 2 = 0 := by
    have h := map_natCast (cstOn g U) (p ^ 2)
    rw [ZMod.natCast_self, map_zero] at h
    rw [← Nat.cast_pow, ← h]
  obtain ⟨F, hFg, hF⟩ := frobLift_stalk p U hU F₀ hp2 hF₀ η hη
  refine ⟨F, hF, fun l => ?_, fun y hy h z hz => ?_⟩
  · have := hFt l
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] at this
    rw [hFg, this, map_pow]
  · obtain ⟨F', hFg', hF'⟩ := frobLift_stalk p U hU F₀ hp2 hF₀ y hy
    have hs : ∀ b, (Y.presheaf.stalkSpecializes h).hom ((Y.presheaf.germ U y hy).hom b) =
        (Y.presheaf.germ U η hη).hom b := fun b =>
      congrArg (fun k => k.hom b) (Y.presheaf.germ_stalkSpecializes hy h)
    have hc : F.comp (Y.presheaf.stalkSpecializes h).hom =
        (Y.presheaf.stalkSpecializes h).hom.comp F' := by
      apply stalk_ringHom_ext U hU y hy
      intro b
      rw [RingHom.comp_apply, RingHom.comp_apply, hs, hFg, hFg', hs]
    obtain ⟨a, rfl⟩ := hz
    obtain ⟨w, hw⟩ := hF' a
    refine ⟨_, ⟨w, rfl⟩, ?_⟩
    have := congrArg (· a) hc
    simp only [RingHom.comp_apply] at this
    rw [this, hw, map_add, map_mul, map_pow, map_natCast]

end GlobalTheory.DI
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.exists_frobenius_lift_stalk : ∀ (p : ℕ) [Fact p.Prime] {Y : Scheme.{0}} (g : Y ⟶ Sp (ZMod (p ^ 2))) (U : Y.Opens) {n : ℕ} (t : Fin n → Γ(Y, U)), IsAffineOpen U → IsEtCoord g U t → ∀ (η : Y) (hη : η ∈ U), ∃ F : Y.presheaf.stalk η →+* Y.presheaf.stalk η, (∀ z, ∃ w, F z = z ^ p + p * w) ∧ (∀ l, F ((Y.presheaf.germ U η hη).hom (t l)) = (Y.presheaf.germ U η hη).hom (t l) ^ p) ∧ ∀ (y : Y), y ∈ U → ∀ (h : η ⤳ y), ∀ z ∈ stalkIm h, ∃ w ∈ stalkIm h, F z = z ^ p + p * w := by
  atlas_forward_decl _root_.GlobalTheory.DI.exists_frobLift_stalk_of_etCoord
end
