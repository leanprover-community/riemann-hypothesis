import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChangeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticDatumTorsionLevelExt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticDatumTorsionLevelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticFormBasisChangeStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SiegelClassify

theorem spMap_spMap {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] (a : R →+* R₁) (b : R₁ →+* R₂) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

theorem isReduced_pullback_localization {o O : Type} [CommRing o] [CommRing O] [Algebra o O] (M : Submonoid o)
    [IsLocalization M O] {X : Scheme.{0}} (s : X ⟶ Sp o) [IsReduced X] :
    IsReduced (pullback s (spMap (algebraMap o O))) := by
  have h1 : IsPreimmersion (spMap (algebraMap o O)) := IsPreimmersion.of_isLocalization M
  have h2 : Flat (spMap (algebraMap o O)) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat O M)
  let π := pullback.fst s (spMap (algebraMap o O))
  have h3 : IsPreimmersion π := inferInstance
  have h4 : Flat π := inferInstance
  have : ∀ x, _root_.IsReduced ((pullback s (spMap (algebraMap o O))).presheaf.stalk x) := fun x => by
    have hs : Function.Surjective (π.stalkMap x) := π.stalkMap_surjective x
    have hf := Flat.stalkMap π x
    have hi : Function.Injective (π.stalkMap x) := by
      algebraize [(π.stalkMap x).hom]
      have : IsLocalHom (algebraMap (X.presheaf.stalk (π x)) ((pullback s (spMap (algebraMap o O))).presheaf.stalk x)) :=
        inferInstanceAs (IsLocalHom (π.stalkMap x).hom)
      have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (π x))
        (B := (pullback s (spMap (algebraMap o O))).presheaf.stalk x)
      exact FaithfulSMul.algebraMap_injective (X.presheaf.stalk (π x)) _
    exact isReduced_of_injective (RingEquiv.ofBijective (π.stalkMap x).hom ⟨hi, hs⟩).symm (RingEquiv.injective _)
  exact isReduced_of_isReduced_stalk _

theorem dense_generic {B O : Type} [CommRing B] [CommRing O] [IsDomain O] (z : B →+* O) (hz : Function.Injective z)
    {T : Scheme.{0}} (sT : T ⟶ Sp O) [Flat sT] : Dense {x : T | ((sT ≫ spMap z) x).asIdeal = ⊥} := by
  intro x
  have hη : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) ⤳ sT x :=
    (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨x', hx', e⟩ := Flat.generalizingMap sT hη
  refine closure_mono (Set.singleton_subset_iff.2 ?_) hx'.mem_closure
  change ((sT ≫ spMap z) x').asIdeal = ⊥
  rw [Scheme.Hom.comp_apply, e]
  change Ideal.comap z ⊥ = ⊥
  exact Ideal.comap_bot_of_injective z hz

theorem exists_localization (p k : ℕ) (hp : p.Prime) {o : Type} [CommRing o] [IsNoetherianRing o] (em : o →+* ℂ)
    (hem : Function.Injective em) (ζ : o) (hζ : em ζ = zeta k) :
    ∃ (M : Submonoid o) (i₀ : Localization M →+* ℂ) (z₀ : ZP p k →+* Localization M), Function.Injective i₀ ∧
      GlobalTheory.Models.IsInc (ZP p k).subtype i₀ z₀ ∧ GlobalTheory.Models.IsInc em i₀ (algebraMap o _) ∧
      ∀ (O : Type) [CommRing O] (i : O →+* ℂ) (z : ZP p k →+* O) (bb : o →+* O), Function.Injective i →
        GlobalTheory.Models.IsInc (ZP p k).subtype i z → GlobalTheory.Models.IsInc em i bb →
        ∃ ga : Localization M →+* O, ga.comp (algebraMap o _) = bb ∧ ga.comp z₀ = z := by
  let M : Submonoid o :=
    { carrier := {x | ∃ n : ℕ, n.Coprime p ∧ x = n}
      one_mem' := ⟨1, by simp, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨n, hn, rfl⟩ ⟨m, hm, rfl⟩
        exact ⟨n * m, Nat.Coprime.mul_left hn hm, by simp⟩ }
  have h0 : ∀ n : ℕ, n.Coprime p → (n : ℂ) ≠ 0 := fun n hn h => by
    have : n = 0 := by exact_mod_cast h
    subst this
    exact hp.one_lt.ne' (by simpa using hn)
  have hu : ∀ y : M, IsUnit (em y) := by
    rintro ⟨_, n, hn, rfl⟩
    simpa using h0 n hn
  let i₀ : Localization M →+* ℂ := IsLocalization.lift hu
  have hi₀ : ∀ x, i₀ (algebraMap o _ x) = em x := IsLocalization.lift_eq hu
  have hinj : Function.Injective i₀ := by
    rw [IsLocalization.lift_injective_iff]
    intro x y
    exact ⟨fun h => by rw [← hi₀, ← hi₀, h], fun h => by rw [hem h]⟩
  have hle : ZP p k ≤ i₀.range := by
    refine Subring.closure_le.2 ?_
    rintro x (rfl | ⟨n, hn, rfl⟩)
    · exact ⟨algebraMap o _ ζ, (hi₀ ζ).trans hζ⟩
    · obtain ⟨v, hv⟩ := (IsLocalization.map_units (Localization M) (⟨n, n, hn, rfl⟩ : M)).exists_right_inv
      refine ⟨v, ?_⟩
      have := congrArg i₀ hv
      rw [map_mul, hi₀, map_one, map_natCast] at this
      exact eq_inv_of_mul_eq_one_right this
  let e : Localization M ≃+* i₀.range := RingEquiv.ofBijective i₀.rangeRestrict
    ⟨fun x y h => hinj (congrArg Subtype.val h), i₀.rangeRestrict_surjective⟩
  let z₀ : ZP p k →+* Localization M := e.symm.toRingHom.comp (Subring.inclusion hle)
  have hz₀ : ∀ x, i₀ (z₀ x) = (ZP p k).subtype x := fun x =>
    congrArg Subtype.val (e.apply_symm_apply (Subring.inclusion hle x))
  refine ⟨M, i₀, z₀, hinj, hz₀, hi₀, fun O _ i z bb hi hz hb => ?_⟩
  have hv : ∀ y : M, IsUnit (bb y) := by
    rintro ⟨_, n, hn, rfl⟩
    refine IsUnit.of_mul_eq_one (z ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr ⟨n, hn, rfl⟩)⟩) (hi ?_)
    rw [map_mul, hz, hb, map_one]
    simpa using mul_inv_cancel₀ (h0 n hn)
  have hga : i.comp (IsLocalization.lift (S := Localization M) hv) = i₀ :=
    IsLocalization.ringHom_ext M (RingHom.ext fun x => by
      simp only [RingHom.comp_apply, IsLocalization.lift_eq]
      exact (hb x).trans (hi₀ x).symm)
  refine ⟨IsLocalization.lift hv, IsLocalization.lift_comp hv, RingHom.ext fun x => hi ?_⟩
  rw [hz, ← hz₀, ← hga]; rfl


end GlobalTheory.SiegelClassify
