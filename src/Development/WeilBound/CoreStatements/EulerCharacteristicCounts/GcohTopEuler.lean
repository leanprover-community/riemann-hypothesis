import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmp
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohField
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohDefs
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohTate
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohFin
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.EulerCharGaloisOfCardEq

section
open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace PositivityTheory.LocalTateOrthogonality.Gcoh

theorem cycKSpec : Formalism.GaloisCohomology.CycKSpec := by
  intro l _ K r σ ζ hζ
  exact cyclotomicCharacter.spec l (MulSemiringAction.toRingAut _ (PadicAlgCl l) σ) ζ hζ

theorem gcMu : SgcMu := by
  intro l hl K r
  have : IsSepClosure ↥K (PadicAlgCl l) :=
    ⟨inferInstance, Algebra.isSeparable_tower_top_of_isSeparable ℚ_[l] K _⟩
  have hn : ((l ^ r : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hl.out.ne_zero)
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  obtain ⟨e⟩ := nonempty_addEquiv_galRootsOfUnity (K := K) (Ksep := PadicAlgCl l) hn
  refine ⟨e.symm, fun g m => ?_⟩
  have key : ∀ x : Additive (rootsOfUnity (l ^ r) (PadicAlgCl l)),
      (galRootsOfUnity.{0} ↥K (PadicAlgCl l) (l ^ r)).ρ g x =
        (Formalism.GaloisCohomology.cycK l K r g : ZMod (l ^ r)).val • x := by
    intro x
    rw [galRootsOfUnity_ρ_apply]
    apply Additive.toMul.injective
    rw [toMul_ofMul, toMul_nsmul]
    apply Subtype.ext
    apply Units.ext
    rw [coe_galRootsOfUnityHom_apply, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val]
    refine cycKSpec l K r g _ ?_
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 x.toMul.2, Units.val_one]
  refine Eq.trans ?_ (key _).symm
  refine Eq.trans ?_ (map_nsmul e.symm _ m)
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val]

end PositivityTheory.LocalTateOrthogonality.Gcoh
end

section
open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace PositivityTheory.LocalTateOrthogonality.Gcoh

theorem top_tate : Formalism.GaloisCohomology.LocalTateDualityK := tate_of gcRep gc0 gc1 gc2 gcField gcMu

theorem top_locfin : Formalism.GaloisCohomology.LocalFinitenessK := locfin_of gcField

end PositivityTheory.LocalTateOrthogonality.Gcoh
end

section
open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace PositivityTheory.LocalTateOrthogonality.Gcoh

theorem exists_card_eq_pow (l : ℕ) [hl : Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] : ∃ k, Nat.card M = l ^ k := by
  have h : IsPGroup l (Multiplicative M) := fun g => ⟨r, by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, ← Nat.cast_smul_eq_nsmul (ZMod (l ^ r)), ZMod.natCast_self,
      zero_smul]⟩
  exact (IsPGroup.iff_card (p := l) (G := Multiplicative M)).1 h

theorem euler_of (hRep : SgcRep) (h0 : Sgc0) (h1 : Sgc1) (h2 : Sgc2) (hF : SgcField) :
    Formalism.GaloisCohomology.LocalEulerCharK := by
  intro l hl K hK r M _ _ _ _ _ rho _ hrho
  obtain ⟨hsep, v, t, hloc, hcard⟩ := hF l K hK
  obtain ⟨A, hA, e, he⟩ := hRep _ _ M rho hrho
  obtain ⟨e0, -⟩ := h0 _ _ M rho A e he
  obtain ⟨e1, -⟩ := h1 _ _ M rho A e he
  obtain ⟨e2, -⟩ := h2 _ _ M rho A e he
  obtain ⟨k, hk⟩ := exists_card_eq_pow l r M
  have : Finite A := Finite.of_equiv M e.toEquiv
  have hA' : Nat.card A = l ^ k := (Nat.card_congr e.toEquiv).symm.trans hk
  have hne : ((Nat.card A : ℕ) : K) ≠ 0 := by
    rw [hA']
    exact Nat.cast_ne_zero.2 (pow_ne_zero _ hl.out.ne_zero)
  have hE := @card_cohomology_mul_div_eq K (PadicAlgCl l) _ v t hloc _ _ hsep A hA this hne
  have hfin := @finite_cohomology_localField K (PadicAlgCl l) _ v t hloc _ _ hsep A hA this hne 1
  rw [hA', hcard k] at hE
  rw [Nat.card_congr e0.toEquiv, Nat.card_congr e1.toEquiv, Nat.card_congr e2.toEquiv, hk]
  have hp1 : (Nat.card (cohomology A 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hp2 : (((l ^ k) ^ Module.finrank ℚ_[l] K : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.2 (pow_ne_zero _ (pow_ne_zero _ hl.out.ne_zero))
  apply Nat.cast_injective (R := ℚ)
  rw [Nat.cast_mul, Nat.cast_mul, (div_eq_iff hp1).1 hE]
  field_simp

end PositivityTheory.LocalTateOrthogonality.Gcoh
end

section
namespace PositivityTheory.LocalTateOrthogonality.Gcoh

theorem top_euler : Formalism.GaloisCohomology.LocalEulerCharK := euler_of gcRep gc0 gc1 gc2 gcField

end PositivityTheory.LocalTateOrthogonality.Gcoh
end
