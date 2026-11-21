import Mathlib
import GroundTheory.ArithmeticGeometry.EtaleCompletion.ArtinHenselCompletionNoetherian
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularSmooth
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularUFD
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAffineCompletionNormal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFormalFibresRegular
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAdicCompletionRegular

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem adicCompletion_isLocalRing_of_isMaximal {A : Type*} [CommRing A] (m : Ideal A) [m.IsMaximal]
    (fg : m.FG) : IsLocalRing (AdicCompletion m A) := by
  have := AdicCompletion.isMaximal_map_of_le m m le_rfl fg
  have := AdicCompletion.isAdicComplete_self m fg
  exact isLocalRing_of_isAdicComplete_maximal (m.map (algebraMap A (AdicCompletion m A)))

theorem AffineCompletionNormal.proof (hF : FlatNormalFibres.Statement) (hR : FormalFibresRegular.Statement) :
    AffineCompletionNormal.Statement := by
  intro σ _ I m hI hIC hm
  have : I.IsPrime := hI
  have : m.IsMaximal := hm
  have hloc := adicCompletion_isLocalRing_of_isMaximal m (Ideal.fg_of_isNoetherianRing m)
  refine hF (MvPolynomial σ ℂ ⧸ I) (AdicCompletion m (MvPolynomial σ ℂ ⧸ I)) inferInstance inferInstance hloc
    inferInstance inferInstance hIC fun P _ => ?_
  have := hR ℂ (MvPolynomial σ ℂ ⧸ I) inferInstance m hm P
  exact ⟨inferInstance, GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isIntegrallyClosed _⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem AdicCompletionRegular.proof : AdicCompletionRegular.Statement := by
  intro R _ hR M hM hreg
  let B := AdicCompletion M R
  have hfg : M.FG := Ideal.fg_of_isNoetherianRing M
  have : IsLocalRing B := adicCompletion_isLocalRing_of_isMaximal M hfg
  have : IsNoetherianRing B := GroundTheory.Arith.Etale.isNoetherianRing_adicCompletion R M
  have hmax : (M.map (algebraMap R B)).IsMaximal := AdicCompletion.isMaximal_map_of_le M M le_rfl hfg
  have hmB : M.map (algebraMap R B) = maximalIdeal B := IsLocalRing.eq_maximalIdeal hmax
  have hc : (M.map (algebraMap R B)).comap (algebraMap R B) = M :=
    (hM.eq_of_le (Ideal.comap_ne_top _ hmax.ne_top) Ideal.le_comap_map).symm
  have hunit : ∀ s : M.primeCompl, IsUnit (algebraMap R B s) := by
    intro s
    by_contra h
    have hs : algebraMap R B s ∈ maximalIdeal B := h
    rw [← hmB] at hs
    have hs' := Ideal.mem_comap.mpr hs
    rw [hc] at hs'
    exact s.2 hs'
  let _ : Algebra (Localization.AtPrime M) B :=
    (IsLocalization.lift (M := M.primeCompl) (S := Localization.AtPrime M) hunit).toAlgebra
  have : IsScalarTower R (Localization.AtPrime M) B :=
    IsScalarTower.of_algebraMap_eq fun r => (IsLocalization.lift_eq hunit r).symm
  have : Module.Flat (Localization.AtPrime M) B :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime M) M.primeCompl B).mpr inferInstance
  have hmap : (maximalIdeal (Localization.AtPrime M)).map (algebraMap (Localization.AtPrime M) B) =
      maximalIdeal B := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq, hmB]
  have : IsLocalHom (algebraMap (Localization.AtPrime M) B) := by
    refine ⟨fun a ha => ?_⟩
    by_contra h
    have h1 : algebraMap (Localization.AtPrime M) B a ∈ maximalIdeal B :=
      hmap ▸ Ideal.mem_map_of_mem _ (show a ∈ maximalIdeal (Localization.AtPrime M) from h)
    exact h1 ha
  exact GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.of_flat_of_map_maximalIdeal hmap

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
