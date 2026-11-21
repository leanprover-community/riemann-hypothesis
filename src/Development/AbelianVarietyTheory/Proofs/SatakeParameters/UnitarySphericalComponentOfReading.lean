import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RpowNegLeNormOfComponent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitarySphericalSatakeOfUnitarisableHasSatake
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitarySphericalSatakeMultisetMapInv

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalRepGL_exists_satakeParameters : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n), IsSpherical π.π → ∃ α : Fin n → ℂˣ, HasSatake π.π α := by
  first | exact @GlobalTheory.SatakeExists.main | exact GlobalTheory.SatakeExists.main | (intros; apply GlobalTheory.SatakeExists.main <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnitarySphericalSatake_of_unitarisable_hasSatake : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ), letI := GlobalTheory.LocalData.complRel w; haveI := GlobalTheory.LocalData.isLocalField w; ∀ (π : Irr (w.adicCompletion E) n) (α : Fin n → ℂˣ), HasSatake π.π α → IsUnitarisable π.π → GlobalTheory.RowSatakeBound.IsUnitarySatakeAt w n (Finset.univ.val.map fun i => (α i : ℂ)) := by
  first | exact @GlobalTheory.SatHecke.isUnitarySatakeAt_of_hasSatake | exact GlobalTheory.SatHecke.isUnitarySatakeAt_of_hasSatake | (intros; apply GlobalTheory.SatHecke.isUnitarySatakeAt_of_hasSatake <;> assumption)
end

section
open GlobalTheory.LatHecke GlobalTheory.RowSatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnitarySphericalSatakeMultiset_map_inv : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (β : Multiset ℂ), IsUnitarySatake O K r β → IsUnitarySatake O K r (β.map (·⁻¹)) := by
  first | exact @GlobalTheory.SatakeInv.isUnitarySatake_map_inv | exact GlobalTheory.SatakeInv.isUnitarySatake_map_inv | (intros; apply GlobalTheory.SatakeInv.isUnitarySatake_map_inv <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.SplitRead

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL
  GlobalTheory.SplitWeil GlobalTheory.RowTie

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem unitarySphericalComponent_of_reading : GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (T : WDTie N A)
      (S : Reading T), Laws S → RowUnit S → GlobalTheory.RowSatakeBound.UnitarySphericalComponent N A := by
  intro hBZ R H what₂ N A T S hL hU i σ hσ w hw hu
  have hloc := (S i w hw).locW σ hσ
  have hsph : IsSpherical ((S i w hw).row σ).π := by
    rw [← (hL i w hw).sph, ← hloc, ← T.unr]
    exact hu
  obtain ⟨α, hα⟩ := GlobalTheory.T.sphericalRepGL_exists_satakeParameters hBZ _ _ _ hsph
  have hfrob : A.frobEig (A.locW i σ w) =
      (Finset.univ.val.map fun j => (α j : ℂ)).map (·⁻¹) := by
    rw [T.frobEig w _ hu, hloc, (hL i w hw).sat _ _ α hα, Multiset.map_map]
    simp
  have h1 : GlobalTheory.RowSatakeBound.IsUnitarySatakeAt w R.r (Finset.univ.val.map fun j => (α j : ℂ)) :=
    GlobalTheory.T.isUnitarySphericalSatake_of_unitarisable_hasSatake H.E w R.r _ α hα (hU i w hw σ hσ)
  rw [hfrob]
  refine ⟨?_, ?_⟩
  · simpa [Multiset.map_map, Function.comp_def] using h1
  · have := GlobalTheory.RowSatakeBound.finite_residue w
    exact GlobalTheory.T.isUnitarySphericalSatakeMultiset_map_inv _ _ _ _ h1

end GlobalTheory.SplitRead
end
end
