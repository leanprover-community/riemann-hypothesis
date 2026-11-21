import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAbelianTotallyRealExtPrescribedCompletion

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AbOverSubfield

theorem exists_place_between {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω]
    [Algebra F K] [Algebra K Ω] [Algebra F Ω] [IsScalarTower F K Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 K), IsPlaceOver A w := by
  have hint : ∀ x : 𝓞 K, algebraMap K Ω (x : K) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap K Ω (x : K)) :=
      (x.isIntegral_coe.map (algebraMap K Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 K →+* A := ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)).codRestrict A hint
  let P : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.comap (algebraMap (𝓞 F) (𝓞 K)) := by
    ext x
    rw [← hA x, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply F K Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP⟩

theorem exists_avoid {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hvT : v ∉ T) :
    ∃ c : 𝓞 F, c ∉ v.asIdeal ∧ ∀ u ∈ T, c ∈ u.asIdeal := by
  classical
  have : ∀ u ∈ T, ∃ a : 𝓞 F, a ∈ u.asIdeal ∧ a ∉ v.asIdeal := by
    intro u hu
    by_contra hc
    push_neg at hc
    have hle : u.asIdeal ≤ v.asIdeal := hc
    have := u.isMaximal.eq_of_le v.isPrime.ne_top hle
    exact hvT (HeightOneSpectrum.ext this ▸ hu)
  choose! a ha using this
  refine ⟨∏ u ∈ T, a u, ?_, fun u hu => ?_⟩
  · intro hmem
    obtain ⟨u, hu, hau⟩ := (Ideal.IsPrime.prod_mem_iff (hp := v.isPrime)).1 hmem
    exact (ha u hu).2 hau
  · rw [← Finset.mul_prod_erase T a hu]
    exact Ideal.mul_mem_right _ _ (ha u hu).1

end GlobalTheory.AbOverSubfield

namespace GlobalTheory.AbOverSubfield


end GlobalTheory.AbOverSubfield
