module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.SurjectiveOfInjectiveOfInjective

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global GroundTheory.LocalField
  GroundTheory.LocalField.Abstract

open scoped GroundTheory.LocalField.Abstract

noncomputable section

section Degree

variable {K : FiniteSubfield} (w : HeightOneSpectrum (𝓞 K.1))

set_option maxHeartbeats 2000000 in
theorem eq_univ_of_unramifiedDegree
    (σ : Gal(AlgebraicClosure (w.adicCompletion K.1)/w.adicCompletion K.1))
    (hσ : unramifiedDegree (w.adicCompletion K.1) (AlgebraicClosure (w.adicCompletion K.1)) σ =
      Multiplicative.ofAdd 1)
    (E : Set Gal(AlgebraicClosure (w.adicCompletion K.1)/w.adicCompletion K.1)) (hE : IsClosed E)
    (hpow : ∀ k : ℤ, σ ^ k ∈ E)
    (hmul : ∀ g ∈ E, ∀ h, unramifiedDegree (w.adicCompletion K.1)
      (AlgebraicClosure (w.adicCompletion K.1)) h = 1 → g * h ∈ E) :
    E = Set.univ := by
  set deg := unramifiedDegree (w.adicCompletion K.1) (AlgebraicClosure (w.adicCompletion K.1))
  have hT : IsClosed (deg '' E) := (hE.isCompact.image continuous_unramifiedDegree).isClosed
  have hsub : (Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ̂)) : Set (Multiplicative ℤ̂)) ⊆ deg '' E := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ⟨σ ^ k, hpow k, by rw [map_zpow, hσ]⟩
  have huniv : deg '' E = Set.univ := by
    have hd := dense_zpowers_ofAdd_one.mono hsub
    rw [← hT.closure_eq, hd.closure_eq]
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨e, he, hde⟩ : deg x ∈ deg '' E := by
    rw [huniv]
    exact Set.mem_univ _
  have hx : x = e * (e⁻¹ * x) := by group
  rw [hx]
  refine hmul e he _ ?_
  rw [map_mul, map_inv, hde, inv_mul_cancel]

end Degree

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (ιs : LocalEmbeddings K)
  (v : {v : HeightOneSpectrum (𝓞 K.1) // v ∉ S})

instance t2Space_galUnramifiedOutside : T2Space (galUnramifiedOutside K.1 (AlgebraicClosure ℚ) S) :=
  galois_t2Space K.1 (maxUnramifiedOutside K.1 (AlgebraicClosure ℚ) S)

instance compactSpace_range_gsDecomp : CompactSpace (gsDecomp K S ιs v).range := by
  refine isCompact_iff_compactSpace.mp ?_
  rw [MonoidHom.coe_range]
  exact isCompact_range (continuous_gsDecomp K S ιs v)

end

end GroundTheory.ProfCoh
