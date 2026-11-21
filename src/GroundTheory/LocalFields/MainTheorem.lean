import Mathlib
import GroundTheory.LocalFields.LocalArtinUniqueness
import GroundTheory.LocalFields.LocalArtinCompletion
import GroundTheory.LocalFields.LocalArtinBaseChange
import GroundTheory.LocalFields.LocalArtinTransport

section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

section Valuation

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem vle_algEquiv_apply_iff {L L' : Type*} [Field L] [Field L'] [Algebra K L] [Algebra K L']
    [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K L'] [ValuativeRel L] [ValuativeRel L']
    [ValuativeExtension K L] [ValuativeExtension K L'] (e : L ≃ₐ[K] L') (x y : L) :
    e x ≤ᵥ e y ↔ x ≤ᵥ y := by
  rw [vle_iff_spectralNorm_le (K := K), vle_iff_spectralNorm_le (K := K)]
  simp only [spectralNorm, minpoly.algEquiv_eq]

end Valuation

section Conjugation

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E] (σ : Ω ≃ₐ[K] Ω)

instance finiteDimensional_map_algEquiv :
    FiniteDimensional K (E.map (σ : Ω →ₐ[K] Ω)) :=
  LinearEquiv.finiteDimensional (IntermediateField.equivMap E (σ : Ω →ₐ[K] Ω)).toLinearEquiv


end Conjugation

section Finite

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {K' : Type*} [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
  [Algebra K K'] [ValuativeExtension K K'] [FiniteDimensional K K']
  {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [IsSepClosure K Ω] [IsSepClosure K' Ω]

omit [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K'] [ValuativeExtension K K'] in

theorem maximalAbelianExtension_le_of_algebra {y : Ω} (hy : y ∈ maximalAbelianExtension K Ω) :
    y ∈ maximalAbelianExtension K' Ω := by
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  set ι := IsScalarTower.toAlgHom K K' Ω
  have : FiniteDimensional K ι.fieldRange :=
    LinearEquiv.finiteDimensional (AlgHom.equivFieldRange ι).toLinearEquiv
  exact (mem_maximalAbelianExtension_transport_iff (AlgHom.equivFieldRange ι).toRingEquiv
    (RingEquiv.refl Ω) (fun _ => rfl)).1 (maximalAbelianExtension_le_restrictScalars ι.fieldRange hy)

theorem localArtinMap_apply_of_algebra (x : K'ˣ) {y : Ω} (hy : y ∈ maximalAbelianExtension K Ω) :
    ((localArtinMap K' Ω x ⟨y, maximalAbelianExtension_le_of_algebra hy⟩ :
      maximalAbelianExtension K' Ω) : Ω) =
      ((localArtinMap K Ω (normUnits K K' x) ⟨y, hy⟩ : maximalAbelianExtension K Ω) : Ω) := by
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  set ι := IsScalarTower.toAlgHom K K' Ω
  have : FiniteDimensional K ι.fieldRange :=
    LinearEquiv.finiteDimensional (AlgHom.equivFieldRange ι).toLinearEquiv
  set e := AlgHom.equivFieldRange ι
  have he : ∀ a b : K', e a ≤ᵥ e b ↔ a ≤ᵥ b := vle_algEquiv_apply_iff e
  have h1 := transport_localArtinMap_apply e.toRingEquiv he (RingEquiv.refl Ω) (fun _ => rfl) x
    (maximalAbelianExtension_le_of_algebra hy)
  simp only [RingEquiv.refl_apply] at h1
  rw [h1, localArtinMap_apply_of_mem ι.fieldRange _ hy]
  congr 3
  ext
  rw [coe_normUnits, coe_normUnits]
  exact Algebra.norm_eq_of_algEquiv e x

end Finite

end GroundTheory.LocalField
end
end

section
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

section Main

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]



end Main

section Functoriality

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {K' : Type*} [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']

theorem isSepClosure_of_isSeparable (K K' Ω : Type*) [Field K] [Field K'] [Field Ω] [Algebra K K']
    [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω] [Algebra.IsSeparable K K'] [IsSepClosure K' Ω] :
    IsSepClosure K Ω :=
  ⟨IsSepClosure.sep_closed K', Algebra.IsSeparable.trans K K' Ω⟩

theorem localArtinMap_norm [Algebra K K'] [ValuativeExtension K K'] [FiniteDimensional K K']
    [Algebra.IsSeparable K K'] {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra K' Ω]
    [IsScalarTower K K' Ω] [IsSepClosure K' Ω] (x : K'ˣ) {y : Ω} :
    have := isSepClosure_of_isSeparable K K' Ω
    ∀ hy : y ∈ maximalAbelianExtension K Ω,
      ((localArtinMap K' Ω x ⟨y, maximalAbelianExtension_le_of_algebra hy⟩ :
        maximalAbelianExtension K' Ω) : Ω) =
        ((localArtinMap K Ω (normUnits K K' x) ⟨y, hy⟩ : maximalAbelianExtension K Ω) : Ω) := by
  intro _ hy
  exact localArtinMap_apply_of_algebra x hy

theorem localArtinMap_transport {Ω Ω' : Type*} [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K' Ω']
    [IsSepClosure K Ω] [IsSepClosure K' Ω'] (e : K ≃+* K') (he : ∀ x y : K, e x ≤ᵥ e y ↔ x ≤ᵥ y)
    (ε : Ω ≃+* Ω') (hε : ∀ x : K, ε (algebraMap K Ω x) = algebraMap K' Ω' (e x)) (x : Kˣ) {y : Ω}
    (hy : y ∈ maximalAbelianExtension K Ω) :
    ε ((localArtinMap K Ω x ⟨y, hy⟩ : maximalAbelianExtension K Ω) : Ω) =
      ((localArtinMap K' Ω' (Units.map e.toRingHom.toMonoidHom x)
        ⟨ε y, (mem_maximalAbelianExtension_transport_iff e ε hε).2 hy⟩ :
          maximalAbelianExtension K' Ω') : Ω') :=
  transport_localArtinMap_apply e he ε hε x hy

end Functoriality

end GroundTheory.LocalField
end
end
