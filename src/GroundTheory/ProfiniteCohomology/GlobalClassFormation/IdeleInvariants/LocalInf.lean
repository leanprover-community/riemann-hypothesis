import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalResKill
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ResLocal
import GroundTheory.LocalFields.MainTheorem
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleRestriction.ExistsInfIdelesLocalResIdelesResFieldEqZeroOfInf

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField GroundTheory.LocalField ValuativeRel
open GroundTheory.LocalField.Abstract GroundTheory.LocalField.Abstract.ProfiniteInteger

noncomputable section

section Structure

variable (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

theorem brauerInvZOfIsSepClosure_eq_brauerInvZ [v : ValuativeRel Ω] [t : TopologicalSpace Ω]
    [IsValuativeTopology Ω] [ValuativeExtension K Ω] :
    brauerInvZOfIsSepClosure K Ω = brauerInvZ K Ω := by
  have hv : algebraicValuativeRel K Ω = v :=
    valuativeRel_eq_of_isAlgebraic K (algebraicValuativeRel_valuativeExtension K Ω) inferInstance
  subst hv
  let : ValuativeRel Ω := algebraicValuativeRel K Ω
  have ht : algebraicTopology K Ω = t :=
    topologicalSpace_eq_of_isValuativeTopology (algebraicTopology_isValuativeTopology K Ω) inferInstance
  subst ht
  rfl

end Structure

section Res

variable (Kv Ω : Type) [Field Kv] [ValuativeRel Kv] [TopologicalSpace Kv] [IsNonarchimedeanLocalField Kv]
  [Field Ω] [Algebra Kv Ω] [IsSepClosure Kv Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [ValuativeExtension Kv Ω] (L : IntermediateField Kv Ω) [FiniteDimensional Kv L]

theorem brauerInvZOfIsSepClosure_unitsScalarsRes (y : cohomology (galUnitsZ Kv Ω) 2) :
    brauerInvZOfIsSepClosure L Ω ((unitsScalarsRes Kv Ω L 2).hom y) =
      Module.finrank Kv L • brauerInvZOfIsSepClosure Kv Ω y := by
  rw [brauerInvZOfIsSepClosure_eq_brauerInvZ L Ω, brauerInvZOfIsSepClosure_eq_brauerInvZ Kv Ω]
  obtain ⟨x, rfl⟩ := (cohomologyULiftIntAddEquiv (galUnits.{0} Kv Ω) 2).surjective y
  have e := cohomologyULiftIntAddEquiv_cohomologyMapAlong (galUnits.{0} Kv Ω)
    (AlgEquiv.restrictScalarsHom Kv) (continuous_restrictScalarsHom_of_tower Kv L Ω)
    (galUnitsResScalars Kv L Ω) (unitsScalarsMor Kv Ω L) (fun _ => rfl) 2 x
  have e' := congrArg (brauerInvZ L Ω) e
  rw [brauerInvZ_cohomologyULiftIntAddEquiv] at e'
  refine e'.symm.trans ?_
  rw [brauerInvZ_cohomologyULiftIntAddEquiv]
  exact brauerInv_brauerRes Kv L Ω x

end Res

section Injective

variable {k G H : Type} [CommRing k] [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H] {A : Rep k G} {B : Rep k H} [IsDiscreteRep A] [IsDiscreteRep B]

theorem cohomologyMapAlong_injective_of_leftInverse (φ : H →* G) (hφ : Continuous φ) (ψ : G →* H)
    (hψ : Continuous ψ) (hφψ : ∀ g, φ (ψ g) = g) (f : Rep.res φ A ⟶ B) (f' : Rep.res ψ B ⟶ A)
    (hff : ∀ a : A, f'.hom (f.hom a) = a) (n : ℕ) :
    Function.Injective (cohomologyMapAlong φ hφ f n).hom := by
  have h : cohomologyMapAlong φ hφ f n ≫ cohomologyMapAlong ψ hψ f' n = 𝟙 _ := by
    rw [← cohomologyMapAlong_comp]
    exact cohomologyMapAlong_eq_id _ _ (MonoidHom.ext hφψ) hff n
  intro x y hxy
  have e := congrArg (cohomologyMapAlong ψ hψ f' n).hom hxy
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, h] at e
  exact e

end Injective

section Quadratic

variable {F F' Ω Ω' : Type} [Field F] [Field F'] [Field Ω] [Field Ω'] [Algebra F Ω] [Algebra F' Ω']
  [FiniteDimensional F Ω] [IsGalois F Ω] [FiniteDimensional F' Ω'] [IsGalois F' Ω']

theorem quadraticInv_cohomologyMapAlong_of_injective (h2 : Module.finrank F Ω ≤ 2) (hN)
    (h2' : Module.finrank F' Ω' ≤ 2) (hN') {ρ : Gal(Ω/F) →* Gal(Ω'/F')} (hρc : Continuous ρ)
    (f : Rep.res ρ (galUnitsZ F' Ω') ⟶ galUnitsZ F Ω)
    (hinj : Function.Injective (cohomologyMapAlong ρ hρc f 2).hom) (x : cohomology (galUnitsZ F' Ω') 2) :
    quadraticInv F Ω h2 hN ((cohomologyMapAlong ρ hρc f 2).hom x) = quadraticInv F' Ω' h2' hN' x := by
  rw [quadraticInv_apply, quadraticInv_apply]
  by_cases hx : x = 0
  · rw [hx, map_zero, quadraticInvFun_zero, quadraticInvFun_zero]
  · rw [quadraticInvFun_of_ne_zero F Ω (fun h => hx (hinj (h.trans (map_zero _).symm))),
      quadraticInvFun_of_ne_zero F' Ω' hx]

end Quadratic

section Surjective

variable {F Ω : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field Ω] [Algebra F Ω] [IsSepClosure F Ω]

theorem exists_galCupClass_eq (x : cohomology (galUnitsZ F Ω) 2) :
    ∃ (χ : Additive Gal(Ω/F) →ₜ+ QZ) (a : Fˣ), galCupClass F Ω χ a = x := by
  let := algebraicValuativeRel F Ω
  let := algebraicTopology F Ω
  have := algebraicTopology_isValuativeTopology F Ω
  have := algebraicValuativeRel_valuativeExtension F Ω
  obtain ⟨r, hr⟩ := QZ.mk_surjective (brauerInvZ F Ω x)
  let n : ℕ+ := ⟨r.den, r.den_pos⟩
  let f₀ : ℤ →+ QZ := zmultiplesHom QZ (QZ.mk r)
  have hf₀ : f₀ ((n : ℕ) : ℤ) = 0 := by
    change ((r.den : ℕ) : ℤ) • QZ.mk r = 0
    rw [natCast_zsmul, ← QZ.mk_nsmul, nsmul_eq_mul, Rat.den_mul_eq_num, QZ.mk_eq_zero_iff]
    exact ⟨r.num, rfl⟩
  let χ₀ : ZMod n →+ QZ := ZMod.lift n ⟨f₀, hf₀⟩
  have hχ₀ : χ₀ 1 = QZ.mk r := by
    rw [show (1 : ZMod n) = ((1 : ℤ) : ZMod n) from Int.cast_one.symm, ZMod.lift_coe]
    change (1 : ℤ) • QZ.mk r = QZ.mk r
    rw [one_zsmul]
  let ψ : Additive Gal(Ω/F) →ₜ+ QZ :=
    { toFun := fun g => χ₀ (proj n (Multiplicative.toAdd (unramifiedDegree F Ω (Additive.toMul g))))
      map_zero' := by
        change χ₀ (proj n (Multiplicative.toAdd (unramifiedDegree F Ω 1))) = 0
        rw [map_one, toAdd_one, map_zero, map_zero]
      map_add' := fun g h => by
        change χ₀ (proj n (Multiplicative.toAdd (unramifiedDegree F Ω (Additive.toMul g * Additive.toMul h)))) = _
        rw [map_mul, toAdd_mul, map_add, map_add]
      continuous_toFun := continuous_of_discreteTopology.comp ((continuous_proj n).comp
        (continuous_toAdd.comp ((continuous_unramifiedDegree (K := F) (Ω := Ω)).comp continuous_toMul))) }
  obtain ⟨π, hπ⟩ : ∃ π : Fˣ, ord (π : F) = 1 := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
    have h0 : (ϖ : F) ≠ 0 := by exact_mod_cast hϖ.ne_zero
    exact ⟨Units.mk0 _ h0, by rw [Units.val_mk0]; exact ord_uniformizer hϖ⟩
  obtain ⟨σ, hσ⟩ := unramifiedDegree_surjective (K := F) (Ω := Ω) (Multiplicative.ofAdd 1)
  have hψ : ∀ g ∈ (unramifiedDegree F Ω).ker, ψ (Additive.ofMul g) = 0 := fun g hg => by
    change χ₀ (proj n (Multiplicative.toAdd (unramifiedDegree F Ω g))) = 0
    rw [MonoidHom.mem_ker.1 hg, toAdd_one, map_zero, map_zero]
  refine ⟨ψ, π, (brauerInvZ_bijective F Ω).1 ?_⟩
  rw [brauerInvZ_galCupClass_of_unramified ψ hψ hσ π, hπ, one_smul, ← hr]
  change χ₀ (proj n (Multiplicative.toAdd (unramifiedDegree F Ω σ))) = QZ.mk r
  rw [hσ, toAdd_ofAdd, map_one, hχ₀]

end Surjective

section Transport

variable {F F' Ω Ω' : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field F'] [ValuativeRel F'] [TopologicalSpace F'] [IsNonarchimedeanLocalField F']
  [Field Ω] [Algebra F Ω] [IsSepClosure F Ω] [Field Ω'] [Algebra F' Ω'] [IsSepClosure F' Ω']
  (e : F ≃+* F') (ε : Ω ≃+* Ω') (hε : ∀ x : F, ε (algebraMap F Ω x) = algebraMap F' Ω' (e x))
  (ρ : Gal(Ω/F) →* Gal(Ω'/F')) (hρc : Continuous ρ) (hρ : ∀ (σ : Gal(Ω/F)) (x : Ω), ρ σ (ε x) = ε (σ x))
  (f : Rep.res ρ (galUnitsZ F' Ω') ⟶ galUnitsZ F Ω)
  (hf : ∀ u : Ω'ˣ, ((Additive.toMul (f.hom (Additive.ofMul u)) : Ωˣ) : Ω) = ε.symm u)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [ValuativeRel F']
  [TopologicalSpace F'] [IsNonarchimedeanLocalField F'] in
include hε hf in

theorem cohomologyMapAlong_galCupClass_transport (χ : Additive Gal(Ω'/F') →ₜ+ QZ) (a : Fˣ) :
    (cohomologyMapAlong ρ hρc f 2).hom (galCupClass F' Ω' χ (Units.map e.toRingHom.toMonoidHom a)) =
      galCupClass F Ω (contCharComp χ ρ hρc) a := by
  refine cohomologyMapAlong_cupCharClassProf ρ hρc f χ _ _ ?_
  apply Additive.toMul.injective
  apply Units.ext
  change algebraMap F Ω a = ((Additive.toMul (f.hom (Additive.ofMul
    (Units.map (algebraMap F' Ω' : F' →* Ω') (Units.map e.toRingHom.toMonoidHom a)))) : Ωˣ) : Ω)
  rw [hf, Units.coe_map, Units.coe_map]
  change algebraMap F Ω a = ε.symm (algebraMap F' Ω' (e a))
  rw [← hε, RingEquiv.symm_apply_apply]

include hε hρ in

theorem brauerInvZOfIsSepClosure_galCupClass_transport (he : ∀ x y : F, e x ≤ᵥ e y ↔ x ≤ᵥ y)
    (χ : Additive Gal(Ω'/F') →ₜ+ QZ) (a : Fˣ) :
    brauerInvZOfIsSepClosure F Ω (galCupClass F Ω (contCharComp χ ρ hρc) a) =
      brauerInvZOfIsSepClosure F' Ω' (galCupClass F' Ω' χ (Units.map e.toRingHom.toMonoidHom a)) := by
  set g : Gal(Ω/F) := (localArtinMap F Ω a).liftNormal Ω
  have hg : ∀ (y : Ω) (hy : y ∈ maximalAbelianExtension F Ω), g y = (localArtinMap F Ω a ⟨y, hy⟩ : Ω) :=
    fun y hy => AlgEquiv.liftNormal_commutes (localArtinMap F Ω a) Ω ⟨y, hy⟩
  rw [brauerInvZOfIsSepClosure_galCupClass _ a g hg, contCharComp_apply]
  refine (brauerInvZOfIsSepClosure_galCupClass χ _ (ρ g) fun y' hy' => ?_).symm
  obtain ⟨y, rfl⟩ := ε.surjective y'
  have hy : y ∈ maximalAbelianExtension F Ω := (mem_maximalAbelianExtension_transport_iff e ε hε).1 hy'
  rw [hρ, hg y hy, localArtinMap_transport e he ε hε a hy]

include hε hρ hf in

theorem brauerInvZOfIsSepClosure_cohomologyMapAlong_transport (he : ∀ x y : F, e x ≤ᵥ e y ↔ x ≤ᵥ y)
    (x : cohomology (galUnitsZ F' Ω') 2) :
    brauerInvZOfIsSepClosure F Ω ((cohomologyMapAlong ρ hρc f 2).hom x) = brauerInvZOfIsSepClosure F' Ω' x := by
  obtain ⟨χ, a', rfl⟩ := exists_galCupClass_eq x
  obtain ⟨a, rfl⟩ : ∃ a : Fˣ, Units.map e.toRingHom.toMonoidHom a = a' :=
    ⟨Units.map e.symm.toRingHom.toMonoidHom a', by ext; simp⟩
  rw [cohomologyMapAlong_galCupClass_transport e ε hε ρ hρc f hf,
    brauerInvZOfIsSepClosure_galCupClass_transport e ε hε ρ hρc hρ he]

end Transport

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain IdeleLimit
  GroundTheory.Global.SemiLocal GroundTheory.LocalField ValuativeRel

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section Valuation

variable {K F Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field F] [ValuativeRel F] [Algebra K F] [ValuativeExtension K F] [Algebra.IsAlgebraic K F]
  [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

theorem algebraicValuativeRel_vle_algHom_iff (c : F →ₐ[K] Ω) (x y : F) :
    (letI := algebraicValuativeRel K Ω; c x ≤ᵥ c y) ↔ x ≤ᵥ y := by
  let := algebraicValuativeRel K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  rw [vle_iff_spectralNorm_le (K := K) (c x) (c y), vle_iff_spectralNorm_le (K := K) x y]
  let := normedField K
  change spectralNorm K Ω (c x) ≤ spectralNorm K Ω (c y) ↔ spectralNorm K F x ≤ spectralNorm K F y
  rw [spectralNorm, spectralNorm, spectralNorm, spectralNorm, minpoly.algHom_eq c c.injective,
    minpoly.algHom_eq c c.injective]

end Valuation

variable {K E : FiniteSubfield} [Fact (K ≤ E)]

section Finite

set_option maxHeartbeats 4000000 in

theorem brauerInvZOfIsSepClosure_idelesLocalRes_idelesResField (v : HeightOneSpectrum (𝓞 K.1))
    (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))
    (ιE : ℚ̄ →ₐ[E.1] AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1))
    (y : cohomology (limitRep K) 2) :
    brauerInvZOfIsSepClosure ((placeOfEmbedding ι E).1.adicCompletion E.1)
        (AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1))
        ((idelesLocalRes ιE 2).hom ((idelesResField K E 2).hom y)) =
      Module.finrank (v.adicCompletion K.1) ((placeOfEmbedding ι E).1.adicCompletion E.1) •
        brauerInvZOfIsSepClosure (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))
          ((idelesLocalRes ι 2).hom y) := by
  have := finiteDimensional_adicCompletion_placesOver (E := E) (placeOfEmbedding ι E)
  let c := completionEmbedding ι E
  let L := c.fieldRange
  let : Algebra ((placeOfEmbedding ι E).1.adicCompletion E.1) (AlgebraicClosure (v.adicCompletion K.1)) :=
    c.toRingHom.toAlgebra
  have : IsScalarTower (v.adicCompletion K.1) ((placeOfEmbedding ι E).1.adicCompletion E.1)
      (AlgebraicClosure (v.adicCompletion K.1)) :=
    IsScalarTower.of_algebraMap_eq fun a => (c.commutes a).symm
  have : Algebra.IsAlgebraic ((placeOfEmbedding ι E).1.adicCompletion E.1) (AlgebraicClosure (v.adicCompletion K.1)) :=
    Algebra.IsAlgebraic.tower_top (K := v.adicCompletion K.1) _
  have : IsAlgClosure ((placeOfEmbedding ι E).1.adicCompletion E.1) (AlgebraicClosure (v.adicCompletion K.1)) :=
    ⟨inferInstance, inferInstance⟩
  let θ : AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1) ≃ₐ[(placeOfEmbedding ι E).1.adicCompletion E.1]
      AlgebraicClosure (v.adicCompletion K.1) := IsAlgClosure.equiv _ _ _
  let : Algebra E.1 (AlgebraicClosure (v.adicCompletion K.1)) :=
    ((algebraMap ((placeOfEmbedding ι E).1.adicCompletion E.1) (AlgebraicClosure (v.adicCompletion K.1))).comp
      (algebraMap E.1 ((placeOfEmbedding ι E).1.adicCompletion E.1))).toAlgebra
  have : IsScalarTower E.1 ((placeOfEmbedding ι E).1.adicCompletion E.1) (AlgebraicClosure (v.adicCompletion K.1)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ιE' : ℚ̄ →ₐ[E.1] AlgebraicClosure (v.adicCompletion K.1) :=
    { ι.toRingHom with commutes' := fun t => (completionEmbedding_algebraMap ι E t).symm }
  let ιE0 : ℚ̄ →ₐ[E.1] AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1) :=
    (θ.symm.toAlgHom.restrictScalars E.1).comp ιE'
  have hι : ∀ t, θ.toRingEquiv (ιE0 t) = ι t := fun t => θ.apply_symm_apply (ι t)
  have hL : ∀ l ∈ L, ∃ t : (placeOfEmbedding ι E).1.adicCompletion E.1,
      θ.toRingEquiv (algebraMap _ (AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1)) t) = l := by
    intro l hl
    obtain ⟨t, rfl⟩ := (AlgHom.mem_fieldRange).1 hl
    exact ⟨t, θ.commutes t⟩
  have : FiniteDimensional (v.adicCompletion K.1) L := LinearEquiv.finiteDimensional c.equivFieldRange.toLinearEquiv
  have : Algebra.IsIntegral L (AlgebraicClosure (v.adicCompletion K.1)) :=
    Algebra.IsIntegral.tower_top (v.adicCompletion K.1)
  have hfin : Module.finrank (v.adicCompletion K.1) L =
      Module.finrank (v.adicCompletion K.1) ((placeOfEmbedding ι E).1.adicCompletion E.1) :=
    c.equivFieldRange.toLinearEquiv.finrank_eq.symm
  have hproj : ∀ z : IdeleLimit, θ.toRingEquiv (idelesProj ιE0 z : AlgebraicClosure _) =
      (idelesProj ι z : AlgebraicClosure (v.adicCompletion K.1)) :=
    idelesProj_eq_of_algebraMap (placeOfEmbedding ι E) ι ιE0 θ.toRingEquiv hι fun a => by
      change θ (algebraMap _ (AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1))
        (algebraMap (v.adicCompletion K.1) _ a)) = _
      rw [θ.commutes]
      exact c.commutes a
  have key := cohomologyMapAlong_globalDecomp_idelesResField (v.adicCompletion K.1)
    ((placeOfEmbedding ι E).1.adicCompletion E.1) L θ.toRingEquiv hL ι ιE0 hι (idelesLocalMor ι) (idelesLocalMor ιE0)
    hproj 2 y
  have key' : (idelesLocalRes ιE0 2).hom ((idelesResField K E 2).hom y) =
      (cohomologyMapAlong (fieldConjHom (v.adicCompletion K.1) L θ.toRingEquiv hL)
        (continuous_fieldConjHom (v.adicCompletion K.1) L θ.toRingEquiv hL)
        (fieldConjUnitsMor (v.adicCompletion K.1) L θ.toRingEquiv hL) 2).hom
        ((unitsScalarsRes (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1)) L 2).hom
          ((idelesLocalRes ι 2).hom y)) := key
  rw [idelesLocalRes_eq_of_algHom ιE0 ιE, key']
  let := algebraicValuativeRel (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))
  let := algebraicTopology (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))
  have := algebraicTopology_isValuativeTopology (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))
  have := algebraicValuativeRel_valuativeExtension (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))
  let e : (placeOfEmbedding ι E).1.adicCompletion E.1 ≃+* L := c.equivFieldRange.toRingEquiv
  have hε : ∀ x, θ.toRingEquiv (algebraMap ((placeOfEmbedding ι E).1.adicCompletion E.1)
      (AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1)) x) =
      algebraMap L (AlgebraicClosure (v.adicCompletion K.1)) (e x) := fun x => θ.commutes x
  have he : ∀ x y : (placeOfEmbedding ι E).1.adicCompletion E.1, e x ≤ᵥ e y ↔ x ≤ᵥ y := fun x y => by
    rw [← IntermediateField.coe_vle_coe_iff]
    exact algebraicValuativeRel_vle_algHom_iff c x y
  have hρ : ∀ (σ : Gal(AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1) /
      (placeOfEmbedding ι E).1.adicCompletion E.1)) (x : AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1)),
      fieldConjHom (v.adicCompletion K.1) L θ.toRingEquiv hL σ (θ.toRingEquiv x) = θ.toRingEquiv (σ x) :=
    fun σ x => by rw [fieldConjHom_apply, RingEquiv.symm_apply_apply]
  rw [brauerInvZOfIsSepClosure_cohomologyMapAlong_transport e θ.toRingEquiv hε _
    (continuous_fieldConjHom (v.adicCompletion K.1) L θ.toRingEquiv hL) hρ _ (fun _ => rfl) he,
    brauerInvZOfIsSepClosure_unitsScalarsRes, hfin]

end Finite

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain IdeleLimit
  GroundTheory.Global.SemiLocal

open scoped NumberField.LiesOver

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K E : FiniteSubfield} [Fact (K ≤ E)]

set_option maxHeartbeats 4000000 in

theorem quadraticInv_infIdelesLocalRes_idelesResField_of_finrank_eq_one {v : InfinitePlace K.1}
    (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)
    (ιE : ℚ̄ →ₐ[E.1] AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion)
    (y : cohomology (limitRep K) 2)
    (h1 : Module.finrank v.Completion (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion = 1) :
    quadraticInv (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion
        (AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion)
        (infAlgClosure_finrank_le_two _) (infAlgClosure_mul_mem_range_norm _)
        ((infIdelesLocalRes ιE 2).hom ((idelesResField K E 2).hom y)) =
      quadraticInv v.Completion (AlgebraicClosure v.Completion) (infAlgClosure_finrank_le_two v)
        (infAlgClosure_mul_mem_range_norm v) ((infIdelesLocalRes ι 2).hom y) := by
  have : (infPlaceOfEmbedding ι E : InfinitePlace E.1).LiesOver v := (infPlaceOfEmbedding ι E).2
  let c := infCompletionEmbedding ι E
  let L := c.fieldRange
  let : Algebra (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion (AlgebraicClosure v.Completion) :=
    c.toRingHom.toAlgebra
  have : IsScalarTower v.Completion (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion
      (AlgebraicClosure v.Completion) :=
    IsScalarTower.of_algebraMap_eq fun a => (c.commutes a).symm
  have : Algebra.IsAlgebraic (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion (AlgebraicClosure v.Completion) :=
    Algebra.IsAlgebraic.tower_top (K := v.Completion) _
  have : IsAlgClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion (AlgebraicClosure v.Completion) :=
    ⟨inferInstance, inferInstance⟩
  let θ : AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion ≃ₐ[(infPlaceOfEmbedding ι E :
      InfinitePlace E.1).Completion] AlgebraicClosure v.Completion := IsAlgClosure.equiv _ _ _
  let : Algebra E.1 (AlgebraicClosure v.Completion) :=
    ((algebraMap (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion (AlgebraicClosure v.Completion)).comp
      (algebraMap E.1 (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion)).toAlgebra
  have : IsScalarTower E.1 (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion (AlgebraicClosure v.Completion) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ιE' : ℚ̄ →ₐ[E.1] AlgebraicClosure v.Completion :=
    { ι.toRingHom with commutes' := fun t => (infCompletionEmbedding_algebraMap ι E t).symm }
  let ιE0 : ℚ̄ →ₐ[E.1] AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion :=
    (θ.symm.toAlgHom.restrictScalars E.1).comp ιE'
  have hι : ∀ t, θ.toRingEquiv (ιE0 t) = ι t := fun t => θ.apply_symm_apply (ι t)
  have hL : ∀ l ∈ L, ∃ t : (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion,
      θ.toRingEquiv (algebraMap _ (AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion) t) = l := by
    intro l hl
    obtain ⟨t, rfl⟩ := (AlgHom.mem_fieldRange).1 hl
    exact ⟨t, θ.commutes t⟩
  have : Algebra.IsIntegral L (AlgebraicClosure v.Completion) := Algebra.IsIntegral.tower_top v.Completion
  have hproj : ∀ z : IdeleLimit, θ.toRingEquiv (infIdelesProj ιE0 z : AlgebraicClosure _) =
      (infIdelesProj ι z : AlgebraicClosure v.Completion) :=
    infIdelesProj_eq_of_algebraMap (infPlaceOfEmbedding ι E) ι ιE0 θ.toRingEquiv hι fun a => by
      change θ (algebraMap _ (AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion)
        (algebraMap v.Completion _ a)) = _
      rw [θ.commutes]
      exact c.commutes a
  have key := cohomologyMapAlong_globalDecomp_idelesResField v.Completion
    (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion L θ.toRingEquiv hL ι ιE0 hι (infIdelesLocalMor ι)
    (infIdelesLocalMor ιE0) hproj 2 y

  let φ := (AlgEquiv.restrictScalarsHom v.Completion).comp (fieldConjHom v.Completion L θ.toRingEquiv hL)
  have hφ : Continuous φ := (continuous_restrictScalarsHom_of_tower v.Completion L (AlgebraicClosure v.Completion)).comp
    (continuous_fieldConjHom v.Completion L θ.toRingEquiv hL)
  let fφ : Rep.res φ (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) ⟶
      galUnitsZ (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion
        (AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion) := (Rep.resFunctor (fieldConjHom v.Completion L θ.toRingEquiv hL)).map
    (unitsScalarsMor v.Completion (AlgebraicClosure v.Completion) L) ≫ fieldConjUnitsMor v.Completion L θ.toRingEquiv hL
  have key' : (infIdelesLocalRes ιE0 2).hom ((idelesResField K E 2).hom y) =
      (cohomologyMapAlong φ hφ fφ 2).hom ((infIdelesLocalRes ι 2).hom y) := by
    refine key.trans ?_
    rw [unitsScalarsRes, cohomologyMapAlong_comp]
    rfl
  rw [infIdelesLocalRes_eq_of_algHom ιE0 ιE, key']

  have hbot := Subalgebra.bot_eq_top_of_finrank_eq_one h1
  have hfix : ∀ (σ : Gal(AlgebraicClosure v.Completion / v.Completion))
      (t : (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion),
      θ.symm (σ (θ (algebraMap _ (AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion) t))) =
        algebraMap _ _ t := by
    intro σ t
    have ht : t ∈ (⊥ : Subalgebra v.Completion (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion) := by
      rw [hbot]
      trivial
    obtain ⟨k, rfl⟩ := Algebra.mem_bot.1 ht
    have hk : θ (algebraMap _ (AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion)
        (algebraMap v.Completion (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion k)) =
          algebraMap v.Completion (AlgebraicClosure v.Completion) k := by
      rw [θ.commutes]
      exact c.commutes k
    rw [hk, σ.commutes, ← hk, AlgEquiv.symm_apply_apply]
  let ψ : Gal(AlgebraicClosure v.Completion / v.Completion) →*
      Gal(AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion /
        (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion) :=
    { toFun := fun σ => AlgEquiv.ofRingEquiv (f := (θ.toRingEquiv.trans σ.toRingEquiv).trans θ.toRingEquiv.symm)
        (hfix σ)
      map_one' := AlgEquiv.ext fun x => θ.symm_apply_apply x
      map_mul' := fun σ τ => AlgEquiv.ext fun x => by
        change θ.symm (σ (τ (θ x))) = θ.symm (σ (θ (θ.symm (τ (θ x)))))
        rw [AlgEquiv.apply_symm_apply] }
  have hψ_apply : ∀ σ x, ψ σ x = θ.symm (σ (θ x)) := fun _ _ => rfl
  have hψ : Continuous ψ := by
    refine continuous_of_continuousAt_one _ ?_
    rw [ContinuousAt, map_one]
    intro s hs
    obtain ⟨M, hM, hMs⟩ := (krullTopology_mem_nhds_one_iff _ _ s).1 hs
    rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
    have : Module.Free (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion M := Module.Free.of_divisionRing _ M
    let b := Module.finBasis (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion M
    let T : Set (AlgebraicClosure v.Completion) :=
      Set.range fun i => θ (b i : AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion)
    refine ⟨IntermediateField.adjoin v.Completion T, ?_, ?_⟩
    · refine IntermediateField.finiteDimensional_adjoin fun x _ => ?_
      exact Algebra.IsIntegral.isIntegral x
    · intro σ hσ
      apply hMs
      rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
      intro x hx
      have hT : ∀ i, ψ σ (b i : AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion) =
          b i := fun i => by
        rw [hψ_apply, hσ _ (IntermediateField.subset_adjoin v.Completion T ⟨i, rfl⟩), AlgEquiv.symm_apply_apply]
      have hlin : (ψ σ).toAlgHom.toLinearMap ∘ₗ M.val.toLinearMap = M.val.toLinearMap :=
        b.ext fun i => hT i
      exact LinearMap.congr_fun hlin ⟨x, hx⟩
  let f' : Rep.res ψ (galUnitsZ (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion
      (AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion)) ⟶
      galUnitsZ v.Completion (AlgebraicClosure v.Completion) :=
    Rep.ofHom ⟨(MonoidHom.toAdditive (Units.map θ.toRingEquiv.toRingHom.toMonoidHom)).toIntLinearMap,
      fun σ => LinearMap.ext fun x => congrArg Additive.ofMul (Units.ext (by
        change θ (θ.symm (σ (θ ((Additive.toMul x : (AlgebraicClosure _)ˣ) : AlgebraicClosure _)))) =
          σ (θ ((Additive.toMul x : (AlgebraicClosure _)ˣ) : AlgebraicClosure _))
        exact θ.apply_symm_apply _))⟩
  have hinj : Function.Injective (cohomologyMapAlong φ hφ fφ 2).hom := by
    refine cohomologyMapAlong_injective_of_leftInverse φ hφ ψ hψ (fun σ => AlgEquiv.ext fun x => ?_) fφ f'
      (fun a => ?_) 2
    · change θ (θ.symm (σ (θ (θ.symm x)))) = σ x
      rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    · apply Additive.toMul.injective
      apply Units.ext
      change θ (θ.symm ((Additive.toMul a : (AlgebraicClosure v.Completion)ˣ) : AlgebraicClosure v.Completion)) = _
      exact θ.apply_symm_apply _
  exact quadraticInv_cohomologyMapAlong_of_injective _ _ _ _ hφ fφ hinj _

end

end GroundTheory.ProfCoh
end
