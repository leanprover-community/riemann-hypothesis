import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem

section
universe u_1 u_2 u_3 u_4

namespace GlobalTheory.ContinuityFromFixedPoints

open Topology

theorem continuous_of_forall_exists_fix {k : Type u_1} {F : Type u_2} {k' : Type u_3}
    {F' : Type u_4} [Field k] [Field F] [Algebra k F] [Field k'] [Field F'] [Algebra k' F']
    [Algebra.IsIntegral k F] (φ : Gal(F/k) →* Gal(F'/k'))
    (h : ∀ y : F', ∃ x : F, ∀ σ : Gal(F/k), σ x = x → φ σ y = y) :
    Continuous φ := by
  classical
  choose x hx using h
  refine continuous_of_continuousAt_one φ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨E', hE', hs'⟩ := (krullTopology_mem_nhds_one_iff k' F' s).1 hs
  let b := Module.finBasis k' E'
  let S : Set F := Set.range fun i => x (b i : F')
  have hS : S.Finite := Set.finite_range _
  haveI : Finite S := hS.to_subtype
  have hfin : FiniteDimensional k (IntermediateField.adjoin k S) :=
    IntermediateField.finiteDimensional_adjoin fun z _ => Algebra.IsIntegral.isIntegral z
  rw [Filter.mem_map]
  refine (krullTopology_mem_nhds_one_iff k F _).2 ⟨IntermediateField.adjoin k S, hfin, ?_⟩
  intro σ hσ
  apply hs'
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  have hb : ∀ i, φ σ (b i : F') = b i := fun i =>
    hx _ σ (hσ _ (IntermediateField.subset_adjoin k S ⟨i, rfl⟩))
  intro y hy
  have hlin : ((φ σ).toLinearMap ∘ₗ E'.val.toLinearMap) = E'.val.toLinearMap :=
    b.ext fun i => by simpa using hb i
  simpa using LinearMap.congr_fun hlin ⟨y, hy⟩

end GlobalTheory.ContinuityFromFixedPoints
end

section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

namespace GlobalTheory.HeckeGal

theorem continuous_galHom_of_fix {k F k' F' : Type*} [Field k] [Field F] [Algebra k F] [Field k'] [Field F']
    [Algebra k' F'] [Algebra.IsIntegral k F] (φ : (F ≃ₐ[k] F) →* (F' ≃ₐ[k'] F'))
    (h : ∀ y : F', ∃ x : F, ∀ σ : F ≃ₐ[k] F, σ x = x → φ σ y = y) : Continuous φ := by
  first
  | exact @_root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix
  | exact _root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix
  | (apply _root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix <;> assumption)
  | (intros; apply _root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix ..)

theorem exists_topAbelianization_mulEquiv {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (φ : G ≃* H) (hφ : IsHomeomorph φ) :
    ∃ ψ : TopologicalAbelianization G ≃* TopologicalAbelianization H, IsHomeomorph ψ ∧
      ∀ g : G, ψ (QuotientGroup.mk g) = QuotientGroup.mk (φ g) := by
  have hc : (commutator G).map (φ : G →* H) = commutator H := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ φ.surjective]
  have hmap : (Subgroup.topologicalClosure (commutator G)).map (φ : G →* H) =
      Subgroup.topologicalClosure (commutator H) := by
    apply SetLike.coe_injective
    rw [Subgroup.coe_map, Subgroup.topologicalClosure_coe, Subgroup.topologicalClosure_coe, ← hc, Subgroup.coe_map]
    exact (hφ.homeomorph φ).image_closure _
  let ψ := QuotientGroup.congr _ _ φ hmap
  have h1 : Continuous ψ :=
    (QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff).2
      (QuotientGroup.continuous_mk.comp hφ.continuous)
  have hs : Continuous φ.symm :=
    (φ.toEquiv.toHomeomorphOfContinuousOpen hφ.continuous hφ.isOpenMap).symm.continuous
  have h2 : Continuous ψ.symm :=
    (QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff).2
      (QuotientGroup.continuous_mk.comp hs)
  exact ⟨ψ, (Homeomorph.mk ψ.toEquiv h1 h2).isHomeomorph, fun g => rfl⟩

theorem exists_abMap_of_algEquiv : ∀ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω]
    (e : Ω ≃ₐ[K] AlgebraicClosure K), ∃ φ : GlobalTheory.HeckeGal.Gab K Ω →* Field.absoluteGaloisGroupAbelianization K,
      Continuous φ ∧ Function.Bijective φ ∧
      ∀ σ : Formalism.ConjugateSelfDual.G K Ω, φ (GlobalTheory.HeckeGal.toAb K Ω σ) = Neutral.B1.toAb K ((e.symm.trans σ).trans e) := by
  intro K _ _ Ω _ _ e
  haveI hint : Algebra.IsIntegral K Ω :=
    ⟨fun x => (isIntegral_algEquiv e).1 (Algebra.IsIntegral.isIntegral (e x))⟩
  let φ : (Ω ≃ₐ[K] Ω) ≃* Field.absoluteGaloisGroup K := AlgEquiv.autCongr e
  have h1 : Continuous φ.toMonoidHom :=
    continuous_galHom_of_fix φ.toMonoidHom fun y => ⟨e.symm y, fun σ hσ => by
      show e (σ (e.symm y)) = y
      rw [hσ, AlgEquiv.apply_symm_apply]⟩
  have h2 : Continuous φ.symm.toMonoidHom :=
    continuous_galHom_of_fix φ.symm.toMonoidHom fun y => ⟨e y, fun τ hτ => by
      show e.symm (τ (e y)) = y
      rw [hτ, AlgEquiv.symm_apply_apply]⟩
  have hφ : IsHomeomorph φ := (Homeomorph.mk φ.toEquiv h1 h2).isHomeomorph
  obtain ⟨ψ, hψ, hψg⟩ := exists_topAbelianization_mulEquiv φ hφ
  refine ⟨ψ.toMonoidHom, hψ.continuous, ψ.bijective, fun σ => ?_⟩
  exact hψg σ

end GlobalTheory.HeckeGal
end
