module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.OfRingsLoc
variable {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R))

instance li : Presheaf.IsLocallyInjective Scheme.etaleTopology.{0}
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  infer_instance

omit [CommRing R] in
theorem ι_comp_apply {X U : Scheme.{0}} (f : X ⟶ U) (W : X.Opens) (y : X) (h : y ∈ W) :
    (Scheme.Opens.ι W ≫ f) ⟨y, h⟩ = f y :=
  rfl

omit [CommRing R] in
theorem cov_pt {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U) (u : U) :
    ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), IsAffine V ∧ Etale j ∧ j v = u ∧ S.arrows j := by
  obtain ⟨𝒰, hle⟩ := (Scheme.mem_grothendieckTopology_iff (P := @Etale)).1 hS
  have : Scheme.JointlySurjective (Scheme.precoverage.{0} @Etale) :=
    Scheme.instJointlySurjectivePrecoverage
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq u
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ := (𝒰.X i).isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ y) isOpen_univ
  have : IsAffine W := hW
  have : Etale (𝒰.f i) := 𝒰.mem₀.2 ⟨i⟩
  refine ⟨W, Scheme.Opens.ι W ≫ 𝒰.f i, ⟨y, hyW⟩, inferInstance, inferInstance, ?_, ?_⟩
  · exact (ι_comp_apply (𝒰.f i) W y hyW).trans hy
  · exact S.downward_closed (hle _ _ (Presieve.ofArrows.mk i)) (Scheme.Opens.ι W)

end LateralTheory.EtaleFoundations.OfRingsLoc
