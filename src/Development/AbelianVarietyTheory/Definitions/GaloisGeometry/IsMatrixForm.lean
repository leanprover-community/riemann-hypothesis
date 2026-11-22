module

public import Mathlib

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

abbrev Shv : Type 2 := Sheaf (Scheme.proetaleTopology.{0}) (ModuleCat.{1} (ULift.{1} R))

omit [TopologicalSpace R] [IsTopologicalRing R] in
instance : HasSheafify (Scheme.proetaleTopology.{0}) (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  infer_instance

omit [TopologicalSpace R] [IsTopologicalRing R] in
instance : IsGrothendieckAbelian.{1} (Shv R) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ (ModuleCat.{1} (ULift.{1} R))

instance (n : ℕ) (X : Scheme.{0}) : AddCommGroup (H R n X) := inferInstanceAs (AddCommGroup (HS R (coef R) n X))

instance (n : ℕ) (X : Scheme.{0}) : Module R (H R n X) :=
  Module.compHom (HS R (coef R) n X) (ULift.ringEquiv.symm : R ≃+* ULift.{1} R).toRingHom

section Galois

variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k))

abbrev geom : Scheme.{0} := pullback p (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))

def galMap (σ : Ω ≃ₐ[k] Ω) : geom Ω p ⟶ geom Ω p :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω))) (by
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, pullback.condition]
    congr 3
    ext x
    simp)

@[reassoc] theorem galMap_fst (σ : Ω ≃ₐ[k] Ω) : galMap Ω p σ ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

@[reassoc] theorem galMap_snd (σ : Ω ≃ₐ[k] Ω) :
    galMap Ω p σ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) := pullback.lift_snd _ _ _

def geomMap {Y : Scheme.{0}} {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y) (hu : u ≫ q = p) : geom Ω p ⟶ geom Ω q :=
  pullback.lift (pullback.fst _ _ ≫ u) (pullback.snd _ _) (by rw [Category.assoc, hu, pullback.condition])

end Galois

end GlobalTheory.Et

end
