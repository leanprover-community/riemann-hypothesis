import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanQuasiIsoOfLocalQuasiIsoBoundedBelowDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFunctorDegreeTermAugmentedExactResolution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyComplexOfSheafCocycleClassPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyComplexOfSheafCocycleClassProperties

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.HCEqv

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R) (E E' : Spc) (f : E ⟶ E'),
    Eqv R f F ↔ SurjH ((HC R F).map f.op) ∧ InjH ((HC R F).map f.op) := by
  intro R _ F E E' f
  obtain ⟨-, cl, hsurj, heq, hzero, hpull⟩ := GlobalTheory.EtC.HCElements.main R F
  constructor
  · intro hf
    refine ⟨fun n z hz => ?_, fun n c hc ⟨y, hy⟩ => ?_⟩
    · obtain ⟨x, hx⟩ := (hf n).2 (cl E n z hz)
      obtain ⟨c, hc, rfl⟩ := hsurj E' n x
      obtain ⟨h, hp⟩ := hpull E E' f n c hc
      rw [hp, heq] at hx
      obtain ⟨y, hy⟩ := hx
      exact ⟨c, y, hc, hy⟩
    · obtain ⟨h, hp⟩ := hpull E E' f n c hc
      have h0 : cl E n (((HC R F).map f.op).f n c) h = 0 := (hzero E n _ h).2 ⟨y, hy⟩
      rw [← hp] at h0
      have : cl E' n c hc = 0 := (hf n).1 (h0.trans (map_zero _).symm)
      obtain ⟨b, hb⟩ := (hzero E' n c hc).1 this
      exact ⟨b, hb.symm⟩
  · rintro ⟨hS, hI⟩ n
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨c, hc, rfl⟩ := hsurj E' n x
      obtain ⟨h, hp⟩ := hpull E E' f n c hc
      rw [hp, hzero] at hx
      obtain ⟨b, hb⟩ := hI n c hc hx
      exact (hzero E' n c hc).2 ⟨b, hb.symm⟩
    · intro x
      obtain ⟨z, hz, rfl⟩ := hsurj E n x
      obtain ⟨c, y, hc, hcy⟩ := hS n z hz
      obtain ⟨h, hp⟩ := hpull E E' f n c hc
      refine ⟨cl E' n c hc, ?_⟩
      rw [hp, heq]
      exact ⟨y, hcy⟩

end GlobalTheory.EtC.HCEqv
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEtaleCohomologyEquivalence_iff_elementwise : ∀ (R : Type) [CommRing R] (F : Shv R) (E E' : Spc) (f : E ⟶ E'), Eqv R f F ↔ SurjH ((HC R F).map f.op) ∧ InjH ((HC R F).map f.op) := by
  first | (exact @GlobalTheory.EtC.HCEqv.main) | (exact GlobalTheory.EtC.HCEqv.main) | (intros; apply GlobalTheory.EtC.HCEqv.main  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.Descent

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R) (T : Type 1) [Category.{0} T] (Cov : MorphismProperty T) [Cov.IsStableUnderComposition] (Φ Φ' : T ⥤ Spcᵒᵖ) (α : Φ' ⟶ Φ), Refines Cov (fun U X a => Hyp R Φ a ∧ Hyp R Φ' a) → (∀ (U : T) (n : ℤ) (x : H R (Φ.obj U).unop F n), ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ y : H R (Φ'.obj V).unop F n, pull R (α.app V).unop F n y = pull R (Φ.map g).unop F n x) → (∀ (U : T) (n : ℤ) (y : H R (Φ'.obj U).unop F n), pull R (α.app U).unop F n y = 0 → ∃ (V : T) (g : U ⟶ V), Cov g ∧ pull R (Φ'.map g).unop F n y = 0) → ∀ U, Eqv R (α.app U).unop F := by
  intro R _ F T _ Cov _ Φ Φ' α hRef hS hI U
  obtain ⟨hneg, cl, hcl_surj, hcl_eq, hcl_zero, hpull⟩ := GlobalTheory.T.cohomologyComplexOfSheaf_cocycle_class_properties R F
  have key := GlobalTheory.T.cartan_quasiIso_of_localQuasiIso_boundedBelow_descent T Cov (Φ' ⋙ HC R F) (Φ ⋙ HC R F) (Functor.whiskerRight α (HC R F)) ?_ ?_ ?_ ?_ U
  · exact (GlobalTheory.T.isEtaleCohomologyEquivalence_iff_elementwise R F _ _ (α.app U).unop).2 key
  · exact ⟨0, fun n hn V => ⟨hneg _ n hn, hneg _ n hn⟩⟩
  · intro U' V' g hg
    obtain ⟨X, a, h, hga, h1, h2⟩ := hRef U' V' g hg
    exact ⟨X, a, h, hga, fun n => ⟨GlobalTheory.T.complexFunctorDegreeTerm_augmented_exact_resolution R F T Φ' U' X a h2 n, GlobalTheory.T.complexFunctorDegreeTerm_augmented_exact_resolution R F T Φ U' X a h1 n⟩⟩
  · intro n U' z hz
    obtain ⟨V, g, hg, y, hy⟩ := hS U' n (cl (Φ.obj U').unop n z hz)
    obtain ⟨c, hc, rfl⟩ := hcl_surj (Φ'.obj V).unop n y
    obtain ⟨h1, e1⟩ := hpull _ _ (α.app V).unop n c hc
    obtain ⟨h2, e2⟩ := hpull _ _ (Φ.map g).unop n z hz
    rw [e1, e2, hcl_eq] at hy
    obtain ⟨y', hy'⟩ := hy
    exact ⟨V, g, hg, c, y', hc, hy'⟩
  · intro n U' c hc ⟨y, hy⟩
    have h0 : pull R (α.app U').unop F n (cl (Φ'.obj U').unop n c hc) = 0 := by
      obtain ⟨h1, e1⟩ := hpull _ _ (α.app U').unop n c hc
      rw [e1, hcl_zero]
      exact ⟨y, hy⟩
    obtain ⟨V, g, hg, hV⟩ := hI U' n _ h0
    obtain ⟨h2, e2⟩ := hpull _ _ (Φ'.map g).unop n c hc
    rw [e2, hcl_zero] at hV
    obtain ⟨b, hb⟩ := hV
    exact ⟨V, g, hg, b, hb.symm⟩

end GlobalTheory.EtC.Descent
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSpace_descent_local_equivalence : ∀ (R : Type) [CommRing R] (F : Shv R) (T : Type 1) [Category.{0} T] (Cov : MorphismProperty T) [Cov.IsStableUnderComposition] (Φ Φ' : T ⥤ Spcᵒᵖ) (α : Φ' ⟶ Φ), Refines Cov (fun U X a => Hyp R Φ a ∧ Hyp R Φ' a) → (∀ (U : T) (n : ℤ) (x : H R (Φ.obj U).unop F n), ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ y : H R (Φ'.obj V).unop F n, pull R (α.app V).unop F n y = pull R (Φ.map g).unop F n x) → (∀ (U : T) (n : ℤ) (y : H R (Φ'.obj U).unop F n), pull R (α.app U).unop F n y = 0 → ∃ (V : T) (g : U ⟶ V), Cov g ∧ pull R (Φ'.map g).unop F n y = 0) → ∀ U, Eqv R (α.app U).unop F := by
  first | (exact @GlobalTheory.EtC.Descent.main) | (exact GlobalTheory.EtC.Descent.main) | (intros; apply GlobalTheory.EtC.Descent.main <;> assumption)
end
