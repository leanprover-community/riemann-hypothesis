module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.KumCoker

instance instWLBKumCoker (R : Type) [CommRing R] :
    (Scheme.etaleTopology.{0}).WEqualsLocallyBijective (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

theorem isSheaf_forget {R : Type} [CommRing R] (F : Shv R) :
    Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
  (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.property)

theorem sec_res_zero {R : Type} [CommRing R] (F : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 :=
  map_zero _

theorem sec_eq_zero {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (x : Sec F U)
    (h : Loc U fun _ g => Sec.res g x = 0) : x = 0 := by
  obtain ⟨S, hS, hP⟩ := h
  refine ((isSheaf_forget F) S hS).isSeparatedFor.ext (fun V g hg => ?_)
  change Sec.res g x = Sec.res g 0
  rw [hP V g hg, sec_res_zero]

theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem sec_map_zero {R : Type} [CommRing R] {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (0 : F ⟶ G) x = 0 := rfl

theorem sec_nat {R : Type} [CommRing R] {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map f x) = Sec.map f (Sec.res g x) := by
  have e := congrArg (fun φ => φ.hom x) (f.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
  exact e.symm

theorem sec_res_comp {R : Type} [CommRing R] (F : Shv R) {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res h (Sec.res g x) = Sec.res (h ≫ g) x := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem unit_res {q : ℕ} {V U : Scheme.{0}} (hU : IsUnit (q : Γ(U, ⊤))) (g : V ⟶ U) : IsUnit (q : Γ(V, ⊤)) := by
  simpa using hU.map g.appTop.hom

end GlobalTheory.EtC.KumCoker

