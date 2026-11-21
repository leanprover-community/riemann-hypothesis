import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaObjectConstantFamilyDualNumbersIsPullback
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningComplexFunctionsStructureStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSectionOfLocallyRegular
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDifferentiableOnVerticalVectorField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalDerivationAlongFibreOfSmooth
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldAbelianVarietyAlgebraic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LocDerRegularCoeff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AlgebraicCoboundaryOfHolomorphicCoboundary
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGrpPullbackRetraction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullbackStatement

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.DerMor

def preHom {Z X : Scheme.{0}} (n : Z ⟶ X) (c : ∀ W : X.Opens, Γ(X, W) →+* Γ(Z, n ⁻¹ᵁ W))
    (hres : ∀ W W' (h : W' ≤ W) f, c W' (resG X h f) = resG Z (fun _ hy => h hy) (c W f)) :
    Z.toPresheafedSpace ⟶ X.toPresheafedSpace where
  base := n.base
  c :=
    { app := fun W => CommRingCat.ofHom (c W.unop)
      naturality := fun W W' i => by
        ext f
        exact hres W.unop W'.unop i.unop.le f }

def deform {Z X : Scheme.{0}} (n : Z ⟶ X) (c : ∀ W : X.Opens, Γ(X, W) →+* Γ(Z, n ⁻¹ᵁ W))
    (hres : ∀ W W' (h : W' ≤ W) f, c W' (resG X h f) = resG Z (fun _ hy => h hy) (c W f))
    (hnil : ∀ W f, IsNilpotent (c W f - (n.app W).hom f)) : Z ⟶ X :=
  ⟨⟨preHom n c hres, fun x => ⟨fun a ha => by
    obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.germ_exist X.presheaf a
    have hU' : n x ∈ U := hU
    have h1 := PresheafedSpace.stalkMap_germ_apply (preHom n c hres) U x hU s
    have h2 : IsUnit ((Z.presheaf.germ (n ⁻¹ᵁ U) x hU').hom (c U s)) := by
      have ha' := ha
      erw [h1] at ha'
      exact ha'
    have h3 : IsUnit ((Z.presheaf.germ (n ⁻¹ᵁ U) x hU').hom ((n.app U).hom s)) := by
      have hn := ((hnil U s).map (Z.presheaf.germ (n ⁻¹ᵁ U) x hU').hom).neg
      have := hn.isUnit_add_left_of_commute h2 (Commute.all _ _)
      simpa using this
    have h4 := Scheme.Hom.germ_stalkMap_apply n U x hU' s
    have h5 : IsUnit ((n.stalkMap x).hom ((X.presheaf.germ U (n x) hU').hom s)) := by
      erw [h4]
      exact h3
    exact (isUnit_map_iff (n.stalkMap x).hom _).mp h5⟩⟩⟩

theorem deform_app {Z X : Scheme.{0}} (n : Z ⟶ X) (c : ∀ W : X.Opens, Γ(X, W) →+* Γ(Z, n ⁻¹ᵁ W))
    (hres : ∀ W W' (h : W' ≤ W) f, c W' (resG X h f) = resG Z (fun _ hy => h hy) (c W f))
    (hnil : ∀ W f, IsNilpotent (c W f - (n.app W).hom f)) (W : X.Opens) :
    (deform n c hres hnil).app W = CommRingCat.ofHom (c W) := rfl

def cH {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ U le_top).hom

theorem cH_eq {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (a : R) :
    constFn p U a = cH p U a := rfl

theorem appLE_cH {R : Type} [CommRing R] {X Y : Scheme.{0}} (p : X ⟶ Sp R) (f : Y ⟶ X) (U : X.Opens)
    (V : Y.Opens) (e : V ≤ f ⁻¹ᵁ U) (a : R) :
    (f.appLE U V e).hom (cH p U a) = cH (f ≫ p) V a := by
  unfold cH
  have key := Scheme.Hom.appLE_comp_appLE f p ⊤ U V le_top e
  rw [← CommRingCat.comp_apply, Category.assoc]
  exact congrArg (fun φ => ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ φ).hom a) key

theorem app_cH {R : Type} [CommRing R] {X Y : Scheme.{0}} (p : X ⟶ Sp R) (f : Y ⟶ X) (U : X.Opens)
    (a : R) : (f.app U).hom (cH p U a) = cH (f ≫ p) (f ⁻¹ᵁ U) a := by
  rw [Scheme.Hom.app_eq_appLE]
  exact appLE_cH p f U (f ⁻¹ᵁ U) le_rfl a

theorem res_cH {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U)
    (a : R) : resG X h (cH p U a) = cH p V a := by
  unfold cH resG
  have key := Scheme.Hom.appLE_map p (U := ⊤) (V := U) (V' := V) le_top (homOfLE h).op
  rw [← CommRingCat.comp_apply, Category.assoc]
  exact congrArg (fun φ => ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ φ).hom a) key

theorem cH_spMap {R S : Type} [CommRing R] [CommRing S] {X : Scheme.{0}} (q : X ⟶ Sp S) (g : R →+* S)
    (U : X.Opens) (a : R) : cH (q ≫ spMap g) U a = cH q U (g a) := by
  unfold cH spMap
  have k1 := Scheme.Hom.comp_appLE q (Spec.map (CommRingCat.ofHom g)) ⊤ U le_top
  have k3 := congrArg (fun φ => (φ ≫ q.appLE ⊤ U le_top).hom a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  simp only [Category.assoc] at k3
  exact (congrArg (fun φ => ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ φ).hom a) k1).trans k3.symm

theorem res_app {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    (f.app V).hom (resG X h a) = resG Y (fun _ hy => h hy) ((f.app U).hom a) := by
  unfold resG
  rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
  rfl

theorem appLE_app_of_section {Y Y' : Scheme.{0}} (ρ : Y' ⟶ Y) (j : Y ⟶ Y') (h : j ≫ ρ = 𝟙 Y)
    (O : Y.Opens) (e : O ≤ j ⁻¹ᵁ (ρ ⁻¹ᵁ O)) (a : Γ(Y, O)) :
    (j.appLE (ρ ⁻¹ᵁ O) O e).hom ((ρ.app O).hom a) = a := by
  have key : ∀ (g : Y ⟶ Y), g = 𝟙 Y → ∀ e' : O ≤ g ⁻¹ᵁ O, (g.appLE O O e').hom a = a := by
    intro g hg e'
    subst hg
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact congrArg (fun φ => φ.hom a) (Y.presheaf.map_id (Opposite.op O))
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  exact key _ h _

theorem ext_cH {R : Type} [CommRing R] {X : Scheme.{0}} (f g : X ⟶ Sp R)
    (h : ∀ a, cH f ⊤ a = cH g ⊤ a) : f = g := by
  have top : ∀ (k : X ⟶ Sp R) (r : R),
      cH k ⊤ r = (Scheme.Γ.map k.op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    intro k r
    have e1 : k.appLE ⊤ ⊤ le_top = k.app ⊤ := k.appLE_eq_app
    unfold cH
    rw [e1]
    rfl
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  ext r
  exact (top f r).symm.trans ((h r).trans (top g r))

def pert {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) (e : C)
    (he : e * e = 0) (d : A → B) (hadd : ∀ f f', d (f + f') = d f + d f')
    (hmul : ∀ f f', d (f * f') = a f * d f' + a f' * d f) : A →+* C where
  toFun f := b (a f) + e * b (d f)
  map_one' := by
    have h := hmul 1 1
    rw [show (1 : A) * 1 = 1 from mul_one 1, map_one] at h
    have h1 : d 1 = 0 := by linear_combination -h
    simp [h1]
  map_zero' := by
    have h := hadd 0 0
    simp only [add_zero] at h
    have h1 : d 0 = 0 := by linear_combination -h
    simp [h1]
  map_add' f f' := by
    simp only [hadd, map_add]; ring
  map_mul' f f' := by
    simp only [hmul, map_add, map_mul]
    linear_combination (-(b (d f) * b (d f'))) * he

theorem exists_mor : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → ∀ (R : Type) [CommRing R] (xD : R →+* DualNumber ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : Y ⟶ X) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)), m ≫ p = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ spMap xD → LocDer q p m (fun r => (xD r).snd) ⊤ d → ∃ Φ : Y' ⟶ X, j ≫ Φ = m ∧ Φ ≫ p = π ≫ spMap xD := by
  intro Y Y' q π ρ j hpb hjρ hjπ R _ xD X p m d hmp hd
  have hee : ∀ V : Y'.Opens, cH π V DualNumber.eps * cH π V DualNumber.eps = 0 := by
    intro V
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  let c : ∀ W : X.Opens, Γ(X, W) →+* Γ(Y', (ρ ≫ m) ⁻¹ᵁ W) := fun W =>
    pert (m.app W).hom (ρ.app (m ⁻¹ᵁ W)).hom (cH π _ DualNumber.eps) (hee _) (d W)
      (hd.add W le_top) (hd.mul W le_top)
  have hres : ∀ W W' (h : W' ≤ W) f,
      c W' (resG X h f) = resG Y' (fun _ hy => h hy) (c W f) := by
    intro W W' h f
    show (ρ.app _).hom ((m.app W').hom (resG X h f)) +
        cH π _ DualNumber.eps * (ρ.app _).hom (d W' (resG X h f)) =
      resG Y' _ ((ρ.app _).hom ((m.app W).hom f) + cH π _ DualNumber.eps * (ρ.app _).hom (d W f))
    have h1 := (congrArg (ρ.app (m ⁻¹ᵁ W')).hom (res_app m h f)).trans
      (res_app ρ (U := m ⁻¹ᵁ W) (V := m ⁻¹ᵁ W') (fun _ hy => h hy) ((m.app W).hom f))
    have h2 := (congrArg (ρ.app (m ⁻¹ᵁ W')).hom (hd.res W W' h le_top f)).trans
      (res_app ρ (U := m ⁻¹ᵁ W) (V := m ⁻¹ᵁ W') (fun _ hy => h hy) (d W f))
    have h3 := (res_cH π (U := ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) (V := ρ ⁻¹ᵁ (m ⁻¹ᵁ W')) (fun _ hy => h hy)
      DualNumber.eps).symm
    rw [map_add, map_mul]
    exact congrArg₂ (· + ·) h1 (congrArg₂ (· * ·) h3 h2)
  have hnil : ∀ W f, IsNilpotent (c W f - ((ρ ≫ m).app W).hom f) := by
    intro W f
    refine ⟨2, ?_⟩
    show ((ρ.app _).hom ((m.app W).hom f) + cH π _ DualNumber.eps * (ρ.app _).hom (d W f) -
      (ρ.app _).hom ((m.app W).hom f)) ^ 2 = 0
    rw [add_sub_cancel_left, mul_pow, sq (cH π _ _), hee, zero_mul]
  have hdual : ∀ x : DualNumber ℂ,
      algebraMap ℂ (DualNumber ℂ) x.fst + DualNumber.eps * algebraMap ℂ (DualNumber ℂ) x.snd = x := by
    intro x
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hfst : ∀ z : DualNumber ℂ, (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom z = z.fst := fun z => rfl
  have hq : ∀ (V : Y.Opens) (z : ℂ),
      (ρ.app V).hom (cH q V z) = cH π (ρ ⁻¹ᵁ V) (algebraMap ℂ (DualNumber ℂ) z) := by
    intro V z
    rw [app_cH, hpb.w, cH_spMap]
  have hc : ∀ W (r : R), c W (cH p W r) = cH π ((ρ ≫ m) ⁻¹ᵁ W) (xD r) := by
    intro W r
    show (ρ.app _).hom ((m.app W).hom (cH p W r)) +
      cH π _ DualNumber.eps * (ρ.app _).hom (d W (cH p W r)) = _
    rw [← cH_eq p W r, hd.base W le_top r]
    simp only [cH_eq]
    rw [app_cH, hmp, ← Category.assoc, cH_spMap, cH_spMap, hq, hq, ← map_mul, ← map_add, hfst,
      hdual]
    rfl
  refine ⟨deform (ρ ≫ m) c hres hnil, ?_, ?_⟩
  · have hb : (j ≫ deform (ρ ≫ m) c hres hnil).base = m.base := by
      show (j ≫ ρ ≫ m).base = m.base
      rw [← Category.assoc, hjρ, Category.id_comp]
    refine Scheme.Hom.ext hb ?_
    intro U
    have hle : m ⁻¹ᵁ U ≤ j ⁻¹ᵁ (ρ ⁻¹ᵁ (m ⁻¹ᵁ U)) := by
      intro x hx
      have hx' : (j ≫ ρ) x = x := by rw [hjρ]; rfl
      show (j ≫ ρ) x ∈ m ⁻¹ᵁ U
      rw [hx']
      exact hx
    apply CommRingCat.hom_ext
    ext f
    change (j.appLE (ρ ⁻¹ᵁ (m ⁻¹ᵁ U)) (m ⁻¹ᵁ U) hle).hom
      (((deform (ρ ≫ m) c hres hnil).app U).hom f) = _
    rw [deform_app]
    show (j.appLE _ _ hle).hom ((ρ.app _).hom ((m.app U).hom f) +
      cH π _ DualNumber.eps * (ρ.app _).hom (d U f)) = _
    rw [map_add, map_mul, appLE_app_of_section ρ j hjρ _ hle, appLE_cH, hjπ, cH_spMap, hfst]
    simp
  · apply ext_cH
    intro r
    rw [cH_spMap]
    have e1 := app_cH p (deform (ρ ≫ m) c hres hnil) ⊤ r
    rw [deform_app] at e1
    have e2 := res_cH (deform (ρ ≫ m) c hres hnil ≫ p)
      (U := (deform (ρ ≫ m) c hres hnil) ⁻¹ᵁ ⊤) (V := ⊤) le_top r
    rw [← e2, ← e1]
    show resG Y' _ (c ⊤ (cH p ⊤ r)) = _
    rw [hc]
    exact res_cH π _ _

end GlobalTheory.KS.DerMor
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_from_const_thickening_of_derivation : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → ∀ (R : Type) [CommRing R] (xD : R →+* DualNumber ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : Y ⟶ X) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)), m ≫ p = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ spMap xD → LocDer q p m (fun r => (xD r).snd) ⊤ d → ∃ Φ : Y' ⟶ X, j ≫ Φ = m ∧ Φ ≫ p = π ≫ spMap xD := by
  atlas_forward_decl GlobalTheory.KS.DerMor.exists_mor
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section
namespace GlobalTheory.KS.ZeroClass
open VertReg

section
variable {R : Type} [CommRing R] {Y X : Scheme.{0}} {q : Y ⟶ Sp ℂ} {p : X ⟶ Sp R} {m : Y ⟶ X} {D : R → ℂ}

theorem locDer_sub {V V' : X.Opens} {d d' : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)} (h : LocDer q p m D V d)
    (h' : LocDer q p m D V' d') : LocDer q p m (fun _ => 0) (V ⊓ V') (fun W f => d W f - d' W f) where
  add W hW f f' := by
    rw [h.add W (hW.trans inf_le_left), h'.add W (hW.trans inf_le_right)]
    abel
  mul W hW f f' := by
    rw [h.mul W (hW.trans inf_le_left), h'.mul W (hW.trans inf_le_right)]
    ring
  res W W' hle hW f := by
    rw [h.res W W' hle (hW.trans inf_le_left), h'.res W W' hle (hW.trans inf_le_right), map_sub]
  base W hW r := by
    rw [h.base W (hW.trans inf_le_left), h'.base W (hW.trans inf_le_right), sub_self,
      ← liftConstHom_apply, map_zero]

theorem ptOf_of_le {V : X.Opens} {d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)} (h : LocDer q p m D V d)
    (y : Sp ℂ ⟶ Y) {W : X.Opens} (hW : W ≤ V) (hy : ⊤ ≤ (y ≫ m) ⁻¹ᵁ W) (f : Γ(X, W)) :
    ptOf V d y W f = valAt' y (m ⁻¹ᵁ W) (d W f) := by
  have hy' : ⊤ ≤ (y ≫ m) ⁻¹ᵁ (W ⊓ V) := (inf_eq_left.mpr hW).symm ▸ hy
  exact val_res h y inf_le_left hW hy' f

theorem ptDer_sub {y : Sp ℂ ⟶ X} {δ δ' : ∀ W : X.Opens, Γ(X, W) → ℂ} (h : PtDer y δ) (h' : PtDer y δ') :
    PtDer y (fun W f => δ W f - δ' W f) := by
  constructor
  · intro W hW f f'
    simp only [h.add W hW, h'.add W hW]
    ring
  · intro W hW f f'
    simp only [h.mul W hW, h'.mul W hW]
    ring
  · intro W W' hle hW f
    simp only [h.res W W' hle hW, h'.res W W' hle hW]

end

theorem ex_add_lattice {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g)
    (z : Fin g → ℂ) (l : u.Λ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).mpr l.2, ← (u.ker 0).mpr (zero_mem _), ← u.ex_add, add_zero]

variable {P₀ : Out.PolAV (Sp ℂ)} {u : HolUnif P₀.A P₀.L P₀.g} {Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ} {χ : u.Λ → ℂ}
  {R : Type} [CommRing R] {x₀ : R →+* ℂ} {X : Scheme.{0}} {p : X ⟶ Sp R} {m : P₀.A.left ⟶ X}

theorem vector_ext (hu : GoodU u Hm χ) (hp : Smooth p) (hm : IsPullback m P₀.A.hom p (spMap x₀)) {V : X.Opens}
    {z : Fin P₀.g → ℂ} (hz : z ∈ dom u m V) {v v' : Fin P₀.g → ℂ}
    (h : ∀ W, W ≤ V → z ∈ dom u m W → ∀ f, fderiv ℂ (fn u m W f) z v = fderiv ℂ (fn u m W f) z v') : v = v' := by
  obtain ⟨W, t, hzW, hdet⟩ := exists_fibre_coords P₀ u Hm χ hu R x₀ X p m hp hm z
  have hzWV : z ∈ dom u m (W ⊓ V) := fun a ha => ⟨hzW ha, hz ha⟩
  have hlin : ∀ (w : Fin P₀.g → ℂ) b, fderiv ℂ (fn u m W (t b)) z w =
      Matrix.vecMul w (Matrix.of fun a b => fderiv ℂ (fn u m W (t b)) z (Pi.single a 1)) b := by
    intro w b
    conv_lhs => rw [← Finset.univ_sum_single w]
    rw [map_sum]
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show Pi.single a (w a) = w a • (Pi.single a 1 : Fin P₀.g → ℂ) by
      ext j; by_cases hj : j = a <;> simp [hj], map_smul, smul_eq_mul]
  have hk : Matrix.vecMul (v - v') (Matrix.of fun a b => fderiv ℂ (fn u m W (t b)) z (Pi.single a 1)) = 0 := by
    ext b
    rw [← hlin, map_sub, Pi.zero_apply, sub_eq_zero]
    have e := h (W ⊓ V) inf_le_right hzWV (resG X inf_le_left (t b))
    rwa [fderiv_fn_resG u m inf_le_left (t b) hzWV] at e
  exact sub_eq_zero.mp (Matrix.eq_zero_of_vecMul_eq_zero hdet hk)

theorem exists_periodic_vector (hu : GoodU u Hm χ) (hp : Smooth p) (hm : IsPullback m P₀.A.hom p (spMap x₀))
    {D : R → ℂ} {s} (hs : KSRel u p m D 0 s) {V : X.Opens} {d} (hd : LocDer P₀.A.hom p m D V d) :
    ∃ w : (Fin P₀.g → ℂ) → (Fin P₀.g → ℂ), DifferentiableOn ℂ w (dom u m V) ∧
      (∀ (l : u.Λ), ∀ z ∈ dom u m V, w (z + l) = w z) ∧
      ∀ W, W ≤ V → ∀ f, ∀ z ∈ dom u m W,
        s z W f = valAt' (u.ex z).left (m ⁻¹ᵁ W) (d W f) + fderiv ℂ (fn u m W f) z (w z) := by
  have hq : ∀ z, (u.ex z).left ≫ P₀.A.hom = 𝟙 _ := fun z => by simp
  have hex : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := fun l z => ex_add_lattice u z l
  have hdomV : IsOpen (dom u m V) := (u.hol (m ⁻¹ᵁ V) 0).1
  have hpt : ∀ z ∈ dom u m V, PtDer ((u.ex z).left ≫ m)
      (fun W f => s z W f - ptOf V d (u.ex z).left W f) ∧
      ∀ r, s z ⊤ (constFn p ⊤ r) - ptOf V d (u.ex z).left ⊤ (constFn p ⊤ r) = 0 := fun z hz =>
    ⟨ptDer_sub (hs.der z) (ptDer_ptOf hd (u.ex z).left hz), fun r => by
      rw [hs.base z r, ptOf_const hd (u.ex z).left (hq z) hz r, sub_self]⟩
  obtain ⟨w, hw, hrep⟩ := GlobalTheory.T.exists_differentiableOn_verticalVectorField P₀ u Hm χ hu R x₀ X p m hp hm P₀.g (dom u m V) id
    (fun z W f => s z W f - ptOf V d (u.ex z).left W f) hdomV differentiable_id hpt
    (fun W f => ((hs.hol W f).mono fun z hz => hz.2).sub
      (((u.hol (m ⁻¹ᵁ (W ⊓ V)) (d (W ⊓ V) (resG X inf_le_left f))).2).mono fun z hz a ha => ⟨hz.2 ha, hz.1 ha⟩))
  refine ⟨w, hw, fun l z hz => ?_, fun W hWV f z hz => ?_⟩
  · have hzl : z + l ∈ dom u m V := by
      show ⊤ ≤ ((u.ex (z + l)).left ≫ m) ⁻¹ᵁ V
      rw [hex]; exact hz
    have hfn : ∀ W (f : Γ(X, W)), fderiv ℂ (fn u m W f) (z + l) = fderiv ℂ (fn u m W f) z := by
      intro W f
      have e : (fun x => fn u m W f (x + l)) = fn u m W f := by
        funext x; simp only [fn, hex]
      rw [← fderiv_comp_add_right, e]
    refine ((GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hu R x₀ X p m hp hm z _ (hpt z hz).1 (hpt z hz).2).unique
      (fun W f hzW => ?_) (fun W f hzW => ?_))
    · have hzlW : z + l ∈ dom u m W := by
        show ⊤ ≤ ((u.ex (z + l)).left ≫ m) ⁻¹ᵁ W
        rw [hex]; exact hzW
      have e := hrep (z + l) hzl W f hzlW
      simp only [id, hex, hfn] at e
      rw [← e, hs.per l W f z hzW, Matrix.zero_mulVec, map_zero, add_zero]
    · exact hrep z hz W f hzW
  · have e := hrep z (fun a ha => hWV (hz ha)) W f hz
    rw [ptOf_of_le hd (u.ex z).left hWV hz f] at e
    simp only [id] at e
    rw [← e]; ring

private theorem valAt'_sub' {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : Γ(X, U)) : valAt' x U (a - b) = valAt' x U a - valAt' x U b := by
  simp only [valAt', dif_pos hx, valAt, map_sub]

private theorem valAt'_add_of_top_le {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : Γ(X, U)) : valAt' x U (a + b) = valAt' x U a + valAt' x U b := by
  simp only [valAt', dif_pos hx, valAt, map_add]

private theorem valAt'_mul_of_top_le {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : Γ(X, U)) : valAt' x U (a * b) = valAt' x U a * valAt' x U b := by
  simp only [valAt', dif_pos hx, valAt, map_mul]

private theorem valAt'_finset_sum {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ U)
    {κ : Type} (s : Finset κ) (F : κ → Γ(X, U)) : valAt' x U (∑ i ∈ s, F i) = ∑ i ∈ s, valAt' x U (F i) := by
  simp only [valAt', dif_pos hx, valAt, map_sum]

private theorem valAt'_comp' {Y X : Scheme.{0}} (y : Sp ℂ ⟶ Y) (m : Y ⟶ X) (W : X.Opens) (f : Γ(X, W)) :
    valAt' (y ≫ m) W f = valAt' y (m ⁻¹ᵁ W) ((m.app W).hom f) := by
  by_cases hy : ⊤ ≤ (y ≫ m) ⁻¹ᵁ W
  · have hy' : ⊤ ≤ y ⁻¹ᵁ (m ⁻¹ᵁ W) := hy
    rw [valAt', dif_pos hy, valAt', dif_pos hy', valAt, valAt]
    first
      | (rw [Scheme.comp_appLE]; rfl)
      | simp [Scheme.comp_appLE]
      | simp [Scheme.Hom.comp_appLE]
  · have hy' : ¬ ⊤ ≤ y ⁻¹ᵁ (m ⁻¹ᵁ W) := hy
    rw [valAt', dif_neg hy, valAt', dif_neg hy']

private theorem valAt'_resG_of_top_le {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {U V : X.Opens} (h : V ≤ U) (hx : ⊤ ≤ x ⁻¹ᵁ V)
    (a : Γ(X, U)) : valAt' x V (resG X h a) = valAt' x U a := by
  have hx' : ⊤ ≤ x ⁻¹ᵁ U := fun p hp => h (hx hp)
  rw [valAt', dif_pos hx, valAt', dif_pos hx', valAt, valAt, resG]
  congr 1
  exact congrArg (fun φ => φ.hom a) (x.map_appLE hx (homOfLE h).op)

private theorem continuousLinearMap_apply_eq_sum_single {n : ℕ} (φ : (Fin n → ℂ) →L[ℂ] ℂ) (w : Fin n → ℂ) :
    φ w = ∑ b, w b * φ (Pi.single b 1) := by
  conv_lhs => rw [← Finset.univ_sum_single w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show Pi.single a (w a) = w a • (Pi.single a 1 : Fin n → ℂ) by
    ext j; by_cases hj : j = a <;> simp [hj], map_smul, smul_eq_mul]

end GlobalTheory.KS.ZeroClass

namespace GlobalTheory.KS
open ZeroClass

theorem regular_of_periods_zero : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D s, IsDer x₀ D → KSRel u p m D 0 s → ∀ W₀, IsAffineOpen W₀ → ∀ W, W ≤ W₀ → ∀ f : Γ(X, W), ∃ a : Γ(P₀.A.left, m ⁻¹ᵁ W), ∀ z ∈ dom u m W, valAt' (u.ex z).left (m ⁻¹ᵁ W) a = s z W f := by
  intro hL P₀ u Hm χ hu R _ x₀ X p m hp hm D s hD hs W₀ hW₀ W hWW₀ f
  choose dd hdd using fun i : X.affineOpens =>
    exists_locDer_of_smooth R x₀ P₀.A.left X P₀.A.hom p m D i.1 hp hm.w hD i.2
  choose ww hww hper hrep using fun i : X.affineOpens => exists_periodic_vector hu hp hm hs (hdd i)
  choose cc hcc using fun i j : X.affineOpens =>
    locDer_regular_coeff P₀ u Hm χ hu R x₀ X p m hp hm _ _ (locDer_sub (hdd i) (hdd j))
  have hrel : ∀ (i j : X.affineOpens) z, z ∈ dom u m (i.1 ⊓ j.1) →
      ww j z - ww i z = fun a => valAt' (u.ex z).left (m ⁻¹ᵁ (i.1 ⊓ j.1)) (cc i j a) := by
    intro i j z hz
    refine vector_ext hu hp hm hz fun W' hW' hzW' f' => ?_
    have e1 := hrep i W' (hW'.trans inf_le_left) f' z hzW'
    have e2 := hrep j W' (hW'.trans inf_le_right) f' z hzW'
    have e3 := hcc i j W' hW' f' z hzW'
    rw [valAt'_sub' (u.ex z).left (m ⁻¹ᵁ W') hzW'] at e3
    rw [map_sub, ← e3]
    linear_combination e1 - e2
  have hcov : ⨆ i : X.affineOpens, m ⁻¹ᵁ i.1 = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    have hy : m.base y ∈ (⨆ i : X.affineOpens, (i.1 : X.Opens)) := by
      rw [iSup_affineOpens_eq_top X]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  let i₀ : X.affineOpens := ⟨W₀, hW₀⟩
  have hcob : ∀ a : Fin P₀.g, ∃ e : Γ(P₀.A.left, m ⁻¹ᵁ W₀), ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W₀) →
      valAt' (u.ex z).left (m ⁻¹ᵁ W₀) e = ww i₀ z a := fun a =>
    algebraic_coboundary_of_holomorphic_coboundary hL P₀ u Hm χ hu X.affineOpens (fun i => m ⁻¹ᵁ i.1)
      (fun i j => cc i j a) (fun i z => ww i z a) hcov
      (fun i => ⟨(differentiableOn_pi.mp (hww i)) a, fun l z hz => congrFun (hper i l z hz) a⟩)
      (fun i j z hz => (congrFun (hrel i j z hz) a).symm) i₀
  choose ee hee using hcob
  choose δ hδ hδv using fun b : Fin P₀.g => invariant_field_algebraic P₀ u Hm χ hu (Pi.single b 1)
  have hW' : m ⁻¹ᵁ W ≤ m ⁻¹ᵁ W₀ := fun y hy => hWW₀ hy
  refine ⟨dd i₀ W f + ∑ b, resG P₀.A.left hW' (ee b) *
    (show Γ(P₀.A.left, m ⁻¹ᵁ W) from δ b (m ⁻¹ᵁ W) ((m.app W).hom f)), fun z hz => ?_⟩
  have hz0 : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W₀) := fun y hy => hWW₀ (hz hy)
  have hzW : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W) := hz
  rw [hrep i₀ W hWW₀ f z hz, valAt'_add_of_top_le _ _ hzW, valAt'_finset_sum _ _ hzW]
  congr 1
  rw [continuousLinearMap_apply_eq_sum_single (fderiv ℂ (fn u m W f) z) (ww i₀ z)]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hv : valAt' (u.ex z).left (m ⁻¹ᵁ W) (show Γ(P₀.A.left, m ⁻¹ᵁ W) from δ b (m ⁻¹ᵁ W) ((m.app W).hom f)) =
      fderiv ℂ (fun z' => valAt' (u.ex z').left (m ⁻¹ᵁ W) ((m.app W).hom f)) z (Pi.single b 1) :=
    hδv b (m ⁻¹ᵁ W) ((m.app W).hom f) z hzW
  have efn : (fun z' => valAt' (u.ex z').left (m ⁻¹ᵁ W) ((m.app W).hom f)) = fn u m W f :=
    funext fun z' => (valAt'_comp' _ _ _ _).symm
  rw [valAt'_mul_of_top_le _ _ hzW, valAt'_resG_of_top_le _ hW' hzW, hee b z hz0, hv, efn]

end GlobalTheory.KS
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_lift_regular_of_periods_zero : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D s, IsDer x₀ D → KSRel u p m D 0 s → ∀ W₀, IsAffineOpen W₀ → ∀ W, W ≤ W₀ → ∀ f : Γ(X, W), ∃ a : Γ(P₀.A.left, m ⁻¹ᵁ W), ∀ z ∈ dom u m W, valAt' (u.ex z).left (m ⁻¹ᵁ W) a = s z W f := by
  atlas_forward_decl GlobalTheory.KS.regular_of_periods_zero
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory

theorem exists_locDer_top_of_ksRel_zero :
    Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D s, IsDer x₀ D → KSRel u p m D 0 s → ∃ d, LocDer P₀.A.hom p m D ⊤ d := by
  intro hL P₀ u Hm χ hu R _ x₀ X p m hp hpb D s hD hs
  have key : ∀ (W : X.Opens) (f : Γ(X, W)), ∃! a : Γ(P₀.A.left, m ⁻¹ᵁ W),
      ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W) → valAt' (u.ex z).left (m ⁻¹ᵁ W) a = s z W f := by
    intro W f
    refine existsUnique_section_of_locally_regular P₀ u Hm χ hu (m ⁻¹ᵁ W) (fun z => s z W f) fun z hz => ?_
    have hz' : ((u.ex z).left ≫ m) (default : PrimeSpectrum ℂ) ∈ W := (top_le_preimage_iff_mem _ _).1 hz
    obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hzW₀, hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hz' W.isOpen
    have hle' : W₀ ≤ W := hle
    obtain ⟨a, ha⟩ := GlobalTheory.T.holomorphic_lift_regular_of_periods_zero hL P₀ u Hm χ hu R x₀ X p m hp hpb D s hD hs W₀ hW₀ W₀ le_rfl (resG X hle' f)
    refine ⟨m ⁻¹ᵁ W₀, a, fun _ hy => hle' hy, (top_le_preimage_iff_mem ((u.ex z).left ≫ m) W₀).2 hzW₀, fun z' hz' => ?_⟩
    exact (ha z' hz').trans ((hs.der z').res W W₀ hle' hz' f)
  choose d hd hu' using key
  have ext : ∀ (W : X.Opens) (f : Γ(X, W)) (a : Γ(P₀.A.left, m ⁻¹ᵁ W)),
      (∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (m ⁻¹ᵁ W) → valAt' (u.ex z).left (m ⁻¹ᵁ W) a = s z W f) → d W f = a :=
    fun W f a h => (hu' W f a h).symm
  refine ⟨d, ⟨fun W _ f f' => ext W _ _ fun z hz => ?_, fun W _ f f' => ext W _ _ fun z hz => ?_,
    fun W W' i _ f => ext W' _ _ fun z hz => ?_, fun W _ r => ext W _ _ fun z hz => ?_⟩⟩
  · rw [valAt'_add, hd W f z hz, hd W f' z hz, (hs.der z).add W hz]
  · rw [valAt'_add, valAt'_mul, valAt'_mul, valAt'_comp, valAt'_comp, hd W f z hz, hd W f' z hz,
      (hs.der z).mul W hz]
  · rw [(hs.der z).res W W' i hz, ← hd W f z fun _ hy => i (hz hy)]
    exact valAt'_res _ _ _ hz
  · have e : constFn p W r = resG X le_top (constFn p ⊤ r) := by
      unfold constFn
      exact (congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
        (Scheme.Hom.appLE_map p (U := ⊤) (V := ⊤) (V' := W) le_top (homOfLE le_top).op)).symm
    rw [e, (hs.der z).res ⊤ W le_top hz, hs.base]
    exact valAt'_constFn _ _ (Over.w (u.ex z)) _ _ hz

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_derivation_of_kodairaSpencer_zero : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ D s, IsDer x₀ D → KSRel u p m D 0 s → ∃ d, LocDer P₀.A.hom p m D ⊤ d := by
  atlas_forward_decl GlobalTheory.exists_locDer_top_of_ksRel_zero
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.ThickeningIso

theorem bijective_of_mod_eps {K B C D : Type} [Field K] [CommRing B] [CommRing C] [CommRing D]
    (a : DualNumber K →+* B) (φ : B →+* C) (p : C →+* D) (hf : (φ.comp a).Flat)
    (hs : Function.Surjective (p.comp φ))
    (hB : RingHom.ker (p.comp φ) = (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom).map a)
    (hC : RingHom.ker p = (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom).map (φ.comp a)) :
    Function.Bijective φ := by
  have hk : RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom = Ideal.span {DualNumber.eps} := by
    ext x
    rw [Ideal.mem_span_singleton', RingHom.mem_ker]
    constructor
    · intro hx
      have hx' : x.fst = 0 := hx
      exact ⟨TrivSqZeroExt.inl x.snd, by ext <;> simp [hx']⟩
    · rintro ⟨y, rfl⟩
      change (y * DualNumber.eps).fst = 0
      simp
  have hB' : ∀ b, p (φ b) = 0 → ∃ b', b = b' * a DualNumber.eps := fun b hb => by
    have : b ∈ RingHom.ker (p.comp φ) := hb
    rw [hB, hk, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at this
    obtain ⟨b', h⟩ := this
    exact ⟨b', h.symm⟩
  have hC' : ∀ c, p c = 0 → ∃ c', c = c' * φ (a DualNumber.eps) := fun c hc => by
    have : c ∈ RingHom.ker p := hc
    rw [hC, hk, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at this
    obtain ⟨b', h⟩ := this
    exact ⟨b', h.symm⟩
  have he : a DualNumber.eps * a DualNumber.eps = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hfl : ∀ c, c * φ (a DualNumber.eps) = 0 → p c = 0 := fun c hc => by
    let _ : Algebra (DualNumber K) C := (φ.comp a).toAlgebra
    have : Module.Flat (DualNumber K) C := hf
    obtain ⟨k, m, y, h1, h2⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
      (R := DualNumber K) (M := C) (f := fun _ : Unit => DualNumber.eps) (x := fun _ => c) (by
        rw [Fintype.sum_unique, Algebra.smul_def, _root_.mul_comm]; exact hc)
    rw [← RingHom.mem_ker, show c = _ from h1 (), hC]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [Algebra.smul_def]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    have h3 := congrArg TrivSqZeroExt.snd (h2 j)
    change (m () j).fst = 0
    simpa using h3
  have h1 : ∀ c, ∃ b c', c = φ b + c' * φ (a DualNumber.eps) := fun c => by
    obtain ⟨b, hb⟩ := hs (p c)
    obtain ⟨c', h⟩ := hC' (c - φ b) (by rw [map_sub, ← hb]; exact sub_self _)
    exact ⟨b, c', by rw [← h]; ring⟩
  refine ⟨(injective_iff_map_eq_zero φ).2 fun b hb => ?_, fun c => ?_⟩
  · obtain ⟨b', rfl⟩ := hB' b (by rw [hb, map_zero])
    obtain ⟨b'', rfl⟩ := hB' b' (hfl _ (by rw [← map_mul, hb]))
    rw [_root_.mul_assoc, he, mul_zero]
  · obtain ⟨b, c', rfl⟩ := h1 c
    obtain ⟨b', c'', rfl⟩ := h1 c'
    refine ⟨b + b' * a DualNumber.eps, ?_⟩
    rw [add_mul, _root_.mul_assoc, ← map_mul φ (a _), he]
    simp

theorem ker_appTop {A C : CommRingCat.{0}} {β : A ⟶ C} (hβ : Function.Surjective β) {Y Z : Scheme.{0}}
    {f : Y ⟶ Spec A} {i : Z ⟶ Y} {f' : Z ⟶ Spec C} (h : IsPullback i f' f (Spec.map β)) [IsAffine Y] :
    RingHom.ker i.appTop.hom =
      (RingHom.ker β.hom).map ((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom := by
  have hpo := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤) le_top
    le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) (isAffineOpen_top _))
  have hpo' : IsPushout ((Scheme.ΓSpecIso A).inv ≫ f.appTop) β i.appTop
      ((Scheme.ΓSpecIso C).inv ≫ f'.appTop) := by
    refine hpo.of_iso (Scheme.ΓSpecIso A) (Iso.refl _) (Scheme.ΓSpecIso C) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    · rw [← Scheme.ΓSpecIso_naturality]
      congr 1
    · simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    · simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  exact PrimeSection.ker_eq_map_of_isPushout hpo' hβ

theorem surjective_fst (K : Type) [Field K] :
    Function.Surjective (TrivSqZeroExt.fstHom K K K).toRingHom := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩

theorem isIso_of_isAffine_of_isIso_appTop {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    [IsIso f.appTop] : IsIso f :=
  (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms _) (arrowIsoSpecΓOfIsAffine f)).mpr
    (inferInstanceAs (IsIso (Spec.map f.appTop)))

theorem isIso_of_isAffine {K : Type} [Field K] {Y Y' Z' : Scheme.{0}} [IsAffine Z'] {q : Y ⟶ Sp K}
    {π' : Z' ⟶ Sp (DualNumber K)} {j : Y ⟶ Y'} {e : Y' ⟶ Z'}
    (h : IsPullback j q (e ≫ π') (spMap (TrivSqZeroExt.fstHom K K K).toRingHom))
    (h' : IsPullback (j ≫ e) q π' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom))
    (hf : Flat (e ≫ π')) : IsIso e := by
  have hs := surjective_fst K
  have h1 : IsClosedImmersion (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) :=
    IsClosedImmersion.spec_of_surjective _ hs
  have h2 : IsClosedImmersion (j ≫ e) := MorphismProperty.of_isPullback h'.flip h1
  have hY : IsAffine Y := isAffine_of_isAffineHom (j ≫ e)
  have hY' : IsAffine Y' := by
    refine AffineThickening.isAffine_of_isPullback_of_sq_eq_bot
      (β := CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) hs ?_ h
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    have : (x * y : DualNumber K) = 0 := by ext <;> simp [hx', hy']
    exact this
  suffices hh : IsIso e.appTop from isIso_of_isAffine_of_isIso_appTop e
  rw [ConcreteCategory.isIso_iff_bijective]
  have k := ker_appTop (β := CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) hs h
  have k' := ker_appTop (β := CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) hs h'
  have hfl : ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫ (e ≫ π').appTop).hom.Flat := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp (.of_bijective (ConcreteCategory.bijective_of_isIso _))
      ((HasRingHomProperty.iff_of_isAffine (P := @Flat)).1 hf)
  have hsur : Function.Surjective (j ≫ e).appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (j ≫ e)).2
  rw [Scheme.Hom.comp_appTop] at k k' hfl hsur
  exact bijective_of_mod_eps
    ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫ π'.appTop).hom e.appTop.hom j.appTop.hom
    hfl hsur k' k

theorem isIso_of_mod_eps : ∀ (Y Y' Z' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (π' : Z' ⟶ Sp (DualNumber ℂ)) (j : Y ⟶ Y') (j' : Y ⟶ Z') (e : Y' ⟶ Z'), IsPullback j q π (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → IsPullback j' q π' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → Flat π → e ≫ π' = π → j ≫ e = j' → IsIso e := by
  rintro Y Y' Z' q _ π' j _ e h h' hf rfl rfl
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) _
    (iSup_affineOpens_eq_top Z')).mpr fun U => ?_
  have : IsAffine U.1 := U.2
  have p1 := (isPullback_morphismRestrict j (e ⁻¹ᵁ U.1))
  have p2 := (isPullback_morphismRestrict e U.1)
  have hw : e ∣_ U.1 ≫ U.1.ι ≫ π' = (e ⁻¹ᵁ U.1).ι ≫ e ≫ π' := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  refine isIso_of_isAffine (K := ℂ) (π' := U.1.ι ≫ π') (j := j ∣_ (e ⁻¹ᵁ U.1))
    (q := (j ⁻¹ᵁ (e ⁻¹ᵁ U.1)).ι ≫ q) ?_ ?_ ?_
  · rw [hw]
    exact p1.paste_vert h
  · exact (p1.paste_horiz p2).paste_vert h'
  · rw [hw]; infer_instance

end GlobalTheory.ThickeningIso
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_thickening_map_of_mod_eps : ∀ (Y Y' Z' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (π' : Z' ⟶ Sp (DualNumber ℂ)) (j : Y ⟶ Y') (j' : Y ⟶ Z') (e : Y' ⟶ Z'), IsPullback j q π (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → IsPullback j' q π' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → Flat π → e ≫ π' = π → j ≫ e = j' → IsIso e := by
  atlas_forward_decl GlobalTheory.ThickeningIso.isIso_of_mod_eps
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem isDer_snd_of_ringHom {R : Type} [CommRing R] (xD : R →+* DualNumber ℂ) :
    IsDer ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp xD) (fun r => (xD r).snd) := by
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · simp only [map_add, TrivSqZeroExt.snd_add]
  · simp only [map_mul, TrivSqZeroExt.snd_mul, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, TrivSqZeroExt.fstHom_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    ring

theorem spMap_fst_comp_algebraMap :
    spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (algebraMap ℂ (DualNumber ℂ)) = 𝟙 (Sp ℂ) := by
  unfold spMap Sp
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

theorem exists_isConst_of_ksRel_zero :
    Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (xD : R →+* DualNumber ℂ) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (φ : A'.left ⟶ A.left) (j : P₀.A.left ⟶ A'.left) (s : (Fin P₀.g → ℂ) → ∀ W : A.left.Opens, Γ(A.left, W) → ℂ), IsAbelianScheme A → IsAbelianScheme A' → IsGrpPullback A' A (spMap xD) φ → IsGrpPullback P₀.A A' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j → KSRel u A.hom (j ≫ φ) (fun r => (xD r).snd) 0 s → ∃ ρ, IsConst A' P₀.A ρ j := by
  intro hL P₀ u Hm χ hU R _ xD A _ A' _ φ j s hA hA' hφ hj hKS

  have hcomp : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap xD =
      spMap ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp xD) := by
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hsq : IsPullback (j ≫ φ) P₀.A.hom A.hom
      (spMap ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp xD)) := by
    rw [← hcomp]
    exact hj.1.paste_horiz hφ.1

  obtain ⟨d, hd⟩ := GlobalTheory.T.exists_global_derivation_of_kodairaSpencer_zero hL P₀ u Hm χ hU R _ A.left A.hom (j ≫ φ) hA.smooth hsq
    (fun r => (xD r).snd) s (isDer_snd_of_ringHom xD) hKS

  obtain ⟨Y', ρ, π, hpb⟩ : ∃ (Y' : Scheme.{0}) (ρ : Y' ⟶ P₀.A.left) (π : Y' ⟶ Sp (DualNumber ℂ)),
      IsPullback ρ π P₀.A.hom (spMap (algebraMap ℂ (DualNumber ℂ))) :=
    ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  have hw : 𝟙 P₀.A.left ≫ P₀.A.hom =
      (P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ spMap (algebraMap ℂ (DualNumber ℂ)) := by
    rw [Category.assoc, spMap_fst_comp_algebraMap, Category.comp_id, Category.id_comp]
  obtain ⟨i, hiρ, hiπ⟩ := hpb.exists_lift (𝟙 _) (P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) hw

  have hm : (j ≫ φ) ≫ A.hom =
      P₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap xD := by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, hj.1.w, Category.assoc]
  obtain ⟨Φ, hiΦ, hΦ⟩ :=
    GlobalTheory.T.exists_hom_from_const_thickening_of_derivation P₀.A.left Y' P₀.A.hom π ρ i hpb hiρ hiπ R xD A.left A.hom (j ≫ φ) d hm hd

  obtain ⟨e, heφ, heπ⟩ := hφ.1.exists_lift Φ π hΦ
  have hie : i ≫ e = j := by
    refine hφ.1.hom_ext ?_ ?_
    · rw [Category.assoc, heφ, hiΦ]
    · rw [Category.assoc, heπ, hiπ, hj.1.w]

  have hpb' := (GlobalTheory.T.const_thickening_complex_functions_structure P₀.A.left Y' P₀.A.hom π ρ i hpb hiρ hiπ).2.1
  have := P₀.isAb.smooth
  have hfl : Flat π := MorphismProperty.of_isPullback (P := @Flat) hpb inferInstance
  have he : IsIso e := GlobalTheory.T.isIso_thickening_map_of_mod_eps P₀.A.left Y' A'.left P₀.A.hom π A'.hom i j e hpb' hj.1 hfl heπ hie

  have hsq2 : IsPullback (inv e) A'.hom π (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, IsIso.inv_comp_eq, heπ]⟩
  have hρ₀ : IsPullback (inv e ≫ ρ) A'.hom P₀.A.hom (spMap (algebraMap ℂ (DualNumber ℂ))) := by
    have h := hsq2.paste_horiz hpb
    rwa [Category.id_comp] at h
  have hjρ : j ≫ inv e ≫ ρ = 𝟙 _ := by
    rw [← hie, Category.assoc, IsIso.hom_inv_id_assoc, hiρ]
  exact exists_isConst_of_isPullback hL P₀.A A' (inv e ≫ ρ) j P₀.isAb hA' hj hρ₀ hjρ

end GlobalTheory.KS
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isConst_of_ksRel_zero' : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (xD : R →+* DualNumber ℂ) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (φ : A'.left ⟶ A.left) (j : P₀.A.left ⟶ A'.left) (s : (Fin P₀.g → ℂ) → ∀ W : A.left.Opens, Γ(A.left, W) → ℂ), IsAbelianScheme A → IsAbelianScheme A' → IsGrpPullback A' A (spMap xD) φ → IsGrpPullback P₀.A A' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j → KSRel u A.hom (j ≫ φ) (fun r => (xD r).snd) 0 s → ∃ ρ, IsConst A' P₀.A ρ j := by
  atlas_forward_decl GlobalTheory.KS.exists_isConst_of_ksRel_zero
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.KerZero

def derPt {o R : Type} [CommRing o] [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ]
    (D : Derivation o R ℂ) : R →+* DualNumber ℂ where
  toFun r := TrivSqZeroExt.inl (algebraMap R ℂ r) + TrivSqZeroExt.inr (D r)
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [Algebra.smul_def, mul_comm, TrivSqZeroExt.algebraMap_eq_inl]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap f' ≫ spMap f = spMap (f'.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]; rfl

theorem spMap_inj {R R' : Type} [CommRing R] [CommRing R'] {f f' : R →+* R'} (h : spMap f = spMap f') : f = f' := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

theorem derivation_eq_zero_of_ks_zero : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (R : Type) [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (t : TObj g k J b (spMap (algebraMap o R))) (s₀ : Sp ℂ ⟶ Sp o) (t₀ : TObj g k J b s₀) (m : t₀.A.left ⟶ t.A.left) (u : HolUnif t₀.pol.A t₀.pol.L t₀.pol.g) (Hm : Matrix (Fin t₀.pol.g) (Fin t₀.pol.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → (IsGrpPullback t₀.A t.A (spMap (algebraMap R ℂ)) m ∧ LBIso t₀.L (t.L.pull m) ∧ (∀ i, (t₀.pt i).left ≫ m = (spMap (algebraMap R ℂ)) ≫ (t.pt i).left) ∧ ∀ jj, (t₀.act jj).left ≫ m = m ≫ (t.act jj).left) → (∀ (x : Sp (DualNumber ℂ) ⟶ Sp R) (t' : TObj g k J b (x ≫ spMap (algebraMap o R))), x ≫ spMap (algebraMap o R) = constPt x ≫ spMap (algebraMap o R) → TMap t' t x → TMap t' t (constPt x) → x = constPt x) → ∀ (D : Derivation o R ℂ) s, KSRel u t.A.hom m (fun r => D r) 0 s → D = 0 := by
  intro h₁ h₂ h₃ o _ g k J b R _ _ _ _ _ t s₀ t₀ m u Hm χ hu hm hun D s hs
  obtain ⟨hm₁, hm₂, hm₃, hm₄⟩ := hm
  have hfst : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (derPt D) = spMap (algebraMap R ℂ) := by
    rw [spMap_comp]; congr 1; ext r; simp [derPt]
  obtain ⟨t', ht'⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g k J b _ _ _ _ (spMap (derPt D)) t rfl
  obtain ⟨φ, hφ₁, hφ₂, hφ₃, hφ₄⟩ := id ht'
  have hp := hφ₁.1
  let j : t₀.A.left ⟶ t'.A.left := hp.lift m (t₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)
    (by rw [hm₁.1.w, Category.assoc, hfst])
  have hj : j ≫ φ = m := hp.lift_fst _ _ _
  have hw : j ≫ t'.A.hom = t₀.A.hom ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom := hp.lift_snd _ _ _
  have hj₁ : IsGrpPullback t₀.A t'.A (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) j :=
    hφ₁.cancel (hm₁.congr hfst.symm hj.symm) hw
  have hj₂ : LBIso t₀.L (t'.L.pull j) :=
    LBIso.trans t₀.isLB (pull_isLB t.isLB m) (pull_isLB t'.isLB j) hm₂
      (LBIso.chartPull (chartPullPull t'.L j j rfl) (chartPullSame t.L _ _ _ j fun _ => hj.symm) hφ₂).symm
  have hj₃ : ∀ i, (t₀.pt i).left ≫ j = (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ (t'.pt i).left := by
    intro i
    apply hp.hom_ext
    · rw [Category.assoc, hj, hm₃, Category.assoc, hφ₃, ← Category.assoc, hfst]
    · have a₁ : (t₀.pt i).left ≫ t₀.A.hom = 𝟙 _ := Over.w (t₀.pt i)
      have a₂ : (t'.pt i).left ≫ t'.A.hom = 𝟙 _ := Over.w (t'.pt i)
      rw [Category.assoc, hw, ← Category.assoc, a₁, Category.assoc, a₂]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  have hj₄ : ∀ jj, (t₀.act jj).left ≫ j = j ≫ (t'.act jj).left := by
    intro a
    apply hp.hom_ext
    · rw [Category.assoc, hj, hm₄, Category.assoc, hφ₄, ← Category.assoc, hj]
    · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w, hw]
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_isConst_of_ksRel_zero' h₁ t₀.pol u Hm χ hu R (derPt D) t.A t'.A φ j s t.ab t'.ab hφ₁ hj₁ (by
    have e : (fun r => (derPt D r).snd) = fun r => D r := by funext r; simp [derPt]
    rw [e]
    exact hj ▸ hs)
  have hc := GlobalTheory.T.thetaObject_constantFamily_dualNumbers_isPullback h₁ h₂ h₃ o g k J b s₀ _ t₀ t' ρ j hρ ⟨hj₁, hj₂, hj₃, hj₄⟩
  have hcp : constPt (spMap (derPt D)) = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (algebraMap R ℂ) := by
    rw [constPt, hfst]
  have hc' : TMap t' t (constPt (spMap (derPt D))) := by
    rw [hcp]
    exact ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g k J b _ _ _ _ _ _ t t₀ t').2 _ _ ⟨m, hm₁, hm₂, hm₃, hm₄⟩).1 hc
  have hx := hun (spMap (derPt D)) t' (by
    rw [hcp, spMap_comp, spMap_comp, spMap_comp]
    congr 1
    ext r <;> simp [derPt, TrivSqZeroExt.algebraMap_eq_inl]) ht' hc'
  rw [hcp, spMap_comp] at hx
  have hx' := spMap_inj hx
  ext r
  have := congrArg (fun f : R →+* DualNumber ℂ => (f r).snd) hx'
  simpa [derPt, TrivSqZeroExt.algebraMap_eq_inl] using this

end GlobalTheory.KS.KerZero
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivation_eq_zero_of_kodairaSpencer_zero : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (R : Type) [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (t : TObj g k J b (spMap (algebraMap o R))) (s₀ : Sp ℂ ⟶ Sp o) (t₀ : TObj g k J b s₀) (m : t₀.A.left ⟶ t.A.left) (u : HolUnif t₀.pol.A t₀.pol.L t₀.pol.g) (Hm : Matrix (Fin t₀.pol.g) (Fin t₀.pol.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → (IsGrpPullback t₀.A t.A (spMap (algebraMap R ℂ)) m ∧ LBIso t₀.L (t.L.pull m) ∧ (∀ i, (t₀.pt i).left ≫ m = (spMap (algebraMap R ℂ)) ≫ (t.pt i).left) ∧ ∀ jj, (t₀.act jj).left ≫ m = m ≫ (t.act jj).left) → (∀ (x : Sp (DualNumber ℂ) ⟶ Sp R) (t' : TObj g k J b (x ≫ spMap (algebraMap o R))), x ≫ spMap (algebraMap o R) = constPt x ≫ spMap (algebraMap o R) → TMap t' t x → TMap t' t (constPt x) → x = constPt x) → ∀ (D : Derivation o R ℂ) s, KSRel u t.A.hom m (fun r => D r) 0 s → D = 0 := by
  atlas_forward_decl GlobalTheory.KS.KerZero.derivation_eq_zero_of_ks_zero
end
