import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullG

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
set_option autoImplicit false
noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TorsSpec

def ValAt {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) {V : Scheme.{0}} (ℓ : V ⟶ X') {M : Type}
    (w : M → (V ⟶ G.left)) (p : (torsion G n).left) (c : M) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (y : Sp Ω ⟶ Spec ((torsion G n).left.presheaf.stalk p)) (z : Sp Ω ⟶ V),
    y ≫ (torsion G n).left.fromSpecStalk p ≫ (torsion G n).hom = z ≫ ℓ →
      y ≫ (torsion G n).left.fromSpecStalk p ≫ (torsion.ι G n).left = z ≫ w c

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem etaSec_w (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X')
    (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (b : Dw.La) :
    (i₀ TF.Y Z ≫ (TF.Y.oF.eta b).left ≫ TF.Y.m.φ) ≫ TF.Y.t.G.hom = ℓ ≫ φ ≫ (barComp TF.Y Z).ι := by
  have h1 := TF.Y.m.cart.1.w
  have h2 := Over.w (TF.Y.oF.eta b)
  simp only [Category.assoc] at h1 ⊢
  rw [h1, ← Category.assoc ((TF.Y.oF.eta b).left), h2, reassoc_of% hℓ, j₀_ι]
  exact congrArg (i₀ TF.Y Z ≫ ·) (Category.id_comp _)

def etaSec (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X')
    (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (b : Dw.La) : V₀ TF.Y Z ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left :=
  pullback.lift _ _ (etaSec_w TF Z φ ℓ hℓ b)

theorem eta_eq_of_mk_eq (TF : TorFlag Xo c) {b b' : Dw.La}
    (h : (Submodule.Quotient.mk b : LevelMod Dw l) = Submodule.Quotient.mk b') :
    TF.Y.oF.eta b = TF.Y.oF.eta b' := by
  rw [Submodule.Quotient.eq] at h
  have := TF.Y.oF.eta_add b' (b - b')
  rwa [add_sub_cancel, TF.Y.oF.eta_ker _ h, mul_one] at this

def etaSecL (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X')
    (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (x : LevelMod Dw l) : V₀ TF.Y Z ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left :=
  Quot.liftOn x (etaSec TF Z φ ℓ hℓ) fun b b' h => by
    have e := eta_eq_of_mk_eq TF (b := b) (b' := b') (Quot.sound h)
    unfold etaSec
    congr 2
    rw [e]

theorem etaSecL_w (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X')
    (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (x : LevelMod Dw l) :
    etaSecL TF Z φ ℓ hℓ x ≫ (GlobalTheory.EqvAct.pullG TF Z φ).hom = ℓ := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact pullback.lift_snd _ _ _

theorem etaSecL_ψ (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}} (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X')
    (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (b : Dw.La) :
    etaSecL TF Z φ ℓ hℓ (Submodule.Quotient.mk b) ≫ GlobalTheory.EqvAct.pullψ TF Z φ =
      i₀ TF.Y Z ≫ (TF.Y.oF.eta b).left ≫ TF.Y.m.φ :=
  pullback.lift_fst _ _ _

end GlobalTheory.TorsSpec
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
set_option autoImplicit false
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory CartesianMonoidalCategory MonObj

open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TorsSpec

theorem act_natCast {E : Type} [Field E] {X' : Scheme.{0}} {G : Over X'} [GrpObj G] (act : OAct (𝓞 E) G) (n : ℕ) :
    act.act (n : 𝓞 E) = mulN G n := by
  induction n with
  | zero =>
    have h := act.add 0 0
    rw [add_zero] at h
    have h0 : act.act 0 = 1 := mul_eq_left.mp h.symm
    rw [Nat.cast_zero, h0, Hom.one_def]
    rfl
  | succ n ih =>
    rw [Nat.cast_succ, act.add, ih, act.one, Hom.mul_def]
    rfl

theorem eta_comp_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : η[G'].left ≫ φ = f ≫ η[G].left := by
  have hw : (η[G'].left ≫ φ) ≫ G.hom = (Over.mk ((𝟙_ (Over S')).hom ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w η[G']]
    rfl
  let x₀ : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G := Over.homMk (η[G'].left ≫ φ) hw
  have h1 : (η[G'] : 𝟙_ (Over S') ⟶ G') * η[G'] = η[G'] := by
    have e : (η[G'] : 𝟙_ (Over S') ⟶ G') = 1 := by
      rw [Hom.one_def]
      exact (Category.id_comp _).symm.trans (congrArg (· ≫ η[G']) (toUnit_unique _ _))
    rw [e, _root_.mul_one]
  have h2 := h.2 (𝟙_ (Over S')) η[G'] η[G'] x₀ x₀ rfl rfl
  rw [h1] at h2
  have h3 : x₀ * x₀ = x₀ := Over.OverMorphism.ext h2
  have h4 : x₀ = 1 := mul_eq_left.mp h3
  have h5 := congrArg (fun q => q.left) h4
  simp only [x₀, Over.homMk_left] at h5
  rw [h5, Hom.one_def, Over.comp_left]
  congr 1

theorem exists_lift_torsion {X' : Scheme.{0}} {G : Over X'} [GrpObj G] (n : ℕ) {Y : Over X'} (a : Y ⟶ G)
    (h : a ≫ mulN G n = 1) : ∃ aT : Y ⟶ torsion G n, aT ≫ torsion.ι G n = a :=
  ⟨pullback.lift a (toUnit Y) (by rw [h, Hom.one_def]), pullback.lift_fst _ _ _⟩

theorem mono_torsion_ι {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) : Mono (torsion.ι G n).left := by
  have : Mono (η[G] : 𝟙_ (Over X') ⟶ G) := ⟨fun g h _ => toUnit_unique g h⟩
  have : Mono (torsion.ι G n) := ⟨fun a b hab => pullback.hom_ext hab (toUnit_unique _ _)⟩
  infer_instance

theorem isDomain_stalk_of_etale {X' W : Scheme.{0}} [GlobalTheory.IsNormalScheme X'] (h : W ⟶ X') [Etale h] (q : W) :
    IsDomain (W.presheaf.stalk q) :=
  (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth h
    (fun y => ⟨GlobalTheory.IsNormalScheme.isDomain_stalk y, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk y⟩) q).1

end GlobalTheory.TorsSpec
end
end
