import Development.EtaleCohomology.EtaleSheaves.LeafKumDeltaPf
import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuUnitsPf
import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuInjPf
import Development.EtaleCohomology.TateTwists.EtaleLocalPropertyBasicClosureProperties
import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuSurjPf
import Development.EtaleCohomology.EtaleSheaves.KummerSequence.KummerH0Surjection

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.H2CurveOrder.LeafKumMuMapPf

theorem prim_pow (q : ℕ) {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨g, hg⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hg
  simpa [sub_eq_zero, ζ.2.2] using h

variable (q : ℕ) [NeZero q]

def unitOf {A : Type} [CommRing A] (ζ : Prim q A) : Aˣ :=
  (IsUnit.of_pow_eq_one (prim_pow q ζ) (NeZero.ne q)).unit

@[simp] theorem unitOf_val {A : Type} [CommRing A] (ζ : Prim q A) : ((unitOf q ζ : Aˣ) : A) = ζ.1 := rfl

theorem unitOf_pow {A : Type} [CommRing A] (ζ : Prim q A) : unitOf q ζ ^ q = 1 :=
  Units.ext (by simp [prim_pow])

def gOf {A : Type} [CommRing A] (ζ : Prim q A) : ZMod q →+ Additive Aˣ :=
  ZMod.lift q ⟨zmultiplesHom _ (Additive.ofMul (unitOf q ζ)), by
    change ((q : ℤ) • Additive.ofMul (unitOf q ζ)) = 0
    rw [natCast_zsmul, ← ofMul_pow, unitOf_pow]; rfl⟩

theorem gOf_int {A : Type} [CommRing A] (ζ : Prim q A) (n : ℤ) :
    gOf q ζ (n : ZMod q) = n • Additive.ofMul (unitOf q ζ) := by
  simp [gOf, ZMod.lift_coe]

theorem gOf_one {A : Type} [CommRing A] (ζ : Prim q A) : gOf q ζ 1 = Additive.ofMul (unitOf q ζ) := by
  have := gOf_int q ζ 1
  simpa using this

def nuA (A : Type) [CommRing A] : (Prim q A →₀ ULift.{1} (ZMod q)) →+ Additive Aˣ :=
  Finsupp.liftAddHom (fun ζ => (gOf q ζ).comp (AddEquiv.ulift.toAddMonoidHom))

theorem nuA_single (A : Type) [CommRing A] (ζ : Prim q A) (b : ULift.{1} (ZMod q)) :
    nuA q A (Finsupp.single ζ b) = gOf q ζ b.down := by
  simp [nuA]; rfl

theorem nuA_smul (A : Type) [CommRing A] (n : ℤ) (x : Prim q A →₀ ULift.{1} (ZMod q)) :
    nuA q A ((ULift.up (n : ZMod q) : ULift.{1} (ZMod q)) • x) = n • nuA q A x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | single ζ b =>
    rw [Finsupp.smul_single, nuA_single, nuA_single, ← map_zsmul]
    congr 1
    change (n : ZMod q) * b.down = n • b.down
    rw [zsmul_eq_mul]

theorem nuA_rel (A : Type) [CommRing A] : ∀ x ∈ twRel q 1 A, nuA q A x = 0 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ζ, ξ, a, h, rfl⟩ := hx
    rw [map_sub, nuA_single, nuA_single, zpow_one]
    change gOf q ξ 1 - gOf q ζ (a : ZMod q) = 0
    have ha : ((a : ZMod q)) = (((a : ZMod q).val : ℤ) : ZMod q) := by simp
    rw [ha, gOf_int, gOf_one, sub_eq_zero, natCast_zsmul, ← ofMul_pow]
    congr 1
    exact Units.ext (by simp [h])
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx =>
    have hc : c = ULift.up (((c.down.cast : ℤ)) : ZMod q) := by
      ext; simp
    rw [hc, nuA_smul, hx, smul_zero]

def nuQ (A : CommRingCat.{0}) : (twF q 1).obj A →+ Additive Aˣ :=
  QuotientAddGroup.lift (twRel q 1 A).toAddSubgroup (nuA q A) (fun x hx => nuA_rel q A x hx)

theorem nuQ_smul (A : CommRingCat.{0}) (n : ℤ) (x : (twF q 1).obj A) :
    nuQ q A ((ULift.up (n : ZMod q) : ULift.{1} (ZMod q)) • x) = n • nuQ q A x := by
  induction x using Submodule.Quotient.induction_on with
  | H x => exact nuA_smul q A n x

theorem unitOf_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (ζ : Prim q A) :
    unitOf q (ζ.map f) = Units.map f.toMonoidHom (unitOf q ζ) := Units.ext rfl

theorem nuQ_nat {A B : CommRingCat.{0}} (f : A ⟶ B) (x : (twF q 1).obj A) :
    nuQ q B (((twF q 1).map f).hom x) = MonoidHom.toAdditive (Units.map f.hom.toMonoidHom) (nuQ q A x) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    change nuA q B (Finsupp.mapDomain (Prim.map f.hom) x) = MonoidHom.toAdditive (Units.map f.hom.toMonoidHom) (nuA q A x)
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [Finsupp.mapDomain_add, map_add, map_add, map_add, hx, hy]
    | single ζ b =>
      rw [Finsupp.mapDomain_single, nuA_single, nuA_single]
      have hb : b.down = ((b.down.cast : ℤ) : ZMod q) := by simp
      rw [hb, gOf_int, gOf_int, map_zsmul, unitOf_map]
      rfl

abbrev fq : ULift.{1} ℤ →+* ULift.{1} (ZMod q) :=
  (ULift.ringEquiv.symm : ZMod q ≃+* ULift.{1} (ZMod q)).toRingHom.comp
    ((Int.castRingHom (ZMod q)).comp (ULift.ringEquiv : ULift.{1} ℤ ≃+* ℤ).toRingHom)

def nuR : twF q 1 ⋙ ModuleCat.restrictScalars.{1} (fq q) ⟶ unitsF where
  app A :=
    letI : Module (ULift.{1} ℤ) ((twF q 1).obj A) := Module.compHom _ (fq q)
    ModuleCat.ofHom (show (ModuleCat.restrictScalars.{1} (fq q)).obj ((twF q 1).obj A) →ₗ[ULift.{1} ℤ]
      ULift.{1} (Additive (A : Type)ˣ) from
    { toFun := fun x => ULift.up (nuQ q A x)
      map_add' := fun x y => congrArg ULift.up (map_add _ x y)
      map_smul' := fun c x => congrArg ULift.up (nuQ_smul q A c.down x) })
  naturality A B f := by
    ext x
    exact congrArg ULift.up (nuQ_nat q f x)

theorem nuQ_q (A : CommRingCat.{0}) (x : (twF q 1).obj A) : q • nuQ q A x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    change q • nuA q A x = 0
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]
    | single ζ b =>
      rw [nuA_single, ← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero]

theorem nuR_pow : nuR q ≫ LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powNat q = 0 := by
  ext A x
  exact congrArg ULift.up (nuQ_q q A x)

abbrev rs := ModuleCat.restrictScalars.{1} (fq q)
abbrev cs := ModuleCat.coextendScalars.{1, 1, 1} (fq q)

instance : (cs q).IsRightAdjoint := (ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} (fq q)).isRightAdjoint

abbrev adjW := Adjunction.whiskerRight Scheme.{0}ᵒᵖ (ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} (fq q))

theorem wr_zero {X Y : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))} :
    ((Functor.whiskeringRight _ _ _).obj (rs q)).map (0 : X ⟶ Y) = 0 := by
  ext U x
  rfl

abbrev nuP : Scheme.Γ ⋙ twF q 1 ⋙ rs q ⟶ Scheme.Γ ⋙ unitsF := Functor.whiskerLeft Scheme.Γ (nuR q)

abbrev tG : Scheme.Γ ⋙ unitsF ⟶ Gm.obj := toSheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ unitsF)

abbrev psi : Scheme.Γ ⋙ twF q 1 ⟶ Gm.obj ⋙ cs q :=
  (adjW q).homEquiv _ _ (nuP q ≫ tG)

theorem hC : Presheaf.IsSheaf Scheme.etaleTopology.{0} (Gm.obj ⋙ cs q) :=
  ((sheafCompose Scheme.etaleTopology.{0} (cs q)).obj Gm).property

abbrev psi' : sheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ twF q 1) ⟶ Gm.obj ⋙ cs q :=
  sheafifyLift Scheme.etaleTopology.{0} (psi q) (hC q)

def kappa : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm :=
  ⟨((adjW q).homEquiv _ _).symm (psi' q)⟩

theorem key : Functor.whiskerRight (toSheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ twF q 1)) (rs q) ≫ (kappa q).hom =
    nuP q ≫ tG := by
  change ((Functor.whiskeringRight _ _ _).obj (rs q)).map (toSheafify _ _) ≫ ((adjW q).homEquiv _ _).symm (psi' q) = _
  rw [← Adjunction.homEquiv_naturality_left_symm, toSheafify_sheafifyLift]
  exact Equiv.symm_apply_apply _ _

theorem homEquiv_zero {X : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))} {Y : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} ℤ)} :
    (adjW q).homEquiv X Y 0 = 0 := by
  have h : (0 : ((Functor.whiskeringRight _ _ _).obj (rs q)).obj X ⟶ Y) =
      ((Functor.whiskeringRight _ _ _).obj (rs q)).map (0 : X ⟶ X) ≫ 0 := by rw [wr_zero, zero_comp]
  rw [h, Adjunction.homEquiv_naturality_left, zero_comp]

theorem homEquiv_symm_zero {X : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))} {Y : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} ℤ)} :
    ((adjW q).homEquiv X Y).symm 0 = 0 := by
  rw [← homEquiv_zero q, Equiv.symm_apply_apply]

omit [NeZero q] in
theorem hpv : tG ≫ (LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powGm q).hom = Functor.whiskerLeft Scheme.Γ (LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powNat q) ≫ tG :=
  (toSheafify_naturality _ _).symm

theorem kappa_pow : kappa q ≫ LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powGm q = 0 := by
  apply (sheafToPresheaf Scheme.etaleTopology.{0} _).map_injective
  rw [Functor.map_comp, Functor.map_zero]
  change ((adjW q).homEquiv _ _).symm (psi' q) ≫ (LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powGm q).hom = 0
  rw [← Adjunction.homEquiv_naturality_right_symm]
  have h0 : psi' q ≫ ((Functor.whiskeringRight _ _ _).obj (cs q)).map (LateralTheory.E.H2CurveOrder.LeafKumSeqPf.powGm q).hom = 0 := by
    apply sheafify_hom_ext _ _ _ (hC q)
    rw [comp_zero, ← Category.assoc, toSheafify_sheafifyLift, ← Adjunction.homEquiv_naturality_right,
      Category.assoc, hpv, ← Category.assoc, ← Functor.whiskerLeft_comp, nuR_pow]
    have hz : Functor.whiskerLeft Scheme.Γ (0 : twF q 1 ⋙ rs q ⟶ unitsF) = 0 := by ext U x; rfl
    rw [hz, zero_comp, homEquiv_zero]
  rw [h0, homEquiv_symm_zero]

theorem gen_kappa : LateralTheory.E.H2CurveOrder.LeafKumMuUnitsPf.Gen q (kappa q) := by
  intro U ζ u hu
  have := congrArg (fun η => (η.app (op U)).hom
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q 1).obj Γ(U, ⊤))) (key q)
  refine this.trans ?_
  exact congrArg (fun y => ((toSheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ unitsF)).app (op U)).hom y)
    (congrArg ULift.up ((nuA_single q _ ζ 1).trans ((gOf_one q ζ).trans (congrArg _ (Units.ext hu.symm)))))

theorem LeafKumMuMap_of : LateralTheory.E.H2CurveOrder.LeafKumMuUnitsPf.LeafKumMuMap := by
  intro q _ B _ _
  exact ⟨kappa q, kappa_pow q, gen_kappa q⟩

end LateralTheory.E.H2CurveOrder.LeafKumMuMapPf
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.E.H2CurveOrder.LeafKumMuInjPfGlue
open LateralTheory.E.H2CurveOrder.LeafKumMuInjPf

theorem cycPow : CycPow := by
  intro q A _ ζ
  obtain ⟨hq, hz⟩ := ζ.2
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · have : Subsingleton A := by
      simp at hz
      exact subsingleton_of_zero_eq_one hz.symm
    exact ⟨1, Subsingleton.elim _ _, fun _ _ => Or.inr this⟩
  have hqz : ζ.1 ^ q = 1 := by
    obtain ⟨G, hG⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
    have := congrArg (aeval ζ.1) hG
    simp [hz] at this
    exact sub_eq_zero.1 this
  have h1 : ζ.1 * ζ.1 ^ (q - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel hq0]; exact hqz
  have hu : IsUnit ζ.1 := ⟨⟨ζ.1, ζ.1 ^ (q - 1), h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  refine ⟨hu.unit, rfl, fun c hc => ?_⟩
  have hc' : ζ.1 ^ c = 1 := by simpa using congrArg Units.val hc
  set d := Nat.gcd c q with hd
  have hdz : ζ.1 ^ d = 1 := pow_gcd_eq_one.2 ⟨hc', hqz⟩
  by_cases hdq : d = q
  · left; rw [← hdq]; exact Nat.gcd_dvd_left c q
  right
  obtain ⟨G, hG⟩ := X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ (Nat.mem_properDivisors.2 ⟨Nat.gcd_dvd_right c q, lt_of_le_of_ne (Nat.le_of_dvd hq0 (Nat.gcd_dvd_right c q)) hdq⟩)
  have hG' := congrArg (Polynomial.map (Int.castRingHom A)) hG
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
    map_cyclotomic] at hG'
  have r1 : (X - C ζ.1) ∣ (X ^ d - 1 : A[X]) := dvd_iff_isRoot.2 (by simp [hdz])
  have r2 : (X - C ζ.1) ∣ cyclotomic q A := dvd_iff_isRoot.2 (by
    have := hz
    rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic] at this)
  obtain ⟨a, ha⟩ := r1
  obtain ⟨b, hb⟩ := r2
  have hE : (X ^ q - 1 : A[X]) = (X - C ζ.1) ^ 2 * (a * b * G.map (Int.castRingHom A)) := by
    rw [hG', ha, hb]; ring
  have hD := congrArg (fun p => eval ζ.1 (derivative p)) hE
  simp [derivative_mul, derivative_pow] at hD
  have hu' : IsUnit ((q : A) * ζ.1 ^ (q - 1)) := hq.mul (hu.pow _)
  have h0 : (q : A) * ζ.1 ^ (q - 1) = 0 := by simpa using hD
  rw [h0] at hu'
  exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hu')

theorem emptySec : EmptySec := by
  intro R _ F V hs y
  have : IsEmpty V := by
    refine ⟨fun x => ?_⟩
    have h1 : (1 : V.presheaf.stalk x) = 0 := by
      rw [← map_one (V.presheaf.germ ⊤ x trivial).hom, Subsingleton.elim (1 : Γ(V, ⊤)) 0, map_zero]
    exact one_ne_zero h1
  exact LateralTheory.E.H2CurveOrder.LeafKumMuInjPf.shfSep R F V y (LateralTheory.EtaleFoundations.LocBasicPf.loc_empty V _)

theorem LeafKumMuInj_of (hL : TwLocGen) (hG : GmSep) : LateralTheory.E.H2CurveOrder.LeafKumMuUnitsPf.LeafKumMuInj :=
  LateralTheory.E.H2CurveOrder.LeafKumMuInjPf.LeafKumMuInj_of hL hG cycPow emptySec

end LateralTheory.E.H2CurveOrder.LeafKumMuInjPfGlue
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct GlobalTheory.EtC

namespace LateralTheory.E.H2CurveOrder.TwLocGenPfSec

theorem ofRings_sec_res {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {V U : Scheme.{0}}
    (g : V ⟶ U) (x : M.obj Γ(U, ⊤)) :
    Sec.res g (ofRings.sec M U x) = ofRings.sec M V ((M.map g.appTop).hom x) := by
  have h := congrArg (fun f => f.hom x)
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality g.op)
  simp only [ModuleCat.hom_comp] at h
  exact h.symm

def TwSecLoc : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U),
  Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom)

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_true (U : Scheme.{0}) : Loc U fun _ _ => True :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun _ _ _ => trivial⟩

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hS'⟩ := hP
  obtain ⟨T, hT, hT'⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨hS' V g hg.1, hT' V g hg.2⟩⟩

theorem loc_bind {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} {Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (hP : Loc U P) (hQ : ∀ V (g : V ⟶ U), P V g → Loc V fun W h => Q W (h ≫ g)) : Loc U Q := by
  obtain ⟨S, hS, hS'⟩ := hP
  choose T hT hT' using fun V (g : V ⟶ U) (hg : S.arrows g) => hQ V g (hS' V g hg)
  refine ⟨Sieve.bind S.arrows T, Scheme.etaleTopology.bind_covering hS hT, ?_⟩
  rintro W _ ⟨V, h, g, hg, hh, rfl⟩
  exact hT' V g hg W h hh

theorem loc_surj {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0})
    (y : Sec (ofRings R M) U) :
    Loc U fun V g => ∃ x : M.obj Γ(V, ⊤), Sec.res g y = ofRings.sec M V x := by
  have h := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) y
  refine ⟨_, h, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := hg
  exact ⟨x, hx.symm⟩

end LateralTheory.E.H2CurveOrder.TwLocGenPfSec

namespace LateralTheory.E.H2CurveOrder.TwLocGenPfSec

def ZarPow : Prop := ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ ξ : Prim q Γ(V, ⊤)),
  Loc V fun W h => ∃ a : (ZMod q)ˣ, (ξ.map h.appTop.hom).1 = (ζ.map h.appTop.hom).1 ^ (a : ZMod q).val

theorem ulift_smul_eq_nsmul {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (r : ULift.{1} (ZMod q)) (m : M) : r • m = r.down.val • m := by
  have : r = ((r.down.val : ℕ) : ULift.{1} (ZMod q)) := by
    cases r with
    | up a =>
      change ULift.up a = ULift.up ((a.val : ℕ) : ZMod q)
      rw [ZMod.natCast_zmod_val]
  conv_lhs => rw [this]
  exact Nat.cast_smul_eq_nsmul _ _ _

theorem twF_map_mk (q : ℕ) (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (x : Prim q A →₀ ULift.{1} (ZMod q)) :
    ((twF q i).map f).hom (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) x) : (twF q i).obj B) := rfl

theorem twF_single_pow (q : ℕ) [NeZero q] (i : ℤ) (A : CommRingCat.{0}) (ζ ξ : Prim q A) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) (b : ULift.{1} (ZMod q)) :
    (Submodule.Quotient.mk (Finsupp.single ξ b) : (twF q i).obj A) =
      (b.down * ((a ^ i : (ZMod q)ˣ) : ZMod q)).val • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj A) := by
  have hrel : (Submodule.Quotient.mk (Finsupp.single ξ 1) : (twF q i).obj A) =
      Submodule.Quotient.mk (Finsupp.single ζ (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q))) :=
    (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩)
  have e1 : Finsupp.single ξ b = b • Finsupp.single ξ (1 : ULift.{1} (ZMod q)) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  have e2 : Finsupp.single ζ (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q)) =
      (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q)) • Finsupp.single ζ (1 : ULift.{1} (ZMod q)) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [e1, Submodule.Quotient.mk_smul, hrel, e2, Submodule.Quotient.mk_smul, smul_smul]
  exact ulift_smul_eq_nsmul _ _

theorem twF_loc (hZ : ZarPow) (q : ℕ) [NeZero q] (i : ℤ) (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤))
    (x : (twF q i).obj Γ(V, ⊤)) :
    Loc V fun W h => ∃ c : ℕ, ((twF q i).map h.appTop).hom x =
      c • (Submodule.Quotient.mk (Finsupp.single (ζ.map h.appTop.hom) 1) : (twF q i).obj Γ(W, ⊤)) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  induction f using Finsupp.induction with
  | zero =>
    refine loc_mono (loc_true V) fun W h _ => ⟨0, ?_⟩
    rw [zero_smul, Submodule.Quotient.mk_zero]
    exact map_zero ((twF q i).map h.appTop).hom
  | single_add ξ b g _ _ ih =>
    refine loc_mono (loc_and (hZ q V ζ ξ) ih) fun W h ⟨⟨a, ha⟩, ⟨c, hc⟩⟩ =>
      ⟨(b.down * ((a ^ i : (ZMod q)ˣ) : ZMod q)).val + c, ?_⟩
    rw [Submodule.Quotient.mk_add]
    refine (map_add ((twF q i).map h.appTop).hom _ _).trans ?_
    rw [hc, twF_map_mk, Finsupp.mapDomain_single,
      twF_single_pow q i _ _ _ a ha b, add_smul]
    rfl

theorem TwSecLoc_of (hZ : ZarPow) : LateralTheory.E.H2CurveOrder.TwLocGenPfSec.TwSecLoc := by
  intro q _ i U ζ y
  refine loc_bind (loc_surj (twF q i) U y) fun V g ⟨x, hx⟩ => ?_
  refine loc_mono (twF_loc hZ q i V (ζ.map g.appTop.hom) x) fun W h ⟨c, hc⟩ => ⟨c, ?_⟩
  have e : Sec.res (h ≫ g) y = Sec.res h (Sec.res g y) := by
    simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hp : (ζ.map g.appTop.hom).map h.appTop.hom = ζ.map (h ≫ g).appTop.hom := by
    apply Subtype.ext
    simp [Prim.map]
    rfl
  rw [e]
  refine (congrArg (fun z => ((tw q i).obj.map h.op).hom z) hx).trans ?_
  refine (LateralTheory.E.H2CurveOrder.TwLocGenPfSec.ofRings_sec_res (twF q i) h x).trans ?_
  rw [hc, ← hp]
  unfold twGen ofRings.sec
  exact map_nsmul _ _ _

end LateralTheory.E.H2CurveOrder.TwLocGenPfSec
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct GlobalTheory.EtC

namespace LateralTheory.E.H2CurveOrder.TwLocGenPfSec

def AlgPow : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ζ ξ : Prim q A),
  ∃ s : Set A, Ideal.span s = ⊤ ∧ ∀ f ∈ s, ∃ (a : (ZMod q)ˣ) (n : ℕ), f ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val) = 0

theorem ZarPow_of (hA : AlgPow) : ZarPow := by
  intro q _ V ζ ξ
  obtain ⟨s, hs, hf⟩ := hA q Γ(V, ⊤) ζ ξ
  let U : s → V.Opens := fun f => V.basicOpen f.1
  have hU : TopologicalSpace.IsOpenCover U := by
    unfold TopologicalSpace.IsOpenCover
    have h := iSup_basicOpen_of_span_eq_top ⊤ s hs
    show ⨆ f : s, V.basicOpen f.1 = ⊤
    rw [iSup_subtype]
    exact h
  let 𝒰 := V.openCoverOfIsOpenCover U hU
  refine ⟨Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f),
    Scheme.zariskiTopology_le_etaleTopology _ (Scheme.mem_grothendieckTopology_iff.2 ⟨𝒰, Sieve.le_generate _⟩), ?_⟩
  rintro W g ⟨Y, h, _, ⟨i⟩, rfl⟩
  obtain ⟨a, n, hn⟩ := hf i.1 i.2
  refine ⟨a, ?_⟩
  have hle : (U i).ι ''ᵁ ⊤ ≤ V.basicOpen i.1 := by simp [U]
  have hu : IsUnit ((U i).ι.appTop.hom i.1) := by
    have := (V.toRingedSpace.isUnit_res_basicOpen i.1).map (V.presheaf.map (homOfLE hle).op).hom
    have e : V.presheaf.map (homOfLE (x := (U i).ι ''ᵁ ⊤) (y := ⊤) le_top).op =
        V.presheaf.map (homOfLE (V.basicOpen_le i.1)).op ≫ V.presheaf.map (homOfLE hle).op := by
      rw [← Functor.map_comp]; rfl
    rw [Scheme.Opens.ι_appTop, e]
    exact this
  have key : (U i).ι.appTop.hom ξ.1 = ((U i).ι.appTop.hom ζ.1) ^ (a : ZMod q).val := by
    have h0 : (U i).ι.appTop.hom (i.1 ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val)) = 0 := by rw [hn, map_zero]
    rw [map_mul, map_pow, map_sub, map_pow] at h0
    exact sub_eq_zero.1 ((hu.pow n).mul_right_eq_zero.1 h0)
  have hc : ∀ x, (h ≫ (U i).ι).appTop.hom x = h.appTop.hom ((U i).ι.appTop.hom x) := fun x => by
    rfl
  show (h ≫ (U i).ι).appTop.hom ξ.1 = ((h ≫ (U i).ι).appTop.hom ζ.1) ^ _
  rw [hc, hc, key]
  exact map_pow _ _ _

theorem TwSecLoc_of_alg (hA : AlgPow) : LateralTheory.E.H2CurveOrder.TwLocGenPfSec.TwSecLoc := TwSecLoc_of (ZarPow_of hA)

end LateralTheory.E.H2CurveOrder.TwLocGenPfSec
end

noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.E.H2CurveOrder.TwLocGenPfSec

theorem root_dom {K : Type} [CommRing K] [IsDomain K] (q : ℕ) [NeZero q] (hq : (q : K) ≠ 0) (z : K)
    (hz : aeval z (cyclotomic q ℤ) = 0) : IsPrimitiveRoot z q := by
  have : NeZero (q : K) := ⟨hq⟩
  have h : (cyclotomic q K).IsRoot z := by
    rw [IsRoot, ← map_cyclotomic_int, eval_map]
    simpa [aeval_def] using hz
  exact (isRoot_cyclotomic_iff).1 h

theorem eq_pow_dom {K : Type} [CommRing K] [IsDomain K] (q : ℕ) [NeZero q] (z x : K)
    (hz : IsPrimitiveRoot z q) (hx : IsPrimitiveRoot x q) : ∃ b : (ZMod q)ˣ, x = z ^ (b : ZMod q).val := by
  obtain ⟨i, hi, hzi⟩ := hz.eq_pow_of_pow_eq_one hx.pow_eq_one
  have hc : i.Coprime q := (hz.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (hzi ▸ hx)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, hzi]

theorem pow_ne_dom {K : Type} [CommRing K] (q : ℕ) [NeZero q] (z : K)
    (hz : IsPrimitiveRoot z q) (a b : (ZMod q)ˣ) (h : a ≠ b) :
    z ^ (a : ZMod q).val ≠ z ^ (b : ZMod q).val := by
  intro e
  apply h
  exact Units.ext (ZMod.val_injective q (hz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e))

theorem pow_q {A : Type} [CommRing A] (q : ℕ) (z : A) (hz : aeval z (cyclotomic q ℤ) = 0) : z ^ q = 1 := by
  obtain ⟨p, hp⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have := congrArg (aeval z) hp
  simp [hz] at this
  exact sub_eq_zero.1 this

theorem self_sq {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) (x y : A)
    (hx : x ^ q = 1) (hy : y ^ q = 1) : ∃ w : A, x - y = (x - y) ^ 2 * w := by
  set d := x - y
  set u := ∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i)
  have hdu : u * d = 0 := by
    have := geom_sum₂_mul x y q
    rw [hx, hy, sub_self] at this
    exact this
  have hyu : IsUnit y := isUnit_iff_exists_inv.2 ⟨y ^ (q - 1), by rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne q)), hy]⟩
  set c : A := (q : A) * y ^ (q - 1)
  have hc : IsUnit c := hq.mul (hyu.pow _)
  have hmem : u - c ∈ Ideal.span {d} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hxy : Ideal.Quotient.mk (Ideal.span {d}) x = Ideal.Quotient.mk (Ideal.span {d}) y := by
      rw [Ideal.Quotient.eq]; exact Ideal.subset_span rfl
    simp only [u, c, map_sub, map_sum, map_mul, map_pow, map_natCast, hxy]
    rw [geom_sum₂_self, sub_self]
  obtain ⟨w0, hw0⟩ := Ideal.mem_span_singleton'.1 hmem
  obtain ⟨cu, hcu⟩ := hc
  refine ⟨-(w0 * ↑cu⁻¹), ?_⟩
  have hdc : d * c = -(d ^ 2 * w0) := by
    have : c = u - w0 * d := by rw [hw0]; ring
    rw [this]; linear_combination hdu
  calc d = d * c * ↑cu⁻¹ := by rw [← hcu, mul_assoc, Units.mul_inv, mul_one]
    _ = _ := by rw [hdc]; ring

theorem self_pow {A : Type} [CommRing A] (d w : A) (h : d = d ^ 2 * w) (k : ℕ) : d = d ^ (k + 1) * w ^ k := by
  induction k with
  | zero => simp
  | succ k ih => calc d = d ^ (k + 1) * w ^ k := ih
      _ = d ^ k * d * w ^ k := by ring
      _ = d ^ k * (d ^ 2 * w) * w ^ k := by rw [← h]
      _ = _ := by ring

theorem AlgPow_of : LateralTheory.E.H2CurveOrder.TwLocGenPfSec.AlgPow := by
  classical
  intro q _ A _ ζ ξ
  obtain ⟨hqA, hζ⟩ := ζ.2
  obtain ⟨-, hξ⟩ := ξ.2
  let f : (ZMod q)ˣ → A := fun a => ∏ b ∈ Finset.univ.erase a, (ξ.1 - ζ.1 ^ (b : ZMod q).val)

  have hdom : ∀ p : Ideal A, p.IsPrime → IsPrimitiveRoot (Ideal.Quotient.mk p ζ.1) q ∧
      IsPrimitiveRoot (Ideal.Quotient.mk p ξ.1) q := by
    intro p hp
    have hq : ((q : ℕ) : A ⧸ p) ≠ 0 := by
      have := hqA.map (Ideal.Quotient.mk p)
      rw [map_natCast] at this
      exact this.ne_zero
    have hm : ∀ z : A, aeval z (cyclotomic q ℤ) = 0 → aeval (Ideal.Quotient.mk p z) (cyclotomic q ℤ) = 0 := by
      intro z hz
      have := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ ℤ p) z (cyclotomic q ℤ)
      rw [hz, map_zero] at this
      simpa using this
    exact ⟨root_dom q hq _ (hm _ hζ), root_dom q hq _ (hm _ hξ)⟩
  refine ⟨Set.range f, ?_, ?_⟩
  · by_contra hne
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨h1, h2⟩ := hdom m hm.isPrime
    obtain ⟨b0, hb0⟩ := eq_pow_dom q _ _ h1 h2
    have hin : f b0 ∈ m := hsm (Ideal.subset_span ⟨b0, rfl⟩)
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hin
    simp only [f, map_prod, map_sub, map_pow, hb0] at hin
    rw [Finset.prod_eq_zero_iff] at hin
    obtain ⟨b, hb, e⟩ := hin
    exact pow_ne_dom q _ h1 b0 b (Finset.ne_of_mem_erase hb).symm (sub_eq_zero.1 e)
  · rintro _ ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    have hnil : IsNilpotent (f a * (ξ.1 - ζ.1 ^ (a : ZMod q).val)) := by
      rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
      intro p hp
      have hp : p.IsPrime := hp
      obtain ⟨h1, h2⟩ := hdom p hp
      obtain ⟨b0, hb0⟩ := eq_pow_dom q _ _ h1 h2
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp only [f, map_mul, map_prod, map_sub, map_pow, hb0]
      by_cases hab : b0 = a
      · subst hab; simp
      · apply mul_eq_zero_of_left
        exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hab, Finset.mem_univ _⟩) (sub_self _)
    obtain ⟨n, hn⟩ := hnil
    obtain ⟨w, hw⟩ := self_sq q hqA ξ.1 (ζ.1 ^ (a : ZMod q).val) (pow_q q _ hξ)
      (by rw [← pow_mul, mul_comm, pow_mul, pow_q q _ hζ, one_pow])
    refine ⟨n, ?_⟩
    rw [self_pow _ w hw n, pow_succ, mul_pow] at *
    calc f a ^ n * ((ξ.1 - ζ.1 ^ (a : ZMod q).val) ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val) * w ^ n)
        = (f a ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val) ^ n) * ((ξ.1 - ζ.1 ^ (a : ZMod q).val) * w ^ n) := by ring
      _ = 0 := by rw [hn, zero_mul]

end LateralTheory.E.H2CurveOrder.TwLocGenPfSec
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.H2CurveOrder.TwLocGenPf
open LateralTheory.E.H2CurveOrder.TwLocGenPfSec

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res (h ≫ g) y = Sec.res h (Sec.res g y) := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem TwLocGen_of : LateralTheory.E.H2CurveOrder.LeafKumMuInjPf.TwLocGen := by
  intro q _ U y
  have hT := TwSecLoc_of_alg AlgPow_of
  refine loc_bind (loc_surj (twF q 1) U y) ?_
  rintro V g ⟨x, hx⟩
  by_cases hP : Nonempty (Prim q Γ(V, ⊤))
  · obtain ⟨ζ⟩ := hP
    refine loc_mono (hT q 1 V ζ (Sec.res g y)) ?_
    rintro W h ⟨c, hc⟩
    right
    exact ⟨ζ.map h.appTop.hom, c, by rw [res_comp]; exact hc⟩
  · have hx0 : x = 0 := by
      haveI : IsEmpty (Prim q Γ(V, ⊤)) := not_nonempty_iff.mp hP
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have : z = 0 := Subsingleton.elim _ _
      rw [this]; rfl
    refine loc_mono (loc_true V) ?_
    intro W h _
    left
    have hx' : Sec.res (F := tw q 1) g y = ofRings.sec (twF q 1) V x := hx
    rw [res_comp, hx', hx0]
    have h0 : ofRings.sec (twF q 1) V 0 = 0 :=
      map_zero ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 1)).app (op V)).hom
    rw [h0]
    exact map_zero _

end LateralTheory.E.H2CurveOrder.TwLocGenPf
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.H2CurveOrder.GmSepPf

def ev (V : Scheme.{0}) (a : Γ(V, ⊤)) : CommRingCat.of (Polynomial ℤ) ⟶ Γ(V, ⊤) :=
  CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom _) a)

def lineMap (V : Scheme.{0}) (a : Γ(V, ⊤)) : V ⟶ Spec (CommRingCat.of (Polynomial ℤ)) :=
  ΓSpec.adjunction.homEquiv V (op (CommRingCat.of (Polynomial ℤ))) (ev V a).op

theorem lineMap_inj (V : Scheme.{0}) (a b : Γ(V, ⊤)) (h : lineMap V a = lineMap V b) : a = b := by
  have h1 := (ΓSpec.adjunction.homEquiv _ _).injective h
  have h2 := congrArg (fun f => f.hom Polynomial.X) (Quiver.Hom.op_inj h1)
  simpa [ev] using h2

theorem ev_comp {W V : Scheme.{0}} (g : W ⟶ V) (a : Γ(V, ⊤)) : ev V a ≫ g.appTop = ev W (g.appTop a) := by
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro n; simp [ev]
  · simp [ev]

theorem lineMap_nat {W V : Scheme.{0}} (g : W ⟶ V) (a : Γ(V, ⊤)) :
    g ≫ lineMap V a = lineMap W (g.appTop a) := by
  unfold lineMap
  refine (ΓSpec.adjunction.homEquiv_naturality_left g (ev V a).op).symm.trans ?_
  congr 1
  apply Quiver.Hom.unop_inj
  exact ev_comp g a

theorem gamma_sep (V : Scheme.{0}) (S : Sieve V) (hS : S ∈ Scheme.etaleTopology V) (a b : Γ(V, ⊤))
    (h : ∀ (W : Scheme.{0}) (g : W ⟶ V), S.arrows g → g.appTop a = g.appTop b) : a = b := by
  have : Scheme.etaleTopology.{0}.Subcanonical :=
    GrothendieckTopology.Subcanonical.of_le Scheme.etaleTopology_le_proetaleTopology
  have hsh := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := Scheme.etaleTopology.{0})
    (yoneda.obj (Spec (CommRingCat.of (Polynomial ℤ))))
  apply lineMap_inj
  refine (hsh S hS).isSeparatedFor.ext (fun W g hg => ?_)
  change g ≫ lineMap V a = g ≫ lineMap V b
  rw [lineMap_nat, lineMap_nat, h W g hg]

theorem gmSep : LateralTheory.E.H2CurveOrder.LeafKumMuInjPf.GmSep := by
  intro V u h
  have h0 : ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op V)).hom (ULift.up (Additive.ofMul u))
      = ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op V)).hom 0 := by
    rw [map_zero]; exact h
  have hm := Presheaf.equalizerSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)) (X := op V)
    (ULift.up (Additive.ofMul u) : (Scheme.Γ ⋙ unitsF).obj (op V)) 0 h0
  apply Units.ext
  refine gamma_sep V _ hm u.1 (1 : Γ(V, ⊤)) (fun W g hg => ?_)
  have h1 := congrArg (fun z : (Scheme.Γ ⋙ unitsF).obj (op W) => ((Additive.toMul z.down : (Γ(W, ⊤))ˣ) : Γ(W, ⊤))) hg
  exact h1

theorem GmSep_of : LateralTheory.E.H2CurveOrder.LeafKumMuInjPf.GmSep := gmSep

end LateralTheory.E.H2CurveOrder.GmSepPf
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.H2CurveOrder.LeafKumMuSurjPf

namespace LateralTheory.E.H2CurveOrder.LeafKumMuSurjPowPf

def powCof {A : Type*} [CommRing A] (u v : A) (q : ℕ) : A := ∑ i ∈ Finset.range q, u ^ i * v ^ (q - 1 - i)

theorem powCof_mul {A : Type*} [CommRing A] (u v : A) (q : ℕ) : powCof u v q * (u - v) = u ^ q - v ^ q :=
  geom_sum₂_mul u v q

theorem powCof_map {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (u v : A) (q : ℕ) :
    φ (powCof u v q) = powCof (φ u) (φ v) q := by
  simp [powCof, map_sum, map_mul, map_pow]

theorem powCof_self {A : Type*} [CommRing A] (v : A) (q : ℕ) : powCof v v q = (q : A) * v ^ (q - 1) := by
  unfold powCof
  rw [Finset.sum_congr rfl (g := fun _ => v ^ (q - 1))]
  · simp
  · intro i hi
    rw [← pow_add]; congr 1; have := Finset.mem_range.1 hi; omega

theorem field_step {K : Type} [Field K] (q : ℕ) [NeZero q] (hq : (q : K) ≠ 0) (z w : K)
    (hz : Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0) (hw : w ^ q = 1) :
    ∃ a : Fin q, powCof w (z ^ (a : ℕ)) q ≠ 0 := by
  have : NeZero (q : K) := ⟨hq⟩
  have hroot : Polynomial.IsRoot (Polynomial.cyclotomic q K) z := by
    rw [← Polynomial.map_cyclotomic_int, Polynomial.IsRoot, Polynomial.eval_map]
    rw [Polynomial.aeval_def, algebraMap_int_eq] at hz
    exact hz
  have hp : IsPrimitiveRoot z q := (Polynomial.isRoot_cyclotomic_iff).1 hroot
  obtain ⟨i, hi, hzi⟩ := hp.eq_pow_of_pow_eq_one hw
  refine ⟨⟨i, hi⟩, ?_⟩
  rw [← hzi, powCof_self]
  have hz0 : z ≠ 0 := fun h => by
    have := hp.pow_eq_one; rw [h, zero_pow (NeZero.ne q)] at this; exact zero_ne_one this
  exact mul_ne_zero hq (pow_ne_zero _ (pow_ne_zero _ hz0))

theorem isUnit_of_basicOpen_top {V : Scheme.{0}} (t : Γ(V, ⊤)) (h : V.basicOpen t = ⊤) : IsUnit t := by
  apply V.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  have hx' : x ∈ V.basicOpen t := by rw [h]; trivial
  exact (V.mem_basicOpen_top t x).1 hx'

theorem pow_pf : LeafKumMuSurjPow := by
  intro q _ U ζ u hu
  let s : Fin q → Γ(U, ⊤) := fun a => powCof (u : Γ(U, ⊤)) (ζ.1 ^ (a : ℕ)) q
  have hcov : TopologicalSpace.IsOpenCover (fun a => U.basicOpen (s a)) := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    rintro x -
    rw [TopologicalSpace.Opens.mem_iSup]
    let φ := (U.Γevaluation x).hom
    have hq : (q : U.residueField x) ≠ 0 := by
      have := ζ.2.1.map φ
      simpa using this.ne_zero
    have hz : Polynomial.aeval (φ ζ.1) (Polynomial.cyclotomic q ℤ) = 0 := by
      have := Polynomial.aeval_algHom_apply φ.toIntAlgHom ζ.1 (Polynomial.cyclotomic q ℤ)
      rw [ζ.2.2, map_zero] at this
      exact this
    have hw : (φ (u : Γ(U, ⊤))) ^ q = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hu, Units.val_one, map_one]
    obtain ⟨a, ha⟩ := field_step q hq _ _ hz hw
    refine ⟨a, ?_⟩
    rw [← Scheme.evaluation_ne_zero_iff_mem_basicOpen (X := U) (U := ⊤) x trivial]
    show φ (s a) ≠ 0
    simp only [s]
    rw [powCof_map, map_pow]
    exact ha
  let 𝒰 := U.openCoverOfIsOpenCover _ hcov
  refine ⟨Sieve.ofArrows 𝒰.X 𝒰.f,
    Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology 𝒰), ?_⟩
  intro V f hf
  obtain ⟨a', g, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hf
  let a : Fin q := a'
  refine ⟨(a : ℕ), ?_⟩
  have hunit : IsUnit ((g ≫ 𝒰.f a).appTop (s a)) := by
    apply isUnit_of_basicOpen_top
    rw [← Scheme.preimage_basicOpen_top, eq_top_iff]
    intro x _
    show (U.basicOpen (s a)).ι.base (g.base x) ∈ U.basicOpen (s a)
    exact (g.base x).2
  have hzero : s a * ((u : Γ(U, ⊤)) - ζ.1 ^ (a : ℕ)) = 0 := by
    simp only [s]
    rw [powCof_mul, ← Units.val_pow_eq_pow_val, hu, Units.val_one, ← pow_mul, mul_comm, pow_mul,
      prim_pow_q ζ, one_pow, sub_self]
  have key : ∀ ψ : Γ(U, ⊤) →+* Γ(V, ⊤), IsUnit (ψ (s a)) → ψ u = ψ ζ.1 ^ (a : ℕ) := fun ψ h => by
    have h2 := congrArg ψ hzero
    rw [map_mul, map_zero] at h2
    rw [← map_pow]
    exact sub_eq_zero.1 ((h.mul_right_eq_zero).1 (by rw [← map_sub]; exact h2))
  apply key
  exact hunit

theorem LeafKumMuSurjPow_of : LeafKumMuSurjPow := pow_pf

end LateralTheory.E.H2CurveOrder.LeafKumMuSurjPowPf
end
end

section
open Polynomial CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
noncomputable section
namespace LateralTheory.E.H2CurveOrder.LeafKumMuSurjPrimPf

theorem cyc_cond (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    ∃ p₁ p₂ : B[X], ∃ n : ℕ, derivative (cyclotomic q B) * p₁ + cyclotomic q B * p₂ = (1 : B[X]) ^ n := by
  obtain ⟨G, hG⟩ := cyclotomic.dvd_X_pow_sub_one q B
  obtain ⟨c, hc⟩ : ∃ c : B, c * q = 1 := ⟨↑hq.unit⁻¹, by simp⟩
  refine ⟨C c * X * G, C c * X * derivative G - G, 1, ?_⟩
  have hd := congrArg derivative hG
  rw [derivative_mul, derivative_sub, derivative_X_pow, derivative_one, sub_zero] at hd
  have key : (1 : B[X]) = C c * X * (C (q : B) * X ^ (q - 1)) - (X ^ q - 1) := by
    rcases Nat.eq_zero_or_pos q with h0 | hpos
    · subst h0; simp at hc; have : Subsingleton B := subsingleton_of_zero_eq_one hc; exact Subsingleton.elim _ _
    · have : X * X ^ (q - 1) = (X : B[X]) ^ q := by rw [← pow_succ', Nat.sub_add_cancel hpos]
      calc (1 : B[X]) = C (c * q) * (X * X ^ (q - 1)) - (X ^ q - 1) := by rw [hc, this]; simp
        _ = _ := by rw [C_mul]; ring
  rw [pow_one, key, hd, hG]
  ring

def cycPair (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) : StandardEtalePair B where
  f := cyclotomic q B
  monic_f := cyclotomic.monic q B
  g := 1
  cond := cyc_cond q B hq

theorem cycPair_X (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    aeval (cycPair q B hq).X (cyclotomic q ℤ) = 0 := by
  have h : aeval (cycPair q B hq).X (cyclotomic q B) = 0 := (cycPair q B hq).hasMap_X.1
  rw [← map_cyclotomic_int, ← algebraMap_int_eq, aeval_map_algebraMap] at h
  exact h

theorem cycX_root (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    aeval (cycPair q B hq).X (cyclotomic q B) = 0 := (cycPair q B hq).hasMap_X.1

theorem root_hasMap (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    (cycPair q B hq).HasMap (AdjoinRoot.root (cyclotomic q B)) := by
  refine ⟨?_, ?_⟩
  · show aeval _ (cyclotomic q B) = 0
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  · show IsUnit (aeval _ (1 : B[X]))
    simp

def cycTo (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    (cycPair q B hq).Ring →ₐ[B] AdjoinRoot (cyclotomic q B) :=
  (cycPair q B hq).lift _ (root_hasMap q B hq)

def cycFrom (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    AdjoinRoot (cyclotomic q B) →ₐ[B] (cycPair q B hq).Ring :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId B _) (cycPair q B hq).X
    (by exact (aeval_def _ _).symm.trans (cycX_root q B hq))

theorem cycFrom_root (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    cycFrom q B hq (AdjoinRoot.root _) = (cycPair q B hq).X := AdjoinRoot.liftAlgHom_root _ _ _ _

theorem cycTo_X (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    cycTo q B hq (cycPair q B hq).X = AdjoinRoot.root _ := StandardEtalePair.lift_X _ _ _

def cycEquiv (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    (cycPair q B hq).Ring ≃ₐ[B] AdjoinRoot (cyclotomic q B) :=
  AlgEquiv.ofAlgHom (cycTo q B hq) (cycFrom q B hq)
    (AdjoinRoot.algHom_ext (by
      show cycTo q B hq (cycFrom q B hq (AdjoinRoot.root _)) = AdjoinRoot.root _
      rw [cycFrom_root, cycTo_X]))
    ((cycPair q B hq).hom_ext (by
      show cycFrom q B hq (cycTo q B hq (cycPair q B hq).X) = (cycPair q B hq).X
      rw [cycTo_X, cycFrom_root]))

theorem cyc_comap_surj (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap B (cycPair q B hq).Ring)) := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · have : IsEmpty (PrimeSpectrum B) := PrimeSpectrum.isEmpty_iff_subsingleton.2 hB
    intro x; exact isEmptyElim x
  · have hfree : Module.Free B (AdjoinRoot (cyclotomic q B)) :=
      Module.Free.of_basis (AdjoinRoot.powerBasis' (cyclotomic.monic q B)).basis
    have : Module.Free B (cycPair q B hq).Ring := Module.Free.of_equiv (cycEquiv q B hq).symm.toLinearEquiv
    have hq0 : q ≠ 0 := by rintro rfl; simp at hq
    have hd : 0 < (cyclotomic q B).natDegree := by
      rw [natDegree_cyclotomic]; exact Nat.totient_pos.2 (Nat.pos_of_ne_zero hq0)
    have : Nontrivial (AdjoinRoot (cyclotomic q B)) :=
      nontrivial_of_ne _ 0 ((AdjoinRoot.powerBasis' (cyclotomic.monic q B)).basis.ne_zero ⟨0, hd⟩)
    have : Nontrivial (cycPair q B hq).Ring := (cycEquiv q B hq).toEquiv.nontrivial
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat

theorem prim_of_hom (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) {A : Type} [CommRing A]
    (ψ : (cycPair q B hq).Ring →+* A) : Nonempty (Prim q A) := by
  refine ⟨⟨ψ (cycPair q B hq).X, ?_, ?_⟩⟩
  · have h := (hq.map (algebraMap B (cycPair q B hq).Ring)).map ψ
    simpa using h
  · rw [show ψ (cycPair q B hq).X = ψ.toIntAlgHom (cycPair q B hq).X from rfl, Polynomial.aeval_algHom_apply, cycPair_X, map_zero]

theorem LeafKumMuSurjPrim_pf : LateralTheory.E.H2CurveOrder.LeafKumMuSurjPf.LeafKumMuSurjPrim := by
  intro q _ B _ hq U hU
  let φ : CommRingCat.of B ⟶ CommRingCat.of (cycPair q B hq).Ring :=
    CommRingCat.ofHom (algebraMap B (cycPair q B hq).Ring)
  let x : U ⟶ Spec (CommRingCat.of B) := hU.some
  have hE : Etale (Spec.map φ) :=
    HasRingHomProperty.Spec_iff.2 ((RingHom.etale_algebraMap (R := B) (S := (cycPair q B hq).Ring)).2 inferInstance)
  have hS : Surjective (Spec.map φ) := ⟨cyc_comap_surj q B hq⟩
  have hE' : Etale (pullback.fst x (Spec.map φ)) := inferInstance
  have hS' : Surjective (pullback.fst x (Spec.map φ)) := inferInstance
  refine ⟨Sieve.generate (Presieve.singleton (pullback.fst x (Spec.map φ))),
    Precoverage.generate_mem_toGrothendieck ((Scheme.singleton_mem_precoverage_iff (P := @Etale) _).2 ⟨hS'.surj, hE'⟩), ?_⟩
  rintro V f ⟨W, g, _, ⟨⟩, rfl⟩
  exact prim_of_hom q B hq ((Scheme.Γ.map (g ≫ pullback.snd x (Spec.map φ)).op).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (cycPair q B hq).Ring)).inv.hom)

theorem LeafKumMuSurjPrim_of : LateralTheory.E.H2CurveOrder.LeafKumMuSurjPf.LeafKumMuSurjPrim := LeafKumMuSurjPrim_pf

end LateralTheory.E.H2CurveOrder.LeafKumMuSurjPrimPf
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.H2CurveOrder.LeafKumSeqPf LateralTheory.E.H2CurveOrder.KummerH0Surjection

namespace LateralTheory.E.H2CurveOrder.LeafKumSecSurjPf

theorem surj_of_mem {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) [Mono φ] {U : Scheme.{0}}
    (s : Sec G U) (hs : Presheaf.imageSieve φ.hom s ∈ Scheme.etaleTopology U) :
    ∃ t : Sec F U, Sec.map φ t = s := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology F.obj (forget _)).1 F.cond)
  have hG := (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology G.obj (forget _)).1 G.cond)
  let x : Presieve.FamilyOfElements (F.obj ⋙ forget _) (Presheaf.imageSieve φ.hom s).arrows :=
    fun V f hf => Presheaf.localPreimage φ.hom s f hf
  have hx : x.Compatible := by
    intro Y1 Y2 Z g1 g2 f1 f2 h1 h2 w
    apply sec_injective φ Z
    have e1 := NatTrans.naturality_apply φ.hom g1.op (x f1 h1)
    have e2 := NatTrans.naturality_apply φ.hom g2.op (x f2 h2)
    dsimp only [Functor.comp_map] at *
    show φ.hom.app _ (F.obj.map g1.op (x f1 h1)) = φ.hom.app _ (F.obj.map g2.op (x f2 h2))
    rw [e1, e2]
    simp only [x, Presheaf.app_localPreimage]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp,
      ← op_comp, ← op_comp, w]
  obtain ⟨t, ht, -⟩ := hF _ hs x hx
  refine ⟨t, ?_⟩
  apply (hG _ hs).isSeparatedFor.ext
  intro V f hf
  dsimp only [Functor.comp_map]
  have e := NatTrans.naturality_apply φ.hom f.op t
  show G.obj.map f.op (φ.hom.app _ t) = G.obj.map f.op s
  rw [← e]
  have := ht f hf
  refine (congrArg (φ.hom.app (op V)) this).trans ?_
  exact Presheaf.app_localPreimage φ.hom s f hf

def LeafUnitRoot : Prop := ∀ (q : ℕ) [NeZero q] (V : Scheme.{0}), IsUnit (q : Γ(V, ⊤)) →
  ∀ b : (Γ(V, ⊤))ˣ, Presheaf.imageSieve (powGm q).hom (unitsToSec V (Additive.ofMul b)) ∈ Scheme.etaleTopology V

theorem kum_le (q : ℕ) {U : Scheme.{0}} (s : Sec Gm U) :
    Presheaf.imageSieve (powGm q).hom s ≤ Presheaf.imageSieve (kumM q).hom s := by
  rintro V f ⟨t, ht⟩
  refine ⟨(kumSC q).g.hom.app _ t, ?_⟩
  rw [← ht, ← kumSC_g_kumM q]
  rfl

theorem LeafKumSecSurj_of (hR : LeafUnitRoot) : LateralTheory.E.H2CurveOrder.KummerH0Surjection.LeafKumSecSurj := by
  intro q _ U hq s
  apply surj_of_mem
  apply Scheme.etaleTopology.superset_covering (kum_le q s)
  have hS : Presheaf.imageSieve (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)) s ∈
      Scheme.etaleTopology U := @Presheaf.imageSieve_mem _ _ Scheme.etaleTopology _ _ _ _ _ _ _ _ (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)) (Presheaf.isLocallySurjective_toSheafify' (J := Scheme.etaleTopology) _) (op U) s
  refine Scheme.etaleTopology.transitive hS _ ?_
  rintro V f ⟨b, hb⟩
  rw [Presheaf.pullback_imageSieve]
  have hqV : IsUnit (q : Γ(V, ⊤)) := by simpa using hq.map f.appTop.hom
  have key := hR q V hqV (Additive.toMul b.down)
  have e : unitsToSec V (Additive.ofMul (Additive.toMul b.down)) = Gm.obj.map f.op s := hb
  rw [e] at key
  exact key

end LateralTheory.E.H2CurveOrder.LeafKumSecSurjPf
end
end

section
open Polynomial
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.H2CurveOrder.LeafKumSeqPf LateralTheory.E.H2CurveOrder.KummerH0Surjection
namespace LateralTheory.E.H2CurveOrder.LeafUnitRootPf
variable {R : Type} [CommRing R]

noncomputable def kf (q : ℕ) (b : Rˣ) : R[X] := X ^ q - C (b : R)

theorem kf_monic (q : ℕ) [NeZero q] (b : Rˣ) : (kf q b).Monic :=
  monic_X_pow_sub_C _ (NeZero.ne q)

noncomputable def kpair (q : ℕ) [NeZero q] (hq : IsUnit (q : R)) (b : Rˣ) : StandardEtalePair R where
  f := kf q b
  monic_f := kf_monic q b
  g := 1
  cond := by
    refine ⟨C (↑hq.unit⁻¹ : R) * C (↑b⁻¹ : R) * X, -C (↑b⁻¹ : R), 0, ?_⟩
    have h1 : C (q : R) * C (↑hq.unit⁻¹ : R) = 1 := by
      rw [← C_mul, ← map_one C]; congr 1; simpa using hq.mul_val_inv
    have h2 : C (b : R) * C (↑b⁻¹ : R) = 1 := by
      rw [← C_mul, ← map_one C]; simp
    have h3 : (X : R[X]) ^ (q - 1) * X = X ^ q := pow_sub_one_mul (NeZero.ne q) _
    simp only [kf, derivative_sub, derivative_X_pow, derivative_C, sub_zero, pow_zero]
    linear_combination (C (q : R) * C (↑hq.unit⁻¹ : R) * C (↑b⁻¹ : R)) * h3 +
      (C (↑b⁻¹ : R) * X ^ q) * h1 + h2

theorem kpair_hasMap (q : ℕ) [NeZero q] (hq : IsUnit (q : R)) (b : Rˣ) :
    (kpair q hq b).HasMap (AdjoinRoot.root (kf q b)) :=
  ⟨by simp [kpair], by simp [kpair]⟩

noncomputable def kpres (q : ℕ) [NeZero q] (hq : IsUnit (q : R)) (b : Rˣ) :
    StandardEtalePresentation R (AdjoinRoot (kf q b)) where
  P := kpair q hq b
  x := AdjoinRoot.root (kf q b)
  hasMap := kpair_hasMap q hq b
  lift_bijective := by
    let Q := kpair q hq b
    let φ := Q.lift _ (kpair_hasMap q hq b)
    have hX : Polynomial.aeval Q.X (kf q b) = 0 := Q.hasMap_X.1
    let ψ : AdjoinRoot (kf q b) →ₐ[R] Q.Ring := AdjoinRoot.liftAlgHom (kf q b) (Algebra.ofId R Q.Ring) Q.X
      (by simpa [Polynomial.aeval_def] using hX)
    have e1 : ψ.comp φ = AlgHom.id R _ := Q.hom_ext (by simp [φ, ψ])
    have e2 : φ.comp ψ = AlgHom.id R _ := AdjoinRoot.algHom_ext (by simp [φ, ψ])
    exact ⟨Function.LeftInverse.injective (g := ψ) (fun x => congrArg (· x) e1),
      Function.RightInverse.surjective (g := ψ) (fun x => congrArg (· x) e2)⟩

instance (q : ℕ) [NeZero q] [Fact (IsUnit (q : R))] (b : Rˣ) : Algebra.IsStandardEtale R (AdjoinRoot (kf q b)) :=
  ⟨⟨kpres q Fact.out b⟩⟩

theorem kf_etale (q : ℕ) [NeZero q] (hq : IsUnit (q : R)) (b : Rˣ) : Algebra.Etale R (AdjoinRoot (kf q b)) := by
  have : Fact (IsUnit (q : R)) := ⟨hq⟩; infer_instance

theorem kf_comap_surj (q : ℕ) [NeZero q] (b : Rˣ) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap R (AdjoinRoot (kf q b)))) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · intro p; exact (p.isPrime.ne_top (Subsingleton.elim _ _)).elim
  · let pb := AdjoinRoot.powerBasis' (kf_monic q b)
    have : Module.Free R (AdjoinRoot (kf q b)) := Module.Free.of_basis pb.basis
    have hd : 0 < pb.dim := by
      have : (kf q b).natDegree = q := natDegree_X_pow_sub_C
      change 0 < (kf q b).natDegree
      rw [this]; exact Nat.pos_of_ne_zero (NeZero.ne q)
    have : Nontrivial (AdjoinRoot (kf q b)) := nontrivial_of_ne _ _ (pb.basis.ne_zero ⟨0, hd⟩)
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat

section geo
variable (q : ℕ) [NeZero q] (V : Scheme.{0}) (b : (Γ(V, ⊤))ˣ)

noncomputable abbrev kA : CommRingCat.{0} := CommRingCat.of (AdjoinRoot (kf q b))
noncomputable abbrev kφ : Γ(V, ⊤) ⟶ kA q V b := CommRingCat.ofHom (algebraMap _ _)
noncomputable abbrev kW : Scheme.{0} := pullback V.toSpecΓ (Spec.map (kφ q V b))
noncomputable abbrev kπ : kW q V b ⟶ V := pullback.fst _ _

theorem kπ_etale_surj (hq : IsUnit (q : Γ(V, ⊤))) : Etale (kπ q V b) ∧ Surjective (kπ q V b) := by
  have := kf_etale q hq b
  have h1 : Etale (Spec.map (kφ q V b)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.2 this
  have h2 : Surjective (Spec.map (kφ q V b)) := by
    refine ((flat_and_surjective_SpecMap_iff (kφ q V b)).2 ?_).2
    refine RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.2 ⟨?_, kf_comap_surj q b⟩
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  exact ⟨inferInstance, inferInstance⟩

noncomputable abbrev kψ : kA q V b ⟶ Γ(kW q V b, ⊤) :=
  (Scheme.ΓSpecIso (kA q V b)).inv ≫ (pullback.snd V.toSpecΓ (Spec.map (kφ q V b))).appTop

theorem kφ_kψ : kφ q V b ≫ kψ q V b = (kπ q V b).appTop := by
  have hnat : kφ q V b ≫ (Scheme.ΓSpecIso (kA q V b)).inv =
      (Scheme.ΓSpecIso Γ(V, ⊤)).inv ≫ (Spec.map (kφ q V b)).appTop := by
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
    exact (Scheme.ΓSpecIso_naturality _).symm
  have hc : V.toSpecΓ.appTop ≫ (kπ q V b).appTop =
      (Spec.map (kφ q V b)).appTop ≫ (pullback.snd V.toSpecΓ (Spec.map (kφ q V b))).appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, pullback.condition]
  rw [← Category.assoc, hnat, Category.assoc, ← hc, Scheme.toSpecΓ_appTop, Iso.inv_hom_id_assoc]

theorem unitsToSec_nat {U W : Scheme.{0}} (f : W ⟶ U) (x : Additive (Γ(U, ⊤))ˣ) :
    Gm.obj.map f.op (unitsToSec U x) = unitsToSec W (Additive.ofMul (Units.map f.appTop.hom x.toMul)) := by
  have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality f.op
  exact (ConcreteCategory.congr_hom h ⟨x⟩).symm
end geo

theorem LeafUnitRoot_of : LateralTheory.E.H2CurveOrder.LeafKumSecSurjPf.LeafUnitRoot := by
  intro q _ V hq b
  obtain ⟨he, hs⟩ := kπ_etale_surj q V b hq
  refine Scheme.etaleTopology.superset_covering ?_ (Precoverage.generate_mem_toGrothendieck
    ((Scheme.singleton_mem_precoverage_iff (P := @Etale) (kπ q V b)).2 ⟨hs.surj, he⟩))
  rw [Sieve.generate_le_iff]
  rintro _ _ ⟨⟩
  have hroot : (AdjoinRoot.root (kf q b)) ^ q = algebraMap _ (AdjoinRoot (kf q b)) (b : Γ(V, ⊤)) := by
    have h2 : AdjoinRoot.mk (kf q b) (X ^ q - C (b : Γ(V, ⊤))) = 0 := AdjoinRoot.mk_self
    rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h2
    exact sub_eq_zero.1 h2
  have hu : IsUnit (AdjoinRoot.root (kf q b)) :=
    (isUnit_pow_iff (NeZero.ne q)).1 (hroot ▸ b.isUnit.map _)
  refine ⟨unitsToSec _ (Additive.ofMul (Units.map (kψ q V b).hom hu.unit)), ?_⟩
  have e := pow_unitsToSec q (kW q V b) (Additive.ofMul (Units.map (kψ q V b).hom hu.unit))
  refine e.trans ?_
  rw [unitsToSec_nat]
  congr 1
  apply Additive.toMul.injective
  ext
  simp only [toMul_nsmul, toMul_ofMul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe,
    IsUnit.unit_spec]
  rw [← map_pow, hroot, ← kφ_kψ]
  rfl

end LateralTheory.E.H2CurveOrder.LeafUnitRootPf
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.H2CurveOrder

open LateralTheory.E.E4 LeafKumSeqPf KummerH0Surjection

theorem resMap_nsmul_homotopy (F : Shv ℤ) (q : ℕ) :
    Nonempty (Homotopy (resMap ℤ (q • 𝟙 F)) (q • 𝟙 (res ℤ F))) := by
  refine ⟨?_⟩
  have H : Homotopy (InjectiveResolution.desc (q • 𝟙 F) (injectiveResolution F) (injectiveResolution F))
      (q • 𝟙 (injectiveResolution F).cocomplex) :=
    InjectiveResolution.descHomotopy (q • 𝟙 F) _ _ (by simp)
      (by simp [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Functor.map_nsmul])
  refine (H.extend ComplexShape.embeddingUpNat).trans (Homotopy.ofEq ?_)
  exact ((ComplexShape.embeddingUpNat.extendFunctor (Shv ℤ)).map_nsmul).trans
    (congrArg (q • ·) ((ComplexShape.embeddingUpNat.extendFunctor (Shv ℤ)).map_id _))

theorem ofHom_nsmul {K L : Cx ℤ} (f : K ⟶ L) (q : ℕ) : Cochain.ofHom (q • f) = q • Cochain.ofHom f := by
  induction q with
  | zero => simp
  | succ q ih => rw [succ_nsmul, succ_nsmul, Cochain.ofHom_add, ih]

theorem comp_nsmul' {K L M : Cx ℤ} {n : ℤ} (a : Cochain K L n) (b : Cochain L M 0) (q : ℕ) :
    a.comp (q • b) (add_zero n) = q • a.comp b (add_zero n) := by
  induction q with
  | zero => simp
  | succ q ih => rw [succ_nsmul, succ_nsmul, Cochain.comp_add, ih]

theorem mk_nsmul {K L : Cx ℤ} {n : ℤ} (a : Cocycle K L n) (q : ℕ) :
    CohomologyClass.mk (q • a) = q • CohomologyClass.mk a := by
  induction q with
  | zero => simp
  | succ q ih => rw [succ_nsmul, succ_nsmul, CohomologyClass.mk_add, ih]

theorem post_nsmul (K : Cx ℤ) (F : Shv ℤ) (q : ℕ) (n : ℤ) (x : HK ℤ K F n) :
    HK.post ℤ K (q • 𝟙 F) n x = q • x := by
  obtain ⟨H⟩ := resMap_nsmul_homotopy F q
  obtain ⟨a, rfl⟩ := CohomologyClass.mk_surjective x
  rw [← mk_nsmul]
  show CohomologyClass.mk _ = CohomologyClass.mk _
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨a.1.comp (Cochain.ofHomotopy H) (by omega), ?_⟩
  rw [δ_comp _ _ _ (n + 1) 0 n (by omega) rfl (by omega), δ_ofHomotopy, Cocycle.δ_eq_zero, ofHom_nsmul,
    Cochain.comp_sub, comp_nsmul']
  simp [zcomp]
  rfl

theorem powGm_eq (q : ℕ) : powGm q = q • 𝟙 Gm := by
  have h : Functor.whiskerLeft Scheme.Γ (powNat q) = q • 𝟙 (Scheme.Γ ⋙ unitsF) := by
    ext U x
    simp [powNat]
    rfl
  unfold powGm
  rw [h, Functor.map_nsmul, CategoryTheory.Functor.map_id]
  rfl

theorem muUnits : LeafKumMuPf.LeafKumMuUnits := by
  have hI := LeafKumMuInjPfGlue.LeafKumMuInj_of TwLocGenPf.TwLocGen_of GmSepPf.GmSep_of
  exact LeafKumMuUnitsPf.LeafKumMuUnits_of LeafKumMuMapPf.LeafKumMuMap_of hI
    (LeafKumMuSurjPf.etale_mu_twist_sections_surj_of_prim_root_pow_inj LeafKumMuSurjPrimPf.LeafKumMuSurjPrim_of
      LeafKumMuSurjPowPf.LeafKumMuSurjPow_of hI)

theorem kumSecSurj : LeafKumSecSurj := LeafKumSecSurjPf.LeafKumSecSurj_of LeafUnitRootPf.LeafUnitRoot_of

theorem unit_of_over (q : ℕ) {Ω : Type} [CommRing Ω] (hq : IsUnit (q : Ω)) {U : Scheme.{0}} (x : U ⟶ Sp Ω) :
    IsUnit (q : Γ(U, ⊤)) := by
  simpa using hq.map ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫ x.appTop).hom

theorem kumSeq : LateralTheory.E.LeafKumDeltaPf.LeafKumSeq := by
  intro hy q _ Ω _ _ hq C c hc
  have hA7 : A7 := hy.2.2.2.2.2.1
  have hA8 : A8 := hy.2.2.2.2.2.2.1
  have hA10 : A10 := hy.2.2.2.2.2.2.2.2.1
  obtain ⟨a, ha0⟩ := LeafKumMuPf.LeafKumMuSec_of muUnits q Ω hq
  have ha := hA10 ℤ (sch.obj C) a (fun U ⟨x⟩ => ha0 U ⟨(show U ⟶ C from x) ≫ c⟩) 2
  have hβ := hA10 ℤ (sch.obj C) (kumM q) (fun U ⟨x⟩ =>
    ⟨sec_injective _ U, kumSecSurj q U (unit_of_over q hq ((show U ⟶ C from x) ≫ c))⟩) 1
  set K := (chains ℤ).obj (sch.obj C) with hK
  obtain ⟨z, hz⟩ := hA7 ℤ (kumSC q) (kumSC_shortExact q)
  obtain ⟨_, hex1, hex2⟩ := hz K 1
  have hR := hA8 ℤ (ZMod q) (Int.castRingHom (ZMod q)) (sch.obj C) (tw q 1) 2
  let P := AddEquiv.ofBijective (HK.post ℤ K (kumM q) 1) hβ
  let A := AddEquiv.ofBijective (HK.post ℤ K a 2) ha
  let Rr := AddEquiv.ofBijective (restrH (Int.castRingHom (ZMod q)) (sch.obj C) (tw q 1) 2) hR
  let T : Ht q (sch.obj C) 2 1 ≃+ HK ℤ K (kumSC q).X₁ (1 + 1) := Rr.trans A
  let ex : HK ℤ K (kumSC q).X₃ 1 →+ HK ℤ K (kumSC q).X₁ (1 + 1) := HK.ext ℤ K z 1 (1 + 1) rfl
  let fm : HK ℤ K (kumSC q).X₁ (1 + 1) →+ HK ℤ K Gm 2 := HK.post ℤ K (kumSC q).f (1 + 1)
  let gm : HK ℤ K Gm 1 →+ HK ℤ K (kumSC q).X₃ 1 := HK.post ℤ K (kumSC q).g 1
  have e1 : Function.Exact gm ex := hex1
  have e2 : Function.Exact ex fm := hex2
  have hpg : ∀ w, P (gm w) = q • w := by
    intro w
    refine (post_comp ℤ K (kumSC q).g (kumM q) 1 w).symm.trans ?_
    have : (kumSC q).g ≫ kumM q = q • 𝟙 Gm := (cokernel.π_desc _ _ _).trans (powGm_eq q)
    rw [this]
    exact post_nsmul K Gm q 1 w
  refine ⟨T.symm.toAddMonoidHom.comp (ex.comp P.symm.toAddMonoidHom), fm.comp T.toAddMonoidHom, ?_, ?_⟩
  · intro y
    change T.symm (ex (P.symm y)) = 0 ↔ _
    rw [AddEquiv.map_eq_zero_iff, e1]
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨w, by rw [← hpg, hw, AddEquiv.apply_symm_apply]⟩
    · rintro ⟨w, rfl⟩
      exact ⟨w, by rw [← hpg, AddEquiv.symm_apply_apply]⟩
  · intro x
    change fm (T x) = 0 ↔ ∃ y, T.symm (ex (P.symm y)) = x
    rw [e2]
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨P w, by rw [AddEquiv.symm_apply_apply, hw, AddEquiv.symm_apply_apply]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨P.symm y, (T.apply_symm_apply _).symm⟩

end LateralTheory.E.H2CurveOrder

end
end
