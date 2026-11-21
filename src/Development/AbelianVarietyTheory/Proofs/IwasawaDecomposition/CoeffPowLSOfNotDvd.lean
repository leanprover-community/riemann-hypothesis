import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefSetNonemptyOfNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasLocalRingPoints
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsPolPremises
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsPullCubicalId

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LocM.FJ
open GlobalTheory.Toroidal
open GlobalTheory.ArcQ (Wit LieImg)

noncomputable section

namespace GlobalTheory.ArcSubst

open GlobalTheory.ArcBaseChange GlobalTheory.ObjRebase

set_option maxHeartbeats 1600000 in

theorem lieImg_subst : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] (b : O →+* A) (a₀ : ArcIn Dw l β A b) (γ γ' : levelForms H l.M' a₀.D₀.X) (h : γ ∈ admitted H l.M' a₀.D₀.X) (h' : γ' ∈ admitted H l.M' a₀.D₀.X) (χ : Sp (PowerSeries A) ⟶ Y.X) (g : PowerSeries A →+* PowerSeries A) (W : Wit Y (withForm a₀ γ h) χ) (W' : Wit Y (withForm a₀ γ' h') (spMap g ≫ χ)) (hD : Out.IsPullDeg g W.P.D.toPre W'.P.D.toPre) (bc : W'.t.G ≅ (Over.pullback (Out.specOf g)).obj W.t.G) (w₁ : LB.Iso W'.P.D.toPre.P.L (a₀.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf g)) ≫ W.φ))), g.comp (PowerSeries.C (R := A)) = PowerSeries.C → g PowerSeries.X ∈ Ideal.span {PowerSeries.X} → Out.IsPullUnif g hD bc W.P.U W'.P.U → (∀ y, hD.xe (W'.e y) = W.e y) → W'.φ = (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf g)) ≫ W.φ → HEq W'.w w₁ → Tri W.w hD.w w₁ → ∀ (ν : Out.GtPt a₀.D₀ (epsR A)) (v : epsR (PowerSeries A) ⟶ W.t.G) (v' : epsR (PowerSeries A) ⟶ W'.t.G), LieImg W ν v → v'.left ≫ bc.hom.left ≫ pullback.fst W.t.G.hom (Out.specOf g) = spMap (dualMap g) ≫ v.left → LieImg W' ν v' := by
  intro E _ _ _ H Dw l Xo c O _ β Y A _ _ _ b a₀ γ γ' h h' χ g W W' hD bc w₁ hgC hgX hU he hφ hw₁ T ν v v' hv hv'
  intro n ρ' κ' vn' hρ₁ hρ₂ hκ₁ hκ₂ hb hf x
  obtain ⟨wL, -, -, -, lev⟩ := (isPullUnif_iff_stalks _ _ _ _ _ _ _ hD _ _ _ _ bc _ _).1 hU
  obtain ⟨hm, hh, ⟨-, ht⟩, -⟩ := lev n
  obtain ⟨ho, Ht⟩ := ht (W'.e x)
  rw [he] at ho Ht
  have Hν := pmaps_pullIdIso _ _ _ (ν.isGen x)
  have hs : W'.φ ≫ 𝟙 _ = (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf g)) ≫ W.φ :=
    (Category.comp_id _).trans hφ
  have S : Sq W.w hD.w (pullIdIso a₀.D₀.P.L) W'.w := by
    intro Z r z j i i' k hj hi hi' hk
    have hj' : W'.φ (r z) ∈ a₀.D₀.P.L.U j := (congrArg (fun f => f (r z) ∈ a₀.D₀.P.L.U j) hφ).mpr hj
    have pg := (isGen_iff W'.w).1 W'.spec.2.1 Z r z j i' k k hj' hi' hk hk
    rw [← T Z r z j i k hj hi hk, ← gw_heq hφ hw₁ r z j k, pg, gm_self W'.P.D.toPre.P.isLB r z hk, inv_one, mul_one,
      gw_pullIdIso a₀.D₀.P.L (r ≫ W'.φ) z j i' hj' hi']

  have := isLocalRing_trunc A n
  have := ConstTan.isLocalRing_dual (PowerSeries A ⧸ Ideal.span {(PowerSeries.X : PowerSeries A)} ^ (n + 1))
  let I : Ideal (PowerSeries A) := Ideal.span {PowerSeries.X}
  have hI : I ^ (n + 1) ≤ (I ^ (n + 1)).comap g := Ideal.map_le_iff_le_comap.1 (by
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton]
    exact Ideal.pow_right_mono ((Ideal.span_singleton_le_iff_mem _).2 hgX) _)
  let gb : PowerSeries A ⧸ I ^ (n + 1) →+* PowerSeries A ⧸ I ^ (n + 1) := Ideal.quotientMap _ g hI
  let ρ : DualNumber (PowerSeries A) →+* DualNumber (PowerSeries A ⧸ I ^ (n + 1)) := dualMap (Ideal.Quotient.mk _)
  let κ : DualNumber A →+* DualNumber (PowerSeries A ⧸ I ^ (n + 1)) :=
    dualMap ((Ideal.Quotient.mk _).comp (PowerSeries.C (R := A)))
  let s : Sp (DualNumber (PowerSeries A ⧸ I ^ (n + 1))) ⟶ Sp (PowerSeries A ⧸ I ^ (n + 1)) := spMap (algebraMap _ _)
  have hs₀ : s ≫ Out.thick (PowerSeries A) I n = spMap ρ ≫ (epsR (PowerSeries A)).hom :=
    ((ArcBaseChange.spMap_comp' _ _).trans (congrArg spMap (RingHom.ext fun r =>
      (dualMap_inl (Ideal.Quotient.mk (I ^ (n + 1))) r).symm : _ = ρ.comp (algebraMap _ _)))).trans
      (ArcBaseChange.spMap_comp' _ _).symm
  let vn : Sp (DualNumber (PowerSeries A ⧸ I ^ (n + 1))) ⟶ (Out.thickObj (PowerSeries A) I n W.t.G).left :=
    pullback.lift (spMap ρ ≫ v.left) s (by rw [Category.assoc, Over.w v, hs₀])
  have hx : vn ≫ (Out.fstG I n W.t.G).left = spMap ρ ≫ v.left := pullback.lift_fst _ _ _
  have G := hv n ρ κ vn (dualMap_inl _) (dualMap_eps' _) (dualMap_inl _) (dualMap_eps' _)
    (pullback.lift_snd _ _ _) hx x
  let q := spMap (dualMap gb)
  have hρ : spMap ρ' ≫ spMap (dualMap g) = q ≫ spMap ρ := by
    rw [ArcBaseChange.spMap_comp', ArcBaseChange.spMap_comp']
    refine congrArg spMap (dual_hom_ext (fun r => ?_) ?_)
    · simp only [RingHom.comp_apply, ρ, dualMap_inl, hρ₁]
      rfl
    · simp only [RingHom.comp_apply, ρ, dualMap_eps', hρ₂]
  have hκ : spMap κ' ≫ 𝟙 _ = q ≫ spMap κ := by
    rw [Category.comp_id, ArcBaseChange.spMap_comp']
    refine congrArg spMap (dual_hom_ext (fun r => ?_) ?_)
    · simp only [RingHom.comp_apply, κ, dualMap_inl, hκ₁]
      exact congrArg (fun y => TrivSqZeroExt.inl (Ideal.Quotient.mk (I ^ (n + 1)) y)) (RingHom.congr_fun hgC r).symm
    · simp only [RingHom.comp_apply, κ, dualMap_eps', hκ₂]
  have hvn : vn' ≫ hm = q ≫ vn := by
    have := thick_mono (PowerSeries A) I n
    have : Mono (Out.fstG I n W.t.G).left := inferInstanceAs (Mono (pullback.fst _ _))
    rw [← cancel_mono (Out.fstG I n W.t.G).left, Category.assoc, hh, ← Category.assoc, hf, Category.assoc]
    erw [hv']
    rw [← Category.assoc, hρ, Category.assoc, Category.assoc, hx]
  refine genRelR_baseChange hs S W.spec.2.1 W.P.D.toPre.P.isLB a₀.D₀.P.isLB ((W.P.U.gt n).t_gen _) (ν.isGen _) ho Ht Hν
    hvn hκ (fun k => ?_) G
  have e := comp_eq_of_squares hs (ho k) (g := Out.DegPre.gtφT a₀.D₀ (epsR A) ν.b x k) (g' := Out.DegPre.gtφT a₀.D₀ (epsR A) ν.b x k) (d := 𝟙 _)
    (by rw [Category.comp_id, Category.id_comp]) hvn hκ (G.1 k)
  simpa only [Category.comp_id] using e

end GlobalTheory.ArcSubst
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LocM.FJ
open GlobalTheory.Toroidal
open GlobalTheory.ArcQ (Wit LieImg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_forms_arc_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] (b : O →+* A) (a₀ : ArcIn Dw l β A b) (γ γ' : levelForms H l.M' a₀.D₀.X) (h : γ ∈ admitted H l.M' a₀.D₀.X) (h' : γ' ∈ admitted H l.M' a₀.D₀.X) (χ : Sp (PowerSeries A) ⟶ Y.X) (g : PowerSeries A →+* PowerSeries A) (W : Wit Y (withForm a₀ γ h) χ) (W' : Wit Y (withForm a₀ γ' h') (spMap g ≫ χ)) (hD : Out.IsPullDeg g W.P.D.toPre W'.P.D.toPre) (bc : W'.t.G ≅ (Over.pullback (Out.specOf g)).obj W.t.G) (w₁ : LB.Iso W'.P.D.toPre.P.L (a₀.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf g)) ≫ W.φ))), g.comp (PowerSeries.C (R := A)) = PowerSeries.C → g PowerSeries.X ∈ Ideal.span {PowerSeries.X} → Out.IsPullUnif g hD bc W.P.U W'.P.U → (∀ y, hD.xe (W'.e y) = W.e y) → W'.φ = (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf g)) ≫ W.φ → HEq W'.w w₁ → Tri W.w hD.w w₁ → ∀ (ν : Out.GtPt a₀.D₀ (epsR A)) (v : epsR (PowerSeries A) ⟶ W.t.G) (v' : epsR (PowerSeries A) ⟶ W'.t.G), LieImg W ν v → v'.left ≫ bc.hom.left ≫ pullback.fst W.t.G.hom (Out.specOf g) = spMap (dualMap g) ≫ v.left → LieImg W' ν v' := by
  atlas_forward_decl GlobalTheory.ArcSubst.lieImg_subst
end

section
set_option maxHeartbeats 800000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LocM.FJ
open GlobalTheory.Toroidal
open GlobalTheory.ArcQ (Wit LieImg)

namespace GlobalTheory.LocM.FJ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Subst

variable {R : Type} [CommRing R] {a : ℕ} (ha : 1 ≤ a)

def powPS : PowerSeries R →+* PowerSeries R := (PowerSeries.expand a (by omega)).toRingHom

theorem powPS_apply (g : PowerSeries R) : powPS ha g = PowerSeries.expand a (by omega) g := rfl

theorem powPS_comp_C : (powPS ha).comp (PowerSeries.C (R := R)) = PowerSeries.C :=
  RingHom.ext fun r => PowerSeries.expand_C a (by omega) r

theorem powPS_X : powPS ha (PowerSeries.X : PowerSeries R) = PowerSeries.X ^ a := PowerSeries.expand_X a (by omega)

theorem powPS_injective : Function.Injective (powPS ha : PowerSeries R → PowerSeries R) := fun f g h => by
  ext m
  have := congrArg (PowerSeries.coeff (a * m)) h
  simpa only [powPS_apply, PowerSeries.coeff_expand_mul] using this

theorem map_powPS {S : Type} [CommRing S] (f : R →+* S) (g : PowerSeries R) :
    PowerSeries.map f (powPS ha g) = powPS ha (PowerSeries.map f g) := PowerSeries.map_expand a (by omega) f g

variable {K : Type} [Field K]

def powLS : LaurentSeries K →+* LaurentSeries K :=
  HahnSeries.embDomainRingHom (AddMonoidHom.mulLeft (a : ℤ)) (mul_right_injective₀ (Int.natCast_ne_zero.2 (by omega)))
    fun _ _ => mul_le_mul_iff_right₀ (Int.natCast_pos.2 (by omega))

theorem coeff_powLS_mul (f : LaurentSeries K) (n : ℤ) : (powLS ha f).coeff (a * n) = f.coeff n :=
  HahnSeries.embDomain_coeff

theorem coeff_powLS_of_not_dvd (f : LaurentSeries K) {n : ℤ} (h : ¬ (a : ℤ) ∣ n) : (powLS ha f).coeff n = 0 :=
  HahnSeries.embDomain_of_notMem_range fun ⟨m, hm⟩ => h ⟨m, hm.symm⟩

theorem powLS_coe (g : PowerSeries K) :
    powLS ha (HahnSeries.ofPowerSeries ℤ K g) = HahnSeries.ofPowerSeries ℤ K (powPS ha g) := by
  ext n
  by_cases h : (a : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [coeff_powLS_mul]
    have ha' : (0 : ℤ) < a := Int.natCast_pos.2 (by omega)
    rcases lt_or_ge m 0 with hm | hm
    · simp [PowerSeries.coeff_coe, hm, mul_neg_of_pos_of_neg ha' hm]
    · lift m to ℕ using hm
      rw [← Nat.cast_mul, LaurentSeries.coeff_coe_powerSeries, LaurentSeries.coeff_coe_powerSeries, powPS_apply,
        PowerSeries.coeff_expand_mul]
  · rw [coeff_powLS_of_not_dvd ha _ h, PowerSeries.coeff_coe]
    split_ifs
    · rfl
    · exact (PowerSeries.coeff_expand_of_not_dvd a (by omega) g fun h' => h (Int.natCast_dvd.2 h')).symm

theorem powLS_comp_toLaurent {p : ℕ} (F : DVF p) : (powLS ha).comp F.toLaurent = F.toLaurent.comp (powPS ha) := by
  refine RingHom.ext fun g => ?_
  show powLS ha (HahnSeries.ofPowerSeries ℤ _ (PowerSeries.map _ g)) =
    HahnSeries.ofPowerSeries ℤ _ (PowerSeries.map _ (powPS ha g))
  rw [powLS_coe, map_powPS]

end Subst

theorem dualMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) :=
  RingHom.ext fun x => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

theorem coe_nsmul_apply {N : ℕ} {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (n : ℕ) (γ : levelForms H N X) (y z : X) :
    ((n • γ : levelForms H N X) : LinearMap.BilinForm ℤ X) y z = n * (γ : LinearMap.BilinForm ℤ X) y z := by
  simp

theorem pow_zpow_form {F : Type} [Field F] (uF : F) (n : ℕ) {N : ℕ} {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
    (γ : levelForms H N X) (y z : X) {k : ℤ} (hk : k ∣ (γ : LinearMap.BilinForm ℤ X) y z) :
    uF ^ (((n • γ : levelForms H N X) : LinearMap.BilinForm ℤ X) y z / k) =
      (uF ^ n) ^ ((γ : LinearMap.BilinForm ℤ X) y z / k) := by
  rw [coe_nsmul_apply, Int.mul_ediv_assoc _ hk, zpow_mul, zpow_natCast]

theorem smul_mem_adm {N : ℕ} {X : Type} [AddCommGroup X] [Module (𝓞 E) X] {γ : levelForms H N X}
    (h : γ ∈ admitted H N X) {n : ℕ} (hn : 1 ≤ n) : n • γ ∈ admitted H N X := by
  refine ⟨fun y hy => ?_, fun y z => ?_⟩
  · rw [coe_nsmul_apply]
    exact mul_pos (by exact_mod_cast hn) (h.1 y hy)
  · rw [coe_nsmul_apply]
    exact Dvd.dvd.mul_left (h.2 y z) _

section Reform

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {A : Type} [CommRing A] [IsDomain A] {b : O →+* A} {a₀ : ArcIn Dw l β A b}

def reform {γ : levelForms H l.M' a₀.D₀.X} {h : γ ∈ admitted H l.M' a₀.D₀.X} {n : ℕ} (h' : n • γ ∈ admitted H l.M' a₀.D₀.X)
    {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {f f' : A →+* R} {u u' : R} {χ : Sp R ⟶ Y.X}
    (W : ArcWit Y (withForm a₀ γ h) I f u' χ) (hf : f = f') (hu : u' = u ^ n) :
    ArcWit Y (withForm a₀ (n • γ) h') I f' u χ where
  t := W.t
  m := W.m
  P := W.P
  φ := W.φ
  he := hf ▸ W.he
  w := W.w
  e := W.e
  spec := by
    subst hf hu
    obtain ⟨s1, s2, s3, s4, s5, s6⟩ := W.spec
    refine ⟨s1, s2, s3, s4, s5, fun F _ _ _ _ uF hF hu => ?_⟩
    obtain ⟨k1, k2⟩ := s6 F (uF ^ n) hF (by rw [hu, map_pow, map_pow])
    have dv : ∀ y z, (2 * (l.M' : ℤ)) ∣ (γ : LinearMap.BilinForm ℤ a₀.D₀.X) y z := h.2
    refine ⟨fun y => ?_, fun yF hyF k p₀ σ hσ q₀ q x e1 e2 e3 e4 => k2 yF hyF k p₀ σ hσ q₀ q x e1 e2 (fun z => ?_) e4⟩
    · have e := pow_zpow_form uF n γ y y (k := 2) ((dvd_mul_right 2 _).trans (dv y y))
      change GenRel _ _ _ (uF ^ (((n • γ : levelForms H l.M' a₀.D₀.X) : LinearMap.BilinForm ℤ a₀.D₀.X) y y / 2))
      rw [e]
      exact k1 y
    · have hk : (k : ℤ) ∣ 2 * (l.M' : ℤ) := by
        refine Dvd.dvd.mul_left (Int.natCast_dvd_natCast.2 ?_) _
        rcases hσ with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact Nat.dvd_lcm_right l.M l.A
        · exact Nat.dvd_lcm_left l.M l.A
      have e := pow_zpow_form uF n γ q₀.y z (k := k) (hk.trans (dv _ _))
      have e3 := e3 z
      change GenRel _ _ _ (uF ^ (((n • γ : levelForms H l.M' a₀.D₀.X) : LinearMap.BilinForm ℤ a₀.D₀.X) q₀.y z / k)) at e3
      rw [e] at e3
      exact e3

end Reform

theorem isArcChart_pow {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    {Y : Model Xo c β} {A : Type} [CommRing A] [IsDomain A] {b : O →+* A} {a₀ a₁ : ArcIn Dw l β A b} {ϖ : A}
    {χ : Sp (PowerSeries A) ⟶ Y.X} {a : ℕ} (ha : 1 ≤ a) (hχ : IsArcChart Y a₀ ϖ χ)
    (hW : Nonempty (Wit Y a₁ (spMap (powPS ha) ≫ χ))) : IsArcChart Y a₁ ϖ (spMap (powPS ha) ≫ χ) := by
  obtain ⟨h₁, h₂, h₃, -⟩ := hχ
  have mem : ∀ (x : Sp (PowerSeries A)) (s : PowerSeries A),
      s ∈ (spMap (powPS (R := A) ha) x).asIdeal ↔ powPS ha s ∈ x.asIdeal := fun _ _ => Iff.rfl
  have ev : ∀ x, (spMap (powPS (R := A) ha) ≫ χ) x = χ (spMap (powPS (R := A) ha) x) := fun _ => rfl
  refine ⟨?_, fun x => ?_, fun x hx => ?_, (Y.hasArcData_iff _ _ _ _ _).2 hW⟩
  · rw [Category.assoc, h₁, ← Category.assoc, ← spMap_comp, powPS_comp_C]
  · rw [ev]
    refine (h₂ (spMap (powPS (R := A) ha) x)).trans ?_
    rw [mem, powPS_X]
    exact not_congr ⟨fun h => x.isPrime.mem_of_pow_mem a h, fun h => Ideal.pow_mem_of_mem _ h a (by omega)⟩
  · rw [ev]
    refine h₃ (spMap (powPS (R := A) ha) x) fun hm => hx ?_
    rw [mem, map_mul, powPS_X, ← RingHom.comp_apply, powPS_comp_C] at hm
    rcases x.isPrime.mem_or_mem hm with hm | hm
    · exact Ideal.mul_mem_right _ _ hm
    · exact Ideal.mul_mem_left _ _ (x.isPrime.mem_of_pow_mem a hm)

theorem exists_lift_bc {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') {G : Over (Sp R)} {G' : Over (Sp R')}
    (bc : G' ≅ (Over.pullback (Out.specOf g)).obj G) (w : epsR R ⟶ G) :
    ∃ v : epsR R' ⟶ G', v.left ≫ bc.hom.left ≫ pullback.fst G.hom (Out.specOf g) = spMap (dualMap g) ≫ w.left := by
  have cond : (spMap (dualMap g) ≫ w.left) ≫ G.hom = (epsR R').hom ≫ Out.specOf g := by
    rw [Category.assoc, Over.w w]
    exact GlobalTheory.ArcCompare.dual_over g
  refine ⟨Over.homMk (pullback.lift _ _ cond ≫ bc.inv.left) ?_, ?_⟩
  · rw [Category.assoc, Over.w bc.inv]
    exact pullback.lift_snd _ _ _
  · simp only [Over.homMk_left]
    rw [Category.assoc, ← Category.assoc bc.inv.left, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.id_comp]
    exact pullback.lift_fst _ _ _

theorem flagAt_bc {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
    {i₀ : Idx H p} (Z : Mdl Y i₀) {k k' : Type} [Field k] [Field k'] (s : k →+* k') {x : Sp k ⟶ Z.X}
    {v : Vecs Dw (Y Z.i).t k} (h : Z.FlagAt x v) : Z.FlagAt (spMap s ≫ x) (v.bc s) := by
  obtain ⟨a, φ, e, hfr, hfl⟩ := h
  refine ⟨a, s.comp φ, ?_, ?_, ?_⟩
  · rw [← e, spMap_comp, Category.assoc]
  · have := GlobalTheory.LocM.isFrame_bc E H Dw _ _ _ _ _ _ _ s _ _ hfr
    rw [Category.assoc]
    exact this
  · have := GlobalTheory.DRFlag.Spez.sameFlag_bc s hfl
    rw [Vecs.bc_bc] at this
    rwa [Category.assoc]

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : Mdl Y i₀} {F : DVF p} (t : CuspOn Z F)

theorem IsArc.pow {a : ℕ} (ha : 1 ≤ a) {γ : t.Forms} {x : Sp (LaurentSeries ↥F.K) ⟶ Z.X}
    {v : Vecs Dw (Y Z.i).t (LaurentSeries ↥F.K)} (hx : IsArc t γ x v) :
    IsArc t (a • γ) (spMap (powLS ha) ≫ x) (v.bc (powLS ha)) := by
  obtain ⟨h, ϖ, χ, Wt, w, hϖ, hχ, hw, hxχ, hv, hfl⟩ := hx
  have h' : a • γ ∈ t.Dir := smul_mem_adm h ha
  have hI : (Ideal.span {(PowerSeries.X : PowerSeries F.O)}).map (powPS (R := F.O) ha) ≤ Ideal.span {PowerSeries.X} := by
    rw [Ideal.map_span, Set.image_singleton, powPS_X]
    exact Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self _ (by omega))
  obtain ⟨W₁, hD, bc, -, hU, hm, he, w₁, hφ, hw₁, T⟩ := ArcWit.baseChange GlobalTheory.allSixLaws.2.2.1.cubePull GlobalTheory.polBaseChange_holds
    GlobalTheory.UnifPullGuards.unifBaseChange_holds GlobalTheory.allSixLaws.2.2.2.2.1 (qkPullExists GlobalTheory.globalFns_holds) polOActPull
    (GlobalTheory.ArcPull.admissibleBase_powerSeries_span_X F.O) (GlobalTheory.ArcPull.admissibleBase_powerSeries_span_X F.O) Wt (powPS (R := F.O) ha) (powPS_injective ha) hI
  let W' : Wit (Y Z.i) (withForm t.a (a • γ) h') (spMap (powPS (R := F.O) ha) ≫ χ) :=
    reform (f' := PowerSeries.C) (u := PowerSeries.X) h' W₁ (powPS_comp_C ha) (powPS_X ha)
  choose w' hw' using fun τ k => exists_lift_bc (R := PowerSeries F.O) (R' := PowerSeries F.O) (G := Wt.t.G) (G' := W₁.t.G) (powPS (R := F.O) ha) bc (w τ k)
  have hX : powPS (R := F.O) ha (PowerSeries.X : PowerSeries F.O) ∈ Ideal.span {PowerSeries.X} := hI (Ideal.mem_map_of_mem _
    (Ideal.mem_span_singleton_self _))
  refine ⟨h', ϖ, spMap (powPS (R := F.O) ha) ≫ χ, W', w', hϖ, isArcChart_pow ha hχ ⟨W'⟩, fun τ k => ?_, ?_, fun τ k => ?_,
    flagAt_bc Z _ hfl⟩
  · exact GlobalTheory.T.admissible_forms_arc_compare E H Dw _ _ _ _ _ (Y Z.i) F.O _ t.a γ (a • γ) h h' χ (powPS (R := F.O) ha) Wt W' hD bc w₁
      (powPS_comp_C ha) hX hU he hφ hw₁ T (t.e τ k) (w τ k) (w' τ k) (hw τ k) (hw' τ k)
  · rw [Category.assoc, hxχ, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp, powLS_comp_toLaurent]
  · change spMap (dualMap (powLS ha)) ≫ v τ k = spMap (dualMap F.toLaurent) ≫ (w' τ k).left ≫ W₁.m.φ
    rw [hv, hm]
    simp only [Category.assoc]
    rw [reassoc_of% (hw' τ k), ← Category.assoc, ← Category.assoc (spMap (dualMap F.toLaurent)), ← spMap_comp,
      ← spMap_comp, ← dualMap_comp, ← dualMap_comp, powLS_comp_toLaurent]

end GlobalTheory.LocM.FJ
end
end
