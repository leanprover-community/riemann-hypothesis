import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusCoordAdd

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem cubN_descent_telescope {A A' U : Type} [CommGroup A] [CommGroup A'] [CommGroup U] (θ : A → A → A → U)
    (θ' : A' → A' → A' → U) (q : A →* A') (W : A → U) (hc : IsCub θ')
    (h : ∀ x y u, θ' (q x) (q y) (q u) * W (x * y) * W (x * u) * W (y * u) * W 1 =
      W (x * y * u) * W x * W y * W u * θ x y u) (k : ℕ) (x y : A) (hx : q x = 1) :
    cubN θ k 1 x y * W (x ^ k * y) * W x ^ k * W y ^ k * W 1 = W (x ^ k) * W y * W (x * y) ^ k * W 1 ^ k := by
  induction k with
  | zero => simp [cubN, mul_comm]
  | succ k ih =>
    have e := h (x ^ k) x y
    rw [hx, hc.face₂, _root_.one_mul, ← pow_succ] at e
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [pow_succ (W x), pow_succ (W y), pow_succ (W (x * y)), pow_succ (W 1)]
    generalize (∏ i ∈ Finset.range k, θ (x ^ i) x y) = P at ih ⊢
    apply Additive.ofMul.injective
    have a1 := congrArg Additive.ofMul ih
    have a2 := congrArg Additive.ofMul e
    simp only [ofMul_mul] at a1 a2 ⊢
    linear_combination (norm := abel) a1 - a2

theorem cubN_descent_opposite : ∀ (A A' U : Type) [CommGroup A] [CommGroup A'] [CommGroup U] (θ : A → A → A → U) (θ' : A' → A' → A' → U) (q : A →* A') (W : A → U), IsCub θ' → (∀ x y u, θ' (q x) (q y) (q u) * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * θ x y u) → ∀ (k : ℕ) (x y : A), q x = 1 → cubN θ k 1 x y * θ y (x ^ k) (x ^ k)⁻¹ * W y ^ (k + 1) * W x ^ k * W (x ^ k)⁻¹ = W (x * y) ^ k * W (y * (x ^ k)⁻¹) * W 1 ^ (k + 1) := by
  intro A A' U _ _ _ θ θ' q W hc h k x y hx
  have t := cubN_descent_telescope θ θ' q W hc h k x y hx
  have e := h y (x ^ k) (x ^ k)⁻¹
  rw [map_pow, hx, one_pow, hc.face₂, _root_.one_mul, mul_inv_cancel, mul_inv_cancel_right, mul_comm y (x ^ k)] at e
  rw [pow_succ (W y), pow_succ (W 1)]
  apply Additive.ofMul.injective
  have a1 := congrArg Additive.ofMul t
  have a2 := congrArg Additive.ofMul e
  simp only [ofMul_mul] at a1 a2 ⊢
  linear_combination (norm := abel) a1 - a2

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.UU.TorMul

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def germScal {W : Type} [CommRing W] {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of W)) (z : Z) :
    W →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ ⊤ z trivial).hom.comp (r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom)

theorem gs_scal {W : Type} [CommRing W] {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of W)) (z : Z) (c : W) :
    gs (𝟙 Z) z ⊤ (scal (R := W) r c) = germScal r z c :=
  gs_eq (𝟙 Z) z ⊤ trivial _

def push (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ G) :=
  pushHom (isGrpPullback_pullback G (thick R I e)) T

theorem push_left (e : ℕ) {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (y : T ⟶ thickObj R I e G) :
    (push I e G T y).left = y.left ≫ (fstG I e G).left := rfl

theorem push_inj (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    Function.Injective (push I e G T) := fun y y' h =>
  Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun q => q.left) h) ((Over.w y).trans (Over.w y').symm))

theorem push_surj (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    Function.Surjective (push I e G T) := fun x =>
  ⟨Over.homMk (pullback.lift x.left T.hom (Over.w x)) (pullback.lift_snd _ _ _),
    Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩

def Coord {e : ℕ} (g : GtCoord I D e G) {W : Type} [CommRing W]
    {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (r : T.left ⟶ Spec (CommRingCat.of W))
    (a : Multiplicative D.X →* Wˣ) (y : T ⟶ thickObj R I e G) : Prop :=
  GlobalTheory.TorusCoord.im g y = 1 ∧ ∀ (χ : D.X) (z : T.left) (J), Good D.P.L z J →
    val (g.t χ) y.left z J = Units.map (germScal r z : W →* _) (a (Multiplicative.ofAdd χ))

section
variable {e : ℕ} (g : GtCoord I D e G) {W : Type} [CommRing W]
    {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (r : T.left ⟶ Spec (CommRingCat.of W))

theorem coord_one : Coord g r 1 (1 : T ⟶ thickObj R I e G) :=
  ⟨GlobalTheory.TorusCoord.im_one g, fun χ z J hJ => (GlobalTheory.TorusCoord.val_unit g χ hJ).trans (map_one _).symm⟩

theorem val_mul_of (hG : GlobalFnsSt) {y y' : T ⟶ thickObj R I e G} (h : GlobalTheory.TorusCoord.im g y = 1)
    (χ : D.X) (z : T.left) (J) (hJ : Good D.P.L z J) :
    val (g.t χ) (y * y').left z J = val (g.t χ) y.left z J * val (g.t χ) y'.left z J := by
  have k := GlobalTheory.TorusCoord.val_t_mul_points g hG χ y y' z J hJ
  have c : GlobalTheory.TorusCoord.cubeVal g χ z J y y' = 1 := by
    unfold GlobalTheory.TorusCoord.cubeVal
    rw [h]
    exact (isCub_cubV D.cub (T := (Over.map (thick R I e)).obj T) hJ).face₂ _ _
  rwa [c, _root_.mul_one] at k

theorem coord_mul (hG : GlobalFnsSt) {a a' : Multiplicative D.X →* Wˣ} {y y' : T ⟶ thickObj R I e G}
    (h : Coord g r a y) (h' : Coord g r a' y') : Coord g r (a * a') (y * y') := by
  refine ⟨by rw [GlobalTheory.TorusCoord.im_mul, h.1, h'.1, _root_.mul_one], fun χ z J hJ => ?_⟩
  exact (val_mul_of g hG h.1 χ z J hJ).trans
    ((congrArg₂ (· * ·) (h.2 χ z J hJ) (h'.2 χ z J hJ)).trans (map_mul _ _ _).symm)

theorem coord_inv (hG : GlobalFnsSt) {a : Multiplicative D.X →* Wˣ} {y : T ⟶ thickObj R I e G}
    (h : Coord g r a y) : Coord g r a⁻¹ y⁻¹ := by
  refine ⟨?_, fun χ z J hJ => ?_⟩
  · have := GlobalTheory.TorusCoord.im_mul g y y⁻¹
    rw [mul_inv_cancel, GlobalTheory.TorusCoord.im_one, h.1, _root_.one_mul] at this
    exact this.symm
  · have k := (((GlobalTheory.TorusCoord.val_unit g χ hJ).symm.trans
      (GlobalTheory.TorusCoord.val_congr g χ (mul_inv_cancel y).symm z J)).trans (val_mul_of g hG h.1 χ z J hJ)).symm
    exact ((eq_inv_of_mul_eq_one_right k).trans (congrArg (·⁻¹) (h.2 χ z J hJ))).trans (map_inv _ _).symm
end

theorem comp_one_left {S : Scheme.{0}} (B : Over S) [GrpObj B] {T T' : Over S} (ρ : T' ⟶ T) :
    ρ.left ≫ (1 : T ⟶ B).left = (1 : T' ⟶ B).left :=
  congrArg (fun q : T' ⟶ B => q.left) (MonObj.comp_one ρ)

theorem torPt_iff (U : PreU I D A G) {W : Type} [CommRing W] [Algebra R W] (a : Multiplicative D.X →* Wˣ)
    (x : TA R W ⟶ G) : U.TorPt a x ↔ ∀ (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (ρ : (Over.map (thick R I e)).obj T ⟶ TA R W) (y : T ⟶ thickObj R I e G),
      push I e G T y = ρ ≫ x → Coord (U.gt e) ρ.left a y := by
  constructor
  · intro h e T ρ y hy
    obtain ⟨h₁, h₂⟩ := h e T.left ρ.left y.left (congrArg (fun q => q.left) hy)
    refine ⟨Over.OverMorphism.ext (h₁.trans (comp_one_left D.P.A ρ)),
      fun χ z J hJ => Units.ext ((h₂ χ z J hJ).trans (gs_scal _ _ _))⟩
  · intro h e Z r xe hx
    let T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (xe ≫ (thickObj R I e G).hom)
    have hw : r ≫ (TA R W).hom = (xe ≫ (thickObj R I e G).hom) ≫ thick R I e := by
      rw [← Over.w x, ← Category.assoc, ← hx, Category.assoc, Category.assoc]
      exact congrArg (xe ≫ ·) (Over.w (fstG I e G))
    let ρ : (Over.map (thick R I e)).obj T ⟶ TA R W := Over.homMk r hw
    let y : T ⟶ thickObj R I e G := Over.homMk xe rfl
    obtain ⟨h₁, h₂⟩ := h e T ρ y (Over.OverMorphism.ext hx)
    exact ⟨(congrArg (fun q => q.left) h₁).trans (comp_one_left D.P.A ρ).symm,
      fun χ z J hJ => (congrArg Units.val (h₂ χ z J hJ)).trans (gs_scal _ _ _).symm⟩

section
variable (U : PreU I D A G) {W : Type} [CommRing W] [Algebra R W]

theorem torPt_one : U.TorPt (1 : Multiplicative D.X →* Wˣ) 1 := by
  refine (torPt_iff U _ _).2 fun e T ρ y hy => ?_
  obtain rfl : y = 1 := push_inj e T (hy.trans ((MonObj.comp_one ρ).trans (map_one _).symm))
  exact coord_one _ _

theorem torPt_mul (hG : GlobalFnsSt) {a a' : Multiplicative D.X →* Wˣ} {x x' : TA R W ⟶ G}
    (h : U.TorPt a x) (h' : U.TorPt a' x') : U.TorPt (a * a') (x * x') := by
  refine (torPt_iff U _ _).2 fun e T ρ y hy => ?_
  obtain ⟨p, hp⟩ := push_surj e T (ρ ≫ x)
  obtain ⟨p', hp'⟩ := push_surj e T (ρ ≫ x')
  obtain rfl : y = p * p' := push_inj e T (by rw [hy, map_mul, hp, hp', MonObj.comp_mul])
  exact coord_mul _ _ hG ((torPt_iff U _ _).1 h e T ρ p hp) ((torPt_iff U _ _).1 h' e T ρ p' hp')

theorem torPt_inv (hG : GlobalFnsSt) {a : Multiplicative D.X →* Wˣ} {x : TA R W ⟶ G}
    (h : U.TorPt a x) : U.TorPt a⁻¹ x⁻¹ := by
  refine (torPt_iff U _ _).2 fun e T ρ y hy => ?_
  obtain ⟨p, hp⟩ := push_surj e T (ρ ≫ x)
  obtain rfl : y = p⁻¹ := push_inj e T (by rw [hy, map_inv, hp]; exact map_inv (preHom ρ) x)
  exact coord_inv _ _ hG ((torPt_iff U _ _).1 h e T ρ p hp)

theorem torPt_pow (hG : GlobalFnsSt) {a : Multiplicative D.X →* Wˣ} {x : TA R W ⟶ G}
    (h : U.TorPt a x) (k : ℕ) : U.TorPt (a ^ k) (x ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact torPt_one U
  | succ k ih => rw [pow_succ, pow_succ]; exact torPt_mul U hG ih h
end

end GlobalTheory.UU.TorMul

theorem GlobalTheory.UU.torPt_group : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (W : Type) [CommRing W] [Algebra R W], U.TorPt (1 : Multiplicative D.X →* Wˣ) 1 ∧ ∀ (a a' : Multiplicative D.X →* Wˣ) (x x' : TA R W ⟶ G), U.TorPt a x → (U.TorPt a' x' → U.TorPt (a * a') (x * x')) ∧ U.TorPt a⁻¹ x⁻¹ ∧ ∀ k : ℕ, U.TorPt (a ^ k) (x ^ k) :=
  fun hG _ _ _ _ _ _ _ _ _ U _ _ _ => ⟨TorMul.torPt_one U, fun _ _ _ _ h =>
    ⟨fun h' => TorMul.torPt_mul U hG h h', TorMul.torPt_inv U hG h, TorMul.torPt_pow U hG h⟩⟩

end
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.FormalValue

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NormGen

theorem exists_factor {V W : Type} [CommRing V] [CommRing W] (I : Ideal V) (φ : V →+* W) (e : ℕ) {Z : Scheme.{0}}
    (r : Z ⟶ Sp W) (σ : Z ⟶ Sp (V ⧸ I ^ (e + 1))) (h : σ ≫ thick V I e = r ≫ spMap φ) :
    ∃ ρ : Z ⟶ Sp (W ⧸ I.map φ ^ (e + 1)), ρ ≫ thick W (I.map φ) e = r := by
  let ψ : CommRingCat.of W ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫ r.appTop
  have hr : Z.toSpecΓ ≫ Spec.map ψ = r := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hk : I.map φ ^ (e + 1) ≤ RingHom.ker ψ.hom := by
    rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro v hv
    have e₁ : CommRingCat.ofHom φ ≫ ψ = CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1))) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (V ⧸ I ^ (e + 1)))).inv ≫ σ.appTop := by
      rw [Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.ΓSpecIso_inv_naturality_assoc, ← Scheme.Hom.comp_appTop,
        ← Scheme.Hom.comp_appTop, h]
    have e₂ := congrArg (fun q => q.hom v) e₁
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
      Ideal.Quotient.eq_zero_iff_mem.2 hv, map_zero] at e₂
    exact e₂
  refine ⟨Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ ψ.hom hk)), ?_⟩
  rw [Category.assoc, ← Spec.map_comp, ← hr]
  rfl

theorem gs_valR {A : Type} [CommRing A] {X Z : Scheme.{0}} (ρ : Z ⟶ Sp A) (y : Sp A ⟶ X) (V : X.Opens)
    (ht : ⊤ ≤ y ⁻¹ᵁ V) (s : Γ(X, V)) (z : Z) :
    gs ρ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (valR y V s)) = gs (ρ ≫ y) z V s := by
  rw [valR, dif_pos ht, Iso.hom_inv_id_apply, ← gs_pull ρ y z V (ht trivial)]
  exact gs_res ρ z ht trivial _

theorem valR_id {A : Type} [CommRing A] (a : A) :
    valR (𝟙 (Sp A)) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) = a := by
  rw [valR, dif_pos (show ⊤ ≤ 𝟙 (Sp A) ⁻¹ᵁ ⊤ from le_top)]
  have : Scheme.Hom.appLE (𝟙 (Sp A)) ⊤ ⊤ le_top = 𝟙 _ := by
    exact (Category.id_comp _).trans ((Sp A).presheaf.map_id _)
  rw [this]
  exact Iso.inv_hom_id_apply _ _

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem exists_limit_unit (U : PreU I D A G) {W : Type} [CommRing W] [IsLocalRing W] (φ : R →+* W)
    [IsAdicComplete (I.map φ) W] (x : Sp W ⟶ G.left) (hx : x ≫ G.hom = spMap φ) (b : Sp W ⟶ D.P.A.left)
    (hb : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → xe ≫ (U.gt e).pG.left = r ≫ b)
    {jL : U.P.L.L.ι} {jM : D.P.L.ι} (hL : ⊤ ≤ x ⁻¹ᵁ U.P.L.L.U jL) (hM : ⊤ ≤ b ⁻¹ᵁ D.P.L.U jM) :
    ∃ a : Γ(Sp W, ⊤)ˣ, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, gm r z ⊤ a * gw (U.w e) xe z jM (fun _ => jL) = 1 := by
  choose y hy using exists_lift_thick I G φ x hx
  have mL : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, (fstG I e G).left (xe z) ∈ U.P.L.L.U jL := fun e Z r xe h z =>
    (congrArg (fun q => q z ∈ U.P.L.L.U jL) h).mpr (hL (show r z ∈ (⊤ : (Sp W).Opens) from trivial))
  have mM : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, (U.gt e).pG.left (xe z) ∈ D.P.L.U jM := fun e Z r xe h z =>
    (congrArg (fun q => q z ∈ D.P.L.U jM) (hb e Z r xe h)).mpr (hM (show r z ∈ (⊤ : (Sp W).Opens) from trivial))
  let O : ∀ e, (thickObj R I e G).left.Opens := fun e =>
    (D.P.L.pull (U.gt e).pG.left).U (fun _ => jM) ⊓ (U.P.L.L.pull (fstG I e G).left).U (fun _ => jL)
  let s : ∀ e, Γ((thickObj R I e G).left, O e)ˣ := fun e => (U.w e).s (fun _ => jM, fun _ => jL)
  have mO : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, xe z ∈ O e := fun e Z r xe h z =>
    ⟨mem_pull.2 (mM e Z r xe h z), mem_pull.2 (mL e Z r xe h z)⟩
  have ht : ∀ e, ⊤ ≤ y e ⁻¹ᵁ O e := fun e z _ => mO e _ _ _ (hy e) z
  have hc : ∀ e, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))
      (valR (y (e + 1)) (O (e + 1)) (s (e + 1)).val) = valR (y e) (O e) (s e).val := fun e => by
    have := isLocalRing_quotient_pow (ne_top_of_isHausdorff (I.map φ)) e
    have := fstG_mono (I := I) (G := G) (e + 1)
    have e₁ : thickTrans W (I.map φ) e ≫ y (e + 1) = y e ≫ thickMap R I e G := by
      rw [← cancel_mono (fstG I (e + 1) G).left, Category.assoc, Category.assoc, hy,
        show thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left from thickMap_comp_fGl I e G, hy,
        ← Category.assoc, thickTrans_comp]
    apply toStkA_injective
    refine (toStkA_map_valR _ _ _ _ (ht _) _).trans (Eq.trans ?_ (toStkA_valR_eq_gs _ _ _ (ht _) _).symm)
    refine (gs_unit _ _ _ (mO (e + 1) _ (thickTrans W (I.map φ) e ≫ thick W (I.map φ) (e + 1)) _ (by
      rw [Category.assoc, hy, Category.assoc]) _) _).trans (Eq.trans ?_ (gs_unit _ _ _ (mO e _ _ _ (hy e) _) _).symm)
    refine congrArg Units.val ((congrArg (fun q => gm q _ (O (e + 1)) (s (e + 1))) e₁).trans ?_)
    exact U.w_compat e _ (y e) _ jM jL (mM e _ _ _ (hy e) _) (mL e _ _ _ (hy e) _)
  obtain ⟨a, ha⟩ := exists_unit_limit (I.map φ) _ hc fun e => isUnit_valR _ _ (ht e) _
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom.toMonoidHom a, fun e Z r xe h z => ?_⟩
  obtain ⟨ρ, rfl⟩ := exists_factor I φ e r (xe ≫ (thickObj R I e G).hom) (by
    rw [← hx, ← Category.assoc r, ← h, Category.assoc, Category.assoc]
    exact congrArg (xe ≫ ·) pullback.condition.symm)
  have := fstG_mono (I := I) (G := G) e
  obtain rfl : xe = ρ ≫ y e := by
    rw [← cancel_mono (fstG I e G).left, h, Category.assoc, Category.assoc, hy]
  apply Units.ext
  have H := congrArg (fun t => gs ρ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (W ⧸ I.map φ ^ (e + 1)))).inv.hom t)) (ha e)
  simp only [map_mul, map_one] at H
  rw [gs_mul ρ z ⊤ trivial, gs_valR _ _ _ (ht e), gs_unit _ _ _ (mO e _ _ _ h z), gs_eq ρ z ⊤ trivial 1, map_one,
    map_one] at H
  refine Eq.trans (congrArg₂ (· * ·) ?_ rfl) H
  rw [← gs_unit _ z ⊤ trivial, ← gs_valR ρ (thick W (I.map φ) e) ⊤ le_top]
  refine congrArg (fun t => gs ρ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (W ⧸ I.map φ ^ (e + 1)))).inv.hom t)) ?_
  have k := valR_spMap (Ideal.Quotient.mk (I.map φ ^ (e + 1))) (𝟙 (Sp W)) ⊤ le_top
    ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom a.val)
  rw [valR_id, Category.comp_id] at k
  exact k

theorem one_pG (U : PreU I D A G) {T : Over (Spec (CommRingCat.of R))} (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ T.left)
    (oe : Z ⟶ (thickObj R I e G).left) (h : oe ≫ (fstG I e G).left = r ≫ (1 : T ⟶ G).left) :
    oe ≫ (U.gt e).pG.left = r ≫ (1 : T ⟶ D.P.A).left := by
  have hf : ∀ (H : Over (Spec (CommRingCat.of R))) [GrpObj H],
      eSec (thickObj R I e H) ≫ (fstG I e H).left = thick R I e ≫ eSec H := fun H _ => by
    show eSec (thickObj R I e H) ≫ pullback.fst H.hom (thick R I e) = _
    simp [eSec]
    rw [pullback.lift_fst, ← Category.assoc, ← pullback.condition, Category.comp_id]
  have hp : eSec (thickObj R I e G) ≫ (U.gt e).pG.left = thick R I e ≫ eSec D.P.A := by
    have := (U.gt e).q_hom
    have h : eSec (thickObj R I e G) ≫ (U.gt e).q.left = eSec (thickObj R I e D.P.A) :=
      congrArg (·.left) (IsMonHom.one_hom (U.gt e).q)
    rw [← hf D.P.A, ← h, Category.assoc]
    rfl
  have hσ : (oe ≫ (thickObj R I e G).hom) ≫ thick R I e = r ≫ T.hom := by
    rw [← Over.w (1 : T ⟶ G), ← Category.assoc r, ← h, Category.assoc, Category.assoc]
    exact congrArg (oe ≫ ·) pullback.condition.symm
  have := fstG_mono (I := I) (G := G) e
  have ho : oe = (oe ≫ (thickObj R I e G).hom) ≫ eSec (thickObj R I e G) := by
    rw [← cancel_mono (fstG I e G).left, h, Category.assoc _ (eSec _), hf, ← Category.assoc _ (thick R I e), hσ,
      one_left, Category.assoc]
  rw [ho, Category.assoc _ (eSec _), hp, ← Category.assoc _ (thick R I e), hσ, one_left, Category.assoc]

theorem gw_change (U : PreU I D A G) (e : ℕ) {Z : Scheme.{0}} (xe : Z ⟶ (thickObj R I e G).left) (z : Z)
    {p : Z ⟶ G.left} {q : Z ⟶ D.P.A.left} (hp : xe ≫ (fstG I e G).left = p) (hq : xe ≫ (U.gt e).pG.left = q)
    {j j' : D.P.L.ι} {k k' : U.P.L.L.ι} (hj : q z ∈ D.P.L.U j) (hj' : q z ∈ D.P.L.U j') (hk : p z ∈ U.P.L.L.U k)
    (hk' : p z ∈ U.P.L.L.U k') :
    gw (U.w e) xe z j (fun _ => k) =
      gm q z _ (D.P.L.g j j') * (gm p z _ (U.P.L.L.g k k'))⁻¹ * gw (U.w e) xe z j' (fun _ => k') := by
  subst hp hq
  have w := (isGen_iff _).1 (U.w_gen e) Z xe z j j' (fun _ => k) (fun _ => k') hj hj' (mem_pull.2 hk) (mem_pull.2 hk')
  rw [gm_pull_g _ _ xe z _ _ (mem_pull.2 hk) (mem_pull.2 hk')] at w
  exact w

theorem exists_normAt : AllPre fun {V} _ _ _ {D} {_} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ (a : Multiplicative D.X →* Wˣ) (x : TA V W ⟶ G), U.TorPt a x → ∃ ν, U.NormAt x ν := by
  intro V _ _ _ _ D A G _ _ U W _ _ _ hW a x hx
  have := hW.2.2.2.2
  obtain ⟨jx, hjx⟩ := exists_chart U.P.L.isLB (x.left (cpt W))
  obtain ⟨jo, hjo⟩ := exists_chart U.P.L.isLB ((1 : TA V W ⟶ G).left (cpt W))
  obtain ⟨jM, hjM⟩ := exists_chart D.P.isLB ((1 : TA V W ⟶ D.P.A).left (cpt W))
  replace hjx := (top_le_iff_cpt (A := W) x.left _).2 hjx
  replace hjo := (top_le_iff_cpt (A := W) (1 : TA V W ⟶ G).left _).2 hjo
  replace hjM := (top_le_iff_cpt (A := W) (1 : TA V W ⟶ D.P.A).left _).2 hjM
  obtain ⟨α, hα⟩ := exists_limit_unit U (algebraMap V W) x.left (Over.w x) (1 : TA V W ⟶ D.P.A).left
    (fun e Z r xe h => (hx e Z r xe h).1) hjx hjM
  obtain ⟨β, hβ⟩ := exists_limit_unit U (algebraMap V W) (1 : TA V W ⟶ G).left (Over.w _) (1 : TA V W ⟶ D.P.A).left
    (fun e Z r xe h => one_pG U (T := TA V W) e Z r xe h) hjo hjM
  obtain ⟨ν, hν⟩ := exists_gen_of_local (V := W) U.P.L.L U.P.L.isLB (K := Fin 2) ![x.left, (1 : TA V W ⟶ G).left] ![-1, 1]
  have ht : ⊤ ≤ LB.wchart U.P.L.L (K := Fin 2) ![x.left, (1 : TA V W ⟶ G).left] ![jx, jo] := fun y _ =>
    Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [hjx trivial, hjo trivial]
  obtain ⟨n, hn⟩ : ∃ n : Γ(Sp W, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JG), Good U.P.L.L z JG →
      val ν r z JG = (gm (r ≫ x.left) z _ (U.P.L.L.g (JG (r ≫ x.left)) jx))⁻¹ *
        gm (r ≫ (1 : TA V W ⟶ G).left) z _ (U.P.L.L.g (JG (r ≫ (1 : TA V W ⟶ G).left)) jo) * gm r z ⊤ n := by
    refine ⟨res (X := Sp W) ht (ν.s ![jx, jo]), fun Z r z JG hG => ?_⟩
    refine (gen_trans hν r z (hG.mem _ r) (ht trivial)).trans (congrArg₂ (· * ·) ?_ (gm_res r z ht trivial _).symm)
    rw [trF, Fin.prod_univ_two]
    exact congrArg₂ (· * ·) (zpow_neg_one _) (zpow_one _)
  refine ⟨UU.scaleGen (β * α⁻¹ * n⁻¹ : Γ(Sp W, ⊤)ˣ) ν, UU.scaleGen_isGen _ hν,
    fun e Z (r : Z ⟶ Sp W) xe oe h₁ h₂ z JG J hG hJ => ?_⟩
  have q₁ := (hx e Z r xe h₁).1
  have q₂ := one_pG U (T := TA V W) e Z r oe h₂
  have m : ∀ {X : Scheme.{0}} {f : Sp W ⟶ X} {O : X.Opens}, ⊤ ≤ f ⁻¹ᵁ O → (r ≫ f) z ∈ O := fun h => h trivial
  have a₁ := eq_inv_of_mul_eq_one_right (hα e Z r xe h₁ z)
  have a₂ := eq_inv_of_mul_eq_one_right (hβ e Z r oe h₂ z)
  have w₁ : U.wv e xe z JG J = _ := (congrArg₂ (fun j k => gw (U.w e) xe z (J j) (fun _ => JG k)) q₁ h₁).trans
    (gw_change U e xe z h₁ q₁ (hJ _) (m hjM) (hG _) (m hjx))
  have w₂ : U.wv e oe z JG J = _ := (congrArg₂ (fun j k => gw (U.w e) oe z (J j) (fun _ => JG k)) q₂ h₂).trans
    (gw_change U e oe z h₂ q₂ (hJ _) (m hjM) (hG _) (m hjo))
  rw [a₁] at w₁
  rw [a₂] at w₂
  have v := val_scaleGen (β * α⁻¹ * n⁻¹) ν r hG
  rw [hn Z r z JG hG, map_mul, map_mul, map_inv, map_inv] at v
  refine (congrArg₂ (· * ·) v w₂).trans (Eq.trans ?_ w₁.symm)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.NormGen
end
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.ShiftExp

theorem sval_secScale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (DVR.SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·) (gs_res r z le_top (hJ.mem _ r) _) rfl)

theorem gs_scal {Y Z : Scheme.{0}} {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z)
    (c : R) : gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := by
  calc gs r z ⊤ (scal p c) = gs (𝟙 _ ≫ r) z ⊤ (scal p c) := by rw [Category.id_comp]
    _ = gs (𝟙 _) z (r ⁻¹ᵁ ⊤) ((r.app ⊤).hom (scal p c)) := (gs_pull (𝟙 _) r z ⊤ (by trivial) _).symm
    _ = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := rfl

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem shift (hG : GlobalFnsSt) (U : PreU I D A G) {W : Type} [CommRing W] [Algebra R W]
    (a : Multiplicative D.X →* Wˣ) (x : TA R W ⟶ G) (hx : U.TorPt a x) (e : ℕ) (Z : Scheme.{0})
    (y y' : Z ⟶ (thickObj R I e G).left) (rG : Z ⟶ (TA R W ⊗ G).left)
    (h₁ : rG ≫ (snd _ G).left = y ≫ (fstG I e G).left)
    (h₂ : y' ≫ (fstG I e G).left = rG ≫ (translPt G x).left) :
    y' ≫ (U.gt e).pG.left = y ≫ (U.gt e).pG.left ∧ ∀ (χ : D.X) (z : Z) (J), Good D.P.L z J →
      (val ((U.gt e).t χ) y' z J).val =
        gs (𝟙 Z) z ⊤ (scal (R := W) (rG ≫ (fst (TA R W) G).left) (a (Multiplicative.ofAdd χ)).val) *
          (val ((U.gt e).t χ) y z J).val := by
  let T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (y ≫ (thickObj R I e G).hom)
  let yo : T ⟶ thickObj R I e G := Over.homMk y rfl
  have hb : rG ≫ (TA R W ⊗ G).hom = T.hom ≫ thick R I e := by
    rw [← Over.w (snd (TA R W) G), ← Category.assoc, h₁, Category.assoc, Over.w (fstG I e G)]
    exact (Category.assoc _ _ _).symm
  let ro : Over.mk (T.hom ≫ thick R I e) ⟶ TA R W ⊗ G := Over.homMk rG hb
  let x₀ : Over.mk (T.hom ≫ thick R I e) ⟶ G := ro ≫ fst _ _ ≫ x
  let xe : T ⟶ thickObj R I e G :=
    Over.homMk (pullback.lift x₀.left T.hom (Over.w x₀)) (pullback.lift_snd _ _ _)
  have hxe : xe.left ≫ pullback.fst G.hom (thick R I e) = x₀.left := pullback.lift_fst _ _ _
  have hm := (isGrpPullback_pullback G (thick R I e)).2 T xe yo x₀ (ro ≫ snd _ _) hxe.symm h₁
  have ht : ro ≫ translPt G x = x₀ * (ro ≫ snd _ _) := MonObj.comp_mul ro (fst _ _ ≫ x) (snd _ _)
  have hf : y' ≫ pullback.fst G.hom (thick R I e) = (xe * yo).left ≫ pullback.fst G.hom (thick R I e) :=
    h₂.trans ((congrArg (fun q => q.left) ht).trans hm)
  haveI : Mono (thick R I e) := by
    haveI : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  have hy : y' = (xe * yo).left := (cancel_mono (pullback.fst G.hom (thick R I e))).1 hf
  obtain ⟨p₁, p₂⟩ := hx e Z (rG ≫ (fst (TA R W) G).left) xe.left (hxe.trans (Category.assoc _ _ _).symm)
  have hone : GlobalTheory.TorusCoord.im (U.gt e) xe = 1 := by
    have : (ro ≫ fst _ _) ≫ (1 : TA R W ⟶ D.P.A) = 1 := MonObj.comp_one _
    exact (Over.OverMorphism.ext p₁).trans this
  subst hy
  refine ⟨?_, fun χ z J hJ => ?_⟩
  · have := GlobalTheory.TorusCoord.im_mul (U.gt e) xe yo
    rw [hone, _root_.one_mul] at this
    exact congrArg (fun q => q.left) this
  · have k := GlobalTheory.TorusCoord.val_t_mul_points (U.gt e) hG χ xe yo z J hJ
    have c : GlobalTheory.TorusCoord.cubeVal (U.gt e) χ z J xe yo = 1 := by
      unfold GlobalTheory.TorusCoord.cubeVal
      rw [hone]
      exact (isCub_cubV D.cub (T := (Over.map (thick R I e)).obj T) hJ).face₂ _ _
    rw [c, _root_.mul_one] at k
    exact (congrArg Units.val k).trans ((Units.val_mul _ _).trans (congrArg (· * _) (p₂ χ z J hJ)))

end GlobalTheory.UU.ShiftExp

theorem GlobalTheory.UU.expansion_translate_torus : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (W : Type) [CommRing W] [Algebra R W] (a : Multiplicative D.X →* Wˣ) (x : TA R W ⟶ G), U.TorPt a x → ∀ (k : ℕ) (σ : U.SecGT (TA R W) k) (f : ∀ α, SecBT D (TA R W) k α), U.ExpT (TA R W) k σ f → ∀ e : ℕ, ∃ s : Finset D.X, ∀ (Z : Scheme.{0}) (y y' : Z ⟶ (thickObj R I e G).left) (rG : Z ⟶ (TA R W ⊗ G).left) (rB : Z ⟶ (TA R W ⊗ D.P.A).left), rG ≫ (snd _ G).left = y ≫ (fstG I e G).left → rB ≫ (snd _ D.P.A).left = y ≫ (U.gt e).pG.left → rB ≫ (fst _ D.P.A).left = rG ≫ (fst _ G).left → y' ≫ (fstG I e G).left = rG ≫ (translPt G x).left → ∀ (z : Z) (JG) (J), Good U.P.L.L z JG → Good D.P.L z J → (∀ α ∉ s, sval (twist a f α) rB z J = 0) ∧ (U.wv e y' z JG J).val ^ k * sval σ (rG ≫ (translT G x).left) z JG = ∑ α ∈ s, sval (twist a f α) rB z J * (val ((U.gt e).t α) y z J).val := by
  intro hG R _ _ I D A G _ _ U W _ _ a x hx k σ f hf e
  obtain ⟨s, hs⟩ := hf e
  refine ⟨s, fun Z y y' rG rB h₁ h₂ h₃ h₄ z JG J hJG hJ => ?_⟩
  obtain ⟨p₁, p₂⟩ := ShiftExp.shift hG U a x hx e Z y y' rG h₁ h₄
  have e₁ : (translT G x).left ≫ (snd (TA R W) G).left = (translPt G x).left :=
    congrArg (fun q => q.left) (lift_snd (fst (TA R W) G) (translPt G x))
  have e₂ : (translT G x).left ≫ (fst (TA R W) G).left = (fst (TA R W) G).left :=
    congrArg (fun q => q.left) (lift_fst (fst (TA R W) G) (translPt G x))
  obtain ⟨q₁, q₂⟩ := hs Z y' (rG ≫ (translT G x).left) rB (by rw [Category.assoc, e₁, h₄]) (h₂.trans p₁.symm)
    (by rw [Category.assoc, e₂, h₃]) z JG J hJG hJ
  have tw : ∀ α, sval (twist a f α) rB z J =
      gs (𝟙 Z) z ⊤ (scal (R := W) (rG ≫ (fst (TA R W) G).left) (a (Multiplicative.ofAdd α)).val) *
        sval (f α) rB z J := fun α => by
    rw [← h₃]
    exact (ShiftExp.sval_secScale _ _ rB z hJ).trans (congrArg (· * _) (ShiftExp.gs_scal _ rB z _))
  refine ⟨fun α hα => by rw [tw, q₁ α hα, mul_zero], q₂.trans (Finset.sum_congr rfl fun α _ => ?_)⟩
  rw [tw, p₂ α z J hJ]
  ring
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.ProdTransl

theorem comp_inv_pow {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {T T' : Over S} (ρ : T' ⟶ T) (x : T ⟶ G)
    (k : ℕ) : ρ ≫ (x ^ k)⁻¹ = ((ρ ≫ x) ^ k)⁻¹ :=
  (map_inv (preHom (G := G) ρ) (x ^ k)).trans (congrArg (·⁻¹) (map_pow (preHom (G := G) ρ) x k))

theorem value_identity {A A' B O : Type} [CommGroup A] [CommGroup A'] [CommGroup B] [CommRing O] (Θ : B → B → B → Oˣ)
    (θ' : A' → A' → A' → Oˣ) (p : A →* B) (q : A →* A') (W : A → Oˣ) (hc : IsCub θ')
    (h : ∀ x y u, θ' (q x) (q y) (q u) * W (x * y) * W (x * u) * W (y * u) * W 1 =
      W (x * y * u) * W x * W y * W u * Θ (p x) (p y) (p u)) (k : ℕ) (x y : A) (hx : q x = 1) (X Y : B) (hX : X = p x)
    (hY : Y = p y) (n n' : Oˣ) (hn : n * W 1 = W x) (hn' : n' * W 1 = W (x ^ k)⁻¹) (s s' t : O)
    (ht : t = (cubN Θ k 1 X Y * Θ Y (X ^ k) (X ^ k)⁻¹ * (n ^ k * n')).val * (s * s')) :
    (W y).val ^ (k + 1) * t = (W (x * y)).val ^ k * s * ((W ((x ^ k)⁻¹ * y)).val ^ 1 * s') := by
  have e := cubN_descent_opposite A A' Oˣ (fun a b c => Θ (p a) (p b) (p c)) θ' q W hc h k x y hx
  have c : cubN (fun a b c => Θ (p a) (p b) (p c)) k 1 x y = cubN Θ k 1 (p x) (p y) := by
    simp only [cubN, map_mul, map_one, map_pow]
  rw [c, map_inv, map_pow, ← hX, ← hY, ← hn, ← hn', mul_comm y, mul_pow] at e
  have e' : W y ^ (k + 1) * (cubN Θ k 1 X Y * Θ Y (X ^ k) (X ^ k)⁻¹ * (n ^ k * n')) =
      W (x * y) ^ k * W ((x ^ k)⁻¹ * y) := by
    apply mul_right_cancel (b := W 1 ^ (k + 1))
    rw [← e, pow_succ (W 1)]
    generalize W y ^ (k + 1) = u₁
    generalize W 1 ^ k = u₂
    generalize n ^ k = u₃
    apply Additive.ofMul.injective
    simp only [ofMul_mul]
    abel
  have e'' := congrArg Units.val e'
  rw [Units.val_mul, Units.val_mul (W (x * y) ^ k), Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at e''
  rw [ht, ← _root_.mul_assoc, e'']
  ring

theorem exists_prod {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)
    {T : Over S} (x : T ⟶ G) (k : ℕ)
    (σ : LB.Sec (LB.LinComb L.L (K := Fin 1) (fun _ => (snd T G).left) (fun _ => (k : ℤ))))
    (ϑ : LB.Sec (LB.LinComb L.L (K := Fin 1) (fun _ => (snd T G).left) (fun _ => ((1 : ℕ) : ℤ))))
    (ν : LB.Gen (LB.LinComb L.L (K := Fin 2) ![x.left, (1 : T ⟶ G).left] ![-1, 1])) (hν : ν.IsGen)
    (ν' : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(x ^ k)⁻¹.left, (1 : T ⟶ G).left] ![-1, 1])) (hν' : ν'.IsGen) :
    ∃ τ : LB.Sec (LB.LinComb L.L (K := Fin 1) (fun _ => (snd T G).left) (fun _ => ((k + 1 : ℕ) : ℤ))),
      ∀ (T' : Over S) (ρ : T' ⟶ T ⊗ G) (z : T'.left) (J), Good L.L z J →
        sval τ ρ.left z J =
          (cubN (cubV c z J) k 1 (ρ ≫ fst T G ≫ x) (ρ ≫ snd T G) *
            cubV c z J (ρ ≫ snd T G) ((ρ ≫ fst T G ≫ x) ^ k) ((ρ ≫ fst T G ≫ x) ^ k)⁻¹ *
            (val ν (ρ.left ≫ (fst T G).left) z J ^ k * val ν' (ρ.left ≫ (fst T G).left) z J)).val *
          (sval σ (ρ.left ≫ (translT G x).left) z J * sval ϑ (ρ.left ≫ (translT G (x ^ k)⁻¹).left) z J) := by
  obtain ⟨t, ht, hv⟩ := exists_cubN c (1 : T ⊗ G ⟶ G) (fst T G ≫ x) (snd T G) k
  have hX : ∀ {T' : Over S} (ρ : T' ⟶ T), ρ ≫ (x ^ k)⁻¹ = ((ρ ≫ x) ^ k)⁻¹ := fun ρ => comp_inv_pow ρ x k
  have e₁ : ∀ u : T ⟶ G, (translT G u).left ≫ (snd T G).left = ((fst T G ≫ u) * snd T G).left := fun u =>
    congrArg (fun q => q.left) (lift_snd (fst T G) (translPt G u))
  have e₂ : (fst T G).left ≫ (1 : T ⟶ G).left = (1 : T ⊗ G ⟶ G).left :=
    congrArg (fun q => q.left) (MonObj.comp_one (M := G) (fst T G) : fst T G ≫ (1 : T ⟶ G) = 1)
  have e₃ : (fst T G).left ≫ (x ^ k)⁻¹.left = ((fst T G ≫ x) ^ k)⁻¹.left := congrArg (fun q => q.left) (hX (fst T G))
  have e₄ : (fst T G).left ≫ x.left = (fst T G ≫ x).left := rfl
  have hu : (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ t (LB.pullGen L.L (thφ G (x3 G)) thε c.t
      (lift (snd T G) (lift ((fst T G ≫ x) ^ k) ((fst T G ≫ x) ^ k)⁻¹)).left))
      (LB.mulGen L.L _ _ _ _ (GeneratorPullback.powGen L.L _ _ (LB.pullGen L.L _ _ ν (fst T G).left) k)
        (LB.pullGen L.L _ _ ν' (fst T G).left))).IsGen :=
    DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.pullGen_isGen _ _ _ _ c.isGen _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hν _) k)
        (DVR.pullGen_isGen _ _ _ _ hν' _))
  obtain ⟨τ, hτ⟩ := exists_sec L.isLB (φ' := fun _ : Fin 1 => (snd T G).left) (ε' := fun _ => ((k + 1 : ℕ) : ℤ))
    (fun U _ h => by
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·)
        ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·)
          ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) rfl
            (prod_cub (snd T G) ((fst T G ≫ x) ^ k) ((fst T G ≫ x) ^ k)⁻¹ h)))
          (Fintype.prod_sum_type _))) (Fintype.prod_sum_type _))).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, e₁, e₂, e₃, e₄, hX, _root_.one_mul, mul_inv_cancel, mul_inv_cancel_right]
      rw [mul_comm (snd T G) ((fst T G ≫ x) ^ k), mul_comm (snd T G) ((fst T G ≫ x) ^ k)⁻¹]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
      push_cast
      module)
    (H1.SectionArithmetic.mulSec (genSec _ hu) (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.pullSec σ (translT G x).left)
      (H1.SectionArithmetic.pullSec ϑ (translT G (x ^ k)⁻¹).left)))
  refine ⟨τ, fun T' ρ z J hJ => (hτ _ _ z J hJ).trans ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
    ((sval_genSec _ hu _ z hJ).trans (congrArg Units.val ?_))
    ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·) (H1.SectionArithmetic.sval_pullSec _ _ _ z hJ)
      (H1.SectionArithmetic.sval_pullSec _ _ _ z hJ)))))⟩
  refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((hv T' ρ z J hJ).trans ?_) ((val_cub c ρ hJ _ _ _).trans ?_)))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((map_pow _ _ _).trans (congrArg (· ^ k) (val_pull hJ _ _ _)))
      (val_pull hJ _ _ _))))
  · rw [MonObj.comp_one]
  · have a : ρ ≫ (fst T G ≫ x) ^ k = (ρ ≫ fst T G ≫ x) ^ k := map_pow (preHom (G := G) ρ) _ _
    have b : ρ ≫ ((fst T G ≫ x) ^ k)⁻¹ = (ρ ≫ (fst T G ≫ x) ^ k)⁻¹ := map_inv (preHom (G := G) ρ) _
    rw [b, a]

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

noncomputable def push (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ G) :=
  MonoidHom.mk' (fun u => (Over.map (thick R I e)).map u ≫ fstG I e G) fun a b =>
    Over.OverMorphism.ext ((isGrpPullback_pullback G (thick R I e)).2 T a b _ _ rfl rfl).symm

theorem prodExp_of_normAt (hG : GlobalFnsSt) (U : PreU I D A G) {W : Type} [CommRing W] [Algebra R W]
    (a a' : Multiplicative D.X →* Wˣ) (x : TA R W ⟶ G) (k : ℕ) (hx : U.TorPt a x) (hx' : U.TorPt a' (x ^ k)⁻¹)
    (ν) (hν : U.NormAt x ν) (ν') (hν' : U.NormAt (x ^ k)⁻¹ ν')
    (σ : U.SecGT (TA R W) k) (ϑ : U.SecGT (TA R W) 1) (f) (g) (hf : U.ExpT (TA R W) k σ f)
    (hg : U.ExpT (TA R W) 1 ϑ g) :
    ∃ τ : U.SecGT (TA R W) (k + 1), U.ProdExp (TA R W) (twist a f) (twist a' g) τ := by
  obtain ⟨τ, hτ⟩ := exists_prod U.P.c x k σ ϑ ν hν.1 ν' hν'.1
  refine ⟨τ, fun e => ?_⟩
  obtain ⟨s, hs⟩ := expansion_translate_torus hG R I D A G U W a x hx k σ f hf e
  obtain ⟨s', hs'⟩ := expansion_translate_torus hG R I D A G U W a' _ hx' 1 ϑ g hg e
  refine ⟨s, s', fun Z y rG rB h₁ h₂ h₃ z JG J hJG hJ => ?_⟩
  let T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (y ≫ (thickObj R I e G).hom)
  let yo : T ⟶ thickObj R I e G := Over.homMk y rfl
  have hb : rG ≫ (TA R W ⊗ G).hom = T.hom ≫ thick R I e := by
    rw [← Over.w (snd (TA R W) G), ← Category.assoc, h₁, Category.assoc, Over.w (fstG I e G)]
    exact (Category.assoc _ _ _).symm
  let ρ : (Over.map (thick R I e)).obj T ⟶ TA R W ⊗ G := Over.homMk rG hb
  let x₀ : (Over.map (thick R I e)).obj T ⟶ G := ρ ≫ fst _ _ ≫ x
  let xe : T ⟶ thickObj R I e G :=
    Over.homMk (pullback.lift x₀.left T.hom (Over.w x₀)) (pullback.lift_snd _ _ _)
  have hxl : xe.left ≫ pullback.fst G.hom (thick R I e) = x₀.left := pullback.lift_fst _ _ _
  have hxe : ρ ≫ fst _ _ ≫ x = push I e G T xe := Over.OverMorphism.ext hxl.symm
  have hy : ρ ≫ snd _ _ = push I e G T yo := Over.OverMorphism.ext h₁
  have hxe' : ρ ≫ fst _ _ ≫ (x ^ k)⁻¹ = push I e G T (xe ^ k)⁻¹ := by
    rw [map_inv, map_pow, ← hxe, ← Category.assoc, ← Category.assoc]
    exact comp_inv_pow _ x k
  have tr : ∀ (u : TA R W ⟶ G) (ue : T ⟶ thickObj R I e G), ρ ≫ fst _ _ ≫ u = push I e G T ue →
      (ue * yo).left ≫ (fstG I e G).left = rG ≫ (translPt G u).left := fun u ue hu =>
    congrArg (fun q => q.left) ((map_mul (push I e G T) ue yo).trans
      ((congrArg₂ (· * ·) hu.symm hy.symm).trans (MonObj.comp_mul ρ (fst _ _ ≫ u) (snd _ _)).symm))
  have pt : ∀ (u : TA R W ⟶ G) (ue : T ⟶ thickObj R I e G), ρ ≫ fst _ _ ≫ u = push I e G T ue →
      ue.left ≫ (fstG I e G).left = (rG ≫ (fst (TA R W) G).left) ≫ u.left := fun u ue hu =>
    (congrArg (fun q => q.left) hu.symm).trans (Category.assoc _ _ _).symm
  have h1 : ρ ≫ fst _ _ ≫ (1 : TA R W ⟶ G) = push I e G T 1 := by
    rw [map_one, MonObj.comp_one, MonObj.comp_one]
  have hq : GlobalTheory.TorusCoord.im (U.gt e) xe = 1 := by
    have : (ρ ≫ fst _ _) ≫ (1 : TA R W ⟶ D.P.A) = 1 := MonObj.comp_one _
    exact (Over.OverMorphism.ext (hx e Z (rG ≫ (fst (TA R W) G).left) xe.left (pt x xe hxe)).1).trans this
  obtain ⟨a₁, a₂⟩ := hs Z y (xe * yo).left rG rB h₁ h₂ h₃ (tr x xe hxe) z JG J hJG hJ
  obtain ⟨b₁, b₂⟩ := hs' Z y ((xe ^ k)⁻¹ * yo).left rG rB h₁ h₂ h₃ (tr _ _ hxe') z JG J hJG hJ
  refine ⟨a₁, b₁, Eq.trans ?_ (congrArg₂ (· * ·) a₂ b₂)⟩
  exact value_identity (O := Z.presheaf.stalk z) (cubV U.P.c (T := (Over.map (thick R I e)).obj T) z JG)
    (cubV D.cub (T := (Over.map (thick R I e)).obj T) z J) (push I e G T)
    (MonoidHom.mk' (fun u : T ⟶ thickObj R I e G => GlobalTheory.TorusCoord.im (U.gt e) u) (GlobalTheory.TorusCoord.im_mul (U.gt e)))
    (fun u => U.wv e u.left z JG J) (isCub_cubV D.cub (T := (Over.map (thick R I e)).obj T) hJ)
    (U.w_vals e T z JG J hJG hJ (fun u => U.wv e u.left z JG J) (fun _ => rfl)).2.2 k xe yo hq _ _ hxe hy _ _
    (hν.2 e Z (rG ≫ (fst (TA R W) G).left) xe.left (1 : T ⟶ thickObj R I e G).left (pt x xe hxe) (pt 1 1 h1)
      z JG J hJG hJ)
    (hν'.2 e Z (rG ≫ (fst (TA R W) G).left) (xe ^ k)⁻¹.left (1 : T ⟶ thickObj R I e G).left (pt _ _ hxe') (pt 1 1 h1)
      z JG J hJG hJ) _ _ _ (hτ _ ρ z JG hJG)

end GlobalTheory.UU.ProdTransl

theorem GlobalTheory.UU.prodExp_opposite_translates : GlobalFnsSt → AllPre fun {V} _ _ _ {D} {_} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ (a : Multiplicative D.X →* Wˣ) (x : TA V W ⟶ G), U.TorPt a x → ∀ (k : ℕ) (σ : U.SecGT (TA V W) k) (ϑ : U.SecGT (TA V W) 1) (f) (g), U.ExpT (TA V W) k σ f → U.ExpT (TA V W) 1 ϑ g → ∃ σ'' : U.SecGT (TA V W) (k + 1), U.ProdExp (TA V W) (twist a f) (twist (a ^ k)⁻¹ g) σ'' := by
  intro hG V _ _ _ hV D A G _ _ U W _ _ _ hW a x hx k σ ϑ f g hf hg
  have hm := (GlobalTheory.UU.torPt_group hG V _ D A G U W).2
  have hx' : U.TorPt (a ^ k)⁻¹ (x ^ k)⁻¹ := (hm _ a _ x ((hm a a x x hx).2.2 k)).2.1
  obtain ⟨ν, hν⟩ := GlobalTheory.NormGen.exists_normAt V hV D A G U W hW a x hx
  obtain ⟨ν', hν'⟩ := GlobalTheory.NormGen.exists_normAt V hV D A G U W hW _ _ hx'
  exact ProdTransl.prodExp_of_normAt hG U a _ x k hx hx' ν hν ν' hν' σ ϑ f g hf hg
end
