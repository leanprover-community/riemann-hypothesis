import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsBaseChangeGroup
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfFin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BaseChangePointsCompat
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatDesc
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDenominatorBtOrder
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsHenselianFlatOverPrime
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqOfLe
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularAtBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFinOpenSubBaseChange
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfInd

section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

noncomputable section

namespace PositivityTheory.HtPt.Htat.ValuationInjectivePi

section Alg

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R']

lemma tensor_frac_form (u : R' ⊗[R] FractionRing R) :
    ∃ (r : R') (d : R), d ≠ 0 ∧ u = r ⊗ₜ[R] (algebraMap R (FractionRing R) d)⁻¹ := by
  have hne : ∀ d : R, d ≠ 0 → algebraMap R (FractionRing R) d ≠ 0 := fun d hd => by
    simpa using hd
  induction u using TensorProduct.induction_on with
  | zero => exact ⟨0, 1, one_ne_zero, by simp⟩
  | tmul r k =>
    obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := R) k
    refine ⟨a • r, d, nonZeroDivisors.ne_zero hd, ?_⟩
    rw [TensorProduct.smul_tmul, div_eq_mul_inv, Algebra.smul_def]
  | add x y hx hy =>
    obtain ⟨r₁, d₁, h₁, rfl⟩ := hx
    obtain ⟨r₂, d₂, h₂, rfl⟩ := hy
    refine ⟨d₂ • r₁ + d₁ • r₂, d₁ * d₂, mul_ne_zero h₁ h₂, ?_⟩
    have i₁ := hne d₁ h₁
    have i₂ := hne d₂ h₂
    rw [TensorProduct.add_tmul, TensorProduct.smul_tmul, TensorProduct.smul_tmul]
    congr 2 <;> (simp only [Algebra.smul_def, map_mul]; field_simp)

def kapL (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R')) :
    FractionRing R →ₗ[R] FractionRing R' where
  toFun := κ
  map_add' := map_add κ
  map_smul' r x := by
    have := congr($hκ r)
    simp only [RingHom.comp_apply] at this
    simp only [Algebra.smul_def, map_mul, RingHom.id_apply, this,
      IsScalarTower.algebraMap_apply R R' (FractionRing R')]

lemma inj_one (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R')) :
    Function.Injective ((kapL κ hκ).liftBaseChange R') := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  obtain ⟨r, d, hd, rfl⟩ := tensor_frac_form u
  rw [LinearMap.liftBaseChange_tmul] at hu
  have h1 : algebraMap R (FractionRing R) d ≠ 0 := by simpa using hd
  have h2 : κ (algebraMap R (FractionRing R) d)⁻¹ ≠ 0 :=
    (map_ne_zero κ).2 (inv_ne_zero h1)
  have h3 : r = 0 := by
    have h4 : algebraMap R' (FractionRing R') r * κ (algebraMap R (FractionRing R) d)⁻¹ = 0 := by
      rw [← Algebra.smul_def]; exact hu
    have := (mul_eq_zero.1 h4).resolve_right h2
    simpa using this
  simp [h3]

lemma inj_pi {T : Type} [Fintype T] [DecidableEq T] (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R')) :
    Function.Injective (((kapL κ hκ).compLeft T).liftBaseChange R') := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  have key : ∀ (y : R' ⊗[R] (T → FractionRing R)) (h : T),
      (kapL κ hκ).liftBaseChange R' (TensorProduct.piRight R R' R' (fun _ : T => FractionRing R) y h) =
        (((kapL κ hκ).compLeft T).liftBaseChange R' y) h := by
    intro y h
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r f => simp [TensorProduct.piRight_apply, LinearMap.liftBaseChange_tmul]
    | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]
  apply (TensorProduct.piRight R R' R' (fun _ : T => FractionRing R)).injective
  rw [map_zero]
  funext h
  apply inj_one κ hκ
  rw [key, hy]
  simp

lemma tensor_pi_ext {T Q : Type} [Fintype T] [DecidableEq T] [AddCommGroup Q] [Module R Q]
    (y : R' ⊗[R] (T → Q)) (h : ∀ t, (LinearMap.proj t : (T → Q) →ₗ[R] Q).lTensor R' y = 0) : y = 0 := by
  have key : ∀ (y : R' ⊗[R] (T → Q)) (t : T),
      TensorProduct.piRight R R' R' (fun _ : T => Q) y t =
        (LinearMap.proj t : (T → Q) →ₗ[R] Q).lTensor R' y := by
    intro y t
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r f => simp [TensorProduct.piRight_apply]
    | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]
  apply (TensorProduct.piRight R R' R' (fun _ : T => Q)).injective
  rw [map_zero]
  funext t
  rw [key, h]
  rfl

theorem alg_core {T : Type} [CommGroup T] [Finite T] [Module.Flat R R']
    (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R'))
    (N : Submodule R (T → FractionRing R)) (M : Submodule R (T → R))
    (hM : ∀ f, f ∈ M ↔ ∀ t, (fun h => algebraMap R (FractionRing R) (f (t * h))) ∈ N)
    (g : T → R')
    (hg : ∀ t, (fun h => algebraMap R' (FractionRing R') (g (t * h))) ∈
      Submodule.span R' {w : T → FractionRing R' | ∃ n ∈ N, w = fun h => κ (n h)}) :
    g ∈ Submodule.span R' {g : T → R' | ∃ f ∈ M, g = fun t => algebraMap R R' (f t)} := by
  classical
  cases nonempty_fintype T
  let a : T → ((T → R) →ₗ[R] (T → FractionRing R)) := fun t =>
    ((Algebra.linearMap R (FractionRing R)).compLeft T) ∘ₗ (LinearMap.funLeft R R (fun h => t * h))
  have ha : ∀ t f h, a t f h = algebraMap R (FractionRing R) (f (t * h)) := fun _ _ _ => rfl
  let b : (T → R) →ₗ[R] (T → (T → FractionRing R) ⧸ N) := LinearMap.pi fun t => N.mkQ ∘ₗ a t
  have hex : Function.Exact M.subtype b := by
    intro f
    constructor
    · intro hf
      have hfM : f ∈ M := (hM f).2 fun t => by
        have h1 : N.mkQ (a t f) = 0 := congrFun hf t
        exact (Submodule.Quotient.mk_eq_zero N).1 h1
      exact ⟨⟨f, hfM⟩, rfl⟩
    · rintro ⟨m, rfl⟩
      funext t
      exact (Submodule.Quotient.mk_eq_zero N).2 ((hM _).1 m.2 t)
  have hexS := Module.Flat.lTensor_exact R' hex
  have hexN := Module.Flat.lTensor_exact R' (LinearMap.exact_subtype_mkQ N)
  let z : R' ⊗[R] (T → R) := ∑ h, g h ⊗ₜ[R] (Pi.single h 1 : T → R)
  let cW := ((kapL κ hκ).compLeft T).liftBaseChange R'
  have hc : ∀ t, cW ((a t).lTensor R' z) =
      fun h => algebraMap R' (FractionRing R') (g (t * h)) := by
    intro t
    funext h
    simp only [z, map_sum, LinearMap.lTensor_tmul, cW, LinearMap.liftBaseChange_tmul, Finset.sum_apply,
      Pi.smul_apply]
    rw [Finset.sum_eq_single (t * h)]
    · have := congr($hκ 1)
      simp [LinearMap.compLeft_apply, ha, kapL, Algebra.smul_def]
    · intro b' _ hb'
      simp [LinearMap.compLeft_apply, ha, kapL, Ne.symm hb']
    · simp
  have hN : ∀ t, ∃ y : R' ⊗[R] N, cW (N.subtype.lTensor R' y) =
      fun h => algebraMap R' (FractionRing R') (g (t * h)) := by
    intro t
    let cN := (((kapL κ hκ).compLeft T) ∘ₗ N.subtype).liftBaseChange R'
    have e1 : ∀ y, cN y = cW (N.subtype.lTensor R' y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r n => simp [cN, cW, LinearMap.liftBaseChange_tmul]
      | add p q hp hq => simp only [map_add, hp, hq]
    have hle : Submodule.span R' {w : T → FractionRing R' | ∃ n ∈ N, w = fun h => κ (n h)} ≤
        LinearMap.range cN := by
      rw [Submodule.span_le]
      rintro _ ⟨n, hn, rfl⟩
      refine ⟨(1 : R') ⊗ₜ[R] (⟨n, hn⟩ : N), ?_⟩
      simp only [cN, LinearMap.liftBaseChange_tmul, one_smul]
      rfl
    obtain ⟨y, hy⟩ := hle (hg t)
    exact ⟨y, by rw [← e1, hy]⟩
  have hz : b.lTensor R' z = 0 := by
    apply tensor_pi_ext
    intro t
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    have e2 : (LinearMap.proj t : (T → (T → FractionRing R) ⧸ N) →ₗ[R] _) ∘ₗ b = N.mkQ ∘ₗ a t := rfl
    rw [e2, LinearMap.lTensor_comp, LinearMap.comp_apply]
    obtain ⟨y, hy⟩ := hN t
    have e3 : (a t).lTensor R' z = N.subtype.lTensor R' y :=
      inj_pi κ hκ ((hc t).trans hy.symm)
    rw [e3]
    exact (hexN _).2 ⟨y, rfl⟩
  obtain ⟨y, hy⟩ := (hexS z).1 hz
  let e := ((Algebra.linearMap R R').compLeft T).liftBaseChange R'
  have hez : e z = g := by
    funext h
    simp only [z, e, map_sum, LinearMap.liftBaseChange_tmul, Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single h]
    · simp [LinearMap.compLeft_apply]
    · intro b' _ hb'
      simp [LinearMap.compLeft_apply, Ne.symm hb']
    · simp
  have hall : ∀ y : R' ⊗[R] M, e (M.subtype.lTensor R' y) ∈
      Submodule.span R' {g : T → R' | ∃ f ∈ M, g = fun t => algebraMap R R' (f t)} := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      simp only [LinearMap.lTensor_tmul, e, LinearMap.liftBaseChange_tmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, m.2, rfl⟩)
    | add p q hp hq =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hp hq
  rw [← hez, ← hy]
  exact hall y

end Alg

section Sch

lemma top_le_pre {X Y : Scheme.{0}} (x : X ⟶ Y) : (⊤ : X.Opens) ≤ x ⁻¹ᵁ ⊤ := by simp

lemma valAt_congr {B : Type} [CommRing B] {X : Scheme.{0}} {x y : Spec (CommRingCat.of B) ⟶ X} (e : x = y)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ U) (s : Γ(X, U)) : valAt x U h s = valAt y U h' s := by
  subst e; rfl

lemma valAt_add {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (s s' : Γ(X, U)) :
    valAt x U h (s + s') = valAt x U h s + valAt x U h s' := by
  simp [valAt]

lemma valAt_mul {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (s s' : Γ(X, U)) :
    valAt x U h (s * s') = valAt x U h s * valAt x U h s' := by
  simp [valAt]

lemma valAt_zero {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : valAt x U h 0 = 0 := by
  simp [valAt]

lemma valAt_comp {B : Type} [CommRing B] {X Y : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ Y) (f : Y ⟶ X)
    (U : X.Opens) (V : Y.Opens) (hV : V ≤ f ⁻¹ᵁ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt (x ≫ f) U h' s = valAt x V h ((f.appLE U V hV).hom s) := by
  simp only [valAt]
  rw [← Scheme.Hom.appLE_comp_appLE x f U V ⊤ hV h]
  rfl

lemma valAt_spec {A B : Type} [CommRing A] [CommRing B] (κ : A →+* B)
    (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ)) ⁻¹ᵁ ⊤) (c : Γ(Spec (CommRingCat.of A), ⊤)) :
    valAt (Spec.map (CommRingCat.ofHom κ)) ⊤ h c = κ ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom c) := by
  have e : (Spec.map (CommRingCat.ofHom κ)).appLE ⊤ ⊤ h = (Spec.map (CommRingCat.ofHom κ)).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  simp only [valAt]
  rw [e]
  have := congr(($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom κ))).hom c)
  exact this

lemma valAt_map {A B : Type} [CommRing A] [CommRing B] (κ : A →+* B) {X : Scheme.{0}}
    (y : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U)
    (h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ y) ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt (Spec.map (CommRingCat.ofHom κ) ≫ y) U h' s = κ (valAt y U h s) := by
  rw [valAt_comp _ y U ⊤ h (top_le_pre _), valAt_spec]
  rfl

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

lemma valAt_const (Γ : QFGroup R T) (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ ⊤) (h' : ⊤ ≤ Γ.G.hom ⁻¹ᵁ ⊤)
    (c : Γ(Spec (CommRingCat.of R), ⊤)) :
    valAt (Γ.pt t).left ⊤ h ((Γ.G.hom.appLE ⊤ ⊤ h').hom c) =
      algebraMap R (FractionRing R) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c) := by
  have e : (Γ.pt t).left ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) :=
    Over.w (Γ.pt t)
  rw [← valAt_comp (Γ.pt t).left Γ.G.hom ⊤ ⊤ h' h (top_le_pre _), valAt_congr e _ _ (top_le_pre _), valAt_spec]

def secFn (Γ : QFGroup R T) : Submodule R (T → FractionRing R) where
  carrier := {f | ∃ s : Γ(Γ.G.left, ⊤), ∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ ⊤),
    valAt (Γ.pt t).left ⊤ h s = f t}
  add_mem' := by
    rintro f f' ⟨s, hs⟩ ⟨s', hs'⟩
    exact ⟨s + s', fun t h => by rw [valAt_add, hs, hs']; rfl⟩
  zero_mem' := ⟨0, fun t h => by rw [valAt_zero]; rfl⟩
  smul_mem' := by
    rintro r f ⟨s, hs⟩
    refine ⟨(Γ.G.hom.appLE ⊤ ⊤ (top_le_pre _)).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) * s,
      fun t h => ?_⟩
    rw [valAt_mul, valAt_const, hs]
    simp [Algebra.smul_def]

lemma mem_btOrder_iff [Finite T] (Γ : QFGroup R T) (f : T → R) :
    f ∈ Γ.btOrder ⊤ ↔ ∀ t, (fun h => algebraMap R (FractionRing R) (f (t * h))) ∈ secFn Γ := by
  rw [PositivityTheory.HtPt.Twhopf.mem_order R T Γ ⊤ f]
  refine forall_congr' fun t => ?_
  have := PositivityTheory.HtPt.Twhopf.reg_iff R T Γ ⊤ (fun h => algebraMap R (FractionRing R) (f (t * h)))
  exact this

lemma pushout_induction {A B C D : CommRingCat.{0}} {a : A ⟶ B} {c : A ⟶ C} {b : B ⟶ D} {d : C ⟶ D}
    (h : IsPushout a c b d) (P : D → Prop) (h0 : P 0) (h1 : ∀ x, P (b.hom x))
    (h2 : ∀ s n, P n → P (d.hom s * n)) (h3 : ∀ x y, P x → P y → P (x + y)) (x : D) : P x := by
  letI : Algebra A B := a.hom.toAlgebra
  letI : Algebra A C := c.hom.toAlgebra
  letI : Algebra B D := b.hom.toAlgebra
  letI : Algebra C D := d.hom.toAlgebra
  letI : Algebra A D := (a ≫ b).hom.toAlgebra
  haveI : IsScalarTower A B D := .of_algebraMap_eq fun r => rfl
  haveI : IsScalarTower A C D := .of_algebraMap_eq fun r => congr($(h.w).hom r)
  have hpo : Algebra.IsPushout A C B D := CommRingCat.isPushout_iff_isPushout.mp h.flip
  induction x using hpo.out.inductionOn with
  | zero => exact h0
  | tmul y => exact h1 y
  | smul s n hn => exact h2 s n hn
  | add x y hx hy => exact h3 x y hx hy

variable {R' : Type} [CommRing R'] [IsDomain R'] [Algebra R R']

theorem val_mem_span [Finite T] [Module.Flat R R'] (Γ : QFGroup R T) (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left)
    (hbc : Γ'.IsBaseChange Γ (algebraMap R R') F)
    (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R'))
    (x : Γ(Γ'.G.left, ⊤)) :
    (fun t => valAt (Γ'.pt t).left ⊤ (top_le_pre _) x) ∈
      Submodule.span R' {w : T → FractionRing R' | ∃ n ∈ secFn Γ, w = fun h => κ (n h)} := by
  haveI := Γ.quasiCompact
  haveI := Γ.separated
  haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have H := hbc.cart
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤) (top_le_pre _) (top_le_pre _)
    (by simp)).1 (isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) (Γ.G.hom.isCompact_preimage (isAffineOpen_top _).isCompact)
      (Γ.G.hom.isQuasiSeparated_preimage (isAffineOpen_top _).isQuasiSeparated))
  refine pushout_induction po (fun y => (fun t => valAt (Γ'.pt t).left ⊤ (top_le_pre _) y) ∈
      Submodule.span R' {w : T → FractionRing R' | ∃ n ∈ secFn Γ, w = fun h => κ (n h)}) ?_ ?_ ?_ ?_ x
  · have : (fun t => valAt (Γ'.pt t).left ⊤ (top_le_pre _) (0 : Γ(Γ'.G.left, ⊤))) = 0 := by
      funext t; exact valAt_zero _ _ _
    rw [this]
    exact Submodule.zero_mem _
  · intro s
    refine Submodule.subset_span ⟨fun t => valAt (Γ.pt t).left ⊤ (top_le_pre _) s, ⟨s, fun _ _ => rfl⟩, ?_⟩
    funext t
    rw [← valAt_comp (Γ'.pt t).left F ⊤ ⊤ _ (top_le_pre _) (top_le_pre _),
      valAt_congr (GlobalTheory.T.base_change_points_compat R T Γ R' Γ' F hbc κ hκ t) _ _ (top_le_pre _),
      valAt_map κ _ _ (top_le_pre _)]
  · intro c n hn
    have : (fun t => valAt (Γ'.pt t).left ⊤ (top_le_pre _) (((Γ'.G.hom.appLE ⊤ ⊤ (top_le_pre _)).hom c) * n)) =
        ((Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom c) •
          (fun t => valAt (Γ'.pt t).left ⊤ (top_le_pre _) n) := by
      funext t
      rw [valAt_mul, valAt_const]
      simp [Algebra.smul_def]
    rw [this]
    exact Submodule.smul_mem _ _ hn
  · intro p q hp hq
    have : (fun t => valAt (Γ'.pt t).left ⊤ (top_le_pre _) (p + q)) =
        (fun t => valAt (Γ'.pt t).left ⊤ (top_le_pre _) p) + (fun t => valAt (Γ'.pt t).left ⊤ (top_le_pre _) q) := by
      funext t
      exact valAt_add _ _ _ _ _
    rw [this]
    exact Submodule.add_mem _ hp hq

lemma flat_inj [Module.Flat R R'] : Function.Injective (algebraMap R R') := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hr0
  have hreg : IsSMulRegular R' r :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hr0)
  have h1 : r • (1 : R') = r • (0 : R') := by rw [Algebra.smul_def, hr]; simp
  exact one_ne_zero (hreg h1)

lemma exists_kappa (hφ : Function.Injective (algebraMap R R')) :
    ∃ κ : FractionRing R →+* FractionRing R',
      κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') := by
  have hinj : Function.Injective ((algebraMap R' (FractionRing R')).comp (algebraMap R R')) :=
    (IsFractionRing.injective R' (FractionRing R')).comp hφ
  refine ⟨IsFractionRing.lift (K := FractionRing R) hinj, ?_⟩
  apply RingHom.ext
  intro r
  exact IsFractionRing.lift_algebraMap (K := FractionRing R) hinj r

lemma btOrder_le_ext [Finite T] [Module.Flat R R'] (Γ : QFGroup R T) (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left)
    (hbc : Γ'.IsBaseChange Γ (algebraMap R R') F)
    (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R')) :
    Γ'.btOrder ⊤ ≤ extOrder (algebraMap R R') (Γ.btOrder ⊤) := by
  intro g hg
  rw [PositivityTheory.HtPt.Htat.ext_span]
  refine alg_core κ hκ (secFn Γ) (Subalgebra.toSubmodule (Γ.btOrder ⊤)) (fun f => mem_btOrder_iff Γ f) g ?_
  intro t
  obtain ⟨x, hx⟩ := (mem_btOrder_iff Γ' g).1 hg t
  have e : (fun h => algebraMap R' (FractionRing R') (g (t * h))) =
      fun h => valAt (Γ'.pt h).left ⊤ (top_le_pre _) x := by
    funext h
    exact (hx h _).symm
  rw [e]
  exact val_mem_span Γ Γ' F hbc κ hκ x

lemma ext_le_btOrder [Finite T] (Γ : QFGroup R T) (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left)
    (hbc : Γ'.IsBaseChange Γ (algebraMap R R') F)
    (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R')) :
    extOrder (algebraMap R R') (Γ.btOrder ⊤) ≤ Γ'.btOrder ⊤ := by
  have hκ' : ∀ r, κ (algebraMap R _ r) = algebraMap R' (FractionRing R') (algebraMap R R' r) :=
    fun r => congr($hκ r)
  refine Algebra.adjoin_le ?_
  rintro _ ⟨f, hf, rfl⟩
  refine (mem_btOrder_iff Γ' _).2 fun t => ?_
  obtain ⟨s, hs⟩ := (mem_btOrder_iff Γ f).1 hf t
  refine ⟨(F.appLE ⊤ ⊤ (top_le_pre _)).hom s, fun h hh => ?_⟩
  rw [← valAt_comp (Γ'.pt h).left F ⊤ ⊤ _ _ (top_le_pre _),
    valAt_congr (GlobalTheory.T.base_change_points_compat R T Γ R' Γ' F hbc κ hκ h) _ _ (top_le_pre _),
    valAt_map κ _ _ (top_le_pre _), hs h, hκ']

end Sch

theorem btOrder_flat_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Module.Flat R R' → Γ'.btOrder ⊤ = extOrder (algebraMap R R') (Γ.btOrder ⊤) := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F hbc hflat
  obtain ⟨κ, hκ⟩ := exists_kappa (flat_inj (R := R) (R' := R'))
  exact le_antisymm (btOrder_le_ext Γ Γ' F hbc κ hκ) (ext_le_btOrder Γ Γ' F hbc κ hκ)

end PositivityTheory.HtPt.Htat.ValuationInjectivePi

theorem PositivityTheory.HtPt.Htat.bt_flat_bc : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Module.Flat R R' → Γ'.btOrder ⊤ = extOrder (algebraMap R R') (Γ.btOrder ⊤) :=
  @PositivityTheory.HtPt.Htat.ValuationInjectivePi.btOrder_flat_baseChange
end
end

section
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace PositivityTheory.HtPt.Htat.HopfOrderFlatLocal

theorem flat_localized_of_flat_baseChange {R : Type} [CommRing R] (M : Type) [AddCommGroup M]
    [Module R M] (P : Ideal R) [P.IsMaximal] (R' : Type) [CommRing R'] [IsLocalRing R']
    [Algebra R R'] [Module.Flat R R']
    (hP : (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P)
    [Module.Flat R' (R' ⊗[R] M)] : Module.Flat R (LocalizedModule P.primeCompl M) := by
  let Rp := Localization.AtPrime P
  have hu : ∀ y : P.primeCompl, IsUnit (algebraMap R R' y) := by
    intro y
    by_contra h
    have h1 : (y : R) ∈ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') :=
      (IsLocalRing.mem_maximalIdeal _).2 h
    exact y.2 (hP.le h1)
  let ψ : Rp →+* R' := IsLocalization.lift hu
  letI : Algebra Rp R' := ψ.toAlgebra
  have hψ : ∀ r : R, algebraMap Rp R' (algebraMap R Rp r) = algebraMap R R' r :=
    fun r => IsLocalization.lift_eq hu r
  haveI : IsScalarTower R Rp R' := .of_algebraMap_eq (fun r => (hψ r).symm)
  haveI : Module.Flat Rp R' := (Module.flat_iff_of_isLocalization Rp P.primeCompl R').2 inferInstance
  haveI : IsLocalHom (algebraMap Rp R') := ⟨fun x hx => by
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl x
    have e : algebraMap R R' r =
        algebraMap Rp R' (IsLocalization.mk' Rp r s) * algebraMap R R' s := by
      rw [← hψ s, ← map_mul, IsLocalization.mk'_spec, hψ]
    have hr : IsUnit (algebraMap R R' r) := by
      rw [e]; exact hx.mul (hu s)
    have hrP : r ∈ P.primeCompl := by
      intro hmem
      rw [← hP] at hmem
      exact (IsLocalRing.mem_maximalIdeal _).1 hmem hr
    have h3 : IsUnit (algebraMap R Rp r) :=
      IsLocalization.map_units Rp (⟨r, hrP⟩ : P.primeCompl)
    rw [← IsLocalization.mk'_spec Rp r s] at h3
    exact isUnit_of_mul_isUnit_left h3⟩
  haveI : Module.FaithfullyFlat Rp R' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  haveI : Module.Flat R' (R' ⊗[Rp] (Rp ⊗[R] M)) :=
    Module.Flat.of_linearEquiv (AlgebraTensorModule.cancelBaseChange R Rp R' R' M)
  haveI : Module.Flat Rp (Rp ⊗[R] M) := Module.Flat.of_flat_tensorProduct Rp (Rp ⊗[R] M) R'
  haveI : Module.Flat R (Rp ⊗[R] M) :=
    (Module.flat_iff_of_isLocalization Rp P.primeCompl (Rp ⊗[R] M)).1 inferInstance
  exact Module.Flat.of_linearEquiv
    (IsLocalizedModule.linearEquiv P.primeCompl (LocalizedModule.mkLinearMap P.primeCompl M)
      (TensorProduct.mk R Rp M 1))

theorem flat_baseChange_of_flat_extOrder {R : Type} [CommRing R] {T : Type} [CommGroup T] [Finite T]
    (A : Subalgebra R (T → R)) (R' : Type) [CommRing R'] [Algebra R R'] [Module.Flat R R']
    [Module.Flat R' (extOrder (algebraMap R R') A)] : Module.Flat R' (R' ⊗[R] A) := by
  classical
  cases nonempty_fintype T
  let L : R' ⊗[R] A →ₗ[R'] (T → R') :=
    (TensorProduct.piScalarRight R R' R' T).toLinearMap ∘ₗ LinearMap.baseChange R' A.val.toLinearMap
  have hL : ∀ (r : R') (a : A), L (r ⊗ₜ a) = fun t => r * algebraMap R R' ((a : T → R) t) := by
    intro r a
    ext t
    simp [L, Algebra.smul_def, mul_comm]
  have hinj : Function.Injective L := by
    have h1 : Function.Injective (LinearMap.baseChange R' A.val.toLinearMap) := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    exact (TensorProduct.piScalarRight R R' R' T).injective.comp h1
  have hrange : LinearMap.range L = Subalgebra.toSubmodule (extOrder (algebraMap R R') A) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r a =>
        rw [hL]
        have : (fun t => algebraMap R R' ((a : T → R) t)) ∈ extOrder (algebraMap R R') A :=
          Algebra.subset_adjoin ⟨a, a.2, rfl⟩
        exact (extOrder (algebraMap R R') A).smul_mem this r
      | add x y hx hy => rw [map_add]; exact add_mem hx hy
    · intro g hg
      have h := (PositivityTheory.HtPt.Htat.ext_span R T R' (algebraMap R R') A g).1 hg
      refine Submodule.span_le.2 ?_ h
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨(1 : R') ⊗ₜ ⟨f, hf⟩, by rw [hL]; simp⟩
  haveI : Module.Flat R' (Subalgebra.toSubmodule (extOrder (algebraMap R R') A)) :=
    inferInstanceAs (Module.Flat R' (extOrder (algebraMap R R') A))
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofInjective L hinj ≪≫ₗ LinearEquiv.ofEq _ _ hrange)

theorem mul_mem_span_prodSpan_of_mem_span {R : Type} [CommRing R] {T : Type} [CommGroup T] {R' : Type} [CommRing R']
    (φ : R →+* R') (A : Subalgebra R (T → R)) {a b : T → R'}
    (ha : a ∈ Submodule.span R' {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)})
    (hb : b ∈ Submodule.span R' {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)}) :
    (fun z : T × T => a z.1 * b z.2) ∈
      Submodule.span R' {g : T × T → R' | ∃ n ∈ prodSpan A, g = fun i => φ (n i)} := by
  induction ha using Submodule.span_induction with
  | mem a h =>
    obtain ⟨a₀, ha₀, rfl⟩ := h
    induction hb using Submodule.span_induction with
    | mem b h =>
      obtain ⟨b₀, hb₀, rfl⟩ := h
      exact Submodule.subset_span ⟨fun z => a₀ z.1 * b₀ z.2,
        Submodule.subset_span ⟨a₀, ha₀, b₀, hb₀, rfl⟩, by ext z; simp⟩
    | zero =>
      convert Submodule.zero_mem _ using 1
      ext z; simp
    | add x y _ _ hx hy =>
      convert add_mem hx hy using 1
      ext z; simp [mul_add]
    | smul c x _ hx =>
      convert Submodule.smul_mem _ c hx using 1
      ext z; simp; ring
  | zero =>
      convert Submodule.zero_mem _ using 1
      ext z; simp
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    ext z; simp [add_mul]
  | smul c x _ hx =>
    convert Submodule.smul_mem _ c hx using 1
    ext z; simp; ring

theorem prodSpan_extOrder_le {R : Type} [CommRing R] {T : Type} [CommGroup T] {R' : Type}
    [CommRing R'] (φ : R →+* R') (A : Subalgebra R (T → R)) :
    prodSpan (extOrder φ A) ≤
      Submodule.span R' {g : T × T → R' | ∃ n ∈ prodSpan A, g = fun i => φ (n i)} := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact mul_mem_span_prodSpan_of_mem_span φ A ((PositivityTheory.HtPt.Htat.ext_span R T R' φ A a).1 ha) ((PositivityTheory.HtPt.Htat.ext_span R T R' φ A b).1 hb)

theorem isHopfOrder_of_flat_local :
    ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] [IsNoetherianRing R]
      (A : Subalgebra R (T → R)), (∃ d : R, d ≠ 0 ∧ ∀ f : T → R, d • f ∈ A) →
      (∀ P : Ideal R, P.IsMaximal → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R')
        (_ : IsLocalRing R') (_ : Algebra R R'), Module.Flat R R' ∧
        (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P ∧
        IsHopfOrder (extOrder (algebraMap R R') A)) → IsHopfOrder A := by
  intro R _ _ T _ _ _ A hfull H
  haveI hfin : Module.Finite R A :=
    Module.Finite.of_injective A.val.toLinearMap Subtype.val_injective
  haveI : Module.FinitePresentation R A := Module.finitePresentation_of_finite R A
  haveI hflat : Module.Flat R A := Module.flat_of_localized_maximal A fun P hP => by
    obtain ⟨R', _, _, _, _, hf, hP', hH⟩ := H P hP
    haveI := hH.projective
    haveI : Module.Flat R' (R' ⊗[R] A) := flat_baseChange_of_flat_extOrder A R'
    exact flat_localized_of_flat_baseChange A P R' hP'
  refine ⟨hfin, Module.Flat.projective_of_finitePresentation, hfull, ?_, ?_⟩
  · intro f hf
    refine PositivityTheory.HtPt.Htat.mem_descent R (T × T) (prodSpan A) _ fun P hP => ?_
    obtain ⟨R', i1, i2, i3, i4, hf', hP', hH⟩ := H P hP
    refine ⟨R', i1, i3, i4, hf', hP', ?_⟩
    have h1 : (fun t => algebraMap R R' (f t)) ∈ extOrder (algebraMap R R') A :=
      Algebra.subset_adjoin ⟨f, hf, rfl⟩
    exact prodSpan_extOrder_le _ A (hH.comul _ h1)
  · intro f hf
    refine PositivityTheory.HtPt.Htat.mem_descent R T (Subalgebra.toSubmodule A) _ fun P hP => ?_
    obtain ⟨R', i1, i2, i3, i4, hf', hP', hH⟩ := H P hP
    refine ⟨R', i1, i3, i4, hf', hP', ?_⟩
    have h1 : (fun t => algebraMap R R' (f t)) ∈ extOrder (algebraMap R R') A :=
      Algebra.subset_adjoin ⟨f, hf, rfl⟩
    exact (PositivityTheory.HtPt.Htat.ext_span R T R' (algebraMap R R') A _).1 (hH.inv _ h1)

end PositivityTheory.HtPt.Htat.HopfOrderFlatLocal
end

section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

noncomputable section

namespace PositivityTheory.HtPt.Htat.StalkDivisibility

def constSec {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) (d : R) : Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d)

section valAt

variable {B C R : Type} [CommRing B] [CommRing C] [CommRing R] {X Y : Scheme.{0}}

theorem valAt_congr {x y : Spec (CommRingCat.of B) ⟶ X} (e : x = y) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ y ⁻¹ᵁ U) (s : Γ(X, U)) : valAt x U h s = valAt y U h' s := by
  subst e; rfl

theorem valAt_res (x : Spec (CommRingCat.of B) ⟶ X) {U V : X.Opens} (i : V ⟶ U) (hV : ⊤ ≤ x ⁻¹ᵁ V)
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt x V hV ((X.presheaf.map i.op).hom s) = valAt x U hU s :=
  congrArg (fun φ => (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (φ.hom s)) (x.map_appLE hV i.op)

theorem valAt_mul (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) :
    valAt x U h (a * b) = valAt x U h a * valAt x U h b := by
  simp [valAt]

theorem valAt_sub (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) :
    valAt x U h (a - b) = valAt x U h a - valAt x U h b := by
  simp [valAt]

theorem valAt_comp (x : Spec (CommRingCat.of B) ⟶ Y) (F : Y ⟶ X) (U : X.Opens) (h : ⊤ ≤ (x ≫ F) ⁻¹ᵁ U)
    (s : Γ(X, U)) : valAt (x ≫ F) U h s = valAt x (F ⁻¹ᵁ U) h ((F.app U).hom s) := by
  simp only [valAt, Scheme.Hom.comp_appLE]
  rfl

theorem specMap_appLE_top (φ : B →+* C) (e) (r : Γ(Spec (CommRingCat.of B), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom (((Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ e).hom r) =
      φ ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom r) := by
  have h : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ e = (Spec.map (CommRingCat.ofHom φ)).appTop := by
    exact (Scheme.Hom.app_eq_appLE _).symm
  rw [h]
  exact congrArg (fun ψ => ψ.hom r) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))

theorem valAt_spec (κ : B →+* C) (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ x) ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt (Spec.map (CommRingCat.ofHom κ) ≫ x) U h' s = κ (valAt x U h s) := by
  have e := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom κ)) x U ⊤ ⊤ h (fun _ _ => trivial)
  simp only [valAt]
  rw [← e]
  exact specMap_appLE_top κ _ _

theorem valAt_const (p : X ⟶ Spec (CommRingCat.of R)) (x : Spec (CommRingCat.of B) ⟶ X) (φ : R →+* B)
    (hx : x ≫ p = Spec.map (CommRingCat.ofHom φ)) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (d : R) :
    valAt x U h (constSec p U d) = φ d := by
  have e := Scheme.Hom.appLE_comp_appLE x p ⊤ U ⊤ (fun _ _ => trivial) h
  have key : ∀ (y : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (_ : y = Spec.map (CommRingCat.ofHom φ)) (e' : ⊤ ≤ y ⁻¹ᵁ ⊤),
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((y.appLE ⊤ ⊤ e').hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d)) = φ d := by
    intro y hy e'
    subst hy
    rw [specMap_appLE_top]
    simp
  change (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom
    ((p.appLE ⊤ U (fun _ _ => trivial) ≫ x.appLE U ⊤ h).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d)) = φ d
  rw [e]
  exact key _ hx _

theorem constSec_res (p : X ⟶ Spec (CommRingCat.of R)) {U V : X.Opens} (i : V ⟶ U) (d : R) :
    (X.presheaf.map i.op).hom (constSec p U d) = constSec p V d :=
  congrArg (fun ψ => ψ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d))
    (p.appLE_map (U := ⊤) (V := U) (V' := V) (fun _ _ => trivial) i.op)

theorem app_constSec {R' : Type} [CommRing R'] (p : X ⟶ Spec (CommRingCat.of R)) (p' : Y ⟶ Spec (CommRingCat.of R'))
    (F : Y ⟶ X) (φ : R →+* R') (hF : F ≫ p = p' ≫ Spec.map (CommRingCat.ofHom φ)) (U : X.Opens) (d : R) :
    (F.app U).hom (constSec p U d) = constSec p' (F ⁻¹ᵁ U) (φ d) := by
  have e₁ := Scheme.Hom.appLE_comp_appLE F p ⊤ U (F ⁻¹ᵁ U) (fun _ _ => trivial) le_rfl
  have e₂ : ∀ (y : Y ⟶ Spec (CommRingCat.of R)) (_ : y = p' ≫ Spec.map (CommRingCat.ofHom φ)) (e' : F ⁻¹ᵁ U ≤ y ⁻¹ᵁ ⊤),
      (y.appLE ⊤ (F ⁻¹ᵁ U) e').hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d) = constSec p' (F ⁻¹ᵁ U) (φ d) := by
    intro y hy e'
    subst hy
    rw [Scheme.Hom.comp_appLE]
    have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
    have n' := congrArg (fun ψ => ψ.hom d) n
    simp only [constSec]
    change (p'.appLE _ _ _).hom (((Spec.map (CommRingCat.ofHom φ)).appTop).hom _) = _
    exact congrArg (p'.appLE ⊤ (F ⁻¹ᵁ U) (fun _ _ => trivial)).hom n'.symm
  rw [← e₂ _ hF (fun _ _ => trivial), ← e₁, Scheme.Hom.app_eq_appLE]
  rfl

theorem dvd_of_stalkMap_dvd (r : Y ⟶ X) [Flat r] (z : Y) {a b : X.presheaf.stalk (r z)}
    (h : (r.stalkMap z).hom a ∣ (r.stalkMap z).hom b) : a ∣ b := by
  let _ := (r.stalkMap z).hom.toAlgebra
  have : Module.Flat (X.presheaf.stalk (r z)) (Y.presheaf.stalk z) := Flat.stalkMap r z
  have : IsLocalHom (algebraMap (X.presheaf.stalk (r z)) (Y.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (r.stalkMap z).hom)
  have : Module.FaithfullyFlat (X.presheaf.stalk (r z)) (Y.presheaf.stalk z) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [← Ideal.mem_span_singleton, ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := Y.presheaf.stalk z) (Ideal.span {a}),
    Ideal.mem_comap, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  exact h

theorem top_le_of_spec_comp {K L : Type} [Field K] [Field L] (κ : K →+* L) (x : Spec (CommRingCat.of K) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro y _
  have : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (Spec (CommRingCat.of L)) := inferInstanceAs (Nonempty (PrimeSpectrum L))
  obtain ⟨w⟩ := this
  have hw := h (show w ∈ (⊤ : (Spec (CommRingCat.of L)).Opens) from trivial)
  rw [Subsingleton.elim y (Spec.map (CommRingCat.ofHom κ) w)]
  simpa using hw

end valAt

theorem regularAt_of_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Module.Flat R R' → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ (f : T → FractionRing R) (g' : Γ'.G.left), Γ'.RegularAt (fun t => κ (f t)) g' → Γ.RegularAt f (F g') := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F hbc hfl κ hκ f g' hreg
  obtain ⟨U', hgU', s', hs'⟩ := hreg
  obtain ⟨d, hd0, U, hgU, s, hs⟩ := GlobalTheory.T.exists_denominator_regular R T Γ f (F g')
  have hφ : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr hfl)
  have hF : Flat F := MorphismProperty.of_isPullback (P := @Flat) hbc.cart.flip hφ
  have hsq : F ≫ Γ.G.hom = Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) := hbc.cart.w
  let W' : Γ'.G.left.Opens := (F ⁻¹ᵁ U) ⊓ U'
  have hgW' : g' ∈ W' := ⟨hgU, hgU'⟩
  let i₁ : W' ⟶ F ⁻¹ᵁ U := homOfLE inf_le_left
  let i₂ : W' ⟶ U' := homOfLE inf_le_right
  have key : (Γ'.G.left.presheaf.map i₁.op).hom ((F.app U).hom s) =
      constSec Γ'.G.hom W' (algebraMap R R' d) * (Γ'.G.left.presheaf.map i₂.op).hom s' := by
    refine sub_eq_zero.mp (PositivityTheory.HtPt.Twhopf.sec_inj R' T Γ' W' _ fun t h => ?_)
    have h₁ : ⊤ ≤ (Γ'.pt t).left ⁻¹ᵁ (F ⁻¹ᵁ U) := fun x hx => (h hx).1
    have h₂ : ⊤ ≤ (Γ'.pt t).left ⁻¹ᵁ U' := fun x hx => (h hx).2
    have hpt := GlobalTheory.T.base_change_points_compat R T Γ R' Γ' F hbc κ hκ t
    have h₃ : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ (Γ.pt t).left) ⁻¹ᵁ U := by
      rw [← hpt]; exact h₁
    have h₄ : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U := top_le_of_spec_comp κ _ U h₃
    have hw' : (Γ'.pt t).left ≫ Γ'.G.hom =
        Spec.map (CommRingCat.ofHom (algebraMap R' (FractionRing R'))) := Over.w (Γ'.pt t)
    rw [valAt_sub, valAt_mul, valAt_res _ i₁ h h₁, valAt_res _ i₂ h h₂, hs' t h₂,
      valAt_const _ _ (algebraMap R' (FractionRing R')) hw', ← valAt_comp _ F U h₁,
      valAt_congr hpt U h₁ h₃, valAt_spec κ _ U h₄ h₃, hs t h₄, map_mul]
    have : κ (algebraMap R _ d) = algebraMap R' _ (algebraMap R R' d) := congrArg (fun ψ => ψ d) hκ
    rw [this, sub_self]
  have hdvd : Γ.G.left.presheaf.germ U (F g') hgU (constSec Γ.G.hom U d) ∣
      Γ.G.left.presheaf.germ U (F g') hgU s := by
    apply dvd_of_stalkMap_dvd F g'
    refine ⟨Γ'.G.left.presheaf.germ W' g' hgW' ((Γ'.G.left.presheaf.map i₂.op).hom s'), ?_⟩
    have e₁ := Scheme.Hom.germ_stalkMap_apply F U g' hgU s
    have e₂ := Scheme.Hom.germ_stalkMap_apply F U g' hgU (constSec Γ.G.hom U d)
    rw [app_constSec _ _ F _ hsq] at e₂
    have e₃ := Γ'.G.left.presheaf.germ_res_apply i₁ g' hgW' ((F.app U).hom s)
    have e₄ := Γ'.G.left.presheaf.germ_res_apply i₁ g' hgW' (constSec Γ'.G.hom (F ⁻¹ᵁ U) (algebraMap R R' d))
    rw [constSec_res] at e₄
    rw [key, map_mul] at e₃
    exact e₁.trans (e₃.symm.trans (by rw [e₄, ← e₂]))
  obtain ⟨x, hx⟩ := hdvd
  obtain ⟨W, hgW, s₀, rfl⟩ := Γ.G.left.presheaf.exists_germ_eq x
  let P : Γ.G.left.Opens := U ⊓ W
  have hgP : F g' ∈ P := ⟨hgU, hgW⟩
  let j₁ : P ⟶ U := homOfLE inf_le_left
  let j₂ : P ⟶ W := homOfLE inf_le_right
  have hP : Γ.G.left.presheaf.germ U (F g') hgU s = Γ.G.left.presheaf.germ P (F g') hgP
      (constSec Γ.G.hom P d * (Γ.G.left.presheaf.map j₂.op).hom s₀) := by
    rw [hx, map_mul, TopCat.Presheaf.germ_res_apply, ← constSec_res _ j₁, TopCat.Presheaf.germ_res_apply]
  obtain ⟨V, hV, iU, iP, hres⟩ := TopCat.Presheaf.germ_eq _ _ hgU hgP _ _ hP
  refine ⟨V, hV, (Γ.G.left.presheaf.map (iP ≫ j₂).op).hom s₀, fun t h => ?_⟩
  have hU : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U := fun x hx => iU.le (h hx)
  have hPt : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ P := fun x hx => iP.le (h hx)
  have hWt : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ W := fun x hx => (iP ≫ j₂).le (h hx)
  have hw : (Γ.pt t).left ≫ Γ.G.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := Over.w (Γ.pt t)
  have hK : algebraMap R (FractionRing R) d ≠ 0 := by
    simpa using hd0
  refine mul_left_cancel₀ hK ?_
  have e₁ := congrArg (valAt (Γ.pt t).left V h) hres
  rw [valAt_res _ iU h hU, hs t hU, valAt_res _ iP h hPt, valAt_mul, valAt_const _ _ _ hw,
    valAt_res _ j₂ hPt hWt] at e₁
  rw [valAt_res _ (iP ≫ j₂) h hWt]
  exact e₁.symm

end PositivityTheory.HtPt.Htat.StalkDivisibility

theorem PositivityTheory.HtPt.Htat.bt_reg_descent : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Module.Flat R R' → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ (f : T → FractionRing R) (g' : Γ'.G.left), Γ'.RegularAt (fun t => κ (f t)) g' → Γ.RegularAt f (F g') :=
  @PositivityTheory.HtPt.Htat.StalkDivisibility.regularAt_of_baseChange
end
end

section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace PositivityTheory.HtPt.Htat.HopfOrderEqTop

theorem btOrder_eq_top (hHenselian : type_of% @GlobalTheory.T.exists_henselian_flat_over_prime) (hBaseChange : type_of% @GlobalTheory.T.exists_base_change_group) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T]
    [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (hU : Γ.IsFinOpenSub U) :
    Γ.btOrder U = Γ.btOrder ⊤ := by
  ext f
  rw [PositivityTheory.HtPt.Twhopf.mem_order, PositivityTheory.HtPt.Twhopf.mem_order]
  refine ⟨fun hf t g _ => ?_, fun hf t g _ => hf t g trivial⟩
  obtain ⟨R', _, _, _, _, hN, hflat, hP⟩ :=
    @hHenselian R _ _ _ (Γ.G.hom g).asIdeal (Γ.G.hom g).isPrime
  have hinj : Function.Injective (algebraMap R R') := FaithfulSMul.algebraMap_injective R R'
  obtain ⟨Γ', F, hF⟩ := hBaseChange R T Γ R' (algebraMap R R') hinj
  have hinj' : Function.Injective ((algebraMap R' (FractionRing R')).comp (algebraMap R R')) :=
    (IsFractionRing.injective R' (FractionRing R')).comp hinj
  let κ : FractionRing R →+* FractionRing R' := IsFractionRing.lift hinj'
  have hκa : ∀ r, κ (algebraMap R _ r) = algebraMap R' _ (algebraMap R R' r) := fun r =>
    IsFractionRing.lift_algebraMap hinj' r
  have hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') := RingHom.ext hκa
  obtain ⟨g', hg1, hg2⟩ := Scheme.exists_preimage_of_isPullback hF.cart g (IsLocalRing.closedPoint R') (by
    apply PrimeSpectrum.ext
    exact hP.symm)
  haveI := Γ'.quasiFinite
  haveI := Γ'.finPres
  haveI := Γ'.separated
  haveI := Γ'.quasiCompact
  obtain ⟨U', hU'fin, hU'cl⟩ := PositivityTheory.HtPt.Twhopf.finite_part R' Γ'.G.left Γ'.G.hom
  have hU' := PositivityTheory.HtPt.Twhopf.finite_sub R' T Γ' U' hU'fin hU'cl
  have hFU := GlobalTheory.T.isFinOpenSub_base_change R T Γ R' Γ' F hF U hU
  have hle : F ⁻¹ᵁ U ≤ U' := PositivityTheory.HtPt.Twhopf.finite_le R' _ Γ'.G.hom _ _ hFU.finite hU'cl
  have h1 : (fun h => algebraMap R R' (f h)) ∈ Γ'.btSet (F ⁻¹ᵁ U) := by
    intro s x hx
    have := hRegular R T Γ R' Γ' F hF κ hκ _ x (hf s (F x) hx)
    simpa only [hκa] using this
  rw [← PositivityTheory.HtPt.Twhopf.mem_order, ← GlobalTheory.T.btOrder_eq_of_le_of_isFinOpenSub R' T Γ' U' _ hU' hFU hle, PositivityTheory.HtPt.Twhopf.mem_order] at h1
  rw [← hg1]
  refine PositivityTheory.HtPt.Htat.bt_reg_descent R T Γ R' Γ' F hF hflat κ hκ _ g' ?_
  simpa only [hκa] using h1 t g' (hU'cl g' hg2)

end PositivityTheory.HtPt.Htat.HopfOrderEqTop

theorem PositivityTheory.HtPt.Htat.bt_sub_eq_top_of (hHenselian : type_of% @GlobalTheory.T.exists_henselian_flat_over_prime) (hBaseChange : type_of% @GlobalTheory.T.exists_base_change_group) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.btOrder U = Γ.btOrder ⊤ :=
  @PositivityTheory.HtPt.Htat.HopfOrderEqTop.btOrder_eq_top hHenselian hBaseChange hRegular
end

section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

theorem PositivityTheory.HtPt.Htat.SubgroupHopfOrder.btOrder_isHopfOrder_of_finOpenSub :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → IsHopfOrder (Γ.btOrder U) := by
  intro R _ _ _ T _ _ Γ U hU
  obtain ⟨H, A, hH, hA, hAf⟩ := PositivityTheory.HtPt.Twhopf.sub_order R T Γ U hU
  have key : Γ.btOrder U = indOrder H.subtype A := by
    ext f
    rw [PositivityTheory.HtPt.Twhopf.mem_order R T Γ U f]
    constructor
    · intro hf t
      obtain ⟨s, hs⟩ := (PositivityTheory.HtPt.Twhopf.reg_iff R T Γ U _).1 (hf t)
      exact (hAf _).2 ⟨s, fun t' h => hs t' h⟩
    · intro hf t
      refine (PositivityTheory.HtPt.Twhopf.reg_iff R T Γ U _).2 ?_
      obtain ⟨s, hs⟩ := (hAf _).1 (hf t)
      exact ⟨s, fun t' h => hs ⟨t', (hH t').2 h⟩ h⟩
  rw [key]
  exact PositivityTheory.HtPt.Twhopf.ind_hopf R T H H.subtype H.subtype_injective A hA

theorem PositivityTheory.HtPt.Htat.bt_sub_hopf : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → IsHopfOrder (Γ.btOrder U) :=
  @PositivityTheory.HtPt.Htat.SubgroupHopfOrder.btOrder_isHopfOrder_of_finOpenSub
end

section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace PositivityTheory.HtPt.Htat.HopfOrderTop

private theorem btOrder_top_isHopfOrder' (hHenselian : type_of% @GlobalTheory.T.exists_henselian_flat_over_prime) (hBaseChange : type_of% @GlobalTheory.T.exists_base_change_group)
    (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) (R' : Type) [CommRing R'] [IsDomain R'] [IsIntegrallyClosed R']
    [HenselianLocalRing R'] (T : Type) [CommGroup T] [Finite T] (Γ' : QFGroup R' T) :
    IsHopfOrder (Γ'.btOrder ⊤) := by
  haveI := Γ'.separated
  haveI := Γ'.quasiCompact
  haveI := Γ'.quasiFinite
  haveI := Γ'.finPres
  have hU : Γ'.IsFinOpenSub (GlobalTheory.finitePart Γ'.G.hom) := by
    apply QFGroup.isFinOpenSub_of_closedFibre
    · exact GlobalTheory.isFinite_finitePart (R := CommRingCat.of R') Γ'.G.hom
    · intro x hx
      exact GlobalTheory.mem_finitePart_of_eq_closedPoint (R := CommRingCat.of R') _ x hx
  rw [← PositivityTheory.HtPt.Htat.HopfOrderEqTop.btOrder_eq_top hHenselian hBaseChange hRegular R' T Γ' _ hU]
  exact PositivityTheory.HtPt.Htat.SubgroupHopfOrder.btOrder_isHopfOrder_of_finOpenSub R' T Γ' _ hU

private theorem exists_smul_mem_of_extOrder {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {T : Type} [CommGroup T] [Finite T] (A : Subalgebra R (T → R))
    (hA : ∀ g : T → K, g ∈ extOrder (algebraMap R K) A) :
    ∃ d : R, d ≠ 0 ∧ ∀ f : T → R, d • f ∈ A := by
  classical
  have key : ∀ x ∈ extOrder (algebraMap R K) A, ∃ s : R, s ≠ 0 ∧ ∃ a ∈ A,
      algebraMap R K s • x = fun t => algebraMap R K (a t) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨1, one_ne_zero, a, ha, by simp⟩
    | algebraMap k =>
      obtain ⟨⟨n, ⟨s, hs⟩⟩, hk⟩ := IsLocalization.surj (nonZeroDivisors R) k
      refine ⟨s, nonZeroDivisors.ne_zero hs, algebraMap R (T → R) n, Subalgebra.algebraMap_mem A n, ?_⟩
      funext t
      simp only [Pi.smul_apply, smul_eq_mul, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rw [mul_comm]
      exact hk
    | add x y _ _ hx hy =>
      obtain ⟨s1, hs1, a1, ha1, e1⟩ := hx
      obtain ⟨s2, hs2, a2, ha2, e2⟩ := hy
      refine ⟨s1 * s2, mul_ne_zero hs1 hs2, s2 • a1 + s1 • a2, A.add_mem (A.smul_mem ha1 _) (A.smul_mem ha2 _), ?_⟩
      funext t
      have h1 := congrFun e1 t
      have h2 := congrFun e2 t
      simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, map_mul, map_add] at h1 h2 ⊢
      linear_combination (algebraMap R K s2) * h1 + (algebraMap R K s1) * h2
    | mul x y _ _ hx hy =>
      obtain ⟨s1, hs1, a1, ha1, e1⟩ := hx
      obtain ⟨s2, hs2, a2, ha2, e2⟩ := hy
      refine ⟨s1 * s2, mul_ne_zero hs1 hs2, a1 * a2, A.mul_mem ha1 ha2, ?_⟩
      funext t
      have h1 := congrFun e1 t
      have h2 := congrFun e2 t
      simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, map_mul] at h1 h2 ⊢
      linear_combination (algebraMap R K s2 * y t) * h1 + (algebraMap R K (a1 t)) * h2
  choose s hs a ha e using fun t : T =>
    key _ (hA (fun u => algebraMap R K ((Pi.single t (1 : R) : T → R) u)))
  haveI := Fintype.ofFinite T
  have hδ : ∀ t, s t • (Pi.single t (1 : R) : T → R) = a t := by
    intro t
    funext u
    apply IsFractionRing.injective R K
    have := congrFun (e t) u
    simpa [Algebra.smul_def] using this
  refine ⟨∏ t, s t, Finset.prod_ne_zero_iff.mpr fun t _ => hs t, fun f => ?_⟩
  have hmem : (∏ t, s t) • f = ∑ t, (f t * ∏ t' ∈ Finset.univ.erase t, s t') • a t := by
    funext u
    simp only [← hδ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Finset.mul_prod_erase _ s (Finset.mem_univ u)]
    ring
  rw [hmem]
  exact A.sum_mem fun t _ => A.smul_mem (ha t) _

theorem btOrder_top_isHopfOrder (hHenselian : type_of% @GlobalTheory.T.exists_henselian_flat_over_prime) (hBaseChange : type_of% @GlobalTheory.T.exists_base_change_group) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) : IsHopfOrder (Γ.btOrder ⊤) := by
  classical
  refine PositivityTheory.HtPt.Htat.HopfOrderFlatLocal.isHopfOrder_of_flat_local R T _ ?_ ?_
  · obtain ⟨ΓK, F, hbc⟩ := hBaseChange R T Γ (FractionRing R) (algebraMap R (FractionRing R))
      (IsFractionRing.injective R _)
    have hK := btOrder_top_isHopfOrder' hHenselian hBaseChange hRegular (FractionRing R) T ΓK
    rw [PositivityTheory.HtPt.Htat.ValuationInjectivePi.btOrder_flat_baseChange R T Γ _ ΓK F hbc inferInstance] at hK
    obtain ⟨d', hd', hd'm⟩ := hK.full
    refine exists_smul_mem_of_extOrder (K := FractionRing R) _ fun g => ?_
    have := hd'm (d'⁻¹ • g)
    rwa [smul_smul, mul_inv_cancel₀ hd', one_smul] at this
  · intro P hP
    haveI := hP.isPrime
    obtain ⟨R', iR, iD, iH, iA, hic, hfl, hcomap⟩ := hHenselian R P
    have hinj : Function.Injective (algebraMap R R') := PositivityTheory.HtPt.Htat.ValuationInjectivePi.flat_inj
    obtain ⟨Γ', F, hbc⟩ := hBaseChange R T Γ R' (algebraMap R R') hinj
    refine ⟨R', iR, iD, inferInstance, iA, hfl, hcomap, ?_⟩
    rw [← PositivityTheory.HtPt.Htat.ValuationInjectivePi.btOrder_flat_baseChange R T Γ R' Γ' F hbc hfl]
    exact btOrder_top_isHopfOrder' hHenselian hBaseChange hRegular R' T Γ'

end PositivityTheory.HtPt.Htat.HopfOrderTop

theorem PositivityTheory.HtPt.Htat.bt_hopf_of (hHenselian : type_of% @GlobalTheory.T.exists_henselian_flat_over_prime) (hBaseChange : type_of% @GlobalTheory.T.exists_base_change_group) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), IsHopfOrder (Γ.btOrder ⊤) :=
  @PositivityTheory.HtPt.Htat.HopfOrderTop.btOrder_top_isHopfOrder hHenselian hBaseChange hRegular
end
