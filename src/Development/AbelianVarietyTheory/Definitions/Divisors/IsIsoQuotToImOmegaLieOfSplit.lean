module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEquivariantToBidual

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (IsFiniteQC pullbackSections)
open GlobalTheory.DualPull (adj adj_app pull_ext appLE_resG resG_appLE theta toCut ofCut cutEquiv)
open GlobalTheory.VB GlobalTheory.Conormal

namespace GlobalTheory.LieVB

variable {S S' : Scheme.{0}}

theorem le_preimage_top {X Y : Scheme.{0}} (f : X ⟶ Y) (V : X.Opens) : V ≤ f ⁻¹ᵁ ⊤ := le_top

theorem appLE_top {X Y : Scheme.{0}} (f : X ⟶ Y) (a : Γ(Y, ⊤)) :
    f.appLE ⊤ ⊤ (le_preimage_top f ⊤) a = f.appTop a :=
  congr($(Scheme.Hom.appLE_eq_app f (U := ⊤)) a)

section Pointed

variable {T T' T'' : Over S}

def sec (s : 𝟙_ (Over S) ⟶ T) : S ⟶ T.left := s.left

theorem sec_hom (s : 𝟙_ (Over S) ⟶ T) : sec s ≫ T.hom = 𝟙 S := Over.w s

instance quasiCompact_sec (s : 𝟙_ (Over S) ⟶ T) [QuasiSeparated T.hom] : QuasiCompact (sec s) :=
  have : QuasiCompact (sec s ≫ T.hom) := sec_hom s ▸ inferInstance
  .of_comp _ T.hom

variable {s : 𝟙_ (Over S) ⟶ T} {s' : 𝟙_ (Over S) ⟶ T'} {s'' : 𝟙_ (Over S) ⟶ T''}

def cotMap (φ : T' ⟶ T) (h : s' ≫ φ = s) : conormal (sec s) ⟶ conormal (sec s') :=
  map (sec_hom s') (Over.w φ) (congrArg (·.left) h)

theorem cotMap_d (φ : T' ⟶ T) (h : s' ≫ φ = s) {V : S.Opens} {W : T.left.Opens}
    {W' : T'.left.Opens} (hW : V ≤ sec s ⁻¹ᵁ W) (hW' : V ≤ sec s' ⁻¹ᵁ W') (k : W' ≤ φ.left ⁻¹ᵁ W)
    (f : Γ(T.left, W)) : (cotMap φ h).app V (d (sec_hom s) hW f) =
      d (sec_hom s') hW' (φ.left.appLE W W' k f) := map_d _ _ _ _ _ _ _ _

theorem cotMap_id {φ : T ⟶ T} (hφ : φ = 𝟙 T) (h : s ≫ φ = s) : cotMap φ h = 𝟙 _ :=
  map_id _ (congrArg (·.left) hφ) _ _

theorem cotMap_comp {φ : T' ⟶ T} {ψ : T'' ⟶ T'} (h : s' ≫ φ = s) (h' : s'' ≫ ψ = s')
    {χ : T'' ⟶ T} (hχ : ψ ≫ φ = χ) (h'' : s'' ≫ χ = s) : cotMap φ h ≫ cotMap ψ h' = cotMap χ h'' :=
  map_comp (sec_hom s) _ _ _ _ _ _ (congrArg (·.left) hχ) _ _

theorem cotMap_eq_zero {φ : T' ⟶ T} (hφ : toUnit T' ≫ s = φ) (h : s' ≫ φ = s) : cotMap φ h = 0 :=
  map_eq_zero (sec_hom s) _ _ _ (congrArg (·.left) hφ)

theorem cotMap_prod [QuasiSeparated T.hom] [QuasiSeparated T'.hom]
    (i₁ : s ≫ lift (𝟙 T) (toUnit T ≫ s') = lift s s') (i₂ : s' ≫ lift (toUnit T' ≫ s) (𝟙 T') = lift s s')
    (p₁ : lift s s' ≫ fst T T' = s) (p₂ : lift s s' ≫ snd T T' = s') :
    cotMap _ i₁ ≫ cotMap _ p₁ + cotMap _ i₂ ≫ cotMap _ p₂ = 𝟙 _ := by
  have : QuasiSeparated (T ⊗ T').hom :=
    inferInstanceAs (QuasiSeparated (pullback.fst T.hom T'.hom ≫ T.hom))
  have c₁ : s' ≫ toUnit T' ≫ s = s := by simp
  have c₂ : s ≫ toUnit T ≫ s' = s' := by simp
  have d₁ := Category.comp_id s
  have d₂ := Category.comp_id s'
  refine prod_hom_ext (sec_hom s') (IsPullback.of_hasPullback T.hom T'.hom) (sec_hom (lift s s'))
    (Over.w (fst T T')) (Over.w (snd T T')) (congrArg (·.left) p₁) (congrArg (·.left) p₂) ?_ ?_
  · change cotMap _ p₁ ≫ _ = cotMap _ p₁ ≫ _
    rw [Preadditive.comp_add, reassoc_of% cotMap_comp p₁ i₁ (lift_fst _ _) d₁,
      reassoc_of% cotMap_comp p₁ i₂ (lift_fst _ _) c₁, cotMap_id rfl, cotMap_eq_zero rfl c₁,
      zero_comp, add_zero, Category.id_comp, Category.comp_id]
  · change cotMap _ p₂ ≫ _ = cotMap _ p₂ ≫ _
    rw [Preadditive.comp_add, reassoc_of% cotMap_comp p₂ i₁ (lift_snd _ _) c₂,
      reassoc_of% cotMap_comp p₂ i₂ (lift_snd _ _) d₂, cotMap_id rfl, cotMap_eq_zero rfl c₂,
      zero_comp, zero_add, Category.id_comp, Category.comp_id]

theorem cotMap_mul {G : Over S} [GrpObj G] [QuasiSeparated G.hom] {x y : T ⟶ G} (hx : s ≫ x = η)
    (hy : s ≫ y = η) (h : s ≫ (x * y) = η) : cotMap (x * y) h = cotMap x hx + cotMap y hy := by
  have hm : lift η η ≫ μ[G] = η := by simpa using lift_comp_one_left (𝟙 _) η[G]
  have hl : s ≫ lift x y = lift η η := by rw [comp_lift, hx, hy]
  have i₁ : η ≫ lift (𝟙 G) (toUnit G ≫ η) = lift η[G] η[G] := by simp
  have i₂ : η ≫ lift (toUnit G ≫ η) (𝟙 G) = lift η[G] η[G] := by simp
  have p₁ := lift_fst η[G] η[G]
  have p₂ := lift_snd η[G] η[G]
  have d := Category.comp_id η[G]
  rw [← cotMap_comp hm hl (Hom.mul_def x y).symm, ← Category.id_comp (cotMap _ hl),
    ← cotMap_prod i₁ i₂ p₁ p₂, Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
    Category.assoc, cotMap_comp p₁ hl (lift_fst x y) hx, cotMap_comp p₂ hl (lift_snd x y) hy,
    reassoc_of% cotMap_comp hm i₁ (lift_comp_one_right (𝟙 G) _) d,
    reassoc_of% cotMap_comp hm i₂ (lift_comp_one_left _ (𝟙 G)) d, cotMap_id rfl, Category.id_comp,
    Category.id_comp]

end Pointed

section Def

variable (G : Over S) [GrpObj G]

abbrev unitSec : S ⟶ G.left := sec η[G]

def omega : S.Modules := conormal (unitSec G)

abbrev Lie : S.Modules := dual (omega G)

def dUnit {V : S.Opens} {W : G.left.Opens} (h : V ≤ unitSec G ⁻¹ᵁ W) :
    Γ(G.left, W) →+ Γ(omega G, V) := d (sec_hom η[G]) h

section dUnit

variable {U V V' : S.Opens} {W W' : G.left.Opens}

theorem resM_dUnit (h : V ≤ unitSec G ⁻¹ᵁ W) (h' : V' ≤ V) (f : Γ(G.left, W)) :
    resM _ h' (dUnit G h f) = dUnit G (h'.trans h) f := resM_d _ h h' f

theorem dUnit_resG (h : V ≤ unitSec G ⁻¹ᵁ W') (k : W' ≤ W) (f : Γ(G.left, W)) :
    dUnit G h (resG _ k f) = dUnit G (h.trans ((unitSec G).preimage_mono k)) f := d_resG _ h k f

theorem dUnit_mul (h : V ≤ unitSec G ⁻¹ᵁ W) (f g : Γ(G.left, W)) : dUnit G h (f * g) =
    (unitSec G).appLE W V h f • dUnit G h g + (unitSec G).appLE W V h g • dUnit G h f :=
  d_mul _ h f g

theorem dUnit_base (h : V ≤ unitSec G ⁻¹ᵁ W) (k : W ≤ G.hom ⁻¹ᵁ U) (a : Γ(S, U)) :
    dUnit G h (G.hom.appLE U W k a) = 0 := d_base _ h k a

variable {G} in
theorem omega_hom_ext {F : S.Modules} {φ ψ : omega G ⟶ F}
    (H : ∀ (W : G.left.Opens) (f : Γ(G.left, W)),
      φ.app _ (dUnit G (le_refl (unitSec G ⁻¹ᵁ W)) f) = ψ.app _ (dUnit G le_rfl f)) : φ = ψ :=
  hom_ext _ H

end dUnit

def omegaHomEquiv (F : S.Modules) : (omega G ⟶ F) ≃ Der G.hom (unitSec G) F :=
  homEquivDer F (sec_hom η[G])

theorem omegaHomEquiv_app {F : S.Modules} (φ : omega G ⟶ F) {V : S.Opens} {W : G.left.Opens}
    (h : V ≤ unitSec G ⁻¹ᵁ W) (f : Γ(G.left, W)) :
    (omegaHomEquiv G F φ).app h f = φ.app V (dUnit G h f) := rfl

def lieEquivDer : Γ(Lie G, ⊤) ≃ Der G.hom (unitSec G) (structureModule S) :=
  (homGlobalEquiv (omega G) (structureModule S)).toEquiv.trans (omegaHomEquiv G _)

instance (priority := 100) quasiSeparated_of_isSemiAbelian [h : IsSemiAbelian G] :
    QuasiSeparated G.hom :=
  have := h.separated
  inferInstance

variable [QuasiSeparated G.hom]

instance isQuasicoherent_omega : (omega G).IsQuasicoherent := isQuasicoherent_conormal _

theorem isVB_omega (g : ℕ) [SmoothOfRelativeDimension g G.hom] : IsVB (omega G) g :=
  isVB_conormal (sec_hom η[G]) g

theorem exists_isFrame_omega [Smooth G.hom] (x : S) :
    ∃ (U : S.Opens) (n : ℕ) (s : Fin n → Γ(omega G, U)), x ∈ U ∧ IsFrame s :=
  exists_isFrame (sec_hom η[G]) x

theorem exists_isVB [Smooth G.hom] [PreconnectedSpace S] :
    ∃ g, IsVB (omega G) g ∧ IsVB (Lie G) g :=
  (exists_isVB_conormal (sec_hom η[G])).imp fun _ h => ⟨h, h.dual⟩

omit [QuasiSeparated G.hom] in
theorem exists_isVB_of_isSemiAbelian [h : IsSemiAbelian G] [PreconnectedSpace S] :
    ∃ g, IsVB (omega G) g ∧ IsVB (Lie G) g :=
  have := h.smooth
  exists_isVB G

end Def

section Map

variable {G H K : Over S} [GrpObj G] [GrpObj H] [GrpObj K]

end Map

section Base

variable {G H : Over S} {G' H' : Over S'} [GrpObj G] [GrpObj H] [GrpObj G'] [GrpObj H']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}

theorem unitSec_comp (h : IsGrpPullback G' G f φ) : unitSec G' ≫ φ = f ≫ unitSec G := by
  let x := pushPt h.1.w (1 : 𝟙_ (Over S') ⟶ G')
  have h₁ : x * x = x := Over.OverMorphism.ext ((h.2 _ 1 1 x x rfl rfl).trans
    (by rw [_root_.mul_one]; rfl))
  have h₂ := congrArg (·.left) (mul_eq_left.1 h₁)
  have h₃ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  refine (congrArg (·.left ≫ φ) h₃).symm.trans (h₂.trans ?_)
  exact congrArg (· ≫ unitSec G) (Category.id_comp f)

def omegaBase (h : IsGrpPullback G' G f φ) : (Scheme.Modules.pullback f).obj (omega G) ⟶ omega G' :=
  baseMap (sec_hom η[G']) h.1.w (unitSec_comp h)

theorem omegaBase_dUnit (h : IsGrpPullback G' G f φ) {V : S.Opens} {W : G.left.Opens}
    (hW : V ≤ unitSec G ⁻¹ᵁ W) {T : S'.Opens} (hT : T ≤ f ⁻¹ᵁ V) {W' : G'.left.Opens}
    (hW' : T ≤ unitSec G' ⁻¹ᵁ W') (k : W' ≤ φ ⁻¹ᵁ W) (a : Γ(G.left, W)) :
    (omegaBase h).app T (pullbackSections f _ hT (dUnit G hW a)) =
      dUnit G' hW' (φ.appLE W W' k a) := baseMap_d _ _ _ _ _ _ _ _ _

instance isIso_omegaBase [QuasiSeparated G.hom] (h : IsGrpPullback G' G f φ) :
    IsIso (omegaBase h) :=
  have : QuasiSeparated G'.hom := MorphismProperty.of_isPullback h.1 ‹_›
  isIso_baseMap (sec_hom η[G]) (sec_hom η[G']) h.1 _

variable [QuasiSeparated G.hom] [QuasiSeparated H.hom]

def lieBase (h : IsGrpPullback G' G f φ) : (Scheme.Modules.pullback f).obj (Lie G) ⟶ Lie G' :=
  theta f (omega G) ≫ dualMap (inv (omegaBase h))

theorem isIso_lieBase (h : IsGrpPullback G' G f φ) {g : ℕ} (hg : IsVB (omega G) g) :
    IsIso (lieBase h) :=
  have := DualPull.isIso_theta f hg
  inferInstanceAs (IsIso (theta f (omega G) ≫ (dualIso (asIso (omegaBase h)).symm).hom))

theorem isVB_omega_of_isGrpPullback (h : IsGrpPullback G' G f φ) {g : ℕ} (hg : IsVB (omega G) g) :
    IsVB (omega G') g := (hg.pullback f).of_iso (asIso (omegaBase h))

end Base

section DualIm

variable {O : Type} [CommRing O] {F : S.Modules} (ρ : O →+* End F) (σ : O →+* Γ(S, ⊤)) {g r : ℕ}

end DualIm

section Act

variable {O : Type} [CommRing O] {G H : Over S} [GrpObj G] [GrpObj H] [QuasiSeparated G.hom]
  [QuasiSeparated H.hom] (i : OAct O G) (σ : O →+* Γ(S, ⊤))

variable {i}

variable {G' : Over S'} [GrpObj G'] [QuasiSeparated G'.hom] {i' : OAct O G'} {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ)
  (w : ∀ a, (i'.act a).left ≫ φ = φ ≫ (i.act a).left)
include w

section ImBase

variable {σ} {g : ℕ} (hg : IsVB (omega G) g) {D : Γ(S, ⊤)} (hf : IsRegularFn (f.appTop D))

section

variable {ε : omega G ⟶ omega G} (hε : IsEigenProj (omegaAct i) σ ε D)

end

section

variable {ε : Lie G ⟶ Lie G} (hε : IsEigenProj (lieAct i) σ ε D)

include hg

end

end ImBase

end Act

section Affine

open ReciprocityTheory.ChartRestriction.G.Pdiv

variable (O : Type) [CommRing O]

def epsZero : 𝟙_ (Over (Sp O)) ⟶ specO O (DualNumber O) :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom O O O).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)

instance : IsAffineHom (specO O (DualNumber O)).hom :=
  inferInstanceAs (IsAffineHom (Spec.map _))

def epsFn : Γ((specO O (DualNumber O)).left, ⊤) :=
  (Scheme.ΓSpecIso (.of (DualNumber O))).inv DualNumber.eps

abbrev cst : O →+* Γ(Sp O, ⊤) := (Scheme.ΓSpecIso (.of O)).inv.hom

def epsCotEquiv : AugCot (TrivSqZeroExt.fstHom O O O) ≃ₗ[O] O :=
  LinearEquiv.ofLinear
    (AugCot.lift _ (TrivSqZeroExt.sndHom O O) fun a b => by simp [mul_comm])
    (LinearMap.toSpanSingleton O _ (AugCot.d _ DualNumber.eps)) (by ext; simp)
    (AugCot.hom_ext fun a => by
      conv_rhs => rw [← a.inl_fst_add_inr_snd_eq, DualNumber.inr_eq_smul_eps]
      have : AugCot.d (TrivSqZeroExt.fstHom O O O) (.inl a.fst) = 0 := AugCot.d_algebraMap _ a.fst
      simp [this])

theorem isFrame_d_eps :
    IsFrame fun _ : Fin 1 => d (sec_hom (epsZero O)) (le_preimage_top _ ⊤) (epsFn O) :=
  isFrame_d_Spec (R := .of O) (A := .of (DualNumber O)) (TrivSqZeroExt.fstHom O O O) _ rfl rfl
    ((Module.Basis.singleton (Fin 1) O).map (epsCotEquiv O).symm) (fun _ => DualNumber.eps)
    fun _ => by simp [epsCotEquiv]

def epsIso : conormal (sec (epsZero O)) ≅ structureModule (Sp O) :=
  (isFrame_d_eps O).iso (isFrame_one ⊤)

theorem epsIso_d : (epsIso O).hom.app ⊤ (d (sec_hom (epsZero O)) (le_preimage_top _ _) (epsFn O)) =
    (1 : Γ(Sp O, ⊤)) := (isFrame_d_eps O).iso_hom_app (isFrame_one ⊤) 0

variable {O}

theorem epsZero_dualScale (a : O) : epsZero O ≫ ptMap (dualScale a) = epsZero O := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext x <;> simp [dualScale]

theorem cotMap_dualScale (a : O) :
    cotMap (ptMap (dualScale a)) (epsZero_dualScale a) = smulHom _ (cst O a) :=
  hom_ext_of_isFrame (isFrame_d_eps O) fun _ => by
    have e₁ : (ptMap (dualScale a)).left.appLE ⊤ ⊤ (le_preimage_top _ _) (epsFn O) =
        (specO O (DualNumber O)).hom.appLE ⊤ ⊤ (le_preimage_top _ _) (cst O a) * epsFn O := by
      refine congr($(Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (dualScale a).toRingHom)) DualNumber.eps).symm.trans ?_
      refine .trans ?_ (congrArg (· * epsFn O) congr($(Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (algebraMap O (DualNumber O)))) a))
      refine .trans (congrArg (Scheme.ΓSpecIso (.of (DualNumber O))).inv.hom ?_) (map_mul _
        (algebraMap O _ a) DualNumber.eps)
      change dualScale a DualNumber.eps = _
      ext <;> simp [dualScale, TrivSqZeroExt.algebraMap_eq_inl]
    rw [cotMap_d _ _ _ (le_preimage_top _ _) (le_preimage_top _ _), e₁, d_mul, d_base, smul_zero, add_zero,
      appLE_base (sec_hom _) _ _ le_rfl]
    rfl

variable {G H : Over (Sp O)} [GrpObj G] [GrpObj H]

theorem epsZero_comp (x : LieG G) : epsZero O ≫ x.1 = η := by
  have h : (toUnit (specO O O)).left = 𝟙 (Sp O) := by
    rw [Over.toUnit_left]
    exact Spec.map_id _
  have h' := congrArg (·.left) x.2
  simp only [Over.comp_left, h] at h'
  ext1
  exact h'.trans (Category.id_comp _)

def tangent (x : LieG G) : Γ(Lie G, ⊤) :=
  (homGlobalEquiv _ _).symm (cotMap x.1 (epsZero_comp x) ≫ (epsIso O).hom)

theorem dualApp_tangent_dUnit (x : LieG G) {V : (Sp O).Opens} {W : G.left.Opens}
    (h : V ≤ unitSec G ⁻¹ᵁ W) (f : Γ(G.left, W)) {T : (specO O (DualNumber O)).left.Opens}
    (hV : V ≤ sec (epsZero O) ⁻¹ᵁ T) (hT : T ≤ (specO O (DualNumber O)).hom ⁻¹ᵁ V)
    (k : T ≤ x.1.left ⁻¹ᵁ W) (a b : Γ(Sp O, V))
    (e : x.1.left.appLE W T k f = (specO O (DualNumber O)).hom.appLE V T hT a +
      (specO O (DualNumber O)).hom.appLE V T hT b * resG _ le_top (epsFn O)) :
    dualApp (tangent x) le_top (dUnit G h f) = b := by
  refine (congrArg ((epsIso O).hom.app V) (cotMap_d x.1 (epsZero_comp x) h hV k f)).trans ?_
  rw [e, map_add (f := _), d_base, zero_add, d_mul, d_base,
    smul_zero, add_zero, appLE_base (sec_hom _) _ _ le_rfl, resG_self, d_resG,
    ← resM_d _ (le_preimage_top _ ⊤) le_top, Scheme.Modules.Hom.app_smul, app_resM, epsIso_d]
  exact (congrArg (b * ·) (map_one (resG (Sp O) (le_top : V ≤ ⊤)))).trans (_root_.mul_one b)

theorem tangent_mul [QuasiSeparated G.hom] (x y : LieG G) (h) :
    tangent ⟨x.1 * y.1, h⟩ = tangent x + tangent y := by
  have e := cotMap_mul (epsZero_comp x) (epsZero_comp y) (epsZero_comp ⟨_, h⟩)
  refine dual_ext fun W _ s => ?_
  exact (congr((epsIso O).hom.app W (($e).app W s))).trans (map_add _ _ _)

theorem tangent_scale (a : O) (x : LieG G) (h) :
    tangent ⟨ptMap (dualScale a) ≫ x.1, h⟩ = cst O a • tangent x := by
  have e := cotMap_comp (epsZero_comp x) (epsZero_dualScale a) rfl (epsZero_comp ⟨_, h⟩)
  rw [cotMap_dualScale] at e
  refine dual_ext fun W _ s => ?_
  exact (congr((epsIso O).hom.app W (($e).app W s))).symm.trans ((epsIso O).hom.app_smul _ _)

end Affine

section Torus

open AddMonoidAlgebra (single)

variable (S) (X Y : Type) [AddCommGroup X] [AddCommGroup Y]

variable {X} {κ : Type} [Fintype κ] (b : Module.Basis κ ℤ X)

end Torus

section Examples

variable {G : Over S} [GrpObj G] [QuasiSeparated G.hom]

end Examples

end GlobalTheory.LieVB
