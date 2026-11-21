import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))

theorem one_left_π {S' S : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {π : G'.left ⟶ G.left} (hg : IsGrpPullback G' G f π) (T : Over S') :
    (1 : T ⟶ G').left ≫ π = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
  let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ π) (by
    show _ = T.hom ≫ f
    rw [Category.assoc, hg.1.w, ← Category.assoc, Over.w])
  have h := hg.2 T 1 1 x₀ x₀ rfl rfl
  rw [_root_.mul_one] at h
  have e : x₀ * x₀ = x₀ := Over.OverMorphism.ext h
  have e' : x₀ = 1 := by
    have := congrArg (· * x₀⁻¹) e
    simpa using this
  exact congrArg Over.Hom.left e'

theorem exists_unit {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left}
    (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) (S : Over (Sp O)) :
    ∃ z : S ⟶ Hs P' x0 hu, z ≫ aH P' x0 hu hg.1 = 1 := by
  obtain ⟨β₀, h1, h2⟩ := P'.fin.one O (lo P' x0 hu)
  have hβ₀ : β₀.comp P'.str = (algebraMap O O).comp x0 := by
    rw [GlobalTheory.HTMap.FP.str, ← RingHom.comp_assoc, h1, lo_comp]
    try rfl
  have hid : (specO O O).hom = 𝟙 _ := by
    change Spec.map (CommRingCat.ofHom (algebraMap O O)) = _
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  let c : S ⟶ specO O O := Over.homMk S.hom (by rw [hid, Category.comp_id]; try rfl)
  refine ⟨c ≫ ptOf P' x0 hu β₀ hβ₀, ?_⟩
  have hz : ptOf P' x0 hu β₀ hβ₀ ≫ aH P' x0 hu hg.1 = 1 := by
    refine Over.OverMorphism.ext (hg.1.hom_ext ?_ ?_)
    · rw [ptOf_aH_π, h2, one_left_π hg]
      refine (GlobalTheory.HTMap.one_of (G := t.G) (g := 𝟙 _) ?_).trans (Category.id_comp _)
      rw [Category.id_comp, hid, Category.id_comp, GlobalTheory.HTMap.spc_assoc, lo_comp]
    · rw [Over.w, Over.w]
  rw [Category.assoc, hz, MonObj.comp_one]

end GlobalTheory.FinPartAt
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

theorem aH_pow_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) (G' : Over (Sp O)) [GrpObj G'] (π : G'.left ⟶ t.G.left) (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π), aH P' x0 hu hg.1 ^ q = 1 := by
  intro E _ _ _ H X t R _ ξ q P' O _ x0 hu G' _ π hg
  have hinj : Function.Injective (pushHom hg (Hs P' x0 hu)) := by
    intro x y hxy
    apply Over.OverMorphism.ext
    apply hg.1.hom_ext
    · exact congrArg (fun z => z.left) hxy
    · rw [Over.w x, Over.w y]
  have hw : (pushHom hg (Hs P' x0 hu) (aH P' x0 hu hg.1)) ^ q = 1 :=
    GlobalTheory.HTMap.tors_of (g := spMap (inB P' x0 hu)) (w := P'.u) (aH_left_π P' x0 hu hg.1) P'.fin.tors
  apply hinj
  rw [map_pow, hw, map_one]

end GlobalTheory.FinPartAt
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_map_pow_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) (G' : Over (Sp O)) [GrpObj G'] (π : G'.left ⟶ t.G.left) (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π), aH P' x0 hu hg.1 ^ q = 1 := by
  atlas_forward_decl GlobalTheory.FinPartAt.aH_pow_eq_one
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))

theorem spMap_injective_divisor {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem ringHom_ext_Bt {S : Type} [CommRing S] {α β : Bt P' x0 hu →+* S}
    (h1 : α.comp (algebraMap O (Bt P' x0 hu)) = β.comp (algebraMap O (Bt P' x0 hu)))
    (h2 : α.comp (inB P' x0 hu) = β.comp (inB P' x0 hu)) : α = β := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o b =>
    have e : (o ⊗ₜ[Localization.Away P'.f] b : Bt P' x0 hu) =
        algebraMap O (Bt P' x0 hu) (show O from o) * inB P' x0 hu b := by
      change _ = (o ⊗ₜ[Localization.Away P'.f] (1 : P'.B)) * ((1 : OL P' x0 hu) ⊗ₜ b)
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
    rw [e, map_mul, map_mul]
    exact congrArg₂ (· * ·) (RingHom.congr_fun h1 (show O from o)) (RingHom.congr_fun h2 b)
  | add x y hx hy => rw [map_add, map_add, hx, hy]

variable {G' : Over (Sp O)} {π : G'.left ⟶ t.G.left}

theorem aH_cancel_aff (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)) {S : Type} [CommRing S]
    (α β : Bt P' x0 hu →+* S)
    (h : spMap α ≫ (aH P' x0 hu hπ).left = spMap β ≫ (aH P' x0 hu hπ).left) : α = β := by
  have hO : α.comp (algebraMap O (Bt P' x0 hu)) = β.comp (algebraMap O (Bt P' x0 hu)) := by
    have e := congrArg (· ≫ G'.hom) h
    simp only [Category.assoc, Over.w (aH P' x0 hu hπ)] at e
    apply spMap_injective_divisor
    exact (GlobalTheory.HTMap.spc (algebraMap O (Bt P' x0 hu)) α).symm.trans (e.trans (GlobalTheory.HTMap.spc _ β))
  have hB : α.comp (inB P' x0 hu) = β.comp (inB P' x0 hu) := by
    have e := congrArg (· ≫ π) h
    simp only [Category.assoc, aH_left_π] at e
    have e2 : spMap (α.comp (inB P' x0 hu)) ≫ P'.u.left = spMap (β.comp (inB P' x0 hu)) ≫ P'.u.left :=
      (GlobalTheory.HTMap.spc_assoc _ _ _).symm.trans (e.trans (GlobalTheory.HTMap.spc_assoc _ _ _))
    refine P'.fin.mono S _ _ (GlobalTheory.HTMap.FP.alg_ext ?_) e2
    change α.comp ((inB P' x0 hu).comp P'.str) = β.comp ((inB P' x0 hu).comp P'.str)
    rw [inB_str, ← RingHom.comp_assoc, ← RingHom.comp_assoc, hO]
  exact ringHom_ext_Bt P' x0 hu hO hB

theorem aH_left_mono (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)) : Mono (aH P' x0 hu hπ).left := by
  constructor
  intro T g h e
  refine Scheme.Cover.hom_ext T.affineCover _ _ fun i => ?_
  have ea := Spec.map_preimage (T.affineCover.f i ≫ g)
  have eb := Spec.map_preimage (T.affineCover.f i ≫ h)
  have key := aH_cancel_aff P' x0 hu hπ (Spec.preimage (T.affineCover.f i ≫ g)).hom
    (Spec.preimage (T.affineCover.f i ≫ h)).hom (by
      change Spec.map (Spec.preimage (T.affineCover.f i ≫ g)) ≫ _ = Spec.map (Spec.preimage (T.affineCover.f i ≫ h)) ≫ _
      rw [ea, eb]
      exact (Category.assoc _ _ _).trans ((congrArg (T.affineCover.f i ≫ ·) e).trans (Category.assoc _ _ _).symm))
  exact ea.symm.trans ((congrArg Spec.map (CommRingCat.hom_ext key)).trans eb)

end GlobalTheory.FinPartAt
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mono_finite_part_pullback : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X} {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q) {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) {G' : Over (Sp O)} {π : G'.left ⟶ t.G.left} (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)), Mono (aH P' x0 hu hπ).left := by
  atlas_forward_decl GlobalTheory.FinPartAt.aH_left_mono
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

theorem push_pow {S' S₀ : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S₀} [GrpObj G] {f : S' ⟶ S₀}
    {π : G'.left ⟶ G.left} (hg : IsGrpPullback G' G f π) {T : Over S'} (x : T ⟶ G')
    (x₀ : Over.mk (T.hom ≫ f) ⟶ G) (h : x₀.left = x.left ≫ π) (n : ℕ) :
    (x₀ ^ n).left = (x ^ n).left ≫ π := by
  have h1 : (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ π := by
    let e : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ π) (by
      show ((1 : T ⟶ G').left ≫ π) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, hg.1.w, ← Category.assoc, Over.w])
    have he : e * e = e := Over.OverMorphism.ext ((hg.2 T 1 1 e e rfl rfl).trans (by rw [_root_.mul_one]; rfl))
    have he1 : e = 1 := mul_eq_left.1 he
    exact (congrArg (fun z => z.left) he1).symm
  induction n with
  | zero => simpa using h1
  | succ n ih => rw [pow_succ, pow_succ]; exact hg.2 T _ _ _ _ ih h

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g := by
  have := congrArg (fun z => (Spec.preimage z).hom) h
  simpa using this

theorem lift_of_residue : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X} {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q) {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left} (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) (h : aH P' x0 hu hg.1 ^ q = 1) (S : Type) [CommRing S] [hS : IsLocalRing S] (y : Sp S ⟶ (torsion G' q).left), (∃ s : Sp (IsLocalRing.ResidueField S) ⟶ (Hs P' x0 hu).left, s ≫ (jH P' x0 hu hg.1 h).left = spMap (IsLocalRing.residue S) ≫ y) → ∃ s : Sp S ⟶ (Hs P' x0 hu).left, s ≫ (jH P' x0 hu hg.1 h).left = y := by
  intro E _ _ _ H X t R _ ξ q P' O _ x0 hu G' _ π hg h S _ hS y hy
  obtain ⟨s0, hs0⟩ := hy
  let o : O →+* S := (Spec.preimage (y ≫ (torsion G' q).hom)).hom
  have ho : spMap o = y ≫ (torsion G' q).hom := Spec.map_preimage _
  let φ : R →+* S := o.comp x0
  have hu' : IsUnit (φ P'.f) := hu.map o
  have hw : (y ≫ (torsion.ι G' q).left ≫ π) ≫ t.G.hom = spMap φ ≫ ξ := by
    rw [Category.assoc, Category.assoc, hg.1.w, ← Category.assoc (torsion.ι G' q).left, Over.w (torsion.ι G' q),
      ← Category.assoc, ← ho, GlobalTheory.HTMap.spc_assoc]
  let w : Over.mk (spMap φ ≫ ξ) ⟶ t.G := GlobalTheory.HTMap.mkPt _ hw
  let T : Over (Sp O) := Over.mk (y ≫ (torsion G' q).hom)
  let yt : T ⟶ torsion G' q := Over.homMk y rfl
  let x : T ⟶ G' := yt ≫ torsion.ι G' q
  have hx : x ^ q = 1 := by
    show (yt ≫ torsion.ι G' q) ^ q = 1
    rw [← MonObj.comp_pow, GlobalTheory.KernelNoTorsion.torsionι_pow, MonObj.comp_one]
  let x₀ : Over.mk (T.hom ≫ (spMap x0 ≫ ξ)) ⟶ t.G := Over.homMk (x.left ≫ π) (by
    show (x.left ≫ π) ≫ t.G.hom = T.hom ≫ spMap x0 ≫ ξ
    rw [Category.assoc, hg.1.w, ← Category.assoc, Over.w x])
  have hx₀ : x₀ ^ q = 1 := by
    refine Over.OverMorphism.ext ?_
    rw [push_pow hg x x₀ rfl q, hx]
    have := push_pow hg x x₀ rfl 0
    simp only [pow_zero] at this
    exact this.symm
  have hwq : w ^ q = 1 := GlobalTheory.HTMap.tors_of (g := 𝟙 _) (w := x₀) (by
    rw [Category.id_comp]
    show y ≫ (torsion.ι G' q).left ≫ π = (y ≫ (torsion.ι G' q).left) ≫ π
    rw [Category.assoc]) hx₀
  obtain ⟨β0, hβ0⟩ : ∃ β, P'.At φ w.left β := by
    refine GlobalTheory.HTMap.FP.at_open hu' rfl w hwq fun 𝔪 h𝔪 => ?_
    obtain rfl := IsLocalRing.eq_maximalIdeal h𝔪
    let gm : Bt P' x0 hu →+* IsLocalRing.ResidueField S := (Spec.preimage s0).hom
    have hgm : spMap gm = s0 := Spec.map_preimage _
    have e1 : spMap (gm.comp (algebraMap O (Bt P' x0 hu))) = spMap ((IsLocalRing.residue S).comp o) := by
      rw [← GlobalTheory.HTMap.spc (algebraMap O (Bt P' x0 hu)) gm, hgm, ← GlobalTheory.HTMap.spc o (IsLocalRing.residue S), ho]
      show s0 ≫ (Hs P' x0 hu).hom = _
      rw [← Over.w (jH P' x0 hu hg.1 h), ← Category.assoc, hs0, Category.assoc]
    have e2 := spMap_inj e1
    refine ⟨gm.comp (inB P' x0 hu), ?_, ?_⟩
    · show (gm.comp (inB P' x0 hu)).comp P'.str = (IsLocalRing.residue S).comp φ
      rw [RingHom.comp_assoc, inB_str, ← RingHom.comp_assoc, e2]
      rfl
    · show spMap (gm.comp (inB P' x0 hu)) ≫ P'.u.left = spMap (IsLocalRing.residue S) ≫ y ≫ (torsion.ι G' q).left ≫ π
      rw [← GlobalTheory.HTMap.spc_assoc, hgm, ← aH_left_π P' x0 hu hg.1, ← jH_ι P' x0 hu hg.1 h, Over.comp_left,
        ← Category.assoc, ← Category.assoc, hs0, Category.assoc, Category.assoc]
  letI : Algebra O S := o.toAlgebra
  have hβ : β0.comp P'.str = (algebraMap O S).comp x0 := hβ0.1
  refine ⟨(ptOf P' x0 hu β0 hβ).left, ?_⟩
  let b : T ⟶ torsion G' q := Over.homMk ((ptOf P' x0 hu β0 hβ).left ≫ (jH P' x0 hu hg.1 h).left) (by
    show ((ptOf P' x0 hu β0 hβ).left ≫ (jH P' x0 hu hg.1 h).left) ≫ (torsion G' q).hom = y ≫ (torsion G' q).hom
    rw [Category.assoc, Over.w (jH P' x0 hu hg.1 h), Over.w (ptOf P' x0 hu β0 hβ)]
    exact ho)
  have hb : b = yt := by
    refine GlobalTheory.KernelNoTorsion.torsion_hom_ext (Over.OverMorphism.ext (hg.1.hom_ext ?_ ?_))
    · have e1 : (b ≫ torsion.ι G' q).left = (ptOf P' x0 hu β0 hβ ≫ aH P' x0 hu hg.1).left := by
        show (ptOf P' x0 hu β0 hβ).left ≫ (jH P' x0 hu hg.1 h).left ≫ (torsion.ι G' q).left = _
        rw [← Over.comp_left, jH_ι]
        rfl
      rw [e1, ptOf_aH_π, hβ0.2]
      show y ≫ (torsion.ι G' q).left ≫ π = (y ≫ (torsion.ι G' q).left) ≫ π
      rw [Category.assoc]
    · rw [Over.w (b ≫ torsion.ι G' q), Over.w (yt ≫ torsion.ι G' q)]
  exact congrArg (fun z => z.left) hb
end GlobalTheory.FinPartAt
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_part_pow_eq_one_local : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X} {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q) {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left} (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) (h : aH P' x0 hu hg.1 ^ q = 1) (S : Type) [CommRing S] [hS : IsLocalRing S] (y : Sp S ⟶ (torsion G' q).left), (∃ s : Sp (IsLocalRing.ResidueField S) ⟶ (Hs P' x0 hu).left, s ≫ (jH P' x0 hu hg.1 h).left = spMap (IsLocalRing.residue S) ≫ y) → ∃ s : Sp S ⟶ (Hs P' x0 hu).left, s ≫ (jH P' x0 hu hg.1 h).left = y := by
  atlas_forward_decl GlobalTheory.FinPartAt.lift_of_residue
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartOpen

theorem isOpenImmersion_of_stalk {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
    [LocallyOfFinitePresentation f]
    (h : ∀ x : X, ∃ s : Spec (Y.presheaf.stalk (f x)) ⟶ X, s ≫ f = Y.fromSpecStalk (f x)) :
    IsOpenImmersion f := by
  have hbij : ∀ x : X, Function.Bijective (f.stalkMap x).hom := by
    intro x
    refine ⟨?_, f.stalkMap_surjective x⟩
    obtain ⟨s, hs⟩ := h x
    obtain ⟨⟨x', φ, hφ⟩, rfl⟩ := (SpecToEquivOfLocalRing X (Y.presheaf.stalk (f x))).symm.surjective s
    rw [SpecToEquivOfLocalRing_symm_apply] at hs
    dsimp only at hs
    have h1 : f x' = f x := by
      have := Scheme.Hom.comp_apply (Spec.map φ ≫ X.fromSpecStalk x') f (IsLocalRing.closedPoint _)
      rw [hs, Scheme.fromSpecStalk_closedPoint, GlobalTheory.TangentCrit.SpecMap_fromSpecStalk_closedPoint] at this
      exact this.symm
    have hx : x' = x := f.isClosedEmbedding.injective h1
    subst hx
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc] at hs
    have key : f.stalkMap x' ≫ φ = 𝟙 _ := by
      have e := (SpecToEquivOfLocalRing Y (Y.presheaf.stalk (f x'))).symm.injective
        (a₁ := ⟨f x', f.stalkMap x' ≫ φ, inferInstance⟩) (a₂ := ⟨f x', 𝟙 _, inferInstance⟩)
        (by rw [SpecToEquivOfLocalRing_symm_apply, SpecToEquivOfLocalRing_symm_apply]
            dsimp only
            rw [hs, Spec.map_id, Category.id_comp])
      rw [SpecToEquivOfLocalRing_eq_iff] at e
      obtain ⟨_, e⟩ := e
      simpa using e
    intro a b hab
    have := congrArg φ.hom hab
    rwa [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, key] at this
  have : Flat f := (Flat.iff_flat_stalkMap f).2 fun x => RingHom.Flat.of_bijective (hbij x)
  exact IsOpenImmersion.of_flat_of_mono f

theorem residue_lift {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f] (x : X) :
    ∃ s : Spec (Y.residueField (f x)) ⟶ X, s ≫ f = Y.fromSpecResidueField (f x) := by
  have hs : Function.Surjective (f.residueFieldMap x).hom := by
    intro a
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective a
    obtain ⟨c, rfl⟩ := f.stalkMap_surjective x b
    exact ⟨IsLocalRing.residue _ c, rfl⟩
  have : IsIso (f.residueFieldMap x) :=
    (ConcreteCategory.isIso_iff_bijective _).2 ⟨(f.residueFieldMap x).hom.injective, hs⟩
  refine ⟨Spec.map (inv (f.residueFieldMap x)) ≫ X.fromSpecResidueField x, ?_⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
    ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))

theorem finite_Bt : Module.Finite O (Bt P' x0 hu) := by
  haveI := P'.fin.finite
  exact inferInstanceAs (Module.Finite (OL P' x0 hu) (OL P' x0 hu ⊗[Localization.Away P'.f] P'.B))

theorem free_Bt : Module.Free O (Bt P' x0 hu) := by
  haveI := P'.fin.free
  exact inferInstanceAs (Module.Free (OL P' x0 hu) (OL P' x0 hu ⊗[Localization.Away P'.f] P'.B))

end

theorem isOpenImmersion_jH : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (p : ℕ) [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)] (P' : GlobalTheory.HTMap.FP t ξ (p ^ n)) (x0 : R →+* 𝓞_ℂ_[p]) (hu : IsUnit (x0 P'.f)) (P : PtP E p) (π : P.G.left ⟶ t.G.left) (hg : IsGrpPullback P.G t.G (spMap x0 ≫ ξ) π) (h : aH P' x0 hu hg.1 ^ (p ^ n) = 1), IsOpenImmersion (jH P' x0 hu hg.1 h).left := by
  intro E _ _ _ H X t R _ ξ p _ n _ P' x0 hu P π hg h
  set j := jH P' x0 hu hg.1 h
  haveI := P.semi.separated
  haveI := P.semi.smooth
  have hm : Mono j.left := by
    haveI := GlobalTheory.T.mono_finite_part_pullback P' x0 hu hg.1
    have e : j.left ≫ (torsion.ι P.G (p ^ n)).left = (aH P' x0 hu hg.1).left := by
      rw [← Over.comp_left, jH_ι]
    exact mono_of_mono_fac e
  have H0 : IsPullback (torsion.ι P.G (p ^ n)).left (torsion P.G (p ^ n)).hom (mulN P.G (p ^ n)).left η[P.G].left := by
    have h := (IsPullback.of_hasPullback (mulN P.G (p ^ n)) (η : 𝟙_ _ ⟶ P.G)).map (Over.forget _)
    have h' : (pullback.snd (mulN P.G (p ^ n)) (η : 𝟙_ _ ⟶ P.G)).left = (torsion P.G (p ^ n)).hom :=
      (Category.comp_id _).symm.trans (Over.w (pullback.snd (mulN P.G (p ^ n)) (η : 𝟙_ _ ⟶ P.G)))
    exact h' ▸ h
  have : LocallyOfFinitePresentation ((mulN P.G (p ^ n)).left ≫ P.G.hom) := by rw [Over.w]; infer_instance
  have h3 := GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp (mulN P.G (p ^ n)).left P.G.hom
  have : IsSeparated ((mulN P.G (p ^ n)).left ≫ P.G.hom) := by rw [Over.w]; infer_instance
  have h4 := IsSeparated.of_comp (mulN P.G (p ^ n)).left P.G.hom
  have hZlfp : LocallyOfFinitePresentation (torsion P.G (p ^ n)).hom :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) H0 h3
  have hZsep : IsSeparated (torsion P.G (p ^ n)).hom :=
    MorphismProperty.of_isPullback (P := @IsSeparated) H0 h4
  haveI := finite_Bt P' x0 hu
  haveI := free_Bt P' x0 hu
  have hHfin : IsFinite (Hs P' x0 hu).hom := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] (Bt P' x0 hu))))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 inferInstance
  have hHlfp : LocallyOfFinitePresentation (Hs P' x0 hu).hom := by
    change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] (Bt P' x0 hu))))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    haveI : Module.FinitePresentation 𝓞_ℂ_[p] (Bt P' x0 hu) := Module.finitePresentation_of_projective _ _
    exact RingHom.finitePresentation_algebraMap.2 (Algebra.FinitePresentation.of_finitePresentation _ _)
  have hc : j.left ≫ (torsion P.G (p ^ n)).hom = (Hs P' x0 hu).hom := Over.w j
  have : IsFinite (j.left ≫ (torsion P.G (p ^ n)).hom) := by rw [hc]; exact hHfin
  have : LocallyOfFinitePresentation (j.left ≫ (torsion P.G (p ^ n)).hom) := by rw [hc]; exact hHlfp
  have : IsFinite j.left := IsFinite.of_comp j.left (torsion P.G (p ^ n)).hom
  have : IsClosedImmersion j.left := (IsClosedImmersion.iff_isFinite_and_mono _).2 ⟨inferInstance, hm⟩
  have : LocallyOfFinitePresentation j.left :=
    GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp j.left (torsion P.G (p ^ n)).hom
  refine isOpenImmersion_of_stalk j.left fun x => ?_
  obtain ⟨s, hs⟩ := residue_lift j.left x
  haveI : IsLocalRing ((torsion P.G (p ^ n)).left.presheaf.stalk (j.left x)) :=
    LocallyRingedSpace.isLocalRing _ _
  exact GlobalTheory.T.finite_part_pow_eq_one_local P' x0 hu hg h ((torsion P.G (p ^ n)).left.presheaf.stalk (j.left x)) (hS := this)
    ((torsion P.G (p ^ n)).left.fromSpecStalk (j.left x)) ⟨s, hs⟩

end GlobalTheory.FinPartOpen
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_map_open_immersion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (p : ℕ) [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)] (P' : GlobalTheory.HTMap.FP t ξ (p ^ n)) (x0 : R →+* 𝓞_ℂ_[p]) (hu : IsUnit (x0 P'.f)) (P : PtP E p) (π : P.G.left ⟶ t.G.left) (hg : IsGrpPullback P.G t.G (spMap x0 ≫ ξ) π) (h : aH P' x0 hu hg.1 ^ (p ^ n) = 1), IsOpenImmersion (jH P' x0 hu hg.1 h).left := by
  atlas_forward_decl GlobalTheory.FinPartOpen.isOpenImmersion_jH
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

theorem hs_isFinite (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X)
    (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O)
    (hu : IsUnit (x0 P'.f)) : IsFinite (Hs P' x0 hu).hom := by
  haveI : Module.Finite (Localization.Away P'.f) P'.B := P'.fin.finite
  haveI : Module.Finite (OL P' x0 hu) (Bt P' x0 hu) := Module.Finite.base_change _ _ _
  haveI : Module.Finite O (OL P' x0 hu) := inferInstanceAs (Module.Finite O O)
  haveI : Module.Finite O (Bt P' x0 hu) := Module.Finite.trans (OL P' x0 hu) (Bt P' x0 hu)
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap O (Bt P' x0 hu))))
  rw [IsFinite.SpecMap_iff]
  rw [CommRingCat.hom_ofHom]
  exact RingHom.finite_algebraMap.mpr inferInstance

end GlobalTheory.FinPartAt
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_scheme_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)), IsFinite (Hs P' x0 hu).hom := by
  atlas_forward_decl GlobalTheory.FinPartAt.hs_isFinite
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))

theorem flat_Bt : Module.Flat O (Bt P' x0 hu) := by
  haveI : Module.Free (Localization.Away P'.f) P'.B := P'.fin.free
  haveI : Module.Flat (OL P' x0 hu) (Bt P' x0 hu) := Module.Flat.baseChange _ _ _
  haveI : Module.Flat O (OL P' x0 hu) := inferInstanceAs (Module.Flat O O)
  exact Module.Flat.trans O (OL P' x0 hu) (Bt P' x0 hu)

theorem flat_Hs : Flat (Hs P' x0 hu).hom := by
  haveI := flat_Bt P' x0 hu
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap O (Bt P' x0 hu))))
  rw [Flat.SpecMap_iff]
  exact (RingHom.flat_algebraMap_iff).2 inferInstance

end GlobalTheory.FinPartAt

theorem GlobalTheory.FinPartAt.flat_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)), Flat (Hs P' x0 hu).hom := by
  intro E _ _ _ H X t R _ ξ q P' O _ x0 hu
  exact GlobalTheory.FinPartAt.flat_Hs P' x0 hu
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_scheme_flat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)), Flat (Hs P' x0 hu).hom := by
  atlas_forward_decl GlobalTheory.FinPartAt.flat_main
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))

theorem aH_left_π_ptMap {G' : Over (Sp O)} {π : G'.left ⟶ t.G.left}
    (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)) {D : Type} [CommRing D] [Algebra O D]
    (a : Bt P' x0 hu →ₐ[O] D) :
    (ptMap a ≫ aH P' x0 hu hπ).left ≫ π = spMap (a.toRingHom.comp (inB P' x0 hu)) ≫ P'.u.left := by
  rw [Over.comp_left, Category.assoc, aH_left_π]
  change spMap a.toRingHom ≫ spMap (inB P' x0 hu) ≫ P'.u.left = _
  rw [GlobalTheory.HTMap.spc_assoc]

theorem str_of_alg {D : Type} [CommRing D] [Algebra O D] (a : Bt P' x0 hu →ₐ[O] D) :
    (a.toRingHom.comp (inB P' x0 hu)).comp P'.str = (algebraMap O D).comp x0 := by
  rw [RingHom.comp_assoc, inB_str, ← RingHom.comp_assoc]
  congr 1
  exact a.comp_algebraMap

theorem at_alg {D : Type} [CommRing D] [Algebra O D] (a : Bt P' x0 hu →ₐ[O] D) :
    P'.At ((algebraMap O D).comp x0) (spMap (a.toRingHom.comp (inB P' x0 hu)) ≫ P'.u.left)
      (a.toRingHom.comp (inB P' x0 hu)) :=
  ⟨str_of_alg P' x0 hu a, rfl⟩

theorem exists_mul_affine {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left}
    (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) {D : Type} [CommRing D] [Algebra O D]
    (a b : Bt P' x0 hu →ₐ[O] D) :
    ∃ z : specO O D ⟶ Hs P' x0 hu, z ≫ aH P' x0 hu hg.1 =
      (ptMap a ≫ aH P' x0 hu hg.1) * (ptMap b ≫ aH P' x0 hu hg.1) := by
  have ha := at_alg P' x0 hu a
  have hb := at_alg P' x0 hu b
  let w₁ : Over.mk ((specO O D).hom ≫ spMap x0 ≫ ξ) ⟶ t.G :=
    GlobalTheory.HTMap.mkPt _ (ha.over.trans (GlobalTheory.HTMap.spc_assoc _ _ _).symm)
  let w₂ : Over.mk ((specO O D).hom ≫ spMap x0 ≫ ξ) ⟶ t.G :=
    GlobalTheory.HTMap.mkPt _ (hb.over.trans (GlobalTheory.HTMap.spc_assoc _ _ _).symm)
  obtain ⟨β'', h''⟩ := GlobalTheory.HTMap.FP.At.mul (w := w₁) (w' := w₂) ha hb
  refine ⟨ptOf P' x0 hu β'' h''.1, ?_⟩
  refine Over.OverMorphism.ext (hg.1.hom_ext ?_ ?_)
  · rw [ptOf_aH_π, h''.2]
    exact hg.2 (specO O D) _ _ w₁ w₂ (aH_left_π_ptMap P' x0 hu hg.1 a).symm
      (aH_left_π_ptMap P' x0 hu hg.1 b).symm
  · rw [Over.w, Over.w]

end GlobalTheory.FinPartAt

namespace GlobalTheory.FinPartAt

theorem exists_mul_factor {O : Type} [CommRing O] {C : Type} [CommRing C] [Algebra O C] (S : Over (Sp O))
    (x y : S ⟶ specO O C) :
    ∃ c : S ⟶ specO O (C ⊗[O] C),
      c ≫ ptMap (Algebra.TensorProduct.includeLeft : C →ₐ[O] C ⊗[O] C) = x ∧
      c ≫ ptMap (Algebra.TensorProduct.includeRight : C →ₐ[O] C ⊗[O] C) = y := by
  have hxy : x.left ≫ (specO O C).hom = y.left ≫ (specO O C).hom := by rw [Over.w, Over.w]
  let l := pullback.lift x.left y.left hxy ≫ (pullbackSpecIso O C C).hom
  have hl : l ≫ (specO O (C ⊗[O] C)).hom = S.hom := by
    change (pullback.lift x.left y.left hxy ≫ (pullbackSpecIso O C C).hom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap O (C ⊗[O] C))) = _
    rw [Category.assoc, pullbackSpecIso_hom_base, ← Category.assoc]
    erw [pullback.lift_fst]
    exact Over.w x
  refine ⟨Over.homMk l hl, ?_, ?_⟩
  · refine Over.OverMorphism.ext ?_
    change (pullback.lift x.left y.left hxy ≫ (pullbackSpecIso O C C).hom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom)) = _
    rw [Category.assoc, pullbackSpecIso_hom_fst]
    erw [pullback.lift_fst]
  · refine Over.OverMorphism.ext ?_
    change (pullback.lift x.left y.left hxy ≫ (pullbackSpecIso O C C).hom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom)) = _
    rw [Category.assoc]
    erw [pullbackSpecIso_hom_snd]
    erw [pullback.lift_snd]

theorem exists_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) (G' : Over (Sp O)) [GrpObj G'] (π : G'.left ⟶ t.G.left) (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) (S : Over (Sp O)) (x y : S ⟶ Hs P' x0 hu), ∃ z : S ⟶ Hs P' x0 hu, z ≫ aH P' x0 hu hg.1 = (x ≫ aH P' x0 hu hg.1) * (y ≫ aH P' x0 hu hg.1) := by
  intro E _ _ _ H X t R _ ξ q P' O _ x0 hu G' _ π hg S x y
  obtain ⟨c, hc₁, hc₂⟩ := exists_mul_factor S x y
  obtain ⟨z₀, hz₀⟩ := exists_mul_affine P' x0 hu hg
    (Algebra.TensorProduct.includeLeft : Bt P' x0 hu →ₐ[O] Bt P' x0 hu ⊗[O] Bt P' x0 hu)
    Algebra.TensorProduct.includeRight
  refine ⟨c ≫ z₀, ?_⟩
  rw [Category.assoc, hz₀, MonObj.comp_mul, ← Category.assoc, hc₁, ← Category.assoc, hc₂]

end GlobalTheory.FinPartAt
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_difference_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) (G' : Over (Sp O)) [GrpObj G'] (π : G'.left ⟶ t.G.left) (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) (S : Over (Sp O)) (x y : S ⟶ Hs P' x0 hu), ∃ z : S ⟶ Hs P' x0 hu, z ≫ aH P' x0 hu hg.1 = (x ≫ aH P' x0 hu hg.1) * (y ≫ aH P' x0 hu hg.1) := by
  atlas_forward_decl GlobalTheory.FinPartAt.exists_mul
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

theorem eq_ptMap' {O : Type} [CommRing O] {D B : Type} [CommRing D] [Algebra O D] [CommRing B] [Algebra O B]
    (x : specO O D ⟶ specO O B) : ∃ α : B →ₐ[O] D, x = ptMap α := by
  obtain ⟨f, hf⟩ := Spec.map_surjective x.left
  have hw : x.left ≫ (specO O B).hom = (specO O D).hom := Over.w x
  rw [← hf] at hw
  change Spec.map f ≫ Spec.map (CommRingCat.ofHom (algebraMap O B)) = Spec.map (CommRingCat.ofHom (algebraMap O D)) at hw
  rw [← Spec.map_comp] at hw
  have hc := Spec.map_injective hw
  refine ⟨{ f.hom with commutes' := fun c => congrArg (fun g : CommRingCat.of O ⟶ CommRingCat.of D => g.hom c) hc }, ?_⟩
  ext1
  rw [← hf]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))
  {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left}

theorem at_ptMap {D : Type} [CommRing D] [Algebra O D] (α : Bt P' x0 hu →ₐ[O] D)
    (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)) :
    P'.At ((algebraMap O D).comp x0) ((ptMap α ≫ aH P' x0 hu hπ).left ≫ π) (α.toRingHom.comp (inB P' x0 hu)) := by
  refine ⟨?_, ?_⟩
  · rw [RingHom.comp_assoc, inB_str]
    exact RingHom.ext fun r => α.commutes (x0 r)
  · rw [Over.comp_left, Category.assoc, aH_left_π]
    change spMap _ ≫ P'.u.left = spMap α.toRingHom ≫ spMap (inB P' x0 hu) ≫ P'.u.left
    exact (GlobalTheory.HTMap.spc_assoc _ _ _).symm

theorem unitOf_ptMap_chi {D : Type} [CommRing D] [Algebra O D] (α : Bt P' x0 hu →ₐ[O] D) (b : P'.Bˣ) :
    (unitOf (ptMap α ≫ chi P' x0 hu b) : D) = α (inB P' x0 hu b) := by
  rw [GlobalTheory.GmPoints.unitOf_ptMap, unitOf_chi]
  rfl

end GlobalTheory.FinPartAt

namespace GlobalTheory.FinPartAt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))
  {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left}

theorem chi_mul_aff (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) {κ : (Sp (FractionRing R) ⟶ t.G.left) → Rˣ}
    {b : P'.Bˣ} (hb : P'.Gl κ b) {D : Type} [CommRing D] [Algebra O D] (x y z : specO O D ⟶ Hs P' x0 hu)
    (h : z ≫ aH P' x0 hu hg.1 = (x ≫ aH P' x0 hu hg.1) * (y ≫ aH P' x0 hu hg.1)) :
    z ≫ chi P' x0 hu b = (x ≫ chi P' x0 hu b) * (y ≫ chi P' x0 hu b) := by
  obtain ⟨αx, rfl⟩ := eq_ptMap' x
  obtain ⟨αy, rfl⟩ := eq_ptMap' y
  obtain ⟨αz, rfl⟩ := eq_ptMap' z
  have hw : ∀ α : Bt P' x0 hu →ₐ[O] D,
      ((ptMap α ≫ aH P' x0 hu hg.1).left ≫ π) ≫ t.G.hom = (specO O D).hom ≫ spMap x0 ≫ ξ := fun α => by
    rw [Category.assoc, hg.1.w, ← Category.assoc, Over.w]
  let w : (Bt P' x0 hu →ₐ[O] D) → (Over.mk ((specO O D).hom ≫ spMap x0 ≫ ξ) ⟶ t.G) := fun α =>
    Over.homMk _ (hw α)
  have hm := hg.2 (specO O D) (ptMap αx ≫ aH P' x0 hu hg.1) (ptMap αy ≫ aH P' x0 hu hg.1) (w αx) (w αy) rfl rfl
  rw [← h] at hm
  have hz : P'.At ((algebraMap O D).comp x0) (w αx * w αy).left (αz.toRingHom.comp (inB P' x0 hu)) := by
    rw [hm]; exact at_ptMap P' x0 hu αz hg.1
  have e := hb.2 D _ _ (w αx) (w αy) _ _ _ (at_ptMap P' x0 hu αx hg.1) (at_ptMap P' x0 hu αy hg.1) hz
  apply GlobalTheory.GmPoints.unitOf_bijective.1
  rw [GlobalTheory.GmPoints.unitOf_mul]
  ext1
  rw [Units.val_mul, unitOf_ptMap_chi, unitOf_ptMap_chi, unitOf_ptMap_chi]
  exact e

end GlobalTheory.FinPartAt

theorem GlobalTheory.FinPartAt.chi_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) (G' : Over (Sp O)) [GrpObj G'] (π : G'.left ⟶ t.G.left) (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) (κ : (Sp (FractionRing R) ⟶ t.G.left) → Rˣ) (b : P'.Bˣ), P'.Gl κ b → ∀ (S : Over (Sp O)) (x y z : S ⟶ Hs P' x0 hu), z ≫ aH P' x0 hu hg.1 = (x ≫ aH P' x0 hu hg.1) * (y ≫ aH P' x0 hu hg.1) → z ≫ chi P' x0 hu b = (x ≫ chi P' x0 hu b) * (y ≫ chi P' x0 hu b) := by
  intro E _ _ _ H X t R _ ξ q P' O _ x0 hu G' _ π hg κ b hb S x y z h
  have loc : ∀ (R' : CommRingCat.{0}) (f : Spec R' ⟶ S.left),
      f ≫ (z ≫ chi P' x0 hu b).left = f ≫ ((x ≫ chi P' x0 hu b) * (y ≫ chi P' x0 hu b)).left := by
    intro R' f
    letI : Algebra O R' := (Spec.preimage (f ≫ S.hom)).hom.toAlgebra
    let c : specO O R' ⟶ S := Over.homMk f (by
      change f ≫ S.hom = Spec.map (CommRingCat.ofHom (Spec.preimage (f ≫ S.hom)).hom)
      rw [CommRingCat.ofHom_hom, Spec.map_preimage])
    have h' : (c ≫ z) ≫ aH P' x0 hu hg.1 = ((c ≫ x) ≫ aH P' x0 hu hg.1) * ((c ≫ y) ≫ aH P' x0 hu hg.1) := by
      rw [Category.assoc, h, MonObj.comp_mul, Category.assoc, Category.assoc]
    have k := GlobalTheory.FinPartAt.chi_mul_aff P' x0 hu hg hb _ _ _ h'
    rw [Category.assoc, Category.assoc, Category.assoc, ← MonObj.comp_mul] at k
    exact congrArg CommaMorphism.left k
  exact Over.OverMorphism.ext (S.left.affineCover.hom_ext _ _ fun i => loc _ _)
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_glued_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) (G' : Over (Sp O)) [GrpObj G'] (π : G'.left ⟶ t.G.left) (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) (κ : (Sp (FractionRing R) ⟶ t.G.left) → Rˣ) (b : P'.Bˣ), P'.Gl κ b → ∀ (S : Over (Sp O)) (x y z : S ⟶ Hs P' x0 hu), z ≫ aH P' x0 hu hg.1 = (x ≫ aH P' x0 hu hg.1) * (y ≫ aH P' x0 hu hg.1) → z ≫ chi P' x0 hu b = (x ≫ chi P' x0 hu b) * (y ≫ chi P' x0 hu b) := by
  first | exact @GlobalTheory.FinPartAt.chi_mul | exact GlobalTheory.FinPartAt.chi_mul | (intros; apply GlobalTheory.FinPartAt.chi_mul <;> assumption)
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

theorem exists_ptMap_eq {O : Type} [CommRing O] {D : Type} [CommRing D] [Algebra O D] (w : specO O O ⟶ specO O D) :
    ∃ φ : D →ₐ[O] O, ptMap φ = w := by
  let f : CommRingCat.of D ⟶ CommRingCat.of O := Spec.preimage w.left
  have hf : Spec.map f = w.left := Spec.map_preimage _
  have hw : w.left ≫ (specO O D).hom = (specO O O).hom := Over.w w
  have hc : ∀ c : O, f.hom (algebraMap O D c) = c := by
    have h2 : Spec.map (CommRingCat.ofHom (algebraMap O D) ≫ f) = Spec.map (CommRingCat.ofHom (algebraMap O O)) := by
      rw [Spec.map_comp, hf]; exact hw
    have h3 := Spec.map_injective h2
    intro c
    have := congrArg (fun g : CommRingCat.of O ⟶ CommRingCat.of O => g.hom c) h3
    simpa using this
  refine ⟨{ f.hom with commutes' := hc }, ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom f.hom) = w.left
  rw [CommRingCat.ofHom_hom, hf]

theorem unitOf_chi_eq_weil : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (p : ℕ) [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)] (P' : GlobalTheory.HTMap.FP t ξ (p ^ n)) (x0 : R →+* 𝓞_ℂ_[p]) (hu : IsUnit (x0 P'.f)) (P : PtP E p) (π : P.G.left ⟶ t.G.left) (hg : IsGrpPullback P.G t.G (spMap x0 ≫ ξ) π) (b : P'.Bˣ) (tt : P.T), (∀ (β : P'.B →+* 𝓞_ℂ_[p]) (w : Sp 𝓞_ℂ_[p] ⟶ t.G.left), P'.At x0 w β → ∀ z : GlobalTheory.ChTor.Pts P.A.A, z.left ≫ P.gen ≫ π = spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ w → algebraMap 𝓞_ℂ_[p] ℂ_[p] (β b) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p])) → ∀ (w : specO 𝓞_ℂ_[p] 𝓞_ℂ_[p] ⟶ Hs P' x0 hu) (z : GlobalTheory.ChTor.Pts P.A.A), z.left ≫ P.gen = spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ (w ≫ aH P' x0 hu hg.1).left → algebraMap 𝓞_ℂ_[p] ℂ_[p] (unitOf (w ≫ chi P' x0 hu b) : 𝓞_ℂ_[p]) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p]) := by
  intro E _ _ _ H X t R _ ξ p _ n _ P' x0 hu P π hg b tt hb w z hz
  obtain ⟨φ, rfl⟩ := exists_ptMap_eq w
  let β : P'.B →+* 𝓞_ℂ_[p] := φ.toRingHom.comp (inB P' x0 hu)
  have hβ1 : β.comp P'.str = x0 := by
    change φ.toRingHom.comp ((inB P' x0 hu).comp P'.str) = x0
    rw [inB_str]
    exact RingHom.ext fun r => φ.commutes (x0 r)
  have hβ2 : spMap β ≫ P'.u.left = (ptMap φ ≫ aH P' x0 hu hg.1).left ≫ π := by
    rw [Over.comp_left, Category.assoc, aH_left_π]
    change _ = spMap φ.toRingHom ≫ spMap (inB P' x0 hu) ≫ P'.u.left
    exact (GlobalTheory.HTMap.spc_assoc _ _ _).symm
  have hat : P'.At x0 ((ptMap φ ≫ aH P' x0 hu hg.1).left ≫ π) β := ⟨hβ1, hβ2⟩
  have hz' : z.left ≫ P.gen ≫ π =
      spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ (ptMap φ ≫ aH P' x0 hu hg.1).left ≫ π := by
    rw [← Category.assoc, hz, Category.assoc]
  have key := hb β _ hat z hz'
  rw [GlobalTheory.GmPoints.unitOf_ptMap, unitOf_chi]
  exact key

end GlobalTheory.FinPartAt
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_unit_torsion_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (p : ℕ) [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)] (P' : GlobalTheory.HTMap.FP t ξ (p ^ n)) (x0 : R →+* 𝓞_ℂ_[p]) (hu : IsUnit (x0 P'.f)) (P : PtP E p) (π : P.G.left ⟶ t.G.left) (hg : IsGrpPullback P.G t.G (spMap x0 ≫ ξ) π) (b : P'.Bˣ) (tt : P.T), (∀ (β : P'.B →+* 𝓞_ℂ_[p]) (w : Sp 𝓞_ℂ_[p] ⟶ t.G.left), P'.At x0 w β → ∀ z : GlobalTheory.ChTor.Pts P.A.A, z.left ≫ P.gen ≫ π = spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ w → algebraMap 𝓞_ℂ_[p] ℂ_[p] (β b) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p])) → ∀ (w : specO 𝓞_ℂ_[p] 𝓞_ℂ_[p] ⟶ Hs P' x0 hu) (z : GlobalTheory.ChTor.Pts P.A.A), z.left ≫ P.gen = spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ (w ≫ aH P' x0 hu hg.1).left → algebraMap 𝓞_ℂ_[p] ℂ_[p] (unitOf (w ≫ chi P' x0 hu b) : 𝓞_ℂ_[p]) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p]) := by
  atlas_forward_decl GlobalTheory.FinPartAt.unitOf_chi_eq_weil
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory

attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

set_option maxHeartbeats 1000000 in

theorem levelHT_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ)
    [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)] (R : Type) [CommRing R] [IsDomain R] (ξ : Sp R ⟶ Y.X) (g : ℕ)
    (e : Fin g → (Sp (DualNumber R) ⟶ Y.t.G.left)), IsTanBasis Y.t ξ e →
    ∀ (P' : GlobalTheory.HTMap.FP Y.t ξ (p ^ n)) (κ : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ) (b : P'.Bˣ), P'.Gl κ b →
    ∀ x0 : R →+* 𝓞_ℂ_[p], P'.Full ((IsLocalRing.maximalIdeal 𝓞_ℂ_[p]).comap x0) →
    ∀ (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left),
      PtOn Y (spMap x0 ≫ ξ) yy P π ψ → GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.LevelReduction P → ∀ tt : P.T,
      (∀ (β : P'.B →+* 𝓞_ℂ_[p]) (w : Sp 𝓞_ℂ_[p] ⟶ Y.t.G.left), P'.At x0 w β →
        ∀ z : GlobalTheory.ChTor.Pts P.A.A, z.left ≫ P.gen ≫ π = spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ w →
          algebraMap 𝓞_ℂ_[p] ℂ_[p] (β b) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p])) →
    ∀ hvec : Fin g → 𝓞_ℂ_[p],
      (∀ (k : Fin g) (β : P'.B →+* DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n})),
        P'.At ((algebraMap 𝓞_ℂ_[p] (DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))).comp x0)
          (spMap (dualMap (Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))) ≫ spMap (dualMap x0) ≫ e k) β →
        (β b).snd = Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) (hvec k)) →
    ∀ (k : Fin g) (x : LieG P.Gt), ITie P π x (spMap (dualMap x0) ≫ e k) →
      hvec k + (P.al₀ tt).1 x ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n} := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ n _ R _ _ ξ g e he P' κ b hb x0 hF yy P π ψ hOn hLR tt hW hvec hD k x hI
  have hu : IsUnit (x0 P'.f) := by
    by_contra hn
    exact hF.1 (Ideal.mem_comap.2 ((IsLocalRing.mem_maximalIdeal _).2 hn))
  have hg := hOn.2.1
  have htors := GlobalTheory.T.hodge_tate_map_pow_eq_one E H Y.X Y.t R ξ (p ^ n) P' 𝓞_ℂ_[p] x0 hu P.G π hg
  have hι := jH_ι P' x0 hu hg.1 htors
  have hOFF : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.IsOpenFiniteFlatSubgroup P.G (p ^ n) (jH P' x0 hu hg.1 htors) := by
    refine ⟨GlobalTheory.T.hodge_tate_map_open_immersion E H Y.X Y.t R ξ p n P' x0 hu P π hg htors, GlobalTheory.T.hodge_tate_scheme_finite E H Y.X Y.t R ξ (p ^ n) P' _ x0 hu,
      GlobalTheory.T.hodge_tate_scheme_flat E H Y.X Y.t R ξ (p ^ n) P' _ x0 hu, fun S => ?_, fun S x y => ?_, fun S x => ?_⟩
    · obtain ⟨z, hz⟩ := exists_unit P' x0 hu hg S
      exact ⟨z, by rw [hι, hz]⟩
    · obtain ⟨z, hz⟩ := GlobalTheory.T.hodge_tate_difference_section E H Y.X Y.t R ξ (p ^ n) P' _ x0 hu P.G π hg S x y
      exact ⟨z, by rw [hι, hz]⟩
    · have key : ∀ m : ℕ, ∃ z : S ⟶ Hs P' x0 hu, z ≫ aH P' x0 hu hg.1 = (x ≫ aH P' x0 hu hg.1) ^ m := by
        intro m
        induction m with
        | zero =>
          obtain ⟨z, hz⟩ := exists_unit P' x0 hu hg S
          exact ⟨z, by rw [hz, pow_zero]⟩
        | succ m ih =>
          obtain ⟨z, hz⟩ := ih
          obtain ⟨z', hz'⟩ := GlobalTheory.T.hodge_tate_difference_section E H Y.X Y.t R ξ (p ^ n) P' _ x0 hu P.G π hg S z x
          exact ⟨z', by rw [hz', hz, pow_succ]⟩
      have hpos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
      obtain ⟨z, hz⟩ := key (p ^ n - 1)
      refine ⟨z, ?_⟩
      rw [hι, hz]
      symm
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel hpos, ← MonObj.comp_pow, htors, MonObj.comp_one]
  have hChar : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.IsCharacter P.G (p ^ n) (jH P' x0 hu hg.1 htors) (chi P' x0 hu b) :=
    fun S x y z h => GlobalTheory.T.hodge_tate_glued_section E H Y.X Y.t R ξ (p ^ n) P' _ x0 hu P.G π hg κ b hb S x y z (by rwa [hι] at h)
  have hExt : ∀ (w : specO 𝓞_ℂ_[p] 𝓞_ℂ_[p] ⟶ Hs P' x0 hu) (z : GlobalTheory.ChTor.Pts P.A.A),
      z.left ≫ P.gen = spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ (w ≫ jH P' x0 hu hg.1 htors ≫ torsion.ι P.G (p ^ n)).left →
        algebraMap 𝓞_ℂ_[p] ℂ_[p] (unitOf (w ≫ chi P' x0 hu b) : 𝓞_ℂ_[p]) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p]) := by
    intro w z hz
    rw [hι] at hz
    exact GlobalTheory.T.hodge_tate_unit_torsion_point E H Y.X Y.t R ξ p n P' x0 hu P π hg b tt hW w z hz
  have hR : (p : 𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) ^ n = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨xG, hC, hxG⟩ := hI
  have hv0 : IsTanAtG Y.t (spMap ((Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n})).comp x0) ≫ ξ)
      (spMap (dualMap ((Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n})).comp x0)) ≫ e k) :=
    GlobalTheory.FactorDepth.isTanAtG_map Y.t _ (he.1 k)
  have hq : ((p ^ n : ℕ) : 𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) = 0 := GlobalTheory.HTMap.cast_quot _ p n
  have hu' : IsUnit ((RingHom.id (DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n})))
      (((algebraMap (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) (DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))).comp
        ((Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n})).comp x0)) P'.f)) :=
    hu.map ((RingHom.id _).comp ((algebraMap _ (DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))).comp
      (Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))))
  obtain ⟨β, hβ⟩ := GlobalTheory.HTMap.tan_at P' hv0 hq (RingHom.id _) hu'
  have e1 : (RingHom.id (DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))).comp
      ((algebraMap (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) (DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))).comp
        ((Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n})).comp x0)) =
      (algebraMap 𝓞_ℂ_[p] (DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))).comp x0 :=
    by rw [RingHom.id_comp, ← RingHom.comp_assoc]; exact congrArg (fun f => RingHom.comp f x0) (alg_dual_mk _)
  have e2 : spMap (RingHom.id (DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))) ≫
      spMap (dualMap ((Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n})).comp x0)) ≫ e k =
      spMap (dualMap (Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))) ≫ spMap (dualMap x0) ≫ e k := by
    rw [show spMap (RingHom.id (DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))) = 𝟙 _ from Spec.map_id _,
      Category.id_comp, GlobalTheory.HTMap.spc_assoc (dualMap x0) (dualMap (Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))) (e k),
      GlobalTheory.HTMap.dual_comp]
  rw [e1, e2] at hβ
  have h2 := hD k β hβ
  have hcmp := cmp_of_corr P n hC (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.isNilpotent_dual hR)
  have hw : ptOf P' x0 hu β hβ.1 ≫ jH P' x0 hu hg.1 htors ≫ torsion.ι P.G (p ^ n) =
      P.cmp _ (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.isNilpotent_dual hR)
        (ptMap (dualBC (Algebra.ofId 𝓞_ℂ_[p] (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))) ≫ x.1) := by
    rw [hι, hcmp]
    refine Over.OverMorphism.ext (hg.1.hom_ext ?_ ?_)
    · rw [ptOf_aH_π, hβ.2, Over.comp_left, Category.assoc, hxG, ptMap_dualBC_left]
    · rw [Over.w, Over.w]
  have h1 := hLR n (Hs P' x0 hu) (jH P' x0 hu hg.1 htors) hOFF tt (chi P' x0 hu b) hChar hExt
    (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) hR x (ptOf P' x0 hu β hβ.1) hw
  rw [unitOf_ptOf_chi] at h1
  have h3 := congrArg TrivSqZeroExt.snd h1
  rw [h2, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
    Ideal.Quotient.algebraMap_eq] at h3
  have h4 : (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.alLeft P tt).1 x = -((P.al₀ tt).1 x) := rfl
  rw [h4, Ideal.Quotient.eq, sub_neg_eq_add] at h3
  exact h3

end GlobalTheory.FinPartAt
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_basis_frame_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ)
    [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)] (R : Type) [CommRing R] [IsDomain R] (ξ : Sp R ⟶ Y.X) (g : ℕ)
    (e : Fin g → (Sp (DualNumber R) ⟶ Y.t.G.left)), IsTanBasis Y.t ξ e →
    ∀ (P' : GlobalTheory.HTMap.FP Y.t ξ (p ^ n)) (κ : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ) (b : P'.Bˣ), P'.Gl κ b →
    ∀ x0 : R →+* 𝓞_ℂ_[p], P'.Full ((IsLocalRing.maximalIdeal 𝓞_ℂ_[p]).comap x0) →
    ∀ (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left),
      PtOn Y (spMap x0 ≫ ξ) yy P π ψ → GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.LevelReduction P → ∀ tt : P.T,
      (∀ (β : P'.B →+* 𝓞_ℂ_[p]) (w : Sp 𝓞_ℂ_[p] ⟶ Y.t.G.left), P'.At x0 w β →
        ∀ z : GlobalTheory.ChTor.Pts P.A.A, z.left ≫ P.gen ≫ π = spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ w →
          algebraMap 𝓞_ℂ_[p] ℂ_[p] (β b) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p])) →
    ∀ hvec : Fin g → 𝓞_ℂ_[p],
      (∀ (k : Fin g) (β : P'.B →+* DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n})),
        P'.At ((algebraMap 𝓞_ℂ_[p] (DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))).comp x0)
          (spMap (dualMap (Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))) ≫ spMap (dualMap x0) ≫ e k) β →
        (β b).snd = Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) (hvec k)) →
    ∀ (k : Fin g) (x : LieG P.Gt), ITie P π x (spMap (dualMap x0) ≫ e k) →
      hvec k + (P.al₀ tt).1 x ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n} := by
  atlas_forward_decl GlobalTheory.FinPartAt.levelHT_at_point
end
end
