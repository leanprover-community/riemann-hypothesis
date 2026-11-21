import Mathlib
import GroundTheory.TateCohomology.AugmentationSES
import GroundTheory.TateCohomology.TateLow

section
set_option maxSynthPendingDepth 1

open CategoryTheory MonoidalCategory groupCohomology

namespace GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Exactness

variable {E : ShortComplex (Rep.{u} k G)} (hE : E.ShortExact)
include hE

theorem shortExact_tensorRight_tensor (B V : Rep.{u} k G) [Module.Flat k V.V]
    (hEB : (E.map (tensorRight B)).ShortExact) : (E.map (tensorRight (V ⊗ B))).ShortExact :=
  shortExact_map_tensorRight hE (V ⊗ B) (injective_whiskerRight_tensor_of_flat V E.f B
    ((Rep.mono_iff_injective _).1 hEB.mono_f))

theorem shortExact_tensorLeft_of_flat (V : Rep.{u} k G) [Module.Flat k V.V] :
    (E.map (tensorLeft V)).ShortExact :=
  shortExact_map_tensorLeft hE V (injective_whiskerLeft_of_flat V E.f
    ((Rep.mono_iff_injective _).1 hE.mono_f))

theorem shortExact_tensorLeft_tensorRight (B V : Rep.{u} k G) [Module.Flat k V.V]
    (hEB : (E.map (tensorRight B)).ShortExact) :
    ((E.map (tensorLeft V)).map (tensorRight B)).ShortExact :=
  shortExact_map_tensorRight (shortExact_tensorLeft_of_flat hE V) B
    (injective_whiskerLeft_whiskerRight_of_flat V E.f B ((Rep.mono_iff_injective _).1 hEB.mono_f))

theorem shortExact_tensorLeft_tensor (A V : Rep.{u} k G) [Module.Flat k V.V]
    (hAE : (E.map (tensorLeft A)).ShortExact) : (E.map (tensorLeft (V ⊗ A))).ShortExact :=
  shortExact_map_tensorLeft hE (V ⊗ A) (injective_tensor_whiskerLeft_of_flat V E.f A
    ((Rep.mono_iff_injective _).1 hAE.mono_f))

theorem shortExact_tensorLeft_tensorLeft (A V : Rep.{u} k G) [Module.Flat k V.V]
    (hAE : (E.map (tensorLeft A)).ShortExact) :
    ((E.map (tensorLeft V)).map (tensorLeft A)).ShortExact :=
  shortExact_map_tensorLeft (shortExact_tensorLeft_of_flat hE V) A
    (injective_whiskerLeft_whiskerLeft_of_flat V E.f A ((Rep.mono_iff_injective _).1 hAE.mono_f))

end Exactness

variable [Fintype G]

def tsgn (k : Type u) [CommRing k] (p : ℤ) : k := ((p.negOnePow : ℤˣ) : ℤ)

theorem tsgn_add_one (p : ℤ) : tsgn k (p + 1) = -tsgn k p := by
  simp [tsgn, Int.negOnePow_succ]

theorem tsgn_natCast (n : ℕ) : tsgn k n = (-1 : k) ^ n := by
  induction n with
  | zero => simp [tsgn]
  | succ n ih => rw [Nat.cast_succ, tsgn_add_one, ih, pow_succ, mul_neg_one]

abbrev TateCupFam (k G : Type u) [CommRing k] [Group G] [Fintype G] (p q : ℤ) : Type (u + 1) :=
  ∀ (A B : Rep.{u} k G) (r : ℤ), p + q = r →
    tateCohomology A p →ₗ[k] tateCohomology B q →ₗ[k] tateCohomology (A ⊗ B) r

noncomputable def tateLeftIso (A B : Rep.{u} k G) (r : ℤ) :
    tateCohomology (A ⊗ B) r ≅ tateCohomology ((augIdeal k G ⊗ A) ⊗ B) (r + 1) :=
  @asIso _ _ _ _ (tδ (augSES_tensorRight_shortExact A B) r (r + 1) rfl)
    (isIso_tδ_of_tateAcyclic (augSES_tensorRight_shortExact A B)
      (tateAcyclic_augSES_tensorRight_X₂ A B) r (r + 1) rfl)

noncomputable def tateRightIso (A B : Rep.{u} k G) (r : ℤ) :
    tateCohomology (A ⊗ B) r ≅ tateCohomology (A ⊗ (augIdeal k G ⊗ B)) (r + 1) :=
  @asIso _ _ _ _ (tδ (augSES_tensorLeft_shortExact A B) r (r + 1) rfl)
    (isIso_tδ_of_tateAcyclic (augSES_tensorLeft_shortExact A B)
      (tateAcyclic_augSES_tensorLeft_X₂ A B) r (r + 1) rfl)

noncomputable abbrev augShiftδ (A : Rep.{u} k G) (p : ℤ) :
    tateCohomology A p ⟶ tateCohomology (augIdeal k G ⊗ A) (p + 1) :=
  tδ (augSES_shortExact A) p (p + 1) rfl

noncomputable def tateCupL {p q : ℤ} (μ : TateCupFam k G (p + 1) q) : TateCupFam k G p q := fun A B r h =>
  ((μ (augIdeal k G ⊗ A) B (r + 1) (by omega)).comp (augShiftδ A p).hom).compr₂ (tateLeftIso A B r).inv.hom

noncomputable def tateCupR {p q : ℤ} (μ : TateCupFam k G p (q + 1)) : TateCupFam k G p q := fun A B r h =>
  tsgn k p • ((μ A (augIdeal k G ⊗ B) (r + 1) (by omega)).compl₂ (augShiftδ B q).hom).compr₂
    (tateRightIso A B r).inv.hom

noncomputable def tateCupBase (p q : ℤ) (hp : 1 ≤ p) (hq : 1 ≤ q) : TateCupFam k G p q := fun A B r h =>
  haveI : NeZero p.toNat := ⟨by omega⟩
  haveI : NeZero q.toNat := ⟨by omega⟩
  haveI : NeZero r.toNat := ⟨by omega⟩
  ((cupH (A := A) (B := B) (show p.toNat + q.toNat = r.toNat by omega)).compl₁₂
    (tateIsoH A p p.toNat (by omega)).hom.hom (tateIsoH B q q.toNat (by omega)).hom.hom).compr₂
    (tateIsoH (A ⊗ B) r r.toNat (by omega)).inv.hom

noncomputable def tateCup (p q : ℤ) : TateCupFam k G p q :=
  if hp : p ≤ 0 then tateCupL (tateCup (p + 1) q)
  else if hq : q ≤ 0 then tateCupR (tateCup p (q + 1))
  else tateCupBase p q (by omega) (by omega)
termination_by (1 - p).toNat + (1 - q).toNat
decreasing_by all_goals omega

theorem tateCup_of_nonpos {p : ℤ} (q : ℤ) (hp : p ≤ 0) : tateCup (k := k) (G := G) p q = tateCupL (tateCup (p + 1) q) := by
  rw [tateCup, dif_pos hp]

theorem tateCup_of_pos_of_nonpos {p q : ℤ} (hp : 0 < p) (hq : q ≤ 0) :
    tateCup (k := k) (G := G) p q = tateCupR (tateCup p (q + 1)) := by
  rw [tateCup, dif_neg (by omega), dif_pos hq]

theorem tateCup_of_pos {p q : ℤ} (hp : 0 < p) (hq : 0 < q) :
    tateCup (k := k) (G := G) p q = tateCupBase p q (by omega) (by omega) := by
  rw [tateCup, dif_neg (by omega), dif_neg (by omega)]

theorem tateLeftIso_hom (A B : Rep.{u} k G) (r : ℤ) :
    (tateLeftIso A B r).hom = tδ (augSES_tensorRight_shortExact A B) r (r + 1) rfl := rfl

theorem tateRightIso_hom (A B : Rep.{u} k G) (r : ℤ) :
    (tateRightIso A B r).hom = tδ (augSES_tensorLeft_shortExact A B) r (r + 1) rfl := rfl

theorem tateLeftIso_cupL {p q : ℤ} (μ : TateCupFam k G (p + 1) q) (A B : Rep.{u} k G) (r : ℤ)
    (h : p + q = r) (a : tateCohomology A p) (b : tateCohomology B q) :
    (tateLeftIso A B r).hom.hom (tateCupL μ A B r h a b) =
      μ (augIdeal k G ⊗ A) B (r + 1) (by omega) ((augShiftδ A p).hom a) b := by
  simp only [tateCupL, LinearMap.compr₂_apply, LinearMap.comp_apply]
  exact (tateLeftIso A B r).inv_hom_id_apply _

theorem tateRightIso_cupR {p q : ℤ} (μ : TateCupFam k G p (q + 1)) (A B : Rep.{u} k G) (r : ℤ)
    (h : p + q = r) (a : tateCohomology A p) (b : tateCohomology B q) :
    (tateRightIso A B r).hom.hom (tateCupR μ A B r h a b) =
      tsgn k p • μ A (augIdeal k G ⊗ B) (r + 1) (by omega) a ((augShiftδ B q).hom b) := by
  simp only [tateCupR, LinearMap.smul_apply, LinearMap.compr₂_apply, LinearMap.compl₂_apply, map_smul]
  rw [(tateRightIso A B r).inv_hom_id_apply]

noncomputable def tensorShortComplex (E S : ShortComplex (Rep.{u} k G)) :
    ShortComplex (ShortComplex (Rep.{u} k G)) where
  X₁ := S.map (tensorLeft E.X₁)
  X₂ := S.map (tensorLeft E.X₂)
  X₃ := S.map (tensorLeft E.X₃)
  f :=
    { τ₁ := E.f ▷ S.X₁
      τ₂ := E.f ▷ S.X₂
      τ₃ := E.f ▷ S.X₃
      comm₁₂ := (whisker_exchange E.f S.f).symm
      comm₂₃ := (whisker_exchange E.f S.g).symm }
  g :=
    { τ₁ := E.g ▷ S.X₁
      τ₂ := E.g ▷ S.X₂
      τ₃ := E.g ▷ S.X₃
      comm₁₂ := (whisker_exchange E.g S.f).symm
      comm₂₃ := (whisker_exchange E.g S.g).symm }
  zero := by
    ext : 1
    · change E.f ▷ S.X₁ ≫ E.g ▷ S.X₁ = 0
      rw [← comp_whiskerRight, E.zero, MonoidalPreadditive.zero_whiskerRight]
    · change E.f ▷ S.X₂ ≫ E.g ▷ S.X₂ = 0
      rw [← comp_whiskerRight, E.zero, MonoidalPreadditive.zero_whiskerRight]
    · change E.f ▷ S.X₃ ≫ E.g ▷ S.X₃ = 0
      rw [← comp_whiskerRight, E.zero, MonoidalPreadditive.zero_whiskerRight]

instance : (augSES k G).PreservesZeroMorphisms where
  map_zero _ _ := ShortComplex.hom_ext _ _ (MonoidalPreadditive.whiskerLeft_zero)
    (MonoidalPreadditive.whiskerLeft_zero) rfl

instance (B : Rep.{u} k G) : (tensorRight B).mapShortComplex.PreservesZeroMorphisms where
  map_zero _ _ := ShortComplex.hom_ext _ _ (MonoidalPreadditive.zero_whiskerRight)
    (MonoidalPreadditive.zero_whiskerRight) (MonoidalPreadditive.zero_whiskerRight)

instance (A : Rep.{u} k G) : (tensorLeft A).mapShortComplex.PreservesZeroMorphisms where
  map_zero _ _ := ShortComplex.hom_ext _ _ (MonoidalPreadditive.whiskerLeft_zero)
    (MonoidalPreadditive.whiskerLeft_zero) (MonoidalPreadditive.whiskerLeft_zero)

section Anticomm

variable {E : ShortComplex (Rep.{u} k G)} (hE : E.ShortExact)

set_option backward.isDefEq.respectTransparency false in

theorem tateRightIso_tδ (B : Rep.{u} k G) (hEB : (E.map (tensorRight B)).ShortExact) (r : ℤ)
    (z : tateCohomology (E.X₃ ⊗ B) r) :
    (tateRightIso E.X₁ B (r + 1)).hom.hom ((tδ hEB r (r + 1) rfl).hom z) =
      -(tδ (shortExact_tensorRight_tensor hE B (augIdeal k G) hEB) (r + 1) (r + 1 + 1) rfl).hom
        ((tateRightIso E.X₃ B r).hom.hom z) := by
  have key := tδ_comp_tδ (tensorShortComplex E ((augSES k G).obj B)) (augSES_tensorLeft_shortExact E.X₁ B)
    (augSES_tensorLeft_shortExact E.X₂ B) (augSES_tensorLeft_shortExact E.X₃ B)
    (shortExact_tensorRight_tensor hE B (augIdeal k G) hEB)
    (shortExact_tensorRight_tensor hE B (Rep.leftRegular k G) hEB) hEB r
  have e := congr(($key).hom z)
  exact e

set_option backward.isDefEq.respectTransparency false in

theorem tateLeftIso_tδ (B : Rep.{u} k G) (hEB : (E.map (tensorRight B)).ShortExact) (r : ℤ)
    (z : tateCohomology (E.X₃ ⊗ B) r) :
    (tateLeftIso E.X₁ B (r + 1)).hom.hom ((tδ hEB r (r + 1) rfl).hom z) =
      -(tδ (shortExact_tensorLeft_tensorRight hE B (augIdeal k G) hEB) (r + 1) (r + 1 + 1)
        rfl).hom ((tateLeftIso E.X₃ B r).hom.hom z) := by
  have key := tδ_comp_tδ ((E.map (augSES k G)).map ((tensorRight B).mapShortComplex))
    (augSES_tensorRight_shortExact E.X₁ B) (augSES_tensorRight_shortExact E.X₂ B)
    (augSES_tensorRight_shortExact E.X₃ B)
    (shortExact_tensorLeft_tensorRight hE B (augIdeal k G) hEB)
    (shortExact_tensorLeft_tensorRight hE B (Rep.leftRegular k G) hEB) hEB r
  have e := congr(($key).hom z)
  exact e

set_option backward.isDefEq.respectTransparency false in

theorem augShiftδ_tδ (p : ℤ) (a : tateCohomology E.X₃ p) :
    (augShiftδ E.X₁ (p + 1)).hom ((tδ hE p (p + 1) rfl).hom a) =
      -(tδ (shortExact_tensorLeft_of_flat hE (augIdeal k G)) (p + 1) (p + 1 + 1) rfl).hom
        ((augShiftδ E.X₃ p).hom a) := by
  have key := tδ_comp_tδ (E.map (augSES k G))
    (augSES_shortExact E.X₁) (augSES_shortExact E.X₂) (augSES_shortExact E.X₃)
    (shortExact_tensorLeft_of_flat hE (augIdeal k G))
    (shortExact_tensorLeft_of_flat hE (Rep.leftRegular k G)) hE p
  have e := congr(($key).hom a)
  exact e

set_option backward.isDefEq.respectTransparency false in

theorem tateLeftIso_tδ' (A : Rep.{u} k G) (hAE : (E.map (tensorLeft A)).ShortExact) (r : ℤ)
    (z : tateCohomology (A ⊗ E.X₃) r) :
    (tateLeftIso A E.X₁ (r + 1)).hom.hom ((tδ hAE r (r + 1) rfl).hom z) =
      -(tδ (shortExact_tensorLeft_tensor hE A (augIdeal k G) hAE) (r + 1) (r + 1 + 1) rfl).hom
        ((tateLeftIso A E.X₃ r).hom.hom z) := by
  have key := tδ_comp_tδ (tensorShortComplex ((augSES k G).obj A) E)
    (shortExact_tensorLeft_tensor hE A (augIdeal k G) hAE)
    (shortExact_tensorLeft_tensor hE A (Rep.leftRegular k G) hAE) hAE
    (augSES_tensorRight_shortExact A E.X₁) (augSES_tensorRight_shortExact A E.X₂)
    (augSES_tensorRight_shortExact A E.X₃) r
  have e := congr(($key).hom z)
  exact (neg_eq_iff_eq_neg.mpr e).symm

set_option backward.isDefEq.respectTransparency false in

theorem tateRightIso_tδ' (A : Rep.{u} k G) (hAE : (E.map (tensorLeft A)).ShortExact) (r : ℤ)
    (z : tateCohomology (A ⊗ E.X₃) r) :
    (tateRightIso A E.X₁ (r + 1)).hom.hom ((tδ hAE r (r + 1) rfl).hom z) =
      -(tδ (shortExact_tensorLeft_tensorLeft hE A (augIdeal k G) hAE) (r + 1) (r + 1 + 1)
        rfl).hom ((tateRightIso A E.X₃ r).hom.hom z) := by
  have key := tδ_comp_tδ ((E.map (augSES k G)).map ((tensorLeft A).mapShortComplex))
    (augSES_tensorLeft_shortExact A E.X₁) (augSES_tensorLeft_shortExact A E.X₂)
    (augSES_tensorLeft_shortExact A E.X₃)
    (shortExact_tensorLeft_tensorLeft hE A (augIdeal k G) hAE)
    (shortExact_tensorLeft_tensorLeft hE A (Rep.leftRegular k G) hAE) hAE r
  have e := congr(($key).hom z)
  exact e

end Anticomm

theorem moduleHom_smul {M N : ModuleCat.{u} k} (f : M ⟶ N) (c : k) (y : M) :
    f.hom (c • y) = c • f.hom y :=
  map_smul _ _ _

theorem smul_smul_neg_self {M : ModuleCat.{u} k} (c : k) (x : M) : c • (c • -x) = -(c • (c • x)) := by
  rw [smul_neg, smul_neg]

theorem moduleIso_hom_injective {M N : ModuleCat.{u} k} (e : M ≅ N) : Function.Injective e.hom.hom :=
  fun x y h => by
    have := congrArg e.inv.hom h
    rwa [e.hom_inv_id_apply, e.hom_inv_id_apply] at this

theorem tateIsoH_tateCup {p q r : ℤ} {n m l : ℕ} [NeZero n] [NeZero m] [NeZero l] (hp : p = n)
    (hq : q = m) (hr : r = l) (h : p + q = r) (hl : n + m = l) (A B : Rep.{u} k G)
    (a : tateCohomology A p) (b : tateCohomology B q) :
    (tateIsoH (A ⊗ B) r l hr).hom.hom (tateCup p q A B r h a b) =
      cupH hl ((tateIsoH A p n hp).hom.hom a) ((tateIsoH B q m hq).hom.hom b) := by
  subst hp hq hr
  have hn := NeZero.pos n
  have hm := NeZero.pos m
  rw [tateCup_of_pos (by omega) (by omega)]
  simp only [tateCupBase, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply]
  exact (tateIsoH (A ⊗ B) l l rfl).inv_hom_id_apply _

set_option maxHeartbeats 1600000 in

theorem tateCup_connecting_left (m : ℕ) : ∀ (p q : ℤ), (1 - p).toNat + (1 - q).toNat = m →
    ∀ {E : ShortComplex (Rep.{u} k G)} (hE : E.ShortExact) (B : Rep.{u} k G)
      (hEB : (E.map (tensorRight B)).ShortExact) (r : ℤ) (h : p + q = r)
      (a : tateCohomology E.X₃ p) (b : tateCohomology B q),
      (tδ hEB r (r + 1) rfl).hom (tateCup p q E.X₃ B r h a b) =
        tateCup (p + 1) q E.X₁ B (r + 1) (by omega) ((tδ hE p (p + 1) rfl).hom a) b := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro p q hm E hE B hEB r h a b
  by_cases hp : p ≤ 0
  · rw [tateCup_of_nonpos q hp]
    apply moduleIso_hom_injective (tateLeftIso E.X₁ B (r + 1))
    rw [tateLeftIso_tδ hE B hEB r, tateLeftIso_cupL]
    erw [ih _ (by omega) (p + 1) q rfl (shortExact_tensorLeft_of_flat hE (augIdeal k G)) B
      (shortExact_tensorLeft_tensorRight hE B (augIdeal k G) hEB) (r + 1) (by omega) _ b]
    rw [tateLeftIso_hom]
    erw [ih _ (by omega) (p + 1) q rfl (augSES_shortExact E.X₁) B
      (augSES_tensorRight_shortExact E.X₁ B) (r + 1) (by omega) _ b]
    erw [augShiftδ_tδ hE p a, map_neg, LinearMap.neg_apply]
    rfl
  by_cases hq : q ≤ 0
  · rw [tateCup_of_pos_of_nonpos (by omega) hq, tateCup_of_pos_of_nonpos (p := p + 1) (by omega) hq]
    apply moduleIso_hom_injective (tateRightIso E.X₁ B (r + 1))
    rw [tateRightIso_tδ hE B hEB r, tateRightIso_cupR, tateRightIso_cupR]
    erw [map_smul]
    erw [ih _ (by omega) p (q + 1) rfl hE (augIdeal k G ⊗ B)
      (shortExact_tensorRight_tensor hE B (augIdeal k G) hEB) (r + 1) (by omega) a _]
    rw [tsgn_add_one, neg_smul]
    rfl
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = n := ⟨p.toNat, by omega⟩
    obtain ⟨m', rfl⟩ : ∃ m' : ℕ, q = m' := ⟨q.toNat, by omega⟩
    obtain ⟨l, rfl⟩ : ∃ l : ℕ, r = l := ⟨r.toNat, by omega⟩
    have : NeZero n := ⟨by omega⟩
    have : NeZero m' := ⟨by omega⟩
    have : NeZero l := ⟨by omega⟩
    have hl : n + m' = l := by omega
    apply moduleIso_hom_injective (tateIsoH (E.X₁ ⊗ B) (l + 1) (l + 1) (Nat.cast_succ l).symm)
    have e1 := congr(($(tδ_comp_tateIsoH hEB l)).hom (tateCup n m' E.X₃ B l h a b))
    have e2 := tateIsoH_tateCup rfl rfl rfl h hl E.X₃ B a b
    have e3 := δ_cupH_left' hE B hEB rfl rfl hl (show n + 1 + m' = l + 1 by omega)
      ((tateIsoH E.X₃ n n rfl).hom.hom a) ((tateIsoH B m' m' rfl).hom.hom b)
    have e4 := congr(($(tδ_comp_tateIsoH hE n)).hom a)
    have e5 := tateIsoH_tateCup (n := n + 1) (Nat.cast_succ n).symm rfl (Nat.cast_succ l).symm
      (show (n : ℤ) + 1 + m' = l + 1 by omega) (show n + 1 + m' = l + 1 by omega) E.X₁ B
      ((tδ hE n (n + 1) rfl).hom a) b
    refine e1.trans ?_
    refine (congrArg (δ hEB l (l + 1) rfl).hom e2).trans ?_
    refine e3.trans ?_
    refine (congrArg (fun y => cupH (show n + 1 + m' = l + 1 by omega) y
      ((tateIsoH B m' m' rfl).hom.hom b)) e4.symm).trans ?_
    exact e5.symm

set_option maxHeartbeats 1600000 in

theorem tateCup_connecting_right (m : ℕ) : ∀ (p q : ℤ), (1 - p).toNat + (1 - q).toNat = m →
    ∀ {E : ShortComplex (Rep.{u} k G)} (hE : E.ShortExact) (A : Rep.{u} k G)
      (hAE : (E.map (tensorLeft A)).ShortExact) (r : ℤ) (h : p + q = r)
      (a : tateCohomology A p) (b : tateCohomology E.X₃ q),
      (tδ hAE r (r + 1) rfl).hom (tateCup p q A E.X₃ r h a b) =
        tsgn k p • tateCup p (q + 1) A E.X₁ (r + 1) (by omega) a ((tδ hE q (q + 1) rfl).hom b) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro p q hm E hE A hAE r h a b
  by_cases hp : p ≤ 0
  · rw [tateCup_of_nonpos q hp, tateCup_of_nonpos (q + 1) hp]
    apply moduleIso_hom_injective (tateLeftIso A E.X₁ (r + 1))
    rw [tateLeftIso_tδ' hE A hAE r, tateLeftIso_cupL, moduleHom_smul, tateLeftIso_cupL]
    erw [ih _ (by omega) (p + 1) q rfl hE (augIdeal k G ⊗ A)
      (shortExact_tensorLeft_tensor hE A (augIdeal k G) hAE) (r + 1) (by omega) _ b]
    rw [tsgn_add_one, neg_smul]
    exact neg_neg _
  by_cases hq : q ≤ 0
  · rw [tateCup_of_pos_of_nonpos (by omega) hq]
    apply moduleIso_hom_injective (tateRightIso A E.X₁ (r + 1))
    rw [tateRightIso_tδ' hE A hAE r, tateRightIso_cupR]
    erw [moduleHom_smul, moduleHom_smul]
    erw [ih _ (by omega) p (q + 1) rfl (shortExact_tensorLeft_of_flat hE (augIdeal k G)) A
      (shortExact_tensorLeft_tensorLeft hE A (augIdeal k G) hAE) (r + 1) (by omega) a _]
    rw [tateRightIso_hom]
    erw [ih _ (by omega) p (q + 1) rfl (augSES_shortExact E.X₁) A
      (augSES_tensorLeft_shortExact A E.X₁) (r + 1) (by omega) a _]
    erw [augShiftδ_tδ hE q b, map_neg]
    exact (smul_smul_neg_self _ _).symm
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = n := ⟨p.toNat, by omega⟩
    obtain ⟨m', rfl⟩ : ∃ m' : ℕ, q = m' := ⟨q.toNat, by omega⟩
    obtain ⟨l, rfl⟩ : ∃ l : ℕ, r = l := ⟨r.toNat, by omega⟩
    have : NeZero n := ⟨by omega⟩
    have : NeZero m' := ⟨by omega⟩
    have : NeZero l := ⟨by omega⟩
    have hl : n + m' = l := by omega
    apply moduleIso_hom_injective (tateIsoH (A ⊗ E.X₁) (l + 1) (l + 1) (Nat.cast_succ l).symm)
    have e1 := congr(($(tδ_comp_tateIsoH hAE l)).hom (tateCup n m' A E.X₃ l h a b))
    have e2 := tateIsoH_tateCup rfl rfl rfl h hl A E.X₃ a b
    have e3 := δ_cupH_right' hE A hAE (p := m') rfl rfl hl (show n + (m' + 1) = l + 1 by omega)
      ((tateIsoH A n n rfl).hom.hom a) ((tateIsoH E.X₃ m' m' rfl).hom.hom b)
    have e4 := congr(($(tδ_comp_tateIsoH hE m')).hom b)
    have e5 := tateIsoH_tateCup (m := m' + 1) rfl (Nat.cast_succ m').symm (Nat.cast_succ l).symm
      (show (n : ℤ) + (m' + 1) = l + 1 by omega) (show n + (m' + 1) = l + 1 by omega) A E.X₁
      a ((tδ hE m' (m' + 1) rfl).hom b)
    refine e1.trans ?_
    refine (congrArg (δ hAE l (l + 1) rfl).hom e2).trans ?_
    refine e3.trans ?_
    rw [map_smul, tsgn_natCast]
    congr 1
    refine (congrArg (fun y => cupH (show n + (m' + 1) = l + 1 by omega)
      ((tateIsoH A n n rfl).hom.hom a) y) e4.symm).trans ?_
    exact e5.symm

set_option backward.isDefEq.respectTransparency false in

theorem tateIsoH_tδ_homologyπ {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact) (n : ℕ)
    (z : (tateComplex S.X₃).cycles n) :
    (tateIsoH S.X₁ (n + 1) (n + 1) (Nat.cast_succ n).symm).hom.hom
      ((tδ hS n (n + 1) rfl).hom (((tateComplex S.X₃).homologyπ n).hom z)) =
      δ hS n (n + 1) rfl (π S.X₃ n (cocyclesMk (((tateComplex S.X₃).iCycles n).hom z)
        (tate_d_iCycles _ n z))) := by
  have hz := tate_d_iCycles_int _ _ z
  obtain ⟨y, x, hy, hx⟩ := exists_lift_of_cocycle hS
    (cocyclesMk (((tateComplex S.X₃).iCycles n).hom z) (tate_d_iCycles _ n z))
  have hd : ((tateComplex S.X₁).d (↑n + 1) (↑n + 1 + 1)).hom (iCocycles S.X₁ (n + 1) x) = 0 := by
    have := d_iCocycles x
    rw [← inhomogeneousCochains.d_def] at this
    exact this
  have hy' : ((tateComplex.map S.g).f n).hom y = ((tateComplex S.X₃).iCycles n).hom z :=
    funext fun v => (hy v).trans (congrFun (iCocycles_mk _ _) v)
  have hx' : ((tateComplex.map S.f).f (↑n + 1)).hom (iCocycles S.X₁ (n + 1) x) =
      ((tateComplex S.X₂).d n (n + 1)).hom y := by
    rw [tateComplex_d_ofNat, inhomogeneousCochains.d_def]
    exact funext hx
  have h2 := δ_π_eq hS _ y hy x hx
  have h3 : (tδ hS n (n + 1) rfl).hom (((tateComplex S.X₃).homologyπ n).hom z) =
      ((tateComplex S.X₁).homologyπ (n + 1)).hom
        (tateCyclesMk S.X₁ (n + 1) (iCocycles S.X₁ (n + 1) x) hd) := by
    have e := tδ_apply hS n _ hz y hy' (iCocycles S.X₁ (n + 1) x) hx' hd
    rw [tateCyclesMk_iCycles] at e
    exact e
  have h4 := tateIsoH_homologyπ S.X₁ (n + 1)
    (tateCyclesMk S.X₁ (n + 1) (iCocycles S.X₁ (n + 1) x) hd)
  refine (congrArg (fun w => (tateIsoH S.X₁ (↑n + 1) (n + 1) (Nat.cast_succ n).symm).hom.hom w)
    h3).trans ?_
  refine (h4.trans ?_).trans h2.symm
  congr 1
  apply cocycles_ext
  exact (iCocycles_mk _ _).trans (iCycles_tateCyclesMk _ _ _ _)

end GroundTheory.GroupCoh
end

section
set_option maxSynthPendingDepth 1

open CategoryTheory MonoidalCategory groupCohomology

namespace GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

def tensorInvariants {A B : Rep.{u} k G} (x : A.ρ.invariants) (y : B.ρ.invariants) :
    (A ⊗ B).ρ.invariants :=
  ⟨x.1 ⊗ₜ[k] y.1, fun g => by
    change A.ρ g x.1 ⊗ₜ[k] B.ρ g y.1 = x.1 ⊗ₜ[k] y.1
    rw [x.2 g, y.2 g]⟩

omit [Fintype G] in

theorem cupH_zero_zero_π {A B : Rep.{u} k G} (f : (Fin 0 → G) → A) (g : (Fin 0 → G) → B)
    (hf : (inhomogeneousCochains.d A 0).hom f = 0) (hg : (inhomogeneousCochains.d B 0).hom g = 0)
    (fg : (Fin 0 → G) → (A ⊗ B : Rep k G)) (hfg : (inhomogeneousCochains.d (A ⊗ B) 0).hom fg = 0)
    (h : ∀ v, fg v = f v ⊗ₜ[k] g v) :
    cupH rfl (π A 0 (cocyclesMk f hf)) (π B 0 (cocyclesMk g hg)) = π (A ⊗ B) 0 (cocyclesMk fg hfg) := by
  rw [cupH_π]
  congr 1
  apply cocycles_ext
  rw [iCocycles_cupCocycles, iCocycles_mk, iCocycles_mk, iCocycles_mk]
  funext v
  rw [cupCochain_apply, h]
  have hv : ∀ w : Fin 0 → G, w = v := fun w => Subsingleton.elim _ _
  rw [hv (fun i : Fin 0 => v ⟨i, by omega⟩), hv (fun j : Fin 0 => v ⟨0 + j, by omega⟩)]
  simp [Fin.partialProd]

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in

theorem tateCup_zero_zero (A B : Rep.{u} k G) (x : A.ρ.invariants) (y : B.ρ.invariants) :
    tateCup 0 0 A B 0 (add_zero 0)
        (((tateCohomologyZeroIso k G).app A).inv.hom (Submodule.Quotient.mk x))
        (((tateCohomologyZeroIso k G).app B).inv.hom (Submodule.Quotient.mk y)) =
      ((tateCohomologyZeroIso k G).app (A ⊗ B)).inv.hom
        (Submodule.Quotient.mk (tensorInvariants x y)) := by
  obtain ⟨zA, hzA⟩ := exists_tateComplex_cycles_zero A x
  obtain ⟨zB, hzB⟩ := exists_tateComplex_cycles_zero B y
  obtain ⟨zAB, hzAB⟩ := exists_tateComplex_cycles_zero (A ⊗ B) (tensorInvariants x y)
  rw [tateCohomologyZeroIso_inv_mk A zA x hzA.symm, tateCohomologyZeroIso_inv_mk B zB y hzB.symm,
    tateCohomologyZeroIso_inv_mk (A ⊗ B) zAB _ hzAB.symm]
  rw [tateCup_of_nonpos 0 le_rfl]
  apply moduleIso_hom_injective (tateLeftIso A B 0)
  rw [tateLeftIso_cupL, tateCup_of_pos_of_nonpos (by norm_num) le_rfl]
  apply moduleIso_hom_injective (tateRightIso (augIdeal k G ⊗ A) B (0 + 1))
  rw [tateRightIso_cupR]
  apply moduleIso_hom_injective (tateIsoH ((augIdeal k G ⊗ A) ⊗ (augIdeal k G ⊗ B)) (0 + 1 + 1) 2
    (by norm_num))
  have hA1 := tateIsoH_tδ_homologyπ (augSES_shortExact A) 0 zA
  have hB1 := tateIsoH_tδ_homologyπ (augSES_shortExact B) 0 zB
  have hAB1 := tateIsoH_tδ_homologyπ (augSES_tensorRight_shortExact A B) 0 zAB
  have hxA : ∀ v, ((tateComplex A).iCycles 0).hom zA v = x.1 := fun v => congrFun hzA v
  have hyB : ∀ v, ((tateComplex B).iCycles 0).hom zB v = y.1 := fun v => congrFun hzB v
  have hxyAB : ∀ v, ((tateComplex (A ⊗ B)).iCycles 0).hom zAB v = x.1 ⊗ₜ[k] y.1 :=
    fun v => congrFun hzAB v
  have hcup0 := cupH_zero_zero_π _ _ (tate_d_iCycles A 0 zA) (tate_d_iCycles B 0 zB) _
    (tate_d_iCycles (A ⊗ B) 0 zAB)
    (fun v => (hxyAB v).trans (congrArg₂ (fun a b => a ⊗ₜ[k] b) (hxA v).symm (hyB v).symm))
  have e_left := δ_cupH_left (augSES_shortExact A) B (augSES_tensorRight_shortExact A B)
    (p := 0) (q := 0) rfl rfl
    (π A 0 (cocyclesMk (((tateComplex A).iCycles 0).hom zA) (tate_d_iCycles A 0 zA)))
    (π B 0 (cocyclesMk (((tateComplex B).iCycles 0).hom zB) (tate_d_iCycles B 0 zB)))
  have e_right := δ_cupH_right (augSES_shortExact B) (augIdeal k G ⊗ A)
    (augSES_tensorLeft_shortExact (augIdeal k G ⊗ A) B) (p := 0) (q := 1) rfl rfl
    (δ (augSES_shortExact A) 0 (0 + 1) rfl
      (π A 0 (cocyclesMk (((tateComplex A).iCycles 0).hom zA) (tate_d_iCycles A 0 zA))))
    (π B 0 (cocyclesMk (((tateComplex B).iCycles 0).hom zB) (tate_d_iCycles B 0 zB)))
  have e_br := congr(($(tδ_comp_tateIsoH (augSES_tensorLeft_shortExact (augIdeal k G ⊗ A) B) 1)).hom
    ((tateLeftIso A B 0).hom.hom (((tateComplex (A ⊗ B)).homologyπ 0).hom zAB)))
  have e_base := tateIsoH_tateCup (n := 1) (m := 1) (l := 2) (p := 0 + 1) (q := 0 + 1) (r := 0 + 1 + 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (augIdeal k G ⊗ A) (augIdeal k G ⊗ B) ((augShiftδ A 0).hom (((tateComplex A).homologyπ 0).hom zA))
    ((augShiftδ B 0).hom (((tateComplex B).homologyπ 0).hom zB))
  refine Eq.trans (moduleHom_smul _ _ _) ?_
  refine Eq.trans (congrArg (tsgn k (0 + 1) • ·) e_base) ?_
  refine Eq.trans (congrArg₂ (fun s t => tsgn k (0 + 1) • cupH (show 1 + 1 = 2 by rfl) s t)
    hA1 hB1) ?_
  refine Eq.trans ?_ e_br.symm
  refine Eq.trans ?_ (congrArg (δ (augSES_tensorLeft_shortExact (augIdeal k G ⊗ A) B) 1 (1 + 1)
    rfl).hom hAB1).symm
  refine Eq.trans ?_ (congrArg (fun t => δ (augSES_tensorLeft_shortExact (augIdeal k G ⊗ A) B) 1
    (1 + 1) rfl (δ (augSES_tensorRight_shortExact A B) 0 (0 + 1) rfl t)) hcup0)
  refine Eq.trans ?_ (congrArg (δ (augSES_tensorLeft_shortExact (augIdeal k G ⊗ A) B) 1
    (1 + 1) rfl).hom e_left).symm
  refine Eq.trans ?_ e_right.symm
  have hs : tsgn k (0 + 1) = (-1 : k) ^ 1 := by
    rw [tsgn_add_one]
    simp [tsgn]
  rw [hs]
  rfl

set_option maxHeartbeats 800000 in

theorem tateCup_unique_of_agrees (μ : ∀ p q : ℤ, TateCupFam k G p q)
    (hpos : ∀ (n m l : ℕ) [NeZero n] [NeZero m] [NeZero l] (hl : n + m = l) (A B : Rep.{u} k G)
      (a : tateCohomology A n) (b : tateCohomology B m),
      (tateIsoH (A ⊗ B) l l rfl).hom.hom (μ n m A B l (by omega) a b) =
        cupH hl ((tateIsoH A n n rfl).hom.hom a) ((tateIsoH B m m rfl).hom.hom b))
    (hleft : ∀ (p q : ℤ) (A B : Rep.{u} k G) (r : ℤ) (h : p + q = r) (a : tateCohomology A p)
      (b : tateCohomology B q),
      (tδ (augSES_tensorRight_shortExact A B) r (r + 1) rfl).hom (μ p q A B r h a b) =
        μ (p + 1) q (augIdeal k G ⊗ A) B (r + 1) (by omega)
          ((tδ (augSES_shortExact A) p (p + 1) rfl).hom a) b)
    (hright : ∀ (p q : ℤ) (A B : Rep.{u} k G) (r : ℤ) (h : p + q = r) (a : tateCohomology A p)
      (b : tateCohomology B q),
      (tδ (augSES_tensorLeft_shortExact A B) r (r + 1) rfl).hom (μ p q A B r h a b) =
        tsgn k p • μ p (q + 1) A (augIdeal k G ⊗ B) (r + 1) (by omega) a
          ((tδ (augSES_shortExact B) q (q + 1) rfl).hom b))
    (m : ℕ) : ∀ (p q : ℤ), (1 - p).toNat + (1 - q).toNat = m → ∀ (A B : Rep.{u} k G) (r : ℤ)
      (h : p + q = r) (a : tateCohomology A p) (b : tateCohomology B q),
      μ p q A B r h a b = tateCup p q A B r h a b := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro p q hm A B r h a b
  by_cases hp : p ≤ 0
  · rw [tateCup_of_nonpos q hp]
    apply moduleIso_hom_injective (tateLeftIso A B r)
    rw [tateLeftIso_cupL, tateLeftIso_hom]
    refine (hleft p q A B r h a b).trans ?_
    exact ih _ (by omega) (p + 1) q rfl _ _ _ _ _ _
  by_cases hq : q ≤ 0
  · rw [tateCup_of_pos_of_nonpos (by omega) hq]
    apply moduleIso_hom_injective (tateRightIso A B r)
    rw [tateRightIso_cupR, tateRightIso_hom]
    refine (hright p q A B r h a b).trans ?_
    exact congrArg (tsgn k p • ·) (ih _ (by omega) p (q + 1) rfl _ _ _ _ _ _)
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = n := ⟨p.toNat, by omega⟩
    obtain ⟨m', rfl⟩ : ∃ m' : ℕ, q = m' := ⟨q.toNat, by omega⟩
    obtain ⟨l, rfl⟩ : ∃ l : ℕ, r = l := ⟨r.toNat, by omega⟩
    have : NeZero n := ⟨by omega⟩
    have : NeZero m' := ⟨by omega⟩
    have : NeZero l := ⟨by omega⟩
    have hl : n + m' = l := by omega
    apply moduleIso_hom_injective (tateIsoH (A ⊗ B) l l rfl)
    rw [hpos n m' l hl, tateIsoH_tateCup rfl rfl rfl h hl]

noncomputable def tateCupTensor (A B : Rep.{u} k G) (p q : ℤ) :
    TensorProduct k (tateCohomology A p) (tateCohomology B q) →ₗ[k] tateCohomology (A ⊗ B) (p + q) :=
  TensorProduct.lift (tateCup p q A B (p + q) rfl)

theorem tateCup_δ_left {E : ShortComplex (Rep.{u} k G)} (hE : E.ShortExact) (B : Rep.{u} k G)
    (hEB : (E.map (tensorRight B)).ShortExact) (p q r : ℤ) (h : p + q = r)
    (a : tateCohomology E.X₃ p) (b : tateCohomology B q) :
    (TateCohomology.δ hEB r).hom (tateCup p q E.X₃ B r h a b) =
      tateCup (p + 1) q E.X₁ B (r + 1) (by omega) ((TateCohomology.δ hE p).hom a) b :=
  tateCup_connecting_left _ p q rfl hE B hEB r h a b

theorem tateCup_δ_right {E : ShortComplex (Rep.{u} k G)} (hE : E.ShortExact) (A : Rep.{u} k G)
    (hAE : (E.map (tensorLeft A)).ShortExact) (p q r : ℤ) (h : p + q = r)
    (a : tateCohomology A p) (b : tateCohomology E.X₃ q) :
    (TateCohomology.δ hAE r).hom (tateCup p q A E.X₃ r h a b) =
      p.negOnePow • tateCup p (q + 1) A E.X₁ (r + 1) (by omega) a ((TateCohomology.δ hE q).hom b) := by
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul k]
  exact tateCup_connecting_right _ p q rfl hE A hAE r h a b

end GroundTheory.GroupCoh
end
