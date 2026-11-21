import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace GlobalTheory.AmpleLocal

variable {Z : Scheme.{0}}

abbrev Fn (Z : Scheme.{0}) : Type := ∀ z : Z, Z.presheaf.stalk z

def Reg (V : Z.Opens) : Subring (Fn Z) where
  carrier := {F | ∃ a : Γ(Z, V), ∀ z (hz : z ∈ V), (Z.presheaf.germ V z hz).hom a = F z}
  mul_mem' := fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a * b, fun z hz => by rw [map_mul, ha, hb]; rfl⟩
  one_mem' := ⟨1, fun z hz => by rw [map_one]; rfl⟩
  add_mem' := fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a + b, fun z hz => by rw [map_add, ha, hb]; rfl⟩
  zero_mem' := ⟨0, fun z hz => by rw [map_zero]; rfl⟩
  neg_mem' := fun ⟨a, ha⟩ => ⟨-a, fun z hz => by rw [map_neg, ha]; rfl⟩

def IsLoc (D W : Z.Opens) (F : Fn Z) : Prop := ∀ z, z ∈ D ↔ z ∈ W ∧ IsUnit (F z)

def inv (F : Fn Z) : Fn Z := fun z => Ring.inverse (F z)

def Gen (D : Z.Opens) (S : Set (Fn Z)) : Prop :=
  ∀ F ∈ Reg D, ∃ b ∈ Subring.closure S, ∀ z ∈ D, F z = b z

theorem sec_ext {V : Z.Opens} {a b : Γ(Z, V)}
    (h : ∀ z (hz : z ∈ V), (Z.presheaf.germ V z hz).hom a = (Z.presheaf.germ V z hz).hom b) : a = b :=
  TopCat.Presheaf.section_ext Z.sheaf V a b h

theorem germ_res' {V W : Z.Opens} (h : V ≤ W) (a : Γ(Z, W)) (z : Z) (hz : z ∈ V) :
    (Z.presheaf.germ V z hz).hom ((Z.presheaf.map (homOfLE h).op).hom a) = (Z.presheaf.germ W z (h hz)).hom a :=
  TopCat.Presheaf.germ_res_apply Z.presheaf _ z hz a

theorem reg_mono {V W : Z.Opens} (h : V ≤ W) {F : Fn Z} (hF : F ∈ Reg W) : F ∈ Reg V := by
  obtain ⟨a, ha⟩ := hF
  exact ⟨_, fun z hz => (germ_res' h a z hz).trans (ha z _)⟩

theorem reg_congr {V : Z.Opens} {F G : Fn Z} (hF : F ∈ Reg V) (h : ∀ z ∈ V, F z = G z) : G ∈ Reg V := by
  obtain ⟨a, ha⟩ := hF
  exact ⟨a, fun z hz => (ha z hz).trans (h z hz)⟩

theorem reg_glue {V : Z.Opens} {F : Fn Z} (h : ∀ z ∈ V, ∃ O : Z.Opens, z ∈ O ∧ F ∈ Reg O) : F ∈ Reg V := by
  choose O hO hF using h
  let W : V → Z.Opens := fun z => O z.1 z.2 ⊓ V
  choose a ha using fun z : V => reg_mono (inf_le_left : W z ≤ _) (hF z.1 z.2)
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' W V (fun i => homOfLE inf_le_right)
    (fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, hO z hz, hz⟩) a
    (fun i j => sec_ext (V := W i ⊓ W j) fun z hz =>
      ((germ_res' inf_le_left _ z hz).trans (ha i z _)).trans ((germ_res' inf_le_right _ z hz).trans (ha j z _)).symm)
  refine ⟨s, fun z hz => ?_⟩
  have hm : z ∈ W ⟨z, hz⟩ := ⟨hO z hz, hz⟩
  exact (germ_res' inf_le_right s z hm).symm.trans
    ((congrArg (Z.presheaf.germ _ z hm).hom (hs ⟨z, hz⟩)).trans (ha _ z hm))

theorem reg_inv {V : Z.Opens} {F : Fn Z} (hF : F ∈ Reg V) (hu : ∀ z ∈ V, IsUnit (F z)) : inv F ∈ Reg V := by
  obtain ⟨a, ha⟩ := hF
  have : IsUnit a := Z.toRingedSpace.isUnit_of_isUnit_germ _ _ fun z hz => by
    have := hu z hz
    rw [← ha z hz] at this
    exact this
  obtain ⟨b, hb⟩ := this.exists_right_inv
  refine ⟨b, fun z hz => ?_⟩
  have e := congrArg (Z.presheaf.germ V z hz).hom hb
  rw [map_mul, map_one, ha] at e
  exact ((Ring.eq_mul_inverse_iff_mul_eq _ _ _ (hu z hz)).2 (by rw [mul_comm, e])).trans (one_mul _)

theorem IsLoc.le {D W : Z.Opens} {F : Fn Z} (h : IsLoc D W F) : D ≤ W := fun z hz => ((h z).1 hz).1

theorem IsLoc.unit {D W : Z.Opens} {F : Fn Z} (h : IsLoc D W F) {z : Z} (hz : z ∈ D) : IsUnit (F z) := ((h z).1 hz).2

theorem IsLoc.eq_basicOpen {D W : Z.Opens} {F : Fn Z} (h : IsLoc D W F) {a : Γ(Z, W)}
    (ha : ∀ z (hz : z ∈ W), (Z.presheaf.germ W z hz).hom a = F z) : D = Z.basicOpen a := by
  ext z
  refine (h z).trans ⟨fun ⟨hz, hu⟩ => (Z.mem_basicOpen a z hz).2 (by rw [← ha z hz] at hu; exact hu), fun hz => ?_⟩
  have hw := Z.basicOpen_le a hz
  exact ⟨hw, by rw [← ha z hw]; exact (Z.mem_basicOpen a z hw).1 hz⟩

theorem exists_loc {W : Z.Opens} {F : Fn Z} (hF : F ∈ Reg W) : ∃ D, IsLoc D W F := by
  obtain ⟨a, ha⟩ := hF
  refine ⟨Z.basicOpen a, fun z => ⟨fun hz => ?_, fun ⟨hz, hu⟩ =>
    (Z.mem_basicOpen a z hz).2 (by rw [← ha z hz] at hu; exact hu)⟩⟩
  have hw := Z.basicOpen_le a hz
  exact ⟨hw, by rw [← ha z hw]; exact (Z.mem_basicOpen a z hw).1 hz⟩

theorem IsLoc.affine {D W : Z.Opens} {F : Fn Z} (h : IsLoc D W F) (hF : F ∈ Reg W) (hW : IsAffineOpen W) :
    IsAffineOpen D := by
  obtain ⟨a, ha⟩ := hF
  rw [h.eq_basicOpen ha]
  exact hW.basicOpen a

theorem kill {D W : Z.Opens} {w F : Fn Z} (hW : IsCompact (W : Set Z)) (h : IsLoc D W w) (hw : w ∈ Reg W)
    (hF : F ∈ Reg W) (h0 : ∀ z ∈ D, F z = 0) : ∃ n : ℕ, ∀ z ∈ W, w z ^ n * F z = 0 := by
  obtain ⟨a, ha⟩ := hw
  obtain ⟨x, hx⟩ := hF
  obtain rfl := h.eq_basicOpen ha
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact Z hW x a
    (sec_ext fun z hz => (germ_res' (Z.basicOpen_le a) x z hz).trans (by rw [hx, h0 z hz, map_zero]))
  refine ⟨n, fun z hz => ?_⟩
  have e := congrArg (Z.presheaf.germ W z hz).hom hn
  rwa [map_mul, map_pow, map_zero, ha, hx] at e

theorem frac {D W : Z.Opens} {w F : Fn Z} (hW : IsAffineOpen W) (h : IsLoc D W w) (hw : w ∈ Reg W)
    (hF : F ∈ Reg D) : ∃ n : ℕ, ∃ G ∈ Reg W, ∀ z ∈ D, w z ^ n * F z = G z := by
  classical
  obtain ⟨a, ha⟩ := hw
  obtain ⟨x, hx⟩ := hF
  obtain rfl := h.eq_basicOpen ha
  obtain ⟨n, y, hn⟩ := exists_eq_pow_mul_of_isAffineOpen Z W hW a x
  refine ⟨n, fun z => if hz : z ∈ W then (Z.presheaf.germ W z hz).hom y else 0, ⟨y, fun z hz => by beta_reduce; rw [dif_pos hz]⟩,
    fun z hz => ?_⟩
  have hw := Z.basicOpen_le a hz
  have e := congrArg (Z.presheaf.germ _ z hz).hom hn
  rw [map_mul, map_pow, hx] at e
  exact ((dif_pos hw).trans ((germ_res' (Z.basicOpen_le a) y z hz).symm.trans (e.trans (congrArg (· ^ n * F z)
    ((germ_res' (Z.basicOpen_le a) a z hz).trans (ha z hw)))))).symm

theorem Gen.mono {D : Z.Opens} {S S' : Set (Fn Z)} (h : Gen D S)
    (hS : ∀ x ∈ S, ∃ b ∈ Subring.closure S', ∀ z ∈ D, x z = b z) : Gen D S' := by
  intro F hF
  obtain ⟨b, hb, e⟩ := h F hF
  suffices ∃ b' ∈ Subring.closure S', ∀ z ∈ D, b z = b' z by
    obtain ⟨b', hb', e'⟩ := this
    exact ⟨b', hb', fun z hz => (e z hz).trans (e' z hz)⟩
  clear e
  induction hb using Subring.closure_induction with
  | mem x hx => exact hS x hx
  | zero => exact ⟨0, zero_mem _, fun _ _ => rfl⟩
  | one => exact ⟨1, one_mem _, fun _ _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, e⟩ := hx
    obtain ⟨b, hb, e'⟩ := hy
    exact ⟨a + b, add_mem ha hb, fun z hz => congrArg₂ (· + ·) (e z hz) (e' z hz)⟩
  | neg x _ hx =>
    obtain ⟨a, ha, e⟩ := hx
    exact ⟨-a, neg_mem ha, fun z hz => congrArg (- ·) (e z hz)⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, e⟩ := hx
    obtain ⟨b, hb, e'⟩ := hy
    exact ⟨a * b, mul_mem ha hb, fun z hz => congrArg₂ (· * ·) (e z hz) (e' z hz)⟩

theorem Gen.loc {D W : Z.Opens} {w : Fn Z} {S : Set (Fn Z)} (hW : IsAffineOpen W) (h : IsLoc D W w) (hw : w ∈ Reg W)
    (hS : Gen W S) : Gen D (insert (inv w) S) := by
  intro F hF
  obtain ⟨n, G, hG, e⟩ := frac hW h hw hF
  obtain ⟨b, hb, e'⟩ := hS G hG
  refine ⟨inv w ^ n * b, mul_mem (pow_mem (Subring.subset_closure (Set.mem_insert _ _)) _)
    (Subring.closure_mono (Set.subset_insert _ _) hb), fun z hz => ?_⟩
  show F z = Ring.inverse (w z) ^ n * b z
  rw [← e' z (h.le hz), ← e z hz, ← mul_assoc, ← mul_pow, Ring.inverse_mul_cancel _ (h.unit hz), one_pow, one_mul]

def van (B : Subring (Fn Z)) (W : Z.Opens) : Ideal B where
  carrier := {b | ∀ z ∈ W, b.1 z = 0}
  add_mem' := fun {a b} ha hb z hz => by
    show a.1 z + b.1 z = 0
    rw [ha z hz, hb z hz, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c a ha z hz => by
    show c.1 z * a.1 z = 0
    rw [ha z hz, mul_zero]

theorem local_global {W : Z.Opens} (B : Subring (Fn Z)) (hB : B ≤ Reg W) {T : Type} (w : T → B)
    (hw : van B W ⊔ Ideal.span (Set.range w) = ⊤) (O : T → Z.Opens) (hO : ∀ t, IsLoc (O t) W (w t).1)
    (haff : ∀ t, IsAffineOpen (O t)) (hgen : ∀ t, Gen (O t) (insert (inv (w t).1) B)) :
    IsAffineOpen W ∧ Gen W B := by
  choose r hr using fun b : B => hB b.2
  let ρ : B →+* Γ(Z, W) :=
    { toFun := r
      map_one' := sec_ext fun z hz => by rw [hr, map_one]; rfl
      map_mul' := fun a b => sec_ext fun z hz => by rw [map_mul, hr, hr, hr]; rfl
      map_zero' := sec_ext fun z hz => by rw [hr, map_zero]; rfl
      map_add' := fun a b => sec_ext fun z hz => by rw [map_add, hr, hr, hr]; rfl }
  have hW : IsAffineOpen W := by
    refine isAffineOpen_of_isAffineOpen_basicOpen W (Set.range fun t => ρ (w t)) ?_ ?_
    · have := congrArg (Ideal.map ρ) hw
      rw [Ideal.map_sup, Ideal.map_top, Ideal.map_span, ← Set.range_comp,
        (Ideal.map_eq_bot_iff_le_ker ρ).2 (fun b hb => sec_ext fun z hz => (hr b z hz).trans
          ((hb z hz).trans (map_zero _).symm)), bot_sup_eq] at this
      exact this
    · rintro _ ⟨t, rfl⟩
      have := haff t
      rwa [(hO t).eq_basicOpen (hr (w t))] at this
  refine ⟨hW, fun F hF => ?_⟩
  let J : Ideal B :=
    { carrier := {b | ∃ b' : B, ∀ z ∈ W, b.1 z * F z = b'.1 z}
      add_mem' := fun {a b} ⟨a', ha⟩ ⟨b', hb⟩ => ⟨a' + b', fun z hz => by
        show (a.1 z + b.1 z) * F z = a'.1 z + b'.1 z
        rw [add_mul, ha z hz, hb z hz]⟩
      zero_mem' := ⟨0, fun z _ => zero_mul _⟩
      smul_mem' := fun c a ⟨a', ha⟩ => ⟨c * a', fun z hz => by
        show (c.1 z * a.1 z) * F z = c.1 z * a'.1 z
        rw [mul_assoc, ha z hz]⟩ }
  have hJ : J.radical = ⊤ := by
    rw [eq_top_iff, ← hw, sup_le_iff, Ideal.span_le]
    refine ⟨fun b hb => Ideal.le_radical ⟨0, fun z hz => by rw [hb z hz, zero_mul]; rfl⟩, ?_⟩
    rintro _ ⟨t, rfl⟩
    obtain ⟨b, hb, e⟩ := hgen t F (reg_mono (hO t).le hF)
    obtain ⟨n, b', e'⟩ : ∃ n : ℕ, ∃ b' : B, ∀ z ∈ O t, (w t).1 z ^ n * b z = b'.1 z := by
      clear e
      induction hb using Subring.closure_induction with
      | mem x hx =>
        rcases hx with rfl | hx
        · exact ⟨1, 1, fun z hz => by rw [pow_one]; exact Ring.mul_inverse_cancel _ ((hO t).unit hz)⟩
        · exact ⟨0, ⟨x, hx⟩, fun z hz => by rw [pow_zero, one_mul]⟩
      | zero => exact ⟨0, 0, fun _ _ => mul_zero _⟩
      | one => exact ⟨0, 1, fun _ _ => by rw [pow_zero, one_mul]; rfl⟩
      | add x y _ _ hx hy =>
        obtain ⟨n, a, e⟩ := hx
        obtain ⟨m, b, e'⟩ := hy
        refine ⟨n + m, w t ^ m * a + w t ^ n * b, fun z hz => ?_⟩
        show (w t).1 z ^ (n + m) * (x z + y z) = (w t).1 z ^ m * a.1 z + (w t).1 z ^ n * b.1 z
        rw [← e z hz, ← e' z hz]; ring
      | neg x _ hx =>
        obtain ⟨n, a, e⟩ := hx
        refine ⟨n, -a, fun z hz => ?_⟩
        show (w t).1 z ^ n * (-x z) = -a.1 z
        rw [← e z hz]; ring
      | mul x y _ _ hx hy =>
        obtain ⟨n, a, e⟩ := hx
        obtain ⟨m, b, e'⟩ := hy
        refine ⟨n + m, a * b, fun z hz => ?_⟩
        show (w t).1 z ^ (n + m) * (x z * y z) = a.1 z * b.1 z
        rw [← e z hz, ← e' z hz]; ring
    obtain ⟨m, hm⟩ := kill hW.isCompact (hO t) (hB (w t).2)
      (sub_mem (mul_mem (pow_mem (hB (w t).2) n) hF) (hB b'.2)) (fun z hz => by
        show (w t).1 z ^ n * F z - b'.1 z = 0
        rw [e z hz, e' z hz, sub_self])
    refine ⟨m + n, w t ^ m * b', fun z hz => ?_⟩
    have := hm z hz
    show (w t).1 z ^ (m + n) * F z = (w t).1 z ^ m * b'.1 z
    change (w t).1 z ^ m * ((w t).1 z ^ n * F z - b'.1 z) = 0 at this
    linear_combination this
  rw [Ideal.radical_eq_top, Ideal.eq_top_iff_one] at hJ
  obtain ⟨b, hb⟩ := hJ
  exact ⟨b.1, Subring.subset_closure b.2, fun z hz => (one_mul _).symm.trans (hb z hz)⟩

theorem exists_one_add_kill {B : Type} [CommRing B] {T : Type} [Finite T] (u : T → B) (K : Ideal B)
    (h : ∀ t, ∃ e : ℕ, u t ^ e ∈ K ⊔ Ideal.span (Set.range u) ^ (e + 1)) :
    ∃ c, c - 1 ∈ Ideal.span (Set.range u) ∧ ∃ d : ℕ, ∀ t, c * u t ^ d ∈ K := by
  classical
  set I := Ideal.span (Set.range u) with hI
  have step : ∀ J ≤ I, ∀ J' ≤ I, ∀ d k m : ℕ, J ^ d ≤ K ⊔ I ^ (d + 1) → d ≤ k → J ^ k * J' ^ m ≤ K ⊔ I ^ (k + m + 1) := by
    intro J hJ J' hJ' d k m hd hk
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hk
    calc J ^ (d + c) * J' ^ m = J ^ d * (J ^ c * J' ^ m) := by ring
      _ ≤ (K ⊔ I ^ (d + 1)) * (I ^ c * I ^ m) :=
        Ideal.mul_mono hd (Ideal.mul_mono (Ideal.pow_right_mono hJ _) (Ideal.pow_right_mono hJ' _))
      _ ≤ _ := by
        rw [Ideal.sup_mul]
        exact sup_le_sup Ideal.mul_le_left (le_of_eq (by ring))
  have key : ∀ s : Finset T, ∃ d : ℕ, Ideal.span (u '' s) ^ d ≤ K ⊔ I ^ (d + 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by simp⟩
    | insert t s _ ih =>
      obtain ⟨d, hd⟩ := ih
      obtain ⟨e, he⟩ := h t
      have h₁ : Ideal.span {u t} ≤ I := Ideal.span_mono (by simp)
      have h₂ : Ideal.span (u '' s) ≤ I := Ideal.span_mono (Set.image_subset_range _ _)
      refine ⟨e + d, ?_⟩
      rw [Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert, ← Ideal.add_eq_sup, add_pow,
        Ideal.sum_eq_sup, Finset.sup_le_iff]
      intro k hk
      have hk' : k ≤ e + d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      refine Ideal.mul_le_left.trans ?_
      by_cases hke : e ≤ k
      · have := step _ h₁ _ h₂ e k (e + d - k) (by
          rw [Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]; exact he) hke
        rwa [Nat.add_sub_cancel' hk'] at this
      · have := step _ h₂ _ h₁ d (e + d - k) k hd (by omega)
        rwa [Nat.sub_add_cancel hk', mul_comm] at this
  have := Fintype.ofFinite T
  obtain ⟨d, hd⟩ := key Finset.univ
  rw [Finset.coe_univ, Set.image_univ, ← hI] at hd
  obtain ⟨c, hc, hle⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup (I := I) (N := K) (N' := I ^ d)
    (P := I ^ d) (Submodule.FG.pow (Submodule.fg_span (Set.finite_range u)) d) le_rfl (by
      rw [Ideal.smul_eq_mul, ← pow_succ']; exact hd)
  exact ⟨c, hc, d, fun t => hle (Submodule.smul_mem_pointwise_smul _ c _
    (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self t)) d))⟩

def Sc {ι : Type} (U : ι → Z.Opens) (G : ι → Fn Z) (W : Z.Opens) (n : ℕ) (F : Fn Z) : Prop :=
  ∀ i, G i ^ n * F ∈ Reg (W ⊓ U i)

section Bundle

variable {ι : Type} {U : ι → Z.Opens} {G : ι → Fn Z}

theorem Sc.mono {V W : Z.Opens} {n : ℕ} {F : Fn Z} (h : Sc U G W n F) (hle : V ≤ W) : Sc U G V n F :=
  fun i => reg_mono (inf_le_inf_right _ hle) (h i)

theorem Sc.mul {W : Z.Opens} {n m : ℕ} {F F' : Fn Z} (h : Sc U G W n F) (h' : Sc U G W m F') :
    Sc U G W (n + m) (F * F') := fun i => by
  rw [pow_add, mul_mul_mul_comm]; exact mul_mem (h i) (h' i)

theorem Sc.pow {W : Z.Opens} {n : ℕ} {F : Fn Z} (h : Sc U G W n F) (d : ℕ) : Sc U G W (n * d) (F ^ d) := fun i => by
  rw [pow_mul, ← mul_pow]; exact pow_mem (h i) d

theorem Sc.zero (W : Z.Opens) (n : ℕ) : Sc U G W n 0 := fun i => by rw [mul_zero]; exact zero_mem _

variable (hU : ∀ z, ∃ i, z ∈ U i) (hG : ∀ i z, IsUnit (G i z))
include hU hG

theorem Sc.exists_loc {W : Z.Opens} {n : ℕ} {F : Fn Z} (h : Sc U G W n F) : ∃ D, IsLoc D W F := by
  choose D hD using fun i => AmpleLocal.exists_loc (h i)
  refine ⟨⨆ i, D i, fun z => Opens.mem_iSup.trans ⟨fun ⟨i, hi⟩ => ?_, fun ⟨hz, hu⟩ => ?_⟩⟩
  · exact ⟨((hD i).le hi).1, isUnit_of_mul_isUnit_right ((hD i).unit hi)⟩
  · obtain ⟨i, hi⟩ := hU z
    exact ⟨i, (hD i z).2 ⟨⟨hz, hi⟩, ((hG i z).pow n).mul hu⟩⟩

theorem Sc.ratio {D W : Z.Opens} {n : ℕ} {F σ : Fn Z} (h : Sc U G W n F) (hσ : Sc U G W n σ) (hD : IsLoc D W σ) :
    F * inv σ ∈ Reg D := by
  refine reg_glue fun z hz => ?_
  obtain ⟨i, hi⟩ := hU z
  have le : D ⊓ U i ≤ W ⊓ U i := inf_le_inf_right _ hD.le
  refine ⟨D ⊓ U i, ⟨hz, hi⟩, reg_congr (mul_mem (reg_mono le (h i)) (reg_inv (reg_mono le (hσ i))
    fun y hy => ((hG i y).pow n).mul (hD.unit hy.1))) fun y _ => ?_⟩
  show G i y ^ n * F y * Ring.inverse (G i y ^ n * σ y) = F y * Ring.inverse (σ y)
  have := Ring.mul_inverse_cancel _ ((hG i y).pow n)
  rw [Ring.mul_inverse_rev]
  linear_combination (F y * Ring.inverse (σ y)) * this

theorem Sc.extend [CompactSpace Z] [QuasiSeparatedSpace Z] (hT : ∀ i j, G i * inv (G j) ∈ Reg (U i ⊓ U j))
    {W : Z.Opens} {f : Fn Z} (hf : f ∈ Reg ⊤) (hW : IsLoc W ⊤ f) {n : ℕ} {F : Fn Z} (h : Sc U G W n F) :
    ∃ k : ℕ, ∃ σ, Sc U G ⊤ n σ ∧ ∀ z ∈ W, σ z = f z ^ k * F z := by
  classical
  choose c hc using hU
  choose V₀ hV₀ hm hle using fun z => exists_isAffineOpen_mem_and_subset (X := Z) (U := U (c z)) (x := z) (hc z)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun z => (V₀ z : Set Z)) (fun z => (V₀ z).isOpen)
    (fun z _ => Set.mem_iUnion.2 ⟨z, hm z⟩)
  let V : s → Z.Opens := fun α => V₀ α.1
  have hV : ∀ α, IsAffineOpen (V α) := fun α => hV₀ α.1
  let e : s → ι := fun α => c α.1
  have he : ∀ α, V α ≤ U (e α) := fun α => hle α.1
  have cov : ∀ z, ∃ α, z ∈ V α := fun z => by
    obtain ⟨α, hα, h⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ z))
    exact ⟨⟨α, hα⟩, h⟩
  have loc : ∀ O : Z.Opens, IsLoc (W ⊓ O) O f := fun O z =>
    ⟨fun hz => ⟨hz.2, hW.unit hz.1⟩, fun hz => ⟨(hW z).2 ⟨trivial, hz.2⟩, hz.1⟩⟩
  have cancel : ∀ i z, Ring.inverse (G i z) ^ n * G i z ^ n = 1 := fun i z => by
    rw [← mul_pow, Ring.inverse_mul_cancel _ (hG i z), one_pow]
  choose p H hH eH using fun α => frac (hV α) (loc (V α)) (reg_mono le_top hf)
    (reg_mono (inf_le_inf_left _ (he α)) (h (e α)))
  obtain ⟨k, hk⟩ := (Set.finite_range p).bddAbove
  let t : s → Fn Z := fun α => f ^ (k - p α) * H α * inv (G (e α)) ^ n
  have ht : ∀ α i, G i ^ n * t α ∈ Reg (U i ⊓ V α) := fun α i => by
    have : G i ^ n * t α = (G i * inv (G (e α))) ^ n * (f ^ (k - p α) * H α) := by simp only [t]; ring
    rw [this]
    exact mul_mem (pow_mem (reg_mono (inf_le_inf_left _ (he α)) (hT _ _)) _)
      (mul_mem (pow_mem (reg_mono le_top hf) _) (reg_mono inf_le_right (hH α)))
  have et : ∀ α, ∀ z ∈ W ⊓ V α, t α z = f z ^ k * F z := fun α z hz => by
    obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le (hk ⟨α, rfl⟩)
    show f z ^ (k - p α) * H α z * Ring.inverse (G (e α) z) ^ n = _
    rw [← eH α z hz, hq, Nat.add_sub_cancel_left]
    show f z ^ q * (f z ^ p α * (G (e α) z ^ n * F z)) * _ = _
    linear_combination (f z ^ (p α + q) * F z) * cancel (e α) z
  have hk2 : ∀ q : s × s, ∃ m : ℕ, ∀ z ∈ V q.1 ⊓ V q.2, f z ^ m * t q.1 z = f z ^ m * t q.2 z := fun ⟨α, β⟩ => by
    obtain ⟨m, hm⟩ := kill (W := V α ⊓ V β) (QuasiSeparatedSpace.inter_isCompact _ _ (V α).isOpen (hV α).isCompact
      (V β).isOpen (hV β).isCompact) (loc _) (reg_mono le_top hf)
      (sub_mem (reg_mono (le_inf (inf_le_left.trans (he α)) inf_le_left) (ht α (e α)))
        (reg_mono (le_inf (inf_le_left.trans (he α)) inf_le_right) (ht β (e α)))) (fun z hz => by
        show G (e α) z ^ n * t α z - G (e α) z ^ n * t β z = 0
        rw [et α z ⟨hz.1, hz.2.1⟩, et β z ⟨hz.1, hz.2.2⟩, sub_self])
    refine ⟨m, fun z hz => ?_⟩
    have h₁ := hm z hz
    change f z ^ m * (G (e α) z ^ n * t α z - G (e α) z ^ n * t β z) = 0 at h₁
    show f z ^ m * t α z = f z ^ m * t β z
    linear_combination Ring.inverse (G (e α) z) ^ n * h₁ - (f z ^ m * t α z - f z ^ m * t β z) * cancel (e α) z
  choose m hm using hk2
  obtain ⟨r, hr⟩ := (Set.finite_range m).bddAbove
  have agree : ∀ α β, ∀ z ∈ V α ⊓ V β, f z ^ r * t α z = f z ^ r * t β z := fun α β z hz => by
    obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le (hr ⟨(α, β), rfl⟩)
    rw [hq]
    linear_combination f z ^ q * hm (α, β) z hz
  choose a ha using cov
  refine ⟨r + k, fun z => f z ^ r * t (a z) z, fun i => reg_glue fun z hz => ⟨U i ⊓ V (a z), ⟨hz.2, ha z⟩, ?_⟩,
    fun z hz => ?_⟩
  · refine reg_congr (mul_mem (pow_mem (reg_mono le_top hf) r) (ht (a z) i)) fun y hy => ?_
    show f y ^ r * (G i y ^ n * t (a z) y) = G i y ^ n * (f y ^ r * t (a y) y)
    rw [← agree (a z) (a y) y ⟨hy.2, ha y⟩]; ring
  · show f z ^ r * t (a z) z = _
    rw [et _ z ⟨hz, ha z⟩]; ring

theorem extra_section {T : Type} [Finite T] {W₀ : Z.Opens} {N d : ℕ} {s : T → Fn Z} (hs : ∀ j, Sc U G W₀ N (s j))
    {D : T → Z.Opens} (hD : ∀ j, IsLoc (D j) W₀ (s j)) (cov : ∀ z ∈ W₀, ∃ j, z ∈ D j) (aff : ∀ j, IsAffineOpen (D j))
    {S₀ : Set (Fn Z)} (hS₀ : ∀ x ∈ S₀, x ∈ Reg W₀) (gen : ∀ j, Gen (D j) (S₀ ∪ Set.range fun m => s m * inv (s j)))
    {τ : Fn Z} (hτ : Sc U G W₀ (N * (d + 1)) τ) {W : Z.Opens} (hW : IsLoc W W₀ τ) :
    IsAffineOpen W ∧ Gen W (S₀ ∪ Set.range fun p : T × T => s p.2 * s p.1 ^ d * inv τ) := by
  set u₀ : T × T → Fn Z := fun p => s p.2 * s p.1 ^ d * inv τ with hu₀
  let B := Subring.closure (S₀ ∪ Set.range u₀)
  let u : T × T → B := fun p => ⟨u₀ p, Subring.subset_closure (Or.inr ⟨p, rfl⟩)⟩
  have hB : B ≤ Reg W := Subring.closure_le.2 (by
    rintro x (hx | ⟨p, rfl⟩)
    · exact reg_mono hW.le (hS₀ x hx)
    · refine Sc.ratio hU hG ?_ hτ hW
      rw [mul_add, mul_one, add_comm]
      exact (hs _).mul ((hs _).pow d))
  let v : T → Fn Z := fun j => τ * inv (s j ^ (d + 1))
  have hv : ∀ j, v j ∈ Reg (D j) := fun j => Sc.ratio hU hG hτ ((hs j).pow _) fun z =>
    (hD j z).trans (and_congr_right' (isUnit_pow_iff d.succ_ne_zero).symm)
  have vu : ∀ j, ∀ z ∈ D j ⊓ W, v j z * u₀ (j, j) z = 1 := fun j z hz => by
    have h₁ := Ring.mul_inverse_cancel _ (((hD j).unit hz.1).pow (d + 1))
    have h₂ := Ring.mul_inverse_cancel _ (hW.unit hz.2)
    show τ z * Ring.inverse (s j z ^ (d + 1)) * (s j z * s j z ^ d * Ring.inverse (τ z)) = 1
    linear_combination (τ z * Ring.inverse (τ z)) * h₁ + h₂
  have l₁ : ∀ j, IsLoc (D j ⊓ W) (D j) (v j) := fun j z =>
    ⟨fun hz => ⟨hz.1, IsUnit.of_mul_eq_one _ (vu j z hz)⟩, fun hz =>
      ⟨hz.1, (hW z).2 ⟨(hD j).le hz.1, isUnit_of_mul_isUnit_left hz.2⟩⟩⟩
  have l₂ : ∀ j, IsLoc (D j ⊓ W) W (u₀ (j, j)) := fun j z =>
    ⟨fun hz => ⟨hz.2, IsUnit.of_mul_eq_one_right _ (vu j z hz)⟩, fun hz =>
      ⟨(hD j z).2 ⟨hW.le hz.1, isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hz.2)⟩, hz.1⟩⟩
  have aff' : ∀ j, IsAffineOpen (D j ⊓ W) := fun j => (l₁ j).affine (hv j) (aff j)
  have rat : ∀ j m, ∀ z ∈ D j ⊓ W, u₀ (j, j) z * (s m z * Ring.inverse (s j z)) = u₀ (j, m) z := fun j m z hz => by
    have h₁ := Ring.mul_inverse_cancel _ ((hD j).unit hz.1)
    show s j z * s j z ^ d * Ring.inverse (τ z) * _ = s m z * s j z ^ d * Ring.inverse (τ z)
    linear_combination (s m z * s j z ^ d * Ring.inverse (τ z)) * h₁
  have cpt : IsCompact (W : Set Z) := by
    have : (W : Set Z) = ⋃ j, ((D j ⊓ W : Z.Opens) : Set Z) := Set.ext fun z =>
      ⟨fun hz => (cov z (hW.le hz)).elim fun j hj => Set.mem_iUnion.2 ⟨j, hj, hz⟩,
        fun hz => (Set.mem_iUnion.1 hz).elim fun j hj => hj.2⟩
    rw [this]
    exact isCompact_iUnion fun j => (aff' j).isCompact
  set I := Ideal.span (Set.range u) with hI
  have uI : ∀ p, u p ∈ I := fun p => Ideal.subset_span (Set.mem_range_self p)
  have deep : ∀ j, ∃ e : ℕ, u (j, j) ^ e ∈ van B W ⊔ I ^ (e + 1) := fun j => by
    obtain ⟨b, hb, eb⟩ := gen j _ (hv j)
    obtain ⟨e, x, hx, ex⟩ : ∃ e : ℕ, ∃ x ∈ I ^ e, ∀ z ∈ D j ⊓ W, u₀ (j, j) z ^ e * b z = x.1 z := by
      clear eb
      induction hb using Subring.closure_induction with
      | mem x hx =>
        rcases hx with hx | ⟨m, rfl⟩
        · exact ⟨0, ⟨x, Subring.subset_closure (Or.inl hx)⟩, by simp, fun z _ => by rw [pow_zero, one_mul]⟩
        · exact ⟨1, u (j, m), by rw [pow_one]; exact uI _, fun z hz => by rw [pow_one]; exact rat j m z hz⟩
      | zero => exact ⟨0, 0, zero_mem _, fun _ _ => mul_zero _⟩
      | one => exact ⟨0, 1, by simp, fun _ _ => by rw [pow_zero, one_mul]; rfl⟩
      | add x y _ _ hx hy =>
        obtain ⟨n, a, ha, e⟩ := hx
        obtain ⟨m, b, hb, e'⟩ := hy
        refine ⟨n + m, a * u (j, j) ^ m + u (j, j) ^ n * b, ?_, fun z hz => ?_⟩
        · rw [pow_add]
          exact add_mem (Ideal.mul_mem_mul ha (Ideal.pow_mem_pow (uI _) _))
            (Ideal.mul_mem_mul (Ideal.pow_mem_pow (uI _) _) hb)
        · show u₀ (j, j) z ^ (n + m) * (x z + y z) = a.1 z * u₀ (j, j) z ^ m + u₀ (j, j) z ^ n * b.1 z
          rw [← e z hz, ← e' z hz]; ring
      | neg x _ hx =>
        obtain ⟨n, a, ha, e⟩ := hx
        refine ⟨n, -a, neg_mem ha, fun z hz => ?_⟩
        show u₀ (j, j) z ^ n * (-x z) = -a.1 z
        rw [← e z hz]; ring
      | mul x y _ _ hx hy =>
        obtain ⟨n, a, ha, e⟩ := hx
        obtain ⟨m, b, hb, e'⟩ := hy
        refine ⟨n + m, a * b, by rw [pow_add]; exact Ideal.mul_mem_mul ha hb, fun z hz => ?_⟩
        show u₀ (j, j) z ^ (n + m) * (x z * y z) = a.1 z * b.1 z
        rw [← e z hz, ← e' z hz]; ring
    obtain ⟨m, hm⟩ := kill cpt (l₂ j) (hB (u (j, j)).2) (hB (u (j, j) ^ e - u (j, j) * x).2) (fun z hz => by
      show u₀ (j, j) z ^ e - u₀ (j, j) z * x.1 z = 0
      rw [← ex z hz, ← eb z hz.1]
      linear_combination (-u₀ (j, j) z ^ e) * vu j z hz)
    refine ⟨m + e, Submodule.mem_sup.2 ⟨u (j, j) ^ m * (u (j, j) ^ e - u (j, j) * x), hm,
      u (j, j) ^ (m + 1) * x, ?_, by ring⟩⟩
    rw [show m + e + 1 = (m + 1) + e by ring, pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (uI _) _) hx
  have upow : ∀ i j, u (i, j) ^ (d + 1) = u (j, j) * u (i, i) ^ d := fun i j => Subtype.ext (by
    show u₀ (i, j) ^ (d + 1) = u₀ (j, j) * u₀ (i, i) ^ d
    simp only [hu₀]; ring)
  obtain ⟨c, hc, q, hq⟩ := exists_one_add_kill u (van B W) (fun ⟨i, j⟩ => by
    obtain ⟨e, he⟩ := deep j
    refine ⟨(d + 1) * e, ?_⟩
    rw [pow_mul, upow, mul_pow, ← pow_mul]
    have := Ideal.mul_mem_mul he (Ideal.pow_mem_pow (uI (i, i)) (d * e))
    rw [Ideal.sup_mul] at this
    have hle : van B W * I ^ (d * e) ⊔ I ^ (e + 1) * I ^ (d * e) ≤ van B W ⊔ I ^ ((d + 1) * e + 1) :=
      sup_le_sup Ideal.mul_le_left (le_of_eq (by ring))
    exact hle this)
  have hc0 : c ∈ van B W := fun z hz => by
    obtain ⟨j, hj⟩ := cov z (hW.le hz)
    exact (((l₂ j).unit ⟨hj, hz⟩).pow q).mul_left_eq_zero.1 (hq (j, j) z hz)
  have top : van B W ⊔ Ideal.span (Set.range fun j => u (j, j)) = ⊤ := by
    rw [← Ideal.radical_eq_top, Ideal.eq_top_iff_one]
    have hle : I ≤ (van B W ⊔ Ideal.span (Set.range fun j => u (j, j))).radical := by
      rw [hI, Ideal.span_le]
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact ⟨d + 1, by
        rw [upow]
        exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩))⟩
    have := sub_mem (Ideal.le_radical (Ideal.mem_sup_left hc0)) (hle hc)
    rwa [sub_sub_cancel] at this
  obtain ⟨h₁, h₂⟩ := local_global B hB (fun j => u (j, j)) top (fun j => D j ⊓ W) l₂ aff' fun j => by
    refine (Gen.loc (aff j) (l₁ j) (hv j) (gen j)).mono ?_
    rintro x (rfl | hx | ⟨m, rfl⟩)
    · refine ⟨u₀ (j, j), Subring.subset_closure (Or.inr (u (j, j)).2), fun z hz => ?_⟩
      exact ((Ring.eq_mul_inverse_iff_mul_eq _ _ _ ((l₁ j).unit hz)).2
        ((mul_comm _ _).trans (vu j z hz))).trans (one_mul _) |>.symm
    · exact ⟨x, Subring.subset_closure (Or.inr (Subring.subset_closure (Or.inl hx))), fun _ _ => rfl⟩
    · refine ⟨inv (u₀ (j, j)) * u₀ (j, m), mul_mem (Subring.subset_closure (Or.inl rfl))
        (Subring.subset_closure (Or.inr (u (j, m)).2)), fun z hz => ?_⟩
      show s m z * Ring.inverse (s j z) = Ring.inverse (u₀ (j, j) z) * u₀ (j, m) z
      rw [← rat j m z hz, ← mul_assoc, Ring.inverse_mul_cancel _ ((l₂ j).unit hz), one_mul]
  exact ⟨h₁, h₂.mono fun x hx => ⟨x, hx, fun _ _ => rfl⟩⟩

end Bundle

end GlobalTheory.AmpleLocal
end
end

section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AmpleLocal

variable {X Y Z : Scheme.{0}}

def Pack {ι : Type} (U : ι → Z.Opens) (G : ι → Fn Z) (W : Z.Opens) (S : Set (Fn Z)) : Prop :=
  ∃ N : ℕ, 1 ≤ N ∧ ∃ M : ℕ, ∃ s : Fin (M + 1) → Fn Z, ∃ D : Fin (M + 1) → Z.Opens, (∀ j, Sc U G W N (s j)) ∧
    (∀ j, IsLoc (D j) W (s j)) ∧ (∀ z ∈ W, ∃ j, z ∈ D j) ∧ (∀ j, IsAffineOpen (D j)) ∧
    ∀ j, Gen (D j) (S ∪ Set.range fun m => s m * inv (s j))

theorem glue_pack {ι : Type} {U : ι → Z.Opens} {G : ι → Fn Z} (hU : ∀ z, ∃ i, z ∈ U i) (hG : ∀ i z, IsUnit (G i z))
    [CompactSpace Z] [QuasiSeparatedSpace Z] (hT : ∀ i j, G i * inv (G j) ∈ Reg (U i ⊓ U j))
    {R : Type} [CommRing R] (φ : R →+* Fn Z) (hφ : ∀ r, φ r ∈ Reg ⊤) {Λ : Type} [Finite Λ] (a : Λ → R)
    (ha : Ideal.span (Set.range a) = ⊤) (W : Λ → Z.Opens) (hW : ∀ l, IsLoc (W l) ⊤ (φ (a l)))
    (H : ∀ l, Pack U G (W l) (insert (inv (φ (a l))) (Set.range φ))) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ M : ℕ, ∃ σ : Fin (M + 1) → Fn Z, (∀ t, Sc U G ⊤ N (σ t)) ∧ (∀ z, ∃ t, IsUnit (σ t z)) ∧
      ∀ t D, IsLoc D ⊤ (σ t) → IsAffineOpen D ∧ Gen D (Set.range φ ∪ Set.range fun m => σ m * inv (σ t)) := by
  classical
  have := Fintype.ofFinite Λ
  choose N hN M s D hs hD cov aff gen using H
  have hd : ∀ l, ∃ d, ∏ l, N l = N l * (d + 1) := fun l => by
    obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ l)
    have : 0 < ∏ l, N l := Finset.prod_pos fun l _ => hN l
    cases e with
    | zero => omega
    | succ e => exact ⟨e, he⟩
  choose d hd using hd
  let T := Σ l, Fin (M l + 1) × Fin (M l + 1)
  have hsc : ∀ t : T, Sc U G (W t.1) (∏ l, N l) (s t.1 t.2.2 * s t.1 t.2.1 ^ d t.1) := fun t => by
    rw [hd t.1, mul_add, mul_one, add_comm]
    exact (hs _ _).mul ((hs _ _).pow _)
  choose k σ hσ eσ using fun t : T => (hsc t).extend hU hG hT (hφ _) (hW t.1)
  have covW : ∀ z, ∃ l, z ∈ W l := fun z => by
    by_contra hn
    have : Ideal.span (Set.range a) ≤ (IsLocalRing.maximalIdeal (Z.presheaf.stalk z)).comap
        ((Pi.evalRingHom _ z).comp φ) := Ideal.span_le.2 (by
      rintro _ ⟨l, rfl⟩ hu
      exact hn ⟨l, (hW l z).2 ⟨trivial, hu⟩⟩)
    rw [ha, top_le_iff, Ideal.comap_eq_top_iff] at this
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top this
  have main : ∀ τ, Sc U G ⊤ (∏ l, N l) τ → ∀ E, IsLoc E ⊤ τ →
      IsAffineOpen E ∧ Gen E (Set.range φ ∪ Set.range fun m => σ m * inv τ) := by
    intro τ hτ E hE
    let B := Subring.closure (Set.range φ ∪ Set.range fun m => σ m * inv τ)
    have hB : B ≤ Reg E := Subring.closure_le.2 (by
      rintro x (⟨r, rfl⟩ | ⟨p, rfl⟩)
      · exact reg_mono le_top (hφ r)
      · exact Sc.ratio hU hG (hσ p) hτ hE)
    let ψ : R →+* B := φ.codRestrict B fun r => Subring.subset_closure (Or.inl ⟨r, rfl⟩)
    have key : ∀ l, IsAffineOpen (W l ⊓ E) ∧ Gen (W l ⊓ E) _ := fun l =>
      extra_section hU hG (hs l) (hD l) (cov l) (aff l) (by
        rintro x (rfl | ⟨r, rfl⟩)
        · exact reg_inv (reg_mono le_top (hφ _)) fun z hz => (hW l).unit hz
        · exact reg_mono le_top (hφ r)) (gen l) (τ := τ) (d := d l) (by rw [← hd l]; exact hτ.mono le_top)
        (W := W l ⊓ E) fun z => ⟨fun hz => ⟨hz.1, hE.unit hz.2⟩, fun hz => ⟨hz.1, (hE z).2 ⟨trivial, hz.2⟩⟩⟩
    obtain ⟨h₁, h₂⟩ := local_global B hB (fun l => ψ (a l)) (by
        have := congrArg (Ideal.map ψ) ha
        rw [Ideal.map_top, Ideal.map_span, ← Set.range_comp] at this
        exact top_le_iff.1 (this.ge.trans le_sup_right)) (fun l => W l ⊓ E)
      (fun l z => ⟨fun hz => ⟨hz.2, (hW l).unit hz.1⟩, fun hz => ⟨(hW l z).2 ⟨trivial, hz.2⟩, hz.1⟩⟩)
      (fun l => (key l).1) fun l => (key l).2.mono (by
        rintro x ((rfl | ⟨r, rfl⟩) | ⟨p, rfl⟩)
        · exact ⟨_, Subring.subset_closure (Or.inl rfl), fun _ _ => rfl⟩
        · exact ⟨_, Subring.subset_closure (Or.inr (ψ r).2), fun _ _ => rfl⟩
        · refine ⟨inv (φ (a l)) ^ k ⟨l, p⟩ * (σ ⟨l, p⟩ * inv τ),
            Subring.mul_mem _ (Subring.pow_mem _ (Subring.subset_closure (Set.mem_insert _ _)) _)
              (Subring.subset_closure (Or.inr (Subring.subset_closure (Or.inr ⟨⟨l, p⟩, rfl⟩)))), fun z hz => ?_⟩
          show s l p.2 z * s l p.1 z ^ d l * inv τ z =
            Ring.inverse (φ (a l) z) ^ k ⟨l, p⟩ * (σ ⟨l, p⟩ z * inv τ z)
          rw [eσ ⟨l, p⟩ z hz.1, mul_assoc (φ _ z ^ _), ← mul_assoc (Ring.inverse _ ^ _), ← mul_pow,
            Ring.inverse_mul_cancel _ ((hW l).unit hz.1), one_pow, one_mul]
          rfl)
    exact ⟨h₁, h₂.mono fun x hx => ⟨x, hx, fun _ _ => rfl⟩⟩
  let e : Fin (Fintype.card T + 1) ≃ Option T :=
    (finSuccEquiv _).trans (Fintype.equivFin T).symm.optionCongr
  let σ' : Option T → Fn Z := fun o => o.elim 0 σ
  have hσ' : ∀ o, Sc U G ⊤ (∏ l, N l) (σ' o) := fun o => by
    cases o with
    | none => exact Sc.zero _ _
    | some t => exact hσ t
  refine ⟨∏ l, N l, (Finset.prod_pos fun l _ => hN l : 0 < ∏ l, N l), Fintype.card T, fun t => σ' (e t), fun t => hσ' _,
    fun z => ?_, fun t E hE => ?_⟩
  · obtain ⟨l, hl⟩ := covW z
    obtain ⟨j, hj⟩ := cov l z hl
    refine ⟨e.symm (some ⟨l, j, j⟩), ?_⟩
    simp only [Equiv.apply_symm_apply]
    show IsUnit (σ ⟨l, j, j⟩ z)
    rw [eσ ⟨l, j, j⟩ z hl]
    exact (((hW l).unit hl).pow _).mul (((hD l j).unit hj).mul (((hD l j).unit hj).pow _))
  · obtain ⟨h₁, h₂⟩ := main _ (hσ' (e t)) E hE
    refine ⟨h₁, h₂.mono ?_⟩
    rintro x (hx | ⟨m, rfl⟩)
    · exact ⟨x, Subring.subset_closure (Or.inl hx), fun _ _ => rfl⟩
    · refine ⟨_, Subring.subset_closure (Or.inr ⟨e.symm (some m), ?_⟩), fun _ _ => rfl⟩
      simp only [Equiv.apply_symm_apply]
      rfl

def pb (h : Y ⟶ Z) : Fn Z →+* Fn Y :=
  Pi.ringHom fun y => (h.stalkMap y).hom.comp (Pi.evalRingHom _ (h y))

theorem pb_apply (h : Y ⟶ Z) (F : Fn Z) (y : Y) : pb h F y = (h.stalkMap y).hom (F (h y)) := rfl

theorem pb_comp (h : Y ⟶ Z) (g : Z ⟶ X) (F : Fn X) : pb (h ≫ g) F = pb h (pb g F) := by
  funext y
  rw [pb_apply, Scheme.Hom.stalkMap_comp]
  rfl

theorem pb_unit (h : Y ⟶ Z) (F : Fn Z) (y : Y) : IsUnit (pb h F y) ↔ IsUnit (F (h y)) :=
  isUnit_map_iff (h.stalkMap y).hom _

theorem pb_inv (h : Y ⟶ Z) (F : Fn Z) : pb h (inv F) = inv (pb h F) := by
  funext y
  show (h.stalkMap y).hom (Ring.inverse (F (h y))) = Ring.inverse (pb h F y)
  by_cases hu : IsUnit (F (h y))
  · refine ((Ring.eq_mul_inverse_iff_mul_eq _ _ _ ((pb_unit h F y).2 hu)).2 ?_).trans (one_mul _)
    rw [pb_apply, ← map_mul, Ring.inverse_mul_cancel _ hu, map_one]
  · rw [Ring.inverse_non_unit _ hu, Ring.inverse_non_unit _ (mt (pb_unit h F y).1 hu), map_zero]

theorem gs_id (V : Z.Opens) (z : Z) (hz : z ∈ V) (a : Γ(Z, V)) : gs (𝟙 Z) z V a = (Z.presheaf.germ V z hz).hom a :=
  gs_eq (𝟙 Z) z V hz a

theorem mem_reg_iff {V : Z.Opens} {F : Fn Z} : F ∈ Reg V ↔ ∃ a : Γ(Z, V), ∀ z ∈ V, gs (𝟙 Z) z V a = F z :=
  exists_congr fun a => forall_congr' fun z => forall_congr' fun hz => by rw [gs_id V z hz]

theorem stalkMap_gs (h : Y ⟶ Z) (g : Z ⟶ X) (y : Y) (V : X.Opens) (hy : g (h y) ∈ V) (a : Γ(X, V)) :
    (h.stalkMap y).hom (gs g (h y) V a) = gs (h ≫ g) y V a := by
  rw [← gs_pull h g y V hy, gs_stalkMap h y (g ⁻¹ᵁ V) hy, gs_pull (𝟙 Z) g (h y) V hy, Category.id_comp]

theorem reg_gs (g : Z ⟶ X) (V : X.Opens) (a : Γ(X, V)) : (fun z => gs g z V a) ∈ Reg (g ⁻¹ᵁ V) :=
  ⟨(g.app V).hom a, fun z hz => (gs_eq g z V hz a).symm⟩

theorem reg_pull (h : Y ⟶ Z) {V : Z.Opens} {F : Fn Z} (hF : F ∈ Reg V) : pb h F ∈ Reg (h ⁻¹ᵁ V) := by
  obtain ⟨a, ha⟩ := mem_reg_iff.1 hF
  exact reg_congr (reg_gs h V a) fun y hy => (gs_stalkMap h y V hy a).trans (congrArg _ (ha _ hy))

def cst (p : Z ⟶ X) : Γ(X, ⊤) →+* Fn Z :=
  Pi.ringHom fun z => (Z.presheaf.germ (p ⁻¹ᵁ ⊤) z trivial).hom.comp (p.app ⊤).hom

theorem cst_apply (p : Z ⟶ X) (r : Γ(X, ⊤)) (z : Z) : cst p r z = gs p z ⊤ r := (gs_eq p z ⊤ trivial r).symm

theorem pb_cst (h : Y ⟶ Z) (p : Z ⟶ X) (r : Γ(X, ⊤)) : pb h (cst p r) = cst (h ≫ p) r := by
  funext y
  rw [pb_apply, cst_apply, cst_apply, stalkMap_gs h p y ⊤ trivial]

theorem reg_cst (p : Z ⟶ X) (r : Γ(X, ⊤)) : cst p r ∈ Reg ⊤ := ⟨(p.app ⊤).hom r, fun _ _ => rfl⟩

theorem loc_cst (r : Γ(X, ⊤)) : IsLoc (X.basicOpen r) ⊤ (cst (𝟙 X) r) := fun x =>
  (X.mem_basicOpen r x trivial).trans ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩

section Open

variable (h : Y ⟶ Z) [IsOpenImmersion h]

theorem pb_inj {F F' : Fn Z} {y : Y} (e : pb h F y = pb h F' y) : F (h y) = F' (h y) :=
  (ConcreteCategory.bijective_of_isIso (h.stalkMap y)).1 e

theorem pb_surj (F' : Fn Y) : ∃ F, pb h F = F' := by
  have : ∀ z : Z, ∃ x : Z.presheaf.stalk z, ∀ y (e : z = h y), (h.stalkMap y).hom (e ▸ x) = F' y := fun z => by
    by_cases hz : ∃ y, h y = z
    · obtain ⟨y, rfl⟩ := hz
      obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (h.stalkMap y)).2 (F' y)
      refine ⟨x, fun y' e => ?_⟩
      obtain rfl := h.isOpenEmbedding.injective e
      exact hx
    · exact ⟨0, fun y e => (hz ⟨y, e.symm⟩).elim⟩
  choose F hF using this
  exact ⟨F, funext fun y => hF (h y) y rfl⟩

theorem reg_push {V : Y.Opens} {F : Fn Z} (hF : pb h F ∈ Reg V) : F ∈ Reg (h ''ᵁ V) := by
  obtain ⟨a, ha⟩ := mem_reg_iff.1 hF
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso (h.appIso V).hom).2 a
  refine mem_reg_iff.2 ⟨b, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  refine pb_inj h (F := fun z => gs (𝟙 Z) z _ b) (Eq.trans ?_ (ha y hy))
  rw [pb_apply, ← gs_stalkMap h y _ (h.apply_mem_image_iff.2 hy), h.appIso_hom']
  exact ((gs_appLE h _ _ _ (𝟙 Y) y hy b).trans (by rw [Category.id_comp])).symm

theorem gen_push {V : Y.Opens} {S : Set (Fn Z)} (hS : Gen V (pb h '' S)) : Gen (h ''ᵁ V) S := by
  intro F hF
  obtain ⟨b, hb, e⟩ := hS _ (reg_mono (h.preimage_image_eq V).ge (reg_pull h hF))
  rw [← RingHom.map_closure] at hb
  obtain ⟨b, hb, rfl⟩ := hb
  refine ⟨b, hb, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact pb_inj h (e y hy)

theorem pack_push {ι : Type} {U : ι → Z.Opens} {G : ι → Fn Z} {S : Set (Fn Z)}
    (H : Pack (fun i => h ⁻¹ᵁ U i) (fun i => pb h (G i)) ⊤ (pb h '' S)) : Pack U G (h ''ᵁ ⊤) S := by
  obtain ⟨N, hN, M, s, D, hs, hD, cov, aff, gen⟩ := H
  choose s' e using fun j => pb_surj h (s j)
  obtain rfl : s = fun j => pb h (s' j) := funext fun j => (e j).symm
  refine ⟨N, hN, M, s', fun j => h ''ᵁ D j, fun j i => ?_, fun j z => ⟨?_, ?_⟩, ?_,
    fun j => (aff j).image_of_isOpenImmersion h, fun j => gen_push h ?_⟩
  · refine reg_mono ?_ (reg_push h (V := ⊤ ⊓ h ⁻¹ᵁ U i) (by rw [map_mul, map_pow]; exact hs j i))
    rintro _ ⟨⟨y, -, rfl⟩, hy⟩
    exact ⟨y, ⟨trivial, hy⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, trivial, rfl⟩, (pb_unit h _ y).1 ((hD j).unit hy)⟩
  · rintro ⟨⟨y, -, rfl⟩, hy⟩
    exact ⟨y, (hD j y).2 ⟨trivial, (pb_unit h _ y).2 hy⟩, rfl⟩
  · rintro _ ⟨y, -, rfl⟩
    obtain ⟨j, hj⟩ := cov y trivial
    exact ⟨j, y, hj, rfl⟩
  · have := gen j
    simpa only [Set.image_union, ← Set.range_comp', map_mul, pb_inv] using this

end Open

theorem gen_iff {R T : Type} [CommRing R] {D : Z.Opens} (ψ : R →+* Γ(Z, D)) (r : T → Γ(Z, D)) (φ : R → Fn Z)
    (ρ : T → Fn Z) (hψ : ∀ c, ∀ z ∈ D, gs (𝟙 Z) z D (ψ c) = φ c z) (hr : ∀ t, ∀ z ∈ D, gs (𝟙 Z) z D (r t) = ρ t z) :
    Gen D (Set.range φ ∪ Set.range ρ) ↔ Function.Surjective (MvPolynomial.eval₂Hom ψ r) := by
  constructor
  · intro H x
    obtain ⟨b, hb, e⟩ := H (fun z => gs (𝟙 Z) z D x) (mem_reg_iff.2 ⟨x, fun _ _ => rfl⟩)
    suffices ∃ p, ∀ z (hz : z ∈ D), (Z.presheaf.germ D z hz).hom (MvPolynomial.eval₂Hom ψ r p) = b z by
      obtain ⟨p, hp⟩ := this
      exact ⟨p, sec_ext fun z hz => (hp z hz).trans ((e z hz).symm.trans (gs_id D z hz x))⟩
    clear e
    induction hb using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨c, rfl⟩ | ⟨t, rfl⟩
      · exact ⟨MvPolynomial.C c, fun z hz => by rw [MvPolynomial.eval₂Hom_C, ← gs_id, hψ c z hz]⟩
      · exact ⟨MvPolynomial.X t, fun z hz => by rw [MvPolynomial.eval₂Hom_X', ← gs_id, hr t z hz]⟩
    | zero => exact ⟨0, fun z hz => by rw [map_zero, map_zero]; rfl⟩
    | one => exact ⟨1, fun z hz => by rw [map_one, map_one]; rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨p, hp⟩ := hx
      obtain ⟨q, hq⟩ := hy
      exact ⟨p + q, fun z hz => by rw [map_add, map_add, hp, hq]; rfl⟩
    | neg x _ hx =>
      obtain ⟨p, hp⟩ := hx
      exact ⟨-p, fun z hz => by rw [map_neg, map_neg, hp]; rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨p, hp⟩ := hx
      obtain ⟨q, hq⟩ := hy
      exact ⟨p * q, fun z hz => by rw [map_mul, map_mul, hp, hq]; rfl⟩
  · rintro H F ⟨x, hx⟩
    obtain ⟨p, rfl⟩ := H x
    suffices ∃ b ∈ Subring.closure (Set.range φ ∪ Set.range ρ),
        ∀ z (hz : z ∈ D), (Z.presheaf.germ D z hz).hom (MvPolynomial.eval₂Hom ψ r p) = b z by
      obtain ⟨b, hb, e⟩ := this
      exact ⟨b, hb, fun z hz => (hx z hz).symm.trans (e z hz)⟩
    clear hx
    induction p using MvPolynomial.induction_on with
    | C c => exact ⟨φ c, Subring.subset_closure (Or.inl ⟨c, rfl⟩), fun z hz => by
        rw [MvPolynomial.eval₂Hom_C, ← gs_id, hψ c z hz]⟩
    | add p q hp hq =>
      obtain ⟨a, ha, e⟩ := hp
      obtain ⟨b, hb, e'⟩ := hq
      exact ⟨a + b, add_mem ha hb, fun z hz => by rw [map_add, map_add, e, e']; rfl⟩
    | mul_X p t hp =>
      obtain ⟨a, ha, e⟩ := hp
      exact ⟨a * ρ t, mul_mem ha (Subring.subset_closure (Or.inr ⟨t, rfl⟩)), fun z hz => by
        rw [map_mul, map_mul, e, MvPolynomial.eval₂Hom_X', ← gs_id, hr t z hz]; rfl⟩

section Link

variable {P : LB Y}

theorem sec_tr (s : LB.Sec P) (y : Y) {k k' : P.ι} (hk : y ∈ P.U k) (hk' : y ∈ P.U k') :
    gs (𝟙 Y) y _ (s.f k) = (gm (𝟙 Y) y _ (P.g k k')).val * gs (𝟙 Y) y _ (s.f k') := by
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ P.U k ⊓ P.U k' := ⟨hk, hk'⟩
  exact (gs_res _ y _ hm _).symm.trans ((congrArg (gs (𝟙 Y) y _) (s.compat k k')).trans ((gs_mul _ y _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit _ y _ hm _) (gs_res _ y _ hm _))))

def sv (γ : Y → P.ι) (s : LB.Sec P) : Fn Y := fun y => gs (𝟙 Y) y (P.U (γ y)) (s.f (γ y))

variable {γ : Y → P.ι} (hγ : ∀ y, y ∈ P.U (γ y))
include hγ

theorem loc_sv (s : LB.Sec P) : IsLoc (nonzeroLocus s) ⊤ (sv γ s) := fun y =>
  (mem_nonzeroLocus s y).trans ⟨fun ⟨k, hk, hu⟩ => ⟨trivial, by
    rw [sec_tr s y hk (hγ y)] at hu; exact isUnit_of_mul_isUnit_right hu⟩, fun hu => ⟨γ y, hγ y, hu.2⟩⟩

theorem ratio_iff (s t : LB.Sec P) (r : Γ(Y, nonzeroLocus s)) :
    (∀ k, (Y.presheaf.map (homOfLE (inf_le_right : nonzeroLocus s ⊓ P.U k ≤ P.U k)).op).hom (t.f k) =
      (Y.presheaf.map (homOfLE (inf_le_left : nonzeroLocus s ⊓ P.U k ≤ nonzeroLocus s)).op).hom r *
        (Y.presheaf.map (homOfLE (inf_le_right : nonzeroLocus s ⊓ P.U k ≤ P.U k)).op).hom (s.f k)) ↔
    ∀ y ∈ nonzeroLocus s, gs (𝟙 Y) y _ r = (sv γ t * inv (sv γ s)) y := by
  constructor
  · intro H y hy
    have hm : (𝟙 Y : Y ⟶ Y) y ∈ nonzeroLocus s ⊓ P.U (γ y) := ⟨hy, hγ y⟩
    have e := congrArg (gs (𝟙 Y) y _) (H (γ y))
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    exact (Ring.eq_mul_inverse_iff_mul_eq _ _ _ ((loc_sv hγ s).unit hy)).2 e.symm
  · intro H k
    refine fn_ext fun y hy => ?_
    have e := (Ring.eq_mul_inverse_iff_mul_eq _ _ _ ((loc_sv hγ s).unit hy.1)).1 (H y hy.1)
    have hm : (𝟙 Y : Y ⟶ Y) y ∈ nonzeroLocus s ⊓ P.U k := hy
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, sec_tr s y hy.2 (hγ y),
      sec_tr t y hy.2 (hγ y), mul_left_comm]
    exact congrArg _ e.symm

omit hγ

variable {ι : Type} {U : ι → Y.Opens} {G : ι → Fn Y} {N : ℕ} {κ : ι → P.ι} {c : Y → ι}
  (hκ : ∀ i, U i ≤ P.U (κ i)) (hc : ∀ y, y ∈ U (c y))
  (hg : ∀ i y, y ∈ U i → (gm (𝟙 Y) y _ (P.g (κ i) (κ (c y)))).val = G i y ^ N)
include hκ hc hg

theorem sc_sv (s : LB.Sec P) : Sc U G ⊤ N (sv (fun y => κ (c y)) s) := fun i =>
  reg_congr (reg_mono (inf_le_right.trans (hκ i)) (reg_gs (𝟙 Y) _ (s.f (κ i)))) fun y hy => by
    rw [sec_tr s y (hκ i hy.2) (hκ _ (hc y)), hg i y hy.2]
    rfl

theorem exists_sv (hP : P.IsLB) {σ : Fn Y} (hσ : Sc U G ⊤ N σ) : ∃ s : LB.Sec P, sv (fun y => κ (c y)) s = σ := by
  have : ∀ k, (fun y => (gm (𝟙 Y) y _ (P.g k (κ (c y)))).val * σ y) ∈ Reg (P.U k) := fun k =>
    reg_glue fun z hz => ⟨P.U k ⊓ U (c z), ⟨hz, hc z⟩, reg_congr
      (mul_mem (reg_mono (inf_le_inf_left _ (hκ _)) (reg_gs (𝟙 Y) _ (P.g k (κ (c z))).val))
        (reg_mono (le_inf le_top inf_le_right) (hσ (c z)))) fun y hy => by
      show gs (𝟙 Y) y _ (P.g k (κ (c z))).val * (G (c z) y ^ N * σ y) = _
      rw [gs_unit (𝟙 Y) y (P.U k ⊓ P.U (κ (c z))) ⟨hy.1, hκ _ hy.2⟩, ← hg _ y hy.2, ← mul_assoc, ← Units.val_mul,
        gm_cocycle hP (𝟙 Y) y hy.1 (hκ _ hy.2) (hκ _ (hc y))]⟩
  choose f hf using fun k => mem_reg_iff.1 (this k)
  refine ⟨⟨f, fun k k' => fn_ext fun y hy => ?_⟩, funext fun y => ?_⟩
  · have hm : (𝟙 Y : Y ⟶ Y) y ∈ P.U k ⊓ P.U k' := hy
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_unit _ y _ hm, hf k y hy.1, hf k' y hy.2,
      ← mul_assoc, ← Units.val_mul, gm_cocycle hP (𝟙 Y) y hy.1 hy.2 (hκ _ (hc y))]
  · refine (hf _ y (hκ _ (hc y))).trans ?_
    rw [gm_self hP (𝟙 Y) y (hκ _ (hc y)), Units.val_one, one_mul]

end Link

theorem Pack.mono {ι : Type} {U : ι → Z.Opens} {G : ι → Fn Z} {W : Z.Opens} {S S' : Set (Fn Z)} (H : Pack U G W S)
    (hS : ∀ x ∈ S, x ∈ Subring.closure S') : Pack U G W S' := by
  obtain ⟨N, hN, M, s, D, hs, hD, cov, aff, gen⟩ := H
  refine ⟨N, hN, M, s, D, hs, hD, cov, aff, fun j => (gen j).mono ?_⟩
  rintro x (hx | hx)
  · exact ⟨x, Subring.closure_mono Set.subset_union_left (hS x hx), fun _ _ => rfl⟩
  · exact ⟨x, Subring.subset_closure (Or.inr hx), fun _ _ => rfl⟩

theorem cst_mem {B V : Scheme.{0}} [IsAffine B] (a : Γ(B, ⊤)) (b : V ⟶ B) [IsOpenImmersion b]
    (hb : b ''ᵁ ⊤ = B.basicOpen a) (q : Y ⟶ V) (h : Y ⟶ Z) (p : Z ⟶ B) (e : h ≫ p = q ≫ b) (c : Γ(V, ⊤)) :
    cst q c ∈ Subring.closure (pb h '' insert (inv (cst p a)) (Set.range (cst p))) := by
  obtain ⟨F, hF⟩ := pb_surj b (cst (𝟙 V) c)
  have h₁ : F ∈ Reg (B.basicOpen a) := hb ▸ reg_push b (hF ▸ reg_cst _ c)
  have h₂ : Gen ⊤ (Set.range (cst (𝟙 B))) := fun F ⟨x, hx⟩ =>
    ⟨cst (𝟙 B) x, Subring.subset_closure ⟨x, rfl⟩, fun z hz => (hx z hz).symm⟩
  obtain ⟨β, hβ, eβ⟩ := Gen.loc (isAffineOpen_top B) (loc_cst a) (reg_cst _ a) h₂ F h₁
  have : cst q c = pb h (pb p β) := by
    rw [← pb_comp, e, ← Category.comp_id q, ← pb_cst, ← hF, ← pb_comp, Category.comp_id q]
    funext y
    rw [pb_apply, pb_apply, eβ]
    rw [← hb]
    exact ⟨q y, trivial, rfl⟩
  rw [this, ← RingHom.map_closure]
  refine ⟨_, ?_, rfl⟩
  have := Subring.mem_map.2 ⟨β, hβ, (rfl : pb p β = _)⟩
  rw [RingHom.map_closure] at this
  simp only [Set.image_insert_eq, ← Set.range_comp', pb_inv, pb_cst, Category.comp_id] at this
  exact this

theorem gm_const (L : LB X) (j : Y ⟶ X) (N : ℕ) (y : Y) (i i' : L.ι) (hi : j y ∈ L.U i) (hi' : j y ∈ L.U i') :
    (gm (𝟙 Y) y _ ((LB.LinComb L (K := Fin N) (fun _ => j) (fun _ => 1)).g (fun _ => i) (fun _ => i'))).val =
      (gm j y _ (L.g i i')).val ^ N := by
  refine (congrArg Units.val (gm_linComb L _ _ (𝟙 _) y _ _ (Set.mem_iInter.2 fun _ => hi)
    (Set.mem_iInter.2 fun _ => hi'))).trans ?_
  simp only [zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Units.val_pow_eq_pow_val,
    Category.id_comp]

theorem pack_of_relAmple {S : Scheme.{0}} (A : Over S) (L : LB A.left) (U : S.Opens) (hU : IsAffineOpen U)
    (U₀ : S.Opens) (H : RelAmple (Over.mk (A.hom ∣_ U₀)) (L.pull (A.hom ⁻¹ᵁ U₀).ι)) (a : Γ(U.toScheme, ⊤))
    (ha : U.toScheme.basicOpen a ≤ U.ι ⁻¹ᵁ U₀) (c : (A.hom ⁻¹ᵁ U).toScheme → L.ι)
    (hc : ∀ z, (A.hom ⁻¹ᵁ U).ι z ∈ L.U (c z)) :
    ∃ W, IsLoc W ⊤ (cst (A.hom ∣_ U) a) ∧ Pack (fun i => (A.hom ⁻¹ᵁ U).ι ⁻¹ᵁ L.U i)
      (fun i z => (gm (A.hom ⁻¹ᵁ U).ι z _ (L.g i (c z))).val) W
      (insert (inv (cst (A.hom ∣_ U) a)) (Set.range (cst (A.hom ∣_ U)))) := by
  have : IsAffine U := hU
  have hle : U.ι ''ᵁ U.toScheme.basicOpen a ≤ U₀ := by
    rintro _ ⟨x, hx, rfl⟩
    exact ha hx
  let V : U₀.toScheme.Opens := U₀.ι ⁻¹ᵁ (U.ι ''ᵁ U.toScheme.basicOpen a)
  have hV : IsAffineOpen V := (((isAffineOpen_top U.toScheme).basicOpen a).image_of_isOpenImmersion
    U.ι).preimage_of_isOpenImmersion U₀.ι (by rwa [Scheme.Opens.opensRange_ι])
  obtain ⟨b, hb⟩ : ∃ b : V.toScheme ⟶ U.toScheme, b ≫ U.ι = V.ι ≫ U₀.ι :=
    ⟨IsOpenImmersion.lift U.ι (V.ι ≫ U₀.ι) (by
      rintro _ ⟨y, rfl⟩
      obtain ⟨x, -, hx⟩ := y.2
      exact ⟨x, hx⟩), IsOpenImmersion.lift_fac _ _ _⟩
  have : IsOpenImmersion (b ≫ U.ι) := by rw [hb]; infer_instance
  have : IsOpenImmersion b := IsOpenImmersion.of_comp b U.ι
  have hb' : b ''ᵁ ⊤ = U.toScheme.basicOpen a := by
    apply U.ι.image_injective
    show U.ι ''ᵁ b ''ᵁ ⊤ = U.ι ''ᵁ _
    rw [← Scheme.Hom.comp_image]
    simp only [hb]
    rw [Scheme.Hom.comp_image, Scheme.Opens.ι_image_top, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, inf_eq_right.2 hle]
  let p₀ := A.hom ∣_ U₀
  let j := (p₀ ⁻¹ᵁ V).ι ≫ (A.hom ⁻¹ᵁ U₀).ι
  have hj : j ≫ A.hom = (p₀ ∣_ V) ≫ b ≫ U.ι := by
    rw [hb, ← Category.assoc, morphismRestrict_ι, Category.assoc, Category.assoc, morphismRestrict_ι]
  obtain ⟨h, hh⟩ : ∃ h : (p₀ ⁻¹ᵁ V).toScheme ⟶ (A.hom ⁻¹ᵁ U).toScheme, h ≫ (A.hom ⁻¹ᵁ U).ι = j :=
    ⟨IsOpenImmersion.lift _ j (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q y ∈ U) hj).mpr (b ((p₀ ∣_ V) y)).2), IsOpenImmersion.lift_fac _ _ _⟩
  have : IsOpenImmersion (h ≫ (A.hom ⁻¹ᵁ U).ι) := by rw [hh]; infer_instance
  have : IsOpenImmersion h := IsOpenImmersion.of_comp h (A.hom ⁻¹ᵁ U).ι
  have e : h ≫ (A.hom ∣_ U) = (p₀ ∣_ V) ≫ b := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hh, hj, Category.assoc]
  have hu : ∀ z, IsUnit (cst (A.hom ∣_ U) a z) ↔ (A.hom ∣_ U) z ∈ U.toScheme.basicOpen a := fun z => by
    rw [← Category.comp_id (A.hom ∣_ U), ← pb_cst, pb_unit, Category.comp_id]
    exact ⟨fun hz => (loc_cst a _).2 ⟨trivial, hz⟩, fun hz => (loc_cst a).unit hz⟩
  refine ⟨h ''ᵁ ⊤, fun z => ⟨?_, fun hz => ?_⟩, pack_push h ?_⟩
  · rintro ⟨y, -, rfl⟩
    refine ⟨trivial, (hu _).2 ?_⟩
    rw [← hb']
    exact ⟨(p₀ ∣_ V) y, trivial, (congrArg (fun q => q y) e).symm⟩
  · have hz := (hu z).1 hz.2
    have e₁ : U.ι ((A.hom ∣_ U) z) = A.hom z.1 := morphismRestrict_base_coe A.hom U z
    have m₀ : z.1 ∈ A.hom ⁻¹ᵁ U₀ := by
      show A.hom z.1 ∈ U₀
      rw [← e₁]; exact ha hz
    have m₁ : (⟨z.1, m₀⟩ : (A.hom ⁻¹ᵁ U₀).toScheme) ∈ p₀ ⁻¹ᵁ V :=
      ⟨_, hz, e₁.trans (morphismRestrict_base_coe A.hom U₀ ⟨z.1, m₀⟩).symm⟩
    exact ⟨⟨_, m₁⟩, trivial, Subtype.ext (congrArg (fun q => q ⟨_, m₁⟩) hh)⟩
  obtain ⟨N, hN, M, s, cov, hs⟩ := H V hV
  choose aff r hr surj using hs
  let P := powOver (Over.mk p₀) (L.pull (A.hom ⁻¹ᵁ U₀).ι) V N
  let κ : L.ι → P.ι := fun i _ _ => i
  have pt : ∀ y, (A.hom ⁻¹ᵁ U).ι (h y) = (A.hom ⁻¹ᵁ U₀).ι ((p₀ ⁻¹ᵁ V).ι y) := fun y => congrArg (fun q => q y) hh
  have hκ : ∀ i, h ⁻¹ᵁ ((A.hom ⁻¹ᵁ U).ι ⁻¹ᵁ L.U i) ≤ P.U (κ i) := fun i y hy =>
    Set.mem_iInter.2 fun _ => mem_pull.2 (show (A.hom ⁻¹ᵁ U₀).ι ((p₀ ⁻¹ᵁ V).ι y) ∈ L.U i from pt y ▸ hy)
  have hγ : ∀ y, y ∈ P.U (κ (c (h y))) := fun y => hκ _ (hc (h y))
  refine Pack.mono (S := Set.range (cst (p₀ ∣_ V))) ⟨N, hN, M, fun i => sv (fun y => κ (c (h y))) (s i),
    fun i => nonzeroLocus (s i), fun i => sc_sv hκ (fun y => hc (h y)) (fun i y hy => ?_) (s i),
    fun i => loc_sv hγ (s i), fun y _ => Opens.mem_iSup.1 (cov.ge trivial), aff, fun i => ?_⟩ ?_
  · have hm : (A.hom ⁻¹ᵁ U).ι (h y) ∈ L.U i ⊓ L.U (c (h y)) := ⟨hy, hc (h y)⟩
    have m₁ : (p₀ ⁻¹ᵁ V).ι y ∈ (L.pull (A.hom ⁻¹ᵁ U₀).ι).U (fun _ => i) :=
      mem_pull.2 ((pt y) ▸ hm.1)
    have m₂ : (p₀ ⁻¹ᵁ V).ι y ∈ (L.pull (A.hom ⁻¹ᵁ U₀).ι).U (fun _ => c (h y)) :=
      mem_pull.2 ((pt y) ▸ hm.2)
    refine (gm_const _ _ N y _ _ m₁ m₂).trans ?_
    refine congrArg (· ^ N) ((congrArg Units.val (gm_pull_g L _ _ y _ _ m₁ m₂)).trans ?_)
    rw [pb_apply, ← gs_unit _ _ _ hm, stalkMap_gs h _ y _ hm, gs_unit _ y _ hm, hh]
  · exact (gen_iff _ (r i) _ _ (fun x y hy => (gs_appLE _ _ _ _ (𝟙 _) y hy x).trans
      (by rw [Category.id_comp, cst_apply]; rfl))
      (fun m => (ratio_iff hγ (s i) (s m) (r i m)).1 (hr i m))).2 (surj i)
  · rintro _ ⟨x, rfl⟩
    exact cst_mem a b hb' _ h _ e x

theorem relAmple_of_locally : ∀ (S : Scheme.{0}) (A : Over S) (L : LB A.left), L.IsLB → QuasiCompact A.hom →
    QuasiSeparated A.hom → (∀ s : S, ∃ (U : S.Opens) (_ : s ∈ U),
      RelAmple (Over.mk (A.hom ∣_ U)) (L.pull (A.hom ⁻¹ᵁ U).ι)) → RelAmple A L := by
  intro S A L hL _ _ H U hU
  have : IsAffine U := hU
  have : CompactSpace (A.hom ⁻¹ᵁ U).toScheme := QuasiCompact.compactSpace_of_compactSpace (A.hom ∣_ U)
  have : QuasiSeparatedSpace (A.hom ⁻¹ᵁ U).toScheme := quasiSeparatedSpace_of_quasiSeparated (A.hom ∣_ U)
  choose c hc using fun z : (A.hom ⁻¹ᵁ U).toScheme => exists_chart hL ((A.hom ⁻¹ᵁ U).ι z)
  let good : Set Γ(U.toScheme, ⊤) := {a | ∃ U₀ : S.Opens, U.toScheme.basicOpen a ≤ U.ι ⁻¹ᵁ U₀ ∧
    RelAmple (Over.mk (A.hom ∣_ U₀)) (L.pull (A.hom ⁻¹ᵁ U₀).ι)}
  have hspan : Ideal.span good = ⊤ := by
    rw [← (isAffineOpen_top U.toScheme).iSup_basicOpen_eq_self_iff, eq_top_iff]
    intro x _
    obtain ⟨U₀, hx, h₀⟩ := H (U.ι x)
    obtain ⟨a, ha, hxa⟩ := (isAffineOpen_top U.toScheme).exists_basicOpen_le (V := U.ι ⁻¹ᵁ U₀) ⟨x, hx⟩ trivial
    exact Opens.mem_iSup.2 ⟨⟨a, U₀, ha, h₀⟩, hxa⟩
  obtain ⟨t, ht, hspan'⟩ := (Ideal.span_eq_top_iff_finite _).1 hspan
  choose W hW hP using fun l : t => (ht l.2).elim fun U₀ h₀ => pack_of_relAmple A L U hU U₀ h₀.2 l.1 h₀.1 c hc
  have hcov : ∀ z, ∃ i, z ∈ (A.hom ⁻¹ᵁ U).ι ⁻¹ᵁ L.U i := fun z => ⟨c z, hc z⟩
  obtain ⟨N, hN, M, σ, hσ, cov, main⟩ := glue_pack hcov (fun _ _ => Units.isUnit _) (fun i j =>
      reg_congr (reg_gs (A.hom ⁻¹ᵁ U).ι _ (L.g i j).val) fun z hz => by
        show _ = (gm (A.hom ⁻¹ᵁ U).ι z _ (L.g i (c z))).val * Ring.inverse (gm (A.hom ⁻¹ᵁ U).ι z _ (L.g j (c z))).val
        rw [gs_unit _ z _ hz, Ring.inverse_unit, ← Units.val_mul, ← gm_cocycle hL _ z hz.1 hz.2 (hc z),
          mul_inv_cancel_right])
    (cst (A.hom ∣_ U)) (reg_cst _) (fun l : t => l.1) (by rw [Subtype.range_coe_subtype]; exact hspan') W hW hP
  let κ : L.ι → (powOver A L U N).ι := fun i _ => i
  have hκ : ∀ i, (A.hom ⁻¹ᵁ U).ι ⁻¹ᵁ L.U i ≤ (powOver A L U N).U (κ i) := fun i y hy => Set.mem_iInter.2 fun _ => hy
  have hγ : ∀ y, y ∈ (powOver A L U N).U (κ (c y)) := fun y => hκ _ (hc y)
  choose s hs using fun m => exists_sv hκ hc (fun i y hy => gm_const L _ N y _ _ hy (hc y))
    (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB L hL _ _) (hσ m)
  have loc : ∀ m, IsLoc (nonzeroLocus (s m)) ⊤ (σ m) := fun m => hs m ▸ loc_sv hγ (s m)
  refine ⟨N, hN, M, s, top_le_iff.1 fun z _ => ?_, fun i => ⟨(main i _ (loc i)).1, ?_⟩⟩
  · obtain ⟨m, hm⟩ := cov z
    exact Opens.mem_iSup.2 ⟨m, (loc m z).2 ⟨trivial, hm⟩⟩
  · choose r hr using fun m => mem_reg_iff.1 (Sc.ratio hcov (fun _ _ => Units.isUnit _) (hσ m) (hσ i) (loc i))
    refine ⟨r, fun m => (ratio_iff hγ (s i) (s m) (r m)).2 (by rw [hs, hs]; exact hr m), ?_⟩
    exact (gen_iff _ r _ _ (fun x y hy => (gs_appLE _ _ _ _ (𝟙 _) y hy x).trans
      (by rw [Category.id_comp, cst_apply])) hr).1 (main i _ (loc i)).2

end GlobalTheory.AmpleLocal
end
end
