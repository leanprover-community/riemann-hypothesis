import Formalism.SharpRestriction.GrowthBounds.ProofRowTieValsDef
import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjLieSelf
import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyEig2
import Formalism.LocalToGlobal.CharacterGerms.RowTieP_TCoord

section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VS

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {σ τ : Type} [Finite σ]

def UImg (V : VF C) (A : σ → MvPowerSeries τ C) (Φ : MvPowerSeries τ C) : Prop :=
  ∃ U : MvPowerSeries σ C, IsIU V U ∧ MvPowerSeries.subst A U = Φ

def GImg (V : VF C) (A : σ → MvPowerSeries τ C) (a : Fin dd → MvPowerSeries τ C) : Prop :=
  ∃ P : Fin dd → MvPowerSeries σ C, VP.GoodPt V P ∧ ∀ i, MvPowerSeries.subst A (P i) = a i

def Cg (V : VF C) (A : σ → MvPowerSeries τ C) (f g : MvPowerSeries τ C) : Prop :=
  MvPowerSeries.constantCoeff f = 0 ∧ MvPowerSeries.constantCoeff g = 0 ∧ UImg V A (mvExp (f - g))

variable {A : σ → MvPowerSeries τ C} (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0)

include hA

theorem UImg.one : UImg V A 1 := ⟨1, IsIU.one, VP.subst_one hA⟩

theorem UImg.mul {Φ Ψ : MvPowerSeries τ C} (h : UImg V A Φ) (h' : UImg V A Ψ) : UImg V A (Φ * Ψ) := by
  obtain ⟨U, hU, rfl⟩ := h
  obtain ⟨U', hU', rfl⟩ := h'
  exact ⟨U * U', hU.mul hU', VP.subst_mul hA _ _⟩

theorem UImg.pow {Φ : MvPowerSeries τ C} (h : UImg V A Φ) (k : ℕ) : UImg V A (Φ ^ k) := by
  obtain ⟨U, hU, rfl⟩ := h
  exact ⟨U ^ k, ⟨hU.1.pow k, by rw [map_pow, V.v.map_pow, hU.2, smul_zero]⟩, VP.subst_pow' hA _ _⟩

theorem UImg.exp_neg {f : MvPowerSeries τ C} (hf : MvPowerSeries.constantCoeff f = 0) (h : UImg V A (mvExp f)) :
    UImg V A (mvExp (-f)) := by
  obtain ⟨U, hU, e⟩ := h
  obtain ⟨U', hU'i, hUU⟩ := VP.intInv hU.1 hU.2
  have hU'0 : V.v (MvPowerSeries.constantCoeff U') = 0 := by
    have h1 := congrArg (fun x => V.v (MvPowerSeries.constantCoeff x)) hUU
    simp only [map_mul, map_one, V.v.map_mul, V.v.map_one, hU.2, add_zero] at h1
    exact h1
  refine ⟨U', ⟨hU'i, hU'0⟩, ?_⟩
  have h2 : MvPowerSeries.subst A U' * mvExp f = 1 := by
    rw [← e, ← VP.subst_mul hA, hUU, VP.subst_one hA]
  have h3 : mvExp (-f) * mvExp f = 1 := by
    rw [← VP.exp_add (by rw [map_neg, hf, neg_zero]) hf, neg_add_cancel, rtj_mvExp_zero]
  calc MvPowerSeries.subst A U' = MvPowerSeries.subst A U' * (mvExp (-f) * mvExp f) := by rw [h3, mul_one]
    _ = (MvPowerSeries.subst A U' * mvExp f) * mvExp (-f) := by ring
    _ = mvExp (-f) := by rw [h2, one_mul]

theorem Cg.refl {f : MvPowerSeries τ C} (hf : MvPowerSeries.constantCoeff f = 0) : Cg V A f f :=
  ⟨hf, hf, by rw [sub_self, rtj_mvExp_zero]; exact UImg.one hA⟩

theorem Cg.symm {f g : MvPowerSeries τ C} (h : Cg V A f g) : Cg V A g f :=
  ⟨h.2.1, h.1, by
    have := UImg.exp_neg hA (by rw [map_sub, h.1, h.2.1, sub_zero]) h.2.2
    rwa [neg_sub] at this⟩

theorem Cg.trans {f g k : MvPowerSeries τ C} (h : Cg V A f g) (h' : Cg V A g k) : Cg V A f k :=
  ⟨h.1, h'.2.1, by
    have := UImg.mul hA h.2.2 h'.2.2
    rw [← VP.exp_add (by rw [map_sub, h.1, h.2.1, sub_zero]) (by rw [map_sub, h'.1, h'.2.1, sub_zero])] at this
    rwa [sub_add_sub_cancel] at this⟩

theorem Cg.add {f g f' g' : MvPowerSeries τ C} (h : Cg V A f g) (h' : Cg V A f' g') : Cg V A (f + f') (g + g') :=
  ⟨by rw [map_add, h.1, h'.1, add_zero], by rw [map_add, h.2.1, h'.2.1, add_zero], by
    have := UImg.mul hA h.2.2 h'.2.2
    rw [← VP.exp_add (by rw [map_sub, h.1, h.2.1, sub_zero]) (by rw [map_sub, h'.1, h'.2.1, sub_zero])] at this
    rwa [show f - g + (f' - g') = f + f' - (g + g') by ring] at this⟩

theorem Cg.sum {ι : Type} (s : Finset ι) {f g : ι → MvPowerSeries τ C} (h : ∀ i ∈ s, Cg V A (f i) (g i)) :
    Cg V A (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  induction s using Finset.induction_on with
  | empty => simpa using (Cg.refl hA (map_zero _) : Cg V A (0 : MvPowerSeries τ C) 0)
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact Cg.add hA (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Cg.nsmul {f g : MvPowerSeries τ C} (h : Cg V A f g) (k : ℕ) : Cg V A ((k : C) • f) ((k : C) • g) :=
  ⟨VP.cc_smul _ h.1, VP.cc_smul _ h.2.1, by
    rw [← smul_sub, VP.exp_nsmul (by rw [map_sub, h.1, h.2.1, sub_zero])]
    exact UImg.pow hA h.2.2 k⟩

theorem Cg.unit {f g : MvPowerSeries τ C} (h : Cg V A f g) :
    ∃ U : MvPowerSeries σ C, IsIU V U ∧ mvExp f = MvPowerSeries.subst A U * mvExp g := by
  obtain ⟨U, hU, e⟩ := h.2.2
  refine ⟨U, hU, ?_⟩
  rw [e, ← VP.exp_add (by rw [map_sub, h.1, h.2.1, sub_zero]) h.2.1, sub_add_cancel]

theorem cg_of {F G : MvPowerSeries σ C} (hF : MvPowerSeries.constantCoeff F = 0)
    (hG : MvPowerSeries.constantCoeff G = 0) (hi : IntS V (mvExp (F - G))) :
    Cg V A (MvPowerSeries.subst A F) (MvPowerSeries.subst A G) :=
  ⟨VP.cc_subst hA hF, VP.cc_subst hA hG, mvExp (F - G), VP.isIU_of_exp hi rfl, by
    rw [VP.subst_exp hA (by rw [map_sub, hF, hG, sub_zero]), VP.subst_sub' hA]⟩

theorem GImg.cc {a : Fin dd → MvPowerSeries τ C} (h : GImg V A a) (i : Fin dd) :
    MvPowerSeries.constantCoeff (a i) = 0 := by
  obtain ⟨P, hP, e⟩ := h
  rw [← e i]
  exact VP.cc_subst hA (hP.1 i)

theorem GImg.zero : GImg V A (fun _ : Fin dd => (0 : MvPowerSeries τ C)) :=
  ⟨fun _ => 0, VP.GoodPt.zero, fun _ => VP.subst_zero' hA⟩

variable (Y : FBChart C V O dd)

theorem GImg.add {a b : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) (hb : GImg V A b) :
    GImg V A (VP.addAt Y a b) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain ⟨Q, hQ, e'⟩ := hb
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  obtain rfl : (fun i => MvPowerSeries.subst A (Q i)) = b := funext e'
  exact ⟨VP.addAt Y P Q, hP.add Y hQ, fun i => VP.addAt_subst Y hA hP.1 hQ.1 i⟩

theorem GImg.act (x : O) {a : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) : GImg V A (VP.actAt Y x a) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  exact ⟨VP.actAt Y x P, hP.act Y x, fun i => VP.actAt_subst Y hA hP.1 x i⟩

omit Y in
theorem GImg.map {Y : FBChart C V O dd} {φ : Pt C 1 dd} (hφ : IsEndo Y φ) {a : Fin dd → MvPowerSeries τ C}
    (ha : GImg V A a) : GImg V A (VP.mapAt φ a) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  exact ⟨VP.mapAt φ P, ⟨VP.cc_mapAt hφ.cc hP.1, fun i =>
    IntS.subst (a := fun q : Fin 1 × Fin dd => P q.2) (fun q => hP.1 q.2) (fun q => hP.2 q.2) (hφ.int i)⟩,
    fun i => VP.mapAt_subst hA φ hP.1 i⟩

theorem gauge_congr_additive_left {a b c : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) (hb : GImg V A b) (hc : GImg V A c) :
    Cg V A (VP.hAt Y (VP.addAt Y a b) c) (VP.hAt Y a c + VP.hAt Y b c) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain ⟨Q, hQ, e'⟩ := hb
  obtain ⟨R, hR, e''⟩ := hc
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  obtain rfl : (fun i => MvPowerSeries.subst A (Q i)) = b := funext e'
  obtain rfl : (fun i => MvPowerSeries.subst A (R i)) = c := funext e''
  have c1 := VP.cc_hAt Y hP.1 hR.1
  have c2 := VP.cc_hAt Y hQ.1 hR.1
  have c3 := VP.cc_hAt Y (VP.cc_addAt Y hP.1 hQ.1) hR.1
  have h := cg_of (V := V) hA (F := VP.hAt Y P R + VP.hAt Y Q R) (G := VP.hAt Y (VP.addAt Y P Q) R)
    (by rw [map_add, c1, c2, add_zero]) c3 (by
      rw [← VP.first_partial_law_at_points Y hP.1 hQ.1 hR.1]
      exact IntS.subst (VP.constantCoeff_triple_substitution hP.1 hQ.1 hR.1) (VP.integral_triple_substitution hP.2 hQ.2 hR.2) Y.intPh1)
  rw [VP.subst_add' hA, VP.hAt_subst Y hA hP.1 hR.1, VP.hAt_subst Y hA hQ.1 hR.1,
    VP.hAt_subst Y hA (VP.cc_addAt Y hP.1 hQ.1) hR.1, funext (VP.addAt_subst Y hA hP.1 hQ.1)] at h
  exact Cg.symm hA h

theorem gauge_congr_additive_right {a b c : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) (hb : GImg V A b) (hc : GImg V A c) :
    Cg V A (VP.hAt Y a (VP.addAt Y b c)) (VP.hAt Y a b + VP.hAt Y a c) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain ⟨Q, hQ, e'⟩ := hb
  obtain ⟨R, hR, e''⟩ := hc
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  obtain rfl : (fun i => MvPowerSeries.subst A (Q i)) = b := funext e'
  obtain rfl : (fun i => MvPowerSeries.subst A (R i)) = c := funext e''
  have c1 := VP.cc_hAt Y hP.1 hQ.1
  have c2 := VP.cc_hAt Y hP.1 hR.1
  have c3 := VP.cc_hAt Y hP.1 (VP.cc_addAt Y hQ.1 hR.1)
  have h := cg_of (V := V) hA (F := VP.hAt Y P Q + VP.hAt Y P R) (G := VP.hAt Y P (VP.addAt Y Q R))
    (by rw [map_add, c1, c2, add_zero]) c3 (by
      rw [← VP.second_partial_law_at_points Y hP.1 hQ.1 hR.1]
      exact IntS.subst (VP.constantCoeff_triple_substitution hP.1 hQ.1 hR.1) (VP.integral_triple_substitution hP.2 hQ.2 hR.2) Y.intPh2)
  rw [VP.subst_add' hA, VP.hAt_subst Y hA hP.1 hQ.1, VP.hAt_subst Y hA hP.1 hR.1,
    VP.hAt_subst Y hA hP.1 (VP.cc_addAt Y hQ.1 hR.1), funext (VP.addAt_subst Y hA hQ.1 hR.1)] at h
  exact Cg.symm hA h

theorem cg_sy {a b : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) (hb : GImg V A b) :
    Cg V A (VP.hAt Y b a) (VP.hAt Y a b) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain ⟨Q, hQ, e'⟩ := hb
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  obtain rfl : (fun i => MvPowerSeries.subst A (Q i)) = b := funext e'
  have h := cg_of (V := V) hA (F := VP.hAt Y Q P) (G := VP.hAt Y P Q) (VP.cc_hAt Y hQ.1 hP.1) (VP.cc_hAt Y hP.1 hQ.1) (by
      rw [← VP.sy_at Y hP.1 hQ.1]
      exact IntS.subst (VP.constantCoeff_pair_substitution hP.1 hQ.1) (VP.integral_pair_substitution hP.2 hQ.2) Y.intSy)
  rwa [VP.hAt_subst Y hA hQ.1 hP.1, VP.hAt_subst Y hA hP.1 hQ.1] at h

theorem cg_ad (x : O) {a b : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) (hb : GImg V A b) :
    Cg V A (VP.hAt Y (VP.actAt Y x a) b) (VP.hAt Y a (VP.actAt Y (star x) b)) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain ⟨Q, hQ, e'⟩ := hb
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  obtain rfl : (fun i => MvPowerSeries.subst A (Q i)) = b := funext e'
  have h := cg_of (V := V) hA (F := VP.hAt Y (VP.actAt Y x P) Q) (G := VP.hAt Y P (VP.actAt Y (star x) Q))
    (VP.cc_hAt Y (VP.cc_actAt Y x hP.1) hQ.1) (VP.cc_hAt Y hP.1 (VP.cc_actAt Y _ hQ.1)) (by
      rw [← VP.ad_at Y hP.1 hQ.1]
      exact IntS.subst (VP.constantCoeff_pair_substitution hP.1 hQ.1) (VP.integral_pair_substitution hP.2 hQ.2) (Y.intAd x))
  rwa [VP.hAt_subst Y hA (VP.cc_actAt Y x hP.1) hQ.1, VP.hAt_subst Y hA hP.1 (VP.cc_actAt Y _ hQ.1),
    funext (VP.actAt_subst Y hA hP.1 x), funext (VP.actAt_subst Y hA hQ.1 (star x))] at h

theorem cg_adj {φ φ' : Pt C 1 dd} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφ' : ∀ i, MvPowerSeries.constantCoeff (φ' i) = 0)
    (hadj : IntS V (FB.expS C (ev (n := 2) ![comp1 φ (pt C dd 0), pt C dd 1] Y.h -
      ev (n := 2) ![pt C dd 0, comp1 φ' (pt C dd 1)] Y.h)))
    {a b : Fin dd → MvPowerSeries τ C} (ha : GImg V A a) (hb : GImg V A b) :
    Cg V A (VP.hAt Y (VP.mapAt φ a) b) (VP.hAt Y a (VP.mapAt φ' b)) := by
  obtain ⟨P, hP, e⟩ := ha
  obtain ⟨Q, hQ, e'⟩ := hb
  obtain rfl : (fun i => MvPowerSeries.subst A (P i)) = a := funext e
  obtain rfl : (fun i => MvPowerSeries.subst A (Q i)) = b := funext e'
  have h := cg_of (V := V) hA (F := VP.hAt Y (VP.mapAt φ P) Q) (G := VP.hAt Y P (VP.mapAt φ' Q))
    (VP.cc_hAt Y (VP.cc_mapAt hφ hP.1) hQ.1) (VP.cc_hAt Y hP.1 (VP.cc_mapAt hφ' hQ.1)) (by
      rw [← VP.cmp_at Y hφ hφ' hP.1 hQ.1]
      exact IntS.subst (VP.constantCoeff_pair_substitution hP.1 hQ.1) (VP.integral_pair_substitution hP.2 hQ.2) hadj)
  rwa [VP.hAt_subst Y hA (VP.cc_mapAt hφ hP.1) hQ.1, VP.hAt_subst Y hA hP.1 (VP.cc_mapAt hφ' hQ.1),
    funext (VP.mapAt_subst hA φ hP.1), funext (VP.mapAt_subst hA φ' hQ.1)] at h

end VS

end Formalism.L2.FormalSeriesBounds
end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VS

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

section Defs

variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o))

def eW (w : WVO (IS I0)) : Fin dd → C := (p w.1).e w.2.2

def tyW (w : WVO (IS I0)) : ZMod d := (p w.1).ty0 w.2.2

def zeK (κ : WVO (IS I0) → C) (m : Fin dd) : MvPowerSeries (WVO (IS I0)) C :=
  ∑ w, (κ w * eW Y p w m) • (MvPowerSeries.X w : MvPowerSeries (WVO (IS I0)) C)

def EK (κ : WVO (IS I0) → C) : Fin dd → MvPowerSeries (WVO (IS I0)) C := VP.exAt Y (zeK Y p κ)

def AA : Fin 2 × Fin dd → MvPowerSeries (WVO (IS I0)) C := VP.linPt Y (uS Y p)

def GK (κ : WVO (IS I0) → C) : Prop := GImg V (AA Y p) (EK Y p κ)

def HK (κ κ' : WVO (IS I0) → C) : MvPowerSeries (WVO (IS I0)) C := VP.hAt Y (EK Y p κ) (EK Y p κ')

def kCol (col : Fin 2) (w : WVO (IS I0)) : C := (p w.1).gm (tyW Y p w) col w.2.1

def lamAct (x : O) (w : WVO (IS I0)) : C := (p w.1).em (tyW Y p w) x

def lamG (o : Orb) (r s : Fin 2) (w : WVO (IS I0)) : C := if w.1 = o then (p w.1).gm (tyW Y p w) r s else 0

def lamG' (o : Orb) (r s : Fin 2) (w : WVO (IS I0)) : C :=
  if w.1 = o then (p w.1).gm (tyW Y p w + (p w.1).hd) r s else 0

end Defs

def ind (s : Orb × Fin 2) (w : WVO (IS I0)) : C := if (w.1, w.2.1) = s then 1 else 0

variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o))

theorem cc_zeK (κ : WVO (IS I0) → C) (m : Fin dd) : MvPowerSeries.constantCoeff (zeK Y p κ m) = 0 := by
  simp [zeK]

theorem cc_EK (κ : WVO (IS I0) → C) (i : Fin dd) : MvPowerSeries.constantCoeff (EK Y p κ i) = 0 := by
  apply VP.cc_exAt
  intro m
  exact cc_zeK Y p κ m

theorem cc_AA (s : Fin 2 × Fin dd) : MvPowerSeries.constantCoeff (AA Y p s) = 0 := by
  obtain ⟨col, i⟩ := s
  exact cc_EK Y p (kCol Y p col) i

theorem cc_HK (κ κ' : WVO (IS I0) → C) : MvPowerSeries.constantCoeff (HK Y p κ κ') = 0 := by
  apply VP.cc_hAt <;> intro i <;> exact cc_EK Y p _ i

theorem AA_eq (col : Fin 2) (i : Fin dd) : AA Y p (col, i) = EK Y p (kCol Y p col) i := rfl

theorem GK_col (col : Fin 2) : GK Y p (kCol Y p col) :=
  ⟨fun i => MvPowerSeries.X (col, i), ⟨fun _ => VP.cc_X _, fun _ => VP.IntS_X _⟩, fun i => by
    rw [VP.subst_X (cc_AA Y p)]; rfl⟩

theorem zeK_add (κ κ' : WVO (IS I0) → C) (m : Fin dd) : zeK Y p (κ + κ') m = zeK Y p κ m + zeK Y p κ' m := by
  simp only [zeK, Pi.add_apply, add_mul, add_smul, Finset.sum_add_distrib]

theorem EK_add (κ κ' : WVO (IS I0) → C) : VP.addAt Y (EK Y p κ) (EK Y p κ') = EK Y p (κ + κ') := by
  unfold EK
  rw [← VP.ex_add Y (cc_zeK Y p κ) (cc_zeK Y p κ')]
  congr 1
  funext m
  exact (zeK_add Y p κ κ' m).symm

theorem EK_zero : EK Y p 0 = fun _ => 0 := by
  have hz : zeK Y p 0 = fun _ => 0 := by
    funext m
    simp [zeK]
  unfold EK
  rw [hz, VP.exAt_zero]

theorem EK_map {φ : Pt C 1 dd} (hφ : IsEndo Y φ) {lam : WVO (IS I0) → C}
    (hl : ∀ w, linAct φ (eW Y p w) = lam w • eW Y p w) (κ : WVO (IS I0) → C) :
    VP.mapAt φ (EK Y p κ) = EK Y p (lam * κ) := by
  funext i
  rw [show VP.mapAt φ (EK Y p κ) i = _ from
    endoLog_holds Y φ hφ.cc hφ.add (WVO (IS I0)) (zeK Y p κ) (cc_zeK Y p κ) i]
  show VP.exAt Y _ i = VP.exAt Y _ i
  congr 1
  funext m
  unfold zeK
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have h := congrFun (hl w) m
  unfold linAct at h
  rw [Pi.smul_apply, smul_eq_mul] at h
  rw [Pi.mul_apply, mul_right_comm, ← h, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem isEndo_act (x : O) : IsEndo Y (Y.B.A.act x) where
  int := Y.intAct x
  cc := Y.B.A.const x
  add := by
    simp only [VP.coordinateChange_comp1_intertwines_action, VP.addOf_eq']
    exact VP.actAt_addAt Y x (VP.cc_pt 0) (VP.cc_pt 1)

theorem EK_act (x : O) (κ : WVO (IS I0) → C) : VP.actAt Y x (EK Y p κ) = EK Y p (lamAct Y p x * κ) :=
  EK_map Y p (isEndo_act Y x) (fun w => (p w.1).e_eig w.2.2 x) κ

theorem GK.add {κ κ' : WVO (IS I0) → C} (h : GK Y p κ) (h' : GK Y p κ') : GK Y p (κ + κ') := by
  have h2 : GImg V (AA Y p) (VP.addAt Y (EK Y p κ) (EK Y p κ')) := by
    first
      | exact GImg.add (Y := Y) (cc_AA Y p) h h'
      | exact GImg.add (Y := Y) h h'
      | exact GImg.add (cc_AA Y p) h h'
  rw [EK_add] at h2
  exact h2

theorem GK.zero : GK Y p 0 := by
  unfold GK
  rw [EK_zero]
  first
    | exact GImg.zero (V := V) (A := AA Y p)
    | exact GImg.zero (V := V) (A := AA Y p) (cc_AA Y p)
    | exact GImg.zero (V := V) (A := AA Y p) (Y := Y)
    | exact GImg.zero (V := V) (A := AA Y p) (Y := Y) (cc_AA Y p)

theorem GK.sum {ι : Type} (s : Finset ι) {κ : ι → WVO (IS I0) → C} (h : ∀ i ∈ s, GK Y p (κ i)) :
    GK Y p (∑ i ∈ s, κ i) := by
  exact Finset.sum_induction κ (GK Y p) (fun a b ha hb => GK.add Y p ha hb) (GK.zero Y p) h

theorem GK.map {φ : Pt C 1 dd} (hφ : IsEndo Y φ) {lam : WVO (IS I0) → C}
    (hl : ∀ w, linAct φ (eW Y p w) = lam w • eW Y p w) {κ : WVO (IS I0) → C} (h : GK Y p κ) :
    GK Y p (lam * κ) := by
  have h2 : GImg V (AA Y p) (VP.mapAt φ (EK Y p κ)) := by
    first
      | exact GImg.map (cc_AA Y p) hφ h
      | exact GImg.map hφ (cc_AA Y p) h
      | exact GImg.map hφ h
  rw [EK_map Y p hφ hl] at h2
  exact h2

theorem GK.act (x : O) {κ : WVO (IS I0) → C} (h : GK Y p κ) : GK Y p (lamAct Y p x * κ) := by
  have h2 : GImg V (AA Y p) (VP.actAt Y x (EK Y p κ)) := by
    first
      | exact GImg.act (Y := Y) (cc_AA Y p) x h
      | exact GImg.act (Y := Y) x (cc_AA Y p) h
      | exact GImg.act (Y := Y) x h
  rw [EK_act] at h2
  exact h2

theorem kill_self (hs : SelfSep Y p) (o : Orb) (φ : Pt C 1 dd) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hcomm : ∀ a, comp1 φ (Y.B.A.act a) = comp1 (Y.B.A.act a) φ)
    (himg : ∀ v : Fin dd → C, ∃ b : I0 o → C, linAct φ v = ∑ c, b c • (p o).e c)
    (o' : Orb) (c' : I0 o') (ho : o' ≠ o) : linAct φ ((p o').e c') = 0 := by
  obtain ⟨b, hb⟩ := himg ((p o').e c')
  have h1 : ∀ a, linAct (Y.B.A.act a) (linAct φ ((p o').e c')) =
      (p o').em ((p o').ty0 c') a • linAct φ ((p o').e c') := by
    intro a
    rw [← VP.linAct_comp1 _ _ hφ, ← hcomm a, VP.linAct_comp1 _ _ (Y.B.A.const a), (p o').e_eig, VP.linAct_smul]
  have h2 : ∀ a, ∑ c, (b c * ((p o).em ((p o).ty0 c) a - (p o').em ((p o').ty0 c') a)) • (p o).e c = 0 := by
    intro a
    have h3 := h1 a
    rw [hb, VP.linAct_sum, Finset.smul_sum] at h3
    have h4 : ∀ c, linAct (Y.B.A.act a) (b c • (p o).e c) = (b c * (p o).em ((p o).ty0 c) a) • (p o).e c := by
      intro c
      rw [VP.linAct_smul, (p o).e_eig, smul_smul]
    rw [Finset.sum_congr rfl fun c _ => h4 c] at h3
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at h3
    rw [← h3]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [smul_smul, ← sub_smul]
    congr 1
    ring
  obtain ⟨W, -, hW⟩ := (p o).e_sat
  have hb0 : ∀ c, b c = 0 := by
    intro c
    obtain ⟨a, ha⟩ := hs (o, (p o).ty0 c) (o', (p o').ty0 c') (fun h => ho (Prod.mk.inj h).1.symm)
    have hne : (p o).em ((p o).ty0 c) a - (p o').em ((p o').ty0 c') a ≠ 0 := by
      intro h
      have h6 : V.v ((p o).em ((p o).ty0 c) a - (p o').em ((p o').ty0 c') a) = 0 := ha
      rw [h, V.v.map_zero] at h6
      exact WithTop.top_ne_zero h6
    have h7 : ∑ x, (∑ c'', (b c'' * ((p o).em ((p o).ty0 c'') a - (p o').em ((p o').ty0 c') a)) • (p o).e c'') x *
        W x c = 0 := by
      rw [h2 a]
      simp
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul] at h7
    rw [Finset.sum_comm] at h7
    have h8 : ∀ c'', ∑ x, b c'' * ((p o).em ((p o).ty0 c'') a - (p o').em ((p o').ty0 c') a) * (p o).e c'' x * W x c =
        if c'' = c then b c'' * ((p o).em ((p o).ty0 c'') a - (p o').em ((p o').ty0 c') a) else 0 := by
      intro c''
      have := hW c'' c
      simp only [mul_assoc]
      rw [← Finset.mul_sum, ← Finset.mul_sum, this]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun c'' _ => h8 c'', Finset.sum_ite_eq'] at h7
    simp only [Finset.mem_univ, if_true] at h7
    exact (mul_eq_zero.1 h7).resolve_right hne
  rw [hb]
  exact Finset.sum_eq_zero fun c _ => by rw [hb0 c, zero_smul]

section Pack

variable {Y p} {γ γ' : Orb → Fin 2 → Fin 2 → Pt C 1 dd} (hs : SelfSep Y p) (hG : ∀ o, GmPack Y (p o) (γ o) (γ' o))

include hs hG

theorem diagG (o : Orb) (r s : Fin 2) (w : WVO (IS I0)) :
    linAct (γ o r s) (eW Y p w) = lamG Y p o r s w • eW Y p w := by
  obtain ⟨o', g, c⟩ := w
  by_cases h : o' = o
  · subst h
    show _ = (if o' = o' then _ else _) • _
    rw [if_pos rfl]
    exact (hG o').lin r s c
  · show _ = (if o' = o then _ else _) • _
    rw [if_neg h, zero_smul]
    exact kill_self Y p hs o (γ o r s) ((hG o).endo r s).cc ((hG o).comm r s) ((hG o).img r s) o' c h

theorem diagG' (o : Orb) (r s : Fin 2) (w : WVO (IS I0)) :
    linAct (γ' o r s) (eW Y p w) = lamG' Y p o r s w • eW Y p w := by
  obtain ⟨o', g, c⟩ := w
  by_cases h : o' = o
  · subst h
    show _ = (if o' = o' then _ else _) • _
    rw [if_pos rfl]
    exact (hG o').lin' r s c
  · show _ = (if o' = o then _ else _) • _
    rw [if_neg h, zero_smul]
    exact kill_self Y p hs o (γ' o r s) ((hG o).endo' r s).cc ((hG o).comm' r s) ((hG o).img' r s) o' c h

theorem GK.mulG (o : Orb) (r s : Fin 2) {κ : WVO (IS I0) → C} (h : GK Y p κ) : GK Y p (lamG Y p o r s * κ) :=
  GK.map Y p ((hG o).endo r s) (diagG hs hG o r s) h

theorem GK.mulG' (o : Orb) (r s : Fin 2) {κ : WVO (IS I0) → C} (h : GK Y p κ) : GK Y p (lamG' Y p o r s * κ) :=
  GK.map Y p ((hG o).endo' r s) (diagG' hs hG o r s) h

end Pack

theorem fin_two_ne_one_sub : ∀ g g' : Fin 2, g' = g ↔ ¬ (1 - g = g') := by
  decide

theorem kCol_eq (col : Fin 2) : kCol Y p col = ∑ s : Orb × Fin 2, lamG Y p s.1 col s.2 * ind s := by
  funext w
  simp only [Finset.sum_apply, Pi.mul_apply, lamG, ind, kCol]
  rw [Finset.sum_eq_single (w.1, w.2.1)]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem ind_eq (s : Orb × Fin 2) : (ind s : WVO (IS I0) → C) = ∑ r, lamG' Y p s.1 r (1 - s.2) * kCol Y p r := by
  obtain ⟨o, g⟩ := s
  funext w
  rw [Finset.sum_apply]
  show (if (w.1, w.2.1) = (o, g) then (1 : C) else 0) =
    ∑ r, (if w.1 = o then (p w.1).gm (tyW Y p w + (p w.1).hd) r (1 - g) else 0) * (p w.1).gm (tyW Y p w) r w.2.1
  by_cases h : w.1 = o
  · simp only [if_pos h]
    rw [(p w.1).gm_hyp]
    by_cases hg : w.2.1 = g
    · rw [if_pos (Prod.ext h hg), if_neg ((fin_two_ne_one_sub g w.2.1).1 hg)]
    · rw [if_neg fun e => hg (Prod.mk.inj e).2, if_pos (not_not.1 fun e => hg ((fin_two_ne_one_sub g w.2.1).2 e))]
  · simp only [if_neg h, zero_mul, Finset.sum_const_zero]
    rw [if_neg fun e => h (Prod.mk.inj e).1]

theorem gram_eq (o o' : Orb) (g g' : Fin 2) (μ : WVO (IS I0) → C) :
    ∑ col, lamG' Y p o col g * (lamG Y p o' col g' * (μ * ind (o', g'))) =
      if (o', g') = (o, 1 - g) then μ * ind (o', g') else 0 := by
  funext w
  rw [Finset.sum_apply]
  simp only [Pi.mul_apply]
  by_cases hw : (w.1, w.2.1) = (o', g')
  · have h1 : w.1 = o' := (Prod.mk.inj hw).1
    by_cases ho : o' = o
    · have h2 : w.1 = o := h1.trans ho
      have e : ∀ col, lamG' Y p o col g w * (lamG Y p o' col g' w * (μ w * ind (o', g') w)) =
          ((p w.1).gm (tyW Y p w + (p w.1).hd) col g * (p w.1).gm (tyW Y p w) col g') * (μ w * ind (o', g') w) := by
        intro col
        unfold lamG' lamG
        rw [if_pos h2, if_pos h1]
        ring
      rw [Finset.sum_congr rfl fun col _ => e col, ← Finset.sum_mul, (p w.1).gm_hyp]
      by_cases hg : g = g'
      · rw [if_pos hg, zero_mul, if_neg fun h => (fin_two_ne_one_sub g g').1 hg.symm (Prod.mk.inj h).2.symm]
        rfl
      · rw [if_neg hg, one_mul, if_pos (Prod.ext ho (not_not.1 fun e => hg ((fin_two_ne_one_sub g g').2 fun e' => e e'.symm).symm))]
        rfl
    · have e : ∀ col, lamG' Y p o col g w * (lamG Y p o' col g' w * (μ w * ind (o', g') w)) = 0 := by
        intro col
        unfold lamG'
        rw [if_neg fun h => ho (h1.symm.trans h), zero_mul]
      rw [Finset.sum_eq_zero fun col _ => e col, if_neg fun h => ho (Prod.mk.inj h).1]
      rfl
  · have e : (ind (o', g') : WVO (IS I0) → C) w = 0 := if_neg hw
    simp only [e, mul_zero, Finset.sum_const_zero]
    split_ifs
    · rw [Pi.mul_apply, e, mul_zero]
    · rfl

section Pack2

variable {Y p} {γ γ' : Orb → Fin 2 → Fin 2 → Pt C 1 dd} (hs : SelfSep Y p) (hG : ∀ o, GmPack Y (p o) (γ o) (γ' o))

include hs hG

theorem GK_ind (s : Orb × Fin 2) : GK Y p (ind s) := by
  rw [ind_eq Y p s]
  exact GK.sum Y p Finset.univ fun r _ => GK.mulG' hs hG s.1 r (1 - s.2) (GK_col Y p r)

end Pack2

theorem toAllS_expPtS (o : Orb) (g col : Fin 2) (i : Fin dd) :
    toAllS (I := IS I0) o ((Y.rawSelf (p o)).expPt g (col, i)) = EK Y p (lamG Y p o col g * ind (o, g)) i := by
  unfold toAllS RawChart.expPt
  have h0 : ∀ x : Fin 2 × Fin dd, MvPowerSeries.constantCoeff (∑ c : I0 o, (Y.rawSelf (p o)).u g c x •
      (MvPowerSeries.X (⟨g, c⟩ : WV (IS I0 o)) : MvPowerSeries (WV (IS I0 o)) C)) = 0 := by
    intro m
    rw [map_sum]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_X, mul_zero]
  show MvPowerSeries.subst _ (MvPowerSeries.subst _ (MvPowerSeries.subst
    (fun x : Fin dd => (MvPowerSeries.X (col, x) : MvPowerSeries (Fin 2 × Fin dd) C)) (VP.e Y i))) = _
  rw [VP.subst_subst (fun _ => VP.cc_X _) h0, VP.subst_subst (fun m => by rw [VP.subst_X h0]; exact h0 _) (fun _ => VP.cc_X _)]
  show _ = MvPowerSeries.subst _ (VP.e Y i)
  congr 1
  funext m
  rw [VP.subst_X h0, VP.subst_sum (fun _ => VP.cc_X _)]
  unfold zeK
  rw [Fintype.sum_sigma, Finset.sum_eq_single o]
  · rw [Fintype.sum_sigma, Finset.sum_eq_single g]
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [VP.subst_smul (fun _ => VP.cc_X _), VP.subst_X (fun _ => VP.cc_X _)]
      congr 1
      rw [Pi.mul_apply]
      unfold lamG ind
      rw [if_pos rfl, if_pos rfl, mul_one]
      rfl
    · intro g' _ hg'
      refine Finset.sum_eq_zero fun c _ => ?_
      have : (ind (o, g) : WVO (IS I0) → C) ⟨o, ⟨g', c⟩⟩ = 0 := if_neg fun h => hg' (Prod.mk.inj h).2
      rw [Pi.mul_apply, this, mul_zero, zero_mul, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro o' _ ho'
    refine Finset.sum_eq_zero fun x _ => ?_
    have : (ind (o, g) : WVO (IS I0) → C) ⟨o', x⟩ = 0 := if_neg fun h => ho' (Prod.mk.inj h).1
    rw [Pi.mul_apply, this, mul_zero, zero_mul, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

end VS

theorem projSelf_of {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
    [NeZero d] {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]
    (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (hG : ∀ o, GmPackSt Y (p o)) : ProjSelfSt Y p := by
  intro hs o g
  choose γ γ' hG using hG
  have h : ∀ col : Fin 2, VS.GK Y p (VS.lamG Y p o col g * VS.ind (o, g)) := fun col =>
    VS.GK.mulG hs hG o col g (VS.GK_ind hs hG (o, g))
  choose P hP hPe using h
  refine ⟨fun x => P x.1 x.2, fun x => (hP x.1).2 x.2, fun x => (hP x.1).1 x.2, fun x => ?_⟩
  obtain ⟨col, i⟩ := x
  rw [VS.toAllS_expPtS]
  exact hPe col i

end Formalism.L2.FormalSeriesBounds
end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VS

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

theorem exp_sum {σ ι : Type} (s : Finset ι) {f : ι → MvPowerSeries σ C}
    (h : ∀ i ∈ s, MvPowerSeries.constantCoeff (f i) = 0) : mvExp (∑ i ∈ s, f i) = ∏ i ∈ s, mvExp (f i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty, Finset.prod_empty]
    ext m
    rw [MvPowerSeries.coeff_one]
    change ∑ k ∈ Finset.range (m.degree + 1),
      MvPowerSeries.coeff m ((0 : MvPowerSeries σ C) ^ k) / (k.factorial : C) = _
    rw [Finset.sum_range_succ']
    simp [MvPowerSeries.coeff_one]
  · intro a t ha ih h
    have ht : ∀ i ∈ t, MvPowerSeries.constantCoeff (f i) = 0 := fun i hi => h i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.prod_insert ha, VP.exp_add (h a (Finset.mem_insert_self a t)), ih ht]
    rw [map_sum]
    exact Finset.sum_eq_zero ht

variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o))

theorem HK_zeroR (κ : WVO (IS I0) → C) : HK Y p κ 0 = 0 := by
  show VP.hAt Y (EK Y p κ) (EK Y p 0) = 0
  rw [EK_zero]
  exact VP.hAt_zero_right (Y := Y) (cc_EK Y p κ)

theorem HK_zeroL (κ : WVO (IS I0) → C) : HK Y p 0 κ = 0 := by
  show VP.hAt Y (EK Y p 0) (EK Y p κ) = 0
  rw [EK_zero]
  exact VP.hAt_zero_left (Y := Y) (cc_EK Y p κ)

theorem HK_addL {κ₁ κ₂ κ' : WVO (IS I0) → C} (h₁ : GK Y p κ₁) (h₂ : GK Y p κ₂) (h' : GK Y p κ') :
    Cg V (AA Y p) (HK Y p (κ₁ + κ₂) κ') (HK Y p κ₁ κ' + HK Y p κ₂ κ') := by
  have e := gauge_congr_additive_left (Y := Y) (cc_AA Y p) h₁ h₂ h'
  rw [EK_add] at e
  exact e

theorem HK_addR {κ κ₁ κ₂ : WVO (IS I0) → C} (h : GK Y p κ) (h₁ : GK Y p κ₁) (h₂ : GK Y p κ₂) :
    Cg V (AA Y p) (HK Y p κ (κ₁ + κ₂)) (HK Y p κ κ₁ + HK Y p κ κ₂) := by
  have e := gauge_congr_additive_right (Y := Y) (cc_AA Y p) h h₁ h₂
  rw [EK_add] at e
  exact e

theorem HK_sumL {ι : Type} (s : Finset ι) {κ : ι → WVO (IS I0) → C} (h : ∀ i ∈ s, GK Y p (κ i))
    {κ' : WVO (IS I0) → C} (h' : GK Y p κ') :
    Cg V (AA Y p) (HK Y p (∑ i ∈ s, κ i) κ') (∑ i ∈ s, HK Y p (κ i) κ') := by
  classical
  have hG : ∀ t : Finset ι, (∀ i ∈ t, GK Y p (κ i)) → GK Y p (∑ i ∈ t, κ i) := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · intro _
      show GImg V (AA Y p) (EK Y p (∑ i ∈ (∅ : Finset ι), κ i))
      rw [Finset.sum_empty, EK_zero]
      exact GImg.zero (cc_AA Y p)
    · intro a t ha ih ht
      show GImg V (AA Y p) (EK Y p (∑ i ∈ insert a t, κ i))
      rw [Finset.sum_insert ha, ← EK_add]
      exact GImg.add (Y := Y) (cc_AA Y p) (ht a (Finset.mem_insert_self a t))
        (ih fun i hi => ht i (Finset.mem_insert_of_mem hi))
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    rw [HK_zeroL]
    exact Cg.refl (cc_AA Y p) (map_zero _)
  · intro a t ha ih h
    have ht : ∀ i ∈ t, GK Y p (κ i) := fun i hi => h i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact Cg.trans (cc_AA Y p) (HK_addL Y p (h a (Finset.mem_insert_self a t)) (hG t ht) h')
      (Cg.add (cc_AA Y p) (Cg.refl (cc_AA Y p) (cc_HK Y p _ _)) (ih ht))

theorem HK_sumR {ι : Type} (s : Finset ι) {κ : ι → WVO (IS I0) → C} (h : ∀ i ∈ s, GK Y p (κ i))
    {κ' : WVO (IS I0) → C} (h' : GK Y p κ') :
    Cg V (AA Y p) (HK Y p κ' (∑ i ∈ s, κ i)) (∑ i ∈ s, HK Y p κ' (κ i)) := by
  classical
  have hG : ∀ t : Finset ι, (∀ i ∈ t, GK Y p (κ i)) → GK Y p (∑ i ∈ t, κ i) := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · intro _
      show GImg V (AA Y p) (EK Y p (∑ i ∈ (∅ : Finset ι), κ i))
      rw [Finset.sum_empty, EK_zero]
      exact GImg.zero (cc_AA Y p)
    · intro a t ha ih ht
      show GImg V (AA Y p) (EK Y p (∑ i ∈ insert a t, κ i))
      rw [Finset.sum_insert ha, ← EK_add]
      exact GImg.add (Y := Y) (cc_AA Y p) (ht a (Finset.mem_insert_self a t))
        (ih fun i hi => ht i (Finset.mem_insert_of_mem hi))
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    rw [HK_zeroR]
    exact Cg.refl (cc_AA Y p) (map_zero _)
  · intro a t ha ih h
    have ht : ∀ i ∈ t, GK Y p (κ i) := fun i hi => h i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact Cg.trans (cc_AA Y p) (HK_addR Y p h' (h a (Finset.mem_insert_self a t)) (hG t ht))
      (Cg.add (cc_AA Y p) (Cg.refl (cc_AA Y p) (cc_HK Y p _ _)) (ih ht))

theorem HK_sy {κ κ' : WVO (IS I0) → C} (h : GK Y p κ) (h' : GK Y p κ') :
    Cg V (AA Y p) (HK Y p κ' κ) (HK Y p κ κ') :=
  cg_sy (Y := Y) (cc_AA Y p) h h'

theorem HK_ad (x : O) {κ κ' : WVO (IS I0) → C} (h : GK Y p κ) (h' : GK Y p κ') :
    Cg V (AA Y p) (HK Y p (lamAct Y p x * κ) κ') (HK Y p κ (lamAct Y p (star x) * κ')) := by
  have e := cg_ad (Y := Y) (cc_AA Y p) x h h'
  simp only [EK_act] at e
  exact e

theorem lamAct_tr : lamAct Y p Y.w0 + lamAct Y p (star Y.w0) = 1 := by
  funext w
  simp only [Pi.add_apply, Pi.one_apply, lamAct]
  rw [← map_add, Y.halfIntegralGenerator_add_conj_eq_one, map_one]

theorem HK_pair {a b : WVO (IS I0) → C} (ha : GK Y p a) (hb : GK Y p b) :
    Cg V (AA Y p) (HK Y p a (lamAct Y p Y.w0 * b) + HK Y p b (lamAct Y p Y.w0 * a)) (HK Y p a b) := by
  have hA := cc_AA Y p
  have e1 : Cg V (AA Y p) (HK Y p b (lamAct Y p Y.w0 * a)) (HK Y p a (lamAct Y p (star Y.w0) * b)) :=
    Cg.trans hA (HK_sy Y p (GK.act Y p Y.w0 ha) hb) (HK_ad Y p Y.w0 ha hb)
  have e3 := HK_addR Y p ha (GK.act Y p Y.w0 hb) (GK.act Y p (star Y.w0) hb)
  have e4 : lamAct Y p Y.w0 * b + lamAct Y p (star Y.w0) * b = b := by
    rw [← add_mul, lamAct_tr, one_mul]
  rw [e4] at e3
  exact Cg.trans hA (Cg.add hA (Cg.refl hA (cc_HK Y p _ _)) e1) (Cg.symm hA e3)

section Pack

variable {Y p} {γ γ' : Orb → Fin 2 → Fin 2 → Pt C 1 dd} (hs : SelfSep Y p) (hG : ∀ o, GmPack Y (p o) (γ o) (γ' o))

include hs hG

theorem HK_adj (o : Orb) (r s : Fin 2) {κ κ' : WVO (IS I0) → C} (h : GK Y p κ) (h' : GK Y p κ') :
    Cg V (AA Y p) (HK Y p (lamG Y p o r s * κ) κ') (HK Y p κ (lamG' Y p o r s * κ')) := by
  have hA := cc_AA Y p
  have e := cg_adj (Y := Y) hA ((hG o).endo r s).cc ((hG o).endo' r s).cc ((hG o).adj r s) h h'
  rw [EK_map Y p ((hG o).endo r s) (diagG hs hG o r s) κ,
    EK_map Y p ((hG o).endo' r s) (diagG' hs hG o r s) κ'] at e
  exact e

theorem HK_key (o o' : Orb) (g g' : Fin 2) {κ κ' : WVO (IS I0) → C} (h : GK Y p κ) (h' : GK Y p κ') :
    Cg V (AA Y p) (∑ col, HK Y p (lamG Y p o col g * κ) (lamG Y p o' col g' * κ'))
      (HK Y p κ (∑ col, lamG' Y p o col g * (lamG Y p o' col g' * κ'))) := by
  have hA := cc_AA Y p
  refine Cg.trans hA (Cg.sum hA Finset.univ fun col _ =>
    HK_adj hs hG o col g h (GK.mulG hs hG o' col g' h')) ?_
  exact Cg.symm hA (HK_sumR Y p Finset.univ
    (fun col _ => GK.mulG' hs hG o col g (GK.mulG hs hG o' col g' h')) h)

theorem HK_gram (o o' : Orb) (g g' : Fin 2) {μ : WVO (IS I0) → C} (hμ : GK Y p (μ * ind (o', g'))) :
    Cg V (AA Y p) (∑ col, HK Y p (lamG Y p o col g * ind (o, g)) (lamG Y p o' col g' * (μ * ind (o', g'))))
      (HK Y p (ind (o, g)) (if (o', g') = (o, 1 - g) then μ * ind (o', g') else 0)) := by
  have e := HK_key hs hG o o' g g' (GK_ind hs hG (o, g)) hμ
  rw [gram_eq] at e
  exact e

theorem main_cg :
    Cg V (AA Y p) (∑ col, HK Y p (kCol Y p col) (lamAct Y p Y.w0 * kCol Y p col))
      (∑ o, ∑ col, HK Y p (lamG Y p o col 0 * ind (o, 0)) (lamG Y p o col 1 * ind (o, 1))) := by
  classical
  have hA := cc_AA Y p
  have ha : ∀ (col : Fin 2) (s : Orb × Fin 2), GK Y p (lamG Y p s.1 col s.2 * ind s) :=
    fun col s => GK.mulG hs hG s.1 col s.2 (GK_ind hs hG s)
  have e1 : ∀ col : Fin 2, Cg V (AA Y p) (HK Y p (kCol Y p col) (lamAct Y p Y.w0 * kCol Y p col))
      (∑ s : Orb × Fin 2, ∑ t : Orb × Fin 2, HK Y p (lamG Y p s.1 col s.2 * ind s)
        (lamG Y p t.1 col t.2 * (lamAct Y p Y.w0 * ind t))) := by
    intro col
    have hK : GK Y p (lamAct Y p Y.w0 * kCol Y p col) := GK.act Y p Y.w0 (GK_col Y p col)
    have hsum := HK_sumL Y p Finset.univ (κ := fun s : Orb × Fin 2 => lamG Y p s.1 col s.2 * ind s)
      (fun s _ => ha col s) hK
    beta_reduce at hsum
    rw [← kCol_eq] at hsum
    refine Cg.trans hA hsum (Cg.sum hA Finset.univ fun s _ => ?_)
    have hR := HK_sumR Y p Finset.univ
      (κ := fun t : Orb × Fin 2 => lamG Y p t.1 col t.2 * (lamAct Y p Y.w0 * ind t))
      (fun t _ => GK.mulG hs hG t.1 col t.2 (GK.act Y p Y.w0 (GK_ind hs hG t))) (ha col s)
    beta_reduce at hR
    have hE : (∑ t : Orb × Fin 2, lamG Y p t.1 col t.2 * (lamAct Y p Y.w0 * ind t)) =
        lamAct Y p Y.w0 * kCol Y p col := by
      rw [kCol_eq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [hE] at hR
    exact hR
  have e2 : Cg V (AA Y p) (∑ col : Fin 2, HK Y p (kCol Y p col) (lamAct Y p Y.w0 * kCol Y p col))
      (∑ s : Orb × Fin 2, ∑ t : Orb × Fin 2,
        HK Y p (ind s) (if t = (s.1, 1 - s.2) then lamAct Y p Y.w0 * ind t else 0)) := by
    refine Cg.trans hA (Cg.sum hA Finset.univ fun col _ => e1 col) ?_
    rw [Finset.sum_comm]
    refine Cg.sum hA Finset.univ fun s _ => ?_
    rw [Finset.sum_comm]
    exact Cg.sum hA Finset.univ fun t _ =>
      HK_gram hs hG s.1 t.1 s.2 t.2 (GK.act Y p Y.w0 (GK_ind hs hG t))
  have e3 : ∀ s : Orb × Fin 2, (∑ t : Orb × Fin 2,
      HK Y p (ind s) (if t = (s.1, 1 - s.2) then lamAct Y p Y.w0 * ind t else 0)) =
      HK Y p (ind s) (lamAct Y p Y.w0 * ind (s.1, 1 - s.2)) := by
    intro s
    simp only [apply_ite (HK Y p (ind s)), HK_zeroR, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have e4 : (∑ s : Orb × Fin 2, HK Y p (ind s) (lamAct Y p Y.w0 * ind (s.1, 1 - s.2))) =
      ∑ o : Orb, (HK Y p (ind (o, 0)) (lamAct Y p Y.w0 * ind (o, 1)) +
        HK Y p (ind (o, 1)) (lamAct Y p Y.w0 * ind (o, 0))) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Fin.sum_univ_two]
    simp
  have e5 : Cg V (AA Y p) (∑ o : Orb, (HK Y p (ind (o, 0)) (lamAct Y p Y.w0 * ind (o, 1)) +
      HK Y p (ind (o, 1)) (lamAct Y p Y.w0 * ind (o, 0)))) (∑ o : Orb, HK Y p (ind (o, 0)) (ind (o, 1))) :=
    Cg.sum hA Finset.univ fun o _ => HK_pair Y p (GK_ind hs hG (o, 0)) (GK_ind hs hG (o, 1))
  have e6 : Cg V (AA Y p)
      (∑ o, ∑ col, HK Y p (lamG Y p o col 0 * ind (o, 0)) (lamG Y p o col 1 * ind (o, 1)))
      (∑ o : Orb, HK Y p (ind (o, 0)) (ind (o, 1))) := by
    refine Cg.sum hA Finset.univ fun o _ => ?_
    have hμ : GK Y p (1 * ind (o, 1)) := by rw [one_mul]; exact GK_ind hs hG (o, 1)
    have e := HK_gram hs hG o o 0 1 hμ
    have hc : ((o, (1 : Fin 2)) = (o, 1 - 0)) := by simp
    rw [if_pos hc] at e
    simp only [one_mul] at e
    exact e
  have e23 := e2
  simp only [e3] at e23
  rw [e4] at e23
  exact Cg.trans hA e23 (Cg.trans hA e5 (Cg.symm hA e6))

end Pack

theorem pullback_exp_column (col : Fin 2) :
    pull2 Y p (ev (n := 2) ![pt C dd col] (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0))) =
      mvExp ((Y.k : C) • HK Y p (kCol Y p col) (lamAct Y p Y.w0 * kCol Y p col)) := by
  have hAA0 : ∀ q : Fin 2 × Fin dd, MvPowerSeries.constantCoeff (VP.linPt Y (uS Y p) q) = 0 :=
    fun q => cc_AA Y p q
  have hAA : MvPowerSeries.HasSubst (VP.linPt Y (uS Y p)) := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hAA0
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent fun q => by
          rw [(hAA0) q]; exact IsNilpotent.zero
  have hb0 : ∀ q : Fin 1 × Fin dd, MvPowerSeries.constantCoeff (AA Y p (col, q.2)) = 0 :=
    fun q => cc_AA Y p _
  have hb : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => AA Y p (col, q.2)) := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hb0
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent fun q => by
          rw [(hb0) q]; exact IsNilpotent.zero
  have hpc0 : ∀ q : Fin 1 × Fin dd,
      MvPowerSeries.constantCoeff ((![pt C dd col] : Fin 1 → Pt C 2 dd) q.1 q.2) = 0 := by
    rintro ⟨j, i⟩
    fin_cases j
    exact MvPowerSeries.constantCoeff_X _
  have hpc : MvPowerSeries.HasSubst
      (fun q : Fin 1 × Fin dd => (![pt C dd col] : Fin 1 → Pt C 2 dd) q.1 q.2) := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hpc0
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent fun q => by
          rw [(hpc0) q]; exact IsNilpotent.zero
  have hp00 : ∀ q : Fin 1 × Fin dd,
      MvPowerSeries.constantCoeff ((![pt C dd 0] : Fin 1 → Pt C 1 dd) q.1 q.2) = 0 := by
    rintro ⟨j, i⟩
    fin_cases j
    exact MvPowerSeries.constantCoeff_X _
  have hp0 : MvPowerSeries.HasSubst
      (fun q : Fin 1 × Fin dd => (![pt C dd 0] : Fin 1 → Pt C 1 dd) q.1 q.2) := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hp00
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent fun q => by
          rw [(hp00) q]; exact IsNilpotent.zero
  have hbX : ∀ i : Fin dd, MvPowerSeries.subst (fun q : Fin 1 × Fin dd => AA Y p (col, q.2))
      (MvPowerSeries.X ((0 : Fin 1), i) : MvPowerSeries (Fin 1 × Fin dd) C) = EK Y p (kCol Y p col) i := by
    intro i
    rw [MvPowerSeries.subst_X hb]
    exact AA_eq Y p col i
  have hF : MvPowerSeries.constantCoeff ((Y.k : C) • Y.B.hL C Y.h Y.w0) = 0 := by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, VP.cc_hL, mul_zero]
  have s1 : pull2 Y p (ev (n := 2) ![pt C dd col] (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0))) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => AA Y p (col, q.2))
        (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)) := by
    unfold pull2 VP.linPull ev
    rw [MvPowerSeries.subst_comp_subst_apply hpc hAA]
    congr 1
    funext q
    rcases q with ⟨j, i⟩
    fin_cases j
    show MvPowerSeries.subst (VP.linPt Y (uS Y p)) (MvPowerSeries.X (col, i)) = _
    rw [MvPowerSeries.subst_X hAA]
    rfl
  rw [s1, VP.expS_eq _ hF, VP.subst_exp hb0 hF]
  congr 1
  rw [← MvPowerSeries.coe_substAlgHom hb, map_smul, MvPowerSeries.coe_substAlgHom]
  congr 1
  unfold FB.hL
  rw [VP.eval_two_points_eq_subst _ _ _ rfl]
  change MvPowerSeries.subst _ (VP.hAt Y (pt C dd 0) (comp1 (Y.B.actK C Y.w0) (pt C dd 0))) = _
  rw [VP.hAt_subst (u := pt C dd 0) (v := comp1 (Y.B.actK C Y.w0) (pt C dd 0)) (hA := hb0)
    (hu := fun i => by exact MvPowerSeries.constantCoeff_X _) (hv := fun i => by
    show MvPowerSeries.constantCoeff (MvPowerSeries.subst
      (fun q : Fin 1 × Fin dd => (![pt C dd 0] : Fin 1 → Pt C 1 dd) q.1 q.2) (Y.B.A.act Y.w0 i)) = 0
    rw [VP.cc_subst_eq hp00]
    exact (isEndo_act Y Y.w0).cc i)]
  show VP.hAt Y _ _ = VP.hAt Y (EK Y p (kCol Y p col)) (EK Y p (lamAct Y p Y.w0 * kCol Y p col))
  rw [← EK_act]
  congr 1
  · funext i
    exact hbX i
  · funext i
    show MvPowerSeries.subst (fun q : Fin 1 × Fin dd => AA Y p (col, q.2))
        (ev ![pt C dd 0] (Y.B.actK C Y.w0 i)) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => EK Y p (kCol Y p col) q.2) (Y.B.A.act Y.w0 i)
    unfold ev
    rw [MvPowerSeries.subst_comp_subst_apply hp0 hb]
    have hfun : (fun q : Fin 1 × Fin dd => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => AA Y p (col, q.2))
        ((![pt C dd 0] : Fin 1 → Pt C 1 dd) q.1 q.2)) = fun q => EK Y p (kCol Y p col) q.2 := by
      funext q
      rcases q with ⟨j, i⟩
      fin_cases j
      exact hbX i
    rw [hfun]
    congr 1

theorem cc_expPtS (o : Orb) (g : Fin 2) (x : Fin 2 × Fin dd) :
    MvPowerSeries.constantCoeff ((Y.rawSelf (p o)).expPt g x) = 0 := by
  obtain ⟨col, i⟩ := x
  have h0 : MvPowerSeries.constantCoeff (toAllS (I := IS I0) o ((Y.rawSelf (p o)).expPt g (col, i))) = 0 := by
    rw [toAllS_expPtS]
    exact cc_EK Y p _ _
  rw [toAllS, VP.cc_subst_eq] at h0
  · exact h0
  · intro w
    exact MvPowerSeries.constantCoeff_X _

theorem hRow_eqS (o : Orb) : (Y.rawSelf (p o)).hRow = (Y.k : C) • ∑ col : Fin 2,
    VP.hAt Y (fun i => (Y.rawSelf (p o)).expPt 0 (col, i)) (fun i => (Y.rawSelf (p o)).expPt 1 (col, i)) := by
  have hS : MvPowerSeries.HasSubst
      (fun q : Fin 2 × (Fin 2 × Fin dd) => (Y.rawSelf (p o)).expPt q.1 q.2) :=
    by first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => cc_expPtS Y p o q.1 q.2
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent fun q => by
          rw [cc_expPtS Y p o q.1 q.2]; exact IsNilpotent.zero
  unfold RawChart.hRow
  congr 1
  show MvPowerSeries.subst (fun q : Fin 2 × (Fin 2 × Fin dd) => (Y.rawSelf (p o)).expPt q.1 q.2)
    (∑ col, hCol col Y.h) = _
  rw [← MvPowerSeries.coe_substAlgHom hS, map_sum]
  refine Finset.sum_congr rfl fun col _ => ?_
  have hX : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin dd =>
      (MvPowerSeries.X (q.1, (col, q.2)) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C)) :=
    by first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => MvPowerSeries.constantCoeff_X _
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent fun q => by
          rw [MvPowerSeries.constantCoeff_X]; exact IsNilpotent.zero
  rw [MvPowerSeries.coe_substAlgHom, hCol, MvPowerSeries.subst_comp_subst_apply hX hS]
  simp only [MvPowerSeries.subst_X hS]
  unfold VP.hAt
  congr 1
  funext q
  rcases q with ⟨g, i⟩
  fin_cases g <;> first | rfl | simp [VP.P2]

theorem toAllS_hRow (o : Orb) : toAllS (I := IS I0) o (mvExp (Y.rawSelf (p o)).hRow) =
    mvExp ((Y.k : C) • ∑ col, HK Y p (lamG Y p o col 0 * ind (o, 0)) (lamG Y p o col 1 * ind (o, 1))) := by
  have hX : ∀ w : WV (IS I0 o), MvPowerSeries.constantCoeff
      ((MvPowerSeries.X (⟨o, w⟩ : WVO (IS I0))) : MvPowerSeries (WVO (IS I0)) C) = 0 :=
    fun w => MvPowerSeries.constantCoeff_X _
  have hcc : MvPowerSeries.constantCoeff (Y.rawSelf (p o)).hRow = 0 := by
    rw [hRow_eqS, MvPowerSeries.smul_eq_C_mul, map_mul, map_sum,
      Finset.sum_eq_zero fun col _ => VP.cc_hAt (Y := Y) (fun i => cc_expPtS Y p o 0 (col, i))
        (fun i => cc_expPtS Y p o 1 (col, i)), mul_zero]
  have hS : MvPowerSeries.HasSubst (fun w : WV (IS I0 o) =>
      ((MvPowerSeries.X (⟨o, w⟩ : WVO (IS I0))) : MvPowerSeries (WVO (IS I0)) C)) := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hX
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent fun w => by
          rw [hX w]; exact IsNilpotent.zero
  unfold toAllS
  rw [VP.subst_exp hX hcc, hRow_eqS]
  congr 1
  rw [← MvPowerSeries.coe_substAlgHom hS, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun col _ => ?_
  rw [MvPowerSeries.coe_substAlgHom, VP.hAt_subst (hA := hX) (hu := fun i => cc_expPtS Y p o 0 (col, i))
    (hv := fun i => cc_expPtS Y p o 1 (col, i))]
  show VP.hAt Y _ _ = VP.hAt Y (EK Y p _) (EK Y p _)
  congr 1 <;> funext i <;> exact toAllS_expPtS Y p o _ col i

end VS

theorem unitSelf_of {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
    [NeZero d] {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]
    (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (hG : ∀ o, GmPackSt Y (p o)) : UnitSelfSt Y p := by
  intro hs
  choose γ γ' hγ using hG
  have hA := VS.cc_AA Y p
  have hk := VS.Cg.nsmul hA (VS.main_cg hs hγ) Y.k
  obtain ⟨U, hU, hE⟩ := VS.Cg.unit hA hk
  refine ⟨U, hU.1, hU.2, ?_⟩
  have hL : pull2 Y p (∏ col : Fin 2, ev (n := 2) ![pt C dd col] (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0))) =
      mvExp ((Y.k : C) • ∑ col : Fin 2,
        VS.HK Y p (VS.kCol Y p col) (VS.lamAct Y p Y.w0 * VS.kCol Y p col)) := by
    rw [VP.pullback_two_var_prod]
    simp only [VS.pullback_exp_column]
    rw [Finset.smul_sum, VS.exp_sum]
    intro col _
    exact (VS.Cg.nsmul hA (VS.Cg.refl (V := V) hA (VS.cc_HK Y p _ _)) Y.k).1
  have hR : ∏ o, toAllS (I := IS I0) o (mvExp (Y.rawSelf (p o)).hRow) =
      mvExp ((Y.k : C) • ∑ o, ∑ col, VS.HK Y p (VS.lamG Y p o col 0 * VS.ind (o, 0))
        (VS.lamG Y p o col 1 * VS.ind (o, 1))) := by
    simp only [VS.toAllS_hRow]
    rw [Finset.smul_sum, VS.exp_sum]
    intro o _
    have h0 : MvPowerSeries.constantCoeff (∑ col, VS.HK Y p (VS.lamG Y p o col 0 * VS.ind (o, 0))
        (VS.lamG Y p o col 1 * VS.ind (o, 1))) = 0 := by
      rw [map_sum]
      exact Finset.sum_eq_zero fun _ _ => VS.cc_HK Y p _ _
    exact (VS.Cg.nsmul hA (VS.Cg.refl (V := V) hA h0) Y.k).1
  rw [hL, hR]
  exact hE

end Formalism.L2.FormalSeriesBounds
end
end

section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ RowTiePE0 RowTiePProj

namespace GmPackP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd d : ℕ}

theorem half [NeZero d] (hLie : ProjLieSelfSt) (Y : FBChart C V O dd) {I0 : Type} [Fintype I0] (p : SelfData Y d I0) (ε : O)
    (hε : ∃ y, ε * ε - ε = (V.l : O) * y) (hε1 : ∀ a, V.MM (p.em a ε - 1))
    (hεx : ∀ x : O, (∀ a, V.MM (p.em a x)) → ∃ y, ε * x = (V.l : O) * y) (M : ℕ → O) (φ : Pt C 1 dd)
    (hT : ∀ i, TendsS V (fun n => Y.B.A.act (M n * ε ^ V.l ^ n) i) (φ i)) :
    (∀ a, comp1 φ (Y.B.A.act a) = comp1 (Y.B.A.act a) φ) ∧
      ∀ v : Fin dd → C, ∃ b : I0 → C, linAct φ v = ∑ c, b c • p.e c := by
  have hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0 := const_of_lim Y hT
  have act0 : ∀ x i, MvPowerSeries.constantCoeff (Y.B.A.act x i) = 0 := Y.B.A.const
  refine ⟨?_, ?_⟩
  · intro a
    funext i
    have L := TendsS.comp1 (φ := fun n => Y.B.A.act (M n * ε ^ V.l ^ n)) (b := fun _ => Y.B.A.act a)
      (fun _ => act0 a) (act0 a) hT (fun _ => TendsS.const _) i
    have R := TendsS.comp1 (φ := fun _ => Y.B.A.act a) (b := fun n => Y.B.A.act (M n * ε ^ V.l ^ n))
      (fun n => act0 _) hφ0 (fun _ => TendsS.const _) hT i
    have eq : (fun n => comp1 (Y.B.A.act (M n * ε ^ V.l ^ n)) (Y.B.A.act a) i) =
        fun n => comp1 (Y.B.A.act a) (Y.B.A.act (M n * ε ^ V.l ^ n)) i := funext fun n => by
      rw [← Y.B.A.mul_act, ← Y.B.A.mul_act, mul_comm]
    rw [eq] at L
    exact L.unique R
  · obtain ⟨E, -, -, -, hET⟩ := StartSelf.lim_endo Y p.em p.em_int p.hd p.em_conj ε hε hεx (fun _ => 1)
      (fun N a => by rw [sub_self, map_zero]; exact VF.Ge.zero _)
    have hElim : ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
        V.Ge N (MvPowerSeries.coeff μ (E i) - MvPowerSeries.coeff μ (Y.B.A.act (ε ^ V.l ^ n) i)) := by
      intro N i μ
      obtain ⟨n0, h⟩ := hET i μ N
      exact ⟨n0, fun n hn => by simpa only [one_mul] using h n hn⟩
    have hEspan := hLie C V O dd Y d I0 p ε hε hε1 hεx E hElim
    have hEφ : comp1 E φ = φ := by
      funext i
      have L := TendsS.comp1 (φ := fun n => Y.B.A.act (1 * ε ^ V.l ^ n)) (b := fun n => Y.B.A.act (M n * ε ^ V.l ^ n))
        (fun n => act0 _) hφ0 hET hT i
      have hdiv : ∀ n, ((V.l : O) ^ (n + 1)) ∣ (1 * ε ^ V.l ^ n) * (M n * ε ^ V.l ^ n) - M n * ε ^ V.l ^ n := by
        intro n
        have e1 : (1 * ε ^ V.l ^ n) * (M n * ε ^ V.l ^ n) - M n * ε ^ V.l ^ n =
            M n * (ε ^ V.l ^ n * ε ^ V.l ^ n - ε ^ V.l ^ n) := by ring
        rw [e1]
        exact dvd_mul_of_dvd_right (sq_cong hε n) _
      have R := tendsS_of_small RowTiePLSmall.lSmall_holds Y
        (x := fun n => (1 * ε ^ V.l ^ n) * (M n * ε ^ V.l ^ n)) (x' := fun n => M n * ε ^ V.l ^ n) hdiv hT i
      have eq : (fun n => comp1 (Y.B.A.act (1 * ε ^ V.l ^ n)) (Y.B.A.act (M n * ε ^ V.l ^ n)) i) =
          fun n => Y.B.A.act ((1 * ε ^ V.l ^ n) * (M n * ε ^ V.l ^ n)) i := funext fun n => by
        rw [Y.B.A.mul_act (1 * ε ^ V.l ^ n) (M n * ε ^ V.l ^ n)]
      rw [eq] at L
      exact L.unique R
    intro v
    obtain ⟨b, hb⟩ := hEspan (linAct φ v)
    exact ⟨b, by rw [← hb, ← VP.linAct_comp1 E φ hφ0, hEφ]⟩

theorem one_entry [NeZero d] (hLie : ProjLieSelfSt) (Y : FBChart C V O dd) {I0 : Type} [Fintype I0] (p : SelfData Y d I0)
    (M : ℕ → O) (t : ZMod d → C) (hMt : ∀ (N : ℕ) a, V.Ge ((N + 1 : ℕ) : ℝ) (t a - p.em a (M N))) :
    ∃ γ γ' : Pt C 1 dd, IsEndo Y γ ∧ IsEndo Y γ' ∧
      (∀ a, comp1 γ (Y.B.A.act a) = comp1 (Y.B.A.act a) γ) ∧
      (∀ a, comp1 γ' (Y.B.A.act a) = comp1 (Y.B.A.act a) γ') ∧
      (∀ c, linAct γ (p.e c) = t (p.ty0 c) • p.e c) ∧
      (∀ c, linAct γ' (p.e c) = t (p.ty0 c + p.hd) • p.e c) ∧
      (∀ v : Fin dd → C, ∃ b : I0 → C, linAct γ v = ∑ c, b c • p.e c) ∧
      (∀ v : Fin dd → C, ∃ b : I0 → C, linAct γ' v = ∑ c, b c • p.e c) ∧
      IntS V (FB.expS C (ev (n := 2) ![comp1 γ (pt C dd 0), pt C dd 1] Y.h -
        ev (n := 2) ![pt C dd 0, comp1 γ' (pt C dd 1)] Y.h)) := by
  obtain ⟨ε, hε, hε1, hεx⟩ := p.em_unr
  have hM : ∀ (N : ℕ) a, V.Ge ((N + 1 : ℕ) : ℝ) (p.em a (M (N + 1) - M N)) := by
    intro N a
    have e2 : p.em a (M (N + 1) - M N) = (t a - p.em a (M N)) - (t a - p.em a (M (N + 1))) := by
      rw [map_sub]; ring
    rw [e2]
    exact (hMt N a).sub ((hMt (N + 1) a).mono (by push_cast; linarith))
  have ht : ∀ a, Tends V (fun n => p.em a (M n)) (t a) := fun a =>
    tends_of_nat fun N => ⟨N, fun n hn => (hMt n a).mono (by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      push_cast; linarith)⟩
  have hεs := star_rel hε
  have hεs1 : ∀ a, V.MM (p.em a (star ε) - 1) := fun a => by rw [p.em_conj]; exact hε1 _
  have hεsx : ∀ x : O, (∀ a, V.MM (p.em a x)) → ∃ y, star ε * x = (V.l : O) * y := by
    intro x hx
    obtain ⟨y, hy⟩ := hεx (star x) fun a => by rw [p.em_conj]; exact hx (a + p.hd)
    refine ⟨star y, ?_⟩
    have h := congrArg star hy
    simp only [star_mul, star_star, star_natCast] at h
    rw [mul_comm, h, mul_comm]
  have hMs : ∀ (N : ℕ) a, V.Ge ((N + 1 : ℕ) : ℝ) (p.em a (star (M (N + 1)) - star (M N))) := fun N a => by
    rw [← star_sub, p.em_conj]; exact hM N (a + p.hd)
  have cvA := StartSelf.actCv_of Y p.em ε hε (fun a => p.em_int a ε) hεx M hM
  have cvB := StartSelf.actCv_of Y p.em (star ε) hεs (fun a => p.em_int a _) hεsx (fun N => star (M N)) hMs
  have sA : (fun n => star (M n * ε ^ V.l ^ n)) = fun n => star (M n) * star ε ^ V.l ^ n :=
    funext fun n => by rw [star_mul', star_pow]
  have sB : (fun n => star (star (M n) * star ε ^ V.l ^ n)) = fun n => M n * ε ^ V.l ^ n :=
    funext fun n => by rw [star_mul', star_pow, star_star, star_star]
  obtain ⟨γ, γb, hγI, -, hγl, hγbl, hhom, hexp⟩ := endomorphism_limit_integral Y (fun n => M n * ε ^ V.l ^ n) cvA (by rw [sA]; exact cvB)
  obtain ⟨γ2, -, hγ2I, -, hγ2l, -, hhom2, -⟩ := endomorphism_limit_integral Y (fun n => star (M n) * star ε ^ V.l ^ n) cvB
    (by rw [sB]; exact cvA)
  have hT : ∀ i, TendsS V (fun n => Y.B.A.act (M n * ε ^ V.l ^ n) i) (γ i) := tends_of_endomorphism_limit Y hγl
  have hTb : ∀ i, TendsS V (fun n => Y.B.A.act (star (M n) * star ε ^ V.l ^ n) i) (γb i) := by
    have h := tends_of_endomorphism_limit Y hγbl
    simpa only [star_mul', star_pow] using h
  have hT2 : ∀ i, TendsS V (fun n => Y.B.A.act (star (M n) * star ε ^ V.l ^ n) i) (γ2 i) := tends_of_endomorphism_limit Y hγ2l
  have heq : γ2 = γb := funext fun i => (hT2 i).unique (hTb i)
  subst heq
  obtain ⟨hc, hi⟩ := half hLie Y p ε hε hε1 hεx M γ hT
  obtain ⟨hc', hi'⟩ := half hLie Y p (star ε) hεs hεs1 hεsx (fun N => star (M N)) γ2 hT2
  refine ⟨γ, γ2, ⟨hγI, const_of_lim Y hT, hhom⟩, ⟨hγ2I, const_of_lim Y hT2, hhom2⟩, hc, hc', ?_, ?_, hi, hi', hexp⟩
  · exact fun c => StartSelf.lin_of_lim Y p M ε hε1 t ht γ hT c
  · exact fun c => StartSelf.lin_of_lim Y p (fun N => star (M N)) (star ε) hεs1 (fun a => t (a + p.hd))
      (fun a => by simp only [p.em_conj]; exact ht (a + p.hd)) γ2 hT2 c

end GmPackP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd d : ℕ}

theorem gmPack_of_lie [NeZero d] (hLie : ProjLieSelfSt) (Y : FBChart C V O dd) {I0 : Type} [Fintype I0]
    (p : SelfData Y d I0) : GmPackSt Y p := by
  choose Mm hMm using fun N : ℕ => p.gm_lim (N + 1)
  have h := fun r s : Fin 2 => GmPackP.one_entry hLie Y p (fun N => Mm N r s) (fun a => p.gm a r s)
    (fun N a => hMm N a r s)
  choose γ γ' h1 h2 h3 h4 h5 h6 h7 h8 h9 using h
  exact ⟨γ, γ', ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩⟩

theorem gmPack_of [NeZero d] (hE : RowTiePKey.KeyEigSt) (Y : FBChart C V O dd) {I0 : Type} [Fintype I0]
    (p : SelfData Y d I0) : GmPackSt Y p := gmPack_of_lie (projLieSelf_of hE) Y p

theorem gmPack_holds [NeZero d] (Y : FBChart C V O dd) {I0 : Type} [Fintype I0] (p : SelfData Y d I0) :
    GmPackSt Y p := gmPack_of RowTiePKey.keyEig_holds Y p

end Formalism.L2.FormalSeriesBounds
end
end

section
namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

theorem unitSelf_holds (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) : UnitSelfSt Y p :=
  unitSelf_of Y p fun o => gmPack_holds Y (p o)

theorem projSelf_holds (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) : ProjSelfSt Y p :=
  projSelf_of Y p fun o => gmPack_holds Y (p o)

theorem germLiftSelf_holds (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o))
    (H : ∀ o, (Y.rawSelf (p o)).Hyps V) : GermLiftSelfSt Y p H :=
  germLiftSelf_of Y p H (projSelf_holds Y p) fun o => tcoordSelf_holds C V O dd Y d (I0 o) (p o) (H o).cartH

end Formalism.L2.FormalSeriesBounds
end
