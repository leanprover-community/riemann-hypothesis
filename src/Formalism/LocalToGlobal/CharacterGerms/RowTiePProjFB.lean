import Formalism.LocalToGlobal.CharacterGerms.CoeffSubstEqSum
import Formalism.LocalToGlobal.CharacterGerms.RowTieProj

section
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePE0

open PartialDerivEval

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem actK_self (B : FB C dd O) (a : O) : B.actK C a = B.A.act a := by
  funext i; unfold FB.actK; rw [show algebraMap C C = RingHom.id C from rfl, map_id]; rfl

theorem TendsS.ev {m n : ℕ} {a : ℕ → Fin m → Pt C n dd} {A : Fin m → Pt C n dd} {f : ℕ → PS C m dd}
    {F : PS C m dd} (ha0 : ∀ k, Z0 (a k)) (hA0 : Z0 A) (ha : ∀ j i, TendsS V (fun k => a k j i) (A j i))
    (hf : TendsS V f F) : TendsS V (fun k => ev (a k) (f k)) (ev A F) := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev
  exact TendsS.subst (fun k p => ha0 k p.1 p.2) (fun p => hA0 p.1 p.2) (fun p => ha p.1 p.2) hf

theorem constant_zero_two_points {n : ℕ} (P Q : Pt C n dd) (hP : ∀ i, constantCoeff (P i) = 0) (hQ : ∀ i, constantCoeff (Q i) = 0) :
    Z0 (![P, Q] : Fin 2 → Pt C n dd) := by
  intro j i; fin_cases j
  · exact hP i
  · exact hQ i

theorem tends_two {n : ℕ} {P Q : ℕ → Pt C n dd} {P' Q' : Pt C n dd} (hP : ∀ i, TendsS V (fun k => P k i) (P' i))
    (hQ : ∀ i, TendsS V (fun k => Q k i) (Q' i)) :
    ∀ j i, TendsS V (fun k => (![P k, Q k] : Fin 2 → Pt C n dd) j i) ((![P', Q'] : Fin 2 → Pt C n dd) j i) := by
  intro j i; fin_cases j
  · exact hP i
  · exact hQ i

theorem const_comp1 {n : ℕ} {φ : Pt C 1 dd} (hφ : ∀ i, constantCoeff (φ i) = 0) {b : Pt C n dd}
    (hb : ∀ i, constantCoeff (b i) = 0) (i : Fin dd) : constantCoeff (comp1 φ b i) = 0 :=
  const_ev (z0_1 b hb) (hφ i)

theorem TendsS.comp1 {n : ℕ} {φ : ℕ → Pt C 1 dd} {Φ : Pt C 1 dd} {b : ℕ → Pt C n dd} {B : Pt C n dd}
    (hb0 : ∀ k i, constantCoeff (b k i) = 0) (hB0 : ∀ i, constantCoeff (B i) = 0)
    (hφ : ∀ i, TendsS V (fun k => φ k i) (Φ i)) (hb : ∀ i, TendsS V (fun k => b k i) (B i)) (i : Fin dd) :
    TendsS V (fun k => comp1 (φ k) (b k) i) (comp1 Φ B i) :=
  TendsS.ev (fun k => z0_1 _ (hb0 k)) (z0_1 _ hB0)
    (fun j i' => by rw [Fin.fin_one_eq_zero j]; exact hb i') (hφ i)

theorem TendsS.expS {n : ℕ} {g : ℕ → PS C n dd} {G : PS C n dd} (hg0 : ∀ k, constantCoeff (g k) = 0)
    (hG0 : constantCoeff G = 0) (hg : TendsS V g G) : TendsS V (fun k => FB.expS C (g k)) (FB.expS C G) := by
  unfold FB.expS PowerSeries.subst
  exact TendsS.subst (fun k _ => hg0 k) (fun _ => hG0) (fun _ => hg) (TendsS.const _)

theorem exists_lim (Y : FBChart C V O dd) {φ : ℕ → Pt C 1 dd}
    (hφ : ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (coeff μ (φ (n + 1) i) - coeff μ (φ n i))) :
    ∃ e : Pt C 1 dd, ∀ i, TendsS V (fun n => φ n i) (e i) := by
  have h : ∀ i μ, ∃ x, Tends V (fun n => coeff μ (φ n i)) x := fun i μ => exists_tends Y.cpl fun N => hφ N i μ
  choose L hL using h
  exact ⟨fun i => (fun μ => L i μ : MvPowerSeries (Fin 1 × Fin dd) C), fun i μ => hL i μ⟩

theorem const_of_lim (Y : FBChart C V O dd) {a : ℕ → O} {e : Pt C 1 dd}
    (he : ∀ i, TendsS V (fun n => Y.B.A.act (a n) i) (e i)) (i : Fin dd) : constantCoeff (e i) = 0 := by
  have h := he i 0
  simp only [coeff_zero_eq_constantCoeff_apply, Y.B.A.const] at h
  exact h.unique (tends_const 0)

theorem endomorphism_limit_integral (Y : FBChart C V O dd) : EndomorphismLimitIntegral Y := by
  intro a ha hb
  obtain ⟨e, he⟩ := exists_lim Y (φ := fun n => Y.B.A.act (a n)) ha
  obtain ⟨eb, heb⟩ := exists_lim Y (φ := fun n => Y.B.A.act (star (a n))) hb
  have e0 := const_of_lim Y he
  have eb0 := const_of_lim Y (a := fun n => star (a n)) heb
  have act0 : ∀ x i, constantCoeff (Y.B.A.act x i) = 0 := Y.B.A.const
  refine ⟨e, eb, fun i => (he i).intS fun n => Y.intAct _ i, fun i => (heb i).intS fun n => Y.intAct _ i,
    fun N i μ => he i μ N, fun N i μ => heb i μ N, ?_, ?_⟩
  ·
    funext i
    have hP : ∀ i, constantCoeff (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) i) = 0 :=
      fun j => const_addOf Y 0 1 j
    have L := TendsS.comp1 (φ := fun k => Y.B.A.act (a k)) (b := fun _ => addOf Y.B.G.F (pt C (n := 2) dd 0)
      (pt C (n := 2) dd 1)) (fun _ => hP) hP he (fun j => TendsS.const _) i
    have hc : ∀ (j : Fin 2) k i', constantCoeff (comp1 (Y.B.A.act (a k)) (pt C (n := 2) dd j) i') = 0 :=
      fun j k i' => const_comp1 (act0 _) (fun _ => z0_pt j _) i'
    have hcl : ∀ (j : Fin 2) i', constantCoeff (comp1 e (pt C (n := 2) dd j) i') = 0 :=
      fun j i' => const_comp1 e0 (fun _ => z0_pt j _) i'
    have R := TendsS.ev (V := V) (f := fun _ => Y.B.G.F i) (F := Y.B.G.F i)
      (a := fun k => ![comp1 (Y.B.A.act (a k)) (pt C (n := 2) dd 0), comp1 (Y.B.A.act (a k)) (pt C (n := 2) dd 1)])
      (A := ![comp1 e (pt C (n := 2) dd 0), comp1 e (pt C (n := 2) dd 1)])
      (fun k => constant_zero_two_points _ _ (hc 0 k) (hc 1 k)) (constant_zero_two_points _ _ (hcl 0) (hcl 1))
      (tends_two (TendsS.comp1 (fun _ => z0_pt 0) (z0_pt 0) he (fun _ => TendsS.const _))
        (TendsS.comp1 (fun _ => z0_pt 1) (z0_pt 1) he (fun _ => TendsS.const _))) (TendsS.const _)
    have eq : (fun k => comp1 (Y.B.A.act (a k)) (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) i) =
        fun k => ev ![comp1 (Y.B.A.act (a k)) (pt C (n := 2) dd 0), comp1 (Y.B.A.act (a k)) (pt C (n := 2) dd 1)]
          (Y.B.G.F i) := funext fun k => by rw [Y.B.A.hom (a k)]; rfl
    rw [eq] at L
    exact L.unique R
  ·
    let g : ℕ → PS C 2 dd := fun k => ev (n := 2) ![comp1 (Y.B.A.act (a k)) (pt C dd 0), pt C dd 1] Y.h -
      ev (n := 2) ![pt C dd 0, comp1 (Y.B.A.act (star (a k))) (pt C dd 1)] Y.h
    have hc0 : ∀ k, Z0 (![comp1 (Y.B.A.act (a k)) (pt C dd 0), pt C dd 1] : Fin 2 → Pt C 2 dd) :=
      fun k => constant_zero_two_points _ _ (const_comp1 (act0 _) (fun _ => z0_pt 0 _)) (fun _ => z0_pt 1 _)
    have hc1 : ∀ k, Z0 (![pt C dd 0, comp1 (Y.B.A.act (star (a k))) (pt C dd 1)] : Fin 2 → Pt C 2 dd) :=
      fun k => constant_zero_two_points _ _ (fun _ => z0_pt 0 _) (const_comp1 (act0 _) (fun _ => z0_pt 1 _))
    have hC0 : Z0 (![comp1 e (pt C dd 0), pt C dd 1] : Fin 2 → Pt C 2 dd) :=
      constant_zero_two_points _ _ (const_comp1 e0 (fun _ => z0_pt 0 _)) (fun _ => z0_pt 1 _)
    have hC1 : Z0 (![pt C dd 0, comp1 eb (pt C dd 1)] : Fin 2 → Pt C 2 dd) :=
      constant_zero_two_points _ _ (fun _ => z0_pt 0 _) (const_comp1 eb0 (fun _ => z0_pt 1 _))
    have hg : TendsS V g (ev (n := 2) ![comp1 e (pt C dd 0), pt C dd 1] Y.h -
        ev (n := 2) ![pt C dd 0, comp1 eb (pt C dd 1)] Y.h) :=
      (TendsS.ev hc0 hC0 (tends_two (TendsS.comp1 (fun _ => z0_pt 0) (z0_pt 0) he (fun _ => TendsS.const _))
        (fun _ => TendsS.const _)) (TendsS.const _)).sub
      (TendsS.ev hc1 hC1 (tends_two (fun _ => TendsS.const _)
        (TendsS.comp1 (fun _ => z0_pt 1) (z0_pt 1) heb (fun _ => TendsS.const _))) (TendsS.const _))
    have hh := h_const Y
    have hg0 : ∀ k, constantCoeff (g k) = 0 := fun k => by
      simp only [g, map_sub, constantCoeff_ev (hc0 k), constantCoeff_ev (hc1 k), hh, sub_zero]
    have hG0 : constantCoeff (ev (n := 2) ![comp1 e (pt C dd 0), pt C dd 1] Y.h -
        ev (n := 2) ![pt C dd 0, comp1 eb (pt C dd 1)] Y.h) = 0 := by
      simp only [map_sub, constantCoeff_ev hC0, constantCoeff_ev hC1, hh, sub_zero]
    have hE := TendsS.expS hg0 hG0 hg
    have hadk : ∀ k, FB.expS C (g k) = Y.B.ad (a k) := fun k => by
      have h1 := Y.gauge.ad (a k)
      rw [toK_self, actK_self, actK_self] at h1
      exact h1.symm
    simp only [hadk] at hE
    exact hE.intS fun k => Y.intAd _


end RowTiePE0

end Formalism.L2.FormalSeriesBounds
end
end

section
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePProj

open PartialDerivEval RowTiePE0

def LSmallSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (x x' : ℕ → O), (∀ n, ((V.l : O) ^ (n + 1)) ∣ x n - x' n) →
    ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
      V.Ge N (MvPowerSeries.coeff μ (Y.B.A.act (x n) i) - MvPowerSeries.coeff μ (Y.B.A.act (x' n) i))

def ProjLieSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I)
    (g : Fin 2) (ε : O), (∃ y, ε * ε - ε = (V.l : O) * y) → (∀ a, V.MM (p.em g a ε - 1)) →
    (∀ x : O, (∀ a, V.MM (p.em g a x)) → ∃ y, ε * x = (V.l : O) * y) →
    ∀ e : Pt C 1 dd, (∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
      V.Ge N (MvPowerSeries.coeff μ (e i) - MvPowerSeries.coeff μ (Y.B.A.act (ε ^ V.l ^ n) i))) →
    ∀ v : Fin dd → C, ∃ b : I g → C, linAct e v = ∑ c, b c • p.u g c

section Alg

variable {O : Type} [CommRing O]

theorem pow_cong {l : ℕ} (hl : 2 ≤ l) {ε : O} (hε : ∃ y, ε * ε - ε = (l : O) * y) (n : ℕ) :
    ((l : O) ^ (n + 1)) ∣ ε ^ l ^ (n + 1) - ε ^ l ^ n := by
  have h1 : ∀ k : ℕ, (l : O) ∣ ε ^ (k + 1) - ε := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨y, hy⟩ := hε
      obtain ⟨z, hz⟩ := ih
      refine ⟨ε * z + y, ?_⟩
      have e : ε ^ (k + 1 + 1) - ε = ε * (ε ^ (k + 1) - ε) + (ε * ε - ε) := by ring
      rw [e, hz, hy]
      ring
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  have h2 := dvd_sub_pow_of_dvd_sub (h1 m) n
  rw [show (m + 1) ^ (n + 1) = (m + 1) * (m + 1) ^ n from pow_succ' _ _, pow_mul]
  exact h2

theorem sq_cong {l : ℕ} {ε : O} (hε : ∃ y, ε * ε - ε = (l : O) * y) (n : ℕ) :
    ((l : O) ^ (n + 1)) ∣ ε ^ l ^ n * ε ^ l ^ n - ε ^ l ^ n := by
  obtain ⟨y, hy⟩ := hε
  have h2 := dvd_sub_pow_of_dvd_sub (⟨y, hy⟩ : (l : O) ∣ ε * ε - ε) n
  rwa [mul_pow] at h2

variable [StarRing O]

theorem star_rel {l : ℕ} {ε : O} (hε : ∃ y, ε * ε - ε = (l : O) * y) : ∃ y, star ε * star ε - star ε = (l : O) * y := by
  obtain ⟨y, hy⟩ := hε
  refine ⟨star y, ?_⟩
  have h := congrArg star hy
  simp only [star_sub, star_mul, star_natCast] at h
  rw [h, mul_comm]

end Alg

section Val

variable {C : Type} [Field C] {V : VF C}

theorem tends_of_nat {s : ℕ → C} {x : C} (h : ∀ N : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (x - s n)) : Tends V s x := by
  intro w
  obtain ⟨n0, hn⟩ := h ⌈w⌉₊
  refine ⟨n0, fun n hn' => ?_⟩
  have h1 := hn n hn'
  unfold VF.Ge at h1 ⊢
  exact le_trans (WithTop.coe_le_coe.mpr (Nat.le_ceil w)) h1

private theorem v_nonneg_of_v_sub_one_pos {z : C} (hz : 0 < V.v (z - 1)) : 0 ≤ V.v z := by
  have h := V.v.map_add (z - 1) 1
  rw [sub_add_cancel, V.v.map_one] at h
  exact le_trans (le_min hz.le le_rfl) h

private theorem v_sub_one_add_le_v_pow_l_sub_one {z : C} {δ : ℝ} (hδ1 : δ ≤ 1) (hδ0 : 0 < δ)
    (hz : ((δ : ℝ) : WithTop ℝ) ≤ V.v (z - 1)) :
    V.v (z - 1) + ((δ : ℝ) : WithTop ℝ) ≤ V.v (z ^ V.l - 1) := by
  have hz0 : 0 < V.v (z - 1) := lt_of_lt_of_le (by exact_mod_cast hδ0) hz
  have hzv : 0 ≤ V.v z := v_nonneg_of_v_sub_one_pos hz0
  have hg : z ^ V.l - 1 = (∑ i ∈ Finset.range V.l, z ^ i) * (z - 1) := (geom_sum_mul z V.l).symm
  have hs : ∑ i ∈ Finset.range V.l, z ^ i = ∑ i ∈ Finset.range V.l, (z ^ i - 1) + (V.l : C) := by
    rw [Finset.sum_sub_distrib]
    simp
  have hterm : ∀ i ∈ Finset.range V.l, ((δ : ℝ) : WithTop ℝ) ≤ V.v (z ^ i - 1) := by
    intro i _
    rw [← geom_sum_mul, V.v.map_mul]
    calc ((δ : ℝ) : WithTop ℝ) = 0 + ((δ : ℝ) : WithTop ℝ) := (zero_add _).symm
      _ ≤ V.v (∑ j ∈ Finset.range i, z ^ j) + V.v (z - 1) :=
        add_le_add (V.v.map_le_sum fun j _ => by rw [V.v.map_pow]; exact nsmul_nonneg hzv j) hz
  have hsum : ((δ : ℝ) : WithTop ℝ) ≤ V.v (∑ i ∈ Finset.range V.l, z ^ i) := by
    rw [hs]
    refine le_trans (le_min (V.v.map_le_sum hterm) ?_) (V.v.map_add _ _)
    rw [V.v_l]
    exact_mod_cast hδ1
  rw [hg, V.v.map_mul]
  calc V.v (z - 1) + ((δ : ℝ) : WithTop ℝ) = ((δ : ℝ) : WithTop ℝ) + V.v (z - 1) := add_comm _ _
    _ ≤ _ := add_le_add hsum le_rfl

theorem tends_pow_one {x : C} (hx : V.MM (x - 1)) : Tends V (fun n => x ^ V.l ^ n) 1 := by
  obtain ⟨δ, hδ0, hδ1, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ((δ : ℝ) : WithTop ℝ) ≤ V.v (x - 1) := by
    unfold VF.MM at hx
    by_cases htop : V.v (x - 1) = ⊤
    · exact ⟨1, one_pos, le_rfl, by rw [htop]; exact le_top⟩
    · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp htop
      rw [← hr] at hx
      have hr0 : 0 < r := by exact_mod_cast hx
      refine ⟨min r 1, lt_min hr0 one_pos, min_le_right _ _, ?_⟩
      rw [← hr]
      exact_mod_cast min_le_left r 1
  have key : ∀ n : ℕ, ((((n : ℝ) + 1) * δ : ℝ) : WithTop ℝ) ≤ V.v (x ^ V.l ^ n - 1) := by
    intro n
    induction n with
    | zero => simpa using hδ
    | succ n ih =>
      have e : x ^ V.l ^ (n + 1) = (x ^ V.l ^ n) ^ V.l := by rw [pow_succ, pow_mul]
      rw [e]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h1 : ((δ : ℝ) : WithTop ℝ) ≤ V.v (x ^ V.l ^ n - 1) :=
        le_trans (by exact_mod_cast (show δ ≤ ((n : ℝ) + 1) * δ by nlinarith)) ih
      have h2 : ((((n + 1 : ℕ) : ℝ) + 1) * δ : ℝ) = ((n : ℝ) + 1) * δ + δ := by push_cast; ring
      rw [h2, WithTop.coe_add]
      exact le_trans (add_le_add ih le_rfl) (v_sub_one_add_le_v_pow_l_sub_one hδ1 hδ0 h1)
  intro w
  obtain ⟨N, hN⟩ := exists_nat_gt (w / δ)
  refine ⟨N, fun n hn => ?_⟩
  unfold VF.Ge
  show ((w : ℝ) : WithTop ℝ) ≤ V.v (1 - x ^ V.l ^ n)
  rw [← neg_sub, V.v.map_neg]
  refine le_trans ?_ (key n)
  have h2 : (N : ℝ) ≤ n := by exact_mod_cast hn
  have h3 : w = (w / δ) * δ := by field_simp
  have : w ≤ ((n : ℝ) + 1) * δ := by
    nlinarith [mul_lt_mul_of_pos_right hN hδ0, mul_le_mul_of_nonneg_right h2 hδ0.le]
  exact_mod_cast this

end Val

section Main

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem tends_of_endomorphism_limit (Y : FBChart C V O dd) {a : ℕ → O} {e : Pt C 1 dd}
    (h : ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
      V.Ge N (MvPowerSeries.coeff μ (e i) - MvPowerSeries.coeff μ (Y.B.A.act (a n) i))) (i : Fin dd) :
    TendsS V (fun n => Y.B.A.act (a n) i) (e i) := by
  intro μ
  exact tends_of_nat fun N => h N i μ

private theorem ge_sub {w : ℝ} {a b : C} (ha : V.Ge w a) (hb : V.Ge w b) : V.Ge w (a - b) := by
  unfold VF.Ge at *
  exact le_trans (le_min ha hb) (V.v.map_sub a b)

private theorem ge_of_ge_natCeil {w : ℝ} {a : C} (ha : V.Ge (⌈w⌉₊ : ℕ) a) : V.Ge w a := by
  unfold VF.Ge at *
  exact le_trans (WithTop.coe_le_coe.mpr (Nat.le_ceil w)) ha

theorem tendsS_of_small (hL : LSmallSt) (Y : FBChart C V O dd) {x x' : ℕ → O}
    (hx : ∀ n, ((V.l : O) ^ (n + 1)) ∣ x n - x' n) {e : Pt C 1 dd}
    (he : ∀ i, TendsS V (fun n => Y.B.A.act (x' n) i) (e i)) (i : Fin dd) :
    TendsS V (fun n => Y.B.A.act (x n) i) (e i) := by
  intro μ w
  obtain ⟨n1, h1⟩ := he i μ w
  obtain ⟨n2, h2⟩ := hL C V O dd Y x x' hx ⌈w⌉₊ i μ
  refine ⟨max n1 n2, fun n hn => ?_⟩
  have a1 := h1 n (le_of_max_le_left hn)
  have a2 := ge_of_ge_natCeil (h2 n (le_of_max_le_right hn))
  have a3 := ge_sub a1 a2
  have heq : MvPowerSeries.coeff μ (e i) - MvPowerSeries.coeff μ (Y.B.A.act (x n) i) =
      (MvPowerSeries.coeff μ (e i) - MvPowerSeries.coeff μ (Y.B.A.act (x' n) i)) -
        (MvPowerSeries.coeff μ (Y.B.A.act (x n) i) - MvPowerSeries.coeff μ (Y.B.A.act (x' n) i)) := by ring
  show V.Ge w (MvPowerSeries.coeff μ (e i) - MvPowerSeries.coeff μ (Y.B.A.act (x n) i))
  rw [heq]
  exact a3

private theorem tends_mul_const {s : ℕ → C} {x : C} (hs : Tends V s x) (c : C) :
    Tends V (fun n => s n * c) (x * c) := by
  by_cases hc : c = 0
  · subst hc
    intro w
    refine ⟨0, fun n _ => ?_⟩
    unfold VF.Ge
    simp
  · have hct : V.v c ≠ ⊤ := fun h => hc ((V.v.top_iff).mp h)
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hct
    intro w
    obtain ⟨n0, h0⟩ := hs (w - r)
    refine ⟨n0, fun n hn => ?_⟩
    have h1 := h0 n hn
    unfold VF.Ge at h1 ⊢
    show ((w : ℝ) : WithTop ℝ) ≤ V.v (x * c - s n * c)
    rw [← sub_mul, V.v.map_mul, ← hr]
    calc ((w : ℝ) : WithTop ℝ) = ((w - r : ℝ) : WithTop ℝ) + ((r : ℝ) : WithTop ℝ) := by
          rw [← WithTop.coe_add, sub_add_cancel]
      _ ≤ _ := add_le_add h1 le_rfl

private theorem tends_fintype_sum {ι : Type} [Fintype ι] {s : ι → ℕ → C} {x : ι → C}
    (h : ∀ j, Tends V (s j) (x j)) : Tends V (fun n => ∑ j, s j n) (∑ j, x j) := by
  intro w
  choose n0 hn0 using fun j => h j w
  refine ⟨Finset.univ.sup n0, fun n hn => ?_⟩
  unfold VF.Ge
  show ((w : ℝ) : WithTop ℝ) ≤ V.v (∑ j, x j - ∑ j, s j n)
  rw [← Finset.sum_sub_distrib]
  exact V.v.map_le_sum fun j _ => hn0 j n (le_trans (Finset.le_sup (Finset.mem_univ j)) hn)

theorem linAct_tends {φ : ℕ → Pt C 1 dd} {Φ : Pt C 1 dd} (hφ : ∀ i, TendsS V (fun n => φ n i) (Φ i))
    (v : Fin dd → C) (i : Fin dd) : Tends V (fun n => linAct (φ n) v i) (linAct Φ v i) := by
  show Tends V (fun n => ∑ j, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (φ n i) * v j)
    (∑ j, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (Φ i) * v j)
  exact tends_fintype_sum fun j => tends_mul_const (hφ i _) (v j)



end Main

end RowTiePProj

end Formalism.L2.FormalSeriesBounds
end
end
