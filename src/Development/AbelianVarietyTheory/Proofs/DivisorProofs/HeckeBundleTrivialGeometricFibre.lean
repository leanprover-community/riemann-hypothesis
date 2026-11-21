import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearIsIsoOfIsProperOfFinitePresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TlLevSurjKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMumfordClassEqZeroAmpleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivisibleBaseChangeIsoSemiabelian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelOfCubWeilOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

set_option autoImplicit false
noncomputable section
open GlobalTheory.CechPic GlobalTheory.AbDual

namespace GlobalTheory.PicBilin

variable {S : Scheme.{0}}

theorem evc_pow_left {A B Y : Over S} [GrpObj A] {P : LB (A ⊗ B).left} (hP : P.IsLB)
    (hadd : ∀ (a a' : Y ⟶ A) (t : Y ⟶ B), evc hP (a * a') t = evc hP a t + evc hP a' t)
    (a : Y ⟶ A) (t : Y ⟶ B) (n : ℕ) : evc hP (a ^ n) t = n • evc hP a t := by
  induction n with
  | zero =>
    have e := hadd 1 1 t
    rw [_root_.mul_one] at e
    rw [pow_zero, zero_smul]
    exact left_eq_add.1 e
  | succ n ih => rw [pow_succ, hadd, ih, succ_nsmul]

theorem comp_pow_pt {A T Y : Over S} [GrpObj A] (f : Y ⟶ T) (g : T ⟶ A) (n : ℕ) :
    f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem cls_heckePow {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (m : ℕ)
    (h : (GlobalTheory.UPel.HT.Hecke.lbPow L m).IsLB) : cls _ h = m • cls L hL := by
  refine (cls_linComb hL (K := Fin m) (fun _ => 𝟙 X) (fun _ => 1) h).trans ?_
  simp [pull_id]

end GlobalTheory.PicBilin

namespace GlobalTheory.PicBilin

theorem triv_pow_of_translDiff : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (P : LB (A ⊗ A).left), P.IsLB →
    (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    LBIso P (P.pull (lift (snd A A) (fst A A)).left) →
    ∀ (T : Over S), (∀ c : GlobalTheory.CechPic.Pic T.left, c = 0) →
    ∀ (h₀ : 𝟙_ (Over S) ⟶ A) (h' : T ⟶ A) (m : ℕ), h' ^ 2 = toUnit T ≫ h₀ →
    (∃ t : (Out.translDiff A (P.pull (lift (𝟙 A) (𝟙 A)).left) (h' ^ m)).Gen, t.IsGen) →
    ∃ t : (((GlobalTheory.UPel.HT.Hecke.lbPow P m).pull (lift (toUnit A ≫ h₀) (𝟙 A)).left).pull (fst A T).left).Gen, t.IsGen := by
  intro S A _ _ hA P hP rig₁ rig₂ hsym T hT h₀ h' m hsq htd
  have hs : (swap P).IsLB := pull_isLB hP _
  obtain ⟨hadd₁, hadd₂⟩ := additive_of_cube GlobalTheory.CubeTop.cubeTheorem hA hA hP rig₁ rig₂
  have eL : ∀ {Y : Over S} (a a' t : Y ⟶ A), evc hP (a * a') t = evc hP a t + evc hP a' t :=
    fun a a' t => (isAdditive_iff hP).1 hadd₁ _ a a' t
  have eR : ∀ {Y : Over S} (a t t' : Y ⟶ A), evc hP a (t * t') = evc hP a t + evc hP a t' := by
    intro Y a t t'
    have e := (isAdditive_iff hs).1 hadd₂ _ t t' a
    rwa [evc_swap hP hs, evc_swap hP hs, evc_swap hP hs] at e
  have hsymc : cls P hP = cls _ hs := (cls_eq_iff hP hs).2 hsym
  have eS : ∀ {Y : Over S} (a b : Y ⟶ A), evc hP a b = evc hP b a := by
    intro Y a b
    rw [← evc_swap hP hs a b]
    simp only [evc, hsymc]
  have hL₁ : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hD : (Out.translDiff A (P.pull (lift (𝟙 A) (𝟙 A)).left) (h' ^ m)).IsLB := LB.isLB_linComb hL₁ _ _
  have e0 := pull_translDiff hL₁ (h' ^ m) hD (snd A T) (fst A T)
  rw [(cls_eq_zero_iff hD).2 htd, map_zero] at e0
  have hu : ∀ u : A ⊗ T ⟶ A, CechPic.pull u.left (cls _ hL₁) = evc hP u u := fun u => by
    rw [cls_ev hP, pull_evc, Category.comp_id]
  rw [hu, hu] at e0
  have hXX : evc hP (snd A T ≫ h' ^ m) (snd A T ≫ h' ^ m) = 0 := by
    rw [← pull_evc, hT (evc hP (h' ^ m) (h' ^ m)), map_zero]
  have key : evc hP (snd A T ≫ h' ^ m) (snd A T ≫ h' ^ m) + evc hP (snd A T ≫ h' ^ m) (fst A T) +
      (evc hP (fst A T) (snd A T ≫ h' ^ m) + evc hP (fst A T) (fst A T)) - evc hP (fst A T) (fst A T) = 0 := by
    rw [← eR, ← eR, ← eL]
    exact e0.symm
  rw [hXX, eS (fst A T) (snd A T ≫ h' ^ m)] at key
  have h2 : 2 • evc hP (snd A T ≫ h' ^ m) (fst A T) = 0 := by
    rw [two_nsmul, ← key]
    abel
  rw [comp_pow_pt, evc_pow_left hP (fun a a' t => eL a a' t)] at h2
  have hsq' : toUnit (A ⊗ T) ≫ h₀ = (snd A T ≫ h') ^ 2 := by
    rw [← comp_pow_pt, hsq, ← Category.assoc, toUnit_unique (snd A T ≫ toUnit T) (toUnit _)]
  have hQ : (GlobalTheory.UPel.HT.Hecke.lbPow P m).IsLB := LB.isLB_linComb hP _ _
  have eQ : ∀ {Y : Over S} (a b : Y ⟶ A), evc hQ a b = m • evc hP a b := by
    intro Y a b
    rw [evc, cls_heckePow hP m hQ, map_nsmul]
    rfl
  refine (cls_eq_zero_iff (pull_isLB (pull_isLB hQ _) _)).1 ?_
  rw [cls_pull (pull_isLB hQ _)]
  change CechPic.pull (fst A T).left (evc hQ (toUnit A ≫ h₀) (𝟙 A)) = 0
  rw [pull_evc, eQ, Category.comp_id, ← Category.assoc, toUnit_unique (fst A T ≫ toUnit A) (toUnit _), hsq',
    evc_pow_left hP (fun a a' t => eL a a' t), smul_comm]
  exact h2

end GlobalTheory.PicBilin
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.biextension_trivial_of_translate_difference_trivial : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (P : LB (A ⊗ A).left), P.IsLB →
    (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    LBIso P (P.pull (lift (snd A A) (fst A A)).left) →
    ∀ (T : Over S), (∀ c : GlobalTheory.CechPic.Pic T.left, c = 0) →
    ∀ (h₀ : 𝟙_ (Over S) ⟶ A) (h' : T ⟶ A) (m : ℕ), h' ^ 2 = toUnit T ≫ h₀ →
    (∃ t : (Out.translDiff A (P.pull (lift (𝟙 A) (𝟙 A)).left) (h' ^ m)).Gen, t.IsGen) →
    ∃ t : (((GlobalTheory.UPel.HT.Hecke.lbPow P m).pull (lift (toUnit A ≫ h₀) (𝟙 A)).left).pull (fst A T).left).Gen, t.IsGen := by
  first | (exact @GlobalTheory.PicBilin.triv_pow_of_translDiff) | (exact GlobalTheory.PicBilin.triv_pow_of_translDiff) | (intros; apply GlobalTheory.PicBilin.triv_pow_of_translDiff  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.HeckeRoot

variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {K : Type} [Field K] {Q : Type} [Group Q]
    {act : D.O → Q → Q} {e : ℕ → Q → Q → Kˣ → Prop}

theorem ev_nsmul (I : TateIsoO D K Q act e) (n j : ℕ) (y : D.La) : I.ev n (j • y) = I.ev n y ^ j := by
  induction j with
  | zero =>
    have h := I.add n 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact mul_left_cancel (a := I.ev n 0) (h.symm.trans (_root_.mul_one _).symm)
  | succ j ih => rw [succ_nsmul, I.add, ih, pow_succ]

theorem pair_one (I : TateIsoO D K Q act e) (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p) (w : D.La)
    (hw : ∀ v, (n : ℤ) ∣ 2 * D.EF w v) :
    I.ev n w ^ n = 1 ∧ ∀ z : Q, z ^ n = 1 → e n (I.ev n w) z 1 := by
  refine ⟨(I.onto n hn hnp _).2 ⟨w, rfl⟩, fun z hz => ?_⟩
  obtain ⟨v, rfl⟩ := (I.onto n hn hnp z).1 hz
  have h := I.isom n hn hnp w v
  obtain ⟨t, ht⟩ := hw v
  rw [ht, zpow_mul, zpow_natCast, (I.ζ_prim n hn hnp).pow_eq_one, one_zpow] at h
  exact h

theorem sqrt_hecke_point_weil_orthogonal : ∀ {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (K : Type) [Field K] (Q : Type) [Group Q]
    (act : D.O → Q → Q) (e : ℕ → Q → Q → Kˣ → Prop) (I : GlobalTheory.UPel.HT.TateIsoO D K Q act e)
    (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 0 < N → N.Coprime p →
    (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ x : D.La,
    ∃ (n : ℕ) (h' : Q), 0 < n ∧ n.Coprime p ∧ h' ^ 2 = I.ev (N * k) (N • g x) ∧ (h' ^ (k ^ 2 / c)) ^ n = 1 ∧
      ∀ z : Q, z ^ n = 1 → e n (h' ^ (k ^ 2 / c)) z 1 := by
  intro p _ D K _ Q _ act e I g c k N hc hk hN hNp hEF hsurj hck x
  have hp : p.Prime := Fact.out
  have hc0 : c ≠ 0 := by
    rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left _ |>.mp hc)
  have hk0 : k ≠ 0 := by
    rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left _ |>.mp hk)
  have hm : k ^ 2 / c * c = k ^ 2 := Nat.div_mul_cancel hck
  have key : ∀ v, ∃ v', ((k ^ 2 / c : ℕ) : ℤ) * D.EF (g x) v = k * D.EF x v' := by
    intro v
    obtain ⟨v', hv'⟩ := hsurj v
    refine ⟨v', ?_⟩
    have h1 : D.EF (g x) (g v') = (k : ℤ) * D.EF (g x) v := by rw [hv', map_nsmul, nsmul_eq_mul]
    have h2 := hEF x v'
    have hcZ : (c : ℤ) ≠ 0 := by exact_mod_cast hc0
    have hmZ : ((k ^ 2 / c : ℕ) : ℤ) * c = (k : ℤ) ^ 2 := by exact_mod_cast hm
    apply mul_left_cancel₀ hcZ
    calc (c : ℤ) * (((k ^ 2 / c : ℕ) : ℤ) * D.EF (g x) v)
        = (((k ^ 2 / c : ℕ) : ℤ) * c) * D.EF (g x) v := by ring
      _ = k * (k * D.EF (g x) v) := by rw [hmZ]; ring
      _ = k * (c * D.EF x v') := by rw [← h1, h2]
      _ = c * (k * D.EF x v') := by ring
  have core : ∀ n j : ℕ, 0 < n → n.Coprime p → (n : ℤ) ∣ 2 * j * N * k →
      (I.ev n (j • N • g x) ^ (k ^ 2 / c)) ^ n = 1 ∧
        ∀ z : Q, z ^ n = 1 → e n (I.ev n (j • N • g x) ^ (k ^ 2 / c)) z 1 := by
    intro n j hn hnp hd
    rw [← ev_nsmul]
    refine pair_one I n hn hnp _ (fun v => ?_)
    obtain ⟨v', hv'⟩ := key v
    have : 2 * D.EF ((k ^ 2 / c) • j • N • g x) v = 2 * j * N * k * D.EF x v' := by
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      calc _ = 2 * (j : ℤ) * N * (((k ^ 2 / c : ℕ) : ℤ) * D.EF (g x) v) := by ring
        _ = _ := by rw [hv']; ring
    rw [this]
    exact hd.mul_right _
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨r, hr⟩ : Odd k := Nat.odd_iff.2 (by
      rcases Nat.mod_two_eq_zero_or_one k with h | h
      · exfalso
        have h2 : 2 ∣ Nat.gcd k 2 := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h) dvd_rfl
        rw [hk] at h2; omega
      · exact h)
    have hnp : (N * k).Coprime 2 := Nat.Coprime.mul hNp hk
    have hn : 0 < N * k := Nat.mul_pos hN (Nat.pos_of_ne_zero hk0)
    refine ⟨N * k, I.ev (N * k) ((r + 1) • N • g x), hn, hnp, ?_, ?_⟩
    · rw [ev_nsmul, ← pow_mul, show (r + 1) * 2 = 1 + k by omega, pow_add, pow_one, ← ev_nsmul,
        smul_smul, mul_comm k N, (I.ker (N * k) hn hnp _).2 ⟨g x, rfl⟩, _root_.mul_one]
    · exact core (N * k) (r + 1) hn hnp ⟨2 * (r + 1), by push_cast; ring⟩
  · have h2p : (2 : ℕ).Coprime p := (Nat.coprime_primes Nat.prime_two hp).2 (fun h => hp2 h.symm)
    have hnp : (N * k * 2).Coprime p := Nat.Coprime.mul (Nat.Coprime.mul hNp hk) h2p
    have hnk : 0 < N * k := Nat.mul_pos hN (Nat.pos_of_ne_zero hk0)
    refine ⟨N * k * 2, I.ev (N * k * 2) (N • g x), by omega, hnp, I.tower (N * k) 2 hnk (by norm_num) hnp _, ?_⟩
    have := core (N * k * 2) 1 (by omega) hnp ⟨1, by push_cast; ring⟩
    simpa only [one_smul] using this

end GlobalTheory.UPel.HT.HeckeRoot
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sqrt_heckePoint_weilPairing_orthogonal : ∀ {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (K : Type) [Field K] (Q : Type) [Group Q]
    (act : D.O → Q → Q) (e : ℕ → Q → Q → Kˣ → Prop) (I : GlobalTheory.UPel.HT.TateIsoO D K Q act e)
    (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 0 < N → N.Coprime p →
    (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ x : D.La,
    ∃ (n : ℕ) (h' : Q), 0 < n ∧ n.Coprime p ∧ h' ^ 2 = I.ev (N * k) (N • g x) ∧ (h' ^ (k ^ 2 / c)) ^ n = 1 ∧
      ∀ z : Q, z ^ n = 1 → e n (h' ^ (k ^ 2 / c)) z 1 := by
  first | (exact @GlobalTheory.UPel.HT.HeckeRoot.sqrt_hecke_point_weil_orthogonal) | (exact GlobalTheory.UPel.HT.HeckeRoot.sqrt_hecke_point_weil_orthogonal) | (intros; apply GlobalTheory.UPel.HT.HeckeRoot.sqrt_hecke_point_weil_orthogonal  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HeckeFibre

theorem transl_triv {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (M : LB A.left) (hM : M.IsLB) (hR : Out.Rigidified A M) (K : Type) [Field K] [IsAlgClosed K]
    (y : Sp K ⟶ S) (n : ℕ) (hn : (n : K) ≠ 0) (x : Over.mk y ⟶ A) (hx : x ^ n = 1)
    (h : ∀ z : Over.mk y ⟶ A, z ^ n = 1 → Out.WeilIs A M (n : ℤ) x z 1) :
    ∃ t : (Out.translDiff A M x).Gen, t.IsGen := by
  obtain ⟨L, hL, ⟨c⟩⟩ := GlobalTheory.Moduli.cubicalStr_of_triv_theta GlobalTheory.abelianSchemeLaws_all.1 _ A hA M hM hR
    (GlobalTheory.WeilIntegral.triv_theta GlobalTheory.CubeTop.cubeTheorem hA hM)
  subst hL
  exact GlobalTheory.OrthKer.mem_kernel_of_cubWeil_orthogonal K S y A hA L c n hn x hx
    (fun z hz => (GlobalTheory.UU.cubWeil_iff_weilIs GlobalTheory.globalFns_holds hA hx hz 1).2 (h z hz))

theorem pic_field_eq_zero (K : Type) [Field K] (c : GlobalTheory.CechPic.Pic (Sp K)) : c = 0 := by
  obtain ⟨V, hV, hc⟩ := GlobalTheory.AbDual.exists_pull_eq_zero c (IsLocalRing.closedPoint K)
  have h := GlobalTheory.AbDual.pull_eq_zero_of_mem V (𝟙 _) (fun z => by
    have : z = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this]; exact hV) hc
  rwa [GlobalTheory.CechPic.pull_id] at h

theorem rigidified_diag {S : Scheme.{0}} (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) (hP : P.IsLB)
    (rig₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) :
    Out.Rigidified A (P.pull (lift (𝟙 A) (𝟙 A)).left) := by
  have h0 := (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP _)).2 rig₁
  refine (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB (pull_isLB hP _) _)).1 ?_
  rw [GlobalTheory.CechPic.cls_pull (pull_isLB hP _), GlobalTheory.CechPic.cls_pull hP, ← GlobalTheory.CechPic.pull_comp]
  have e : eSec A ≫ (lift (𝟙 A) (𝟙 A)).left = eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left := by
    have h1 : η[A] ≫ (1 : A ⟶ A) = η[A] := by
      rw [MonObj.comp_one, CategoryTheory.Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    simp only [eSec, ← Over.comp_left, comp_lift, Category.comp_id, h1]
  rw [e, GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull hP _ (pull_isLB hP _), h0, map_zero]

end GlobalTheory.HeckeFibre

namespace GlobalTheory.HeckeFibre

theorem fibre_triv : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), ∃ t : (((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (toUnit o.A ≫ h) (𝟙 o.A)).left).pull (pullback.fst o.A.hom y)).Gen, t.IsGen := by
  intro p _ D R _ b g c k N hc hk hN3 hNp hEF hsurj hdvd S s o h hh K _ _ y
  obtain ⟨x, rfl⟩ := hh
  obtain ⟨β, hβ⟩ : ∃ β : R →+* K, y ≫ s = spMap β :=
    ⟨(Spec.preimage (y ≫ s)).hom, by simp [spMap]⟩
  obtain ⟨I, hI⟩ := o.geom K y β hβ
  obtain ⟨n, h', hn0, hnp, hsq, hpow, hW⟩ :=
    GlobalTheory.T.exists_sqrt_heckePoint_weilPairing_orthogonal D K _ _ _ I g c k N hc hk (by omega) hNp hEF hsurj hdvd x
  have hnK : (n : K) ≠ 0 := by
    have := (b.unit n hnp).map β
    rw [map_natCast] at this
    exact this.ne_zero
  have htr := transl_triv o.A o.ab _ (pull_isLB o.isLB _) (rigidified_diag o.A o.P o.isLB o.rig₁) K y n hnK
    (h' ^ (k ^ 2 / c)) hpow (fun z hz => by
      have w := hW z hz
      have e1 : unitOn (1 : Kˣ) = 1 := map_one _
      rw [e1] at w
      exact w)
  exact GlobalTheory.T.biextension_trivial_of_translate_difference_trivial o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.symm (Over.mk y) (pic_field_eq_zero K)
    (o.eta (N • g x)) h' (k ^ 2 / c) (by rw [hsq, hI]) htr

end GlobalTheory.HeckeFibre
end
end
