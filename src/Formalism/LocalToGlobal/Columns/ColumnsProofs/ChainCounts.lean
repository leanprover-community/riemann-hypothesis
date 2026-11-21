import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

namespace ChainCounts

section Gen

variable {E : Type} [Field E] [NumberField E]

def UnifAt (P : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ a : E, IntAt P a → redP P a = 0 → IntAt P (a / (qOf P : E))

theorem qOf_ne_zero (P : HeightOneSpectrum (𝓞 E)) : (qOf P : E) ≠ 0 := by
  have h : qOf P ≠ 0 := by
    unfold qOf
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact P.ne_bot
  exact_mod_cast h

theorem intAt_zero (P : HeightOneSpectrum (𝓞 E)) : IntAt P (0 : E) := by
  simpa using IntAt.coe P (0 : 𝓞 E)

theorem intAt_one (P : HeightOneSpectrum (𝓞 E)) : IntAt P (1 : E) := by
  simpa using IntAt.coe P (1 : 𝓞 E)

theorem intAt_natCast (P : HeightOneSpectrum (𝓞 E)) (k : ℕ) : IntAt P (k : E) := by
  simpa using IntAt.coe P (k : 𝓞 E)

theorem intAt_neg {P : HeightOneSpectrum (𝓞 E)} {a : E} (h : IntAt P a) : IntAt P (-a) := by
  have := IntAt.mul (IntAt.coe P (-1 : 𝓞 E)) h
  simpa using this

theorem intAt_sub {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a - b) := by
  simpa [sub_eq_add_neg] using IntAt.add ha (intAt_neg hb)

theorem intAt_zpow_mul (P : HeightOneSpectrum (𝓞 E)) {k : ℤ} (hk : 0 ≤ k) {a : E} (ha : IntAt P a) :
    IntAt P ((qOf P : E) ^ k * a) := by
  obtain ⟨k', rfl⟩ := Int.eq_ofNat_of_zero_le hk
  rw [zpow_natCast]
  have h := intAt_natCast (E := E) P (qOf P ^ k')
  push_cast at h
  exact IntAt.mul h ha

theorem reduction_sub' {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) :
    redP P (a - b) = redP P a - redP P b := by
  have h := reduction_add (intAt_sub ha hb) hb
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem card_quot (P : HeightOneSpectrum (𝓞 E)) : Nat.card (𝓞 E ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

instance finite_quot (P : HeightOneSpectrum (𝓞 E)) : Finite (𝓞 E ⧸ P.asIdeal) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_quot, Ne, Ideal.absNorm_eq_zero_iff]
  exact P.ne_bot

theorem mem_localization_of_smul_mem₂ [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) {s : 𝓞 E}
    (hs : s ∉ P.asIdeal) {w : Sp E n} (h : s • w ∈ localization₂ P.asIdeal N) : w ∈ localization₂ P.asIdeal N := by
  obtain ⟨s', hs', h'⟩ := (mem_locP P N _).1 h
  refine (mem_locP P N w).2 ⟨s' * s, fun hm => (P.isPrime.mem_or_mem hm).elim hs' hs, ?_⟩
  rwa [mul_smul]

theorem natCast_smul_mem {n : ℕ} (M : Submodule (𝓞 E) (Sp E n)) (k : ℕ) {w : Sp E n} (h : w ∈ M) :
    ((k : ℕ) : E) • w ∈ M := by
  rw [Nat.cast_smul_eq_nsmul]
  exact M.nsmul_mem h k

theorem unifAt_of_not_mem_sq (P : HeightOneSpectrum (𝓞 E)) (h : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) : UnifAt P := by
  intro a ⟨r, s, hs, hsa⟩ hred
  have hr : r ∈ P.asIdeal := by
    have := reduction_spec P hs hsa
    rw [hred, mul_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this.symm
  have hqP : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem P.asIdeal
  obtain ⟨I, hI⟩ : P.asIdeal ∣ Ideal.span {((qOf P : ℕ) : 𝓞 E)} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hqP)
  have hIP : ¬ I ≤ P.asIdeal := by
    intro hle
    apply h
    have : Ideal.span {((qOf P : ℕ) : 𝓞 E)} ≤ P.asIdeal ^ 2 := by
      rw [hI, sq]
      exact Ideal.mul_mono_right hle
    exact (Ideal.span_singleton_le_iff_mem _).1 this
  obtain ⟨s', hs'I, hs'P⟩ := Set.not_subset.1 hIP
  have hmem : r * s' ∈ Ideal.span {((qOf P : ℕ) : 𝓞 E)} := by
    rw [hI]
    exact Ideal.mul_mem_mul hr hs'I
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨t, s' * s, fun hm => (P.isPrime.mem_or_mem hm).elim hs'P hs, ?_⟩
  have hq := qOf_ne_zero (E := E) P
  have ht' := congrArg (algebraMap (𝓞 E) E) ht
  simp only [map_mul, map_natCast] at ht'
  rw [map_mul, div_eq_mul_inv,
    show algebraMap (𝓞 E) E s' * algebraMap (𝓞 E) E s * (a * ((qOf P : ℕ) : E)⁻¹) =
      (algebraMap (𝓞 E) E s * a) * algebraMap (𝓞 E) E s' * ((qOf P : ℕ) : E)⁻¹ by ring, hsa, ← ht',
    mul_inv_cancel_right₀ hq]

end Gen

section Scl

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem mem_stabL_iff {n : ℕ} {M : Submodule (𝓞 E) (Sp E n)} {κ : Sp E n ≃ₗ[E] Sp E n} :
    κ ∈ stabL E n M ↔ ∀ x, κ x ∈ M ↔ x ∈ M := Iff.rfl

theorem mem_sclLat (P : HeightOneSpectrum (𝓞 E)) (q N : ℕ) (e : ℕ → ℤ) (v : Sp E N) :
    v ∈ LocE.sclLat P q N e ↔ ∀ l : Fin N, IntAt P (((q : E) ^ e l.1)⁻¹ * v l) := by
  unfold LocE.sclLat
  rw [Submodule.mem_comap]
  unfold stdAt
  rw [mem_localization_standardLattice]
  rfl

theorem sclLat_anti (P : HeightOneSpectrum (𝓞 E)) (N : ℕ) {e e' : ℕ → ℤ} (h : ∀ l : Fin N, e l.1 ≤ e' l.1) :
    LocE.sclLat P (qOf P) N e' ≤ LocE.sclLat P (qOf P) N e := by
  intro v hv
  rw [mem_sclLat] at hv ⊢
  intro l
  have hq := qOf_ne_zero (E := E) P
  have key : ((qOf P : E) ^ e l.1)⁻¹ * v l = (qOf P : E) ^ (e' l.1 - e l.1) * (((qOf P : E) ^ e' l.1)⁻¹ * v l) := by
    rw [zpow_sub₀ hq]
    have h1 : (qOf P : E) ^ e l.1 ≠ 0 := zpow_ne_zero _ hq
    have h2 : (qOf P : E) ^ e' l.1 ≠ 0 := zpow_ne_zero _ hq
    field_simp
  rw [key]
  exact intAt_zpow_mul P (by have := h l; omega) (hv l)

theorem mem_sclLat_of_qinv (P : HeightOneSpectrum (𝓞 E)) (N : ℕ) {e e' : ℕ → ℤ} (h : ∀ l : Fin N, e' l.1 ≤ e l.1 + 1)
    {w : Sp E N} (hw : ((qOf P : E))⁻¹ • w ∈ LocE.sclLat P (qOf P) N e) : w ∈ LocE.sclLat P (qOf P) N e' := by
  rw [mem_sclLat] at hw ⊢
  intro l
  have hq := qOf_ne_zero (E := E) P
  have key : ((qOf P : E) ^ e' l.1)⁻¹ * w l =
      (qOf P : E) ^ (e l.1 + 1 - e' l.1) * (((qOf P : E) ^ e l.1)⁻¹ * ((qOf P : E)⁻¹ • w) l) := by
    rw [zpow_sub₀ hq, zpow_add₀ hq, zpow_one, Pi.smul_apply, smul_eq_mul]
    have h1 : (qOf P : E) ^ e l.1 ≠ 0 := zpow_ne_zero _ hq
    have h2 : (qOf P : E) ^ e' l.1 ≠ 0 := zpow_ne_zero _ hq
    field_simp
  rw [key]
  exact intAt_zpow_mul P (by have := h l; omega) (hw l)

theorem smul_mem_sclLat {P : HeightOneSpectrum (𝓞 E)} {q N : ℕ} {e : ℕ → ℤ} {a : E} (ha : IntAt P a) {v : Sp E N}
    (hv : v ∈ LocE.sclLat P q N e) : a • v ∈ LocE.sclLat P q N e := by
  rw [mem_sclLat] at hv ⊢
  intro l
  have : ((q : E) ^ e l.1)⁻¹ * (a • v) l = a * (((q : E) ^ e l.1)⁻¹ * v l) := by
    rw [Pi.smul_apply, smul_eq_mul]; ring
  rw [this]
  exact IntAt.mul ha (hv l)

def basV (q N : ℕ) (e : ℕ → ℤ) (l : Fin N) : Sp E N := ((q : E) ^ e l.1) • (Pi.single l 1 : Sp E N)

theorem basV_mem (P : HeightOneSpectrum (𝓞 E)) (N : ℕ) (e : ℕ → ℤ) (l : Fin N) :
    basV (E := E) (qOf P) N e l ∈ LocE.sclLat P (qOf P) N e := by
  rw [mem_sclLat]
  intro l'
  have hq := qOf_ne_zero (E := E) P
  unfold basV
  rw [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs with h
  · subst h
    rw [mul_one, inv_mul_cancel₀ (zpow_ne_zero _ hq)]
    exact intAt_one P
  · rw [mul_zero, mul_zero]
    exact intAt_zero P

theorem sum_basV (P : HeightOneSpectrum (𝓞 E)) (N : ℕ) (e : ℕ → ℤ) (x : Sp E N) :
    ∑ l, (((qOf P : E) ^ e l.1)⁻¹ * x l) • basV (E := E) (qOf P) N e l = x := by
  have hq := qOf_ne_zero (E := E) P
  funext l''
  rw [Finset.sum_apply, Finset.sum_eq_single l'']
  · unfold basV
    rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, smul_eq_mul, mul_one]
    have h1 : (qOf P : E) ^ e l''.1 ≠ 0 := zpow_ne_zero _ hq
    field_simp
  · intro b _ hb
    unfold basV
    rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

def redM (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} (e : ℕ → ℤ) (κ : Sp E N ≃ₗ[E] Sp E N) : Fin N → Fin N → 𝓞 E ⧸ P.asIdeal :=
  fun l l' => redP P (((qOf P : E) ^ e l.1)⁻¹ * κ (basV (qOf P) N e l') l)

theorem cong_of_redM {P : HeightOneSpectrum (𝓞 E)} (hU : UnifAt P) {N : ℕ} {e : ℕ → ℤ} {κ κ' : Sp E N ≃ₗ[E] Sp E N}
    (hκ : κ ∈ stabL E N (LocE.sclLat P (qOf P) N e)) (hκ' : κ' ∈ stabL E N (LocE.sclLat P (qOf P) N e))
    (hred : redM P e κ = redM P e κ') :
    ∀ x ∈ LocE.sclLat P (qOf P) N e, ((qOf P : E))⁻¹ • ((κ⁻¹ * κ') x - x) ∈ LocE.sclLat P (qOf P) N e := by
  intro x hx
  have hq := qOf_ne_zero (E := E) P
  let T : Sp E N →ₗ[E] Sp E N := ((qOf P : E))⁻¹ • (κ'.toLinearMap - κ.toLinearMap)
  have hT : ∀ y, T y = ((qOf P : E))⁻¹ • (κ' y - κ y) := fun y => rfl
  have hbas : ∀ l', T (basV (qOf P) N e l') ∈ LocE.sclLat P (qOf P) N e := by
    intro l'
    rw [hT, mem_sclLat]
    intro l
    have hb := basV_mem (E := E) P N e l'
    have hu := (mem_sclLat P _ N e _).1 ((mem_stabL_iff.1 hκ' _).2 hb) l
    have hv := (mem_sclLat P _ N e _).1 ((mem_stabL_iff.1 hκ _).2 hb) l
    have hr : redP P (((qOf P : E) ^ e l.1)⁻¹ * κ' (basV (qOf P) N e l') l -
        ((qOf P : E) ^ e l.1)⁻¹ * κ (basV (qOf P) N e l') l) = 0 := by
      rw [reduction_sub' hu hv]
      have := congrFun (congrFun hred l) l'
      unfold redM at this
      rw [this, sub_self]
    have h3 := hU _ (intAt_sub hu hv) hr
    have key : ((qOf P : E) ^ e l.1)⁻¹ * ((qOf P : E)⁻¹ • (κ' (basV (qOf P) N e l') - κ (basV (qOf P) N e l'))) l =
        (((qOf P : E) ^ e l.1)⁻¹ * κ' (basV (qOf P) N e l') l - ((qOf P : E) ^ e l.1)⁻¹ * κ (basV (qOf P) N e l') l) /
          (qOf P : E) := by
      rw [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
    rw [key]
    exact h3
  have hTx : T x ∈ LocE.sclLat P (qOf P) N e := by
    rw [← sum_basV P N e x, map_sum]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [map_smul]
    exact smul_mem_sclLat ((mem_sclLat P _ N e x).1 hx l) (hbas l)
  have e1 : (κ⁻¹ * κ') x - x = κ⁻¹ (κ' x - κ x) := by
    rw [map_sub]
    show κ.symm (κ' x) - x = κ.symm (κ' x) - κ.symm (κ x)
    rw [LinearEquiv.symm_apply_apply]
  rw [e1, ← map_smul]
  exact (mem_stabL_iff.1 (Subgroup.inv_mem _ hκ) _).2 hTx

end Scl

section AtG

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem mem_flagU_iff {N : ℕ} {M : ℕ → Submodule (𝓞 E) (Sp E N)} {e : ℕ → Sp E N} {r : ℕ} {st : Set ℕ}
    {κ : Sp E N ≃ₗ[E] Sp E N} :
    κ ∈ LocE.flagU M e r st ↔ (∀ s ∈ st, κ ∈ stabL E N (M s)) ∧ ∀ s < r, κ ∈ stabL E N (M s) ∧ κ (e s) - e s ∈ M s :=
  Iff.rfl



theorem bvecG_mem (P : HeightOneSpectrum (𝓞 E)) (k₀ n c s : ℕ) :
    LocE.bvecG E (qOf P) k₀ n c s ∈ LocE.lamY P (qOf P) n c fun i => i + 1 := by
  unfold LocE.bvecG LocE.lamY
  rw [mem_sclLat]
  intro l
  have hq := qOf_ne_zero (E := E) P
  rw [Pi.smul_apply, smul_eq_mul]
  unfold Loc.eN
  split_ifs with h
  · rw [h, mul_one, inv_mul_cancel₀ (zpow_ne_zero _ hq)]
    exact intAt_one P
  · rw [mul_zero, mul_zero]
    exact intAt_zero P



theorem flagS_le (P : HeightOneSpectrum (𝓞 E)) (k₀ rS n c s : ℕ) :
    LocE.flagS P (qOf P) k₀ rS n c s ≤ LocE.lamY P (qOf P) n c fun i => i + 1 := by
  unfold LocE.flagS LocE.lamY
  apply sclLat_anti
  intro l
  split_ifs <;> omega

theorem mem_flagS_of_qinv (P : HeightOneSpectrum (𝓞 E)) (k₀ rS n c s : ℕ) {w : Sp E (n + c)}
    (hw : ((qOf P : E))⁻¹ • w ∈ LocE.lamY P (qOf P) n c fun i => i + 1) : w ∈ LocE.flagS P (qOf P) k₀ rS n c s := by
  unfold LocE.flagS
  unfold LocE.lamY at hw
  refine mem_sclLat_of_qinv P _ (fun l => ?_) hw
  split_ifs <;> omega

theorem stab_flagS_of_cong (P : HeightOneSpectrum (𝓞 E)) {n c : ℕ} {κ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hs : κ ∈ stabL E (n + c) (LocE.lamY P (qOf P) n c fun i => i + 1))
    (hc : ∀ x ∈ LocE.lamY P (qOf P) n c (fun i => i + 1), ((qOf P : E))⁻¹ • (κ x - x) ∈ LocE.lamY P (qOf P) n c fun i => i + 1)
    (k₀ rS s : ℕ) :
    κ ∈ stabL E (n + c) (LocE.flagS P (qOf P) k₀ rS n c s) ∧
      ∀ s', κ (LocE.bvecG E (qOf P) k₀ n c s') - LocE.bvecG E (qOf P) k₀ n c s' ∈ LocE.flagS P (qOf P) k₀ rS n c s := by
  refine ⟨mem_stabL_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩, fun s' => mem_flagS_of_qinv P k₀ rS n c s (hc _ (bvecG_mem P k₀ n c s'))⟩
  · have hxΛ : x ∈ LocE.lamY P (qOf P) n c fun i => i + 1 := (mem_stabL_iff.1 hs x).1 (flagS_le P k₀ rS n c s hx)
    have h1 := mem_flagS_of_qinv P k₀ rS n c s (hc x hxΛ)
    have : x = κ x - (κ x - x) := by abel
    rw [this]
    exact sub_mem hx h1
  · have hxΛ := flagS_le P k₀ rS n c s hx
    have h1 := mem_flagS_of_qinv P k₀ rS n c s (hc x hxΛ)
    have : κ x = (κ x - x) + x := by abel
    rw [this]
    exact add_mem h1 hx

theorem mem_JGsym_of_cong (P : HeightOneSpectrum (𝓞 E)) {n c : ℕ} {κ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hs : κ ∈ stabL E (n + c) (LocE.lamY P (qOf P) n c fun i => i + 1))
    (hc : ∀ x ∈ LocE.lamY P (qOf P) n c (fun i => i + 1), ((qOf P : E))⁻¹ • (κ x - x) ∈ LocE.lamY P (qOf P) n c fun i => i + 1)
    (k₀ rS r t : ℕ) : κ ∈ LocE.JGsym P (qOf P) k₀ rS r t n c := by
  unfold LocE.JGsym
  exact Subgroup.mem_inf.2 ⟨hs, mem_flagU_iff.2 ⟨fun s _ => (stab_flagS_of_cong P hs hc k₀ rS s).1, fun s _ =>
    ⟨(stab_flagS_of_cong P hs hc k₀ rS s).1, (stab_flagS_of_cong P hs hc k₀ rS s).2 _⟩⟩⟩

end AtG

section Yb

variable {E : Type} [Field E] [NumberField E] [StarRing E]


end Yb

section Chain

open Classical

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

def UnifG (Pr : Primes X) : Prop := ∀ P ∈ Pr.vGs, UnifAt P


theorem rowSG_eq_of_QE (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) : rowSG Pr sel mu = Pr.vGs := by
  unfold rowSG uSG
  rw [hQ, Finset.union_empty]



theorem gg_pos (hPr : Pr.Ok) : 0 < Pr.g 0 * Pr.g 1 := Nat.mul_pos (hPr.g_prime 0).pos (hPr.g_prime 1).pos


theorem N_le (R : Ranks) {j : ℕ} (hj : j ≤ R.m) : R.N j ≤ R.N R.m := by
  unfold Ranks.N
  have := Nat.mul_le_mul_right (R.t + 1) hj
  omega

def redIdx (j : ℕ) (b : L.β j) :
    ∀ P : rowSG Pr sel mu, Fin (R.N j + cOf R j) → Fin (R.N j + cOf R j) → 𝓞 X.E ⧸ P.1.asIdeal :=
  fun P => redM P.1 (LocE.scE (R.N j) fun i => i + 1) (L.h j b P)




def redY {n : ℕ} {ST : Finset (HeightOneSpectrum (𝓞 X.E))} (d : Deco X.E n ST Pr.vGs) (Y : Set (Sp X.E n)) :
    ∀ P : rowSG Pr sel mu, Fin n → 𝓞 X.E ⧸ P.1.asIdeal :=
  fun P => if h : P.1 ∈ Pr.vGs then d.be ⟨P.1, h⟩ (((qOf P.1 : ℕ) : X.E) • repY Y) else 0







structure CountsN (m2 : ℕ) : Prop where
  n0 : Fintype.card (L.β 0) = 1
  nLast : Fintype.card (L.β (m2 + 1)) = 1
  nMid : ∀ j, 1 ≤ j → j ≤ m2 → Fintype.card (L.β j) ≤ (Pr.g 0 * Pr.g 1) ^ (X.f * R.N R.m ^ 2)
  ybFin : ∀ (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)), (ybSet sel mu cst p.deco.1.N).Finite
  nY : ∀ (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)),
    (ybSet sel mu cst p.deco.1.N).ncard ≤ (Pr.g 0 * Pr.g 1) ^ (X.f * R.N R.m)



end Chain

section Unram

open Classical

variable {X : Fields} {Pr : Primes X}

theorem mem_of_mem_divs {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {P : HeightOneSpectrum A} (h : P ∈ divs a) :
    a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hf
  · simpa using hf.mem_toFinset.1 h
  · exact absurd h (Finset.notMem_empty _)

theorem conjO_conjO (x : 𝓞 X.E) : X.conjO (X.conjO x) = x := by
  apply RingOfIntegers.ext
  show starRingEnd X.E (starRingEnd X.E (x : X.E)) = (x : X.E)
  rw [starRingEnd_apply, starRingEnd_apply, star_star]

theorem finrank_E (hX : X.Ok) : Module.finrank ℚ X.E = 2 * X.f := by
  rw [← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, Fields.f, hX.card_Tau, mul_comm]

theorem absNorm_natCast (hX : X.Ok) (g : ℕ) : Ideal.absNorm (Ideal.span {((g : ℕ) : 𝓞 X.E)}) = g ^ (2 * X.f) := by
  rw [Ideal.absNorm_span_singleton, ← finrank_E hX, ← NumberField.RingOfIntegers.rank]
  have : ((g : ℕ) : 𝓞 X.E) = algebraMap ℤ (𝓞 X.E) (g : ℤ) := by simp
  rw [this, Algebra.norm_algebraMap]
  simp [Int.natAbs_pow]

theorem g_not_mem_sq (hX : X.Ok) (hPr : Pr.Ok) (i : Fin 2) {P0 : HeightOneSpectrum (𝓞 X.E)} (hP0 : P0 ∈ Pr.vG i) :
    ((Pr.g i : ℕ) : 𝓞 X.E) ∉ P0.asIdeal ^ 2 := by
  intro hsq
  have hgp : (Pr.g i).Prime := hPr.g_prime i
  have hπ : ∀ P ∈ Pr.vG i, X.conjO (Pr.piG i) ∈ P.asIdeal := fun P hP => mem_of_mem_divs hP
  have hgσ : X.conjO ((Pr.g i : ℕ) : 𝓞 X.E) = ((Pr.g i : ℕ) : 𝓞 X.E) := map_natCast _ _
  have hgmem : ∀ P ∈ Pr.vG i, ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
    intro P hP
    rw [← hPr.piG_norm i]
    exact Ideal.mul_mem_left _ _ (hπ P hP)
  have hne0 : ((Pr.g i : ℕ) : 𝓞 X.E) ≠ 0 := Nat.cast_ne_zero.2 hgp.ne_zero
  set A : Finset (Ideal (𝓞 X.E)) := (Pr.vG i).image fun P => P.asIdeal with hA
  set B : Finset (Ideal (𝓞 X.E)) := (Pr.vG i).image fun P => P.asIdeal.comap X.conjO with hB
  have hT : ∀ Q ∈ A ∪ B, ((Pr.g i : ℕ) : 𝓞 X.E) ∈ Q ∧ Q.IsMaximal := by
    intro Q hQ
    rcases Finset.mem_union.1 hQ with hQA | hQB
    · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hQA
      exact ⟨hgmem P hP, P.isMaximal⟩
    · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hQB
      have hm : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal.comap X.conjO := by
        rw [Ideal.mem_comap, hgσ]
        exact hgmem P hP
      have : (P.asIdeal.comap X.conjO).IsPrime := Ideal.IsPrime.comap _
      refine ⟨hm, Ideal.IsPrime.isMaximal this ?_⟩
      intro hbot
      rw [hbot] at hm
      exact hne0 ((Submodule.mem_bot _).1 hm)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro Q hQA hQB
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hQA
    obtain ⟨P', hP', he⟩ := Finset.mem_image.1 hQB
    have h1 : Pr.piG i ∈ P.asIdeal := by
      rw [← he, Ideal.mem_comap]
      exact hπ P' hP'
    have h2 := hπ P hP
    obtain ⟨a, b, hab⟩ := hPr.piG_cop i
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
  have hcardA : A.card = X.f := by
    rw [hA, Finset.card_image_of_injective _ (fun P P' h => HeightOneSpectrum.ext h), hPr.vG_card i]
  have hcardB : B.card = X.f := by
    rw [hB, Finset.card_image_of_injective _ ?_, hPr.vG_card i]
    intro P P' h
    apply HeightOneSpectrum.ext
    ext x
    have := congrArg (fun I : Ideal (𝓞 X.E) => X.conjO x ∈ I) h
    simpa [Ideal.mem_comap, conjO_conjO] using this
  have hcardT : (A ∪ B).card = 2 * X.f := by
    rw [Finset.card_union_of_disjoint hdisj, hcardA, hcardB]
    ring
  have hP0T : P0.asIdeal ∈ A ∪ B := Finset.mem_union_left _ (Finset.mem_image_of_mem _ hP0)
  have hdvd : ∏ Q ∈ A ∪ B, (if Q = P0.asIdeal then Q ^ 2 else Q) ∣ Ideal.span {((Pr.g i : ℕ) : 𝓞 X.E)} := by
    apply Finset.prod_dvd_of_coprime
    · intro Q hQ Q' hQ' hne
      have hc : IsCoprime Q Q' :=
        Ideal.isCoprime_iff_sup_eq.2 (Ideal.IsMaximal.coprime_of_ne (hT Q hQ).2 (hT Q' hQ').2 hne)
      simp only [Function.onFun]
      split_ifs
      · exact hc.pow
      · exact hc.pow_left
      · exact hc.pow_right
      · exact hc
    · intro Q hQ
      rw [Ideal.dvd_span_singleton]
      split_ifs with h
      · rw [h]
        exact hsq
      · exact (hT Q hQ).1
  have hgQ : ∀ Q ∈ A ∪ B, Pr.g i ∣ Ideal.absNorm Q := by
    intro Q hQ
    have h1 : Ideal.absNorm Q ∣ (Pr.g i) ^ (2 * X.f) := by
      rw [← absNorm_natCast hX]
      exact map_dvd Ideal.absNorm (Ideal.dvd_span_singleton.2 (hT Q hQ).1)
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hgp).1 h1
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, Ideal.absNorm_eq_one_iff] at hk
      exact (hT Q hQ).2.ne_top hk
    rw [hk]
    exact dvd_pow_self _ hk0
  have h2 : (Pr.g i) ^ (2 * X.f) * Pr.g i ∣ Ideal.absNorm (Ideal.span {((Pr.g i : ℕ) : 𝓞 X.E)}) := by
    refine dvd_trans ?_ (map_dvd Ideal.absNorm hdvd)
    rw [map_prod]
    have e1 : (Pr.g i) ^ (2 * X.f) * Pr.g i = ∏ Q ∈ A ∪ B, (Pr.g i * if Q = P0.asIdeal then Pr.g i else 1) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, hcardT, Finset.prod_ite_eq', if_pos hP0T]
    rw [e1]
    refine Finset.prod_dvd_prod_of_dvd _ _ fun Q hQ => ?_
    split_ifs with h
    · rw [map_pow, sq]
      exact mul_dvd_mul (hgQ Q hQ) (hgQ Q hQ)
    · rw [mul_one]
      exact hgQ Q hQ
  rw [absNorm_natCast hX, ← pow_succ, Nat.pow_dvd_pow_iff_le_right hgp.one_lt] at h2
  omega

theorem unifG_of (hX : X.Ok) (hPr : Pr.Ok) : UnifG Pr := by
  intro P hP
  apply unifAt_of_not_mem_sq
  unfold qOf
  rcases Finset.mem_union.1 hP with h | h
  · rw [hPr.vG_norm 0 P h]
    exact g_not_mem_sq hX hPr 0 h
  · rw [hPr.vG_norm 1 P h]
    exact g_not_mem_sq hX hPr 1 h

end Unram

section Final

open Classical

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))



end Final

end ChainCounts

end Formalism.L2.Col
