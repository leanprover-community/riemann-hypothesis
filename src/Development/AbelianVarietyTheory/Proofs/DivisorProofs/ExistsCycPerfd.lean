import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationPrimitiveRootPrimePowSubOne

section
section
open Ideal WittVector

namespace GlobalTheory.PadicComplQuot

theorem mem_map_iff_evalOne {A : Type} [CommRing A] (I : Ideal A) (hI : I.FG) (x : AdicCompletion I A) :
    x ∈ I.map (algebraMap A (AdicCompletion I A)) ↔ AdicCompletion.evalOneₐ I x = 0 := by
  rw [← AdicCompletion.ker_evalOneₐ_eq_map _ hI, RingHom.mem_ker]
  rfl

theorem quot_completion (p : ℕ) (A : Type) [CommRing A] (_hp : IsSMulRegular A (p : A)) :
    Function.Surjective ((Ideal.Quotient.mk (Ideal.span {(p : AdicCompletion (Ideal.span {(p : A)}) A)})).comp
        (algebraMap A (AdicCompletion (Ideal.span {(p : A)}) A))) ∧
      RingHom.ker ((Ideal.Quotient.mk (Ideal.span {(p : AdicCompletion (Ideal.span {(p : A)}) A)})).comp
        (algebraMap A (AdicCompletion (Ideal.span {(p : A)}) A))) = Ideal.span {(p : A)} := by
  set I : Ideal A := Ideal.span {(p : A)} with hIdef
  have hfg : I.FG := Submodule.fg_span_singleton _
  have hspan : Ideal.span {(p : AdicCompletion I A)} = I.map (algebraMap A (AdicCompletion I A)) := by
    rw [hIdef, Ideal.map_span, Set.image_singleton, map_natCast]
  have hcomm : ∀ a : A, AdicCompletion.evalOneₐ I (algebraMap A (AdicCompletion I A) a) = Ideal.Quotient.mk I a :=
    fun a => (AdicCompletion.evalOneₐ I).commutes a
  refine ⟨?_, ?_⟩
  · intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ I r)
    refine ⟨a, ?_⟩
    rw [RingHom.comp_apply, Ideal.Quotient.eq, hspan, mem_map_iff_evalOne I hfg, map_sub, hcomm, ha, sub_self]
  · ext a
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hspan, mem_map_iff_evalOne I hfg, hcomm,
      Ideal.Quotient.eq_zero_iff_mem]

end GlobalTheory.PadicComplQuot
end

open Ideal WittVector
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adic_completion_quotient_ker_eq : ∀ (p : ℕ) (A : Type) [CommRing A], IsSMulRegular A (p : A) → Function.Surjective ((Ideal.Quotient.mk (Ideal.span {(p : AdicCompletion (Ideal.span {(p : A)}) A)})).comp (algebraMap A (AdicCompletion (Ideal.span {(p : A)}) A))) ∧ RingHom.ker ((Ideal.Quotient.mk (Ideal.span {(p : AdicCompletion (Ideal.span {(p : A)}) A)})).comp (algebraMap A (AdicCompletion (Ideal.span {(p : A)}) A))) = Ideal.span {(p : A)} := by
  atlas_forward_decl GlobalTheory.PadicComplQuot.quot_completion
end

section
section
open Ideal WittVector

namespace GlobalTheory

theorem isSMulRegular_natCast_adicCompletion (p : ℕ) (A : Type) [CommRing A]
    (hp : IsSMulRegular A (p : A)) :
    IsSMulRegular (AdicCompletion (Ideal.span {(p : A)}) A)
      (p : AdicCompletion (Ideal.span {(p : A)}) A) := by
  set I : Ideal A := Ideal.span {(p : A)}
  intro x y hxy
  have key : ∀ z : AdicCompletion I A, (p : AdicCompletion I A) * z = 0 → z = 0 := by
    intro z hz
    apply AdicCompletion.ext
    intro n
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (z.val (n + 1))
    have hz' : (p • z).val (n + 1) = 0 := by
      rw [nsmul_eq_mul, hz]; rfl
    rw [AdicCompletion.val_smul_apply, ← ha, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero] at hz'
    have hmem : (p : A) * a ∈ Ideal.span {(p : A) ^ (n + 1)} := by
      have : p • a = (p : A) * a := by rw [nsmul_eq_mul]
      rw [← this, ← Ideal.span_singleton_pow]
      simpa [smul_eq_mul, Ideal.mul_top] using hz'
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
    have hab : a = (p : A) ^ n * b := by
      apply hp
      simp only [smul_eq_mul]
      rw [← hb]; ring
    have htr := z.property (Nat.le_succ n)
    change AdicCompletion.transitionMap I A (Nat.le_succ n) (z.val (n + 1)) = z.val n at htr
    rw [← htr, ← ha, AdicCompletion.val_zero_apply]
    change (Submodule.Quotient.mk a : A ⧸ (I ^ n • ⊤ : Submodule A A)) = 0
    rw [Submodule.Quotient.mk_eq_zero, hab]
    simp only [smul_eq_mul, Ideal.mul_top, I, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton'.mpr ⟨b, mul_comm _ _⟩
  have h0 : (p : AdicCompletion I A) * (x - y) = 0 := by
    rw [mul_sub, sub_eq_zero]; exact hxy
  exact sub_eq_zero.mp (key _ h0)

end GlobalTheory
end

open Ideal WittVector
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSMulRegular_adicCompletion : ∀ (p : ℕ) (A : Type) [CommRing A], IsSMulRegular A (p : A) → IsSMulRegular (AdicCompletion (Ideal.span {(p : A)}) A) (p : AdicCompletion (Ideal.span {(p : A)}) A) := by
  atlas_forward_decl GlobalTheory.isSMulRegular_natCast_adicCompletion
end

section
section
open Ideal WittVector

namespace GlobalTheory

theorem pflat_dvd_of_roots : ∀ (p : ℕ) [Fact p.Prime] (A R : Type) [CommRing A] [IsDomain A] [CommRing R]
    [Fact ¬IsUnit (p : R)] [IsAdicComplete (Ideal.span {(p : R)}) R] (φ : A →+* R), (p : A) ≠ 0 →
    Function.Surjective ((Ideal.Quotient.mk (Ideal.span {(p : R)})).comp φ) →
    RingHom.ker ((Ideal.Quotient.mk (Ideal.span {(p : R)})).comp φ) = Ideal.span {(p : A)} →
    ∀ π : ℕ → A, π 0 = p → (∀ n, π (n + 1) ^ p = π n) → (∀ (n : ℕ) (x : A), (p : A) ∣ x ^ (p ^ n) → π n ∣ x) →
    ∃ pflat : PreTilt R p, PreTilt.untilt pflat = (p : R) ∧ ∀ c : PreTilt R p, PreTilt.coeff 0 c = 0 → pflat ∣ c := by
  intro p hp A R _ _ _ _ _ φ hp0 hsurj hker π hπ0 hπ hdiv
  classical
  have hpp : p.Prime := hp.out
  have : CharP (R ⧸ Ideal.span {(p : R)}) p := (inferInstance : CharP (ModP R p) p)
  set g := (Ideal.Quotient.mk (Ideal.span {(p : R)})).comp φ with hg
  have hf : ∀ n, φ (π (n + 1)) ^ p = φ (π n) := fun n => by rw [← map_pow, hπ]
  refine ⟨ReciprocityTheory.PGsh.ofRoots (fun n => φ (π n)) hf, ?_, ?_⟩
  · rw [ReciprocityTheory.PGsh.untilt_ofRoots, hπ0, map_natCast]
  intro c hc
  have hz : ∀ x, g x = 0 ↔ (p : A) ∣ x := fun x => by
    rw [← RingHom.mem_ker, hker, Ideal.mem_span_singleton]
  have hππ : ∀ n, π n ^ p ^ n = p := by
    intro n
    induction n with
    | zero => simp [hπ0]
    | succ n ih => rw [pow_succ', pow_mul, hπ, ih]
  have hcs : ∀ n, Perfection.coeff (ModP R p) p (n + 1) c ^ p = Perfection.coeff (ModP R p) p n c :=
    fun n => Perfection.coeff_pow_p' c n
  have hc0 : Perfection.coeff (ModP R p) p 0 c = 0 := by rw [← PreTilt.coeff_def]; exact hc
  have hcp : ∀ n, Perfection.coeff (ModP R p) p n c ^ p ^ n = 0 := by
    intro n
    induction n with
    | zero => simpa using hc0
    | succ n ih => rw [pow_succ', pow_mul, hcs, ih]
  choose y hy using fun n => hsurj (show R ⧸ Ideal.span {(p : R)} from Perfection.coeff (ModP R p) p n c)
  have hyp : ∀ n, (p : A) ∣ y n ^ p ^ n := fun n => (hz _).1 (by rw [map_pow, hy]; exact hcp n)
  choose z hzy using fun n => hdiv n (y n) (hyp n)
  have compat : ∀ n, g (z (n + 2) ^ p) ^ p = g (z (n + 1) ^ p) := by
    intro n
    set b := z (n + 2) ^ p - z (n + 1) with hb
    have h1 : π (n + 1) * b = y (n + 2) ^ p - y (n + 1) := by
      rw [hzy (n + 2), hzy (n + 1), mul_pow, hπ (n + 1), hb]; ring
    have h2 : g (π (n + 1) * b) = 0 := by
      rw [h1, map_sub, map_pow, hy, hy]
      exact sub_eq_zero.2 (hcs (n + 1))
    obtain ⟨w, hw⟩ := (hz _).1 h2
    have e1 : π n * b ^ p = (p : A) ^ p * w ^ p := by rw [← hπ n, ← mul_pow, hw, mul_pow]
    have hp2 : (p : A) ^ p = (p : A) ^ (p - 2) * (p : A) ^ 2 := by
      rw [← pow_add, Nat.sub_add_cancel hpp.two_le]
    have hn1 : π n ^ p ^ n = π n ^ (p ^ n - 1) * π n := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hpp.pos)]
    have e2 : (p : A) * b ^ p = (p : A) * ((p : A) * ((p : A) ^ (p - 2) * w ^ p * π n ^ (p ^ n - 1))) := by
      calc (p : A) * b ^ p = π n ^ p ^ n * b ^ p := by rw [hππ]
        _ = π n ^ (p ^ n - 1) * (π n * b ^ p) := by rw [hn1]; ring
        _ = _ := by rw [e1, hp2]; ring
    have hbp : g (b ^ p) = 0 := (hz _).2 ⟨_, mul_left_cancel₀ hp0 e2⟩
    have hz2 : z (n + 2) ^ p = z (n + 1) + b := by rw [hb]; ring
    rw [← map_pow, ← pow_mul, mul_comm, pow_mul, hz2, map_pow, map_add, add_pow_char, ← map_pow g b, hbp,
      add_zero, map_pow]
  let d : PreTilt R p := ⟨fun n => g (z (n + 1) ^ p), fun n => compat n⟩
  refine ⟨d, Perfection.ext fun n => ?_⟩
  show Perfection.coeff (ModP R p) p n c = g (π n) * g (z (n + 1) ^ p)
  rw [← map_mul, ← hπ n, ← mul_pow, ← hzy (n + 1), map_pow, hy, hcs]

end GlobalTheory
end

open Ideal WittVector
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perfectoid_tower_surjective : ∀ (p : ℕ) [Fact p.Prime] (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (Ideal.span {(p : R)}) R] (φ : A →+* R), (p : A) ≠ 0 → Function.Surjective ((Ideal.Quotient.mk (Ideal.span {(p : R)})).comp φ) → RingHom.ker ((Ideal.Quotient.mk (Ideal.span {(p : R)})).comp φ) = Ideal.span {(p : A)} → ∀ π : ℕ → A, π 0 = p → (∀ n, π (n + 1) ^ p = π n) → (∀ (n : ℕ) (x : A), (p : A) ∣ x ^ (p ^ n) → π n ∣ x) → ∃ pflat : PreTilt R p, PreTilt.untilt pflat = (p : R) ∧ ∀ c : PreTilt R p, PreTilt.coeff 0 c = 0 → pflat ∣ c := by
  atlas_forward_decl GlobalTheory.pflat_dvd_of_roots
end

section
section
open Ideal WittVector

namespace GlobalTheory

private lemma perfection_isUnit_of_coeff_zero {p : ℕ} [hp : Fact p.Prime] {R : Type*}
    [CommRing R] [CharP R p]
    (x : Perfection R p) (h : IsUnit (Perfection.coeff R p 0 x)) : IsUnit x := by
  have hn : ∀ n, IsUnit (Perfection.coeff R p n x) := fun n => by
    have e : Perfection.coeff R p n x ^ p ^ n = Perfection.coeff R p 0 x :=
      Perfection.coeffMonoidHom_pow_p_pow_self x n
    rw [← e] at h
    exact (isUnit_pow_iff (pow_ne_zero _ hp.out.ne_zero)).1 h
  let y : Perfection R p := ⟨fun n => ((hn n).unit⁻¹ : Rˣ), fun n => by
    have e : (hn (n + 1)).unit ^ p = (hn n).unit :=
      Units.ext (by simp [Perfection.coeff_pow_p' x n])
    rw [← Units.val_pow_eq_pow_val, inv_pow, e]⟩
  have hy : ∀ n, Perfection.coeff R p n x * Perfection.coeff R p n y = 1 := fun n => by
    rw [Perfection.coeff_mk]
    exact (hn n).mul_val_inv
  refine ⟨⟨x, y, ?_, ?_⟩, rfl⟩
  · ext n; rw [map_mul, hy, map_one]
  · ext n; rw [map_mul, mul_comm, hy, map_one]

private lemma untilt_sub_one_congr {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O] (x : PreTilt O p) :
    ∃ t : O, (x - 1).untilt = x.untilt - 1 + p * t := by
  have h : Ideal.Quotient.mk (span {(p : O)}) (x - 1).untilt =
      Ideal.Quotient.mk (span {(p : O)}) (x.untilt - 1) := by
    rw [PreTilt.mk_untilt_eq_coeff_zero, map_sub, map_sub, PreTilt.mk_untilt_eq_coeff_zero,
      map_one, map_one]
  obtain ⟨t, ht⟩ := mem_span_singleton'.1 (Ideal.Quotient.eq.1 h)
  exact ⟨t, by linear_combination -ht⟩

theorem preTilt_pow_sub_one_pow_dvd_of_associated (p : ℕ) [hp : Fact p.Prime] (R : Type)
    [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (Ideal.span {(p : R)}) R]
    (hreg : IsSMulRegular R (p : R)) (pflat f : PreTilt R p)
    (hpf : PreTilt.untilt pflat = (p : R))
    (hker : ∀ c : PreTilt R p, PreTilt.coeff 0 c = 0 → pflat ∣ c)
    (hass : Associated ((PreTilt.untilt f - 1) ^ (p * (p - 1))) (p : R))
    (c : PreTilt R p) (hc : PreTilt.coeff 0 c = 0) : (f ^ p - 1) ^ (p - 1) ∣ c := by
  obtain ⟨w, hw⟩ := hass
  obtain ⟨t, ht⟩ := untilt_sub_one_congr f
  set a : R := PreTilt.untilt f - 1 with ha
  have h2 := hp.out.two_le
  obtain ⟨M, hM⟩ : ∃ M, p * (p - 1) = M + 2 := by
    refine ⟨p * (p - 1) - 2, ?_⟩
    have : 2 * 1 ≤ p * (p - 1) := Nat.mul_le_mul h2 (by omega)
    omega
  have hpJ : (p : R) ∈ jacobson (⊥ : Ideal R) :=
    IsAdicComplete.le_jacobson_bot (span {(p : R)}) (mem_span_singleton_self _)
  have haJ : a ∈ jacobson (⊥ : Ideal R) := by
    refine Ideal.isRadical_jacobson ⊥ ⟨p * (p - 1), ?_⟩
    have : a ^ (p * (p - 1)) = (p : R) * ((w⁻¹ : Rˣ) : R) := by
      rw [← hw, mul_assoc, Units.mul_inv, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ hpJ
  have hu : IsUnit (a * (a ^ M * w * t) + 1) := mem_jacobson_bot.1 haJ _
  have h1 : (f - 1).untilt = a * (a * (a ^ M * w * t) + 1) := by
    rw [ht, ← hw, hM]; ring
  have hg : (f ^ p - 1) ^ (p - 1) = (f - 1) ^ (p * (p - 1)) := by
    rw [pow_mul, sub_pow_char (p := p) f 1, one_pow]
  have hu' : IsUnit (((w⁻¹ : Rˣ) : R) * (a * (a ^ M * w * t) + 1) ^ (p * (p - 1))) :=
    (Units.isUnit _).mul (hu.pow _)
  set u : R := ((w⁻¹ : Rˣ) : R) * (a * (a ^ M * w * t) + 1) ^ (p * (p - 1)) with hudef
  have hunt : ((f ^ p - 1) ^ (p - 1)).untilt = (p : R) * u := by
    rw [hg, PreTilt.untilt.map_pow, h1, mul_pow, hudef, ← hw, mul_assoc (a ^ (p * (p - 1))) (w : R),
      Units.mul_inv_cancel_left]
  have h0 : PreTilt.coeff 0 ((f ^ p - 1) ^ (p - 1)) = 0 := by
    rw [← PreTilt.mk_untilt_eq_coeff_zero, hunt]
    exact Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.mul_mem_right _ _ (mem_span_singleton_self _))
  obtain ⟨d, hd⟩ := hker _ h0
  have hdu : d.untilt = u := by
    apply hreg
    have := hunt
    rw [hd, map_mul, hpf] at this
    simpa [smul_eq_mul] using this
  have hdunit : IsUnit d := by
    apply perfection_isUnit_of_coeff_zero d
    have : IsUnit (PreTilt.coeff 0 d) := by
      rw [← PreTilt.mk_untilt_eq_coeff_zero, hdu]
      exact hu'.map _
    exact this
  rw [hd, hdunit.mul_right_dvd]
  exact hker c hc

end GlobalTheory
end

open Ideal WittVector
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_untilt_divides_pow : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (Ideal.span {(p : R)}) R], IsSMulRegular R (p : R) → ∀ (pflat f : PreTilt R p), PreTilt.untilt pflat = (p : R) → (∀ c : PreTilt R p, PreTilt.coeff 0 c = 0 → pflat ∣ c) → Associated ((PreTilt.untilt f - 1) ^ (p * (p - 1))) (p : R) → ∀ c : PreTilt R p, PreTilt.coeff 0 c = 0 → (f ^ p - 1) ^ (p - 1) ∣ c := by
  atlas_forward_decl GlobalTheory.preTilt_pow_sub_one_pow_dvd_of_associated
end

section
section
open Ideal WittVector

noncomputable section

namespace GlobalTheory

theorem mem_span_of_step_adic {A : Type*} [CommRing A] (q a : A)
    [IsAdicComplete (span {q}) A] (P : A → Prop)
    (h : ∀ x, P x → ∃ y x', x = a * y + q * x' ∧ P x') (x : A) (hx : P x) :
    x ∈ span {a} := by
  classical
  let g : {z // P z} → A × {z // P z} := fun z =>
    ((h z.1 z.2).choose, ⟨(h z.1 z.2).choose_spec.choose, (h z.1 z.2).choose_spec.choose_spec.2⟩)
  have hg : ∀ z : {z // P z}, z.1 = a * (g z).1 + q * (g z).2.1 := fun z =>
    (h z.1 z.2).choose_spec.choose_spec.1
  let xs : ℕ → {z // P z} := fun n => Nat.rec ⟨x, hx⟩ (fun _ z => (g z).2) n
  have hxs : ∀ n, xs (n + 1) = (g (xs n)).2 := fun n => rfl
  let S : ℕ → A := fun n => ∑ k ∈ Finset.range n, q ^ k * (g (xs k)).1
  have hS : ∀ n, S (n + 1) = S n + q ^ n * (g (xs n)).1 := fun n => Finset.sum_range_succ _ _
  have hY : ∀ n, x = a * S n + q ^ n * (xs n).1 := by
    intro n
    induction n with
    | zero => simp [S, xs]
    | succ n ih =>
      rw [hS, hxs]
      linear_combination ih + q ^ n * hg (xs n)
  have hC : ∀ m n, m ≤ n → S n - S m ∈ span {q ^ m} := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hS, show S n + q ^ n * (g (xs n)).1 - S m = (S n - S m) + q ^ n * (g (xs n)).1 by ring]
      refine add_mem ih (mem_span_singleton.2 (Dvd.dvd.mul_right (pow_dvd_pow q hmn) _))
  obtain ⟨L, hL⟩ := (inferInstance : IsPrecomplete (span {q}) A).prec' S (by
    intro m n hmn
    simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    rw [← neg_sub]
    exact neg_mem (hC m n hmn))
  have hxL : x - a * L = 0 := by
    refine (inferInstance : IsHausdorff (span {q}) A).haus' _ (fun n => ?_)
    have hn := hL n
    simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem] at hn ⊢
    rw [sub_zero, show x - a * L = a * (S n - L) + q ^ n * (xs n).1 by
      linear_combination hY n]
    exact add_mem (mul_mem_left _ _ hn) (mul_mem_right _ _ (mem_span_singleton_self _))
  exact mem_span_singleton'.2 ⟨L, by rw [mul_comm]; exact (sub_eq_zero.1 hxL).symm⟩

theorem ker_fontaineTheta_eq_span_of_dvd : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    [Fact ¬IsUnit (p : R)] [IsAdicComplete (Ideal.span {(p : R)}) R], IsSMulRegular R (p : R) →
    ∀ ξ : WittVector p (PreTilt R p), fontaineTheta R p ξ = 0 →
    (∀ c : PreTilt R p, PreTilt.coeff 0 c = 0 → WittVector.constantCoeff ξ ∣ c) →
    RingHom.ker (fontaineTheta R p) = Ideal.span {ξ} := by
  intro p _ R _ _ _ hreg ξ hθξ hdiv
  ext x
  constructor
  · intro hx
    rw [RingHom.mem_ker] at hx
    refine mem_span_of_step_adic (p : WittVector p (PreTilt R p)) ξ
      (fun x => fontaineTheta R p x = 0) ?_ x hx
    intro x hx
    have hc : PreTilt.coeff 0 (x.coeff 0) = 0 := by
      rw [← mk_fontaineTheta, hx, map_zero]
    obtain ⟨d, hd⟩ := hdiv _ hc
    have hm : x - ξ * teichmuller p d ∈ span {(p : WittVector p (PreTilt R p))} := by
      rw [← ker_constantCoeff, RingHom.mem_ker, map_sub, map_mul]
      change x.coeff 0 - constantCoeff ξ * (teichmuller p d).coeff 0 = 0
      rw [teichmuller_coeff_zero, ← hd, sub_self]
    obtain ⟨z, hz⟩ := mem_span_singleton'.1 hm
    refine ⟨teichmuller p d, z, by linear_combination -hz, ?_⟩
    apply hreg
    change (p : R) * fontaineTheta R p z = (p : R) * 0
    rw [mul_zero, ← map_natCast (fontaineTheta R p) p, ← map_mul, mul_comm, hz, map_sub, map_mul,
      hx, hθξ, zero_mul, sub_zero]
  · intro hx
    obtain ⟨a, rfl⟩ := mem_span_singleton'.1 hx
    rw [RingHom.mem_ker, map_mul, hθξ, mul_zero]

end GlobalTheory
end
end

open Ideal WittVector
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_fontaineTheta_eq_span_of_distinguished : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (Ideal.span {(p : R)}) R], IsSMulRegular R (p : R) → ∀ ξ : WittVector p (PreTilt R p), fontaineTheta R p ξ = 0 → (∀ c : PreTilt R p, PreTilt.coeff 0 c = 0 → WittVector.constantCoeff ξ ∣ c) → RingHom.ker (fontaineTheta R p) = Ideal.span {ξ} := by
  atlas_forward_decl GlobalTheory.ker_fontaineTheta_eq_span_of_dvd
end

section
section
open Ideal WittVector Polynomial

namespace GlobalTheory.Sandwich

theorem charP_sub_one_pow_pred_eq_geom_sum {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]
    (x : R) : (x - 1) ^ (p - 1) = ∑ i ∈ Finset.range p, x ^ i := by
  have key : ((X : (ZMod p)[X]) - 1) ^ (p - 1) = ∑ i ∈ Finset.range p, (X : (ZMod p)[X]) ^ i := by
    have h1 : ((X : (ZMod p)[X]) - 1) ^ p = (∑ i ∈ Finset.range p, (X : (ZMod p)[X]) ^ i) *
        ((X : (ZMod p)[X]) - 1) := by
      rw [geom_sum_mul, sub_pow_char, one_pow]
    have h2 : ((X : (ZMod p)[X]) - 1) ^ p = ((X : (ZMod p)[X]) - 1) ^ (p - 1) *
        ((X : (ZMod p)[X]) - 1) := by
      rw [← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le]
    have hne : ((X : (ZMod p)[X]) - 1) ≠ 0 := X_sub_C_ne_zero 1
    exact mul_right_cancel₀ hne (h2.symm.trans h1)
  have := congrArg (eval₂RingHom (ZMod.castHom (dvd_refl p) R) x) key
  simpa [map_sum, map_pow, map_sub] using this

theorem constantCoeff_xi : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p),
    WittVector.constantCoeff (GlobalTheory.Sandwich.xi ε) = (GlobalTheory.Sandwich.root ε - 1) ^ (p - 1) := by
  intro p _ O _ _ _ ε
  rw [charP_sub_one_pow_pred_eq_geom_sum, xi, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

end GlobalTheory.Sandwich
end

open Ideal WittVector
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCoeff_xi_eq_root_sub_one_pow : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p), WittVector.constantCoeff (GlobalTheory.Sandwich.xi ε) = (GlobalTheory.Sandwich.root ε - 1) ^ (p - 1) := by
  atlas_forward_decl GlobalTheory.Sandwich.constantCoeff_xi
end

section
set_option autoImplicit false

noncomputable section

open Ideal WittVector

namespace GlobalTheory.PerfdCompletion

theorem t_complete (p : ℕ) (A : Type) [CommRing A] :
    IsAdicComplete (span {(p : AdicCompletion (span {(p : A)}) A)})
      (AdicCompletion (span {(p : A)}) A) := by
  have h := AdicCompletion.isAdicComplete (R := A) (I := span {(p : A)}) (M := A)
    (Submodule.fg_span_singleton _)
  rw [← IsAdicComplete.map_algebraMap_iff (S := AdicCompletion (span {(p : A)}) A)] at h
  simpa [Ideal.map_span] using h

section Closed

theorem exists_pow_eq {A : Type} (K : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [IsAlgClosed K]
    [Algebra A K] [IsFractionRing A K] (x : A) {n : ℕ} (hn : 0 < n) : ∃ y : A, y ^ n = x := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A K x) hn
  have hi : IsIntegral A z := ⟨Polynomial.X ^ n - Polynomial.C x,
    Polynomial.monic_X_pow_sub_C x hn.ne', by simp [hz]⟩
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := K)).1 hi
  exact ⟨y, IsFractionRing.injective A K (by rw [map_pow, hy, hz])⟩

theorem dvd_of_dvd_pow {A : Type} (K : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K]
    [Algebra A K] [IsFractionRing A K] {a π x : A} {m : ℕ} (hm : 0 < m) (hπ : π ^ m = a) (h0 : π ≠ 0)
    (h : a ∣ x ^ m) : π ∣ x := by
  obtain ⟨b, hb⟩ := h
  have hπK : algebraMap A K π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 h0
  set z := algebraMap A K x / algebraMap A K π
  have hz : z ^ m = algebraMap A K b := by
    have ha : algebraMap A K a ≠ 0 := by rw [← hπ, map_pow]; exact pow_ne_zero _ hπK
    rw [div_pow, div_eq_iff (pow_ne_zero _ hπK), ← map_pow, ← map_pow, hπ, hb, map_mul, mul_comm]
  have hi : IsIntegral A z := ⟨Polynomial.X ^ m - Polynomial.C b,
    Polynomial.monic_X_pow_sub_C b hm.ne', by simp [hz]⟩
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := K)).1 hi
  refine ⟨y, IsFractionRing.injective A K ?_⟩
  rw [map_mul, hy, mul_div_cancel₀ _ hπK]

end Closed

theorem exists_cycPerfd : ∀ (p : ℕ) [Fact p.Prime] (A K : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [IsAlgClosed K] [CharZero K] [Algebra A K] [IsFractionRing A K], ¬ IsUnit (p : A) → ∀ ζ : ℕ → A, (∀ n, IsPrimitiveRoot (ζ n) (p ^ n)) → (∀ n, ζ (n + 1) ^ p = ζ n) → ∃ (S : GlobalTheory.Published.CycPerfd p) (e : AdicCompletion (Ideal.span {(p : A)}) A ≃+* S.R), ∀ n, GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.zeta S.ε n = e (algebraMap A _ (ζ n)) := by
  intro p _ A K _ _ _ _ _ _ _ _ hpA ζ hζ hζs
  have hp0 : (p : A) ≠ 0 := by
    intro h
    have h' := congrArg (algebraMap A K) h
    rw [map_natCast, map_zero, Nat.cast_eq_zero] at h'
    exact (Fact.out : p.Prime).ne_zero h'
  have hreg : IsSMulRegular A (p : A) := fun x y h => mul_left_cancel₀ hp0 h
  obtain ⟨hsurj, hker⟩ := GlobalTheory.T.adic_completion_quotient_ker_eq p A hreg
  set R := AdicCompletion (span {(p : A)}) A
  set φ := (Ideal.Quotient.mk (span {(p : R)})).comp (algebraMap A R) with hφ
  have hnu : ¬IsUnit (p : R) := by
    intro h
    have h1 : IsUnit (Ideal.Quotient.mk (span {(p : R)}) (p : R)) := h.map _
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (mem_span_singleton_self _), isUnit_zero_iff] at h1
    have h2 : (1 : A) ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, map_one]; exact h1.symm
    rw [hker, mem_span_singleton] at h2
    exact hpA (isUnit_of_dvd_one h2)
  haveI : Fact ¬IsUnit (p : R) := ⟨hnu⟩
  haveI : IsAdicComplete (span {(p : R)}) R := t_complete p A
  set z : ℕ → R := fun n => algebraMap A R (ζ n) with hzdef
  have hz : ∀ n, z (n + 1) ^ p = z n := fun n => by simp only [hzdef, ← map_pow, hζs]
  set ε : PreTilt R p := ReciprocityTheory.PGsh.ofRoots z hz with hεdef
  have hroot : (GlobalTheory.Sandwich.root : PreTilt R p → PreTilt R p) =
      ⇑(_root_.frobeniusEquiv (PreTilt R p) p).symm := rfl
  have hzeta : ∀ n, GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.zeta ε n = z n := by
    intro n
    have := ReciprocityTheory.PGsh.untilt_eq_of_coeff (GlobalTheory.Sandwich.root^[n] ε) (fun k => z (n + k))
      (fun k => hz (n + k)) (fun k => by
        rw [hroot, ← PreTilt.coeff_def, PreTilt.coeff_iterate_frobeniusEquiv_symm, PreTilt.coeff_def,
          ReciprocityTheory.PGsh.coeff_ofRoots, add_comm])
    simpa [GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.zeta] using this
  have hzeta0 : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.zeta ε 0 = 1 := by
    rw [hzeta 0, hzdef]
    have h1 : ζ 0 = 1 := by simpa using (hζ 0)
    simp [h1]
  have hfrob : Function.Surjective (_root_.frobenius (ModP R p) p) := by
    intro c
    obtain ⟨x, rfl⟩ := hsurj c
    obtain ⟨y, hy⟩ := exists_pow_eq K x (Fact.out : p.Prime).pos
    exact ⟨φ y, by rw [frobenius_def, ← map_pow, hy]⟩

  have hroots : ∀ x : A, ∃ y : A, y ^ p = x := fun x => exists_pow_eq K x (Fact.out : p.Prime).pos
  choose r hr using hroots
  let π : ℕ → A := fun n => Nat.rec (p : A) (fun _ y => r y) n
  have hπs : ∀ n, π (n + 1) ^ p = π n := fun n => hr _
  have hπpow : ∀ n, π n ^ (p ^ n) = p := by
    intro n
    induction n with
    | zero => simp [π]
    | succ n ih => rw [pow_succ', pow_mul, hπs, ih]
  have hπ0 : ∀ n, π n ≠ 0 := fun n h => hp0 (by rw [← hπpow n, h, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)])
  have hdiv : ∀ (n : ℕ) (x : A), (p : A) ∣ x ^ (p ^ n) → π n ∣ x := fun n x h =>
    dvd_of_dvd_pow K (pow_pos (Fact.out : p.Prime).pos n) (hπpow n) (hπ0 n) h
  obtain ⟨pflat, hpf, hpdiv⟩ := GlobalTheory.T.perfectoid_tower_surjective p A R (algebraMap A R) hp0 hsurj hker π rfl hπs hdiv
  have hregR := GlobalTheory.T.isSMulRegular_adicCompletion p A hreg

  set f : PreTilt R p := (_root_.frobeniusEquiv (PreTilt R p) p).symm (GlobalTheory.Sandwich.root ε) with hf
  have hfp : f ^ p = GlobalTheory.Sandwich.root ε := frobeniusEquiv_symm_pow_p (PreTilt R p) p _
  have hfu : PreTilt.untilt f = z 2 := by
    rw [← hzeta 2]
    simp [GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.zeta, hf, hroot]
  have hass : Associated ((PreTilt.untilt f - 1) ^ (p * (p - 1))) (p : R) := by
    have h := GlobalTheory.associated_primitiveRoot_sub_one_pow_totient_prime_pow (k := 1)
      (Fact.out : p.Prime) (hζ 2)
    rw [Nat.totient_prime_pow_succ (Fact.out : p.Prime), pow_one] at h
    have h2 := h.map (algebraMap A R)
    rw [map_pow, map_sub, map_one, map_natCast] at h2
    rw [hfu]; exact h2
  have hdivξ : ∀ c : PreTilt R p, PreTilt.coeff 0 c = 0 → WittVector.constantCoeff (GlobalTheory.Sandwich.xi ε) ∣ c := by
    intro c hc
    rw [GlobalTheory.T.constantCoeff_xi_eq_root_sub_one_pow, ← hfp]
    exact GlobalTheory.T.tilt_untilt_divides_pow p R hregR pflat f hpf hpdiv hass c hc
  have hθξ : fontaineTheta R p (GlobalTheory.Sandwich.xi ε) = 0 := by
    have h1 : PreTilt.untilt (GlobalTheory.Sandwich.root ε) = z 1 := by
      rw [← hzeta 1]; rfl
    rw [GlobalTheory.Sandwich.xi, map_sum]
    simp only [map_pow, fontaineTheta_teichmuller, h1]
    have h2 : ∑ i ∈ Finset.range p, z 1 ^ i = algebraMap A R (∑ i ∈ Finset.range p, ζ 1 ^ i) := by
      simp [hzdef]
    have h3 : ∑ i ∈ Finset.range p, ζ 1 ^ i = 0 := by
      have := (hζ 1).geom_sum_eq_zero (by simpa using (Fact.out : p.Prime).one_lt)
      simpa using this
    rw [h2, h3, map_zero]
  refine ⟨⟨R, hregR, ε, hzeta0, surjective_fontaineTheta hfrob,
    GlobalTheory.T.ker_fontaineTheta_eq_span_of_distinguished p R hregR _ hθξ hdivξ⟩, RingEquiv.refl _, fun n => ?_⟩
  exact hzeta n

end GlobalTheory.PerfdCompletion
end
end
