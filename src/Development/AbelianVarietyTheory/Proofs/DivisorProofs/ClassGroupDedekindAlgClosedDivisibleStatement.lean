import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffHasse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapQuotBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowLeSpanPowSup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Target
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalBoundedIn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NewtonPowerSeriesSurjectiveLinearizationSolution
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesTaylorSubstFirstOrder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNeZeroForallPointExtendSubalgebra
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FieldNormSurjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TsenLangRatFunc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FiniteExtensionLang
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparableNormalisationReducedFibresStatement

section
open Polynomial

namespace GlobalTheory.CurveCompletionG

theorem residue_exists (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (Q : Ideal A) (hQ : Q.IsMaximal) (c : A) :
    ∃ a : k, c - algebraMap k A a ∈ Q := by
  letI := Ideal.Quotient.field Q
  haveI : Module.Finite k (A ⧸ Q) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ Q)
  obtain ⟨a, ha⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := A ⧸ Q)).2
    (Ideal.Quotient.mk Q c)
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← ha]
  simp [Ideal.Quotient.algebraMap_eq]

section Dedekind
variable {A : Type} [CommRing A] [IsDedekindDomain A]

theorem pow_le_span_sup {Q : Ideal A} [Q.IsPrime] (hQ : Q ≠ ⊥) {π : A} (hπ : π ∈ Q)
    (hπ2 : π ∉ Q ^ 2) : ∀ m : ℕ, Q ^ m ≤ Ideal.span {π ^ m} ⊔ Q ^ (m + 1) := by
  first
  | exact @_root_.GlobalTheory.SpanPowerSupremum.pow_le_span_pow_sup
  | exact _root_.GlobalTheory.SpanPowerSupremum.pow_le_span_pow_sup
  | (apply _root_.GlobalTheory.SpanPowerSupremum.pow_le_span_pow_sup <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpanPowerSupremum.pow_le_span_pow_sup <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpanPowerSupremum.pow_le_span_pow_sup <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpanPowerSupremum.pow_le_span_pow_sup ..)

theorem pow_not_mem {Q : Ideal A} [Q.IsPrime] (hQ : Q ≠ ⊥) {π : A} (hπ : π ∈ Q)
    (hπ2 : π ∉ Q ^ 2) (m : ℕ) : π ^ m ∉ Q ^ (m + 1) := by
  first
  | exact @_root_.GlobalTheory.AlgebraicIntegerNormBound.main
  | exact _root_.GlobalTheory.AlgebraicIntegerNormBound.main
  | (apply _root_.GlobalTheory.AlgebraicIntegerNormBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AlgebraicIntegerNormBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AlgebraicIntegerNormBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AlgebraicIntegerNormBound.main ..)

end Dedekind

section Series
variable {k A : Type} [Field k] [CommRing A] [Algebra k A] (Q : Ideal A) (π : A)

theorem aeval_mem_of_dvd (hπ : π ∈ Q) (m : ℕ) (r : k[X]) (h : X ^ m ∣ r) :
    aeval π r ∈ Q ^ m := by
  obtain ⟨s, rfl⟩ := h
  rw [map_mul, map_pow, aeval_X]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hπ m)

theorem dvd_of_aeval_mem (hπ : π ∈ Q) (hnot : ∀ m : ℕ, π ^ m ∉ Q ^ (m + 1)) :
    ∀ (m : ℕ) (r : k[X]), aeval π r ∈ Q ^ m → X ^ m ∣ r := by
  intro m
  induction m with
  | zero => intro r _; simp
  | succ m ih =>
    intro r hr
    obtain ⟨s, rfl⟩ := ih r (Ideal.pow_le_pow_right (Nat.le_succ m) hr)
    obtain ⟨s', hs'⟩ := Polynomial.X_dvd_sub_C (p := s)
    have hs : s = C (s.coeff 0) + X * s' := by rw [← hs']; ring
    by_cases h0 : s.coeff 0 = 0
    · rw [hs, h0, map_zero, zero_add, ← mul_assoc, ← pow_succ]
      exact dvd_mul_right _ _
    · exfalso
      apply hnot m
      have e0 : aeval π s = algebraMap k A (s.coeff 0) + π * aeval π s' := by
        conv_lhs => rw [hs]
        simp [aeval_C]
      have e : aeval π (X ^ m * s) =
          π ^ m * algebraMap k A (s.coeff 0) + π ^ (m + 1) * aeval π s' := by
        rw [map_mul, map_pow, aeval_X, e0]; ring
      rw [e] at hr
      have h2 : π ^ m * algebraMap k A (s.coeff 0) ∈ Q ^ (m + 1) := by
        have h3 : π ^ (m + 1) * aeval π s' ∈ Q ^ (m + 1) :=
          Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hπ _)
        have := Ideal.sub_mem _ hr h3
        simpa using this
      have h4 := Ideal.mul_mem_right (algebraMap k A (s.coeff 0)⁻¹) _ h2
      rwa [mul_assoc, ← map_mul, mul_inv_cancel₀ h0, map_one, mul_one] at h4

theorem aeval_mem_iff (hπ : π ∈ Q) (hnot : ∀ m : ℕ, π ^ m ∉ Q ^ (m + 1)) (m : ℕ) (r : k[X]) :
    aeval π r ∈ Q ^ m ↔ X ^ m ∣ r :=
  ⟨dvd_of_aeval_mem Q π hπ hnot m r, aeval_mem_of_dvd Q π hπ m r⟩

theorem coe_dvd_iff (m : ℕ) (r : k[X]) :
    (PowerSeries.X : PowerSeries k) ^ m ∣ (r : PowerSeries k) ↔ X ^ m ∣ r := by
  rw [PowerSeries.X_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
  simp [Polynomial.coeff_coe]

theorem eq_of_forall_dvd (f g : PowerSeries k)
    (h : ∀ m : ℕ, (PowerSeries.X : PowerSeries k) ^ m ∣ f - g) : f = g := by
  ext n
  have := PowerSeries.X_pow_dvd_iff.mp (h (n + 1)) n (Nat.lt_succ_self n)
  rw [map_sub, sub_eq_zero] at this
  exact this

end Series

section Construction
variable {k A : Type} [Field k] [CommRing A] [Algebra k A] (Q : Ideal A) (π : A)
  (hex : ∀ (m : ℕ) (u : A), ∃ p : k[X], u - aeval π p ∈ Q ^ m)

noncomputable def approx (m : ℕ) (u : A) : k[X] := Classical.choose (hex m u)

theorem approx_spec (m : ℕ) (u : A) : u - aeval π (approx Q π hex m u) ∈ Q ^ m :=
  Classical.choose_spec (hex m u)

noncomputable def ser (u : A) : PowerSeries k :=
  PowerSeries.mk fun n => (approx Q π hex (n + 1) u).coeff n

variable {Q π} (hπ : π ∈ Q) (hnot : ∀ m : ℕ, π ^ m ∉ Q ^ (m + 1))
include hπ hnot

theorem ser_sub_approx (m : ℕ) (u : A) :
    (PowerSeries.X : PowerSeries k) ^ m ∣ ser Q π hex u - (approx Q π hex m u : PowerSeries k) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro n hn
  rw [map_sub, Polynomial.coeff_coe, ser, PowerSeries.coeff_mk, sub_eq_zero]
  have hmem : aeval π (approx Q π hex m u - approx Q π hex (n + 1) u) ∈ Q ^ (n + 1) := by
    have e : aeval π (approx Q π hex m u - approx Q π hex (n + 1) u) =
        (u - aeval π (approx Q π hex (n + 1) u)) - (u - aeval π (approx Q π hex m u)) := by
      rw [map_sub]; ring
    rw [e]
    exact Ideal.sub_mem _ (approx_spec Q π hex _ u)
      (Ideal.pow_le_pow_right hn (approx_spec Q π hex m u))
  have hd := (Polynomial.X_pow_dvd_iff).mp (dvd_of_aeval_mem Q π hπ hnot _ _ hmem) n
    (Nat.lt_succ_self n)
  rw [Polynomial.coeff_sub, sub_eq_zero] at hd
  exact hd.symm

theorem mem_iff_dvd (m : ℕ) (u : A) (p : k[X]) :
    u - aeval π p ∈ Q ^ m ↔
      (PowerSeries.X : PowerSeries k) ^ m ∣ ser Q π hex u - (p : PowerSeries k) := by
  set q := approx Q π hex m u
  have e1 : u - aeval π p = (u - aeval π q) + aeval π (q - p) := by rw [map_sub]; ring
  have e2 : ser Q π hex u - (p : PowerSeries k) =
      (ser Q π hex u - (q : PowerSeries k)) + ((q - p : k[X]) : PowerSeries k) := by
    rw [Polynomial.coe_sub]; ring
  rw [e1, Ideal.add_mem_iff_right _ (approx_spec Q π hex m u), e2,
    (dvd_add_right (ser_sub_approx hex hπ hnot m u)), coe_dvd_iff,
    aeval_mem_iff Q π hπ hnot]

theorem ser_eq (u : A) (f : PowerSeries k)
    (h : ∀ m : ℕ, ∃ p : k[X], u - aeval π p ∈ Q ^ m ∧
      (PowerSeries.X : PowerSeries k) ^ m ∣ f - (p : PowerSeries k)) :
    ser Q π hex u = f := by
  apply eq_of_forall_dvd
  intro m
  obtain ⟨p, hp, hd⟩ := h m
  have := dvd_sub ((mem_iff_dvd hex hπ hnot m u p).mp hp) hd
  rwa [sub_sub_sub_cancel_right] at this

noncomputable def serHom : A →ₐ[k] PowerSeries k where
  toFun := ser Q π hex
  map_one' := ser_eq hex hπ hnot 1 1 fun m => ⟨1, by simp, by simp⟩
  map_zero' := ser_eq hex hπ hnot 0 0 fun m => ⟨0, by simp, by simp⟩
  map_add' u v := by
    apply ser_eq hex hπ hnot
    intro m
    refine ⟨approx Q π hex m u + approx Q π hex m v, ?_, ?_⟩
    · have e : u + v - aeval π (approx Q π hex m u + approx Q π hex m v) =
          (u - aeval π (approx Q π hex m u)) + (v - aeval π (approx Q π hex m v)) := by
        rw [map_add]; ring
      rw [e]
      exact Ideal.add_mem _ (approx_spec Q π hex m u) (approx_spec Q π hex m v)
    · have e : ser Q π hex u + ser Q π hex v -
          ((approx Q π hex m u + approx Q π hex m v : k[X]) : PowerSeries k) =
          (ser Q π hex u - (approx Q π hex m u : PowerSeries k)) +
            (ser Q π hex v - (approx Q π hex m v : PowerSeries k)) := by
        rw [Polynomial.coe_add]; ring
      rw [e]
      exact dvd_add (ser_sub_approx hex hπ hnot m u) (ser_sub_approx hex hπ hnot m v)
  map_mul' u v := by
    apply ser_eq hex hπ hnot
    intro m
    refine ⟨approx Q π hex m u * approx Q π hex m v, ?_, ?_⟩
    · have e : u * v - aeval π (approx Q π hex m u * approx Q π hex m v) =
          (u - aeval π (approx Q π hex m u)) * v +
            aeval π (approx Q π hex m u) * (v - aeval π (approx Q π hex m v)) := by
        rw [map_mul]; ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (approx_spec Q π hex m u))
        (Ideal.mul_mem_left _ _ (approx_spec Q π hex m v))
    · have e : ser Q π hex u * ser Q π hex v -
          ((approx Q π hex m u * approx Q π hex m v : k[X]) : PowerSeries k) =
          (ser Q π hex u - (approx Q π hex m u : PowerSeries k)) * ser Q π hex v +
            (approx Q π hex m u : PowerSeries k) *
              (ser Q π hex v - (approx Q π hex m v : PowerSeries k)) := by
        rw [Polynomial.coe_mul]; ring
      rw [e]
      exact dvd_add (Dvd.dvd.mul_right (ser_sub_approx hex hπ hnot m u) _)
        (Dvd.dvd.mul_left (ser_sub_approx hex hπ hnot m v) _)
  commutes' c := by
    apply ser_eq hex hπ hnot
    intro m
    exact ⟨C c, by simp, by simp⟩

end Construction

section Existence
variable {k A : Type} [Field k] [CommRing A] [Algebra k A] {Q : Ideal A} {π : A}

theorem exists_approx (hπ : π ∈ Q) (hres : ∀ c : A, ∃ a : k, c - algebraMap k A a ∈ Q)
    (hsup : ∀ m : ℕ, Q ^ m ≤ Ideal.span {π ^ m} ⊔ Q ^ (m + 1)) :
    ∀ (m : ℕ) (u : A), ∃ p : k[X], u - aeval π p ∈ Q ^ m := by
  first
  | exact @_root_.GlobalTheory.IntegralNormBound.target
  | exact _root_.GlobalTheory.IntegralNormBound.target
  | (apply _root_.GlobalTheory.IntegralNormBound.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralNormBound.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralNormBound.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralNormBound.target ..)

end Existence

theorem exists_completion_embedding : ∀ (k A : Type) [Field k] [IsAlgClosed k]
    [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (Q : Ideal A),
    Q.IsMaximal → Q ≠ ⊥ → ∃ (σ : A →ₐ[k] PowerSeries k) (π : A), σ π = PowerSeries.X ∧
      Function.Injective σ ∧
      (∀ (m : ℕ) (u : A), u ∈ Q ^ m ↔ (PowerSeries.X : PowerSeries k) ^ m ∣ σ u) ∧
      ∀ (m : ℕ) (φ : PowerSeries k), ∃ u : A,
        (PowerSeries.X : PowerSeries k) ^ m ∣ φ - σ u := by
  intro k A _ _ _ _ _ _ Q hQ hQ0
  haveI : Q.IsPrime := hQ.isPrime
  obtain ⟨π, hπ1, hπ2⟩ := SetLike.exists_of_lt (Ideal.pow_succ_lt_pow hQ0 1)
  have hπ : π ∈ Q := by simpa using hπ1
  have hnot := pow_not_mem hQ0 hπ hπ2
  have hex := exists_approx (k := k) hπ (residue_exists k A Q hQ) (pow_le_span_sup hQ0 hπ hπ2)
  have hmem : ∀ (m : ℕ) (u : A),
      u ∈ Q ^ m ↔ (PowerSeries.X : PowerSeries k) ^ m ∣ serHom hex hπ hnot u := by
    intro m u
    have := mem_iff_dvd hex hπ hnot m u 0
    change u ∈ Q ^ m ↔ (PowerSeries.X : PowerSeries k) ^ m ∣ ser Q π hex u
    simpa using this
  refine ⟨serHom hex hπ hnot, π, ?_, ?_, hmem, ?_⟩
  · exact ser_eq hex hπ hnot π PowerSeries.X fun m => ⟨X, by simp, by simp⟩
  · rw [injective_iff_map_eq_zero]
    intro u hu
    have hall : ∀ m : ℕ, u ∈ Q ^ m := fun m => (hmem m u).mpr (by rw [hu]; exact dvd_zero _)
    have hbot := Ideal.iInf_pow_eq_bot_of_isDomain Q hQ.ne_top
    have : u ∈ ⨅ i, Q ^ i := Submodule.mem_iInf _ |>.mpr hall
    rw [hbot] at this
    exact (Submodule.mem_bot A).mp this
  · intro m φ
    refine ⟨aeval π (PowerSeries.trunc m φ), ?_⟩
    have h1 := (mem_iff_dvd hex hπ hnot m (aeval π (PowerSeries.trunc m φ))
      (PowerSeries.trunc m φ)).mp (by simp)
    have h2 : (PowerSeries.X : PowerSeries k) ^ m ∣ φ - (PowerSeries.trunc m φ : PowerSeries k) := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro n hn
      rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hn, sub_self]
    have := dvd_sub h2 h1
    rwa [sub_sub_sub_cancel_right] at this

end GlobalTheory.CurveCompletionG
end

section
open Polynomial

namespace GlobalTheory.PicDiv

theorem degree_count_generates : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (I : Type) [Fintype I] (D P₀ P : Ideal A) (Q Q' : I → Ideal A) (f₀ f : A), P₀.IsMaximal → P.IsMaximal → (∀ i, (Q i).IsMaximal) → (∀ i, (Q' i).IsMaximal) → Function.Injective Q' → (∀ i, Q' i ≠ P) → (∀ i, ¬ D ≤ Q' i) → ¬ D ≤ P →
 f₀ ≠ 0 → f ≠ 0 → Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N → f ∈ D → f ∈ P → (∀ i, f ∈ Q' i ^ N) → Module.finrank k (A ⧸ Ideal.span {f}) ≤ Module.finrank k (A ⧸ Ideal.span {f₀}) →
 Ideal.span {f} = P * D * ∏ i, Q' i ^ N := by
  intro k A _ _ _ _ _ _ N I _ D P₀ P Q Q' f₀ f hP₀ hP hQ hQ' hinj hQ'P hDQ' hDP hf₀ hf hspan hfD hfP hfQ' hdeg
  obtain ⟨_hfin, hmax, hmul, hle⟩ := GlobalTheory.DedekindCodimG.dedekind_finiteType_codim k A
  have hPne : P ≠ ⊥ := by
    intro h; apply hf; rw [h] at hfP; simpa using hfP
  have hmaxne : ∀ M : Ideal A, M.IsMaximal → M ≠ ⊥ := by
    intro M hM h
    subst h
    exact hPne (hM.eq_of_le hP.ne_top bot_le).symm
  have hDne : D ≠ ⊥ := by
    intro h; exact hDP (h ▸ bot_le)
  have hprodne : ∀ (s : Finset I) (g : I → Ideal A), (∀ i, g i ≠ ⊥) → (∏ i ∈ s, g i) ≠ ⊥ := by
    intro s g hg
    rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    intro i _; rw [Ideal.zero_eq_bot]; exact hg i
  have hpowne : ∀ (M : Ideal A) (n : ℕ), M ≠ ⊥ → M ^ n ≠ ⊥ := by
    intro M n hM
    rw [← Ideal.zero_eq_bot] at hM ⊢
    exact pow_ne_zero n hM
  have hmulne : ∀ (M M' : Ideal A), M ≠ ⊥ → M' ≠ ⊥ → M * M' ≠ ⊥ := by
    intro M M' hM hM'
    rw [← Ideal.zero_eq_bot] at hM hM' ⊢
    exact mul_ne_zero hM hM'
  have htop : Module.finrank k (A ⧸ (⊤ : Ideal A)) = 0 := by
    haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Module.finrank_zero_of_subsingleton
  have hpow : ∀ (M : Ideal A) (n : ℕ), M.IsMaximal → Module.finrank k (A ⧸ M ^ n) = n := by
    intro M n hM
    induction n with
    | zero => rw [pow_zero, Ideal.one_eq_top, htop]
    | succ n ih =>
      rw [pow_succ, hmul _ _ (hpowne M n (hmaxne M hM)) (hmaxne M hM), ih, (hmax M hM).1]
  have hprod : ∀ (s : Finset I) (g : I → Ideal A), (∀ i, g i ≠ ⊥) →
      Module.finrank k (A ⧸ ∏ i ∈ s, g i) = ∑ i ∈ s, Module.finrank k (A ⧸ g i) := by
    intro s g hg
    classical
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty, Ideal.one_eq_top, htop]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, hmul _ _ (hg a) (hprodne s g hg), ih]
  have hPowProd : ∀ (R : I → Ideal A), (∀ i, (R i).IsMaximal) →
      Module.finrank k (A ⧸ ∏ i, R i ^ N) = N * Fintype.card I := by
    intro R hR
    rw [hprod _ _ (fun i => hpowne _ _ (hmaxne _ (hR i)))]
    simp only [hpow _ _ (hR _), Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  have hPowNe : ∀ (R : I → Ideal A), (∀ i, (R i).IsMaximal) → (∏ i, R i ^ N) ≠ ⊥ :=
    fun R hR => hprodne _ _ (fun i => hpowne _ _ (hmaxne _ (hR i)))
  have h0 : Module.finrank k (A ⧸ Ideal.span {f₀}) =
      1 + Module.finrank k (A ⧸ D) + N * Fintype.card I := by
    rw [hspan, hmul _ _ (hmulne _ _ (hmaxne _ hP₀) hDne) (hPowNe Q hQ),
      hmul _ _ (hmaxne _ hP₀) hDne, (hmax _ hP₀).1, hPowProd Q hQ]
  have hcop_max : ∀ M M' : Ideal A, M.IsMaximal → M'.IsMaximal → M ≠ M' → IsCoprime M M' := by
    intro M M' hM hM' hne
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    have h1 := hM.eq_of_le h le_sup_left
    have h2 := hM'.eq_of_le h le_sup_right
    exact hne (h1.trans h2.symm)
  have hcopD : ∀ M : Ideal A, M.IsMaximal → ¬ D ≤ M → IsCoprime M D := by
    intro M hM hDM
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    exact hDM (le_sup_right.trans (hM.eq_of_le h le_sup_left).ge)
  have hdvd : ∀ M : Ideal A, f ∈ M → M ∣ Ideal.span {f} := fun M hM =>
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hM)
  have hX : (∏ i, Q' i ^ N) ∣ Ideal.span {f} := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact (hcop_max _ _ (hQ' i) (hQ' j) (hinj.ne hij)).pow
    · intro i _; exact hdvd _ (hfQ' i)
  have hPD : P * D ∣ Ideal.span {f} := (hcopD P hP hDP).mul_dvd (hdvd _ hfP) (hdvd _ hfD)
  have hPDX : IsCoprime (P * D) (∏ i, Q' i ^ N) :=
    IsCoprime.mul_left
      (IsCoprime.prod_right fun i _ => (hcop_max P (Q' i) hP (hQ' i) (hQ'P i).symm).pow_right)
      (IsCoprime.prod_right fun i _ => (hcopD (Q' i) (hQ' i) (hDQ' i)).symm.pow_right)
  have hJ : P * D * ∏ i, Q' i ^ N ∣ Ideal.span {f} := hPDX.mul_dvd hPD hX
  apply hle _ _ _ (Ideal.le_of_dvd hJ)
  · rw [hmul _ _ (hmulne _ _ hPne hDne) (hPowNe Q' hQ'), hmul _ _ hPne hDne, (hmax _ hP).1,
      hPowProd Q' hQ']
    rw [h0] at hdeg; exact hdeg
  · rw [Ne, Ideal.span_singleton_eq_bot]; exact hf

end GlobalTheory.PicDiv
end

section
open Polynomial

namespace GlobalTheory.PicDiv

theorem classGroup_nthPower_of_codim_one_mod : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ), 1 ≤ N → (∀ P₀ : Ideal A, P₀.IsMaximal → ∀ h₀ : P₀ ∈ nonZeroDivisors (Ideal A), ∃ a : A, a ≠ 0 ∧ ∀ P : Ideal A, P.IsMaximal → a ∉ P → ∀ h : P ∈ nonZeroDivisors (Ideal A), ∃ d : ClassGroup A, ClassGroup.mk0 ⟨P, h⟩ = ClassGroup.mk0 ⟨P₀, h₀⟩ * d ^ N) → (∃ f : A, f ≠ 0 ∧ Module.finrank k (A ⧸ Ideal.span {f}) % N = 1 % N) → ∀ c : ClassGroup A, ∃ d, c = d ^ N := by
  intro k A _ _ _ _ _ _ N _hN hyp hf c
  obtain ⟨f, hf0, hfm⟩ := hf
  obtain ⟨_hfin, hmax, hadd, _hle⟩ := GlobalTheory.DedekindCodimG.dedekind_finiteType_codim k A
  have nz : ∀ I : Ideal A, I ≠ ⊥ → I ∈ nonZeroDivisors (Ideal A) := fun I hI =>
    mem_nonZeroDivisors_of_ne_zero hI
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  have hI0 : (I : Ideal A) ≠ ⊥ := nonZeroDivisors.coe_ne_zero I
  by_cases hex : ∃ P₀ : Ideal A, P₀.IsMaximal ∧ P₀ ≠ ⊥
  swap
  · push_neg at hex
    have htop : (I : Ideal A) = ⊤ := by
      by_contra h
      obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ h
      exact hI0 (le_bot_iff.mp (hex M hM ▸ hIM))
    refine ⟨1, ?_⟩
    have : I = 1 := Subtype.ext (by rw [htop]; exact Ideal.one_eq_top.symm)
    rw [this, map_one, one_pow]
  obtain ⟨P₀, hP₀, hP₀ne⟩ := hex
  let H : Subgroup (ClassGroup A) := (powMonoidHom N : ClassGroup A →* ClassGroup A).range
  let π : ClassGroup A →* ClassGroup A ⧸ H := QuotientGroup.mk' H
  have hπ : ∀ d : ClassGroup A, π (d ^ N) = 1 := fun d =>
    (QuotientGroup.eq_one_iff _).mpr ⟨d, rfl⟩
  let γ : ClassGroup A := ClassGroup.mk0 ⟨P₀, nz P₀ hP₀ne⟩
  have hbot : ¬ (⊥ : Ideal A).IsMaximal := fun h =>
    hP₀ne (h.eq_of_le hP₀.ne_top bot_le).symm
  have hjac : ∀ x : A, x ≠ 0 → ∃ Q : Ideal A, Q.IsMaximal ∧ x ∉ Q := by
    intro x hx
    haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
    have hj : (⊥ : Ideal A).jacobson = ⊥ :=
      IsJacobsonRing.out' _ (Ideal.isPrime_bot).isRadical
    by_contra hne
    push_neg at hne
    apply hx
    have : x ∈ (⊥ : Ideal A).jacobson := by
      rw [Ideal.jacobson]
      exact Submodule.mem_sInf.mpr fun J hJ => hne J hJ.2
    rw [hj] at this
    exact (Submodule.mem_bot A).mp this
  have hmaxcls : ∀ (P : Ideal A) (hP : P.IsMaximal) (hPne : P ≠ ⊥),
      π (ClassGroup.mk0 ⟨P, nz P hPne⟩) = π γ := by
    intro P hP hPne
    obtain ⟨a₀, ha₀, H0⟩ := hyp P₀ hP₀ (nz P₀ hP₀ne)
    obtain ⟨a₁, ha₁, H1⟩ := hyp P hP (nz P hPne)
    obtain ⟨Q, hQ, hQa⟩ := hjac (a₀ * a₁) (mul_ne_zero ha₀ ha₁)
    have hQne : Q ≠ ⊥ := by rintro rfl; exact hbot hQ
    obtain ⟨d, hd⟩ := H0 Q hQ (fun h => hQa (Q.mul_mem_right _ h)) (nz Q hQne)
    obtain ⟨e, he⟩ := H1 Q hQ (fun h => hQa (Q.mul_mem_left _ h)) (nz Q hQne)
    have h1 := congrArg π hd
    have h2 := congrArg π he
    rw [map_mul, hπ, mul_one] at h1 h2
    rw [← h2, h1]
  have hall : ∀ J : Ideal A, ∀ hJ : J ∈ nonZeroDivisors (Ideal A),
      π (ClassGroup.mk0 ⟨J, hJ⟩) = π γ ^ Module.finrank k (A ⧸ J) := by
    intro J
    refine UniqueFactorizationMonoid.induction_on_prime (P := fun J : Ideal A => ∀ hJ : J ∈ nonZeroDivisors (Ideal A),
      π (ClassGroup.mk0 ⟨J, hJ⟩) = π γ ^ Module.finrank k (A ⧸ J)) J ?_ ?_ ?_
    · intro h; exact absurd rfl (nonZeroDivisors.ne_zero h)
    · intro x hx h
      have hx' : x = ⊤ := Ideal.isUnit_iff.mp hx
      subst hx'
      have e1 : (⟨⊤, h⟩ : nonZeroDivisors (Ideal A)) = 1 := Subtype.ext Ideal.one_eq_top.symm
      haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
      rw [e1, map_one, map_one, Module.finrank_zero_of_subsingleton, pow_zero]
    · intro a p ha hp ih h
      have hpne : p ≠ ⊥ := hp.ne_zero
      have hpmax : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hpne
      have e1 : (⟨p * a, h⟩ : nonZeroDivisors (Ideal A)) = ⟨p, nz p hpne⟩ * ⟨a, nz a ha⟩ := rfl
      rw [e1, map_mul, map_mul, hmaxcls p hpmax hpne, ih (nz a ha), hadd p a hpne ha,
        (hmax p hpmax).1, pow_add, pow_one]
  have hγN : π γ ^ N = 1 := by rw [← map_pow]; exact hπ γ
  have hspan : Ideal.span {f} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hf0
  have hγ1 : π γ = 1 := by
    have e := hall _ (nz _ hspan)
    have e0 : ClassGroup.mk0 (⟨Ideal.span {f}, nz _ hspan⟩ : nonZeroDivisors (Ideal A)) = 1 :=
      (ClassGroup.mk0_eq_one_iff _).mpr ⟨⟨f, rfl⟩⟩
    rw [e0, map_one] at e
    calc π γ = π γ ^ (1 % N) := by rw [← pow_eq_pow_mod 1 hγN, pow_one]
      _ = π γ ^ (Module.finrank k (A ⧸ Ideal.span {f}) % N) := by rw [hfm]
      _ = 1 := by rw [← pow_eq_pow_mod _ hγN, ← e]
  have hc := hall I.1 I.2
  rw [hγ1, one_pow] at hc
  have hmem : ClassGroup.mk0 I ∈ H := (QuotientGroup.eq_one_iff _).mp hc
  obtain ⟨d, hd⟩ := hmem
  exact ⟨d, hd.symm⟩

end GlobalTheory.PicDiv
end

section
open Polynomial

namespace GlobalTheory.PicDiv

theorem jets_mem_subalgebra_of_finiteType : ∀ (k A R : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [CommRing R] [Algebra k R] (N : ℕ) (Δ : ℕ → A →ₗ[k] R), Δ 0 1 = 1 → (∀ l, ∀ u w : A, Δ l (u * w) = ∑ p ∈ Finset.range (l + 1), Δ p u * Δ (l - p) w) →
 ∃ T : Finset R, ∀ S : Subalgebra k R, (∀ t ∈ T, t ∈ S) → ∀ l < N, ∀ u, Δ l u ∈ S := by
  intro k A R _ _ _ _ _ _ N Δ _ hL
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := A)
  refine ⟨(Finset.range N ×ˢ insert 1 s).image (fun x => Δ x.1 x.2), ?_⟩
  intro S hT l hl u
  have key : ∀ u ∈ Algebra.adjoin k (s : Set A), ∀ l < N, Δ l u ∈ S := by
    intro u hu
    induction hu using Algebra.adjoin_induction with
    | mem x hx =>
      intro l hl
      exact hT _ (Finset.mem_image.2 ⟨(l, x), by simp [hl, Finset.mem_coe.1 hx], rfl⟩)
    | algebraMap c =>
      intro l hl
      rw [Algebra.algebraMap_eq_smul_one, map_smul]
      exact S.smul_mem (hT _ (Finset.mem_image.2 ⟨(l, 1), by simp [hl], rfl⟩)) c
    | add x y _ _ hx hy =>
      intro l hl
      rw [map_add]
      exact S.add_mem (hx l hl) (hy l hl)
    | mul x y _ _ hx hy =>
      intro l hl
      rw [hL]
      refine S.sum_mem (fun p hp => S.mul_mem (hx p ?_) (hy (l - p) ?_))
      · have := Finset.mem_range.1 hp; omega
      · omega
  exact key u (hs ▸ Algebra.mem_top) l hl

end GlobalTheory.PicDiv
end

section
open Polynomial

namespace GlobalTheory.PicDiv.DeformZerosHasse

variable {k J I : Type} [Field k] [Fintype J] [Fintype I]

noncomputable def sys (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k)
    (x : J ⊕ I → PowerSeries k) : Option (I × Fin N) → PowerSeries k
  | none => ∑ j, x (Sum.inl j) * ξ j
  | some (i, l) => ∑ j, x (Sum.inl j) *
      ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst (x (Sum.inr i)) : PowerSeries k)

noncomputable def linFun (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k) (y₀ : J → k)
    (v : J ⊕ I → k) : Option (I × Fin N) → k
  | none => ∑ j, v (Sum.inl j) * PowerSeries.constantCoeff (ξ j)
  | some (i, l) => ∑ j, v (Sum.inl j) *
        PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse l.1 (s i j))
      + v (Sum.inr i) * ∑ j, y₀ j * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse l.1 (s i j))

noncomputable def lin (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k) (y₀ : J → k) :
    (J ⊕ I → k) →ₗ[k] (Option (I × Fin N) → k) where
  toFun := linFun N ξ s y₀
  map_add' v w := by
    funext e; rcases e with _ | ⟨i, l⟩ <;> simp [linFun, add_mul, Finset.sum_add_distrib] <;> ring
  map_smul' c v := by
    funext e; rcases e with _ | ⟨i, l⟩ <;> simp [linFun, Finset.mul_sum, mul_assoc, mul_add]

lemma cc_subst (φ a : PowerSeries k) (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.constantCoeff (φ.subst a : PowerSeries k) = PowerSeries.constantCoeff φ :=
  (GlobalTheory.taylor_subst_first_order k φ a 0 1 le_rfl ha).1

end GlobalTheory.PicDiv.DeformZerosHasse

namespace GlobalTheory.PicDiv.DeformZerosHasse

variable {k : Type} [Field k]

lemma dvd_step {m : ℕ} (hm : 1 ≤ m) (y g S S' : PowerSeries k) (y0 c A : k)
    (hy : PowerSeries.constantCoeff y = y0) (hS : PowerSeries.constantCoeff S = A)
    (hT : (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣
      S' - S - PowerSeries.X ^ m * PowerSeries.C c) :
    (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣
      (y + PowerSeries.X ^ m * g) * S' - y * S
        - PowerSeries.X ^ m * PowerSeries.C (PowerSeries.constantCoeff g * A + y0 * c) := by
  obtain ⟨r, hr⟩ := hT
  have hS' : S' = S + PowerSeries.X ^ m * PowerSeries.C c + PowerSeries.X ^ (m + 1) * r := by
    linear_combination hr
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have heq : (y + PowerSeries.X ^ (n + 1) * g) * S' - y * S
      - PowerSeries.X ^ (n + 1) * PowerSeries.C (PowerSeries.constantCoeff g * A + y0 * c)
      = PowerSeries.X ^ (n + 1) * (y * PowerSeries.C c - PowerSeries.C (y0 * c)
          + (g * S - PowerSeries.C (PowerSeries.constantCoeff g * A)))
        + PowerSeries.X ^ (n + 1 + 1) * (y * r + PowerSeries.X ^ n *
          (g * PowerSeries.C c + PowerSeries.X * g * r)) := by
    rw [hS', map_add]; ring
  rw [heq]
  refine dvd_add ?_ (dvd_mul_right _ _)
  rw [pow_succ]
  refine mul_dvd_mul_left _ ?_
  rw [PowerSeries.X_dvd_iff]
  simp [hy, hS]

end GlobalTheory.PicDiv.DeformZerosHasse

namespace GlobalTheory.PicDiv.DeformZerosHasse

theorem deform : ∀ (k J I : Type) [Field k] [Fintype J] [Fintype I] (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k) (y₀ : J → k), 1 ≤ N → (N : k) ≠ 0 →
 ∑ j, y₀ j * PowerSeries.constantCoeff (ξ j) = 0 →
 (∀ i, ∀ l < N, ∑ j, y₀ j * PowerSeries.coeff l (s i j) = 0) → (∀ i, ∑ j, y₀ j * PowerSeries.coeff N (s i j) ≠ 0) →
 (∀ (e₀ : k) (e : I → ℕ → k), ∃ h : J → k, ∑ j, h j * PowerSeries.constantCoeff (ξ j) = e₀ ∧ ∀ i, ∀ l, l + 1 < N → ∑ j, h j * PowerSeries.coeff l (s i j) = e i l) →
 ∃ (y : J → PowerSeries k) (a : I → PowerSeries k), (∀ j, PowerSeries.constantCoeff (y j) = y₀ j) ∧ (∀ i, PowerSeries.constantCoeff (a i) = 0) ∧
   ∑ j, y j * ξ j = 0 ∧ ∀ i, ∀ l < N, ∑ j, y j * ((GlobalTheory.PicDiv.hasse l (s i j)).subst (a i) : PowerSeries k) = 0 := by
  intro k J I _ _ _ N ξ s y₀ hN hNk h0 hlow hN' hsurj
  have hA : ∀ (f : PowerSeries k) (l : ℕ), PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse l f)
      = PowerSeries.coeff l f := fun f l => GlobalTheory.PicDiv.constantCoeff_hasse l f
  have hB : ∀ (f : PowerSeries k) (l : ℕ), PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse l f)
      = ((l + 1 : ℕ) : k) * PowerSeries.coeff (l + 1) f := fun f l => GlobalTheory.PicDiv.coeff_one_hasse l f
  have hsur : Function.Surjective (lin N ξ s y₀) := by
    intro w
    obtain ⟨hv, hv0, hvl⟩ := hsurj (w none)
      (fun i l => if hl : l < N then w (some (i, ⟨l, hl⟩)) else 0)
    have hN1 : N - 1 < N := by omega
    have hS : ∀ i, ∑ j, y₀ j * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse (N - 1) (s i j)) ≠ 0 := by
      intro i
      simp only [hB]
      have e1 : N - 1 + 1 = N := by omega
      rw [e1]
      calc ∑ j, y₀ j * (((N : ℕ) : k) * PowerSeries.coeff N (s i j))
          = ((N : ℕ) : k) * ∑ j, y₀ j * PowerSeries.coeff N (s i j) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ ≠ 0 := mul_ne_zero hNk (hN' i)
    refine ⟨Sum.elim hv (fun i => (w (some (i, ⟨N - 1, hN1⟩)) - ∑ j, hv j *
        PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse (N - 1) (s i j))) /
        ∑ j, y₀ j * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse (N - 1) (s i j))), ?_⟩
    funext e
    rcases e with _ | ⟨i, l⟩
    · simpa [lin, linFun] using hv0
    · simp only [lin, linFun, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr]
      rcases Nat.lt_or_ge (l.1 + 1) N with hl | hl
      · have h1 : ∑ j, hv j * PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse l.1 (s i j))
            = w (some (i, l)) := by
          simp only [hA]
          have := hvl i l.1 hl
          rw [dif_pos l.2] at this
          exact this
        have h2 : ∑ j, y₀ j * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse l.1 (s i j)) = 0 := by
          simp only [hB]
          calc ∑ j, y₀ j * (((l.1 + 1 : ℕ) : k) * PowerSeries.coeff (l.1 + 1) (s i j))
              = ((l.1 + 1 : ℕ) : k) * ∑ j, y₀ j * PowerSeries.coeff (l.1 + 1) (s i j) := by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
            _ = 0 := by rw [hlow i (l.1 + 1) (by omega), mul_zero]
        rw [h1, h2, mul_zero, add_zero]
      · have hl' : l = ⟨N - 1, hN1⟩ := Fin.ext (by simp; omega)
        subst hl'
        rw [div_mul_cancel₀ _ (hS i)]
        ring
  have hbase : ∀ e, PowerSeries.constantCoeff
      (sys N ξ s (fun i => PowerSeries.C (Sum.elim y₀ 0 i)) e) = 0 := by
    intro e
    rcases e with _ | ⟨i, l⟩
    · simp [sys, map_sum, h0]
    · simp only [sys, map_sum, map_mul, PowerSeries.constantCoeff_C, Sum.elim_inl, Sum.elim_inr]
      have h' : ∀ j, PowerSeries.constantCoeff ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst
          (PowerSeries.C ((0 : I → k) i)) : PowerSeries k) = PowerSeries.coeff l.1 (s i j) := by
        intro j; rw [cc_subst _ _ (by simp), hA]
      simp only [h']
      exact hlow i l.1 l.2
  have htay : ∀ (x h : J ⊕ I → PowerSeries k) (m : ℕ), 1 ≤ m →
      (∀ i, PowerSeries.constantCoeff (x i) = Sum.elim y₀ 0 i) → ∀ e,
      (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ sys N ξ s (fun i => x i + PowerSeries.X ^ m * h i) e
        - sys N ξ s x e - PowerSeries.X ^ m *
          PowerSeries.C (lin N ξ s y₀ (fun i => PowerSeries.constantCoeff (h i)) e) := by

    intro x h m hm hx0 e
    rcases e with _ | ⟨i, l⟩
    · simp only [sys, lin, linFun, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl]
      have heq : ∑ j, (x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) * ξ j - ∑ j, x (Sum.inl j) * ξ j
          - PowerSeries.X ^ m * PowerSeries.C (∑ j, PowerSeries.constantCoeff (h (Sum.inl j)) * PowerSeries.constantCoeff (ξ j))
          = PowerSeries.X ^ m * (∑ j, h (Sum.inl j) * ξ j - PowerSeries.C (∑ j, PowerSeries.constantCoeff (h (Sum.inl j)) * PowerSeries.constantCoeff (ξ j))) := by
        rw [mul_sub, Finset.mul_sum]; simp only [add_mul, Finset.sum_add_distrib, mul_assoc]; ring
      rw [heq, pow_succ]
      refine mul_dvd_mul_left _ ?_
      rw [PowerSeries.X_dvd_iff]
      simp [map_sum]
    · simp only [sys, lin, linFun, LinearMap.coe_mk, AddHom.coe_mk]
      set a := x (Sum.inr i)
      set b := h (Sum.inr i)
      have ha : PowerSeries.constantCoeff a = 0 := by simpa using hx0 (Sum.inr i)
      have key : ∀ j, (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣
          (x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) *
            ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst (a + PowerSeries.X ^ m * b) : PowerSeries k)
          - x (Sum.inl j) * ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst a : PowerSeries k)
          - PowerSeries.X ^ m * PowerSeries.C (PowerSeries.constantCoeff (h (Sum.inl j)) *
              PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse l.1 (s i j))
              + y₀ j * (PowerSeries.constantCoeff b * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse l.1 (s i j)))) := by
        intro j
        have T := GlobalTheory.taylor_subst_first_order k (GlobalTheory.PicDiv.hasse l.1 (s i j)) a b m hm ha
        exact dvd_step hm _ _ _ _ _ _ _ (by simpa using hx0 (Sum.inl j)) T.1 T.2
      have heq : ∑ j, (x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) *
            ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst (a + PowerSeries.X ^ m * b) : PowerSeries k)
          - ∑ j, x (Sum.inl j) * ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst a : PowerSeries k)
          - PowerSeries.X ^ m * PowerSeries.C (∑ j, PowerSeries.constantCoeff (h (Sum.inl j)) *
              PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse l.1 (s i j))
              + PowerSeries.constantCoeff b * ∑ j, y₀ j * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse l.1 (s i j)))
          = ∑ j, ((x (Sum.inl j) + PowerSeries.X ^ m * h (Sum.inl j)) *
            ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst (a + PowerSeries.X ^ m * b) : PowerSeries k)
          - x (Sum.inl j) * ((GlobalTheory.PicDiv.hasse l.1 (s i j)).subst a : PowerSeries k)
          - PowerSeries.X ^ m * PowerSeries.C (PowerSeries.constantCoeff (h (Sum.inl j)) *
              PowerSeries.constantCoeff (GlobalTheory.PicDiv.hasse l.1 (s i j))
              + y₀ j * (PowerSeries.constantCoeff b * PowerSeries.coeff 1 (GlobalTheory.PicDiv.hasse l.1 (s i j))))) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← map_sum,
          Finset.sum_add_distrib, Finset.mul_sum (a := PowerSeries.constantCoeff b)]
        congr 4
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [heq]
      exact Finset.dvd_sum fun j _ => key j
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.newton_powerSeries_target k (J ⊕ I) (Option (I × Fin N)) (sys N ξ s) (Sum.elim y₀ 0)
    (lin N ξ s y₀) hsur hbase htay
  refine ⟨fun j => x (Sum.inl j), fun i => x (Sum.inr i), fun j => by simpa using hx0 (Sum.inl j),
    fun i => by simpa using hx0 (Sum.inr i), hx none, ?_⟩
  intro i l hl
  exact hx (some (i, ⟨l, hl⟩))

end GlobalTheory.PicDiv.DeformZerosHasse
end

section
section
open Polynomial

namespace GlobalTheory.PicDiv

variable {R : Type*} [CommRing R]

theorem hasse_coe (l : ℕ) (f : R[X]) :
    hasse l (f : PowerSeries R) = ((hasseDeriv l f : R[X]) : PowerSeries R) := by
  ext n
  rw [coeff_hasse, Polynomial.coeff_coe, Polynomial.coeff_coe, hasseDeriv_coeff]

theorem coeff_hasse_congr {l n : ℕ} {φ φ' : PowerSeries R}
    (h : ∀ m ≤ n + l, PowerSeries.coeff m φ = PowerSeries.coeff m φ') :
    PowerSeries.coeff n (hasse l φ) = PowerSeries.coeff n (hasse l φ') := by
  rw [coeff_hasse, coeff_hasse, h _ le_rfl]

theorem coeff_mul_congr {n : ℕ} {φ φ' ψ ψ' : PowerSeries R}
    (h₁ : ∀ m ≤ n, PowerSeries.coeff m φ = PowerSeries.coeff m φ')
    (h₂ : ∀ m ≤ n, PowerSeries.coeff m ψ = PowerSeries.coeff m ψ') :
    PowerSeries.coeff n (φ * ψ) = PowerSeries.coeff n (φ' * ψ') := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun ij hij => ?_
  have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [h₁ _ (by omega), h₂ _ (by omega)]

theorem hasse_mul (l : ℕ) (φ ψ : PowerSeries R) :
    hasse l (φ * ψ) = ∑ p ∈ Finset.range (l + 1), hasse p φ * hasse (l - p) ψ := by
  ext n
  set M := n + l + 1 with hM
  set f : R[X] := PowerSeries.trunc M φ
  set g : R[X] := PowerSeries.trunc M ψ
  have hf : ∀ m < M, PowerSeries.coeff m φ = PowerSeries.coeff m (f : PowerSeries R) := by
    intro m hm
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm]
  have hg : ∀ m < M, PowerSeries.coeff m ψ = PowerSeries.coeff m (g : PowerSeries R) := by
    intro m hm
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm]
  have hpoly : hasse l ((f : PowerSeries R) * (g : PowerSeries R)) =
      ∑ p ∈ Finset.range (l + 1), hasse p (f : PowerSeries R) * hasse (l - p) (g : PowerSeries R) := by
    rw [← Polynomial.coe_mul, hasse_coe, hasseDeriv_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => hasseDeriv i f * hasseDeriv j g) l]
    simp only [hasse_coe]
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    simp [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_mul]
  rw [coeff_hasse_congr (φ' := (f : PowerSeries R) * (g : PowerSeries R)), hpoly, map_sum, map_sum]
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hpl : p ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
    apply coeff_mul_congr
    · intro m hm
      exact (coeff_hasse_congr fun m' hm' => hf m' (by omega)).symm
    · intro m hm
      exact (coeff_hasse_congr fun m' hm' => hg m' (by omega)).symm
  · intro m hm
    exact coeff_mul_congr (fun m' hm' => hf m' (by omega)) (fun m' hm' => hg m' (by omega))

end GlobalTheory.PicDiv

namespace GlobalTheory

theorem hasse_mul_subst :
    ∀ (k : Type) [Field k] (a φ ψ : PowerSeries k) (l : ℕ), PowerSeries.constantCoeff a = 0 →
      ((GlobalTheory.PicDiv.hasse l (φ * ψ)).subst a : PowerSeries k) =
        ∑ p ∈ Finset.range (l + 1),
          ((GlobalTheory.PicDiv.hasse p φ).subst a : PowerSeries k) * (GlobalTheory.PicDiv.hasse (l - p) ψ).subst a := by
  intro k _ a φ ψ l ha
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero' ha
  rw [GlobalTheory.PicDiv.hasse_mul, ← PowerSeries.coe_substAlgHom hs, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_mul]

end GlobalTheory
end

open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasseDerivativePowerSeries_mul_subst_leibniz : ∀ (k : Type) [Field k] (a φ ψ : PowerSeries k) (l : ℕ), PowerSeries.constantCoeff a = 0 → ((GlobalTheory.PicDiv.hasse l (φ * ψ)).subst a : PowerSeries k) = ∑ p ∈ Finset.range (l + 1), ((GlobalTheory.PicDiv.hasse p φ).subst a : PowerSeries k) * (GlobalTheory.PicDiv.hasse (l - p) ψ).subst a := by
  atlas_forward_decl GlobalTheory.hasse_mul_subst
end

section
section
open Polynomial

namespace GlobalTheory

theorem hasseJet_vanishing_mem_pow (k A : Type) [Field k] [IsAlgClosed k] [CommRing A]
    [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (Δ : ℕ → A →ₗ[k] k)
    (hN : 2 ≤ N) (h01 : Δ 0 1 = 1)
    (hL : ∀ l < N, ∀ u w : A, Δ l (u * w) = ∑ p ∈ Finset.range (l + 1), Δ p u * Δ (l - p) w)
    (hπ : ∃ π : A, Δ 1 π = 1) :
    ∃ Q : Ideal A, Q.IsMaximal ∧ (∀ u, u ∈ Q ↔ Δ 0 u = 0) ∧
      ∀ f : A, (∀ l < N, Δ l f = 0) → f ∈ Q ^ N := by
  classical
  obtain ⟨π, hπ⟩ := hπ
  have hN0 : 0 < N := by omega
  have hN1 : 1 < N := by omega
  have hmul0 : ∀ u w : A, Δ 0 (u * w) = Δ 0 u * Δ 0 w := by
    intro u w
    have := hL 0 hN0 u w
    simpa using this
  let φ : A →+* k :=
    { toFun := Δ 0
      map_one' := h01
      map_mul' := hmul0
      map_zero' := map_zero _
      map_add' := map_add _ }
  have hφ : ∀ u, φ u = Δ 0 u := fun _ => rfl
  have halg : ∀ l c, Δ l (algebraMap k A c) = c * Δ l 1 := by
    intro l c
    rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
  have hsurj : Function.Surjective φ := by
    intro c
    refine ⟨algebraMap k A c, ?_⟩
    rw [hφ, halg, h01, mul_one]
  set Q : Ideal A := RingHom.ker φ with hQdef
  have hQmax : Q.IsMaximal := RingHom.ker_isMaximal_of_surjective φ hsurj
  have hQmem : ∀ u, u ∈ Q ↔ Δ 0 u = 0 := fun u => RingHom.mem_ker
  have h11 : Δ 1 (1 : A) = 0 := by
    have := hL 1 hN1 1 1
    rw [Finset.sum_range_succ, Finset.sum_range_one] at this
    norm_num [h01] at this
    first | exact this | linear_combination -this
  have hvan : ∀ j, ∀ u ∈ Q ^ j, ∀ l < N, l < j → Δ l u = 0 := by
    intro j
    induction j with
    | zero => intro u _ l _ hl; omega
    | succ j ih =>
      intro u hu
      rw [pow_succ] at hu
      refine Submodule.mul_induction_on (C := fun r => ∀ l < N, l < j + 1 → Δ l r = 0) hu ?_ ?_
      · intro a ha b hb l hl hlj
        rw [hL l hl]
        refine Finset.sum_eq_zero fun p hp => ?_
        have hp' : p < l + 1 := Finset.mem_range.mp hp
        by_cases hpj : p < j
        · rw [ih a ha p (by omega) hpj, zero_mul]
        · have : l - p = 0 := by omega
          rw [this, (hQmem b).mp hb, mul_zero]
      · intro a b ha hb l hl hlj
        rw [map_add, ha l hl hlj, hb l hl hlj, add_zero]
  set x : A := π - algebraMap k A (Δ 0 π) with hx
  have hx0 : Δ 0 x = 0 := by rw [hx, map_sub, halg, h01, mul_one, sub_self]
  have hx1 : Δ 1 x = 1 := by rw [hx, map_sub, halg, h11, mul_zero, sub_zero, hπ]
  have hxQ : x ∈ Q := (hQmem x).mpr hx0
  have hxpow : ∀ j < N, Δ j (x ^ j) = 1 := by
    intro j
    induction j with
    | zero => intro _; simpa using h01
    | succ j ih =>
      intro hj
      rw [pow_succ, hL (j + 1) hj, Finset.sum_eq_single j]
      · rw [ih (by omega), show j + 1 - j = 1 by omega, hx1, one_mul]
      · intro p hp hpj
        have hp' := Finset.mem_range.mp hp
        by_cases hlt : p < j
        · rw [hvan j (x ^ j) (Ideal.pow_mem_pow hxQ j) p (by omega) hlt, zero_mul]
        · have : p = j + 1 := by omega
          subst this
          rw [Nat.sub_self, hx0, mul_zero]
      · intro h
        exact absurd (Finset.mem_range.mpr (by omega)) h
  have hxQ2 : x ∉ Q ^ 2 := by
    intro h
    have := hvan 2 x h 1 hN1 (by norm_num)
    rw [hx1] at this
    exact one_ne_zero this
  obtain ⟨J, hJ⟩ : Q ∣ Ideal.span {x} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hxQ)
  have hJQ : Q ⊔ J = ⊤ := by
    by_contra hne
    have hle : J ≤ Q := by
      have := hQmax.eq_of_le hne le_sup_left
      rw [this]
      exact le_sup_right
    apply hxQ2
    have : Ideal.span {x} ≤ Q ^ 2 := by
      rw [hJ, sq]
      exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self x)
  have hdec : ∀ j, Q ^ j ≤ Ideal.span {x ^ j} ⊔ Q ^ (j + 1) := by
    intro j
    have htop : J ^ j ⊔ Q = ⊤ := by
      rw [sup_comm]
      exact Ideal.sup_pow_eq_top hJQ
    calc Q ^ j = Q ^ j * (J ^ j ⊔ Q) := by rw [htop, Ideal.mul_top]
      _ = Q ^ j * J ^ j ⊔ Q ^ j * Q := Ideal.mul_sup _ _ _
      _ = Ideal.span {x ^ j} ⊔ Q ^ (j + 1) := by
        rw [← mul_pow, ← hJ, Ideal.span_singleton_pow, pow_succ]
      _ ≤ _ := le_rfl
  refine ⟨Q, hQmax, hQmem, fun f hf => ?_⟩
  have key : ∀ j ≤ N, f ∈ Q ^ j := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hdec j (ih (by omega)))
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      have hzv : Δ j z = 0 := hvan (j + 1) z hz j (by omega) (by omega)
      have hfj : Δ j f = 0 := hf j (by omega)
      have ha : Δ 0 a = 0 := by
        rw [← hyz, map_add, hzv, add_zero, mul_comm a, hL j (by omega),
          Finset.sum_eq_single j] at hfj
        · rwa [hxpow j (by omega), Nat.sub_self, one_mul] at hfj
        · intro p hp hpj
          have hp' := Finset.mem_range.mp hp
          rw [hvan j (x ^ j) (Ideal.pow_mem_pow hxQ j) p (by omega) (by omega), zero_mul]
        · intro h
          exact absurd (Finset.mem_range.mpr (by omega)) h
      rw [← hyz]
      refine Ideal.add_mem _ ?_ hz
      rw [pow_succ, mul_comm a]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hxQ j) ((hQmem a).mpr ha)
  exact key N le_rfl

end GlobalTheory
end

open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maximal_mem_pow_of_hasse_vanishing : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (Δ : ℕ → A →ₗ[k] k), 2 ≤ N → Δ 0 1 = 1 → (∀ l < N, ∀ u w : A, Δ l (u * w) = ∑ p ∈ Finset.range (l + 1), Δ p u * Δ (l - p) w) → (∃ π : A, Δ 1 π = 1) → ∃ Q : Ideal A, Q.IsMaximal ∧ (∀ u, u ∈ Q ↔ Δ 0 u = 0) ∧ ∀ f : A, (∀ l < N, Δ l f = 0) → f ∈ Q ^ N := by
  atlas_forward_decl GlobalTheory.hasseJet_vanishing_mem_pow
end

section
section
open Polynomial

namespace GlobalTheory

theorem isLocalization_fractionRing_of_finite_polynomial (k A : Type) [Field k] [CommRing A] [IsDomain A]
    [Algebra k[X] A] [Module.Finite k[X] A] [FaithfulSMul k[X] A] :
    IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors k[X])) (FractionRing A) := by
  have hinj : Function.Injective (algebraMap k[X] A) := FaithfulSMul.algebraMap_injective k[X] A
  have hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors k[X]) ≤ nonZeroDivisors A := by
    rintro _ ⟨p, hp, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hp))
  refine
    { map_units := fun y => IsLocalization.map_units (FractionRing A) ⟨y.1, hle y.2⟩
      surj := fun z => ?_
      exists_of_eq := fun {x y} hxy => ⟨1, by rw [IsFractionRing.injective A (FractionRing A) hxy]⟩ }
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors A) z
  have hb0 : (b : A) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hne := Ideal.comap_ne_bot_of_integral_mem (R := k[X]) hb0 (Ideal.mem_span_singleton_self (b : A))
    (Algebra.IsIntegral.isIntegral _)
  obtain ⟨p, hpI, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hpI
  refine ⟨⟨c * a, ⟨_, ⟨p, mem_nonZeroDivisors_of_ne_zero hp0, rfl⟩⟩⟩, ?_⟩
  simp only
  rw [← hc, map_mul, map_mul, ← hab]
  ring

end GlobalTheory

namespace GlobalTheory

theorem exists_finrank_quotient_span_mod_eq_one :
    ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra k[X] A]
      [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A] (N : ℕ), 1 ≤ N →
      ∃ f : A, f ≠ 0 ∧ Module.finrank k (A ⧸ Ideal.span {f}) % N = 1 % N := by
  intro k A _ _ _ _ _ _ _ _ _ N hN
  have : FaithfulSMul k[X] A := inferInstance
  have hinjA : Function.Injective (algebraMap k[X] A) := FaithfulSMul.algebraMap_injective k[X] A
  set L := FractionRing A
  have hinjL : Function.Injective (algebraMap k[X] L) := by
    rw [IsScalarTower.algebraMap_eq k[X] A L]
    exact (IsFractionRing.injective A L).comp hinjA
  have : FaithfulSMul k[X] L := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinjL
  letI : Algebra (RatFunc k) L := RatFunc.liftAlgebra k L
  have : IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors k[X])) L :=
    isLocalization_fractionRing_of_finite_polynomial k A
  have : Module.Finite (RatFunc k) L :=
    Module.Finite.of_isLocalization k[X] A (Rₚ := RatFunc k) (Sₚ := L) (nonZeroDivisors k[X])
  have hC1 : GlobalTheory.NeedB.IsFirstChernClassOfLineBundle (RatFunc k) :=
    GlobalTheory.is_c1_of_finite_of_tsen_lang_systems (RatFunc k) (RatFunc k) (GlobalTheory.tsenLang_ratFunc k)
  obtain ⟨h, hh⟩ := GlobalTheory.norm_surjective_of_is_c1 (RatFunc k) L hC1 RatFunc.X RatFunc.X_ne_zero
  obtain ⟨⟨x, ⟨_, ⟨m, hm0, rfl⟩⟩⟩, hx⟩ :=
    IsLocalization.surj (Algebra.algebraMapSubmonoid A (nonZeroDivisors k[X])) h
  have hm0' : m ≠ 0 := nonZeroDivisors.ne_zero hm0
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  set g : A := x * algebraMap k[X] A (m ^ M) with hg
  have hgL : algebraMap A L g
      = h * algebraMap (RatFunc k) L (algebraMap k[X] (RatFunc k) (m ^ (M + 1))) := by
    simp only at hx
    rw [hg, map_mul, ← hx, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, pow_succ, map_mul]
    ring
  have hnorm : Algebra.norm k[X] g = X * (m ^ (M + 1)) ^ Module.finrank (RatFunc k) L := by
    apply IsFractionRing.injective k[X] (RatFunc k)
    rw [← Algebra.norm_localization k[X] (Rₘ := RatFunc k) (Sₘ := L) (nonZeroDivisors k[X]) g, hgL, map_mul, hh,
      Algebra.norm_algebraMap, map_mul, RatFunc.algebraMap_X, ← map_pow]
  have hp : (m ^ (M + 1)) ^ Module.finrank (RatFunc k) L ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hm0')
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0, Algebra.norm_zero] at hnorm
    exact mul_ne_zero X_ne_zero hp hnorm.symm
  refine ⟨g, hg0, ?_⟩
  rw [finrank_quotient_span_eq_natDegree_norm (Module.Free.chooseBasis k[X] A) hg0, hnorm,
    natDegree_mul X_ne_zero hp, natDegree_X, natDegree_pow, natDegree_pow, mul_left_comm,
    Nat.add_mul_mod_self_left]

end GlobalTheory
end

open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finrank_quotient_span_mod_eq_one' : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A] (N : ℕ), 1 ≤ N → ∃ f : A, f ≠ 0 ∧ Module.finrank k (A ⧸ Ideal.span {f}) % N = 1 % N := by
  atlas_forward_decl GlobalTheory.exists_finrank_quotient_span_mod_eq_one
end

section
open Polynomial

namespace GlobalTheory.PicDiv.FormalDeformHasse

theorem constantCoeff_subst_eq {k : Type} [Field k] (a φ : PowerSeries k)
    (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.constantCoeff (φ.subst a : PowerSeries k) = PowerSeries.constantCoeff φ := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' ha
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst' hs,
    finsum_eq_single _ 0]
  · simp
  · intro d hd
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, ha, zero_pow hd, smul_zero]

theorem not_mem_pow_succ {A : Type} [CommRing A] [IsDedekindDomain A] {N : ℕ} {I : Type}
    [Fintype I] {D P₀ : Ideal A} {Q : I → Ideal A} {f₀ : A} (hP₀ : P₀.IsMaximal)
    (hQmax : ∀ i, (Q i).IsMaximal) (hQinj : Function.Injective Q) (hQP : ∀ i, Q i ≠ P₀)
    (hDQ : ∀ i, ¬ D ≤ Q i) (hf₀ : f₀ ≠ 0)
    (hspan : Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N) (i : I) : f₀ ∉ Q i ^ (N + 1) := by
  classical
  intro hmem
  have hQne : Q i ≠ ⊥ := by
    intro h
    rw [h, Ideal.bot_pow (Nat.succ_ne_zero N), Ideal.mem_bot] at hmem
    exact hf₀ hmem
  have hp : Prime (Q i) := Ideal.prime_of_isPrime hQne (hQmax i).isPrime
  have hdvd : Q i ^ (N + 1) ∣ Ideal.span {f₀} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
  have hsplit : Ideal.span {f₀} = Q i ^ N * (P₀ * D * ∏ j ∈ Finset.univ.erase i, Q j ^ N) := by
    rw [hspan, ← Finset.mul_prod_erase Finset.univ (fun j => Q j ^ N) (Finset.mem_univ i)]
    ring
  rw [hsplit, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero N hQne)] at hdvd
  rcases hp.dvd_or_dvd hdvd with h | h
  · rcases hp.dvd_or_dvd h with h | h
    · exact hQP i (hP₀.eq_of_le (hQmax i).ne_top (Ideal.le_of_dvd h)).symm
    · exact hDQ i (Ideal.le_of_dvd h)
  · obtain ⟨j, hj, hji⟩ := (hp.dvd_finset_prod_iff _).mp h
    have hle : Q j ≤ Q i := Ideal.le_of_dvd (hp.dvd_of_dvd_pow hji)
    exact (Finset.mem_erase.mp hj).1 (hQinj ((hQmax j).eq_of_le (hQmax i).ne_top hle))

theorem coeff_map_sum {k A : Type} [Field k] [CommRing A] [Algebra k A] {m : ℕ}
    (σ : A →ₐ[k] PowerSeries k) (v : Fin m → A) (c : Fin m → k) (l : ℕ) :
    ∑ j, c j * PowerSeries.coeff l (σ (v j)) = PowerSeries.coeff l (σ (∑ j, c j • v j)) := by
  simp [map_sum, map_smul]

theorem formal_deformation : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (I : Type) [Fintype I] (V : Submodule k A) (D P₀ : Ideal A) (Q : I → Ideal A) (f₀ : A), 2 ≤ N → (N : k) ≠ 0 → P₀.IsMaximal → (FiniteDimensional k V ∧ (∀ v ∈ V, v ∈ D) ∧ (∀ i, (Q i).IsMaximal) ∧ Function.Injective Q ∧ (∀ i, Q i ≠ P₀) ∧ (∀ i, ¬ D ≤ Q i) ∧ ¬ D ≤ P₀ ∧ f₀ ∈ V ∧ f₀ ≠ 0 ∧ Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N ∧ (∀ u : A, ∃ v ∈ V, u - v ∈ P₀ * ∏ i, Q i ^ (N - 1))) → ∃ (ξ : A →ₐ[k] PowerSeries k) (Δ : I → ℕ → A →ₗ[k] PowerSeries k) (m : ℕ) (v : Fin m → A) (y : Fin m → PowerSeries k),
  Function.Injective ξ ∧ (∀ i, Δ i 0 1 = 1) ∧ (∀ i, (∀ l, ∀ u w : A, Δ i l (u * w) = ∑ p ∈ Finset.range (l + 1), Δ i p u * Δ i (l - p) w)) ∧ (∀ i, ∃ π : A, Δ i 1 π = 1) ∧
  (∀ j, v j ∈ V) ∧ LinearIndependent k v ∧ (∃ j, IsUnit (y j)) ∧ ∑ j, y j * ξ (v j) = 0 ∧ (∀ i, ∀ l < N, ∑ j, y j * Δ i l (v j) = 0) ∧
  (∀ i i', i ≠ i' → ∃ u : A, IsUnit (Δ i 0 u - Δ i' 0 u)) ∧ (∀ i, ∃ u : A, IsUnit (Δ i 0 u - ξ u)) ∧ (∀ i, ∃ u ∈ D, IsUnit (Δ i 0 u)) ∧ (∃ u ∈ D, IsUnit (ξ u)) := by
  intro k A _ _ _ _ _ _ N I _ V D P₀ Q f₀ hN hNk hP₀ hyp
  obtain ⟨hVfin, hVD, hQmax, hQinj, hQP, hDQ, hDP, hf₀V, hf₀, hspan, hsurj⟩ := hyp
  classical
  have hne : Ideal.span {f₀} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hf₀
  have hf₀P : f₀ ∈ P₀ := by
    have : Ideal.span {f₀} ≤ P₀ := hspan ▸ le_trans Ideal.mul_le_left Ideal.mul_le_left
    exact this (Ideal.mem_span_singleton_self f₀)
  have hf₀Q : ∀ i, f₀ ∈ Q i ^ N := by
    intro i
    have h1 : Ideal.span {f₀} ≤ ∏ i, Q i ^ N := hspan ▸ Ideal.mul_le_right
    have h2 : (∏ i, Q i ^ N) ≤ Q i ^ N :=
      Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun j => Q j ^ N) (Finset.mem_univ i))
    exact h2 (h1 (Ideal.mem_span_singleton_self f₀))
  have hP₀ne : P₀ ≠ ⊥ := by
    rintro rfl; exact hf₀ ((Ideal.mem_bot).mp hf₀P)
  have hQne : ∀ i, Q i ≠ ⊥ := by
    intro i h
    have := hf₀Q i
    rw [h, Ideal.bot_pow (by omega), Ideal.mem_bot] at this
    exact hf₀ this

  obtain ⟨σ₀, π₀, -, hσ₀inj, hσ₀pow, hσ₀surj⟩ := GlobalTheory.CurveCompletionG.exists_completion_embedding k A P₀ hP₀ hP₀ne
  have hcomp := fun i => GlobalTheory.CurveCompletionG.exists_completion_embedding k A (Q i) (hQmax i) (hQne i)
  choose σ π hσπ hσinj hσpow hσsurj using hcomp
  have hzero : ∀ (τ : A →ₐ[k] PowerSeries k) (R : Ideal A),
      (∀ (m : ℕ) (u : A), u ∈ R ^ m ↔ (PowerSeries.X : PowerSeries k) ^ m ∣ τ u) →
      ∀ u, u ∈ R ↔ PowerSeries.constantCoeff (τ u) = 0 := by
    intro τ R h u
    rw [← PowerSeries.X_dvd_iff, ← pow_one (PowerSeries.X : PowerSeries k), ← h 1 u, pow_one]

  set b := Module.finBasis k V with hb
  set m := Module.finrank k V with hm
  let v : Fin m → A := fun j => (b j : A)
  have hrepr : ∀ x : V, ∑ j, b.repr x j • v j = (x : A) := by
    intro x
    have h := congrArg Subtype.val (b.sum_repr x)
    rw [Submodule.coe_sum] at h
    simpa [v] using h
  let y₀ : Fin m → k := fun j => b.repr ⟨f₀, hf₀V⟩ j
  have hy₀ : ∑ j, y₀ j • v j = f₀ := hrepr ⟨f₀, hf₀V⟩
  have hlin : ∀ (τ : A →ₐ[k] PowerSeries k) (c : Fin m → k) (l : ℕ),
      ∑ j, c j * PowerSeries.coeff l (τ (v j)) = PowerSeries.coeff l (τ (∑ j, c j • v j)) :=
    fun τ c l => coeff_map_sum τ v c l
  have hlin0 : ∀ (τ : A →ₐ[k] PowerSeries k) (c : Fin m → k),
      ∑ j, c j * PowerSeries.constantCoeff (τ (v j)) =
        PowerSeries.constantCoeff (τ (∑ j, c j • v j)) := by
    intro τ c
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hlin τ c 0
  have h1 : ∑ j, y₀ j * PowerSeries.constantCoeff (σ₀ (v j)) = 0 := by
    rw [hlin0, hy₀]; exact (hzero σ₀ P₀ hσ₀pow f₀).mp hf₀P
  have h2 : ∀ i, ∀ l < N, ∑ j, y₀ j * PowerSeries.coeff l (σ i (v j)) = 0 := by
    intro i l hl
    rw [hlin, hy₀]
    exact PowerSeries.X_pow_dvd_iff.mp ((hσpow i N f₀).mp (hf₀Q i)) l hl
  have h3 : ∀ i, ∑ j, y₀ j * PowerSeries.coeff N (σ i (v j)) ≠ 0 := by
    intro i hc
    rw [hlin, hy₀] at hc
    apply not_mem_pow_succ hP₀ hQmax hQinj hQP hDQ hf₀ hspan i
    rw [hσpow i (N + 1) f₀, PowerSeries.X_pow_dvd_iff]
    intro l hl
    rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
    · exact PowerSeries.X_pow_dvd_iff.mp ((hσpow i N f₀).mp (hf₀Q i)) l hl
    · exact hc
  have h4 : ∀ (e₀ : k) (e : I → ℕ → k), ∃ h : Fin m → k,
      ∑ j, h j * PowerSeries.constantCoeff (σ₀ (v j)) = e₀ ∧
        ∀ i, ∀ l, l + 1 < N → ∑ j, h j * PowerSeries.coeff l (σ i (v j)) = e i l := by
    intro e₀ e
    obtain ⟨u₀, hu₀⟩ := hσ₀surj 1 (PowerSeries.C e₀)
    choose u hu using fun i => hσsurj i (N - 1) (PowerSeries.mk (e i))
    let P : Option I → Ideal A := fun o => o.elim P₀ Q
    let ex : Option I → ℕ := fun o => o.elim 1 (fun _ => N - 1)
    obtain ⟨w, hw⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Finset.univ) P ex
      (by
        rintro (_ | i) -
        exacts [Ideal.prime_of_isPrime hP₀ne hP₀.isPrime,
          Ideal.prime_of_isPrime (hQne i) (hQmax i).isPrime])
      (by
        rintro (_ | i) - (_ | j) - hij
        · exact absurd rfl hij
        · exact (hQP j).symm
        · exact hQP i
        · exact hQinj.ne (fun h => hij (by rw [h])))
      (fun o => o.1.elim u₀ u)
    have hw₀ : w - u₀ ∈ P₀ := by simpa [P, ex] using hw none (Finset.mem_univ _)
    have hwi : ∀ i, w - u i ∈ Q i ^ (N - 1) := fun i => by
      simpa [P, ex] using hw (some i) (Finset.mem_univ _)
    obtain ⟨v', hv'V, hv'⟩ := hsurj w
    have hv'P : v' - u₀ ∈ P₀ := by
      have : w - v' ∈ P₀ := Ideal.mul_le_left hv'
      have e1 : v' - u₀ = (w - u₀) - (w - v') := by ring
      rw [e1]; exact P₀.sub_mem hw₀ this
    have hv'Q : ∀ i, v' - u i ∈ Q i ^ (N - 1) := by
      intro i
      have h5 : (∏ i, Q i ^ (N - 1)) ≤ Q i ^ (N - 1) :=
        Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun j => Q j ^ (N - 1)) (Finset.mem_univ i))
      have : w - v' ∈ Q i ^ (N - 1) := h5 (Ideal.mul_le_right hv')
      have e1 : v' - u i = (w - u i) - (w - v') := by ring
      rw [e1]; exact Ideal.sub_mem _ (hwi i) this
    refine ⟨fun j => b.repr ⟨v', hv'V⟩ j, ?_, ?_⟩
    · rw [hlin0, hrepr ⟨v', hv'V⟩]
      have h6 : (PowerSeries.X : PowerSeries k) ^ 1 ∣ σ₀ v' - σ₀ u₀ := by
        rw [← map_sub, ← hσ₀pow 1, pow_one]; exact hv'P
      have h7 : (PowerSeries.X : PowerSeries k) ∣ PowerSeries.C e₀ - σ₀ v' := by
        have := dvd_sub hu₀ h6
        rw [pow_one] at this
        convert this using 1; ring
      rw [PowerSeries.X_dvd_iff, map_sub, PowerSeries.constantCoeff_C, sub_eq_zero] at h7
      exact h7.symm
    · intro i l hl
      rw [hlin, hrepr ⟨v', hv'V⟩]
      have h6 : (PowerSeries.X : PowerSeries k) ^ (N - 1) ∣ σ i v' - σ i (u i) := by
        rw [← map_sub, ← hσpow i]; exact hv'Q i
      have h7 := PowerSeries.X_pow_dvd_iff.mp (dvd_sub (hu i) h6) l (by omega)
      rw [show PowerSeries.mk (e i) - σ i (u i) - (σ i v' - σ i (u i)) =
        PowerSeries.mk (e i) - σ i v' by ring, map_sub, PowerSeries.coeff_mk, sub_eq_zero] at h7
      exact h7.symm
  obtain ⟨y, a, hy0, ha0, hyξ, hyΔ⟩ := GlobalTheory.PicDiv.DeformZerosHasse.deform k (Fin m) I N (fun j => σ₀ (v j))
    (fun i j => σ i (v j)) y₀ (by omega) hNk h1 h2 h3 h4
  have hsub : ∀ i, PowerSeries.HasSubst (a i) :=
    fun i => PowerSeries.HasSubst.of_constantCoeff_zero' (ha0 i)
  let Δ : I → ℕ → A →ₗ[k] PowerSeries k := fun i l =>
    (PowerSeries.substAlgHom (R := k) (hsub i)).toLinearMap ∘ₗ
      (GlobalTheory.PicDiv.hasse l) ∘ₗ (σ i).toLinearMap
  have hΔ : ∀ i l u, Δ i l u =
      ((GlobalTheory.PicDiv.hasse l (σ i u)).subst (a i) : PowerSeries k) := by
    intro i l u
    simp only [Δ, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      PowerSeries.coe_substAlgHom]
  have hcc : ∀ i u, PowerSeries.constantCoeff (Δ i 0 u) = PowerSeries.constantCoeff (σ i u) := by
    intro i u
    rw [hΔ, GlobalTheory.PicDiv.hasse_zero]
    exact constantCoeff_subst_eq _ _ (ha0 i)
  have hunit : ∀ φ : PowerSeries k, IsUnit φ ↔ PowerSeries.constantCoeff φ ≠ 0 := by
    intro φ; rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  have hQσ : ∀ i u, u ∈ Q i ↔ PowerSeries.constantCoeff (σ i u) = 0 :=
    fun i => hzero (σ i) (Q i) (hσpow i)
  have hPσ : ∀ u, u ∈ P₀ ↔ PowerSeries.constantCoeff (σ₀ u) = 0 := hzero σ₀ P₀ hσ₀pow
  refine ⟨σ₀, Δ, m, v, y, hσ₀inj, ?_, ?_, ?_, ?_, ?_, ?_, hyξ, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hΔ, GlobalTheory.PicDiv.hasse_zero, map_one, ← PowerSeries.coe_substAlgHom (hsub i), map_one]
  · intro i l u w
    simp only [hΔ, map_mul]
    exact GlobalTheory.T.hasseDerivativePowerSeries_mul_subst_leibniz k (a i) _ _ l (ha0 i)
  · intro i
    refine ⟨π i, ?_⟩
    have hX : GlobalTheory.PicDiv.hasse 1 (PowerSeries.X : PowerSeries k) = 1 := by
      ext n; rw [GlobalTheory.PicDiv.coeff_hasse, PowerSeries.coeff_X, PowerSeries.coeff_one]; rcases n with _ | n <;> simp
    rw [hΔ, hσπ, hX, ← PowerSeries.coe_substAlgHom (hsub i), map_one]
  · intro j; exact (b j).2
  · exact b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  · by_contra hcon
    push_neg at hcon
    have hz : ∀ j, y₀ j = 0 := by
      intro j
      have := hcon j
      rwa [hunit, hy0, not_not] at this
    apply hf₀
    rw [← hy₀]
    simp [hz]
  · intro i l hl
    simpa only [hΔ] using hyΔ i l hl
  · intro i i' hii'
    have hle : ¬ Q i' ≤ Q i := fun h =>
      hii' (hQinj ((hQmax i').eq_of_le (hQmax i).ne_top h)).symm
    obtain ⟨u, hu', hu⟩ := SetLike.not_le_iff_exists.mp hle
    refine ⟨u, ?_⟩
    rw [hunit, map_sub, hcc, hcc, (hQσ i' u).mp hu', sub_zero]
    exact fun h => hu ((hQσ i u).mpr h)
  · intro i
    have hle : ¬ P₀ ≤ Q i := fun h => hQP i (hP₀.eq_of_le (hQmax i).ne_top h).symm
    obtain ⟨u, hu', hu⟩ := SetLike.not_le_iff_exists.mp hle
    refine ⟨u, ?_⟩
    rw [hunit, map_sub, hcc, (hPσ u).mp hu', sub_zero]
    exact fun h => hu ((hQσ i u).mpr h)
  · intro i
    obtain ⟨u, hu', hu⟩ := SetLike.not_le_iff_exists.mp (hDQ i)
    refine ⟨u, hu', ?_⟩
    rw [hunit, hcc]
    exact fun h => hu ((hQσ i u).mpr h)
  · obtain ⟨u, hu', hu⟩ := SetLike.not_le_iff_exists.mp hDP
    refine ⟨u, hu', ?_⟩
    rw [hunit]
    exact fun h => hu ((hPσ u).mpr h)

end GlobalTheory.PicDiv.FormalDeformHasse

namespace GlobalTheory.PicDiv
namespace GenericSpecialHasse

theorem ext_unit_ne {k R : Type} [Field k] [CommRing R] [IsDomain R] [Algebra k R]
    (S : Subalgebra k R) (L : R →ₗ[k] k) (hone : L 1 = 1)
    (hmul : ∀ x ∈ S, ∀ z ∈ S, L (x * z) = L x * L z) (x : R) (hx : x ∈ S) (hu : IsUnit x)
    (hi : Ring.inverse x ∈ S) : L x ≠ 0 := by
  intro h
  have e := hmul x hx _ hi
  rw [Ring.mul_inverse_cancel x hu, hone, h, zero_mul] at e
  exact one_ne_zero e

theorem lin_eq_of_zero_iff {k A : Type} [Field k] [CommRing A] [Algebra k A]
    (g h : A →ₗ[k] k) (hg : g 1 = 1) (hh : h 1 = 1) (hk : ∀ u, g u = 0 ↔ h u = 0) (u : A) :
    g u = h u := by
  have h1 : g (u - g u • 1) = 0 := by simp [hg]
  have h2 := (hk _).1 h1
  rw [map_sub, map_smul, hh, smul_eq_mul, mul_one, sub_eq_zero] at h2
  exact h2.symm

end GenericSpecialHasse

theorem specialise_generic_solution_hasse : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (R : Type) [CommRing R] [IsDomain R] [Algebra k R] (N : ℕ) (I : Type) [Fintype I] (V : Submodule k A) (D : Ideal A), 2 ≤ N → (∃ (ξ : A →ₐ[k] R) (Δ : I → ℕ → A →ₗ[k] R) (m : ℕ) (v : Fin m → A) (y : Fin m → R),
  Function.Injective ξ ∧ (∀ i, Δ i 0 1 = 1) ∧ (∀ i, (∀ l, ∀ u w : A, Δ i l (u * w) = ∑ p ∈ Finset.range (l + 1), Δ i p u * Δ i (l - p) w)) ∧ (∀ i, ∃ π : A, Δ i 1 π = 1) ∧
  (∀ j, v j ∈ V) ∧ LinearIndependent k v ∧ (∃ j, IsUnit (y j)) ∧ ∑ j, y j * ξ (v j) = 0 ∧ (∀ i, ∀ l < N, ∑ j, y j * Δ i l (v j) = 0) ∧
  (∀ i i', i ≠ i' → ∃ u : A, IsUnit (Δ i 0 u - Δ i' 0 u)) ∧ (∀ i, ∃ u : A, IsUnit (Δ i 0 u - ξ u)) ∧ (∀ i, ∃ u ∈ D, IsUnit (Δ i 0 u)) ∧ (∃ u ∈ D, IsUnit (ξ u))) → ∃ a : A, a ≠ 0 ∧ ∀ P : Ideal A, P.IsMaximal → a ∉ P → ∃ (Q' : I → Ideal A) (f : A), (∀ i, (Q' i).IsMaximal) ∧ Function.Injective Q' ∧ (∀ i, Q' i ≠ P) ∧ (∀ i, ¬ D ≤ Q' i) ∧ ¬ D ≤ P ∧ f ∈ V ∧ f ≠ 0 ∧ f ∈ P ∧ ∀ i, f ∈ Q' i ^ N := by
  intro k A _ _ _ _ _ _ R _ _ _ N I _ V D hN hex
  classical
  obtain ⟨ξ, Δ, m, v, y, hinj, h01, hleib, hπ, hvV, hli, ⟨j0, hj0⟩, heq0, heqΔ, hsep, hsepξ,
    hD, hDξ⟩ := hex
  have hsep' : ∀ p : I × I, ∃ u : A, p.1 ≠ p.2 → IsUnit (Δ p.1 0 u - Δ p.2 0 u) := by
    intro p
    by_cases hp : p.1 = p.2
    · exact ⟨0, fun h => absurd hp h⟩
    · obtain ⟨u, hu⟩ := hsep p.1 p.2 hp
      exact ⟨u, fun _ => hu⟩
  choose us hus using hsep'
  choose uξ huξ using hsepξ
  choose uD huDmem huD using hD
  obtain ⟨u0, hu0D, hu0⟩ := hDξ
  choose TJ hTJ using fun i => GlobalTheory.PicDiv.jets_mem_subalgebra_of_finiteType k A R N (Δ i) (h01 i) (hleib i)
  let T : Finset R := Finset.univ.biUnion TJ ∪ Finset.univ.image y ∪
    Finset.univ.image (fun p : I × I => Ring.inverse (Δ p.1 0 (us p) - Δ p.2 0 (us p))) ∪
    Finset.univ.image (fun i => Ring.inverse (Δ i 0 (uξ i) - ξ (uξ i))) ∪
    Finset.univ.image (fun i => Ring.inverse (Δ i 0 (uD i))) ∪
    {Ring.inverse (ξ u0), Ring.inverse (y j0)}
  obtain ⟨a, S, hξS, ha0, hTS, hspec⟩ := GlobalTheory.exists_ne_zero_forall_point_extend_subalgebra k A R ξ hinj T
  refine ⟨a, ha0, ?_⟩
  intro P hPmax haP
  obtain ⟨-, φ, hφ⟩ := (GlobalTheory.DedekindCodimG.dedekind_finiteType_codim k A).2.1 P hPmax
  obtain ⟨ψ, hψ⟩ := hspec φ (fun h => haP ((hφ a).2 h))
  obtain ⟨L, hL⟩ := LinearMap.exists_extend (ψ.toLinearMap.comp
    (LinearEquiv.refl k (Subalgebra.toSubmodule S)).toLinearMap)
  have hLS : ∀ x (hx : x ∈ S), L x = ψ ⟨x, hx⟩ := by
    intro x hx
    exact LinearMap.congr_fun hL ⟨x, hx⟩
  have hone : L 1 = 1 := by rw [hLS 1 S.one_mem]; exact map_one ψ
  have hmul : ∀ x ∈ S, ∀ z ∈ S, L (x * z) = L x * L z := by
    intro x hx z hz
    rw [hLS _ (S.mul_mem hx hz), hLS x hx, hLS z hz, ← map_mul]; rfl
  have hLξ : ∀ u, L (ξ u) = φ u := fun u => by rw [hLS _ (hξS u), hψ]
  have hSΔ : ∀ i l, l < N → ∀ u, Δ i l u ∈ S := fun i =>
    hTJ i S (fun t ht => hTS t (by simp only [T, Finset.mem_union, Finset.mem_biUnion]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨i, Finset.mem_univ _, ht⟩))))))
  have hy : ∀ j, y j ∈ S := fun j => hTS _ (by simp [T])
  have hN0 : 0 < N := by omega
  have hN1 : 1 < N := by omega
  let Δ' : I → ℕ → A →ₗ[k] k := fun i l => if l < N then L ∘ₗ Δ i l else 0
  have hΔ' : ∀ i l, l < N → ∀ u, Δ' i l u = L (Δ i l u) := by
    intro i l h u; simp [Δ', h]
  have hjet : ∀ i, ∃ Q : Ideal A, Q.IsMaximal ∧ (∀ u, u ∈ Q ↔ Δ' i 0 u = 0) ∧
      ∀ f : A, (∀ l < N, Δ' i l f = 0) → f ∈ Q ^ N := by
    intro i
    apply GlobalTheory.T.exists_maximal_mem_pow_of_hasse_vanishing k A N (Δ' i) hN
    · rw [hΔ' i 0 hN0, h01 i, hone]
    · intro l hl u w
      rw [hΔ' i l hl, hleib i l u w, map_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' : p < l + 1 := Finset.mem_range.1 hp
      rw [hmul _ (hSΔ i p (by omega) u) _ (hSΔ i (l - p) (by omega) w),
        hΔ' i p (by omega), hΔ' i (l - p) (by omega)]
    · obtain ⟨π, hπ'⟩ := hπ i
      exact ⟨π, by rw [hΔ' i 1 hN1, hπ', hone]⟩
  choose Q' hQmax hQmem hQpow using hjet
  have hunit : ∀ x ∈ S, IsUnit x → Ring.inverse x ∈ S → L x ≠ 0 :=
    fun x hx hu hi => GenericSpecialHasse.ext_unit_ne S L hone hmul x hx hu hi
  let f : A := ∑ j, L (y j) • v j
  refine ⟨Q', f, hQmax, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro i i' hii'
    by_contra hne
    have hu := hus (i, i') hne
    set u := us (i, i')
    have heqv := GenericSpecialHasse.lin_eq_of_zero_iff (Δ' i 0) (Δ' i' 0)
      (by rw [hΔ' i 0 hN0, h01 i, hone]) (by rw [hΔ' i' 0 hN0, h01 i', hone])
      (fun w => by rw [← hQmem, ← hQmem, hii']) u
    rw [hΔ' i 0 hN0, hΔ' i' 0 hN0] at heqv
    refine hunit _ (S.sub_mem (hSΔ i 0 hN0 u) (hSΔ i' 0 hN0 u)) hu
      (hTS _ (by simp only [T, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl (Or.inl (Or.inr ⟨(i, i'), Finset.mem_univ _, rfl⟩))))) ?_
    rw [map_sub, heqv, sub_self]
  · intro i hiP
    have hu := huξ i
    have heqv := GenericSpecialHasse.lin_eq_of_zero_iff (Δ' i 0) φ.toLinearMap
      (by rw [hΔ' i 0 hN0, h01 i, hone]) (map_one φ)
      (fun w => by rw [← hQmem, hiP, hφ]; rfl) (uξ i)
    rw [hΔ' i 0 hN0, AlgHom.toLinearMap_apply, ← hLξ] at heqv
    refine hunit _ (S.sub_mem (hSΔ i 0 hN0 _) (hξS _)) hu
      (hTS _ (by simp only [T, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl (Or.inr ⟨i, Finset.mem_univ _, rfl⟩)))) ?_
    rw [map_sub, heqv, sub_self]
  · intro i hDQ
    have h0 : Δ' i 0 (uD i) = 0 := (hQmem i _).1 (hDQ (huDmem i))
    rw [hΔ' i 0 hN0] at h0
    exact hunit _ (hSΔ i 0 hN0 _) (huD i)
      (hTS _ (by simp only [T, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inr ⟨i, Finset.mem_univ _, rfl⟩))) h0
  · intro hDP
    have h0 : φ u0 = 0 := (hφ u0).1 (hDP hu0D)
    rw [← hLξ] at h0
    exact hunit _ (hξS _) hu0 (hTS _ (by simp [T])) h0
  · exact Submodule.sum_mem _ fun j _ => V.smul_mem _ (hvV j)
  · intro hf
    have := (Fintype.linearIndependent_iff.1 hli) (fun j => L (y j)) hf j0
    exact hunit _ (hy j0) hj0 (hTS _ (by simp [T])) this
  · apply (hφ f).2
    have : φ f = L (∑ j, y j * ξ (v j)) := by
      simp only [f, map_sum, map_smul, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hmul _ (hy j) _ (hξS _), hLξ]
    rw [this, heq0, map_zero]
  · intro i
    apply hQpow i
    intro l hl
    have : Δ' i l f = L (∑ j, y j * Δ i l (v j)) := by
      simp only [f, map_sum, map_smul, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hmul _ (hy j) _ (hSΔ i l hl _), hΔ' i l hl]
    rw [this, heqΔ i l hl, map_zero]

end GlobalTheory.PicDiv

namespace GlobalTheory.PicDiv

theorem classGroup_mk0_mul_mul_pow_eq_one_of_span_eq {A : Type} [CommRing A] [IsDedekindDomain A]
    (N : ℕ) (P D C : Ideal A) (f : A) (hP : P ∈ nonZeroDivisors (Ideal A))
    (hD : D ∈ nonZeroDivisors (Ideal A)) (hC : C ∈ nonZeroDivisors (Ideal A))
    (h : Ideal.span {f} = P * D * C ^ N) :
    ClassGroup.mk0 ⟨P, hP⟩ * ClassGroup.mk0 ⟨D, hD⟩ * ClassGroup.mk0 ⟨C, hC⟩ ^ N = 1 := by
  rw [← map_pow, ← map_mul, ← map_mul]
  have hm : P * D * C ^ N ∈ nonZeroDivisors (Ideal A) :=
    mul_mem (mul_mem hP hD) (pow_mem hC N)
  have e : (⟨P, hP⟩ * ⟨D, hD⟩ * ⟨C, hC⟩ ^ N : nonZeroDivisors (Ideal A)) = ⟨P * D * C ^ N, hm⟩ :=
    Subtype.ext (by simp)
  rw [e, ClassGroup.mk0_eq_one_iff, ← h]
  exact ⟨⟨f, rfl⟩⟩

theorem prod_maximal_mem_nonZeroDivisors {A : Type} [CommRing A] [IsDedekindDomain A]
    {I : Type} [Fintype I] (Q : I → Ideal A) (hQ : ∀ i, (Q i).IsMaximal)
    (P₀ : Ideal A) (hP₀ : P₀.IsMaximal) (h₀ : P₀ ≠ ⊥) :
    (∏ i, Q i) ∈ nonZeroDivisors (Ideal A) := by
  refine prod_mem fun i _ => mem_nonZeroDivisors_of_ne_zero ?_
  intro hi
  have hb : (⊥ : Ideal A).IsMaximal := by
    have := hQ i
    rwa [hi] at this
  exact h₀ (hb.eq_of_le hP₀.ne_top bot_le).symm

theorem exists_classGroup_mk0_eq_mul_pow_reduced :
    ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A]
      [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A]
      [Module.Free k[X] A], (∃ δ : k[X], δ ≠ 0 ∧ ∀ α : k, δ.eval α ≠ 0 → ∀ Q : Ideal A, Q.IsMaximal → algebraMap k[X] A (X - C α) ∉ Q ^ 2) → ∀ (N : ℕ), 2 ≤ N → (N : k) ≠ 0 → ∀ P₀ : Ideal A, P₀.IsMaximal →
      ∀ h₀ : P₀ ∈ nonZeroDivisors (Ideal A), ∃ a : A, a ≠ 0 ∧ ∀ P : Ideal A, P.IsMaximal →
        a ∉ P → ∀ h : P ∈ nonZeroDivisors (Ideal A), ∃ d : ClassGroup A,
          ClassGroup.mk0 ⟨P, h⟩ = ClassGroup.mk0 ⟨P₀, h₀⟩ * d ^ N := by
  intro k A _ _ _ _ _ _ _ _ _ hred N hN hNk P₀ hP₀ h₀
  haveI : Algebra.FiniteType k A :=
    Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
  obtain ⟨r, V, D, Q, f₀, hset, hdeg⟩ := GlobalTheory.PicDiv.linear_system_setup k A hred N P₀ (by omega) hP₀
  have hform := GlobalTheory.PicDiv.FormalDeformHasse.formal_deformation k A N (Fin r) V D P₀ Q f₀ hN hNk hP₀ hset
  obtain ⟨a, ha, hall⟩ := GlobalTheory.PicDiv.specialise_generic_solution_hasse k A (PowerSeries k) N (Fin r) V D hN hform
  obtain ⟨-, hVD, hQ, -, -, -, -, -, hf₀, hspan₀, -⟩ := hset
  refine ⟨a, ha, fun P hP haP h => ?_⟩
  obtain ⟨Q', f, hQ', hinj, hne, hDQ', hDP, hfV, hf, hfP, hfQ'⟩ := hall P hP haP
  have hspan := GlobalTheory.PicDiv.degree_count_generates k A N (Fin r) D P₀ P Q Q' f₀ f hP₀ hP hQ hQ' hinj hne hDQ' hDP
    hf₀ hf hspan₀ (hVD f hfV) hfP hfQ' (hdeg f hfV hf)
  have hP₀ne : P₀ ≠ ⊥ := nonZeroDivisors.ne_zero h₀
  have hD : D ∈ nonZeroDivisors (Ideal A) := by
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro hD0
    apply hDP
    rw [hD0]
    exact bot_le
  have hC := prod_maximal_mem_nonZeroDivisors Q hQ P₀ hP₀ hP₀ne
  have hC' := prod_maximal_mem_nonZeroDivisors Q' hQ' P₀ hP₀ hP₀ne
  rw [Finset.prod_pow] at hspan hspan₀
  have e := classGroup_mk0_mul_mul_pow_eq_one_of_span_eq N P D _ f h hD hC' hspan
  have e₀ := classGroup_mk0_mul_mul_pow_eq_one_of_span_eq N P₀ D _ f₀ h₀ hD hC hspan₀
  refine ⟨ClassGroup.mk0 ⟨_, hC⟩ / ClassGroup.mk0 ⟨_, hC'⟩, ?_⟩
  generalize ClassGroup.mk0 ⟨P, h⟩ = p at e ⊢
  generalize ClassGroup.mk0 ⟨P₀, h₀⟩ = p₀ at e₀ ⊢
  generalize ClassGroup.mk0 ⟨D, hD⟩ = d at e e₀
  generalize ClassGroup.mk0 ⟨_, hC⟩ = c at e₀ ⊢
  generalize ClassGroup.mk0 ⟨_, hC'⟩ = c' at e ⊢
  have e' : p * c' ^ N = p₀ * c ^ N := by
    apply mul_right_cancel (b := d)
    rw [mul_right_comm p, mul_right_comm p₀, e, e₀]
  rw [div_pow, ← mul_div_assoc, ← e', mul_div_cancel_right]

end GlobalTheory.PicDiv

namespace GlobalTheory.PicDiv

theorem injective_of_finite_not_field (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B]
    [Algebra k B] (y : B) (hfin : (Polynomial.aeval (R := k) y).Finite) (hB : ¬ IsField B) :
    Function.Injective (Polynomial.aeval (R := k) y) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  by_contra hp0
  have hint : IsIntegral k y := (isAlgebraic_iff_isIntegral).mp ⟨p, hp0, hp⟩
  have hdeg : (minpoly k y).natDegree = 1 := by
    have := IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)
    exact Polynomial.natDegree_eq_of_degree_eq_some this
  obtain ⟨r, hr⟩ := (minpoly.natDegree_eq_one_iff).mp hdeg
  letI : Algebra k[X] B := (Polynomial.aeval y).toRingHom.toAlgebra
  haveI : Module.Finite k[X] B := hfin
  have hsmul : ∀ (q : k[X]) (b : B), q • b = (q.eval r) • b := by
    intro q b
    rw [Algebra.smul_def, Algebra.smul_def]
    change Polynomial.aeval y q * b = _
    rw [← hr, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_def]
    rfl
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := k[X]) (M := B)
  have hk : Submodule.span k (s : Set B) = ⊤ := by
    have key : ∀ b ∈ Submodule.span k[X] (s : Set B), b ∈ Submodule.span k (s : Set B) := by
      intro b hb
      induction hb using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span hx
      | zero => exact zero_mem _
      | add x z _ _ hx hz => exact add_mem hx hz
      | smul q x _ hx => rw [hsmul]; exact Submodule.smul_mem _ _ hx
    rw [eq_top_iff]
    intro b _
    exact key b (by rw [hs]; trivial)
  haveI : Module.Finite k B := ⟨⟨s, hk⟩⟩
  exact hB ((Algebra.IsIntegral.isField_iff_isField (algebraMap k B).injective).mp (Field.toIsField k))

end GlobalTheory.PicDiv

namespace GlobalTheory.PicDiv

theorem pic_divisible : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ c : CommRing.Pic B, ∃ d, d ^ q = c := by
  intro k B _ _ _ _ _ _ _ q hq c
  suffices h : ∀ c : ClassGroup B, ∃ d, d ^ q = c by
    obtain ⟨d, hd⟩ := h ((ClassGroup.equivPic B).symm c)
    exact ⟨ClassGroup.equivPic B d, by rw [← map_pow, hd, MulEquiv.apply_symm_apply]⟩
  intro c
  have hNk : (q : k) ≠ 0 := hq.ne_zero
  have hq0 : q ≠ 0 := by rintro rfl; exact hNk (by simp)
  by_cases hfield : IsField B
  · refine ⟨1, ?_⟩
    obtain ⟨⟨I, hI⟩, rfl⟩ := ClassGroup.mk0_surjective c
    rw [one_pow, eq_comm, ClassGroup.mk0_eq_one_iff]
    have hI0 : I ≠ ⊥ := nonZeroDivisors.ne_zero hI
    obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
    have hu : IsUnit x := by
      obtain ⟨z, hz⟩ := hfield.mul_inv_cancel hx0
      exact isUnit_iff_exists_inv.mpr ⟨z, hz⟩
    rw [Ideal.eq_top_of_isUnit_mem I hxI hu]
    exact ⟨⟨1, by simp⟩⟩
  rcases Nat.lt_or_ge q 2 with h1 | h2
  · have : q = 1 := by omega
    subst this; exact ⟨c, pow_one c⟩
  obtain ⟨y, hfin, hred⟩ := GlobalTheory.T.exists_separable_normalization_reduced_fibers k B hfield
  letI : Algebra k[X] B := (Polynomial.aeval y).toRingHom.toAlgebra
  have hmap : ∀ p : k[X], algebraMap k[X] B p = Polynomial.aeval y p := fun p => rfl
  haveI : IsScalarTower k k[X] B := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [hmap, Polynomial.algebraMap_eq, Polynomial.aeval_C])
  haveI : Module.Finite k[X] B := hfin
  have hinj : Function.Injective (algebraMap k[X] B) := injective_of_finite_not_field k B y hfin hfield
  haveI : Module.IsTorsionFree k[X] B := (NoZeroSMulDivisors.iff_algebraMap_injective).mpr hinj
  haveI : Module.Free k[X] B := Module.free_of_finite_type_torsion_free'
  have hred' : (∃ δ : k[X], δ ≠ 0 ∧ ∀ α : k, δ.eval α ≠ 0 → ∀ Q : Ideal B, Q.IsMaximal → algebraMap k[X] B (X - C α) ∉ Q ^ 2) := by
    obtain ⟨δ, hδ0, hδ⟩ := hred
    refine ⟨δ, hδ0, fun α hα Q hQ => ?_⟩
    rw [hmap, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
    exact hδ α hα Q hQ
  have key := exists_classGroup_mk0_eq_mul_pow_reduced k B hred' q h2 hNk
  obtain ⟨f, hf0, hfmod⟩ := GlobalTheory.T.exists_finrank_quotient_span_mod_eq_one' k B q (by omega)
  obtain ⟨d, hd⟩ := classGroup_nthPower_of_codim_one_mod k B q (by omega) key ⟨f, hf0, hfmod⟩ c
  exact ⟨d, hd.symm⟩

end GlobalTheory.PicDiv
end

section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pic_divisible_dedekind_finiteType_algClosed : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ c : CommRing.Pic B, ∃ d, d ^ q = c := by
  first | (exact @GlobalTheory.PicDiv.pic_divisible) | (exact GlobalTheory.PicDiv.pic_divisible) | (intros; apply GlobalTheory.PicDiv.pic_divisible  <;> assumption)
end

section
open Polynomial

namespace GlobalTheory.PicDiv

theorem classGroup_divisible : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B]
    [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), (q : k) ≠ 0 →
    ∀ c : ClassGroup B, ∃ d : ClassGroup B, d ^ q = c := by
  intro k B _ _ _ _ _ _ _ q hq c
  obtain ⟨d, hd⟩ := GlobalTheory.T.pic_divisible_dedekind_finiteType_algClosed k B q (Ne.isUnit hq) (ClassGroup.equivPic B c)
  refine ⟨(ClassGroup.equivPic B).symm d, ?_⟩
  apply (ClassGroup.equivPic B).injective
  rw [map_pow, MulEquiv.apply_symm_apply, hd]

end GlobalTheory.PicDiv
end

section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classGroup_dedekind_algClosed_divisible : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), (q : k) ≠ 0 → ∀ c : ClassGroup B, ∃ d : ClassGroup B, d ^ q = c := by
  first | (exact @GlobalTheory.PicDiv.classGroup_divisible) | (exact GlobalTheory.PicDiv.classGroup_divisible) | (intros; apply GlobalTheory.PicDiv.classGroup_divisible <;> assumption)
end
