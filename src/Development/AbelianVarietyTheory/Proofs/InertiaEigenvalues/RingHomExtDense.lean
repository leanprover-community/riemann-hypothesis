import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.AcrisPrism

variable {l : ℕ} [hl : Fact l.Prime]

theorem exists_eq_l_mul_of_natCast {A : Type} [CommRing A] (htf : ∀ x : A, (l : A) * x = 0 → x = 0)
    {m k : ℕ} (hm : m ≠ 0) (hv : padicValNat l m < padicValNat l k) {y z : A}
    (h : (m : A) * y = (k : A) * z) : ∃ w, y = l * w := by
  have hp := hl.out
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hv
  have htf' : ∀ (j : ℕ) (x : A), (l : A) ^ j * x = 0 → x = 0 := fun j => by
    induction j with
    | zero => simp
    | succ j ih => exact fun x hx => htf x (ih _ (by linear_combination hx))
  rw [← Nat.factorization_def m hp, ← Nat.factorization_def k hp] at hv
  have hm' := Nat.ordProj_mul_ordCompl_eq_self m l
  have hk' := Nat.ordProj_mul_ordCompl_eq_self k l
  have hcop := Nat.coprime_ordCompl hp hm
  generalize m / l ^ m.factorization l = m' at hm' hcop
  generalize k / l ^ k.factorization l = k' at hk'
  generalize m.factorization l = a at hm' hv
  generalize k.factorization l = b at hk' hv
  subst hm' hk'
  push_cast at h
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have huv' : (u : A) * l + (v : A) * m' = 1 := by
    have := congrArg (Int.cast : ℤ → A) huv
    push_cast at this
    exact this
  have e : (l : A) ^ b = (l : A) ^ a * ((l : A) ^ (b - a - 1) * l) := by
    rw [← pow_succ, ← pow_add]
    congr 1
    omega
  have h1 : (m' : A) * y = (l : A) ^ (b - a - 1) * l * k' * z := by
    apply sub_eq_zero.1
    apply htf' a
    rw [e] at h
    linear_combination h
  exact ⟨u * y + v * (l : A) ^ (b - a - 1) * k' * z, by linear_combination (-y) * huv' + (v : A) * h1⟩

theorem cong_add {A : Type} [CommRing A] (φ : A →+* A) {a b : A} (ha : ∃ w, φ a = a ^ l + (l : A) * w)
    (hb : ∃ w, φ b = b ^ l + (l : A) * w) : ∃ w, φ (a + b) = (a + b) ^ l + (l : A) * w := by
  obtain ⟨w, hw⟩ := ha
  obtain ⟨w', hw'⟩ := hb
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl.out a b
  exact ⟨w + w' - a * b * r, by rw [map_add, hw, hw', hr]; ring⟩

theorem cong_mul {A : Type} [CommRing A] (φ : A →+* A) {a b : A} (ha : ∃ w, φ a = a ^ l + (l : A) * w)
    (hb : ∃ w, φ b = b ^ l + (l : A) * w) : ∃ w, φ (a * b) = (a * b) ^ l + (l : A) * w := by
  obtain ⟨w, hw⟩ := ha
  obtain ⟨w', hw'⟩ := hb
  exact ⟨a ^ l * w' + w * b ^ l + (l : A) * w * w', by rw [map_mul, hw, hw']; ring⟩

theorem frobC_ainfToAcris (b : Ainf l) :
    frobC l (ainfToAcris l b) = ainfToAcris l (WittVector.frobenius b) := by
  rw [← GlobalTheory.RingBasics.φA_apply]
  exact (GlobalTheory.CrisMaps.phiA_extends l).alg b

theorem cong_ainf (b : Ainf l) :
    ∃ w, frobC l (ainfToAcris l b) = ainfToAcris l b ^ l + (l : Per.Acris l) * w := by
  obtain ⟨c, hc⟩ := frobenius_eq_pow_add b
  exact ⟨ainfToAcris l c, by rw [frobC_ainfToAcris, hc, map_add, map_pow, map_mul, map_natCast]⟩

theorem frob_mem_of_theta {x : Ainf l} (hx : Per.θ l x = 0) :
    ∃ u, ainfToAcris l (WittVector.frobenius x) = (l : Per.Acris l) * u := by
  obtain ⟨c, hc⟩ := frobenius_eq_pow_add x
  obtain ⟨d, hd⟩ := exists_dpow hx l
  have hf : (l.factorial : Per.Acris l) = (l : Per.Acris l) * ((l - 1).factorial : Per.Acris l) := by
    rw [← Nat.cast_mul, Nat.mul_factorial_pred hl.out.ne_zero]
  refine ⟨((l - 1).factorial : Per.Acris l) * d + ainfToAcris l c, ?_⟩
  rw [hc, map_add, map_pow, ← hd, map_mul, map_natCast, hf]
  ring

theorem padicValNat_factorial_bound {n : ℕ} (hn : n ≠ 0) :
    l * padicValNat l n.factorial < padicValNat l n.factorial + n := by
  have h := sub_one_mul_padicValNat_factorial (p := l) n
  have hlast := Nat.getLast_digit_ne_zero l hn
  have hpos : 0 < (l.digits n).sum :=
    lt_of_lt_of_le (Nat.pos_of_ne_zero hlast) (List.le_sum_of_mem (List.getLast_mem _))
  have h2 : 2 ≤ l := hl.out.two_le
  generalize padicValNat l n.factorial = v at h ⊢
  generalize (l.digits n).sum = s at h hpos
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h
  have e : (k + 1) * v = k * v + v := by ring
  rw [e]
  generalize k * v = t at h ⊢
  omega

theorem cong_gen {x : Ainf l} (hx : Per.θ l x = 0) {n : ℕ} {Y : Per.Acris l}
    (hY : (n.factorial : Per.Acris l) * Y = ainfToAcris l x ^ n) :
    ∃ w, frobC l Y = Y ^ l + (l : Per.Acris l) * w := by
  have htf := (GlobalTheory.MemLoc.acris_basic l).2.1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Y = 1 := by simpa using hY
    exact ⟨0, by rw [this]; simp⟩
  obtain ⟨u, hu⟩ := frob_mem_of_theta hx
  obtain ⟨w1, hw1⟩ : ∃ w, frobC l Y = (l : Per.Acris l) * w := by
    have h1 := congrArg (frobC l) hY
    rw [map_mul, map_natCast, map_pow, frobC_ainfToAcris, hu, mul_pow] at h1
    refine exists_eq_l_mul_of_natCast htf (Nat.factorial_ne_zero n) (k := l ^ n) (z := u ^ n) ?_ ?_
    · rw [padicValNat.prime_pow]
      exact padicValNat_factorial_lt_of_ne_zero l hn.ne'
    · rw [h1]; push_cast; rfl
  obtain ⟨w2, hw2⟩ : ∃ w, Y ^ l = (l : Per.Acris l) * w := by
    obtain ⟨d, hd⟩ := exists_dpow hx (l * n)
    have h2 : ((n.factorial ^ l : ℕ) : Per.Acris l) * Y ^ l = ((l * n).factorial : ℕ) * d := by
      rw [hd, Nat.cast_pow, ← mul_pow, hY, ← pow_mul, mul_comm n l]
    refine exists_eq_l_mul_of_natCast htf (pow_ne_zero _ (Nat.factorial_ne_zero n)) ?_ h2
    rw [padicValNat.pow n.factorial l, padicValNat_factorial_mul]
    exact padicValNat_factorial_bound hn.ne'
  exact ⟨w1 - w2, by rw [hw1, hw2]; ring⟩

theorem cong_acris0 : ∀ (s : Per.AinfP l) (hs : s ∈ Per.Acris0 l),
    ∃ w, frobC l (algebraMap (Per.Acris0 l) (Per.Acris l) ⟨s, hs⟩) =
      (algebraMap (Per.Acris0 l) (Per.Acris l) ⟨s, hs⟩) ^ l + (l : Per.Acris l) * w := by
  intro s hs
  let S : Subalgebra (Per.Ainf l) (Per.Acris0 l) :=
    { carrier := {t | ∃ w, frobC l (algebraMap (Per.Acris0 l) (Per.Acris l) t) =
        (algebraMap (Per.Acris0 l) (Per.Acris l) t) ^ l + (l : Per.Acris l) * w}
      mul_mem' := fun {x y} hx hy => by
        change ∃ w, frobC l (algebraMap (Per.Acris0 l) (Per.Acris l) (x * y)) =
          (algebraMap (Per.Acris0 l) (Per.Acris l) (x * y)) ^ l + (l : Per.Acris l) * w
        rw [map_mul]
        exact cong_mul (frobC l).toRingHom hx hy
      add_mem' := fun {x y} hx hy => by
        change ∃ w, frobC l (algebraMap (Per.Acris0 l) (Per.Acris l) (x + y)) =
          (algebraMap (Per.Acris0 l) (Per.Acris l) (x + y)) ^ l + (l : Per.Acris l) * w
        rw [map_add]
        exact cong_add (frobC l).toRingHom hx hy
      algebraMap_mem' := fun r => by
        change ∃ w, frobC l (algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) r)) =
          (algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) r)) ^ l +
            (l : Per.Acris l) * w
        rw [← GlobalTheory.RingIface.tower]
        exact cong_ainf r }
  have hle : Per.Acris0 l ≤ S.map (Per.Acris0 l).val := by
    refine GlobalTheory.RingIface.acris0_le_3 l _ fun x hx n y hy hn => ?_
    refine Subalgebra.mem_map.2 ⟨⟨y, hy⟩, ?_, rfl⟩
    refine cong_gen hx (n := n) ?_
    have h1 : ((n.factorial : ℕ) : Per.Acris0 l) * ⟨y, hy⟩ =
        algebraMap (Per.Ainf l) (Per.Acris0 l) x ^ n := Subtype.ext (by simpa using hn)
    have h2 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) h1
    rw [map_mul, map_natCast, map_pow, ← GlobalTheory.RingIface.tower] at h2
    exact h2
  obtain ⟨t, ht, e⟩ := Subalgebra.mem_map.1 (hle hs)
  have e' : (⟨s, hs⟩ : Per.Acris0 l) = t := Subtype.ext e.symm
  rw [e']
  exact ht

theorem frobC_cong (y : Per.Acris l) : ∃ w, frobC l y = y ^ l + (l : Per.Acris l) * w := by
  obtain ⟨s, z, rfl⟩ := (GlobalTheory.MemLoc.acris_basic l).2.2.1 y 1
  obtain ⟨w, hw⟩ := cong_acris0 s.1 s.2
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (algebraMap (Per.Acris0 l) (Per.Acris l) s + (l : Per.Acris l) ^ 1 * z)
    (algebraMap (Per.Acris0 l) (Per.Acris l) s) l
  refine ⟨w + frobC l z - z * c, ?_⟩
  rw [map_add, map_mul, map_pow, map_natCast, hw]
  linear_combination -hc

end GlobalTheory.AcrisPrism

namespace GlobalTheory.AcrisPrism

variable (l : ℕ) [hl : Fact l.Prime]

def acrisDelta : Delta l (Per.Acris l) :=
  Delta.ofLift l (frobC l).toRingHom (GlobalTheory.MemLoc.acris_basic l).2.1 fun a => frobC_cong a

theorem isUnit_delta_l : IsUnit ((acrisDelta l).δ (l : Per.Acris l)) := by
  have h := (acrisDelta l).φ_eq (l : Per.Acris l)
  have h1 : (acrisDelta l).φ (l : Per.Acris l) = l := map_natCast _ _
  rw [h1] at h
  have htf := (GlobalTheory.MemLoc.acris_basic l).2.1
  have e : (l : Per.Acris l) ^ l = (l : Per.Acris l) ^ 2 * (l : Per.Acris l) ^ (l - 2) := by
    rw [← pow_add]
    congr 1
    have := hl.out.two_le
    omega
  have h2 : (acrisDelta l).δ (l : Per.Acris l) = (l : Per.Acris l) * (-(l : Per.Acris l) ^ (l - 2)) + 1 := by
    apply sub_eq_zero.1
    apply htf
    linear_combination -h - e
  haveI := (GlobalTheory.MemLoc.acris_basic l).1
  rw [h2]
  exact Ideal.mem_jacobson_bot.1
    (IsAdicComplete.le_jacobson_bot _ (Ideal.mem_span_singleton_self (l : Per.Acris l))) _

theorem l_mem_nonZeroDivisors : (l : Per.Acris l) ∈ nonZeroDivisors (Per.Acris l) := by
  have htf := (GlobalTheory.MemLoc.acris_basic l).2.1
  exact mem_nonZeroDivisors_iff.2 ⟨htf, fun x hx => htf x (by rw [mul_comm, hx])⟩

def ainfPhiToAcris : Ainf l →+* Per.Acris l := (ainfToAcris l).toRingHom.comp WittVector.frobenius

theorem ainfPhiToAcris_le (F : FinExt l) :
    (ainfObj F).I ≤ (Ideal.span {(l : Per.Acris l)}).comap (ainfPhiToAcris l) := by
  intro a ha
  have hx : Per.θ l a = 0 := RingHom.mem_ker.1 ha
  obtain ⟨u, hu⟩ := frob_mem_of_theta hx
  exact Ideal.mem_span_singleton'.2 ⟨u, by rw [mul_comm]; exact hu.symm⟩

def acrisObj (F : FinExt l) : Obj l ↥(OL F) :=
  Obj.ofDistinguished hl.out.pos (acrisDelta l) (l : Per.Acris l) (l_mem_nonZeroDivisors l)
    (isUnit_delta_l l) (by rw [sup_idem]; exact (GlobalTheory.MemLoc.acris_basic l).1)
    ⟨1, fun x _ => by
      have : ((l : ℕ) : Per.Acris l ⧸ Ideal.span {(l : Per.Acris l)}) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_span_singleton_self _
      simp [this]⟩
    ((Ideal.quotientMap (I := RingHom.ker (Per.θ l)) (Ideal.span {(l : Per.Acris l)}) (ainfPhiToAcris l) (ainfPhiToAcris_le l F)).comp
      (ainfObj F).str)

def acrisHom (F : FinExt l) : Hom (ainfObj F) (acrisObj l F) where
  f := ainfPhiToAcris l
  f_δ := Delta.map_δ_of_map_φ (ainfObj F).D (acrisDelta l) (GlobalTheory.MemLoc.acris_basic l).2.1 _
    fun a => (frobC_ainfToAcris (WittVector.frobenius a)).symm
  f_I := fun a ha => ainfPhiToAcris_le l F ha
  f_str := fun r a h => by
    change Ideal.Quotient.mk _ (ainfPhiToAcris l a) =
      Ideal.quotientMap (I := RingHom.ker (Per.θ l)) (Ideal.span {(l : Per.Acris l)}) (ainfPhiToAcris l)
        (ainfPhiToAcris_le l F) ((ainfObj F).str r)
    rw [← h]
    rfl

theorem main : ∀ (l : ℕ) [Fact l.Prime] (F : FinExt l), ∃ (C : Obj l ↥(OL F)) (eC : C.A ≃+* Per.Acris l) (h : GlobalTheory.Prism.Hom (ainfObj F) C), C.I = Ideal.span {(l : C.A)} ∧ (∀ x, eC (C.D.φ x) = frobC l (eC x)) ∧ ∀ x : Ainf l, eC (h.f x) = ainfToAcris l (WittVector.frobenius x) :=
  fun l _ F => ⟨acrisObj l F, RingEquiv.refl _, acrisHom l F, rfl, fun _ => rfl, fun _ => rfl⟩

end GlobalTheory.AcrisPrism
end
end

section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysEval

section Abstract

variable {B P R : Type} [CommRing B] [CommRing P] [CommRing R] (l : ℕ) (ι : B →+* P) (f : B →+* R)

def Approx (F : P) (r : ℕ) (y : R) : Prop :=
  ∃ (n : ℕ) (b : B) (p h : P), n ≠ 0 ∧ (n : P) * p = ι b ∧ F = p + (l : P) ^ r * h ∧ (n : R) * y = f b

variable {l ι f}

theorem approx_add {F G : P} {r : ℕ} {y z : R} (hF : Approx l ι f F r y) (hG : Approx l ι f G r z) :
    Approx l ι f (F + G) r (y + z) := by
  obtain ⟨n, b, p, h, hn, hp, hF, hy⟩ := hF
  obtain ⟨m, c, q, k, hm, hq, hG, hz⟩ := hG
  refine ⟨n * m, (m : B) * b + (n : B) * c, p + q, h + k, mul_ne_zero hn hm, ?_, ?_, ?_⟩
  · rw [map_add, map_mul, map_mul, map_natCast, map_natCast, ← hp, ← hq]; push_cast; ring
  · rw [hF, hG]; ring
  · rw [map_add, map_mul, map_mul, map_natCast, map_natCast, ← hy, ← hz]; push_cast; ring

theorem approx_mul {F G : P} {r : ℕ} {y z : R} (hF : Approx l ι f F r y) (hG : Approx l ι f G r z) :
    Approx l ι f (F * G) r (y * z) := by
  obtain ⟨n, b, p, h, hn, hp, hF, hy⟩ := hF
  obtain ⟨m, c, q, k, hm, hq, hG, hz⟩ := hG
  refine ⟨n * m, b * c, p * q, p * k + h * q + (l : P) ^ r * h * k, mul_ne_zero hn hm, ?_, ?_, ?_⟩
  · rw [map_mul, ← hp, ← hq]; push_cast; ring
  · rw [hF, hG]; ring
  · rw [map_mul, ← hy, ← hz]; push_cast; ring

theorem approx_ι (b : B) (r : ℕ) : Approx l ι f (ι b) r (f b) :=
  ⟨1, b, ι b, 0, one_ne_zero, by simp, by simp, by simp⟩

theorem approx_one (r : ℕ) : Approx l ι f 1 r 1 := by
  simpa using approx_ι (l := l) (ι := ι) (f := f) 1 r

theorem approx_zero (r : ℕ) : Approx l ι f 0 r 0 := by
  simpa using approx_ι (l := l) (ι := ι) (f := f) 0 r

variable (htf : ∀ (n : ℕ) (x : R), n ≠ 0 → (n : R) * x = 0 → x = 0)
  (hK : ∀ (n : ℕ) (b : B) (p : P), n ≠ 0 → (n : P) * p = ι b → ∃ y : R, (n : R) * y = f b) (hl0 : l ≠ 0)
include htf hK hl0

theorem approx_dvd {F : P} {r s : ℕ} (hrs : r ≤ s) {y z : R} (hy : Approx l ι f F r y)
    (hz : Approx l ι f F s z) : (l : R) ^ r ∣ y - z := by
  obtain ⟨n, b, p, h, hn, hp, hF, hy⟩ := hy
  obtain ⟨m, c, q, k, hm, hq, hF', hz⟩ := hz
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrs
  have h0 : p - q = (l : P) ^ r * ((l : P) ^ d * k - h) := by linear_combination hF' - hF
  have h1 : ((n * m * l ^ r : ℕ) : P) * ((l : P) ^ d * k - h) = ι ((m : B) * b - (n : B) * c) := by
    rw [map_sub, map_mul, map_mul, map_natCast, map_natCast, ← hp, ← hq]
    push_cast
    linear_combination ((n : P) * m) * h0.symm
  obtain ⟨w, hw⟩ := hK _ _ _ (mul_ne_zero (mul_ne_zero hn hm) (pow_ne_zero _ hl0)) h1
  refine ⟨w, (sub_eq_zero.1 (htf (n * m) _ (mul_ne_zero hn hm) ?_)).symm⟩
  rw [map_sub, map_mul, map_mul, map_natCast, map_natCast, ← hy, ← hz] at hw
  push_cast at hw ⊢
  linear_combination hw

variable [IsAdicComplete (Ideal.span {(l : R)}) R]
  (hD : ∀ (F : P) (r : ℕ), ∃ (n : ℕ) (b : B) (p h : P), n ≠ 0 ∧ (n : P) * p = ι b ∧ F = p + (l : P) ^ r * h)

omit htf hl0 in
include hD in
theorem exists_approx (F : P) (r : ℕ) : ∃ y, Approx l ι f F r y := by
  obtain ⟨n, b, p, h, hn, hp, hF⟩ := hD F r
  obtain ⟨y, hy⟩ := hK n b p hn hp
  exact ⟨y, n, b, p, h, hn, hp, hF, hy⟩

omit htf hK hl0 in
variable (l) in

theorem sep_l (x : R) (h : ∀ r : ℕ, (l : R) ^ r ∣ x) : x = 0 :=
  IsHausdorff.haus' (I := Ideal.span {(l : R)}) x fun n => by
    simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact h n

include hD in
theorem exists_lim (F : P) : ∃ L : R, ∀ r y, Approx l ι f F r y → (l : R) ^ r ∣ L - y := by
  choose y hy using exists_approx hK hD F
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(l : R)}) y (fun {m n} hmn => by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact approx_dvd htf hK hl0 hmn (hy m) (hy n))
  refine ⟨L, fun r z hz => ?_⟩
  have h1 := hL r
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
  have h2 := approx_dvd htf hK hl0 le_rfl (hy r) hz
  have e : L - z = (y r - z) - (y r - L) := by ring
  rw [e]
  exact dvd_sub h2 h1

include hD in

theorem exists_ringHom : ∃ E : P →+* R, ∀ F r y, Approx l ι f F r y → (l : R) ^ r ∣ E F - y := by
  choose L hL using exists_lim htf hK hl0 hD
  have key : ∀ F z, (∀ r, ∃ y, Approx l ι f F r y ∧ (l : R) ^ r ∣ z - y) → L F = z := fun F z hz =>
    sub_eq_zero.1 (sep_l l _ fun r => by
      obtain ⟨y, hy, hzy⟩ := hz r
      have e : L F - z = (L F - y) - (z - y) := by ring
      rw [e]
      exact dvd_sub (hL F r y hy) hzy)
  have h1 : L 1 = 1 := key 1 1 fun r => ⟨1, approx_one r, by simp⟩
  have h0 : L 0 = 0 := key 0 0 fun r => ⟨0, approx_zero r, by simp⟩
  have hm : ∀ F G, L (F * G) = L F * L G := by
    intro F G
    refine key _ _ fun r => ?_
    obtain ⟨y, hy⟩ := exists_approx hK hD F r
    obtain ⟨z, hz⟩ := exists_approx hK hD G r
    obtain ⟨c, hc⟩ := hL F r y hy
    obtain ⟨d, hd⟩ := hL G r z hz
    exact ⟨y * z, approx_mul hy hz, c * z + y * d + (l : R) ^ r * c * d, by
      linear_combination (L G) * hc + (y + (l : R) ^ r * c) * hd⟩
  have ha : ∀ F G, L (F + G) = L F + L G := by
    intro F G
    refine key _ _ fun r => ?_
    obtain ⟨y, hy⟩ := exists_approx hK hD F r
    obtain ⟨z, hz⟩ := exists_approx hK hD G r
    obtain ⟨c, hc⟩ := hL F r y hy
    obtain ⟨d, hd⟩ := hL G r z hz
    exact ⟨y + z, approx_add hy hz, c + d, by linear_combination hc + hd⟩
  exact ⟨{ toFun := L, map_one' := h1, map_zero' := h0, map_mul' := hm, map_add' := ha }, hL⟩

omit hK in
include hD in

theorem ringHom_ext_dense (G₁ G₂ : P →+* R) (h : ∀ b, G₁ (ι b) = G₂ (ι b)) : G₁ = G₂ := by
  ext F
  refine sub_eq_zero.1 (sep_l l _ fun r => ?_)
  obtain ⟨n, b, p, k, hn, hp, hF⟩ := hD F r
  have e1 : (n : R) * (G₁ p - G₂ p) = G₁ ((n : P) * p) - G₂ ((n : P) * p) := by
    rw [map_mul, map_mul, map_natCast, map_natCast]; ring
  have h1 : G₁ p = G₂ p := sub_eq_zero.1 (htf n _ hn (by rw [e1, hp, h, sub_self]))
  exact ⟨G₁ k - G₂ k, by rw [hF, map_add, map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, h1]; ring⟩

end Abstract

section Concrete

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [Algebra O K] (t : Wq l a →ₐ[ℤ_[l]] O)

variable (K) in

def embK (τ : ZMod a) : Wq l a →+* K := (algebraMap O K).comp (emb t τ).toRingHom

variable (l a) in

abbrev Bp : Type := Polynomial (Polynomial (Wq l a))

variable (K) in

def rhoK (τ : ZMod a) : Polynomial (Wq l a) →+* K⟦X⟧ :=
  (PowerSeries.map (embK K t τ)).comp Polynomial.coeToPowerSeries.ringHom

variable (K) in

def iotaP : Bp l a →+* (ZMod a → K⟦X⟧⟦X⟧) :=
  Pi.ringHom fun τ => (PowerSeries.map (rhoK K t τ)).comp Polynomial.coeToPowerSeries.ringHom

theorem coeff_iotaP (b : Bp l a) (τ : ZMod a) (i n : ℕ) :
    coeff n (coeff i (iotaP K t b τ)) = embK K t τ ((b.coeff i).coeff n) := by
  rw [show iotaP K t b τ = PowerSeries.map (rhoK K t τ) (b : (Polynomial (Wq l a))⟦X⟧) from rfl, coeff_map,
    Polynomial.coeff_coe, rhoK, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, coeff_map,
    Polynomial.coeff_coe]

theorem rhoK_eq_toAc [IsUltrametricDist K] [IsUnitBall O K] (q : Polynomial (Wq l a)) (τ : ZMod a) :
    rhoK K t τ q = (toAc t K (q : (Wq l a)⟦X⟧) τ : K⟦X⟧) := by
  ext n
  rw [coeff_toAc]
  simp [rhoK, embK, coeff_map, Polynomial.coeff_coe]

theorem charZero_K [NormedAlgebra ℚ_[l] K] : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective

theorem embK_injective [NormedAlgebra ℚ_[l] K] (τ : ZMod a) : Function.Injective (embK K t τ) := by
  have := charZero_K (l := l) (K := K)
  refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
  by_contra h0
  obtain ⟨m, v, hv, rfl⟩ := WittVector.exists_eq_pow_p_mul w h0
  have hu : IsUnit v := WittVector.isUnit_of_coeff_zero_ne_zero v hv
  rw [map_mul, map_pow, map_natCast] at hw
  exact mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero)) (hu.map _).ne_zero hw

include t in

theorem wq_nat_cancel [NormedAlgebra ℚ_[l] K] {n : ℕ} (hn : n ≠ 0) {x : Wq l a}
    (h : (n : Wq l a) * x = 0) : x = 0 := by
  have := charZero_K (l := l) (K := K)
  refine embK_injective (K := K) t 0 ?_
  have h1 := congrArg (embK K t 0) h
  rw [map_mul, map_natCast, map_zero] at h1
  rw [map_zero]
  exact (mul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 hn)

variable {e : ℕ} (ϖ : PiSys l e)

theorem ev_coe (q : Polynomial (Wq l a)) :
    ϖ.ev a (q : (Wq l a)⟦X⟧) = q.eval₂ (wA l a).toRingHom ϖ.teich := by
  have h := Polynomial.ringHom_ext (f := (ϖ.ev a).comp Polynomial.coeToPowerSeries.ringHom)
    (g := Polynomial.eval₂RingHom (wA l a).toRingHom ϖ.teich) (fun w => by simp) (by simp)
  exact RingHom.congr_fun h q

variable (a) in

def evC : Polynomial (Wq l a) →+* Per.Acris l :=
  ((ainfToAcris l).toRingHom.comp (ϖ.ev a)).comp Polynomial.coeToPowerSeries.ringHom

variable (a) in

def fP (g : GQ l) : Bp l a →+* Per.Acris l :=
  Polynomial.eval₂RingHom (evC a ϖ) (ainfToAcris l (ϖ.mu g * ϖ.teich))

end Concrete

end GlobalTheory.CrysEval
end
end
