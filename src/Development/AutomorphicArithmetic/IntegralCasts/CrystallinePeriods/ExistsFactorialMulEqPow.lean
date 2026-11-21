import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.TruncLogEqOfPowEqZero

section
noncomputable section

open Ideal
open scoped Nat

namespace Reformulated.AutPerF

universe u v w

section Adic

variable {A : Type u} [CommRing A]

theorem evalₐ_eq_zero_iff_dvd (a : A) (n : ℕ) (x : AdicCompletion (span {a}) A) :
    AdicCompletion.evalₐ (span {a}) n x = 0 ↔
      algebraMap A (AdicCompletion (span {a}) A) a ^ n ∣ x := by
  constructor
  · intro h
    have h1 : AdicCompletion.eval (span {a}) A n x = 0 := by
      rw [← AdicCompletion.factor_evalₐ_eq_eval (span {a}) x (by simp), h, map_zero]
    have h2 : x ∈ (span {a} ^ n • ⊤ : Submodule A (AdicCompletion (span {a}) A)) := by
      rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton a)]
      exact h1
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at h2
    obtain ⟨y, -, rfl⟩ := h2
    exact ⟨y, by rw [Algebra.smul_def, map_pow]⟩
  · rintro ⟨y, rfl⟩
    rw [map_mul, map_pow, AlgHom.commutes, Ideal.Quotient.algebraMap_eq, ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow (mem_span_singleton_self _) _), zero_mul]

theorem descFactorial_pred_modEq {m k : ℕ} (hk : k < m) :
    ∃ c : ℤ, ((m - 1).descFactorial k : ℤ) = (-1) ^ k * (k ! : ℤ) + m * c := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih (by omega)
    have h : ((m - 1 - k : ℕ) : ℤ) = m - (k + 1) := by omega
    refine ⟨(-1) ^ k * (k ! : ℤ) + (m - (k + 1)) * c, ?_⟩
    rw [Nat.descFactorial_succ, Nat.cast_mul, h, hc, Nat.factorial_succ]
    push_cast
    ring

theorem mul_sum_descFactorial {B : Type*} [CommRing B] [Algebra ℚ B] (m : ℕ) (x : B) :
    (m : B) * ∑ k ∈ Finset.range m,
      ((m - 1).descFactorial k : B) * ((((k + 1) ! : ℕ) : ℚ)⁻¹ • x ^ (k + 1)) = (x + 1) ^ m - 1 := by
  rw [add_pow, Finset.sum_range_succ', Finset.mul_sum]
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := Finset.mem_range.1 hk; omega⟩
  rw [← mul_assoc, ← Nat.cast_mul, Nat.add_sub_cancel, ← Nat.succ_descFactorial_succ,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, Algebra.smul_def,
    ← map_natCast (algebraMap ℚ B) (k + 1)!]
  have : algebraMap ℚ B ((k + 1)! : ℕ) * algebraMap ℚ B (((k + 1)! : ℕ) : ℚ)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero _), map_one]
  linear_combination (((m + 1).choose (k + 1) : ℕ) : B) * x ^ (k + 1) * this

end Adic

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

namespace AcrisZero

@[simp] theorem coe_gamma (n : ℕ) (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    (gamma n x hx : AinfInv p R) = AinfInv.gamma n (algebraMap _ _ x) := rfl

theorem p_pow_mul_cancel (n : ℕ) {x y : AcrisZero p R} (h : (p : AcrisZero p R) ^ n * x = p ^ n * y) :
    x = y := by
  apply Subtype.ext
  have h' := congrArg (Subtype.val) h
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast] at h'
  exact ((AinfInv.isUnit_p p).pow n).mul_left_cancel h'

theorem p_mul_cancel {x y : AcrisZero p R} (h : (p : AcrisZero p R) * x = p * y) : x = y :=
  p_pow_mul_cancel 1 (by simpa using h)

theorem mem_span_pow_iff (n : ℕ) (x : AcrisZero p R) :
    x ∈ span {(p : AcrisZero p R)} ^ n ↔ (p : AcrisZero p R) ^ n ∣ x := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem factorial_mul_gamma (n : ℕ) (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    (n ! : AcrisZero p R) * gamma n x hx = algebraMap (Ainf p R) _ x ^ n := by
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast, coe_gamma,
    AinfInv.gamma, Subalgebra.coe_algebraMap]
  rw [Algebra.smul_def, ← map_natCast (algebraMap ℚ (AinfInv p R)), ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero _), map_one, one_mul]

end AcrisZero

namespace Acris

theorem eval_surjective (n : ℕ) : Function.Surjective (eval p R n) :=
  AdicCompletion.surjective_evalₐ _ n

theorem factorPow_eval {m n : ℕ} (hle : m ≤ n) (x : Acris p R) :
    Ideal.Quotient.factorPow _ hle (eval p R n x) = eval p R m x :=
  factorPow_evalₐ _ hle x

theorem eval_eq_zero_iff (n : ℕ) (x : Acris p R) : eval p R n x = 0 ↔ (p : Acris p R) ^ n ∣ x := by
  have := evalₐ_eq_zero_iff_dvd (p : AcrisZero p R) n x
  rw [map_natCast] at this
  exact this

theorem ker_eval (n : ℕ) : RingHom.ker (eval p R n) = span {(p : Acris p R)} ^ n := by
  ext x
  rw [RingHom.mem_ker, eval_eq_zero_iff, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem exists_eq_add (n : ℕ) (x : Acris p R) :
    ∃ (a : AcrisZero p R) (y : Acris p R), x = algebraMap _ _ a + (p : Acris p R) ^ n * y := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (eval p R n x)
  obtain ⟨y, hy⟩ := (eval_eq_zero_iff n (x - algebraMap _ _ a)).1
    (by rw [map_sub, eval_algebraMap, ha, sub_self])
  exact ⟨a, y, by rw [← hy]; ring⟩

theorem eq_zero_of_forall_dvd {x : Acris p R} (h : ∀ n, (p : Acris p R) ^ n ∣ x) : x = 0 :=
  ext_eval fun n => by rw [(eval_eq_zero_iff n x).2 (h n), map_zero]

instance isAdicComplete : IsAdicComplete (span {(p : Acris p R)}) (Acris p R) := by
  have := AdicCompletion.isAdicComplete_self (span {(p : AcrisZero p R)})
    (Submodule.fg_span_singleton _)
  rw [Ideal.map_span, Set.image_singleton, map_natCast] at this
  exact this

theorem eq_zero_of_p_mul_eq_zero {x : Acris p R} (h : (p : Acris p R) * x = 0) : x = 0 := by
  refine ext_eval fun n => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (eval p R (n + 1) x)
  have h1 := congrArg (eval p R (n + 1)) h
  rw [map_mul, map_zero, map_natCast, ← ha,
    ← map_natCast (Ideal.Quotient.mk (span {(p : AcrisZero p R)} ^ (n + 1))), ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem, AcrisZero.mem_span_pow_iff] at h1
  obtain ⟨b, hb⟩ := h1
  have hab : a = p ^ n * b := AcrisZero.p_mul_cancel (by rw [hb]; ring)
  rw [← factorPow_eval (Nat.le_succ n), ← ha, map_zero]
  simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.eq_zero_iff_mem, AcrisZero.mem_span_pow_iff]
  exact ⟨b, hab⟩

theorem p_mul_cancel {x y : Acris p R} (h : (p : Acris p R) * x = p * y) : x = y :=
  sub_eq_zero.1 (eq_zero_of_p_mul_eq_zero (by rw [mul_sub, h, sub_self]))

theorem p_mem_nonZeroDivisors : (p : Acris p R) ∈ nonZeroDivisors (Acris p R) :=
  mem_nonZeroDivisors_iff_left.2 fun _ h => eq_zero_of_p_mul_eq_zero h

theorem p_pow_mul_cancel (n : ℕ) {x y : Acris p R} (h : (p : Acris p R) ^ n * x = p ^ n * y) :
    x = y :=
  sub_eq_zero.1 (mem_nonZeroDivisors_iff_left.1 (pow_mem p_mem_nonZeroDivisors n) _
    (by rw [mul_sub, h, sub_self]))

theorem hom_ext {B : Type*} [CommRing B] [IsHausdorff (span {(p : B)}) B] {f g : Acris p R →+* B}
    (h : ∀ a : AcrisZero p R, f (algebraMap _ _ a) = g (algebraMap _ _ a)) : f = g := by
  ext x
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : B)})]
  intro n
  obtain ⟨a, y, rfl⟩ := exists_eq_add n x
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  refine ⟨f y - g y, ?_⟩
  simp only [map_add, map_mul, map_pow, map_natCast, h]
  ring

theorem exists_quot (u : Ainf p R) (hu : Ainf.theta p R u = 1) (n : ℕ) :
    ∃ l : AcrisZero p R, (p : AcrisZero p R) ^ n * l = algebraMap (Ainf p R) _ u ^ p ^ n - 1 ∧
      eval p R n (log u hu) = Ideal.Quotient.mk _ l := by
  refine ⟨∑ k ∈ Finset.range (p ^ n), ((p ^ n - 1).descFactorial k : AcrisZero p R) *
    AcrisZero.gamma (k + 1) (u - 1) (by simp [hu]), ?_, ?_⟩
  · apply Subtype.ext
    have := mul_sum_descFactorial (p ^ n) (algebraMap (Ainf p R) (AinfInv p R) (u - 1))
    rw [← map_one (algebraMap (Ainf p R) (AinfInv p R)), ← map_add, sub_add_cancel, map_one,
      Nat.cast_pow] at this
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast,
      AddSubmonoidClass.coe_finset_sum, AcrisZero.coe_gamma, AinfInv.gamma,
      AddSubgroupClass.coe_sub, OneMemClass.coe_one, Subalgebra.coe_algebraMap]
    exact this
  · rw [eval_log u hu le_rfl, Ideal.Quotient.eq, logPartial, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun k hk => ?_
    rw [← sub_mul]
    refine Ideal.mul_mem_right _ _ ?_
    obtain ⟨c, hc⟩ := descFactorial_pred_modEq (Finset.mem_range.1 hk)
    have hc' := congrArg (Int.cast : ℤ → AcrisZero p R) hc
    push_cast at hc'
    rw [AcrisZero.mem_span_pow_iff, hc']
    exact ⟨-c, by ring⟩

theorem eval_log_of_mul_eq (u : Ainf p R) (hu : Ainf.theta p R u = 1) (n : ℕ) (l : AcrisZero p R)
    (hl : (p : AcrisZero p R) ^ n * l = algebraMap (Ainf p R) _ u ^ p ^ n - 1) :
    eval p R n (log u hu) = Ideal.Quotient.mk _ l := by
  obtain ⟨l', h1, h2⟩ := exists_quot u hu n
  rw [h2, AcrisZero.p_pow_mul_cancel n (h1.trans hl.symm)]

theorem log_congr {u v : Ainf p R} (hu : Ainf.theta p R u = 1) (hv : Ainf.theta p R v = 1)
    (h : u = v) : log u hu = log v hv := by subst h; rfl

theorem log_mul (u v : Ainf p R) (hu : Ainf.theta p R u = 1) (hv : Ainf.theta p R v = 1)
    (huv : Ainf.theta p R (u * v) = 1) : log (u * v) huv = log u hu + log v hv := by
  refine ext_eval fun n => ?_
  obtain ⟨a, ha, ha'⟩ := exists_quot u hu n
  obtain ⟨b, hb, hb'⟩ := exists_quot v hv n
  rw [map_add, ha', hb', eval_log_of_mul_eq _ huv n (a + b + p ^ n * a * b), ← map_add,
    Ideal.Quotient.eq, AcrisZero.mem_span_pow_iff]
  · exact ⟨a * b, by ring⟩
  · rw [map_mul, mul_pow, eq_add_of_sub_eq ha.symm, eq_add_of_sub_eq hb.symm]
    ring

@[simp] theorem log_one (h : Ainf.theta p R 1 = 1) : log (1 : Ainf p R) h = 0 :=
  ext_eval fun n => by rw [eval_log_of_mul_eq _ h n 0 (by simp), map_zero, map_zero]

theorem log_pow (u : Ainf p R) (hu : Ainf.theta p R u = 1) (m : ℕ)
    (hm : Ainf.theta p R (u ^ m) = 1) : log (u ^ m) hm = m * log u hu := by
  induction m with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul]; exact log_one _
  | succ m ih =>
    have h : Ainf.theta p R (u ^ m) = 1 := by rw [map_pow, hu, one_pow]
    rw [log_congr hm (by rw [map_mul, h, hu, one_mul]) (pow_succ u m), log_mul _ _ h hu, ih h]
    push_cast
    ring

theorem logTeich_mul (η η' : tateModule p R) : logTeich (η * η') = logTeich η + logTeich η' := by
  unfold logTeich
  rw [← log_mul _ _ _ _ (by
    rw [map_mul, Ainf.theta_teich, Ainf.theta_teich, show PreTilt.untilt η.1 = 1 from η.2,
      show PreTilt.untilt η'.1 = 1 from η'.2, one_mul])]
  exact log_congr _ _ (map_mul _ _ _)

@[simp] theorem logTeich_one : logTeich (1 : tateModule p R) = 0 :=
  (log_congr _ (map_one _) (map_one _)).trans (log_one _)

variable (p R) in

def logTeichHom : tateModule p R →* Multiplicative (Acris p R) where
  toFun η := Multiplicative.ofAdd (logTeich η)
  map_one' := by simp
  map_mul' η η' := by rw [logTeich_mul]; rfl

theorem logTeich_pow (η : tateModule p R) (m : ℕ) : logTeich (η ^ m) = m * logTeich η := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, logTeich_mul, ih]; push_cast; ring

end Acris

namespace BcrisPlus

theorem algebraMap_injective : Function.Injective (algebraMap (Acris p R) (BcrisPlus p R)) :=
  IsLocalization.injective (M := Submonoid.powers (p : Acris p R)) _
    (Submonoid.powers_le.2 Acris.p_mem_nonZeroDivisors)

end BcrisPlus

namespace Bcris

theorem logTeich_mul (η η' : tateModule p R) : logTeich (η * η') = logTeich η + logTeich η' := by
  simp [logTeich, Acris.logTeich_mul]

@[simp] theorem logTeich_one : logTeich (1 : tateModule p R) = 0 := by simp [logTeich]

theorem logTeich_pow (η : tateModule p R) (m : ℕ) : logTeich (η ^ m) = m * logTeich η := by
  simp [logTeich, Acris.logTeich_pow]

theorem isUnit_logTeich {ε : tateModule p R} (h : IsPrimitive ε) : IsUnit (logTeich ε) :=
  IsLocalization.map_units (M := BcrisPlus.periods p R) (Bcris p R)
    ⟨_, Submonoid.subset_closure ⟨ε, h, rfl⟩⟩

theorem isUnit_p : IsUnit (p : Bcris p R) := by
  simpa using (BcrisPlus.isUnit_p p R).map (algebraMap _ (Bcris p R))

end Bcris

end Reformulated.AutPerF
end
end

section
noncomputable section

open Ideal
open scoped Nat

namespace Reformulated.AutPerF

universe u v w

variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {U : Type w} [CommRing U] [Fact ¬IsUnit (p : U)] [IsAdicComplete (span {(p : U)}) U]

theorem exists_factorial_mul_eq_pow (n : ℕ) : ∃ a : ℤ_[p], (n ! : ℤ_[p]) * a = p ^ n := by
  have hp : p.Prime := Fact.out
  obtain ⟨v, m, hm, h⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero n) p hp.ne_one
  have hv : v ≤ n := by
    have h1 : v ≤ padicValNat p n ! :=
      (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).1 ⟨m, h⟩
    exact h1.trans (padicValNat_factorial_le p n)
  have hu : IsUnit (m : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.2 hm
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hv
  refine ⟨w * p ^ d, ?_⟩
  rw [h]
  push_cast
  linear_combination (p : ℤ_[p]) ^ (v + d) * hw

def tateModule.map (f : R →+* S) : tateModule p R →* tateModule p S where
  toFun η := ⟨Tilt.map p f η.1, by
    change PreTilt.untilt _ = 1
    rw [Tilt.untilt_map, show PreTilt.untilt η.1 = 1 from η.2, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

def PFlat.map (f : R →+* S) (ϖ : PFlat p R) : PFlat p S :=
  ⟨Tilt.map p f ϖ.1, by rw [Tilt.untilt_map, ϖ.2, map_natCast]⟩

variable {p}

@[simp] theorem tateModule.coe_map (f : R →+* S) (η : tateModule p R) :
    (tateModule.map p f η).1 = Tilt.map p f η.1 := rfl

@[simp] theorem tateModule.map_id (η : tateModule p R) : tateModule.map p (RingHom.id R) η = η :=
  Subtype.ext (Tilt.map_id _)

theorem tateModule.map_map (f : R →+* S) (g : S →+* U) (η : tateModule p R) :
    tateModule.map p g (tateModule.map p f η) = tateModule.map p (g.comp f) η :=
  Subtype.ext (Tilt.map_map _ _ _)

@[simp] theorem PFlat.coe_map (f : R →+* S) (ϖ : PFlat p R) :
    (PFlat.map p f ϖ).1 = Tilt.map p f ϖ.1 := rfl

@[simp] theorem PFlat.map_id (ϖ : PFlat p R) : PFlat.map p (RingHom.id R) ϖ = ϖ :=
  Subtype.ext (Tilt.map_id _)

theorem PFlat.map_map (f : R →+* S) (g : S →+* U) (ϖ : PFlat p R) :
    PFlat.map p g (PFlat.map p f ϖ) = PFlat.map p (g.comp f) ϖ :=
  Subtype.ext (Tilt.map_map _ _ _)

theorem PFlat.map_twist (f : R →+* S) (η : tateModule p R) (ϖ : PFlat p R) :
    PFlat.map p f (ϖ.twist η) = (PFlat.map p f ϖ).twist (tateModule.map p f η) :=
  Subtype.ext (map_mul (Tilt.map p f) _ _)

theorem IsPrimitive.map {ε : tateModule p R} (h : IsPrimitive ε) (f : R →+* S)
    (hf : Function.Injective f) : IsPrimitive (tateModule.map p f ε) := by
  unfold IsPrimitive at h ⊢
  rw [tateModule.coe_map, ← RingHom.map_frobeniusEquiv_symm, Tilt.untilt_map]
  exact fun h' => h (hf (by rw [h', map_one]))

omit [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S] in
theorem AinfInv.map_gamma (f : AinfInv p R →+* AinfInv p S) (n : ℕ) (x : AinfInv p R) :
    f (AinfInv.gamma n x) = AinfInv.gamma n (f x) := by
  simp [AinfInv.gamma, map_rat_smul]

omit [IsAdicComplete (span {(p : R)}) R] in
theorem AinfInv.factorial_mul_gamma (n : ℕ) (x : AinfInv p R) :
    (n ! : AinfInv p R) * AinfInv.gamma n x = x ^ n := by
  rw [AinfInv.gamma, Algebra.smul_def, ← map_natCast (algebraMap ℚ (AinfInv p R)), ← mul_assoc,
    ← map_mul, mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero _), map_one, one_mul]

omit [IsAdicComplete (span {(p : R)}) R] in
theorem AinfInv.eq_gamma {n : ℕ} {x y : AinfInv p R} (h : (n ! : AinfInv p R) * y = x ^ n) :
    AinfInv.gamma n x = y := by
  have hu : IsUnit (n ! : AinfInv p R) := by
    rw [← map_natCast (algebraMap ℚ (AinfInv p R))]
    exact (IsUnit.mk0 _ (by exact_mod_cast Nat.factorial_ne_zero _)).map _
  exact hu.mul_left_cancel (by rw [AinfInv.factorial_mul_gamma, h])

namespace AcrisZero

theorem extend_mem (ψ : Ainf p R →+* Ainf p S)
    (h : ∀ n x, Ainf.theta p R x = 0 → AinfInv.gamma n (algebraMap _ _ (ψ x)) ∈ acrisZero p S)
    {y : AinfInv p R} (hy : y ∈ acrisZero p R) : AinfInv.extend p ψ y ∈ acrisZero p S := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨n, x, hx, rfl⟩ := hy
    rw [AinfInv.map_gamma, AinfInv.extend_algebraMap]
    exact h n x hx
  | algebraMap r => rw [AinfInv.extend_algebraMap]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

def extend (ψ : Ainf p R →+* Ainf p S)
    (h : ∀ n x, Ainf.theta p R x = 0 → AinfInv.gamma n (algebraMap _ _ (ψ x)) ∈ acrisZero p S) :
    AcrisZero p R →+* AcrisZero p S where
  toFun y := ⟨AinfInv.extend p ψ y.1, extend_mem ψ h y.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem gamma_map_mem (f : R →+* S) (n : ℕ) (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    AinfInv.gamma n (algebraMap _ _ (Ainf.map p f x)) ∈ acrisZero p S :=
  (gamma n (Ainf.map p f x) (by rw [Ainf.theta_map, hx, map_zero])).2

theorem p_dvd_frob (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    (p : AcrisZero p R) ∣ algebraMap (Ainf p R) (AcrisZero p R) (Ainf.frob p R x) := by
  obtain ⟨y, hy⟩ := Ainf.p_dvd_frob_sub_pow x
  rw [eq_add_of_sub_eq hy, map_add, map_mul, map_natCast, map_pow, ← factorial_mul_gamma p x hx]
  refine dvd_add (dvd_mul_right _ _) (Dvd.dvd.mul_right ?_ _)
  exact Nat.cast_dvd_cast (Nat.dvd_factorial (Fact.out : p.Prime).pos le_rfl)

theorem gamma_p_mul_mem (n : ℕ) (z : AcrisZero p R) :
    AinfInv.gamma n ((p : AinfInv p R) * z.1) ∈ acrisZero p R := by
  obtain ⟨a, ha⟩ := exists_factorial_mul_eq_pow p n
  have ha' := congrArg ((algebraMap (Ainf p R) (AinfInv p R)).comp (algebraMap ℤ_[p] _)) ha
  rw [map_mul, map_pow, map_natCast, map_natCast, RingHom.comp_apply] at ha'
  rw [AinfInv.eq_gamma (y := algebraMap (Ainf p R) _ (algebraMap ℤ_[p] _ a) * z.1 ^ n)
    (by rw [← mul_assoc, ha', mul_pow])]
  exact mul_mem (Subalgebra.algebraMap_mem _ _) (pow_mem z.2 _)

theorem gamma_frob_mem (n : ℕ) (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    AinfInv.gamma n (algebraMap _ _ (Ainf.frob p R x)) ∈ acrisZero p R := by
  obtain ⟨z, hz⟩ := p_dvd_frob x hx
  have hz' := congrArg Subtype.val hz
  simp only [MulMemClass.coe_mul, SubringClass.coe_natCast, Subalgebra.coe_algebraMap] at hz'
  rw [hz']
  exact gamma_p_mul_mem n z

variable (p) in

def map (f : R →+* S) : AcrisZero p R →+* AcrisZero p S := extend (Ainf.map p f) (gamma_map_mem f)

variable (p R) in

def frob : AcrisZero p R →+* AcrisZero p R := extend (Ainf.frob p R) gamma_frob_mem

@[simp] theorem coe_map (f : R →+* S) (x : AcrisZero p R) :
    (map p f x : AinfInv p S) = AinfInv.map p f x := rfl

@[simp] theorem coe_frob (x : AcrisZero p R) : (frob p R x : AinfInv p R) = AinfInv.frob p R x := rfl

@[simp] theorem map_algebraMap (f : R →+* S) (x : Ainf p R) :
    map p f (algebraMap _ _ x) = algebraMap _ _ (Ainf.map p f x) :=
  Subtype.ext (AinfInv.map_algebraMap f x)

@[simp] theorem frob_algebraMap (x : Ainf p R) :
    frob p R (algebraMap _ _ x) = algebraMap _ _ (Ainf.frob p R x) :=
  Subtype.ext (AinfInv.frob_algebraMap x)

@[simp] theorem map_id (x : AcrisZero p R) : map p (RingHom.id R) x = x :=
  Subtype.ext (AinfInv.map_id _)

theorem map_map (f : R →+* S) (g : S →+* U) (x : AcrisZero p R) :
    map p g (map p f x) = map p (g.comp f) x :=
  Subtype.ext (AinfInv.map_map f g _)

theorem map_frob (f : R →+* S) (x : AcrisZero p R) :
    map p f (frob p R x) = frob p S (map p f x) :=
  Subtype.ext (AinfInv.map_frob f _)

end AcrisZero

namespace Acris

def extend (g : AcrisZero p R →+* AcrisZero p S) : Acris p R →+* Acris p S :=
  adicMap _ _ g (span_natCast_le_comap p g)

@[simp] theorem extend_algebraMap (g : AcrisZero p R →+* AcrisZero p S) (a : AcrisZero p R) :
    extend g (algebraMap _ _ a) = algebraMap _ _ (g a) :=
  adicMap_algebraMap _ _ g _ a

theorem eval_extend (g : AcrisZero p R →+* AcrisZero p S) (n : ℕ) (x : Acris p R) :
    eval p S n (extend g x) =
      Ideal.quotientMap _ g (pow_le_comap_pow (span_natCast_le_comap p g) n) (eval p R n x) :=
  evalₐ_adicMap _ _ g _ n x

theorem extend_log (g : AcrisZero p R →+* AcrisZero p S) (u : Ainf p R) (v : Ainf p S)
    (hu : Ainf.theta p R u = 1) (hv : Ainf.theta p S v = 1)
    (h : g (algebraMap _ _ u) = algebraMap _ _ v) : extend g (log u hu) = log v hv := by
  refine ext_eval fun n => ?_
  obtain ⟨l, hl, hl'⟩ := exists_quot u hu n
  rw [eval_extend, hl', Ideal.quotientMap_mk, eval_log_of_mul_eq v hv n (g l)]
  rw [← h, ← map_natCast g, ← map_pow, ← map_mul, hl, map_sub, map_pow, map_one]

variable (p) in

def map (f : R →+* S) : Acris p R →+* Acris p S := extend (AcrisZero.map p f)

variable (p R) in

def frob : Acris p R →+* Acris p R := extend (AcrisZero.frob p R)

@[simp] theorem map_algebraMap_zero (f : R →+* S) (x : AcrisZero p R) :
    map p f (algebraMap _ _ x) = algebraMap _ _ (AcrisZero.map p f x) := extend_algebraMap _ x

@[simp] theorem frob_algebraMap_zero (x : AcrisZero p R) :
    frob p R (algebraMap _ _ x) = algebraMap _ _ (AcrisZero.frob p R x) := extend_algebraMap _ x

@[simp] theorem map_algebraMap (f : R →+* S) (x : Ainf p R) :
    map p f (algebraMap _ _ x) = algebraMap _ _ (Ainf.map p f x) := by
  rw [IsScalarTower.algebraMap_apply (Ainf p R) (AcrisZero p R) (Acris p R), map_algebraMap_zero,
    AcrisZero.map_algebraMap, ← IsScalarTower.algebraMap_apply]

@[simp] theorem frob_algebraMap (x : Ainf p R) :
    frob p R (algebraMap _ _ x) = algebraMap _ _ (Ainf.frob p R x) := by
  rw [IsScalarTower.algebraMap_apply (Ainf p R) (AcrisZero p R) (Acris p R), frob_algebraMap_zero,
    AcrisZero.frob_algebraMap, ← IsScalarTower.algebraMap_apply]

@[simp] theorem map_algebraMap_padicInt (f : R →+* S) (a : ℤ_[p]) :
    map p f (algebraMap _ _ a) = algebraMap _ _ a := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] (Ainf p R) (Acris p R), map_algebraMap,
    Ainf.map_algebraMap, ← IsScalarTower.algebraMap_apply]

@[simp] theorem frob_algebraMap_padicInt (a : ℤ_[p]) :
    frob p R (algebraMap _ _ a) = algebraMap _ _ a := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] (Ainf p R) (Acris p R), frob_algebraMap,
    Ainf.frob_algebraMap]

@[simp] theorem map_id (x : Acris p R) : map p (RingHom.id R) x = x :=
  RingHom.congr_fun (hom_ext (f := map p (RingHom.id R)) (g := RingHom.id _) (by simp)) x

theorem map_map (f : R →+* S) (g : S →+* U) (x : Acris p R) :
    map p g (map p f x) = map p (g.comp f) x :=
  RingHom.congr_fun (hom_ext (f := (map p g).comp (map p f)) (g := map p (g.comp f))
    (by simp [AcrisZero.map_map])) x

theorem map_frob (f : R →+* S) (x : Acris p R) : map p f (frob p R x) = frob p S (map p f x) :=
  RingHom.congr_fun (hom_ext (f := (map p f).comp (frob p R)) (g := (frob p S).comp (map p f))
    (by simp [AcrisZero.map_frob])) x

theorem map_log (f : R →+* S) (u : Ainf p R) (hu : Ainf.theta p R u = 1)
    (hv : Ainf.theta p S (Ainf.map p f u) = 1) : map p f (log u hu) = log (Ainf.map p f u) hv :=
  extend_log _ _ _ _ _ (AcrisZero.map_algebraMap f u)


@[simp] theorem map_logTeich (f : R →+* S) (η : tateModule p R) :
    map p f (logTeich η) = logTeich (tateModule.map p f η) :=
  extend_log _ _ _ _ _ (by rw [AcrisZero.map_algebraMap, Ainf.map_teich]; rfl)

@[simp] theorem frob_logTeich (η : tateModule p R) : frob p R (logTeich η) = p * logTeich η := by
  rw [← logTeich_pow]
  exact extend_log _ _ _ _ _ (by rw [AcrisZero.frob_algebraMap, Ainf.frob_teich, ← map_pow]; rfl)

end Acris

namespace BcrisPlus

def lift {B : Type*} [CommRing B] (g : Acris p R →+* B) (h : IsUnit (p : B)) :
    BcrisPlus p R →+* B :=
  IsLocalization.Away.lift (p : Acris p R) (g := g) (by simpa using h)

@[simp] theorem lift_algebraMap {B : Type*} [CommRing B] (g : Acris p R →+* B)
    (h : IsUnit (p : B)) (x : Acris p R) : lift g h (algebraMap _ _ x) = g x :=
  IsLocalization.Away.lift_eq _ _ x

theorem hom_ext {B : Type*} [CommRing B] {f g : BcrisPlus p R →+* B}
    (h : ∀ x : Acris p R, f (algebraMap _ _ x) = g (algebraMap _ _ x)) : f = g :=
  IsLocalization.ringHom_ext (Submonoid.powers (p : Acris p R)) (RingHom.ext h)

theorem algebraMap_padicInt (a : ℤ_[p]) :
    algebraMap ℚ_[p] (BcrisPlus p R) (algebraMap ℤ_[p] ℚ_[p] a) =
      algebraMap (Acris p R) _ (algebraMap ℤ_[p] _ a) :=
  padicLift_algebraMap p _ _ a

variable (p) in

def map (f : R →+* S) : BcrisPlus p R →+* BcrisPlus p S :=
  lift ((algebraMap (Acris p S) _).comp (Acris.map p f)) (isUnit_p p S)

variable (p R) in

def frob : BcrisPlus p R →+* BcrisPlus p R :=
  lift ((algebraMap (Acris p R) _).comp (Acris.frob p R)) (isUnit_p p R)

@[simp] theorem map_algebraMap (f : R →+* S) (x : Acris p R) :
    map p f (algebraMap _ _ x) = algebraMap _ _ (Acris.map p f x) := lift_algebraMap _ _ x

@[simp] theorem frob_algebraMap (x : Acris p R) :
    frob p R (algebraMap _ _ x) = algebraMap _ _ (Acris.frob p R x) := lift_algebraMap _ _ x

@[simp] theorem map_algebraMap_padic (f : R →+* S) (a : ℚ_[p]) :
    map p f (algebraMap _ _ a) = algebraMap _ _ a :=
  RingHom.congr_fun (padic_hom_ext (f := (map p f).comp (algebraMap ℚ_[p] _))
    (g := algebraMap ℚ_[p] _) (fun a => by
      rw [RingHom.comp_apply, algebraMap_padicInt, algebraMap_padicInt, map_algebraMap,
        Acris.map_algebraMap_padicInt])) a

@[simp] theorem frob_algebraMap_padic (a : ℚ_[p]) :
    frob p R (algebraMap _ _ a) = algebraMap _ _ a :=
  RingHom.congr_fun (padic_hom_ext (f := (frob p R).comp (algebraMap ℚ_[p] _))
    (g := algebraMap ℚ_[p] _) (fun a => by
      rw [RingHom.comp_apply, algebraMap_padicInt, frob_algebraMap,
        Acris.frob_algebraMap_padicInt])) a

@[simp] theorem map_id (x : BcrisPlus p R) : map p (RingHom.id R) x = x :=
  RingHom.congr_fun (hom_ext (f := map p (RingHom.id R)) (g := RingHom.id _) (by simp)) x

theorem map_map (f : R →+* S) (g : S →+* U) (x : BcrisPlus p R) :
    map p g (map p f x) = map p (g.comp f) x :=
  RingHom.congr_fun (hom_ext (f := (map p g).comp (map p f)) (g := map p (g.comp f))
    (by simp [Acris.map_map])) x

theorem map_frob (f : R →+* S) (x : BcrisPlus p R) :
    map p f (frob p R x) = frob p S (map p f x) :=
  RingHom.congr_fun (hom_ext (f := (map p f).comp (frob p R)) (g := (frob p S).comp (map p f))
    (by simp [Acris.map_frob])) x

end BcrisPlus

namespace Bcris

def lift {B : Type*} [CommRing B] (g : BcrisPlus p R →+* B)
    (h : ∀ ε : tateModule p R, IsPrimitive ε →
      IsUnit (g (algebraMap (Acris p R) _ (Acris.logTeich ε)))) : Bcris p R →+* B :=
  IsLocalization.lift (M := BcrisPlus.periods p R) (g := g) (by
    rintro ⟨x, hx⟩
    induction hx using Submonoid.closure_induction with
    | mem x hx => obtain ⟨ε, hε, rfl⟩ := hx; exact h ε hε
    | one => simp
    | mul x y _ _ hx hy => simpa using hx.mul hy)

@[simp] theorem lift_algebraMap {B : Type*} [CommRing B] (g : BcrisPlus p R →+* B)
    (h : ∀ ε : tateModule p R, IsPrimitive ε →
      IsUnit (g (algebraMap (Acris p R) _ (Acris.logTeich ε)))) (x : BcrisPlus p R) :
    lift g h (algebraMap _ _ x) = g x :=
  IsLocalization.lift_eq _ x

theorem hom_ext {B : Type*} [CommRing B] {f g : Bcris p R →+* B}
    (h : ∀ x : BcrisPlus p R, f (algebraMap _ _ x) = g (algebraMap _ _ x)) : f = g :=
  IsLocalization.ringHom_ext (BcrisPlus.periods p R) (RingHom.ext h)

variable (p) in

def map (f : R →+* S) (hf : Function.Injective f) : Bcris p R →+* Bcris p S :=
  lift ((algebraMap (BcrisPlus p S) _).comp (BcrisPlus.map p f)) (fun ε hε => by
    rw [RingHom.comp_apply, BcrisPlus.map_algebraMap, Acris.map_logTeich]
    exact isUnit_logTeich (hε.map f hf))

variable (p R) in

def frob : Bcris p R →+* Bcris p R :=
  lift ((algebraMap (BcrisPlus p R) _).comp (BcrisPlus.frob p R)) (fun ε hε => by
    rw [RingHom.comp_apply, BcrisPlus.frob_algebraMap, Acris.frob_logTeich, map_mul, map_mul,
      map_natCast, map_natCast]
    exact isUnit_p.mul (isUnit_logTeich hε))

@[simp] theorem map_algebraMap (f : R →+* S) (hf : Function.Injective f) (x : BcrisPlus p R) :
    map p f hf (algebraMap _ _ x) = algebraMap _ _ (BcrisPlus.map p f x) := lift_algebraMap _ _ x

@[simp] theorem frob_algebraMap (x : BcrisPlus p R) :
    frob p R (algebraMap _ _ x) = algebraMap _ _ (BcrisPlus.frob p R x) := lift_algebraMap _ _ x

@[simp] theorem map_algebraMap_acris (f : R →+* S) (hf : Function.Injective f) (x : Acris p R) :
    map p f hf (algebraMap _ _ x) = algebraMap _ _ (Acris.map p f x) := by
  rw [IsScalarTower.algebraMap_apply (Acris p R) (BcrisPlus p R) (Bcris p R), map_algebraMap,
    BcrisPlus.map_algebraMap, ← IsScalarTower.algebraMap_apply]

@[simp] theorem frob_algebraMap_acris (x : Acris p R) :
    frob p R (algebraMap _ _ x) = algebraMap _ _ (Acris.frob p R x) := by
  rw [IsScalarTower.algebraMap_apply (Acris p R) (BcrisPlus p R) (Bcris p R), frob_algebraMap,
    BcrisPlus.frob_algebraMap, ← IsScalarTower.algebraMap_apply]

@[simp] theorem map_algebraMap_padic (f : R →+* S) (hf : Function.Injective f) (a : ℚ_[p]) :
    map p f hf (algebraMap _ _ a) = algebraMap _ _ a := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (BcrisPlus p R) (Bcris p R), map_algebraMap,
    BcrisPlus.map_algebraMap_padic, ← IsScalarTower.algebraMap_apply]

@[simp] theorem frob_algebraMap_padic (a : ℚ_[p]) :
    frob p R (algebraMap _ _ a) = algebraMap _ _ a := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (BcrisPlus p R) (Bcris p R), frob_algebraMap,
    BcrisPlus.frob_algebraMap_padic]

@[simp] theorem map_id (h : Function.Injective (RingHom.id R)) (x : Bcris p R) :
    map p (RingHom.id R) h x = x :=
  RingHom.congr_fun (hom_ext (f := map p (RingHom.id R) h) (g := RingHom.id _) (by simp)) x

theorem map_map (f : R →+* S) (hf : Function.Injective f) (g : S →+* U)
    (hg : Function.Injective g) (hgf : Function.Injective (g.comp f)) (x : Bcris p R) :
    map p g hg (map p f hf x) = map p (g.comp f) hgf x :=
  RingHom.congr_fun (hom_ext (f := (map p g hg).comp (map p f hf)) (g := map p (g.comp f) hgf)
    (by simp [BcrisPlus.map_map])) x

theorem map_congr {f g : R →+* S} (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f = g) : map p f hf = map p g hg := by subst h; rfl

theorem map_frob (f : R →+* S) (hf : Function.Injective f) (x : Bcris p R) :
    map p f hf (frob p R x) = frob p S (map p f hf x) :=
  RingHom.congr_fun (hom_ext (f := (map p f hf).comp (frob p R))
    (g := (frob p S).comp (map p f hf)) (by simp [BcrisPlus.map_frob])) x

@[simp] theorem map_logTeich (f : R →+* S) (hf : Function.Injective f) (η : tateModule p R) :
    map p f hf (logTeich η) = logTeich (tateModule.map p f η) := by
  simp [logTeich]

@[simp] theorem frob_logTeich (η : tateModule p R) : frob p R (logTeich η) = p * logTeich η := by
  simp [logTeich]

end Bcris

namespace Bst

variable (p) in

def map (f : R →+* S) (hf : Function.Injective f) : Bst p R →+* Bst p S :=
  lift ((algebraMap (Bcris p S) _).comp (Bcris.map p f hf)) (fun ϖ => logFlat (PFlat.map p f ϖ))
    (fun η ϖ => by rw [PFlat.map_twist, logFlat_twist, RingHom.comp_apply, Bcris.map_logTeich])

variable (p R) in

def frob : Bst p R →+* Bst p R :=
  lift ((algebraMap (Bcris p R) _).comp (Bcris.frob p R)) (fun ϖ => p * logFlat ϖ)
    (fun η ϖ => by
      rw [logFlat_twist, RingHom.comp_apply, Bcris.frob_logTeich, map_mul, map_natCast, mul_add])

@[simp] theorem map_algebraMap (f : R →+* S) (hf : Function.Injective f) (x : Bcris p R) :
    map p f hf (algebraMap _ _ x) = algebraMap _ _ (Bcris.map p f hf x) := lift_algebraMap _ _ _ x

@[simp] theorem frob_algebraMap (x : Bcris p R) :
    frob p R (algebraMap _ _ x) = algebraMap _ _ (Bcris.frob p R x) := lift_algebraMap _ _ _ x

@[simp] theorem map_logFlat (f : R →+* S) (hf : Function.Injective f) (ϖ : PFlat p R) :
    map p f hf (logFlat ϖ) = logFlat (PFlat.map p f ϖ) := lift_logFlat _ _ _ ϖ

@[simp] theorem frob_logFlat (ϖ : PFlat p R) : frob p R (logFlat ϖ) = p * logFlat ϖ :=
  lift_logFlat _ _ _ ϖ

@[simp] theorem map_algebraMap_padic (f : R →+* S) (hf : Function.Injective f) (a : ℚ_[p]) :
    map p f hf (algebraMap _ _ a) = algebraMap _ _ a := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (Bcris p R) (Bst p R), map_algebraMap,
    Bcris.map_algebraMap_padic, ← IsScalarTower.algebraMap_apply]

@[simp] theorem frob_algebraMap_padic (a : ℚ_[p]) :
    frob p R (algebraMap _ _ a) = algebraMap _ _ a := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (Bcris p R) (Bst p R), frob_algebraMap,
    Bcris.frob_algebraMap_padic]

@[simp] theorem map_id (h : Function.Injective (RingHom.id R)) (x : Bst p R) :
    map p (RingHom.id R) h x = x :=
  RingHom.congr_fun (hom_ext (f := map p (RingHom.id R) h) (g := RingHom.id _) (by simp)
    (by simp)) x

theorem map_map (f : R →+* S) (hf : Function.Injective f) (g : S →+* U)
    (hg : Function.Injective g) (hgf : Function.Injective (g.comp f)) (x : Bst p R) :
    map p g hg (map p f hf x) = map p (g.comp f) hgf x :=
  RingHom.congr_fun (hom_ext (f := (map p g hg).comp (map p f hf)) (g := map p (g.comp f) hgf)
    (fun x => by simp [Bcris.map_map f hf g hg hgf]) (by simp [PFlat.map_map])) x

theorem map_congr {f g : R →+* S} (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f = g) : map p f hf = map p g hg := by subst h; rfl

theorem map_frob (f : R →+* S) (hf : Function.Injective f) (x : Bst p R) :
    map p f hf (frob p R x) = frob p S (map p f hf x) :=
  RingHom.congr_fun (hom_ext (f := (map p f hf).comp (frob p R))
    (g := (frob p S).comp (map p f hf)) (by simp [Bcris.map_frob]) (by simp)) x

theorem induction_on {P : Bst p R → Prop} (x : Bst p R)
    (h₁ : ∀ a : Bcris p R, P (algebraMap _ _ a)) (h₂ : ∀ x y, P x → P y → P (x + y))
    (h₃ : ∀ x ϖ, P x → P (x * logFlat ϖ)) : P x := by
  obtain ⟨f, rfl⟩ := mk_surjective p R x
  induction f using MvPolynomial.induction_on with
  | C a => have := h₁ a; rwa [← (mk p R).commutes] at this
  | add f g hf hg => rw [map_add]; exact h₂ _ _ hf hg
  | mul_X f ϖ hf => rw [map_mul]; exact h₃ _ ϖ hf

@[simp] theorem monodromy_algebraMap (a : Bcris p R) : monodromy p R (algebraMap _ _ a) = 0 :=
  Derivation.map_algebraMap _ a



end Bst

end Reformulated.AutPerF
end
end
