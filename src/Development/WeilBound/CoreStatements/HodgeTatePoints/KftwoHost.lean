import Mathlib
import Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoDefs
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt

section
noncomputable section

open NumberField

namespace PositivityTheory.HtPt.Kftwo

structure Biq (F : Type) [Field F] [CharZero F] (m : ℕ) where

  w : F

  i : F
  w_sq : w * w = w - m
  i_sq : i * i = -1
  span : ∀ x : F, ∃ a b c e : ℚ, x = a + b * w + c * i + e * (w * i)
  indep : ∀ a b c e : ℚ, (a : F) + b * w + c * i + e * (w * i) = 0 → a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0

  σ : F →+* F

  τ : F →+* F
  σw : σ w = w
  σi : σ i = -i
  τw : τ w = 1 - w
  τi : τ i = i

section Exists

variable (m : ℕ)

abbrev Q1 : Type := QuadraticAlgebra ℚ (-(m : ℚ)) 1

abbrev Q2 : Type := QuadraticAlgebra (Q1 m) (-1) 0

attribute [local simp] QuadraticAlgebra.re_one QuadraticAlgebra.im_one

theorem fact1 (hm : 0 < m) : ∀ r : ℚ, r ^ 2 ≠ -(m : ℚ) + 1 * r := fun r h => by
  have : (1 : ℚ) ≤ m := by exact_mod_cast hm
  nlinarith [sq_nonneg (r - 1 / 2)]

theorem fact2 (hp : (4 * m - 1).Prime) (r : Q1 m) : r ^ 2 ≠ -1 + 0 * r := fun h => by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp [Nat.not_prime_zero] at hp
    · exact h
  have h1 := congrArg QuadraticAlgebra.re h
  have h2 := congrArg QuadraticAlgebra.im h
  simp [pow_two] at h1 h2
  have hb : r.im ≠ 0 := fun h0 => by
    rw [h0] at h1
    nlinarith [sq_nonneg r.re]
  have ha : r.im = -2 * r.re := by
    have : r.im * (r.im + 2 * r.re) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hb
    · linear_combination h
  have hr : r.re ≠ 0 := fun h0 => hb (by rw [ha, h0, mul_zero])
  have hd : ((4 * m - 1 : ℕ) : ℚ) = (1 / r.re) * (1 / r.re) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    field_simp
    rw [ha] at h1
    linear_combination -h1
  have hs : IsSquare ((4 * m - 1 : ℕ) : ℚ) := ⟨_, hd⟩
  exact hp.not_isSquare (Rat.isSquare_natCast_iff.1 hs)

theorem exists_biq (hp : (4 * m - 1).Prime) :
    ∃ (F : Type) (_ : Field F) (_ : CharZero F), Nonempty (Biq F m) := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp [Nat.not_prime_zero] at hp
    · exact h
  have := Fact.mk (fact1 m hm)
  have := Fact.mk (fact2 m hp)
  have hc : ∀ a : ℚ, (a : (Q2 m)) = ⟨⟨a, 0⟩, 0⟩ := fun a => by
    have := map_ratCast ((algebraMap (Q1 m) (Q2 m)).comp (algebraMap ℚ (Q1 m))) a
    rw [← this]; rfl
  let τ : (Q2 m) →+* (Q2 m) :=
    { toFun := fun z => ⟨star z.re, star z.im⟩
      map_one' := by ext1 <;> simp
      map_zero' := by ext1 <;> simp
      map_add' := fun x y => by ext1 <;> simp
      map_mul' := fun x y => by ext1 <;> simp }
  refine ⟨(Q2 m), inferInstance, inferInstance, ⟨⟨⟨⟨0, 1⟩, 0⟩, ⟨0, 1⟩, ?_, ?_, fun x => ?_, fun a b c e h => ?_,
    starRingEnd (Q2 m), τ, ?_, ?_, ?_, ?_⟩⟩⟩
  · ext <;> simp
  · ext <;> simp
  · refine ⟨x.re.re, x.re.im, x.im.re, x.im.im, ?_⟩
    simp only [hc]
    ext <;> simp
  · simp only [hc] at h
    have h1 := congrArg (fun z : (Q2 m) => z.re.re) h
    have h2 := congrArg (fun z : (Q2 m) => z.re.im) h
    have h3 := congrArg (fun z : (Q2 m) => z.im.re) h
    have h4 := congrArg (fun z : (Q2 m) => z.im.im) h
    simp at h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  · rw [starRingEnd_apply]; ext <;> simp
  · rw [starRingEnd_apply]; ext <;> simp
  · ext <;> simp [τ]
  · ext <;> simp [τ]

end Exists

namespace Biq

variable {F : Type} [Field F] [CharZero F] {m : ℕ} (B : Biq F m)

theorem int_of_integral {q : ℚ} (h : IsIntegral ℤ (q : F)) : ∃ n : ℤ, q = n := by
  have h' : IsIntegral ℤ (algebraMap ℚ F q) := by simpa using h
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (isIntegral_algebraMap_iff (algebraMap ℚ F).injective |>.1 h')
  exact ⟨n, by simpa using hn.symm⟩

omit [CharZero F] in
theorem of_eq {x y : F} (h : IsIntegral ℤ x) (e : y = x) : IsIntegral ℤ y := e ▸ h

omit [CharZero F] in
theorem integral_map {x : F} (f : F →+* F) (h : IsIntegral ℤ x) : IsIntegral ℤ (f x) := h.map f.toIntAlgHom

omit [CharZero F] in
theorem integral_int (n : ℤ) : IsIntegral ℤ (n : F) := by
  simpa using isIntegral_algebraMap (R := ℤ) (A := F) (x := n)

theorem integral_w : IsIntegral ℤ B.w :=
  ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), by monicity!, by
    simp [Polynomial.eval₂_add, Polynomial.eval₂_sub]; linear_combination B.w_sq⟩

theorem integral_i : IsIntegral ℤ B.i :=
  ⟨Polynomial.X ^ 2 + 1, by monicity!, by simp; linear_combination B.i_sq⟩

theorem gauss {u v : ℚ} (h : IsIntegral ℤ ((u : F) + v * B.i)) : (∃ n : ℤ, u = n) ∧ ∃ n : ℤ, v = n := by
  have h' := integral_map B.σ h
  simp only [map_add, map_mul, map_ratCast, B.σi] at h'
  obtain ⟨p, hp⟩ := int_of_integral (F := F) (q := 2 * u) (by
    refine of_eq (h.add h') ?_; push_cast; ring)
  obtain ⟨q, hq⟩ := int_of_integral (F := F) (q := 2 * v) (by
    refine of_eq ((h'.sub h).mul B.integral_i) ?_; push_cast; linear_combination (2 * v : F) * B.i_sq)
  obtain ⟨n, hn⟩ := int_of_integral (F := F) (q := u ^ 2 + v ^ 2) (by
    refine of_eq (h.mul h') ?_; push_cast; linear_combination (v : F) ^ 2 * B.i_sq)
  have e : p ^ 2 + q ^ 2 = 4 * n := by
    have : (p : ℚ) ^ 2 + q ^ 2 = 4 * n := by rw [← hp, ← hq, ← hn]; ring
    exact_mod_cast this
  have hpq : Even p ∧ Even q := by
    rcases Int.even_or_odd' p with ⟨s, rfl | rfl⟩ <;> rcases Int.even_or_odd' q with ⟨t, rfl | rfl⟩
    · simp
    · exfalso; have : 4 * (s ^ 2 + t ^ 2 + t - n) + 1 = 0 := by linear_combination e
      omega
    · exfalso; have : 4 * (s ^ 2 + t ^ 2 + s - n) + 1 = 0 := by linear_combination e
      omega
    · exfalso; have : 4 * (s ^ 2 + t ^ 2 + s + t - n) + 2 = 0 := by linear_combination e
      omega
  obtain ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩ := hpq
  push_cast at hp hq
  exact ⟨⟨s, by linarith⟩, t, by linarith⟩

theorem quad {d : ℕ} (hd : d + 1 = 4 * m) (hp : d.Prime) {a b : ℚ} {r s : ℤ} (hr : d * a = r) (hs : d * b = s)
    (h : IsIntegral ℤ ((a : F) + b * B.w)) : (∃ n : ℤ, a = n) ∧ ∃ n : ℤ, b = n := by
  have h' := integral_map B.τ h
  simp only [map_add, map_mul, map_ratCast, B.τw] at h'
  obtain ⟨p, hp'⟩ := int_of_integral (F := F) (q := 2 * a + b) (by
    refine of_eq (h.add h') ?_; push_cast; ring)
  obtain ⟨n, hn⟩ := int_of_integral (F := F) (q := a ^ 2 + a * b + m * b ^ 2) (by
    refine of_eq (h.mul h') ?_; push_cast; linear_combination (b : F) ^ 2 * B.w_sq)
  have hdq : (d : ℚ) + 1 = 4 * m := by exact_mod_cast hd
  have e : s ^ 2 = d * (4 * n - p ^ 2) := by
    have : (s : ℚ) ^ 2 = d * (4 * n - p ^ 2) := by
      rw [← hs, ← hn, ← hp']; linear_combination (d * b ^ 2 : ℚ) * hdq
    exact_mod_cast this
  obtain ⟨t, rfl⟩ : (d : ℤ) ∣ s := (Nat.prime_iff_prime_int.1 hp).dvd_of_dvd_pow ⟨_, e⟩
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hb : b = t := by push_cast at hs; exact mul_left_cancel₀ hd0 hs
  refine ⟨⟨2 * m * (p - t) - r, ?_⟩, t, hb⟩
  push_cast
  rw [← hp', ← hr, ← hb]
  linear_combination a * hdq

theorem coords {d : ℕ} (hd : d + 1 = 4 * m) (hp : d.Prime) {x : F} (h : IsIntegral ℤ x) :
    ∃ a b c e : ℤ, x = a + b * B.w + c * B.i + e * (B.w * B.i) := by
  obtain ⟨a, b, c, e, rfl⟩ := B.span x
  have hdF : (d : F) = 4 * m - 1 := by
    have : (d : F) + 1 = 4 * m := by exact_mod_cast hd
    linear_combination this
  have h1 := integral_map B.τ h
  have h2 := integral_map B.σ h
  simp only [map_add, map_mul, map_ratCast, B.τw, B.τi, B.σw, B.σi] at h1 h2
  have hw := B.integral_w
  have hi := B.integral_i
  obtain ⟨⟨b', hb⟩, e', he⟩ := B.gauss (u := d * b) (v := d * e) (by
    refine of_eq ((h1.sub h).mul ((hw.add hw).sub isIntegral_one)) ?_
    push_cast; rw [hdF]; linear_combination (4 * (b + e * B.i) : F) * B.w_sq)
  have hbF : (b' : F) = d * b := by exact_mod_cast congrArg (fun q : ℚ => (q : F)) hb.symm
  have heF : (e' : F) = d * e := by exact_mod_cast congrArg (fun q : ℚ => (q : F)) he.symm
  obtain ⟨⟨a', ha⟩, c', hc⟩ := B.gauss (u := d * a) (v := d * c) (by
    refine of_eq ((((integral_int (d : ℤ)).mul h).sub ((integral_int b').mul hw)).sub
      ((integral_int e').mul (hw.mul hi))) ?_
    push_cast; rw [hbF, heF]; ring)
  have haF : (a' : F) = d * a := by exact_mod_cast congrArg (fun q : ℚ => (q : F)) ha.symm
  have hα : IsIntegral ℤ ((a : F) + b * B.w) := by
    refine of_eq (((integral_int (2 * m : ℤ)).mul (h.add h2)).sub ((integral_int a').add ((integral_int b').mul hw))) ?_
    push_cast; rw [haF, hbF, hdF]; ring
  have hβ : IsIntegral ℤ ((c : F) + e * B.w) := by
    refine of_eq ((hα.sub h).mul hi) ?_
    linear_combination (c + e * B.w : F) * B.i_sq
  obtain ⟨⟨a, rfl⟩, b, rfl⟩ := B.quad hd hp ha hb hα
  obtain ⟨⟨c, rfl⟩, e, rfl⟩ := B.quad hd hp hc he hβ
  exact ⟨a, b, c, e, by simp⟩

include B in
theorem numberField : NumberField F := by
  classical
  have : Module.Finite ℚ F := by
    refine ⟨⟨{1, B.w, B.i, B.w * B.i}, eq_top_iff.2 fun x _ => ?_⟩⟩
    obtain ⟨a, b, c, e, rfl⟩ := B.span x
    have k : ∀ (q : ℚ) (y : F), y ∈ ({1, B.w, B.i, B.w * B.i} : Finset F) →
        (q : F) * y ∈ Submodule.span ℚ (({1, B.w, B.i, B.w * B.i} : Finset F) : Set F) := fun q y hy => by
      rw [← Rat.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hy)
    refine add_mem (add_mem (add_mem ?_ (k _ _ (by simp))) (k _ _ (by simp))) (k _ _ (by simp))
    simpa using k a 1 (by simp)
  exact {}

theorem conj_w (hm : 0 < m) (φ : F →+* ℂ) : starRingEnd ℂ (φ B.w) = 1 - φ B.w := by
  have h := congrArg φ B.w_sq
  simp only [map_mul, map_sub, map_natCast] at h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp at h1 h2
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hv : (φ B.w).im ≠ 0 := fun h0 => by
    rw [h0] at h1
    nlinarith [sq_nonneg ((φ B.w).re - 1 / 2)]
  have : (φ B.w).im * (2 * (φ B.w).re - 1) = 0 := by linear_combination h2
  have hu := (mul_eq_zero.1 this).resolve_left hv
  apply Complex.ext <;> simp
  linarith

theorem conj_i (φ : F →+* ℂ) : starRingEnd ℂ (φ B.i) = -φ B.i := by
  have h := congrArg φ B.i_sq
  simp only [map_mul, map_neg, map_one] at h
  have : (φ B.i - Complex.I) * (φ B.i + Complex.I) = 0 := by linear_combination h - Complex.I_mul_I
  rcases mul_eq_zero.1 this with h | h
  · rw [sub_eq_zero.1 h, Complex.conj_I]
  · rw [eq_neg_of_add_eq_zero_left h, map_neg, Complex.conj_I]

theorem conj_eq (hm : 0 < m) (φ : F →+* ℂ) (x : F) : φ (B.σ (B.τ x)) = starRingEnd ℂ (φ x) := by
  obtain ⟨a, b, c, e, rfl⟩ := B.span x
  simp only [map_add, map_mul, map_ratCast, B.τw, B.τi, B.σw, B.σi, map_sub, map_one, map_neg, B.conj_w hm, B.conj_i]

theorem mem_real (hm : 0 < m) {x : F} (h : B.σ (B.τ x) = x) : x ∈ maximalRealSubfield F := by
  rw [mem_maximalRealSubfield_iff]
  intro φ
  rw [RCLike.star_def, ← B.conj_eq hm, h]

theorem i_ne_zero : B.i ≠ 0 := fun h => by simpa [h] using B.i_sq

include B in
theorem isCMField (hm : 0 < m) : IsCMField F := by
  have := B.numberField
  have hT : IsTotallyComplex F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff]
    intro h
    have h1 := RingHom.congr_fun h B.i
    rw [ComplexEmbedding.conjugate_coe_eq, B.conj_i] at h1
    exact B.i_ne_zero (v.embedding.injective (by rw [map_zero]; linear_combination (-1 / 2 : ℂ) * h1))⟩
  have hc : ∀ x, B.σ (B.τ (B.σ (B.τ x))) = x := fun x => by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    apply φ.injective
    rw [B.conj_eq hm, B.conj_eq hm, Complex.conj_conj]
  have hli : LinearIndependent (maximalRealSubfield F) ![(1 : F), B.i] := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 : (s : F) + t * B.i = 0 := by simpa [Subfield.smul_def] using h
    have h1 := congrArg φ h0
    have h2 := congrArg (starRingEnd ℂ) h1
    have hs := (mem_maximalRealSubfield_iff _).1 s.2 φ
    have ht := (mem_maximalRealSubfield_iff _).1 t.2 φ
    rw [RCLike.star_def] at hs ht
    simp only [map_add, map_mul, map_zero, hs, ht, B.conj_i] at h1 h2
    have e1 : (s : F) = 0 := φ.injective (by rw [map_zero]; linear_combination (1 / 2 : ℂ) * (h1 + h2))
    rw [e1, zero_add] at h0
    exact ⟨Subtype.ext e1, Subtype.ext ((mul_eq_zero.1 h0).resolve_right B.i_ne_zero)⟩
  have hsp : ⊤ ≤ Submodule.span (maximalRealSubfield F) (Set.range ![(1 : F), B.i]) := fun x _ => by
    rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair]
    refine ⟨⟨(x + B.σ (B.τ x)) / 2, B.mem_real hm ?_⟩, ⟨(B.σ (B.τ x) - x) * B.i / 2, B.mem_real hm ?_⟩, ?_⟩
    · simp only [map_div₀, map_add, map_ofNat, hc]; ring
    · simp only [map_div₀, map_sub, map_mul, map_ofNat, hc, B.τi, B.σi]; ring
    · simp only [Subfield.smul_def, smul_eq_mul]
      linear_combination ((B.σ (B.τ x) - x) / 2) * B.i_sq
  have : Algebra.IsQuadraticExtension (maximalRealSubfield F) F :=
    { finrank_eq_two' := by simpa using Module.finrank_eq_card_basis (Module.Basis.mk hli hsp) }
  exact {}

end Biq

end PositivityTheory.HtPt.Kftwo
end
end

section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.HtPt.Kftwo

namespace Biq

variable {F : Type} [Field F] [NumberField F] {m : ℕ} (B : Biq F m)

def W : 𝓞 F := ⟨B.w, B.integral_w⟩

def J : 𝓞 F := ⟨B.i, B.integral_i⟩

def mk4 (v : ℤ × ℤ × ℤ × ℤ) : 𝓞 F := v.1 + v.2.1 * B.W + v.2.2.1 * B.J + v.2.2.2 * (B.W * B.J)

theorem coe_W : algebraMap (𝓞 F) F B.W = B.w := rfl
theorem coe_J : algebraMap (𝓞 F) F B.J = B.i := rfl

theorem W_sq : B.W * B.W = B.W - m := RingOfIntegers.ext (by
  simpa only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_sub, map_natCast, coe_W] using B.w_sq)

theorem J_sq : B.J * B.J = -1 := RingOfIntegers.ext (by
  simpa only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_neg, map_one, coe_J] using B.i_sq)

theorem coe_mk_quad (v : ℤ × ℤ × ℤ × ℤ) : algebraMap (𝓞 F) F (B.mk4 v) =
    v.1 + v.2.1 * B.w + v.2.2.1 * B.i + v.2.2.2 * (B.w * B.i) := by
  simp only [mk4, map_add, map_mul, map_intCast, coe_W, coe_J]

theorem mk_quad_injective : Function.Injective B.mk4 := fun v v' h => by
  have h' := congrArg (algebraMap (𝓞 F) F) h
  rw [coe_mk_quad, coe_mk_quad] at h'
  obtain ⟨h1, h2, h3, h4⟩ := B.indep (v.1 - v'.1) (v.2.1 - v'.2.1) (v.2.2.1 - v'.2.2.1) (v.2.2.2 - v'.2.2.2) (by
    push_cast; linear_combination h')
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · exact_mod_cast sub_eq_zero.1 h1
  · exact_mod_cast sub_eq_zero.1 h2
  · exact_mod_cast sub_eq_zero.1 h3
  · exact_mod_cast sub_eq_zero.1 h4

theorem mk_quad_surjective {d : ℕ} (hd : d + 1 = 4 * m) (hp : d.Prime) : Function.Surjective B.mk4 := fun x => by
  obtain ⟨a, b, c, e, h⟩ := B.coords hd hp x.isIntegral_coe
  exact ⟨(a, b, c, e), RingOfIntegers.ext (by rw [RingOfIntegers.coe_eq_algebraMap, coe_mk_quad]; exact h.symm)⟩

theorem σ_σ (x : F) : B.σ (B.σ x) = x := by
  obtain ⟨a, b, c, e, rfl⟩ := B.span x
  simp only [map_add, map_mul, map_ratCast, B.σw, B.σi, map_neg, neg_neg]

def σO : 𝓞 F ≃+* 𝓞 F :=
  RingOfIntegers.mapRingEquiv (RingEquiv.ofRingHom B.σ B.σ (RingHom.ext B.σ_σ) (RingHom.ext B.σ_σ))

theorem sigma_W : B.σO B.W = B.W := RingOfIntegers.ext B.σw

theorem σO_J : B.σO B.J = -B.J := RingOfIntegers.ext B.σi

variable [IsCMField F]

theorem complexConj_eq (hm : 0 < m) (x : F) : IsCMField.complexConj F x = B.σ (B.τ x) := by
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, B.conj_eq hm]

include B in
theorem unramified {d : ℕ} (hd : d + 1 = 4 * m) (hp : d.Prime) :
    Algebra.Unramified (𝓞 (maximalRealSubfield F)) (𝓞 F) := by
  have hm : 0 < m := by omega
  let R := 𝓞 (maximalRealSubfield F)
  let δ := KaehlerDifferential.D R (𝓞 F)
  have h1 : (2 * B.J) • δ B.J = 0 := by
    have := congrArg δ B.J_sq
    rw [Derivation.leibniz, map_neg, Derivation.map_one_eq_zero, neg_zero] at this
    rw [two_mul, add_smul, this]
  have h2 : (2 * B.W - 1) • δ B.W = 0 := by
    have := congrArg δ B.W_sq
    rw [Derivation.leibniz, map_sub, Derivation.map_natCast, sub_zero] at this
    rw [two_mul, sub_smul, add_smul, this, one_smul, sub_self]
  have h3 : δ (B.J * (B.W + B.W - 1)) = 0 := by
    obtain ⟨r, hr⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff F (B.J * (B.W + B.W - 1))).1
      (RingOfIntegers.ext (by
        rw [IsCMField.coe_ringOfIntegersComplexConj, B.complexConj_eq hm]
        simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_sub, map_add, map_one, coe_W, coe_J, B.τi, B.τw,
          B.σi, B.σw]
        ring))
    rw [← hr, Derivation.map_algebraMap]
  rw [Derivation.leibniz, map_sub, map_add, Derivation.map_one_eq_zero, sub_zero] at h3
  have hJ : δ B.J = 0 := by
    have e : (1 : 𝓞 F) = -(2 * m * B.J) * (2 * B.J) + (2 * B.W - 1) * (B.W + B.W - 1) := by
      linear_combination (4 * m : 𝓞 F) * B.J_sq - 4 * B.W_sq
    have e2 : (2 * B.W - 1) • ((B.W + B.W - 1) • δ B.J) = 0 := by
      rw [eq_neg_of_add_eq_zero_right h3, smul_neg, smul_comm, smul_add, h2, add_zero, smul_zero, neg_zero]
    rw [← one_smul (𝓞 F) (δ B.J), e, add_smul, mul_smul, mul_smul (2 * B.W - 1), h1, e2, smul_zero, add_zero]
  have hW : δ B.W = 0 := by
    rw [hJ, smul_zero, add_zero, ← two_smul (𝓞 F), smul_smul] at h3
    have e : (1 : 𝓞 F) = -(2 * m * B.J) * (B.J * 2) + (2 * B.W - 1) * (2 * B.W - 1) := by
      linear_combination (4 * m : 𝓞 F) * B.J_sq - 4 * B.W_sq
    rw [← one_smul (𝓞 F) (δ B.W), e, add_smul, mul_smul, mul_smul (2 * B.W - 1), h3, h2, smul_zero, smul_zero, add_zero]
  have hall : ∀ x, δ x = 0 := fun x => by
    obtain ⟨v, rfl⟩ := B.mk_quad_surjective hd hp x
    simp only [mk4, map_add, Derivation.leibniz, hW, hJ, Derivation.map_intCast, smul_zero, add_zero]
  have hs : Subsingleton (Ω[𝓞 F⁄R]) := by
    rw [← Submodule.subsingleton_iff (𝓞 F), ← subsingleton_iff_bot_eq_top, eq_comm,
      ← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
    rintro _ ⟨x, rfl⟩
    exact hall x
  have : Algebra.FormallyUnramified R (𝓞 F) := ⟨hs⟩
  have : Algebra.FiniteType R (𝓞 F) := Algebra.FiniteType.of_restrictScalars_finiteType ℤ R (𝓞 F)
  exact {}

end Biq

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def mat (w : 𝓞 E) (v : ℤ × ℤ × ℤ × ℤ) : Matrix (Fin 2) (Fin 2) (𝓞 E) :=
  !![v.1 + v.2.1 * w, -(v.2.2.1 + v.2.2.2 * w); v.2.2.1 + v.2.2.2 * w, v.1 + v.2.1 * w]

set_option maxHeartbeats 1600000 in

theorem exists_pairHost {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    ∃ (E' : Type) (_ : Field E') (_ : NumberField E') (_ : IsCMField E') (H' : Host E'), Nonempty (PairHost H H') := by
  obtain ⟨m, hd⟩ : ∃ m, H.d + 1 = 4 * m := ⟨(H.d + 1) / 4, by have := H.d_mod; omega⟩
  have hm : 0 < m := by omega
  obtain ⟨F, _, _, ⟨B⟩⟩ := exists_biq m (by rw [show 4 * m - 1 = H.d by omega]; exact H.d_prime)
  have := B.numberField
  have := B.isCMField hm
  have hdO : (H.d : 𝓞 F) + 1 = 4 * m := by exact_mod_cast hd
  let H' : Host F :=
    { d := H.d, d_mod := H.d_mod, d_prime := H.d_prime, rt := 2 * B.W - 1
      rt_sq := by linear_combination 4 * B.W_sq + hdO
      w0 := B.W, two_weight_eq_one_add_root := by ring
      bar := (IsCMField.ringOfIntegersComplexConj F).toRingEquiv
      bar_eq := fun _ => rfl
      unram := B.unramified hd H.d_prime
      rt0 := H.rt0, sqrt_neg_disc_sq := H.sqrt_neg_disc_sq }
  have hbW : H'.bar B.W = 1 - B.W := GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator H'
  have hbJ : H'.bar B.J = -B.J := RingOfIntegers.ext (by
    rw [H'.bar_eq, B.complexConj_eq hm]
    show B.σ (B.τ B.i) = -B.i
    rw [B.τi, B.σi])
  have hw : H.w0 * H.w0 = H.w0 - m := by
    have hdE : (H.d : 𝓞 E) + 1 = 4 * m := by exact_mod_cast hd
    have h1 := H.rt_sq
    rw [GlobalTheory.HostModel.rt_eq] at h1
    have : (4 : 𝓞 E) * (H.w0 * H.w0 - (H.w0 - m)) = 0 := by linear_combination h1 - hdE
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (by norm_num))
  let e := Equiv.ofBijective B.mk4 ⟨B.mk_quad_injective, B.mk_quad_surjective hd H.d_prime⟩
  have he : ∀ (x : 𝓞 F) v, x = B.mk4 v → mat H.w0 (e.symm x) = mat H.w0 v := by
    rintro _ v rfl
    rw [show e.symm (B.mk4 v) = v from e.symm_apply_apply v]
  let ψ : 𝓞 F →+* Matrix (Fin 2) (Fin 2) (𝓞 E) :=
    { toFun := fun x => mat H.w0 (e.symm x)
      map_one' := by
        rw [he 1 (1, 0, 0, 0) (by simp [Biq.mk4])]
        ext1 i j; fin_cases i <;> fin_cases j <;> simp [mat]
      map_zero' := by
        rw [he 0 (0, 0, 0, 0) (by simp [Biq.mk4])]
        ext1 i j; fin_cases i <;> fin_cases j <;> simp [mat]
      map_add' := fun x y => by
        obtain ⟨⟨a, b, c, f⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
        obtain ⟨⟨a', b', c', f'⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime y
        rw [he _ _ rfl, he _ _ rfl, he _ (a + a', b + b', c + c', f + f') (by simp only [Biq.mk4]; push_cast; ring)]
        ext1 i j; fin_cases i <;> fin_cases j <;> simp [mat] <;> ring
      map_mul' := fun x y => by
        obtain ⟨⟨a, b, c, f⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
        obtain ⟨⟨a', b', c', f'⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime y
        rw [he _ _ rfl, he _ _ rfl, he _ (a * a' - m * b * b' - c * c' + m * f * f',
          a * b' + b * a' + b * b' - c * f' - f * c' - f * f', a * c' + c * a' - m * b * f' - m * f * b',
          a * f' + b * c' + b * f' + c * b' + f * a' + f * b') (by
            simp only [Biq.mk4]; push_cast
            linear_combination ((b * b' + (b * f' + f * b') * B.J - f * f' : 𝓞 F)) * B.W_sq +
              ((c + f * B.W) * (c' + f' * B.W) : 𝓞 F) * B.J_sq)]
        ext1 i j
        fin_cases i <;> fin_cases j <;> simp [mat, Matrix.mul_apply, Fin.sum_univ_two]
        · linear_combination (f * f' - b * b' : 𝓞 E) * hw
        · linear_combination (b * f' + f * b' : 𝓞 E) * hw
        · linear_combination (-(b * f' + f * b') : 𝓞 E) * hw
        · linear_combination (f * f' - b * b' : 𝓞 E) * hw }
  have hψ : ∀ (x : 𝓞 F) v, x = B.mk4 v → ψ x = mat H.w0 v := he
  clear_value ψ
  refine ⟨F, inferInstance, inferInstance, inferInstance, H', ⟨⟨ψ, B.σO, fun x i j => ?_, ?_, fun x => ?_, ?_,
    fun k _ _ τ τ' h => ?_⟩⟩⟩
  · obtain ⟨⟨a, b, c, f⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
    rw [hψ _ _ rfl, hψ _ (a + b, -b, -c - f, f) (by
      simp only [Biq.mk4, map_add, map_mul, map_intCast, hbW, hbJ]; push_cast; ring)]
    fin_cases i <;> fin_cases j <;> simp [mat] <;> ring
  · rw [hψ _ (0, 1, 0, 0) (by simp [Biq.mk4, H'])]
    ext1 i j; fin_cases i <;> fin_cases j <;> simp [mat]
  · obtain ⟨⟨a, b, c, f⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
    rw [hψ _ _ rfl, hψ _ (a, b, -c, -f) (by
      simp only [Biq.mk4, map_add, map_mul, map_intCast, B.sigma_W, B.σO_J]; push_cast; ring)]
    ext1 i j
    fin_cases i <;> fin_cases j <;> simp [mat, Matrix.mul_diagonal, Matrix.diagonal_mul] <;> ring
  · show B.σO (2 * B.W - 1) = 2 * B.W - 1
    rw [map_sub, map_mul, map_ofNat, map_one, B.sigma_W]
  · have hW : τ' B.W = τ B.W := by
      change τ (2 * B.W - 1) = τ' (2 * B.W - 1) at h
      simp only [map_sub, map_mul, map_ofNat, map_one] at h
      linear_combination (-1 / 2 : k) * h
    have h1 := congrArg τ B.J_sq
    have h2 := congrArg τ' B.J_sq
    simp only [map_mul, map_neg, map_one] at h1 h2
    have : (τ' B.J - τ B.J) * (τ' B.J + τ B.J) = 0 := by linear_combination h2 - h1
    rcases mul_eq_zero.1 this with h3 | h3
    · refine Or.inl (RingHom.ext fun x => ?_)
      obtain ⟨v, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
      simp only [Biq.mk4, map_add, map_mul, map_intCast, hW, sub_eq_zero.1 h3]
    · refine Or.inr (RingHom.ext fun x => ?_)
      obtain ⟨v, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
      show _ = τ (B.σO _)
      simp only [Biq.mk4, map_add, map_mul, map_intCast, hW, eq_neg_of_add_eq_zero_left h3, B.sigma_W, B.σO_J, map_neg]

end PositivityTheory.HtPt.Kftwo
end
end
