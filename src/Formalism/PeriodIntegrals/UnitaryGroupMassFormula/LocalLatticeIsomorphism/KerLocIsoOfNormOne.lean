import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.RpOfIsIntegral
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.IndBasic

section
noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KLW

section conj
variable {K E : Type} [Field K] [Field E] [CharZero E] [Algebra K E]

def conjK (cj : E ≃ₐ[ℚ] E) (h : ∀ k : K, ∃ k' : K, cj (algebraMap K E k) = algebraMap K E k') :
    K →+* K where
  toFun k := Classical.choose (h k)
  map_one' := by
    apply (algebraMap K E).injective
    show algebraMap K E (Classical.choose (h 1)) = algebraMap K E 1
    rw [← Classical.choose_spec (h 1)]; simp
  map_mul' x y := by
    apply (algebraMap K E).injective
    show algebraMap K E (Classical.choose (h (x * y))) =
      algebraMap K E (Classical.choose (h x) * Classical.choose (h y))
    have hs : ∀ k, algebraMap K E (Classical.choose (h k)) = cj (algebraMap K E k) :=
      fun k => (Classical.choose_spec (h k)).symm
    rw [hs (x * y), map_mul (algebraMap K E) (Classical.choose (h x)), hs x, hs y, map_mul, map_mul]
  map_zero' := by
    apply (algebraMap K E).injective
    show algebraMap K E (Classical.choose (h 0)) = algebraMap K E 0
    rw [← Classical.choose_spec (h 0)]; simp
  map_add' x y := by
    apply (algebraMap K E).injective
    show algebraMap K E (Classical.choose (h (x + y))) =
      algebraMap K E (Classical.choose (h x) + Classical.choose (h y))
    have hs : ∀ k, algebraMap K E (Classical.choose (h k)) = cj (algebraMap K E k) :=
      fun k => (Classical.choose_spec (h k)).symm
    rw [hs (x + y), map_add (algebraMap K E) (Classical.choose (h x)), hs x, hs y, map_add, map_add]

theorem conjK_spec (cj : E ≃ₐ[ℚ] E)
    (h : ∀ k : K, ∃ k' : K, cj (algebraMap K E k) = algebraMap K E k') (k : K) :
    algebraMap K E (conjK cj h k) = cj (algebraMap K E k) :=
  (Classical.choose_spec (h k)).symm

theorem sum_conj (cj : E ≃ₐ[ℚ] E)
    (h : ∀ k : K, ∃ k' : K, cj (algebraMap K E k) = algebraMap K E k') {ι : Type} [Fintype ι]
    (v w : ι → K) :
    ∑ i, algebraMap K E (v i) * cj (algebraMap K E (w i)) = algebraMap K E (hf (conjK cj h) v w) := by
  simp only [hf, map_sum, map_mul, conjK_spec]

theorem trace_natCast_mul (cj : E ≃ₐ[ℚ] E) (s t : ℕ) (x y : E) :
    Algebra.trace K E (((s : E) * x) * cj ((t : E) * y)) =
      ((s * t : ℕ) : K) * Algebra.trace K E (x * cj y) := by
  have e : ((s : E) * x) * cj ((t : E) * y) = algebraMap K E ((s * t : ℕ) : K) * (x * cj y) := by
    rw [map_mul cj, map_natCast cj, map_natCast]; push_cast; ring
  rw [e, ← Algebra.smul_def, map_smul, smul_eq_mul]

end conj

section rp
variable {K : Type} [Field K] [NumberField K] {p : ℕ}

theorem Rp_finset {α : Type} (T : Finset α) (f : α → K) (h : ∀ z ∈ T, Rp K p (f z)) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ z ∈ T, (s : K) * f z ∈ (algebraMap (𝓞 K) K).range := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, Nat.coprime_one_left p, by simp⟩
  | insert a T ha ih =>
    obtain ⟨s, hs, hsT⟩ := ih fun z hz => h z (Finset.mem_insert_of_mem hz)
    obtain ⟨t, ht, hta⟩ := h a (Finset.mem_insert_self a T)
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, fun z hz => ?_⟩
    rcases Finset.mem_insert.mp hz with rfl | hz
    · have e : ((s * t : ℕ) : K) * f z = (s : K) * ((t : K) * f z) := by push_cast; ring
      rw [e]
      exact Subring.mul_mem _ (natCast_mem _ s) hta
    · have e : ((s * t : ℕ) : K) * f z = (t : K) * ((s : K) * f z) := by push_cast; ring
      rw [e]
      exact Subring.mul_mem _ (natCast_mem _ t) (hsT z hz)


end rp

section main
variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

theorem conjK_invol (cj : E ≃ₐ[ℚ] E) (hc : PI.KerIso.IsConj K cj) (k : K) :
    conjK cj hc.2.1 (conjK cj hc.2.1 k) = k :=
  (algebraMap K E).injective (by rw [conjK_spec, conjK_spec, hc.1])


theorem hf_isom (cj : E ≃ₐ[ℚ] E)
    (h : ∀ k : K, ∃ k' : K, cj (algebraMap K E k) = algebraMap K E k') {n : Type} [Fintype n]
    (g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)) (hg : PI.KerIso.IsIsom cj g₀) (x y : Fin 4 → E) :
    hf (conjK cj h) (g₀ x) (g₀ y) = ∑ a, Algebra.trace K E (x a * cj (y a)) :=
  (algebraMap K E).injective (by rw [← sum_conj, hg])

def Lset {n : Type} [Fintype n] (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (p : ℕ)
    (g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)) : Set (Fin 4 × n → K) :=
  {v | ∃ s : ℕ, Nat.Coprime s p ∧ ∀ a, (s : E) * g₀.symm v a ∈ I}

end main

end PI.KLW
end
end

section
noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KLW

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

theorem trace_mul_natCast (cj : E ≃ₐ[ℚ] E) (s : ℕ) (z y : E) :
    Algebra.trace K E (z * cj ((s : E) * y)) = (s : K) * Algebra.trace K E (z * cj y) := by
  have e : z * cj ((s : E) * y) = algebraMap K E (s : K) * (z * cj y) := by
    rw [map_mul cj, map_natCast cj, map_natCast]; ring
  rw [e, ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem exists_ne_zero_mem (cj : E ≃ₐ[ℚ] E) (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hI : PI.KerIso.SelfDualI K cj I) : ∃ y0 ∈ I, y0 ≠ 0 := by
  by_contra hne
  push Not at hne
  have h1 : (1 : E) ∈ I := (hI 1).2 fun z hz => by
    rw [hne z hz, zero_mul, map_zero]; exact zero_mem _
  exact one_ne_zero (hne 1 h1)

theorem exists_natCast_mul_mem (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) {y0 : E}
    (hy0 : y0 ∈ I) (hne : y0 ≠ 0) (e : E) : ∃ N : ℕ, N ≠ 0 ∧ (N : E) * e ∈ I := by
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (L := E) {e / y0}
  have hi : IsIntegral ℤ ((y : E) * (e / y0)) := by
    have := hint (e / y0) (Finset.mem_singleton_self _)
    simpa [zsmul_eq_mul] using this
  have hN : IsIntegral ℤ ((y.natAbs : E) * (e / y0)) := by
    rcases Int.natAbs_eq y with h | h
    · have : (y.natAbs : E) = (y : E) := by rw [← Int.cast_natCast, ← h]
      rw [this]; exact hi
    · have : (y.natAbs : E) = -(y : E) := by
        have h' : (y.natAbs : ℤ) = -y := by omega
        rw [← Int.cast_natCast, h', Int.cast_neg]
      rw [this, neg_mul]; exact hi.neg
  refine ⟨y.natAbs, Int.natAbs_ne_zero.mpr hy, ?_⟩
  have key : (y.natAbs : E) * e = ((⟨(y.natAbs : E) * (e / y0), hN⟩ : 𝓞 E) : E) * y0 := by
    show (y.natAbs : E) * e = (y.natAbs : E) * (e / y0) * y0
    field_simp
  rw [key]
  exact (I : Submodule (𝓞 E) E).smul_mem (⟨(y.natAbs : E) * (e / y0), hN⟩ : 𝓞 E) hy0

theorem natCast_mul_mem (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (q : ℕ) {z : E}
    (hz : z ∈ I) : (q : E) * z ∈ I := by
  have := (I : Submodule (𝓞 E) E).smul_mem (q : 𝓞 E) hz
  rwa [Algebra.smul_def, map_natCast] at this

variable (cj : E ≃ₐ[ℚ] E) (hc : PI.KerIso.IsConj K cj) {n : Type} [Fintype n]
  (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (p : ℕ)
  (g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K))

include hc in
theorem lset_unimod (hI : PI.KerIso.SelfDualI K cj I) (hg : PI.KerIso.IsIsom cj g₀) :
    Unimod K (conjK cj hc.2.1) p (Lset I p g₀) := by
  intro v
  constructor
  · rintro ⟨s, hs, hsv⟩ w ⟨t, ht, htw⟩
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
    have e1 : hf (conjK cj hc.2.1) v w =
        ∑ a, Algebra.trace K E (g₀.symm v a * cj (g₀.symm w a)) := by
      rw [← hf_isom cj hc.2.1 g₀ hg]; simp
    rw [e1, Finset.mul_sum]
    refine Subring.sum_mem _ fun a _ => ?_
    rw [← trace_natCast_mul]
    exact (hI _).1 (htw a) _ (hsv a)
  · intro hv
    set x := g₀.symm v with hx

    have claim1 : ∀ a, ∀ z ∈ I, Rp K p (Algebra.trace K E (z * cj (x a))) := by
      intro a z hz
      classical
      have hw : g₀ (Pi.single a z) ∈ Lset I p g₀ := ⟨1, Nat.coprime_one_left p, fun b => by
        rw [Nat.cast_one, one_mul, LinearEquiv.symm_apply_apply]
        by_cases hb : b = a
        · subst hb; simpa using hz
        · rw [Pi.single_eq_of_ne hb]; exact FractionalIdeal.mem_coe.mp (I : Submodule (𝓞 E) E).zero_mem⟩
      have h2 := Rp_map (conjK cj hc.2.1) (hv _ hw)
      rw [← hf_symm _ (conjK_invol cj hc)] at h2
      have e2 : hf (conjK cj hc.2.1) (g₀ (Pi.single a z)) v =
          Algebra.trace K E (z * cj (x a)) := by
        have : v = g₀ x := by simp [hx]
        rw [this, hf_isom cj hc.2.1 g₀ hg, Finset.sum_eq_single a]
        · simp
        · intro b _ hb; simp [hb]
        · intro h; exact absurd (Finset.mem_univ a) h
      rwa [e2] at h2

    obtain ⟨T, hT⟩ := (FractionalIdeal.fg_of_isNoetherianRing le_rfl I).restrictScalars (R := ℤ)
    have hTI : ∀ z ∈ T, z ∈ I := fun z hz => by
      have : z ∈ ((I : Submodule (𝓞 E) E).restrictScalars ℤ) := hT ▸ Submodule.subset_span hz
      exact this
    have claim2 : ∀ a, ∃ s : ℕ, Nat.Coprime s p ∧
        ∀ z ∈ I, (s : K) * Algebra.trace K E (z * cj (x a)) ∈ (algebraMap (𝓞 K) K).range := by
      intro a
      obtain ⟨s, hs, hsT⟩ := Rp_finset (p := p) T (fun z => Algebra.trace K E (z * cj (x a)))
        fun z hz => claim1 a z (hTI z hz)
      refine ⟨s, hs, fun z hz => ?_⟩
      have hz' : z ∈ Submodule.span ℤ (T : Set E) := by
        rw [hT]; exact hz
      clear hz
      induction hz' using Submodule.span_induction with
      | mem z hz => exact hsT z hz
      | zero => simp
      | add z z' _ _ h h' =>
        rw [add_mul, map_add, mul_add]; exact Subring.add_mem _ h h'
      | smul k z _ h =>
        have e : (s : K) * Algebra.trace K E ((k • z) * cj (x a)) =
            k • ((s : K) * Algebra.trace K E (z * cj (x a))) := by
          rw [smul_mul_assoc, map_zsmul, mul_smul_comm]
        rw [e]; exact Subring.zsmul_mem _ h k
    choose s hs hsI using claim2
    refine ⟨∏ a, s a, Nat.Coprime.prod_left fun a _ => hs a, fun a => (hI _).2 fun z hz => ?_⟩
    rw [trace_mul_natCast]
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem s (Finset.mem_univ a)
    rw [hq, Nat.cast_mul, mul_comm (s a : K), mul_assoc]
    exact Subring.mul_mem _ (natCast_mem _ q) (hsI a z hz)

include hc in
theorem lset_spans (hI : PI.KerIso.SelfDualI K cj I) : Spans K (Lset I p g₀) := by
  intro v
  obtain ⟨y0, hy0, hne⟩ := exists_ne_zero_mem cj I hI
  choose N hN hNI using fun a => exists_natCast_mul_mem I hy0 hne (g₀.symm v a)
  refine ⟨∏ a, N a, Finset.prod_ne_zero_iff.mpr fun a _ => hN a, 1, Nat.coprime_one_left p,
    fun a => ?_⟩
  rw [Nat.cast_one, one_mul, map_smul, Pi.smul_apply, Algebra.smul_def, map_natCast]
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ a)
  rw [hq, Nat.cast_mul, mul_comm (N a : E), mul_assoc]
  exact natCast_mul_mem I q (hNI a)

end PI.KLW
end
end

section
noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KLW


end PI.KLW
end
end

section
noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KLW.Ind

open PI.KLW

theorem exists_refl {K : Type} [Field K] (c : K →+* K) (hc : ∀ x, c (c x) = x) {ι : Type}
    [Fintype ι] (e0 e : ι → K) (h0 : hf c e0 e0 = 1) (h1 : hf c e e = 1) (hne : hf c e0 e ≠ 1) :
    ∃ σ : (ι → K) ≃ₗ[K] (ι → K), IsUnitary c σ ∧ σ e0 = e := by
  obtain ⟨w, hw⟩ : ∃ w, w = e0 - e := ⟨_, rfl⟩
  obtain ⟨t, htdef⟩ : ∃ t, t = hf c e0 w := ⟨_, rfl⟩
  have ht : t = 1 - hf c e0 e := by rw [htdef, hw, hf_sub_right, h0]
  have ht0 : t ≠ 0 := by rw [ht]; exact sub_ne_zero.mpr (Ne.symm hne)
  have hct : c t = 1 - hf c e e0 := by rw [htdef, hf_conj c hc, hw, hf_sub_left, h0]
  have hww : hf c w w = t + c t := by
    rw [hct, ht, hw, hf_sub_left, hf_sub_right, hf_sub_right, h0, h1]
    ring
  have hct0 : c t ≠ 0 := (map_ne_zero c).mpr ht0
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = t⁻¹ := ⟨_, rfl⟩
  have key : γ + c γ = γ * c γ * hf c w w := by
    rw [hww, hγ, map_inv₀]
    field_simp
    ring
  let φ : (ι → K) →ₗ[K] K :=
    { toFun := fun v => γ * hf c v w
      map_add' := fun a b => by rw [hf_add_left, mul_add]
      map_smul' := fun k a => by rw [hf_smul_left, RingHom.id_apply, smul_eq_mul]; ring }
  let σL : (ι → K) →ₗ[K] (ι → K) := LinearMap.id - φ.smulRight w
  have hσ : ∀ v, σL v = v - (γ * hf c v w) • w := fun v => rfl
  have iso : ∀ v v', hf c (σL v) (σL v') = hf c v v' := by
    intro v v'
    rw [hσ, hσ]
    simp only [hf_sub_left, hf_sub_right, hf_smul_left, hf_smul_right, map_mul]
    rw [← hf_conj c hc v' w]
    linear_combination (-(hf c v w * c (hf c v' w))) * key
  refine ⟨mkU c σL iso, mkU_unitary c σL iso, ?_⟩
  rw [mkU_apply, hσ, ← htdef, hγ, inv_mul_cancel₀ ht0, one_smul, hw, sub_sub_cancel]



def extL {K : Type} [Field K] {ι : Type} [DecidableEq ι] (i0 : ι) :
    ({i // i ≠ i0} → K) →ₗ[K] (ι → K) where
  toFun w i := if h : i = i0 then 0 else w ⟨i, h⟩
  map_add' a b := by
    funext i
    by_cases h : i = i0 <;> simp [h]
  map_smul' k a := by
    funext i
    by_cases h : i = i0 <;> simp [h]

def resL {K : Type} [Field K] {ι : Type} (i0 : ι) : (ι → K) →ₗ[K] ({i // i ≠ i0} → K) :=
  LinearMap.funLeft K K Subtype.val

theorem extL_self {K : Type} [Field K] {ι : Type} [DecidableEq ι] (i0 : ι)
    (w : {i // i ≠ i0} → K) : extL i0 w i0 = 0 := by
  simp [extL]

theorem extL_ne {K : Type} [Field K] {ι : Type} [DecidableEq ι] (i0 : ι)
    (w : {i // i ≠ i0} → K) (j : {i // i ≠ i0}) : extL i0 w j.1 = w j := by
  simp [extL, j.2]

theorem resL_apply {K : Type} [Field K] {ι : Type} (i0 : ι) (v : ι → K) (j : {i // i ≠ i0}) :
    resL i0 v j = v j.1 := rfl

theorem decomp {K : Type} [Field K] {ι : Type} [DecidableEq ι] (i0 : ι) (v : ι → K) :
    v = extL i0 (resL i0 v) + v i0 • Pi.single i0 1 := by
  funext i
  by_cases h : i = i0
  · subst h
    simp [extL_self]
  · have := extL_ne i0 (resL i0 v) ⟨i, h⟩
    simp only at this
    simp [this, resL_apply, Pi.single_eq_of_ne h]

theorem hf_ext_ext {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (i0 : ι) (a b : {i // i ≠ i0} → K) : hf c (extL i0 a) (extL i0 b) = hf c a b := by
  unfold hf
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i0]
  simp only [extL_self, extL_ne, zero_mul, zero_add]

theorem hf_decomp {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (i0 : ι) (a b : {i // i ≠ i0} → K) (x y : K) :
    hf c (extL i0 a + x • Pi.single i0 1) (extL i0 b + y • Pi.single i0 1)
      = hf c a b + x * c y := by
  simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, hf_ext_ext,
    hf_single_right, hf_single_left, extL_self, map_zero, Pi.add_apply, Pi.smul_apply,
    Pi.single_eq_same, smul_eq_mul, mul_one, zero_add]
  ring

theorem split_step {K : Type} [Field K] [NumberField K] (c : K →+* K) (p : ℕ) {ι : Type}
    [Fintype ι] [DecidableEq ι] (i0 : ι) (L : Set (ι → K)) (hL : Unimod K c p L)
    (hS : Spans K L) (he : Pi.single i0 (1 : K) ∈ L)
    (hrec : ∀ L' : Set ({i // i ≠ i0} → K), Unimod K c p L' → Spans K L' →
      ∃ u : ({i // i ≠ i0} → K) ≃ₗ[K] ({i // i ≠ i0} → K),
        IsUnitary c u ∧ ∀ v, v ∈ L' ↔ ∀ j, Rp K p (u v j)) :
    ∃ u : (ι → K) ≃ₗ[K] (ι → K), IsUnitary c u ∧ ∀ v, v ∈ L ↔ ∀ i, Rp K p (u v i) := by
  have hv0 : ∀ v ∈ L, Rp K p (v i0) := fun v hv => by
    have := (hL v).1 hv _ he
    rwa [hf_single_right] at this
  have hres : ∀ v ∈ L, extL i0 (resL i0 v) ∈ L := fun v hv => by
    have e1 : extL i0 (resL i0 v) = v + (-(v i0)) • Pi.single i0 1 := by
      rw [neg_smul, ← sub_eq_add_neg]
      exact eq_sub_iff_add_eq.mpr (decomp i0 v).symm
    rw [e1]
    exact add_smul_mem hL hv he (rp_neg (hv0 v hv))
  let L' : Set ({i // i ≠ i0} → K) := {a | extL i0 a ∈ L}
  have hL' : Unimod K c p L' := by
    intro a
    constructor
    · intro ha b hb
      rw [← hf_ext_ext c i0]
      exact (hL _).1 ha _ hb
    · intro h
      show extL i0 a ∈ L
      rw [hL]
      intro x hx
      rw [decomp i0 x, hf_add_right, hf_smul_right, hf_single_right, extL_self, mul_zero,
        add_zero, hf_ext_ext]
      exact h _ (hres x hx)
  have hS' : Spans K L' := fun a => by
    obtain ⟨N, hN, h⟩ := hS (extL i0 a)
    exact ⟨N, hN, by show extL i0 _ ∈ L; rw [map_smul]; exact h⟩
  obtain ⟨u', hu', hmem'⟩ := hrec L' hL' hS'
  let U : (ι → K) →ₗ[K] (ι → K) :=
    extL i0 ∘ₗ (u'.toLinearMap ∘ₗ resL i0) + (LinearMap.proj i0).smulRight (Pi.single i0 1)
  have hU : ∀ v, U v = extL i0 (u' (resL i0 v)) + v i0 • Pi.single i0 1 := fun v => rfl
  have iso : ∀ v w, hf c (U v) (U w) = hf c v w := by
    intro v w
    rw [hU, hU, hf_decomp, hu']
    conv_rhs => rw [decomp i0 v, decomp i0 w]
    rw [hf_decomp]
  refine ⟨mkU c U iso, mkU_unitary c U iso, fun v => ?_⟩
  simp only [mkU_apply]
  have hUi0 : U v i0 = v i0 := by
    rw [hU]
    simp [extL_self]
  have hUj : ∀ j : {i // i ≠ i0}, U v j.1 = u' (resL i0 v) j := fun j => by
    rw [hU, Pi.add_apply, extL_ne, Pi.smul_apply, Pi.single_eq_of_ne j.2, smul_zero, add_zero]
  constructor
  · intro hv i
    by_cases h : i = i0
    · subst h
      rw [hUi0]
      exact hv0 v hv
    · have := hUj ⟨i, h⟩
      simp only at this
      rw [this]
      exact (hmem' _).1 (hres v hv) _
  · intro h
    have h0 : Rp K p (v i0) := hUi0 ▸ h i0
    have h1 : resL i0 v ∈ L' := (hmem' _).2 fun j => hUj j ▸ h j.1
    rw [decomp i0 v]
    exact add_smul_mem hL h1 he h0




end PI.KLW.Ind

namespace PI.KLW


end PI.KLW
end
end

section
namespace PI.KLW


end PI.KLW
end
