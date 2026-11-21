import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FourSquareQuaternions.FourSqOf

section
noncomputable section
open scoped BigOperators
open Module

namespace PI.KerIso.FourSqW

section Conj

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

def conjFun (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (k : K) : K := Classical.choose (hc.2.1 k)

theorem conjFun_spec (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (k : K) :
    algebraMap K E (conjFun cj hc k) = cj (algebraMap K E k) :=
  (Classical.choose_spec (hc.2.1 k)).symm

theorem conjFun_conjFun (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (k : K) :
    conjFun cj hc (conjFun cj hc k) = k :=
  (algebraMap K E).injective (by rw [conjFun_spec, conjFun_spec, hc.1])

def conjK (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) : K ≃+* K where
  toFun := conjFun cj hc
  invFun := conjFun cj hc
  left_inv := conjFun_conjFun cj hc
  right_inv := conjFun_conjFun cj hc
  map_mul' x y := (algebraMap K E).injective (by
    rw [conjFun_spec, map_mul, map_mul, map_mul, conjFun_spec, conjFun_spec])
  map_add' x y := (algebraMap K E).injective (by
    rw [conjFun_spec, map_add, map_add, map_add, conjFun_spec, conjFun_spec])

theorem conjK_apply (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (k : K) : conjK cj hc k = conjFun cj hc k := rfl

theorem trace_cj (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (z : E) :
    algebraMap K E (Algebra.trace K E (cj z)) = cj (algebraMap K E (Algebra.trace K E z)) := by
  have he : (algebraMap K E).comp (conjK cj hc : K →+* K) = (cj.toRingEquiv : E →+* E).comp (algebraMap K E) := by
    ext k
    simp only [RingHom.comp_apply, RingHom.coe_coe, conjK_apply, conjFun_spec]
    rfl
  have h1 := Algebra.trace_eq_of_equiv_equiv (conjK cj hc) cj.toRingEquiv he z
  have h2 : conjK cj hc (Algebra.trace K E z) = Algebra.trace K E (cj z) := by
    rw [h1, RingEquiv.apply_symm_apply]
    rfl
  rw [← h2, conjK_apply, conjFun_spec]

theorem fixed_rat (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (h2 : finrank ℚ K = 2) (k : K)
    (hk : cj (algebraMap K E k) = algebraMap K E k) : ∃ r : ℚ, k = (r : K) := by
  let φ : K →ₗ[ℚ] E := (IsScalarTower.toAlgHom ℚ K E).toLinearMap
  let L : K →ₗ[ℚ] E := cj.toLinearMap.comp φ - φ
  have hL : ∀ x, L x = cj (algebraMap K E x) - algebraMap K E x := fun x => rfl
  have hker : ∀ x, x ∈ LinearMap.ker L ↔ cj (algebraMap K E x) = algebraMap K E x := by
    intro x; rw [LinearMap.mem_ker, hL, sub_eq_zero]
  have hrange : LinearMap.range L ≠ ⊥ := by
    obtain ⟨k0, hk0⟩ := hc.2.2
    intro h
    rw [LinearMap.range_eq_bot] at h
    apply hk0
    have := congrArg (fun f : K →ₗ[ℚ] E => f k0) h
    simp only [LinearMap.zero_apply, hL, sub_eq_zero] at this
    exact this
  have hr1 : 1 ≤ finrank ℚ (LinearMap.range L) := Submodule.one_le_finrank_iff.mpr hrange
  have hsum := L.finrank_range_add_finrank_ker
  have hk1 : finrank ℚ (LinearMap.ker L) ≤ 1 := by omega
  have h1mem : (1 : K) ∈ LinearMap.ker L := by
    rw [hker, map_one, map_one]
  have hle : Submodule.span ℚ {(1 : K)} ≤ LinearMap.ker L := by
    rw [Submodule.span_le, Set.singleton_subset_iff]; exact h1mem
  have hfr : finrank ℚ (Submodule.span ℚ {(1 : K)}) = 1 := finrank_span_singleton one_ne_zero
  have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
  have hkmem : k ∈ Submodule.span ℚ {(1 : K)} := by rw [heq, hker]; exact hk
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hkmem
  exact ⟨r, by rw [← hr, Rat.smul_one_eq_cast]⟩

end Conj

section Orth

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

def trL (cj : E ≃ₐ[ℚ] E) (y : E) : E →ₗ[K] K :=
  (Algebra.trace K E).comp (LinearMap.mulRight K (cj y))

theorem trL_apply (cj : E ≃ₐ[ℚ] E) (y x : E) : trL (K := K) cj y x = Algebra.trace K E (x * cj y) := rfl

theorem tr_swap (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (x y : E) :
    algebraMap K E (Algebra.trace K E (y * cj x)) = cj (algebraMap K E (Algebra.trace K E (x * cj y))) := by
  rw [← trace_cj cj hc, map_mul cj, hc.1, mul_comm]

theorem tr_swap_zero (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (x y : E)
    (h : Algebra.trace K E (x * cj y) = 0) : Algebra.trace K E (y * cj x) = 0 := by
  apply (algebraMap K E).injective
  rw [tr_swap cj hc, h, map_zero, map_zero]

theorem tr_self_ne (cj : E ≃ₐ[ℚ] E) (hpos : ∀ x : E, x ≠ 0 → 0 < Algebra.trace ℚ E (x * cj x))
    (x : E) (hx : x ≠ 0) : Algebra.trace K E (x * cj x) ≠ 0 := by
  have : Module.Finite K E := Module.Finite.of_restrictScalars_finite ℚ K E
  intro h
  have := hpos x hx
  rw [← Algebra.trace_trace (S := K), h, map_zero] at this
  exact lt_irrefl _ this

theorem tr_self_rat (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj) (h2 : finrank ℚ K = 2)
    (hpos : ∀ x : E, x ≠ 0 → 0 < Algebra.trace ℚ E (x * cj x)) (x : E) (hx : x ≠ 0) :
    ∃ r : ℚ, 0 < r ∧ Algebra.trace K E (x * cj x) = (r : K) := by
  have : Module.Finite K E := Module.Finite.of_restrictScalars_finite ℚ K E
  have hfix : cj (algebraMap K E (Algebra.trace K E (x * cj x))) = algebraMap K E (Algebra.trace K E (x * cj x)) :=
    (tr_swap cj hc x x).symm
  obtain ⟨r, hr⟩ := fixed_rat cj hc h2 _ hfix
  refine ⟨r, ?_, hr⟩
  have := hpos x hx
  rw [← Algebra.trace_trace (S := K), hr] at this
  have h3 : Algebra.trace ℚ K (r : K) = 2 * r := by
    rw [show (r : K) = algebraMap ℚ K r from rfl, Algebra.trace_algebraMap, h2, nsmul_eq_mul]
    norm_num
  rw [h3] at this
  linarith

theorem exists_orth (cj : E ≃ₐ[ℚ] E) (hc : IsConj K cj)
    (hpos : ∀ x : E, x ≠ 0 → 0 < Algebra.trace ℚ E (x * cj x)) :
    ∀ m : ℕ, m ≤ finrank K E → ∃ e : Fin m → E, (∀ i, e i ≠ 0) ∧
      ∀ i j, i ≠ j → Algebra.trace K E (e i * cj (e j)) = 0 := by
  have : Module.Finite K E := Module.Finite.of_restrictScalars_finite ℚ K E
  intro m
  induction m with
  | zero => intro _; exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    intro hm
    obtain ⟨e, he0, heo⟩ := ih (by omega)
    let F : E →ₗ[K] (Fin m → K) := LinearMap.pi (fun i => trL cj (e i))
    have hF : LinearMap.ker F ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
      rw [Module.finrank_fin_fun]; omega)
    obtain ⟨x, hxk, hx0⟩ := (Submodule.ne_bot_iff _).mp hF
    have hxo : ∀ i, Algebra.trace K E (x * cj (e i)) = 0 := by
      intro i
      have := congrArg (fun f => f i) (LinearMap.mem_ker.mp hxk)
      simpa [F, trL_apply] using this
    refine ⟨Fin.snoc e x, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa using hx0
      · simpa using he0 i
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd rfl hij
        | cast j => simpa using hxo j
      | cast i =>
        induction j using Fin.lastCases with
        | last => simpa using tr_swap_zero cj hc _ _ (hxo i)
        | cast j =>
          have : i ≠ j := fun h => hij (by rw [h])
          simpa using heo i j this

theorem orth_linInd {n : Type} [Fintype n] (cj : E ≃ₐ[ℚ] E)
    (hpos : ∀ x : E, x ≠ 0 → 0 < Algebra.trace ℚ E (x * cj x)) (v : n → E)
    (hv0 : ∀ i, v i ≠ 0) (hvo : ∀ i j, i ≠ j → Algebra.trace K E (v i * cj (v j)) = 0) :
    LinearIndependent K v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := congrArg (trL (K := K) cj (v j)) hg
  rw [map_sum, map_zero, Finset.sum_eq_single j] at h
  · rw [map_smul, trL_apply, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_right (tr_self_ne cj hpos _ (hv0 j))
  · intro i _ hij
    rw [map_smul, trL_apply, hvo i j hij, smul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem orthogonal_diagonal : OrthDiag := by
  intro K E _ _ _ _ _ cj n _ h2 hn hc hpos
  classical
  have : Module.Finite K E := Module.Finite.of_restrictScalars_finite ℚ K E
  obtain ⟨e, he0, heo⟩ := exists_orth (K := K) cj hc hpos (finrank K E) le_rfl
  let σ : n ≃ Fin (finrank K E) := Fintype.equivFinOfCardEq hn
  let v : n → E := fun i => e (σ i)
  have hv0 : ∀ i, v i ≠ 0 := fun i => he0 _
  have hvo : ∀ i j, i ≠ j → Algebra.trace K E (v i * cj (v j)) = 0 :=
    fun i j hij => heo _ _ (fun h => hij (σ.injective h))
  have hli := orth_linInd (K := K) cj hpos v hv0 hvo
  let b : Basis n K E := basisOfLinearIndependentOfCardEqFinrank' v hli hn
  have hb : ∀ i, b i = v i := fun i => by simp [b]
  choose q hq0 hq using fun i => tr_self_rat (K := K) cj hc h2 hpos (v i) (hv0 i)
  refine ⟨b, q, hq0, ?_⟩

  have hcol : ∀ y i, Algebra.trace K E (y * cj (v i)) = b.repr y i * (q i : K) := by
    intro y i
    have h := congrArg (trL (K := K) cj (v i)) (b.sum_repr y)
    rw [map_sum, Finset.sum_eq_single i] at h
    · rw [← trL_apply, ← h, map_smul, trL_apply, hb, hq, smul_eq_mul]
    · intro j _ hji
      rw [map_smul, trL_apply, hb, hvo j i hji, smul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  intro x y
  have hx := congrArg (fun z => algebraMap K E (trL (K := K) cj y z)) (b.sum_repr x)
  simp only [map_sum, map_smul, trL_apply, smul_eq_mul, map_mul] at hx
  rw [← hx]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hb, tr_swap cj hc, hcol, map_mul, map_mul, map_ratCast, map_ratCast]
  ring

end Orth

end PI.KerIso.FourSqW
end
end

section
noncomputable section
open scoped BigOperators Matrix

namespace PI.KerFourSqW

def quatMat (r₁ r₂ r₃ r₄ : ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  !![r₁, -r₂, -r₃, -r₄;
     r₂, r₁, -r₄, r₃;
     r₃, r₄, r₁, -r₂;
     r₄, -r₃, r₂, r₁]

theorem quatMat_transpose_mul (r₁ r₂ r₃ r₄ : ℚ) :
    (quatMat r₁ r₂ r₃ r₄)ᵀ * quatMat r₁ r₂ r₃ r₄ = (r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2 + r₄ ^ 2) • (1 : Matrix (Fin 4) (Fin 4) ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatMat, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;> ring

theorem rat_sum_four_squares (a : ℚ) (ha : 0 < a) :
    ∃ r₁ r₂ r₃ r₄ : ℚ, r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2 + r₄ ^ 2 = a := by
  obtain ⟨s₁, s₂, s₃, s₄, hs⟩ := Nat.sum_four_squares (a.num.toNat * a.den)
  have hnum : 0 < a.num := Rat.num_pos.mpr ha
  have hden : (0 : ℚ) < a.den := by exact_mod_cast a.pos
  refine ⟨s₁ / a.den, s₂ / a.den, s₃ / a.den, s₄ / a.den, ?_⟩
  have hcast : ((a.num.toNat * a.den : ℕ) : ℚ) = (a.num : ℚ) * a.den := by
    push_cast
    congr 1
    exact_mod_cast Int.toNat_of_nonneg hnum.le
  have h1 : ((s₁ : ℚ) ^ 2 + (s₂ : ℚ) ^ 2 + (s₃ : ℚ) ^ 2 + (s₄ : ℚ) ^ 2) = (a.num : ℚ) * a.den := by
    rw [← hcast]; exact_mod_cast hs
  rw [div_pow, div_pow, div_pow, div_pow, ← add_div, ← add_div, ← add_div, h1, pow_two, ← div_div,
    mul_div_cancel_right₀ _ hden.ne', Rat.num_div_den]

theorem exists_quat (a : ℚ) (ha : 0 < a) :
    ∃ Q : Matrix (Fin 4) (Fin 4) ℚ, Qᵀ * Q = a • (1 : Matrix (Fin 4) (Fin 4) ℚ) := by
  obtain ⟨r₁, r₂, r₃, r₄, h⟩ := rat_sum_four_squares a ha
  exact ⟨quatMat r₁ r₂ r₃ r₄, by rw [quatMat_transpose_mul, h]⟩

theorem sum_mul_cast {L : Type*} [Field L] [CharZero L] (Q : Matrix (Fin 4) (Fin 4) ℚ) (a : ℚ)
    (hQ : Qᵀ * Q = a • (1 : Matrix (Fin 4) (Fin 4) ℚ)) (j k : Fin 4) :
    ∑ b, (Q b j : L) * (Q b k : L) = if j = k then (a : L) else 0 := by
  have h := congrFun (congrFun hQ j) k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul] at h
  have h' : ((∑ b, Q b j * Q b k : ℚ) : L) = ((a * if j = k then 1 else 0 : ℚ) : L) := by rw [h]
  push_cast at h'
  rw [h']
  split_ifs <;> simp

theorem quat_herm {L F : Type*} [Field L] [CharZero L] [FunLike F L L] [RingHomClass F L L] (c : F) (Q : Matrix (Fin 4) (Fin 4) ℚ) (a : ℚ)
    (hQ : Qᵀ * Q = a • (1 : Matrix (Fin 4) (Fin 4) ℚ)) (x y : Fin 4 → L) :
    ∑ b, (∑ j, (Q b j : L) * x j) * c (∑ k, (Q b k : L) * y k) = (a : L) * ∑ j, x j * c (y j) := by
  have hc : ∀ b, c (∑ k, (Q b k : L) * y k) = ∑ k, (Q b k : L) * c (y k) := by
    intro b
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_ratCast]
  simp_rw [hc, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  have : ∀ j, ∑ b, ∑ k, (Q b j : L) * x j * ((Q b k : L) * c (y k))
      = ∑ k, (∑ b, (Q b j : L) * (Q b k : L)) * (x j * c (y k)) := by
    intro j
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  simp_rw [this, sum_mul_cast Q a hQ, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.mul_sum]

end PI.KerFourSqW
end
end

section
noncomputable section
open scoped BigOperators Matrix

namespace PI.KerIso.FourSqW

open PI.KerFourSqW

def qmap {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E] {n : Type*}
    (b : Module.Basis n K E) (Q : n → Matrix (Fin 4) (Fin 4) ℚ) :
    (Fin 4 → E) →ₗ[K] (Fin 4 × n → K) where
  toFun x w := ∑ a, (Q w.2 w.1 a : K) * b.repr (x a) w.2
  map_add' x y := by
    ext w
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext w
    simp [Finset.mul_sum, mul_left_comm]

theorem qmap_apply {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E] {n : Type*}
    (b : Module.Basis n K E) (Q : n → Matrix (Fin 4) (Fin 4) ℚ) (x : Fin 4 → E) (w : Fin 4 × n) :
    qmap b Q x w = ∑ a, (Q w.2 w.1 a : K) * b.repr (x a) w.2 := rfl

theorem qmap_back {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E] {n : Type*}
    (b : Module.Basis n K E) (Q : n → Matrix (Fin 4) (Fin 4) ℚ) (q : n → ℚ)
    (hQ : ∀ i, (Q i)ᵀ * Q i = q i • (1 : Matrix (Fin 4) (Fin 4) ℚ)) (x : Fin 4 → E) (a' : Fin 4) (i : n) :
    ∑ c, (Q i c a' : K) * qmap b Q x (c, i) = (q i : K) * b.repr (x a') i := by
  simp only [qmap_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ a, ∑ c, (Q i c a' : K) * ((Q i c a : K) * b.repr (x a) i)
      = (∑ c, (Q i c a' : K) * (Q i c a : K)) * b.repr (x a) i := by
    intro a
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  simp_rw [h, sum_mul_cast (Q i) (q i) (hQ i), ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem qmap_injective {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E] {n : Type*}
    (b : Module.Basis n K E) (Q : n → Matrix (Fin 4) (Fin 4) ℚ) (q : n → ℚ) (hq : ∀ i, 0 < q i)
    (hQ : ∀ i, (Q i)ᵀ * Q i = q i • (1 : Matrix (Fin 4) (Fin 4) ℚ)) :
    Function.Injective (qmap b Q) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  funext a'
  rw [b.ext_elem_iff]
  intro i
  have h := qmap_back b Q q hQ x a' i
  simp only [hx, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h
  have hqi : (q i : K) ≠ 0 := by exact_mod_cast (hq i).ne'
  have h0 : b.repr (x a') i = 0 := by
    rcases mul_eq_zero.mp h.symm with h1 | h1
    · exact absurd h1 hqi
    · exact h1
  simp [h0]

theorem from_diagonal : FromDiag := by
  intro K E _ _ _ _ _ cj n _ b q hq hb
  choose Q hQ using fun i => exists_quat (q i) (hq i)
  have : Module.Finite K E := Module.Finite.of_basis b
  have hdim : Module.finrank K (Fin 4 → E) = Module.finrank K (Fin 4 × n → K) := by
    rw [Module.finrank_pi_fintype, Module.finrank_fintype_fun_eq_card, Module.finrank_eq_card_basis b,
      Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
  refine ⟨(qmap b Q).linearEquivOfInjective (qmap_injective b Q q hq hQ) hdim, ?_⟩
  intro x y
  simp only [LinearMap.linearEquivOfInjective_apply]
  rw [map_sum]
  unfold DiagId at hb
  simp_rw [hb]
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_comm (γ := Fin 4)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hx : ∀ c, algebraMap K E (qmap b Q x (c, i))
      = ∑ a, (Q i c a : E) * algebraMap K E (b.repr (x a) i) := by
    intro c
    rw [qmap_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, map_ratCast]
  have hy : ∀ c, algebraMap K E (qmap b Q y (c, i))
      = ∑ a, (Q i c a : E) * algebraMap K E (b.repr (y a) i) := by
    intro c
    rw [qmap_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, map_ratCast]
  simp_rw [hx, hy]
  rw [quat_herm cj (Q i) (q i) (hQ i), Finset.mul_sum]

end PI.KerIso.FourSqW
end
end

section
namespace PI.KerIso.FourSqW

theorem main : FourSq := fourSq_of orthogonal_diagonal from_diagonal

end PI.KerIso.FourSqW
end
