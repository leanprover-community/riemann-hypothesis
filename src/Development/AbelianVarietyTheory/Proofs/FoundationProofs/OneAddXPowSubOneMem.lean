import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBasisOneAddXPow
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsAdicCompleteComapConstantCoeff

section
section
noncomputable section

open GlobalTheory.Col PowerSeries

namespace GlobalTheory.Col.Interp

variable {R : Type} [CommRing R]

theorem coeff_one_add_X_pow (n k : ℕ) : coeff k ((1 + X : PowerSeries R) ^ n) = (n.choose k : R) := by
  have : ((1 + X : PowerSeries R) ^ n) = (((1 + Polynomial.X : Polynomial R) ^ n : Polynomial R) : PowerSeries R) := by
    simp
  rw [this, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

theorem one_add_X_pow_sub_one_ne_zero [Nontrivial R] (N : ℕ) (hN : 1 ≤ N) :
    ((1 + X : PowerSeries R) ^ N - 1) ≠ 0 := by
  intro h
  have := congrArg (coeff N) h
  rw [map_sub, coeff_one_add_X_pow, Nat.choose_self, coeff_one, if_neg (by omega)] at this
  simp at this

theorem cyc_succ (p n : ℕ) (hp : p.Prime) :
    cyc R p (n + 1) = ∑ i ∈ Finset.range p, ((1 + X : PowerSeries R) ^ (p ^ n)) ^ i := by
  unfold cyc
  rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum hp]
  simp [Polynomial.eval₂_finset_sum, Polynomial.eval₂_pow, Polynomial.eval₂_X]

theorem om_succ (p n : ℕ) (hp : p.Prime) :
    (1 + X : PowerSeries R) ^ (p ^ (n + 1)) - 1 = cyc R p (n + 1) * ((1 + X : PowerSeries R) ^ (p ^ n) - 1) := by
  rw [cyc_succ p n hp, geom_sum_mul, ← pow_mul, ← pow_succ]

theorem cyc_sub_p (p n : ℕ) (hp : p.Prime) :
    ∃ u : PowerSeries R, cyc R p (n + 1) - (p : PowerSeries R) = u * ((1 + X : PowerSeries R) ^ (p ^ n) - 1) := by
  refine ⟨∑ i ∈ Finset.range p, ∑ l ∈ Finset.range i, ((1 + X : PowerSeries R) ^ (p ^ n)) ^ l, ?_⟩
  rw [cyc_succ p n hp, Finset.sum_mul]
  have : (p : PowerSeries R) = ∑ i ∈ Finset.range p, (1 : PowerSeries R) := by simp
  rw [this, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [geom_sum_mul]

theorem cancel_prime [IsDomain R] {q : R} (hq : Prime q) {f : PowerSeries R}
    (hf : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {q})) f ≠ 0)
    {B s t : PowerSeries R} (m : ℕ)
    (h : C q * B = C q ^ (m + 1) * s + f * t) : ∃ t', B = C q ^ m * s + f * t' := by
  haveI : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).2 hq
  have hCq : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {q})) (C q) = 0 := by
    rw [PowerSeries.map_C, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self q), map_zero]
  have ht : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {q})) t = 0 := by
    have h2 : f * t = C q * (B - C q ^ m * s) := by rw [mul_sub, ← mul_assoc, ← pow_succ', h]; ring
    have h3 := congrArg (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {q}))) h2
    rw [map_mul, map_mul, hCq, zero_mul] at h3
    exact (mul_eq_zero.1 h3).resolve_left hf
  have hd : ∀ n, ∃ a, coeff n t = q * a := by
    intro n
    have := congrArg (coeff n) ht
    rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
    exact this
  choose a ha using hd
  have ht' : t = C q * PowerSeries.mk a := by
    ext n; rw [coeff_C_mul, coeff_mk, ha]
  refine ⟨PowerSeries.mk a, ?_⟩
  have hq0 : (C q : PowerSeries R) ≠ 0 := by
    intro h0; exact hq.ne_zero (by simpa using congrArg (constantCoeff) h0)
  apply mul_left_cancel₀ hq0
  rw [h, ht']; ring

end GlobalTheory.Col.Interp

namespace GlobalTheory.Col

open Interp in

theorem X_mul_mem_span_of_levels (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (hR : IsDomain R)
    (hpR : Prime (p : R)) (_hc : IsAdicComplete (Ideal.span {(p : R)}) R)
    (h : PowerSeries R) (k c : ℕ)
    (hyp : ∀ r, 1 ≤ r → r ≤ k → ∃ y : PowerSeries R, ev R p r h = ev R p r ((p : PowerSeries R) ^ c * y)) :
    ∀ j, j ≤ k → j ≤ c → X * h ∈ Ideal.span {(p : PowerSeries R) ^ (c - j), (1 + X) ^ (p ^ j) - 1} := by
  intro j
  induction j with
  | zero =>
    intro _ _
    refine Ideal.mem_span_pair.2 ⟨0, h, ?_⟩
    simp [mul_comm]
  | succ n ih =>
    intro hk hcn
    obtain ⟨A, B, hAB⟩ := Ideal.mem_span_pair.1 (ih (by omega) (by omega))
    obtain ⟨y, hy⟩ := hyp (n + 1) (by omega) hk
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hy)
    obtain ⟨u, hu⟩ := cyc_sub_p (R := R) p n hp.out
    obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 + n := ⟨c - (n + 1), by omega⟩
    have e1 : m + 1 + n - n = m + 1 := by omega
    have e2 : m + 1 + n - (n + 1) = m := by omega
    rw [e1] at hAB
    rw [e2]
    set P : PowerSeries R := (p : PowerSeries R) with hP
    set om : PowerSeries R := (1 + X : PowerSeries R) ^ (p ^ n) - 1 with hom
    have key : C (p : R) * B = C (p : R) ^ (m + 1) * (u * A - u * X * P ^ n * y)
        + cyc R p (n + 1) * (B - u * X * g) := by
      rw [map_natCast]
      linear_combination (-B) * hu - u * hAB + (u * X) * hg
    have hf : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : R)})) (cyc R p (n + 1)) ≠ 0 := by
      haveI : (Ideal.span {(p : R)}).IsPrime := (Ideal.span_singleton_prime hpR.ne_zero).2 hpR
      intro h0
      have h1 := congrArg (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : R)}))) (om_succ (R := R) p n hp.out)
      rw [map_mul, h0, zero_mul] at h1
      refine one_add_X_pow_sub_one_ne_zero (R := R ⧸ Ideal.span {(p : R)}) (p ^ (n + 1))
        (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hp.out.ne_zero)) ?_
      simpa using h1
    obtain ⟨t', ht'⟩ := cancel_prime hpR hf m key
    rw [map_natCast] at ht'
    refine Ideal.mem_span_pair.2 ⟨A * P + (u * A - u * X * P ^ n * y) * om, t', ?_⟩
    rw [om_succ (R := R) p n hp.out]
    linear_combination hAB - om * ht'

end GlobalTheory.Col
end
end

open GlobalTheory.Col PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.X_mul_mem_span_of_colemanLevels : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime], IsDomain R → Prime (p : R) → IsAdicComplete (Ideal.span {(p : R)}) R → ∀ (h : PowerSeries R) (k c : ℕ), (∀ r, 1 ≤ r → r ≤ k → ∃ y : PowerSeries R, ev R p r h = ev R p r ((p : PowerSeries R) ^ c * y)) → ∀ j, j ≤ k → j ≤ c → X * h ∈ Ideal.span {(p : PowerSeries R) ^ (c - j), (1 + X) ^ (p ^ j) - 1} := by
  atlas_forward_decl GlobalTheory.Col.X_mul_mem_span_of_levels
end

section
noncomputable section

open PowerSeries

namespace GlobalTheory.Col

theorem trace_basis_pow {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (p : ℕ)
    (b : Module.Basis (Fin p) B A) (x : A) (y : B) (hb : ∀ i, b i = x ^ (i : ℕ))
    (hx : x ^ p = algebraMap B A y) (i : Fin p) :
    Algebra.trace B A (b i) = if (i : ℕ) = 0 then (p : B) else 0 := by
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  have hd : ∀ j : Fin p, Algebra.leftMulMatrix b (b i) j j = if (i : ℕ) = 0 then 1 else 0 := by
    intro j
    rw [Algebra.leftMulMatrix_eq_repr_mul, hb i, hb j, ← pow_add]
    by_cases h : (i : ℕ) + j < p
    · rw [← hb ⟨_, h⟩, b.repr_self, Finsupp.single_apply]
      by_cases hi : (i : ℕ) = 0
      · rw [if_pos hi, if_pos (Fin.ext (by simp only [Fin.val_mk]; omega))]
      · rw [if_neg hi, if_neg (fun h' => hi (by have := congrArg Fin.val h'; simp only [Fin.val_mk] at this; omega))]
    · have e : x ^ ((i : ℕ) + j) = y • b ⟨(i : ℕ) + j - p, by omega⟩ := by
        rw [hb, Algebra.smul_def, ← hx, ← pow_add]
        congr 1
        simp only [Fin.val_mk]
        omega
      rw [e, map_smul, b.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero, if_neg]
      · omega
      · simp only [Fin.ext_iff]
        omega
  simp only [Matrix.diag, hd]
  split_ifs <;> simp

theorem trace_eq_p_mul {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (p : ℕ) (hp : 0 < p)
    (b : Module.Basis (Fin p) B A) (x : A) (y : B) (hb : ∀ i, b i = x ^ (i : ℕ))
    (hx : x ^ p = algebraMap B A y) (s : A) :
    Algebra.trace B A s = (p : B) * b.repr s ⟨0, hp⟩ := by
  conv_lhs => rw [← b.sum_repr s]
  rw [map_sum]
  simp only [map_smul, trace_basis_pow p b x y hb hx, smul_eq_mul]
  rw [Finset.sum_eq_single ⟨0, hp⟩]
  · simp [mul_comm]
  · intro j _ hj
    rw [if_neg, mul_zero]
    intro h0
    exact hj (Fin.ext h0)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem norm_one_add_pow_mul {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (p : ℕ) (hp : 0 < p)
    (b : Module.Basis (Fin p) B A) (x : A) (y : B) (hb : ∀ i, b i = x ^ (i : ℕ))
    (hx : x ^ p = algebraMap B A y) (s : A) (k : ℕ) (hk : 1 ≤ k) :
    ∃ t : B, Algebra.norm B (1 + (p : A) ^ k * s) = 1 + (p : B) ^ (k + 1) * t := by
  have e : (p : A) ^ k * s = ((p : B) ^ k) • s := by
    rw [Algebra.smul_def, map_pow, map_natCast]
  rw [e, Algebra.norm_eq_matrix_det b, map_add, map_one, map_smul, Matrix.det_one_add_smul,
    ← Algebra.trace_eq_matrix_trace b, trace_eq_p_mul p hp b x y hb hx]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine ⟨b.repr s ⟨0, hp⟩ + (Matrix.det (1 + (Polynomial.X : Polynomial B) •
    (Algebra.leftMulMatrix b s).map Polynomial.C)).divX.divX.eval (((p : B)) ^ (m + 1)) * (p : B) ^ m, ?_⟩
  ring

theorem normOp_congr_of_basis (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime]
    (b : @Module.Basis (Fin p) (PowerSeries R) (PowerSeries R) _ _
      ((phi (R := R) p hp.out.pos).toRingHom.toAlgebra.toModule))
    (hb : ∀ i, b i = (1 + X : PowerSeries R) ^ (i : ℕ))
    (h₁ h₂ r : PowerSeries R) (k : ℕ) (hk : 1 ≤ k) (hu : IsUnit h₂)
    (he : h₁ = h₂ + (p : PowerSeries R) ^ k * r) :
    ∃ r' : PowerSeries R, normOp p h₁ = normOp p h₂ + (p : PowerSeries R) ^ (k + 1) * r' := by
  letI inst : Algebra (PowerSeries R) (PowerSeries R) := (phi (R := R) p hp.out.pos).toRingHom.toAlgebra
  have hx : (1 + X : PowerSeries R) ^ p = algebraMap (PowerSeries R) (PowerSeries R) (1 + X) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact (phi_one_add_X (R := R) p hp.out.pos).symm
  have hN : ∀ z, normOp p z = Algebra.norm (PowerSeries R) z := fun z => rfl
  obtain ⟨u, rfl⟩ := hu
  have h1 : h₁ = (u : PowerSeries R) * (1 + (p : PowerSeries R) ^ k * ((↑u⁻¹ : PowerSeries R) * r)) := by
    have hui := u.mul_inv
    linear_combination he - ((p : PowerSeries R) ^ k * r) * hui
  obtain ⟨t, ht⟩ := @norm_one_add_pow_mul (PowerSeries R) (PowerSeries R) _ _ inst p hp.out.pos b (1 + X) (1 + X)
    hb hx ((↑u⁻¹ : PowerSeries R) * r) k hk
  refine ⟨normOp p (u : PowerSeries R) * t, ?_⟩
  rw [h1, hN, hN, map_mul, ht]
  ring

end GlobalTheory.Col
end
end

section
section
open GlobalTheory.Col PowerSeries

namespace GlobalTheory.Col

theorem normOp_congr : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ →
    ∀ (h₁ h₂ r : PowerSeries R) (k : ℕ), 1 ≤ k → IsUnit h₂ → h₁ = h₂ + (p : PowerSeries R) ^ k * r →
    ∃ r' : PowerSeries R, normOp p h₁ = normOp p h₂ + (p : PowerSeries R) ^ (k + 1) * r' := by
  intro R _ p hp σ hF h₁ h₂ r k hk hu he
  obtain ⟨b, hb⟩ := exists_basis_one_add_X_pow R p hF.complete
  exact normOp_congr_of_basis R p b hb h₁ h₂ r k hk hu he

end GlobalTheory.Col
end

open GlobalTheory.Col PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normOp_congr_mod_pow_succ : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ → ∀ (h₁ h₂ r : PowerSeries R) (k : ℕ), 1 ≤ k → IsUnit h₂ → h₁ = h₂ + (p : PowerSeries R) ^ k * r → ∃ r' : PowerSeries R, normOp p h₁ = normOp p h₂ + (p : PowerSeries R) ^ (k + 1) * r' := by
  atlas_forward_decl GlobalTheory.Col.normOp_congr
end

section
open GlobalTheory.Col PowerSeries

noncomputable section
namespace GlobalTheory.Col.NormFrob

theorem ringHom_ext_of_poly {R S : Type} [CommRing R] [CommRing S] (f g : PowerSeries R →+* PowerSeries S)
    (hfg : f.comp Polynomial.coeToPowerSeries.ringHom = g.comp Polynomial.coeToPowerSeries.ringHom)
    (hf : X ∣ f X) (hg : X ∣ g X) : f = g := by
  ext1 h
  ext n
  set P : Polynomial R := trunc (n + 1) h
  have hd : X ^ (n + 1) ∣ h - (P : PowerSeries R) := by
    rw [X_pow_dvd_iff]
    intro m hm
    simp [P, Polynomial.coeff_coe, coeff_trunc, hm]
  obtain ⟨q, hq⟩ := hd
  have hh : h = (P : PowerSeries R) + X ^ (n + 1) * q := by rw [← hq]; ring
  have hP : f (P : PowerSeries R) = g (P : PowerSeries R) := by
    have := congrArg (fun F => F P) hfg
    simpa using this
  have key : ∀ F : PowerSeries R →+* PowerSeries S, X ∣ F X → coeff n (F (X ^ (n + 1) * q)) = 0 := by
    intro F hF
    have : X ^ (n + 1) ∣ F (X ^ (n + 1) * q) := by
      rw [map_mul, map_pow]
      exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hF _) _
    exact (X_pow_dvd_iff.1 this) n (Nat.lt_succ_self n)
  rw [hh, map_add, map_add, map_add, map_add, hP, key f hf, key g hg]

end GlobalTheory.Col.NormFrob

namespace GlobalTheory.Col.NormFrob
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

abbrev red : PowerSeries R →+* PowerSeries (R ⧸ Ideal.span {(p : R)}) :=
  PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : R)}))

theorem exists_of_red_eq_zero (D : PowerSeries R) (hD : red p D = 0) :
    ∃ g : PowerSeries R, D = (p : PowerSeries R) * g := by
  have hc : ∀ n, ∃ c : R, coeff n D = (p : R) * c := by
    intro n
    have h1 : coeff n (red p D) = 0 := by rw [hD, map_zero]
    rw [coeff_map, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h1
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, by rw [← hc, mul_comm]⟩
  choose c hc using hc
  refine ⟨PowerSeries.mk c, ?_⟩
  ext n
  rw [hc n, show (p : PowerSeries R) = C (p : R) from (map_natCast C p).symm, coeff_C_mul, coeff_mk]

theorem red_pow_eq (σ : R ≃+* R) (hfl : FrobLift R p σ) (h : PowerSeries R) :
    red p h ^ p = red p (phi (R := R) p hp.out.pos (smap σ h)) := by
  haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := CharP.quotient R p (hfl.prime.not_unit)
  haveI : CharP (PowerSeries (R ⧸ Ideal.span {(p : R)})) p :=
    charP_of_injective_algebraMap (R := R ⧸ Ideal.span {(p : R)}) (PowerSeries.C_injective) p
  have hX1 : ((frobenius (PowerSeries (R ⧸ Ideal.span {(p : R)})) p).comp (red p)) X = X ^ p := by
    simp [frobenius_def]
  have hX2 : ((red p).comp ((phi (R := R) p hp.out.pos).toRingHom.comp (smap σ))) X = X ^ p := by
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, smap, map_X, phi_X, map_sub, map_pow,
      map_add, map_one]
    rw [add_pow_char, one_pow, add_sub_cancel_left]
  suffices H : (frobenius (PowerSeries (R ⧸ Ideal.span {(p : R)})) p).comp (red p) =
      (red p).comp ((phi (R := R) p hp.out.pos).toRingHom.comp (smap σ)) by
    have := congrArg (fun F => F h) H
    simpa [frobenius_def] using this
  apply ringHom_ext_of_poly
  · apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.coe_C, smap, map_C, frobenius_def, ← map_pow]
      have h1 : (phi (R := R) p hp.out.pos) (C (σ a)) = C (σ a) := (phi (R := R) p hp.out.pos).commutes (σ a)
      have h2 : Ideal.Quotient.mk (Ideal.span {(p : R)}) (σ a) = (Ideal.Quotient.mk (Ideal.span {(p : R)}) a) ^ p := by
        rw [← map_pow]; exact Ideal.Quotient.eq.2 (hfl.frob a)
      rw [h1, map_C, h2, map_pow]
    · simp only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
      rw [RingHom.comp_apply] at hX1 hX2
      rw [hX1, RingHom.comp_apply] at *
      rw [hX2]
  · rw [hX1]; exact dvd_pow_self _ hp.out.ne_zero
  · rw [hX2]; exact dvd_pow_self _ hp.out.ne_zero

end GlobalTheory.Col.NormFrob

namespace GlobalTheory.Col.NormFrob
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

theorem normOp_eq_smap_add (σ : R ≃+* R) (hfl : FrobLift R p σ)
    (b : @Module.Basis (Fin p) (PowerSeries R) (PowerSeries R) _ _
      ((phi (R := R) p hp.out.pos).toRingHom.toAlgebra.toModule)) (h : PowerSeries R) :
    ∃ r : PowerSeries R, normOp p h = smap σ h + (p : PowerSeries R) * r := by
  haveI := hfl.dom
  haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := CharP.quotient R p (hfl.prime.not_unit)
  haveI : CharP (PowerSeries (R ⧸ Ideal.span {(p : R)})) p :=
    charP_of_injective_algebraMap (R := R ⧸ Ideal.span {(p : R)}) (PowerSeries.C_injective) p
  haveI : (Ideal.span {(p : R)}).IsPrime := (Ideal.span_singleton_prime hfl.prime.ne_zero).2 hfl.prime
  letI := (phi (R := R) p hp.out.pos).toRingHom.toAlgebra
  letI : Module (PowerSeries R) (PowerSeries R) := Algebra.toModule
  haveI : Module.Free (PowerSeries R) (PowerSeries R) := Module.Free.of_basis b
  have hrank : Module.finrank (PowerSeries R) (PowerSeries R) = p := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hred0 : red p (p : PowerSeries R) = 0 := by
    rw [map_natCast]; exact CharP.cast_eq_zero _ p

  have hcong : ∀ x g : PowerSeries R,
      red p (Algebra.norm (PowerSeries R) (x + (p : PowerSeries R) * g)) = red p (Algebra.norm (PowerSeries R) x) := by
    intro x g
    rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b, RingHom.map_det, RingHom.map_det, map_add,
      map_mul, map_natCast, map_add, map_mul, map_natCast]
    have hz : ((p : ℕ) : Matrix (Fin p) (Fin p) (PowerSeries (R ⧸ Ideal.span {(p : R)}))) = 0 := by
      ext i j
      rw [Matrix.natCast_apply]
      split_ifs <;> simp [CharP.cast_eq_zero]
    rw [hz, zero_mul, add_zero]
  obtain ⟨g, hg⟩ := exists_of_red_eq_zero p (h ^ p - phi (R := R) p hp.out.pos (smap σ h)) (by
    rw [map_sub, map_pow, red_pow_eq p σ hfl h, sub_self])
  have hpow : red p (normOp p h) ^ p = red p (smap σ h) ^ p := by
    have e1 : h ^ p = phi (R := R) p hp.out.pos (smap σ h) + (p : PowerSeries R) * g := by rw [← hg]; ring
    have e2 : Algebra.norm (PowerSeries R) (phi (R := R) p hp.out.pos (smap σ h)) = (smap σ h) ^ p := by
      have := Algebra.norm_algebraMap (S := PowerSeries R) (smap σ h)
      rw [hrank] at this; exact this
    unfold normOp
    rw [← map_pow, ← map_pow (Algebra.norm _), e1, hcong, e2, map_pow]
  have hinj := frobenius_inj (PowerSeries (R ⧸ Ideal.span {(p : R)})) p
  have heq : red p (normOp p h) = red p (smap σ h) := hinj (by simpa [frobenius_def] using hpow)
  obtain ⟨r, hr⟩ := exists_of_red_eq_zero p (normOp p h - smap σ h) (by rw [map_sub, heq, sub_self])
  exact ⟨r, by rw [← hr]; ring⟩

end GlobalTheory.Col.NormFrob
end
end

section
section
open GlobalTheory.Col PowerSeries

theorem GlobalTheory.Col.normOp_frob : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ →
    ∀ h : PowerSeries R, ∃ r : PowerSeries R, normOp p h = smap σ h + (p : PowerSeries R) * r := by
  intro R _ p _ σ hfl h
  obtain ⟨b, -⟩ := GlobalTheory.Col.exists_basis_one_add_X_pow R p hfl.complete
  exact GlobalTheory.Col.NormFrob.normOp_eq_smap_add p σ hfl b h
end

open GlobalTheory.Col PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normOp_eq_smap_add_mul : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ → ∀ h : PowerSeries R, ∃ r : PowerSeries R, normOp p h = smap σ h + (p : PowerSeries R) * r := by
  atlas_forward_decl GlobalTheory.Col.normOp_frob
end

section
section
open GlobalTheory.Col PowerSeries

noncomputable section

namespace GlobalTheory.Col.NormCoeff

variable {R : Type} [CommRing R]

def smapEquiv (σ : R ≃+* R) : PowerSeries R ≃+* PowerSeries R :=
  RingEquiv.ofRingHom (smap σ) (smap σ.symm)
    (by ext h n; simp [PowerSeries.coeff_map])
    (by ext h n; simp [PowerSeries.coeff_map])

theorem smapEquiv_apply (σ : R ≃+* R) (h : PowerSeries R) : smapEquiv σ h = smap σ h := rfl

theorem map_phi (p : ℕ) (hp : 0 < p) (f : R →+* R) (h : PowerSeries R) :
    PowerSeries.map f (phi (R := R) p hp h) = phi (R := R) p hp (PowerSeries.map f h) := by
  unfold phi
  rw [PowerSeries.coe_substAlgHom]
  have key := PowerSeries.map_subst (hasSubst_om (R := R) p hp) (h := f) h
  have e : (MvPowerSeries.map f) (((1 + PowerSeries.X : PowerSeries R) ^ p) - 1)
      = ((1 + PowerSeries.X : PowerSeries R) ^ p) - 1 := by
    change PowerSeries.map f _ = _
    simp
  rw [e] at key
  exact key

theorem normOp_smap (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R) (h : PowerSeries R) :
    normOp p (smap σ h) = smap σ (normOp p h) := by
  have key := @Algebra.norm_eq_of_equiv_equiv (PowerSeries R) (PowerSeries R) (PowerSeries R) (PowerSeries R)
    _ _ _ _ (phi (R := R) p hp.out.pos).toRingHom.toAlgebra (phi (R := R) p hp.out.pos).toRingHom.toAlgebra
    (smapEquiv σ) (smapEquiv σ) (by
      ext1 x
      exact (map_phi p hp.out.pos (σ : R →+* R) x).symm) h
  have key2 : normOp p h = (smapEquiv σ).symm (normOp p (smap σ h)) := key
  rw [key2, ← smapEquiv_apply, ← smapEquiv_apply, RingEquiv.apply_symm_apply]

end GlobalTheory.Col.NormCoeff
end
end

open GlobalTheory.Col PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.colemanNormOperator_powerSeriesCoeffAutMap_comm : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R) (h : PowerSeries R), normOp p (smap σ h) = smap σ (normOp p h) := by
  atlas_forward_decl GlobalTheory.Col.NormCoeff.normOp_smap
end

section
section
open GlobalTheory.Col PowerSeries

namespace GlobalTheory

theorem normOp_isUnit {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime] {h : PowerSeries R} (hu : IsUnit h) :
    IsUnit (normOp p h) := by
  unfold normOp
  exact hu.map _

theorem normOp_iterate_isUnit {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime] {h : PowerSeries R} (hu : IsUnit h)
    (j : ℕ) : IsUnit ((normOp p)^[j] h) := by
  induction j with
  | zero => simpa using hu
  | succ j ih => rw [Function.iterate_succ_apply']; exact normOp_isUnit p ih

theorem normOp_iterate_congr : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ →
    ∀ (h : PowerSeries R), IsUnit h → ∀ j : ℕ, ∃ r : PowerSeries R,
      (normOp p)^[j + 1] h = smap σ ((normOp p)^[j] h) + (p : PowerSeries R) ^ (j + 1) * r := by
  intro R _ p hp σ hσ h hu j
  induction j with
  | zero =>
    obtain ⟨r, hr⟩ := GlobalTheory.T.normOp_eq_smap_add_mul R p σ hσ h
    exact ⟨r, by simpa using hr⟩
  | succ j ih =>
    obtain ⟨r, hr⟩ := ih
    have hu2 : IsUnit (smap σ ((normOp p)^[j] h)) := (normOp_iterate_isUnit p hu j).map _
    obtain ⟨r', hr'⟩ := GlobalTheory.T.normOp_congr_mod_pow_succ R p σ hσ _ _ r (j + 1) (by omega) hu2 hr
    refine ⟨r', ?_⟩
    rw [Function.iterate_succ_apply' (normOp p) (j + 1), hr', GlobalTheory.T.colemanNormOperator_powerSeriesCoeffAutMap_comm R p σ, ← Function.iterate_succ_apply' (normOp p) j]

end GlobalTheory
end

open GlobalTheory.Col PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.colemanNormOperator_iterate_succ_congr_frobenius : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ → ∀ (h : PowerSeries R), IsUnit h → ∀ j : ℕ, ∃ r : PowerSeries R, (normOp p)^[j + 1] h = smap σ ((normOp p)^[j] h) + (p : PowerSeries R) ^ (j + 1) * r := by
  atlas_forward_decl GlobalTheory.normOp_iterate_congr
end

section
section
open GlobalTheory.Col PowerSeries

namespace GlobalTheory.Col

theorem ev_normOp_eq_nrm (R : Type) [CommRing R] (p m : ℕ) [hp : Fact p.Prime] (hm : 1 ≤ m)
    (hR : IsAdicComplete (Ideal.span {(p : R)}) R) (h : PowerSeries R) :
    ev R p m (normOp p h) = nrm p m hm (ev R p (m + 1) h) := by
  obtain ⟨b, hb⟩ := GlobalTheory.Col.exists_basis_one_add_X_pow R p hR
  letI iA : Algebra (PowerSeries R) (PowerSeries R) := (phi (R := R) p hp.out.pos).toRingHom.toAlgebra
  letI iM : Module (PowerSeries R) (PowerSeries R) := @Algebra.toModule _ _ _ _ iA
  letI iS : SMul (PowerSeries R) (PowerSeries R) := iM.toSMul
  have F1 : ∀ x : PowerSeries R, ∑ i, phi (R := R) p hp.out.pos (b.repr x i) * (1 + X) ^ (i : ℕ) = x := by
    intro x
    conv_rhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb i]; rfl
  have F3 : ∀ (d : Fin p → PowerSeries R) (i : Fin p),
      b.repr (∑ j, phi (R := R) p hp.out.pos (d j) * (1 + X) ^ (j : ℕ)) i = d i := by
    intro d i
    have h1 : (∑ j, phi (R := R) p hp.out.pos (d j) * (1 + X) ^ (j : ℕ)) = b.equivFun.symm d := by
      rw [Module.Basis.equivFun_symm_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hb j]; rfl
    rw [h1, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have F2 : ∀ (a x : PowerSeries R) (i : Fin p),
      b.repr (phi (R := R) p hp.out.pos a * x) i = a * b.repr x i := by
    intro a x i
    have : phi (R := R) p hp.out.pos a * x = a • x := rfl
    rw [this, LinearEquiv.map_smul]; rfl

  letI iU : Algebra (lev R p m) (lev R p (m + 1)) := (up (R := R) p m hm).toAlgebra
  have hup : ∀ a : PowerSeries R, up (R := R) p m hm (ev R p m a) = ev R p (m + 1) (phi (R := R) p hp.out.pos a) :=
    fun a => rfl
  have hsm : ∀ (a : PowerSeries R) (y : PowerSeries R),
      ev R p (m + 1) (phi (R := R) p hp.out.pos a * y) = (ev R p m a) • ev R p (m + 1) y := by
    intro a y
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, hup, map_mul]
  let v : Fin p → lev R p (m + 1) := fun i => ev R p (m + 1) ((1 + X) ^ (i : ℕ))
  have hli : LinearIndependent (lev R p m) v := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    choose d hd using fun i => Ideal.Quotient.mk_surjective (g i)
    have hx : ev R p (m + 1) (∑ j, phi (R := R) p hp.out.pos (d j) * (1 + X) ^ (j : ℕ)) = 0 := by
      rw [← hg, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hsm, ← hd j]
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hx)
    rw [← phi_cyc (R := R) p m hm, mul_comm] at ha
    have := F3 d i
    rw [← ha, F2] at this
    rw [← hd i, ← this, map_mul]
    have h0 : ev R p m (cyc R p m) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    rw [h0, zero_mul]
  have hsp : ⊤ ≤ Submodule.span (lev R p m) (Set.range v) := by
    intro z _
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    show ev R p (m + 1) y ∈ _
    rw [← F1 y, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hsm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' : Module.Basis (Fin p) (lev R p m) (lev R p (m + 1)) := Module.Basis.mk hli hsp
  have G : ∀ (y : PowerSeries R) (i : Fin p), b'.repr (ev R p (m + 1) y) i = ev R p m (b.repr y i) := by
    intro y i
    have e1 : ev R p (m + 1) y = b'.equivFun.symm (fun i => ev R p m (b.repr y i)) := by
      rw [Module.Basis.equivFun_symm_apply]
      conv_lhs => rw [← F1 y]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Module.Basis.mk_apply, hsm]
    rw [e1, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  unfold nrm normOp
  rw [Algebra.norm_eq_matrix_det b', Algebra.norm_eq_matrix_det b, RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.mk_apply, ← map_mul, G, hb]

end GlobalTheory.Col
end

open GlobalTheory.Col PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ev_normOp_eq_nrm_ev_succ : ∀ (R : Type) [CommRing R] (p m : ℕ) [hp : Fact p.Prime] (hm : 1 ≤ m), IsAdicComplete (Ideal.span {(p : R)}) R → ∀ h : PowerSeries R, ev R p m (normOp p h) = nrm p m hm (ev R p (m + 1) h) := by
  atlas_forward_decl GlobalTheory.Col.ev_normOp_eq_nrm
end

section
section
noncomputable section
open PowerSeries

namespace GlobalTheory.Col

variable {R : Type} [CommRing R]

theorem cyc_eq_coe_taylor (p m : ℕ) :
    cyc R p m = ((Polynomial.taylor 1 (Polynomial.cyclotomic (p ^ m) R) : Polynomial R) : PowerSeries R) := by
  unfold cyc
  rw [Polynomial.taylor_apply, Polynomial.comp, ← Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.hom_eval₂]
  have h1 : (Polynomial.coeToPowerSeries.ringHom : Polynomial R →+* PowerSeries R).comp Polynomial.C = PowerSeries.C := by
    ext a; simp
  have h2 : (Polynomial.coeToPowerSeries.ringHom : Polynomial R →+* PowerSeries R) (Polynomial.X + Polynomial.C 1) = 1 + PowerSeries.X := by
    simp [add_comm]
  rw [h1, h2]

theorem taylor_cyclotomic_dist (p m : ℕ) [hp : Fact p.Prime] :
    (Polynomial.taylor 1 (Polynomial.cyclotomic (p ^ m) R)).IsDistinguishedAt (Ideal.span {(p : R)}) := by
  have hmap : Polynomial.taylor 1 (Polynomial.cyclotomic (p ^ m) R)
      = (Polynomial.taylor 1 (Polynomial.cyclotomic (p ^ m) ℤ)).map (Int.castRingHom R) := by
    rw [Polynomial.taylor_apply, Polynomial.taylor_apply, Polynomial.map_comp, Polynomial.map_cyclotomic]
    simp
  have hW : (Polynomial.taylor 1 (Polynomial.cyclotomic (p ^ m) ℤ)).IsWeaklyEisensteinAt (Ideal.span {(p : ℤ)}) := by
    rcases m with _ | n
    · refine ⟨fun {k} hk => ?_⟩
      simp only [pow_zero, Polynomial.cyclotomic_one, Polynomial.taylor_apply, Polynomial.sub_comp, Polynomial.X_comp,
        Polynomial.one_comp] at hk ⊢
      have : (Polynomial.X + Polynomial.C (1 : ℤ) - 1) = Polynomial.X := by simp
      rw [this] at hk ⊢
      simp at hk
      subst hk
      simp
    · exact (cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p n).isWeaklyEisensteinAt
  have hW' := hW.map (Int.castRingHom R)
  rw [Ideal.map_span, Set.image_singleton, map_natCast, ← hmap] at hW'
  refine { toIsWeaklyEisensteinAt := hW', monic := ?_ }
  rw [Polynomial.taylor_apply]
  exact (Polynomial.cyclotomic.monic _ R).comp_X_add_C 1

def levEquiv (p m : ℕ) [hp : Fact p.Prime] [IsAdicComplete (Ideal.span {(p : R)}) R] :
    AdjoinRoot (Polynomial.cyclotomic (p ^ m) R) ≃ₐ[R] lev R p m :=
  (Ideal.quotientEquivAlg (Ideal.span {Polynomial.cyclotomic (p ^ m) R})
      (Ideal.span {Polynomial.taylor 1 (Polynomial.cyclotomic (p ^ m) R)}) (Polynomial.taylorEquiv (1 : R))
      (by rw [Ideal.map_span, Set.image_singleton]; rfl)).trans
    ((taylor_cyclotomic_dist (R := R) p m).algEquivQuotient.trans
      (Ideal.quotientEquivAlgOfEq R (by rw [cyc_eq_coe_taylor])))

theorem levEquiv_root (p m : ℕ) [hp : Fact p.Prime] [IsAdicComplete (Ideal.span {(p : R)}) R] :
    levEquiv p m (AdjoinRoot.root (Polynomial.cyclotomic (p ^ m) R)) = ev R p m (1 + X) := by
  change levEquiv p m (Ideal.Quotient.mk _ Polynomial.X) = _
  have h1 : Ideal.quotientEquivAlg (Ideal.span {Polynomial.cyclotomic (p ^ m) R})
      (Ideal.span {Polynomial.taylor 1 (Polynomial.cyclotomic (p ^ m) R)}) (Polynomial.taylorEquiv (1 : R))
      (by rw [Ideal.map_span, Set.image_singleton]; rfl) (Ideal.Quotient.mk _ Polynomial.X)
      = Ideal.Quotient.mk _ (Polynomial.X + Polynomial.C 1) := by
    rw [Ideal.quotientEquivAlg_mk]
    congr 1
    exact Polynomial.taylor_X 1
  have h : levEquiv p m (Ideal.Quotient.mk (Ideal.span {Polynomial.cyclotomic (p ^ m) R}) Polynomial.X)
      = (Ideal.quotientEquivAlgOfEq R (by rw [cyc_eq_coe_taylor]))
          ((taylor_cyclotomic_dist (R := R) p m).algEquivQuotient
            (Ideal.quotientEquivAlg (Ideal.span {Polynomial.cyclotomic (p ^ m) R})
      (Ideal.span {Polynomial.taylor 1 (Polynomial.cyclotomic (p ^ m) R)}) (Polynomial.taylorEquiv (1 : R))
      (by rw [Ideal.map_span, Set.image_singleton]; rfl) (Ideal.Quotient.mk _ Polynomial.X))) := rfl
  rw [h, h1, Polynomial.IsDistinguishedAt.algEquivQuotient_apply]
  simp only [Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk, Ideal.quotientEquivAlgOfEq_mk]
  simp [add_comm]

theorem lev_basis : ∀ (R : Type) [CommRing R] (p m : ℕ) [hp : Fact p.Prime], IsAdicComplete (Ideal.span {(p : R)}) R →
    ∃ b : Module.Basis (Fin (Nat.totient (p ^ m))) R (lev R p m), ∀ i, b i = ev R p m ((1 + X) ^ (i : ℕ)) := by
  intro R _ p m hp hc
  rcases subsingleton_or_nontrivial R with hs | hs
  · haveI : Subsingleton (lev R p m) := Module.subsingleton R _
    exact ⟨Module.Basis.ofRepr (LinearEquiv.ofSubsingleton _ _), fun i => Subsingleton.elim _ _⟩
  let pb := AdjoinRoot.powerBasis' (Polynomial.cyclotomic.monic (p ^ m) R)
  have hd : pb.dim = Nat.totient (p ^ m) := by
    simp [pb, Polynomial.natDegree_cyclotomic]
  refine ⟨(pb.basis.map (levEquiv p m).toLinearEquiv).reindex (finCongr hd), fun i => ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.map_apply, PowerBasis.coe_basis]
  simp [pb, levEquiv_root]

end GlobalTheory.Col
end
end

open GlobalTheory.Col PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_colemanLevelRing_basis_one_add_X_pow : ∀ (R : Type) [CommRing R] (p m : ℕ) [hp : Fact p.Prime], IsAdicComplete (Ideal.span {(p : R)}) R → ∃ b : Module.Basis (Fin (Nat.totient (p ^ m))) R (lev R p m), ∀ i, b i = ev R p m ((1 + X) ^ (i : ℕ)) := by
  atlas_forward_decl GlobalTheory.Col.lev_basis
end

section
open GlobalTheory.Col PowerSeries

namespace GlobalTheory.ColEx

theorem iter_cong : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ → ∀ h : PowerSeries R, IsUnit h → ∀ j i : ℕ, ∃ r : PowerSeries R, (normOp p)^[j + i] h = (smap σ)^[i] ((normOp p)^[j] h) + (p : PowerSeries R) ^ (j + 1) * r := by
  intro R _ p _ σ hF h hh j i
  induction i with
  | zero => exact ⟨0, by simp⟩
  | succ i ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨r', hr'⟩ := GlobalTheory.T.colemanNormOperator_iterate_succ_congr_frobenius R p σ hF h hh (j + i)
    refine ⟨smap σ r + (p : PowerSeries R) ^ i * r', ?_⟩
    rw [show j + (i + 1) = (j + i) + 1 by omega, hr', hr, Function.iterate_succ_apply' (smap σ), map_add, map_mul, map_pow, map_natCast]
    ring

theorem norm_tower : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime], IsAdicComplete (Ideal.span {(p : R)}) R → ∀ u : ∀ m : ℕ, (lev R p (m + 1))ˣ, (∀ m : ℕ, nrm p (m + 1) (by omega) ((u (m + 1) : lev R p (m + 2))) = (u m : lev R p (m + 1))) → ∀ (m i : ℕ) (h : PowerSeries R), ev R p (m + i + 1) h = (u (m + i) : lev R p (m + i + 1)) → ev R p (m + 1) ((normOp p)^[i] h) = u m := by
  intro R _ p _ hR u hu m i
  induction i with
  | zero => intro h hh; exact hh
  | succ i ih =>
    intro h hh
    rw [Function.iterate_succ_apply]
    apply ih
    rw [GlobalTheory.T.ev_normOp_eq_nrm_ev_succ R p (m + i + 1) (by omega) hR h, ← hu (m + i)]
    congr 1

theorem ev_map_congr : ∀ (R : Type) [CommRing R] (p m : ℕ) (τ : R →+* R) (g g' : PowerSeries R), ev R p m g = ev R p m g' → ev R p m (PowerSeries.map τ g) = ev R p m (PowerSeries.map τ g') := by
  intro R _ p m τ g g' hg
  have hc : PowerSeries.map τ (cyc R p m) = cyc R p m := by
    unfold cyc
    rw [Polynomial.hom_eval₂]
    have h1 : (PowerSeries.map τ).comp (PowerSeries.C (R := R)) = (PowerSeries.C (R := R)).comp τ := by
      ext a : 1; simp
    rw [h1, map_add, map_one, PowerSeries.map_X, ← Polynomial.eval₂_map, Polynomial.map_cyclotomic]
  rw [Ideal.Quotient.eq] at hg ⊢
  rw [← map_sub]
  obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.1 hg
  rw [← hc', map_mul, hc]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

end GlobalTheory.ColEx

namespace GlobalTheory.ColEx

theorem unit_of_ev : ∀ (R : Type) [CommRing R] (p n : ℕ) [Fact p.Prime], IsAdicComplete (Ideal.span {(p : R)}) R → ∀ g : PowerSeries R, IsUnit (ev R p n g) → IsUnit g := by
  intro R _ p n hp hR g hg
  haveI := hR
  obtain ⟨w, hw⟩ := hg.exists_right_inv
  obtain ⟨g', rfl⟩ := Ideal.Quotient.mk_surjective w
  rw [← map_mul, ← map_one (ev R p n), Ideal.Quotient.eq] at hw
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hw
  have hcyc : constantCoeff (cyc R p n) ∈ Ideal.span {(p : R)} := by
    have e : constantCoeff (cyc R p n) = (Polynomial.cyclotomic (p ^ n) R).eval 1 := by
      unfold cyc
      rw [Polynomial.hom_eval₂]
      have h1 : (constantCoeff (R := R)).comp (PowerSeries.C (R := R)) = RingHom.id R := by ext a; simp
      rw [h1, map_add, map_one, constantCoeff_X, add_zero]
      rfl
    rw [e]
    rcases n with _ | n
    · simp
    · rw [Polynomial.eval_one_cyclotomic_prime_pow]; exact Ideal.subset_span rfl
  have hj : constantCoeff g * constantCoeff g' - 1 ∈ Ideal.jacobson (⊥ : Ideal R) := by
    have := congrArg (constantCoeff (R := R)) hc
    rw [map_mul, map_sub, map_mul, map_one] at this
    rw [← this]
    exact IsAdicComplete.le_jacobson_bot _ (Ideal.mul_mem_left _ _ hcyc)
  have hu : IsUnit (constantCoeff g * constantCoeff g') := by
    have := (Ideal.mem_jacobson_bot.1 hj) 1
    simpa using this
  exact PowerSeries.isUnit_iff_constantCoeff.2 (isUnit_of_mul_isUnit_left hu)

theorem one_add_X_pow_sub_one_mem : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] (j : ℕ), (1 + X : PowerSeries R) ^ (p ^ j) - 1 ∈ ((Ideal.span {(p : R)}).comap (constantCoeff (R := R))) ^ (j + 1) := by
  intro R _ p hp j
  have hpJ : (p : PowerSeries R) ∈ (Ideal.span {(p : R)}).comap (constantCoeff (R := R)) := by
    rw [Ideal.mem_comap, map_natCast]; exact Ideal.subset_span rfl
  have hXJ : (X : PowerSeries R) ∈ (Ideal.span {(p : R)}).comap (constantCoeff (R := R)) := by
    rw [Ideal.mem_comap, constantCoeff_X]; exact Ideal.zero_mem _
  induction j with
  | zero => simpa using hXJ
  | succ j ih =>
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out ((1 + X : PowerSeries R) ^ (p ^ j) - 1) 1
    have e : (1 + X : PowerSeries R) ^ (p ^ (j + 1)) - 1 = ((1 + X : PowerSeries R) ^ (p ^ j) - 1) ^ p
        + (p : PowerSeries R) * ((1 + X : PowerSeries R) ^ (p ^ j) - 1) * 1 * r := by
      rw [sub_add_cancel, one_pow, ← pow_mul, ← pow_succ] at hr
      rw [hr]; ring
    rw [e]
    refine Ideal.add_mem _ ?_ ?_
    · have := Ideal.pow_mem_pow ih p
      rw [← pow_mul] at this
      exact Ideal.pow_le_pow_right (by nlinarith [hp.out.two_le]) this
    · rw [mul_one, pow_succ']
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hpJ ih)

theorem ev_of_mem_pow : ∀ (R : Type) [CommRing R] (p m N : ℕ) [Fact p.Prime] (g : PowerSeries R), g ∈ ((Ideal.span {(p : R)}).comap (constantCoeff (R := R))) ^ (p ^ m * N) → ∃ y : PowerSeries R, ev R p m g = ev R p m ((p : PowerSeries R) ^ N * y) := by
  intro R _ p m N hp g hg
  have hXp : ev R p m X ^ (p ^ m) ∈ Ideal.span {(p : lev R p m)} := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp.out (X : PowerSeries R) 1 m
    obtain ⟨s, hs⟩ := cyc_dvd_level (R := R) p m
    have h0 : ev R p m ((1 + X : PowerSeries R) ^ (p ^ m) - 1) = 0 := by
      rw [hs, map_mul, ev_cyc_self, zero_mul]
    rw [add_comm (1 : PowerSeries R) X, hr] at h0
    simp only [map_sub, map_add, map_mul, map_pow, map_one, one_pow, map_natCast] at h0
    rw [Ideal.mem_span_singleton']
    exact ⟨-(ev R p m X * ev R p m r), by linear_combination -h0⟩
  have hJP : ((Ideal.span {(p : R)}).comap (constantCoeff (R := R))) ^ (p ^ m)
      ≤ Ideal.comap (ev R p m) (Ideal.span {(p : lev R p m)}) := by
    intro g hg
    rw [GlobalTheory.ChartRing.mem_pow_comap_constantCoeff_iff] at hg
    rw [g.eq_X_pow_mul_shift_add_trunc (p ^ m)]
    refine Ideal.add_mem _ ?_ ?_
    · rw [Ideal.mem_comap, map_mul, map_pow]; exact Ideal.mul_mem_right _ _ hXp
    · rw [trunc_apply, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
      refine Ideal.sum_mem _ fun i hi => ?_
      have hi' : i < p ^ m := (Finset.mem_Ico.1 hi).2
      rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_monomial, monomial_eq_C_mul_X_pow]
      have hc : coeff i g ∈ Ideal.span {(p : R)} := Ideal.pow_le_self (by omega) (hg i)
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hc
      have e : (C (coeff i g) * X ^ i : PowerSeries R) = (p : PowerSeries R) * (C d * X ^ i) := by
        rw [← hd, map_mul, map_natCast]; ring
      rw [e, Ideal.mem_comap, map_mul, map_natCast]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have h2 : g ∈ (Ideal.comap (ev R p m) (Ideal.span {(p : lev R p m)})) ^ N := by
    rw [pow_mul] at hg
    exact Ideal.pow_right_mono hJP N hg
  have h3 := Ideal.le_comap_pow (f := ev R p m) (K := Ideal.span {(p : lev R p m)}) N h2
  rw [Ideal.mem_comap, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h3
  obtain ⟨z, hz⟩ := h3
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨y, by rw [← hz, map_mul, map_pow, map_natCast, mul_comm]⟩

theorem lev_sep : ∀ (R : Type) [CommRing R] (p m : ℕ) [Fact p.Prime], IsAdicComplete (Ideal.span {(p : R)}) R → ∀ x : lev R p m, (∀ N : ℕ, ∃ y : PowerSeries R, x = ev R p m ((p : PowerSeries R) ^ N * y)) → x = 0 := by
  intro R _ p m _ hR x hx
  haveI := hR
  obtain ⟨b, -⟩ := GlobalTheory.T.exists_colemanLevelRing_basis_one_add_X_pow R p m hR
  apply b.repr.injective
  rw [map_zero]
  ext i
  rw [Finsupp.coe_zero, Pi.zero_apply]
  apply IsHausdorff.haus' (I := Ideal.span {(p : R)}) (b.repr x i)
  intro N
  obtain ⟨y, hy⟩ := hx N
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have e : x = ((p : R) ^ N) • ev R p m y := by
    rw [hy, Algebra.smul_def, map_mul, map_pow, map_pow, map_natCast, map_natCast]
  rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact dvd_mul_right _ _

end GlobalTheory.ColEx

namespace GlobalTheory.Col

theorem exists_coleman_series : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ → ∀ u : ∀ m : ℕ, (lev R p (m + 1))ˣ, (∀ m : ℕ, nrm p (m + 1) (by omega) ((u (m + 1) : lev R p (m + 2))) = (u m : lev R p (m + 1))) → ∃ f : (PowerSeries R)ˣ, ∀ m : ℕ, ev R p (m + 1) (PowerSeries.map (((σ.symm : R ≃+* R) : R →+* R) ^ (m + 1)) (f : PowerSeries R)) = u m := by
  intro R _ p hp σ hF u hu
  have hR := hF.complete
  haveI : IsAdicComplete (Ideal.span {(p : R)}) R := hF.complete
  haveI : IsAdicComplete ((Ideal.span {(p : R)}).comap (constantCoeff (R := R))) (PowerSeries R) :=
    GlobalTheory.ChartRing.isAdicComplete_comap_constantCoeff _
  set J : Ideal (PowerSeries R) := (Ideal.span {(p : R)}).comap (constantCoeff (R := R)) with hJ

  have hcoeff : ∀ (k : ℕ) (x : PowerSeries R) (n : ℕ), coeff n ((smap σ)^[k] x) = (⇑σ)^[k] (coeff n x) := by
    intro k
    induction k with
    | zero => intro x n; rfl
    | succ k ih =>
      intro x n
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', coeff_map, ih]
      rfl
  have hτ' : ∀ (m : ℕ) (x : PowerSeries R) (n : ℕ),
      coeff n (PowerSeries.map (((σ.symm : R ≃+* R) : R →+* R) ^ (m + 1)) x) = (⇑σ.symm)^[m + 1] (coeff n x) := by
    intro m x n; rw [coeff_map, RingHom.coe_pow]; rfl
  have hτ : ∀ (m : ℕ) (x : PowerSeries R) (n : ℕ),
      coeff n (PowerSeries.map (((σ : R ≃+* R) : R →+* R) ^ (m + 1)) x) = (⇑σ)^[m + 1] (coeff n x) := by
    intro m x n; rw [coeff_map, RingHom.coe_pow]; rfl
  have hcancel : ∀ (m a : ℕ) (x : PowerSeries R), m + 1 ≤ a →
      PowerSeries.map (((σ.symm : R ≃+* R) : R →+* R) ^ (m + 1)) ((smap σ)^[a] x) = (smap σ)^[a - (m + 1)] x := by
    intro m a x h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    ext n
    rw [hτ', hcoeff, hcoeff, Function.iterate_add_apply (⇑σ) (m + 1) d, Nat.add_sub_cancel_left]
    exact (Function.LeftInverse.iterate (fun c => σ.symm_apply_apply c) (m + 1)) _
  have hinv : ∀ (m : ℕ) (x : PowerSeries R), PowerSeries.map (((σ : R ≃+* R) : R →+* R) ^ (m + 1))
      (PowerSeries.map (((σ.symm : R ≃+* R) : R →+* R) ^ (m + 1)) x) = x := by
    intro m x
    ext n
    rw [hτ, hτ']
    exact (Function.LeftInverse.iterate (fun c => σ.apply_symm_apply c) (m + 1)) _

  have hmapJ : ∀ (τ : R →+* R) (n : ℕ) (g : PowerSeries R), g ∈ J ^ n → PowerSeries.map τ g ∈ J ^ n := by
    intro τ n g hg
    rw [hJ, GlobalTheory.ChartRing.mem_pow_comap_constantCoeff_iff] at hg ⊢
    intro i
    have := hg i
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at this ⊢
    obtain ⟨c, hc⟩ := this
    exact ⟨τ c, by rw [coeff_map, ← hc, map_mul, map_pow, map_natCast]⟩

  have hdivX : ∀ (n : ℕ) (g : PowerSeries R), X * g ∈ J ^ (n + 1) → g ∈ J ^ n := by
    intro n g hg
    rw [hJ, GlobalTheory.ChartRing.mem_pow_comap_constantCoeff_iff] at hg ⊢
    intro i
    have := hg (i + 1)
    rwa [coeff_succ_X_mul, Nat.add_sub_add_right] at this
  have hpJ : (p : PowerSeries R) ∈ J := by
    rw [hJ, Ideal.mem_comap, map_natCast]; exact Ideal.subset_span rfl

  have hlift : ∀ n, ∃ h : PowerSeries R, ev R p (n + 1) h = u n := fun n => Ideal.Quotient.mk_surjective _
  choose H hH using hlift
  have hHu : ∀ n, IsUnit (H n) := fun n =>
    GlobalTheory.ColEx.unit_of_ev R p (n + 1) hR (H n) (by rw [hH]; exact (u n).isUnit)

  set F : ℕ → PowerSeries R := fun k => (smap σ)^[k + 1] ((normOp p)^[k + 1] (H (2 * k + 1))) with hFdef
  have C1 : ∀ k m, m ≤ k → ∃ y : PowerSeries R,
      ev R p (m + 1) (PowerSeries.map (((σ.symm : R ≃+* R) : R →+* R) ^ (m + 1)) (F k))
        = u m + ev R p (m + 1) ((p : PowerSeries R) ^ (k + 1 + 1) * y) := by
    intro k m hmk
    obtain ⟨r, hr⟩ := GlobalTheory.ColEx.iter_cong R p σ hF (H (2 * k + 1)) (hHu _) (k + 1) (k - m)
    have h3 := GlobalTheory.ColEx.norm_tower R p hR u hu m (k + 1 + (k - m)) (H (m + (k + 1 + (k - m)))) (hH _)
    have e : m + (k + 1 + (k - m)) = 2 * k + 1 := by omega
    rw [e, hr, map_add] at h3
    refine ⟨-r, ?_⟩
    rw [hFdef]
    dsimp only
    rw [hcancel m (k + 1) _ (by omega), show k + 1 - (m + 1) = k - m by omega, mul_neg, map_neg, ← h3]
    ring
  have C2 : ∀ k, F (k + 1) - F k ∈ J ^ ((k + 1) / 2) := by
    intro k
    have hsmall : ∀ r, 1 ≤ r → r ≤ k + 1 → ∃ y : PowerSeries R,
        ev R p r (F (k + 1) - F k) = ev R p r ((p : PowerSeries R) ^ (k + 2) * y) := by
      intro r h1 h2
      obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
      obtain ⟨y1, h1'⟩ := C1 (k + 1) m (by omega)
      obtain ⟨y2, h2'⟩ := C1 k m (by omega)
      have hD : ev R p (m + 1) (PowerSeries.map (((σ.symm : R ≃+* R) : R →+* R) ^ (m + 1)) (F (k + 1) - F k))
          = ev R p (m + 1) ((p : PowerSeries R) ^ (k + 2) * ((p : PowerSeries R) * y1 - y2)) := by
        rw [map_sub, map_sub, h1', h2', map_mul, map_mul, map_mul, map_sub, map_mul, map_pow, map_pow]
        ring
      have := GlobalTheory.ColEx.ev_map_congr R p (m + 1) (((σ : R ≃+* R) : R →+* R) ^ (m + 1)) _ _ hD
      rw [hinv, map_mul, map_pow, map_natCast] at this
      exact ⟨_, this⟩
    have hI := GlobalTheory.T.X_mul_mem_span_of_colemanLevels R p hF.dom hF.prime hR (F (k + 1) - F k) (k + 1) (k + 2) hsmall ((k + 1) / 2)
      (by omega) (by omega)
    apply hdivX
    refine (Ideal.span_le.2 ?_) hI
    intro z hz
    rcases hz with rfl | hz
    · exact Ideal.pow_le_pow_right (by omega) (Ideal.pow_mem_pow hpJ _)
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact GlobalTheory.ColEx.one_add_X_pow_sub_one_mem R p ((k + 1) / 2)

  have C3 : ∀ n k, n ≤ k → F (2 * k) - F (2 * n) ∈ J ^ n := by
    intro n k hnk
    induction k, hnk using Nat.le_induction with
    | base => simp
    | succ k hnk ih =>
      have e1 : F (2 * (k + 1)) - F (2 * n) = (F (2 * k + 1 + 1) - F (2 * k + 1)) + (F (2 * k + 1) - F (2 * k))
          + (F (2 * k) - F (2 * n)) := by
        rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]; ring
      rw [e1]
      refine add_mem (add_mem ?_ ?_) ih
      · exact Ideal.pow_le_pow_right (by omega) (C2 (2 * k + 1))
      · exact Ideal.pow_le_pow_right (by omega) (C2 (2 * k))
  obtain ⟨f0, hf0⟩ := IsPrecomplete.prec' (I := J) (fun n => F (2 * n)) (fun {a b} hab => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub]
    exact neg_mem (C3 a b hab))
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf0
  have C5 : ∀ m, ev R p (m + 1) (PowerSeries.map (((σ.symm : R ≃+* R) : R →+* R) ^ (m + 1)) f0) = u m := by
    intro m
    apply sub_eq_zero.1
    apply GlobalTheory.ColEx.lev_sep R p (m + 1) hR
    intro N
    obtain ⟨y1, hy1⟩ := C1 (2 * (p ^ (m + 1) * N + m + N)) m (by omega)
    have hmem : PowerSeries.map (((σ.symm : R ≃+* R) : R →+* R) ^ (m + 1)) (f0 - F (2 * (p ^ (m + 1) * N + m + N)))
        ∈ J ^ (p ^ (m + 1) * N) := by
      apply hmapJ
      have hm0 : f0 - F (2 * (p ^ (m + 1) * N + m + N)) ∈ J ^ (p ^ (m + 1) * N + m + N) := by
        rw [← neg_sub]; exact neg_mem (hf0 _)
      exact Ideal.pow_le_pow_right (by omega) hm0
    obtain ⟨y2, hy2⟩ := GlobalTheory.ColEx.ev_of_mem_pow R p (m + 1) N _ hmem
    set n := p ^ (m + 1) * N + m + N
    have e : (p : PowerSeries R) ^ (2 * n + 1 + 1) = (p : PowerSeries R) ^ N * (p : PowerSeries R) ^ (2 * n + 1 + 1 - N) := by
      rw [← pow_add]; congr 1; omega
    refine ⟨y2 + (p : PowerSeries R) ^ (2 * n + 1 + 1 - N) * y1, ?_⟩
    rw [map_sub, map_sub] at hy2
    rw [mul_add, map_add, ← hy2, ← mul_assoc, ← e]
    linear_combination hy1
  have hu0 : IsUnit (PowerSeries.map (((σ.symm : R ≃+* R) : R →+* R) ^ (0 + 1)) f0) :=
    GlobalTheory.ColEx.unit_of_ev R p (0 + 1) hR _ (by rw [C5 0]; exact (u 0).isUnit)
  have hunit : IsUnit f0 := by
    have := hu0.map (PowerSeries.map (((σ : R ≃+* R) : R →+* R) ^ (0 + 1)))
    rwa [hinv] at this
  exact ⟨hunit.unit, fun m => by rw [IsUnit.unit_spec]; exact C5 m⟩

end GlobalTheory.Col
end
