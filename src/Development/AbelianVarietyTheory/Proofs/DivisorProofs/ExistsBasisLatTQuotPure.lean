import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleGramRelationsBlocksOrthogonal
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateLatticeSpans

section
section
open scoped TensorProduct

namespace GlobalTheory.CmIdealGlue

variable {Λ : Type} [CommRing Λ]

theorem natCast_tmul (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (b : Λ) :
    ((n : ℤ_[ℓ]) ⊗ₜ[ℤ] b) = (1 : ℤ_[ℓ]) ⊗ₜ[ℤ] ((n : Λ) * b) := by
  rw [← nsmul_one, TensorProduct.smul_tmul, nsmul_eq_mul]

theorem natCast_eq (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    ((n : ℤ_[ℓ] ⊗[ℤ] Λ)) = (n : ℤ_[ℓ]) ⊗ₜ[ℤ] (1 : Λ) := by
  rw [← Algebra.TensorProduct.includeLeftRingHom_apply, map_natCast]

theorem exists_decomp (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ) (x : ℤ_[ℓ] ⊗[ℤ] Λ) :
    ∃ a : Λ, ∃ r : ℤ_[ℓ] ⊗[ℤ] Λ, x = (1 : ℤ_[ℓ]) ⊗ₜ[ℤ] a + ((ℓ : ℤ_[ℓ] ⊗[ℤ] Λ) ^ k) * r := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul z b =>
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec k z)
    refine ⟨(PadicInt.appr z k : Λ) * b, w ⊗ₜ[ℤ] b, ?_⟩
    have hz : z = (PadicInt.appr z k : ℤ_[ℓ]) + (ℓ : ℤ_[ℓ]) ^ k * w := by rw [mul_comm, hw]; ring
    conv_lhs => rw [hz]
    have hl : ((ℓ : ℤ_[ℓ] ⊗[ℤ] Λ)) ^ k = ((ℓ : ℤ_[ℓ]) ^ k) ⊗ₜ[ℤ] (1 : Λ) := by
      rw [natCast_eq, Algebra.TensorProduct.tmul_pow, one_pow]
    rw [TensorProduct.add_tmul, natCast_tmul, hl, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy =>
    obtain ⟨a, r, rfl⟩ := hx
    obtain ⟨a', r', rfl⟩ := hy
    exact ⟨a + a', r + r', by rw [TensorProduct.tmul_add]; ring⟩

theorem isUnit_natCast (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (n : ℕ) (hn : ¬ ℓ ∣ n) :
    IsUnit (n : ℤ_[ℓ] ⊗[ℤ] Λ) := by
  have h : IsUnit (n : ℤ_[ℓ]) := PadicInt.isUnit_iff.mpr
    (PadicInt.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd hℓ.out).mpr hn))
  simpa using h.map (Algebra.TensorProduct.includeLeftRingHom : ℤ_[ℓ] →+* ℤ_[ℓ] ⊗[ℤ] Λ)

theorem castRingHom_pow_eq_zero (ℓ k : ℕ) :
    (Int.castRingHom (Λ ⧸ Ideal.span {((ℓ ^ k : ℕ) : Λ)})) ((ℓ ^ k : ℕ) : ℤ) = 0 := by
  rw [eq_intCast, Int.cast_natCast, ← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

noncomputable def padicToQuot (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ) :
    ℤ_[ℓ] →+* Λ ⧸ Ideal.span {((ℓ ^ k : ℕ) : Λ)} :=
  ((Ideal.Quotient.lift (Ideal.span {((ℓ ^ k : ℕ) : ℤ)})
      (Int.castRingHom (Λ ⧸ Ideal.span {((ℓ ^ k : ℕ) : Λ)})) (fun a ha => by
        obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        rw [map_mul, castRingHom_pow_eq_zero, mul_zero])).comp
    (Int.quotientSpanNatEquivZMod (ℓ ^ k)).symm.toRingHom).comp (PadicInt.toZModPow k)

noncomputable def toQuot (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ) :
    ℤ_[ℓ] ⊗[ℤ] Λ →+* Λ ⧸ Ideal.span {((ℓ ^ k : ℕ) : Λ)} :=
  (Algebra.TensorProduct.lift (padicToQuot ℓ k).toIntAlgHom (Ideal.Quotient.mk _).toIntAlgHom
    (fun _ _ => Commute.all _ _)).toRingHom

theorem toQuot_tmul (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ) (a : Λ) :
    toQuot ℓ k ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] a) = Ideal.Quotient.mk _ a := by
  simp [toQuot]

theorem exists_coprime_mul_mem (J : Ideal Λ) (m : ℕ) (hm : 0 < m) (hmJ : (m : Λ) ∈ J) (x : Λ)
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime]
    (hx : (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ) x ∈
      J.map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom) :
    ∃ n : ℕ, 0 < n ∧ ¬ ℓ ∣ n ∧ (n : Λ) * x ∈ J := by
  obtain ⟨k, n, hn, hmn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' ℓ hℓ.out.one_lt.ne'
  refine ⟨n, Nat.pos_of_ne_zero (by rintro rfl; simp at hmn; omega), hn, ?_⟩
  have h1 := Ideal.mem_map_of_mem (toQuot (Λ := Λ) ℓ k) hx
  rw [Ideal.map_map] at h1
  have hcomp : (toQuot (Λ := Λ) ℓ k).comp
      (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom = Ideal.Quotient.mk _ := by
    ext a; simp [toQuot_tmul]
  rw [hcomp] at h1
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
    toQuot_tmul] at h1
  obtain ⟨j, hj, hjx⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h1
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp hjx.symm)
  have : (n : Λ) * x = n * j + t * m := by
    rw [hmn, Nat.cast_mul]
    have : x = j + t * ((ℓ ^ k : ℕ) : Λ) := by rw [ht]; ring
    rw [this]; ring
  rw [this]
  exact J.add_mem (J.mul_mem_left _ hj) (J.mul_mem_left _ hmJ)

theorem mem_of_forall_map (J : Ideal Λ) (m : ℕ) (hm : 0 < m) (hmJ : (m : Λ) ∈ J) (x : Λ)
    (hx : ∀ (ℓ : ℕ) [Fact ℓ.Prime], (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ) x ∈
      J.map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom) :
    x ∈ J := by
  classical
  have hex : ∃ g : ℕ, 0 < g ∧ (g : Λ) * x ∈ J := ⟨m, hm, J.mul_mem_right _ hmJ⟩
  set g := Nat.find hex with hg
  obtain ⟨hg0, hgJ⟩ := Nat.find_spec hex

  have hdvd : ∀ n : ℕ, 0 < n → (n : Λ) * x ∈ J → g ∣ n := by
    intro n hn hnJ
    have hgcd0 : 0 < Nat.gcd g n := Nat.gcd_pos_of_pos_left _ hg0
    have hgcdJ : ((Nat.gcd g n : ℕ) : Λ) * x ∈ J := by
      have e := Nat.gcd_eq_gcd_ab g n
      have e' : ((Nat.gcd g n : ℕ) : Λ) = (g : Λ) * ((Nat.gcdA g n : ℤ) : Λ) + (n : Λ) * ((Nat.gcdB g n : ℤ) : Λ) := by
        have := congrArg (fun z : ℤ => (z : Λ)) e
        push_cast at this
        exact this
      rw [e', add_mul]
      refine J.add_mem ?_ ?_
      · rw [mul_comm (g : Λ), mul_assoc]; exact J.mul_mem_left _ hgJ
      · rw [mul_comm (n : Λ), mul_assoc]; exact J.mul_mem_left _ hnJ
    have hle : g ≤ Nat.gcd g n := Nat.find_min' hex ⟨hgcd0, hgcdJ⟩
    have hge : Nat.gcd g n ≤ g := Nat.le_of_dvd hg0 (Nat.gcd_dvd_left g n)
    have : Nat.gcd g n = g := le_antisymm hge hle
    rw [← this]; exact Nat.gcd_dvd_right g n
  have hg1 : g = 1 := by
    by_contra hne
    have hp : (Nat.minFac g).Prime := Nat.minFac_prime hne
    haveI : Fact (Nat.minFac g).Prime := ⟨hp⟩
    obtain ⟨n, hn0, hnd, hnJ⟩ := exists_coprime_mul_mem J m hm hmJ x (Nat.minFac g) (hx _)
    exact hnd ((Nat.minFac_dvd g).trans (hdvd n hn0 hnJ))
  rw [← hg, hg1, Nat.cast_one, one_mul] at hgJ
  exact hgJ

theorem natCast_eq_tmul (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    (n : ℤ_[ℓ] ⊗[ℤ] Λ) = (1 : ℤ_[ℓ]) ⊗ₜ[ℤ] (n : Λ) := by
  rw [← Algebra.TensorProduct.includeRight_apply (R := ℤ) (A := ℤ_[ℓ]), map_natCast]

theorem natCast_mem_span_of_assoc (ℓ : ℕ) [Fact ℓ.Prime] {d e : ℤ_[ℓ] ⊗[ℤ] Λ} {D : Λ} {m : ℕ}
    (hmD : (m : Λ) ∈ Ideal.span {D}) (h : Associated (d * e) ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] D)) :
    (m : ℤ_[ℓ] ⊗[ℤ] Λ) ∈ Ideal.span {d} := by
  rw [Ideal.mem_span_singleton]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hmD
  obtain ⟨u, hu⟩ := h
  refine ⟨e * u * ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] t), ?_⟩
  rw [natCast_eq_tmul, ← ht, ← one_mul (1 : ℤ_[ℓ]), ← Algebra.TensorProduct.tmul_mul_tmul, ← hu]
  ring

noncomputable def glued (δ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℤ_[ℓ] ⊗[ℤ] Λ) : Ideal Λ :=
  ⨅ (ℓ : ℕ) (_ : Fact ℓ.Prime), (Ideal.span {δ ℓ}).comap
    (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom

theorem mem_glued (δ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℤ_[ℓ] ⊗[ℤ] Λ) (x : Λ) :
    x ∈ glued δ ↔ ∀ (ℓ : ℕ) [Fact ℓ.Prime], (1 : ℤ_[ℓ]) ⊗ₜ[ℤ] x ∈ Ideal.span {δ ℓ} := by
  simp [glued, Ideal.mem_iInf]

theorem glue : ∀ (Λ : Type) [CommRing Λ] (c : Λ →+* Λ) (D : Λ) (m : ℕ), 0 < m → (m : Λ) ∈ Ideal.span {D} →
    ∀ (δ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℤ_[ℓ] ⊗[ℤ] Λ),
    (∀ (ℓ : ℕ) [Fact ℓ.Prime], Associated
      (δ ℓ * Algebra.TensorProduct.map (AlgHom.id ℤ_[ℓ] ℤ_[ℓ]) c.toIntAlgHom (δ ℓ)) ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] D)) →
    ∃ 𝔫 : Ideal Λ, 𝔫 * 𝔫.map c = Ideal.span {D} ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      𝔫.map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom = Ideal.span {δ ℓ} := by
  intro Λ _ c D m hm hmD δ hδ
  have hmδ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], (m : ℤ_[ℓ] ⊗[ℤ] Λ) ∈ Ideal.span {δ ℓ} :=
    fun ℓ _ => natCast_mem_span_of_assoc ℓ hmD (hδ ℓ)
  have hmN : (m : Λ) ∈ glued δ := by
    rw [mem_glued]; intro ℓ _
    rw [← natCast_eq_tmul]; exact hmδ ℓ
  have hloc : ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      (glued δ).map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom =
        Ideal.span {δ ℓ} := by
    intro ℓ hℓ
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [mem_glued] at hx
      simpa using hx ℓ
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      obtain ⟨k, n, hn, hmn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' ℓ hℓ.out.one_lt.ne'
      obtain ⟨a, r, hdec⟩ := exists_decomp ℓ k (δ ℓ)
      have hnu : IsUnit (n : ℤ_[ℓ] ⊗[ℤ] Λ) := isUnit_natCast ℓ n hn
      have hna : (n : Λ) * a ∈ glued δ := by
        rw [mem_glued]; intro ℓ' hℓ'
        rw [Ideal.mem_span_singleton]
        have hm' := hmδ ℓ'
        rw [Ideal.mem_span_singleton, hmn, Nat.cast_mul] at hm'
        have e : (1 : ℤ_[ℓ']) ⊗ₜ[ℤ] ((n : Λ) * a) = (n : ℤ_[ℓ'] ⊗[ℤ] Λ) * ((1 : ℤ_[ℓ']) ⊗ₜ[ℤ] a) := by
          rw [natCast_eq_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        rw [e]
        by_cases h : ℓ' = ℓ
        · subst h
          have hk : δ ℓ' ∣ ((ℓ' ^ k : ℕ) : ℤ_[ℓ'] ⊗[ℤ] Λ) := (IsUnit.dvd_mul_right hnu).mp hm'
          have e2 : (1 : ℤ_[ℓ']) ⊗ₜ[ℤ] a = δ ℓ' - ((ℓ' ^ k : ℕ) : ℤ_[ℓ'] ⊗[ℤ] Λ) * r := by
            rw [hdec]; push_cast; ring
          rw [e2]
          exact Dvd.dvd.mul_left (dvd_sub dvd_rfl (hk.mul_right r)) _
        · have hku : IsUnit ((ℓ ^ k : ℕ) : ℤ_[ℓ'] ⊗[ℤ] Λ) := isUnit_natCast ℓ' _ (fun hd =>
            h ((Nat.prime_dvd_prime_iff_eq hℓ'.out hℓ.out).mp (hℓ'.out.dvd_of_dvd_pow hd)))
          have : δ ℓ' ∣ (n : ℤ_[ℓ'] ⊗[ℤ] Λ) := (IsUnit.dvd_mul_left hku).mp hm'
          exact this.mul_right _
      have h1 : (n : ℤ_[ℓ] ⊗[ℤ] Λ) * ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] a) ∈
          (glued δ).map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom := by
        have := Ideal.mem_map_of_mem
          (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom hna
        simpa [natCast_eq_tmul, Algebra.TensorProduct.tmul_mul_tmul] using this
      have h2 : ((ℓ ^ k : ℕ) : ℤ_[ℓ] ⊗[ℤ] Λ) * (n : ℤ_[ℓ] ⊗[ℤ] Λ) ∈
          (glued δ).map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom := by
        have := Ideal.mem_map_of_mem
          (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom hmN
        rw [map_natCast, hmn, Nat.cast_mul] at this
        exact this
      have h1' := (Ideal.unit_mul_mem_iff_mem _ hnu).mp h1
      have h2' := (Ideal.mul_unit_mem_iff_mem _ hnu).mp h2
      rw [hdec]
      push_cast at h2'
      exact Ideal.add_mem _ h1' (Ideal.mul_mem_right _ _ h2')
  refine ⟨glued δ, ?_, hloc⟩
  have hJ1 : ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      (glued δ * (glued δ).map c).map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom =
        Ideal.span {(1 : ℤ_[ℓ]) ⊗ₜ[ℤ] D} := by
    intro ℓ _
    have hc : (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom.comp c =
        (Algebra.TensorProduct.map (AlgHom.id ℤ_[ℓ] ℤ_[ℓ]) c.toIntAlgHom).toRingHom.comp
          (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom := by
      ext a; simp
    rw [Ideal.map_mul, Ideal.map_map, hc, ← Ideal.map_map, hloc ℓ, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_mul_span_singleton]
    obtain ⟨u, hu⟩ := hδ ℓ
    rw [← hu, Ideal.span_singleton_mul_right_unit u.isUnit]
    rfl
  have hJ2 : ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      (Ideal.span {D}).map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom =
        Ideal.span {(1 : ℤ_[ℓ]) ⊗ₜ[ℤ] D} := by
    intro ℓ _
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  apply le_antisymm
  · intro x hx
    apply mem_of_forall_map _ m hm hmD x
    intro ℓ _
    rw [hJ2 ℓ, ← hJ1 ℓ]
    exact Ideal.mem_map_of_mem _ hx
  · intro x hx
    have hmm : (((m * m : ℕ)) : Λ) ∈ glued δ * (glued δ).map c := by
      rw [Nat.cast_mul]
      refine Ideal.mul_mem_mul hmN ?_
      have := Ideal.mem_map_of_mem c hmN
      rwa [map_natCast] at this
    apply mem_of_forall_map _ (m * m) (Nat.mul_pos hm hm) hmm x
    intro ℓ _
    rw [hJ1 ℓ, ← hJ2 ℓ]
    exact Ideal.mem_map_of_mem _ hx

end GlobalTheory.CmIdealGlue
end

open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_norm_equation_from_local_associates : ∀ (Λ : Type) [CommRing Λ] (c : Λ →+* Λ) (D : Λ) (m : ℕ), 0 < m → (m : Λ) ∈ Ideal.span {D} →
    ∀ (δ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℤ_[ℓ] ⊗[ℤ] Λ),
    (∀ (ℓ : ℕ) [Fact ℓ.Prime], Associated
      (δ ℓ * Algebra.TensorProduct.map (AlgHom.id ℤ_[ℓ] ℤ_[ℓ]) c.toIntAlgHom (δ ℓ)) ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] D)) →
    ∃ 𝔫 : Ideal Λ, 𝔫 * 𝔫.map c = Ideal.span {D} ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      𝔫.map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom = Ideal.span {δ ℓ} := by
  atlas_forward_decl GlobalTheory.CmIdealGlue.glue
end

section
section
namespace GlobalTheory.CMNorm

open Matrix

variable {A R Λ : Type} [CommRing A] [CommRing R] [CommRing Λ] [Algebra A R]

theorem span_ind (ι : Λ →+* R) (hspan : Submodule.span A (Set.range ι) = ⊤) {p : R → Prop}
    (h0 : p 0) (hadd : ∀ x y, p x → p y → p (x + y)) (hsmul : ∀ (a : A) x, p x → p (a • x))
    (hι : ∀ a, p (ι a)) (r : R) : p r := by
  let S : Submodule A R :=
    { carrier := {r | p r}
      add_mem' := fun {x y} hx hy => hadd x y hx hy
      zero_mem' := h0
      smul_mem' := fun a x hx => hsmul a x hx }
  have hle : Submodule.span A (Set.range ι) ≤ S :=
    Submodule.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact hι a)
  exact hle (hspan ▸ Submodule.mem_top)

theorem map_smul_of_iota (ι : Λ →+* R) (hspan : Submodule.span A (Set.range ι) = ⊤)
    {X Y : Type} [AddCommGroup X] [Module A X] [Module R X] [IsScalarTower A R X]
    [AddCommGroup Y] [Module A Y] [Module R Y] [IsScalarTower A R Y]
    (F : X →ₗ[A] Y) (hF : ∀ a x, F (ι a • x) = ι a • F x) (r : R) (x : X) :
    F (r • x) = r • F x := by
  refine span_ind ι hspan (p := fun r => F (r • x) = r • F x) (by simp) ?_ ?_ (fun a => hF a x) r
  · intro u v hu hv; simp [add_smul, hu, hv]
  · intro a u hu; simp only [smul_assoc, map_smul, hu]

theorem invol (ι : Λ →+* R) (hspan : Submodule.span A (Set.range ι) = ⊤) (c : Λ →+* Λ)
    (cR : R →ₐ[A] R) (hc : ∀ a, cR (ι a) = ι (c a)) (hcc : ∀ a, c (c a) = a) (r : R) :
    cR (cR r) = r := by
  refine span_ind ι hspan (p := fun r => cR (cR r) = r) (by simp) ?_ ?_ ?_ r
  · intro u v hu hv; simp [hu, hv]
  · intro a u hu; simp [hu]
  · intro a; simp [hc, hcc]

theorem adj (ι : Λ →+* R) (hspan : Submodule.span A (Set.range ι) = ⊤) (c : Λ →+* Λ)
    (cR : R →ₐ[A] R) (hc : ∀ a, cR (ι a) = ι (c a))
    {κ T : Type} [AddCommGroup T] [Module A T] (ρ : Λ →+* Module.End A T)
    (e : LinearMap.BilinForm A T) (hadj : ∀ a x y, e (ρ a x) y = e x (ρ (c a) y))
    (f : (κ → R) ≃ₗ[A] T) (hf : ∀ a r, f (ι a • r) = ρ a (f r)) (r : R) (x y : κ → R) :
    e (f (r • x)) (f y) = e (f x) (f (cR r • y)) := by
  refine span_ind ι hspan (p := fun r => e (f (r • x)) (f y) = e (f x) (f (cR r • y)))
    (by simp) ?_ ?_ ?_ r
  · intro u v hu hv; simp [add_smul, hu, hv]
  · intro a u hu; simp [smul_assoc, hu]
  · intro a; rw [hf, hadj, hc, hf]

theorem unit_vec (x : Unit → R) : x = x () • (1 : Unit → R) := by
  funext u; cases u; simp

def lam {T₁ : Type} [AddCommGroup T₁] [Module A T₁] (e₁ : LinearMap.BilinForm A T₁)
    (f₁ : (Unit → R) ≃ₗ[A] T₁) : R →ₗ[A] A where
  toFun r := e₁ (f₁ (r • (1 : Unit → R))) (f₁ 1)
  map_add' x y := by simp [add_smul]
  map_smul' a x := by simp [smul_assoc]

theorem lam_apply {T₁ : Type} [AddCommGroup T₁] [Module A T₁] (e₁ : LinearMap.BilinForm A T₁)
    (f₁ : (Unit → R) ≃ₗ[A] T₁) (r : R) : lam e₁ f₁ r = e₁ (f₁ (r • (1 : Unit → R))) (f₁ 1) := rfl

end GlobalTheory.CMNorm

namespace GlobalTheory.CMNorm

variable {A R Λ : Type} [CommRing A] [CommRing R] [CommRing Λ] [Algebra A R]

section abelian₂
variable (ι : Λ →+* R) (hspan : Submodule.span A (Set.range ι) = ⊤) (c : Λ →+* Λ)
    (cR : R →ₐ[A] R) (hc : ∀ a, cR (ι a) = ι (c a)) (hcc : ∀ a, c (c a) = a)
    {T₁ : Type} [AddCommGroup T₁] [Module A T₁] (ρ₁ : Λ →+* Module.End A T₁)
    (e₁ : LinearMap.BilinForm A T₁) (he₁ : Function.Bijective e₁)
    (hadj₁ : ∀ a x y, e₁ (ρ₁ a x) y = e₁ x (ρ₁ (c a) y))
    (f₁ : (Unit → R) ≃ₗ[A] T₁) (hf₁ : ∀ a r, f₁ (ι a • r) = ρ₁ a (f₁ r))
include hspan hc hcc hadj₁ hf₁

theorem lam_pair (t s : R) :
    e₁ (f₁ (t • (1 : Unit → R))) (f₁ (s • 1)) = lam e₁ f₁ (cR s * t) := by
  rw [lam_apply, ← smul_smul, adj ι hspan c cR hc ρ₁ e₁ hadj₁ f₁ hf₁ (cR s) (t • 1) 1, invol ι hspan c cR hc hcc]

include he₁ in
theorem lam_inj (t : R) (h : ∀ r, lam e₁ f₁ (r * t) = 0) : t = 0 := by
  have h0 : e₁ (f₁ (t • (1 : Unit → R))) = 0 := by
    ext z
    rw [← f₁.apply_symm_apply z, unit_vec (f₁.symm z), lam_pair ι hspan c cR hc hcc ρ₁ e₁ hadj₁ f₁ hf₁, h]
    simp
  have h1 : f₁ (t • (1 : Unit → R)) = 0 := he₁.1 (by rw [h0, map_zero])
  have h2 : t • (1 : Unit → R) = 0 := by simpa using h1
  simpa using congrFun h2 ()

include he₁ in
theorem lam_onto (g : R →ₗ[A] A) : ∃ t, ∀ r, g r = lam e₁ f₁ (r * t) := by
  obtain ⟨x, hx⟩ := he₁.2 ((g.comp cR.toLinearMap).comp
    ((LinearMap.proj () : (Unit → R) →ₗ[A] R).comp f₁.symm.toLinearMap))
  refine ⟨f₁.symm x (), fun r => ?_⟩
  have hx' : x = f₁ (f₁.symm x () • (1 : Unit → R)) := by
    rw [← unit_vec, f₁.apply_symm_apply]
  have := LinearMap.congr_fun hx (f₁ (cR r • (1 : Unit → R)))
  rw [hx', lam_pair ι hspan c cR hc hcc ρ₁ e₁ hadj₁ f₁ hf₁, invol ι hspan c cR hc hcc] at this
  simpa [invol ι hspan c cR hc hcc] using this.symm

end abelian₂
end GlobalTheory.CMNorm

namespace GlobalTheory.CMNorm

variable {A R Λ : Type} [CommRing A] [CommRing R] [CommRing Λ] [Algebra A R]

theorem exists_gram (cR : R →ₐ[A] R) (hcc : ∀ r, cR (cR r) = r) (l : R →ₗ[A] A)
    (hinj : ∀ t, (∀ r, l (r * t) = 0) → t = 0)
    (honto : ∀ g : R →ₗ[A] A, ∃ t, ∀ r, g r = l (r * t))
    {κ T : Type} [Fintype κ] [DecidableEq κ] [AddCommGroup T] [Module A T]
    (e : LinearMap.BilinForm A T) (he : Function.Surjective e) (f : (κ → R) ≃ₗ[A] T)
    (hadj : ∀ (r : R) x y, e (f (r • x)) (f y) = e (f x) (f (cR r • y))) :
    ∃ H : Matrix κ κ R, IsUnit H.det ∧
      ∀ (r : R) x y, e (f (r • x)) (f y) = l (r * ∑ i, ∑ j, x i * H i j * cR (y j)) := by
  have hex : ∀ i j : κ, ∃ t, ∀ r : R,
      e (f (r • Pi.single i (1 : R))) (f (Pi.single j 1)) = l (r * t) := fun i j =>
    honto
      { toFun := fun r => e (f (r • Pi.single i (1 : R))) (f (Pi.single j 1))
        map_add' := fun x y => by simp [add_smul]
        map_smul' := fun a x => by simp [smul_assoc] }
  choose H hH using hex
  have hvec : ∀ x : κ → R, x = ∑ i, x i • (Pi.single i (1 : R) : κ → R) := by
    intro x; ext j; simp [Finset.sum_apply, Pi.single_apply]
  have hform : ∀ (r : R) x y, e (f (r • x)) (f y) = l (r * ∑ i, ∑ j, x i * H i j * cR (y j)) := by
    intro r x y
    conv_lhs => rw [hvec (r • x), hvec y]
    simp only [map_sum, LinearMap.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← hcc (y j), ← hadj, smul_smul, hH, hcc]
    congr 1
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨Matrix.of H, ?_, hform⟩
  have hX : ∀ k : κ, ∃ x : κ → R, ∀ y, e (f x) (f y) = l (cR (y k)) := by
    intro k
    obtain ⟨z, hz⟩ := he ((l.comp cR.toLinearMap).comp
      ((LinearMap.proj k : (κ → R) →ₗ[A] R).comp f.symm.toLinearMap))
    exact ⟨f.symm z, fun y => by simp [hz]⟩
  choose X hX using hX
  refine Matrix.isUnit_det_of_left_inverse (B := Matrix.of X) ?_
  ext k j
  rw [← sub_eq_zero]
  refine hinj _ fun s => ?_
  have h1 := hform 1 (X k) (Pi.single j (cR s))
  rw [one_smul, hX, one_mul] at h1
  rw [mul_sub, map_sub, sub_eq_zero]
  have h2 : ∑ i, ∑ j', X k i * H i j' * cR ((Pi.single j (cR s) : κ → R) j') =
      s * (Matrix.of X * Matrix.of H) k j := by
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single j]
    · simp [hcc, mul_comm]
    · intro b _ hb; simp [hb]
    · simp
  rw [← h2, ← h1]
  congr 1
  by_cases hkj : k = j
  · subst hkj; simp [hcc]
  · simp [hkj]

end GlobalTheory.CMNorm

namespace GlobalTheory.CMNorm

open Matrix

theorem frame_row {A R Λ : Type} [CommRing A] [CommRing R] [CommRing Λ] [Algebra A R]
    (ι : Λ →+* R) (hspan : Submodule.span A (Set.range ι) = ⊤)
    {κ T₁ T : Type} [AddCommGroup T₁] [Module A T₁] [AddCommGroup T] [Module A T]
    (ρ₁ : Λ →+* Module.End A T₁) (ρ : Λ →+* Module.End A T) (φ : T₁ →ₗ[A] T)
    (hφ : ∀ a x, φ (ρ₁ a x) = ρ a (φ x))
    (f₁ : (Unit → R) ≃ₗ[A] T₁) (f : (κ → R) ≃ₗ[A] T)
    (hf₁ : ∀ a r, f₁ (ι a • r) = ρ₁ a (f₁ r)) (hf : ∀ a r, f (ι a • r) = ρ a (f r))
    (v : κ → R) (hv : f v = φ (f₁ 1)) (r : R) : f (r • v) = φ (f₁ (r • 1)) := by
  have h := map_smul_of_iota ι hspan (f.symm.toLinearMap ∘ₗ φ ∘ₗ f₁.toLinearMap)
    (fun a x => f.injective (by simp [hf, hf₁, hφ])) r 1
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
  rw [← hv, f.symm_apply_apply] at h
  rw [← h, f.apply_symm_apply]

theorem associated_det_mul_conj : ∀ (A R Λ : Type) [CommRing A] [CommRing R] [CommRing Λ] [Algebra A R] (ι : Λ →+* R),
    Submodule.span A (Set.range ι) = ⊤ → ∀ (c : Λ →+* Λ) (cR : R →ₐ[A] R), (∀ a, cR (ι a) = ι (c a)) →
    (∀ a, c (c a) = a) →
    ∀ (T₁ T₂ T : Type) [AddCommGroup T₁] [Module A T₁] [AddCommGroup T₂] [Module A T₂] [AddCommGroup T] [Module A T]
      (ρ₁ : Λ →+* Module.End A T₁) (ρ₂ : Λ →+* Module.End A T₂) (ρ : Λ →+* Module.End A T)
      (e₁ : LinearMap.BilinForm A T₁) (e₂ : LinearMap.BilinForm A T₂) (e : LinearMap.BilinForm A T),
      Function.Bijective e₁ → Function.Bijective e₂ → Function.Bijective e →
      (∀ a x y, e₁ (ρ₁ a x) y = e₁ x (ρ₁ (c a) y)) → (∀ a x y, e₂ (ρ₂ a x) y = e₂ x (ρ₂ (c a) y)) →
      (∀ a x y, e (ρ a x) y = e x (ρ (c a) y)) →
    ∀ (m n : Type) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
      (φ₁ : m → (T₁ →ₗ[A] T)) (φ₂ : n → (T₂ →ₗ[A] T)) (g₁ : Matrix m m Λ) (g₂ : Matrix n n Λ),
      (∀ k a x, φ₁ k (ρ₁ a x) = ρ a (φ₁ k x)) → (∀ k a x, φ₂ k (ρ₂ a x) = ρ a (φ₂ k x)) →
      (∀ k l x y, e (φ₁ k x) (φ₁ l y) = e₁ (ρ₁ (g₁ k l) x) y) →
      (∀ k l x y, e (φ₂ k x) (φ₂ l y) = e₂ (ρ₂ (g₂ k l) x) y) →
      (∀ k l x y, e (φ₁ k x) (φ₂ l y) = 0) → (∀ k l x y, e (φ₂ k x) (φ₁ l y) = 0) →
    ∀ (f₁ : (Unit → R) ≃ₗ[A] T₁) (f₂ : (Unit → R) ≃ₗ[A] T₂) (f : (m ⊕ n → R) ≃ₗ[A] T),
      (∀ a r, f₁ (ι a • r) = ρ₁ a (f₁ r)) → (∀ a r, f₂ (ι a • r) = ρ₂ a (f₂ r)) →
      (∀ a r, f (ι a • r) = ρ a (f r)) →
    ∀ M : Matrix (m ⊕ n) (m ⊕ n) R, (∀ k, f (M (Sum.inl k)) = φ₁ k (f₁ 1)) →
      (∀ k, f (M (Sum.inr k)) = φ₂ k (f₂ 1)) →
      Associated (M.det * cR M.det) (ι (g₁.det * g₂.det)) := by
  intro A R Λ _ _ _ _ ι hspan c cR hc hcc T₁ T₂ T _ _ _ _ _ _ ρ₁ ρ₂ ρ e₁ e₂ e he₁ he₂ he
    ha₁ ha₂ ha m n _ _ _ _ φ₁ φ₂ g₁ g₂ hφ₁ hφ₂ hg₁ hg₂ h12 h21 f₁ f₂ f hf₁ hf₂ hf M hM₁ hM₂
  have hinv := invol ι hspan c cR hc hcc
  have hinj := lam_inj ι hspan c cR hc hcc ρ₁ e₁ he₁ ha₁ f₁ hf₁
  have honto := lam_onto ι hspan c cR hc hcc ρ₁ e₁ he₁ ha₁ f₁ hf₁
  obtain ⟨H, hH, hHf⟩ := exists_gram cR hinv _ hinj honto e he.2 f (adj ι hspan c cR hc ρ e ha f hf)
  obtain ⟨W, hW, hWf⟩ := exists_gram cR hinv _ hinj honto e₂ he₂.2 f₂
    (adj ι hspan c cR hc ρ₂ e₂ ha₂ f₂ hf₂)
  rw [Matrix.det_unique] at hW
  have hr₁ := fun k => frame_row ι hspan ρ₁ ρ (φ₁ k) (hφ₁ k) f₁ f hf₁ hf _ (hM₁ k)
  have hr₂ := fun k => frame_row ι hspan ρ₂ ρ (φ₂ k) (hφ₂ k) f₂ f hf₂ hf _ (hM₂ k)
  have hent : ∀ i j (b : R), (∀ r : R, e (f (r • M i)) (f (M j)) = lam e₁ f₁ (r * b)) →
      (M * H * (M.map cR)ᵀ) i j = b := by
    intro i j b hb
    rw [← sub_eq_zero]
    refine hinj _ fun r => ?_
    rw [mul_sub, map_sub, sub_eq_zero, ← hb, hHf]
    congr 2
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hmat : M * H * (M.map cR)ᵀ =
      Matrix.fromBlocks (g₁.map ι) 0 0 (W default default • g₂.map ι) := by
    ext i j
    refine hent i j _ fun r => ?_
    rcases i with i | i <;> rcases j with j | j
    · rw [hr₁, hM₁, hg₁, ← hf₁, smul_smul, lam_apply]
      simp [mul_comm]
    · rw [hr₁, hM₂, h12]; simp
    · rw [hr₂, hM₁, h21]; simp
    · rw [hr₂, hM₂, hg₂, ← hf₂, smul_smul, hWf]
      congr 1
      simp only [Finset.univ_unique, Finset.sum_singleton, Pi.one_apply, map_one,
        Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      ring
  have hdet := congrArg Matrix.det hmat
  have hc' : (M.map cR).det = cR M.det := (AlgHom.map_det cR M).symm
  have hi₁ : (g₁.map ι).det = ι g₁.det := (RingHom.map_det ι g₁).symm
  have hi₂ : (g₂.map ι).det = ι g₂.det := (RingHom.map_det ι g₂).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_smul, hc', hi₁, hi₂] at hdet
  have hfin : M.det * cR M.det * H.det =
      ι (g₁.det * g₂.det) * W default default ^ Fintype.card n := by
    rw [map_mul]; linear_combination hdet
  refine (associated_mul_unit_right _ _ hH).trans ?_
  rw [hfin]
  exact associated_mul_unit_left _ _ (hW.pow _)

end GlobalTheory.CMNorm
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_linear_tensor_module_decomposition : ∀ (A R Λ : Type) [CommRing A] [CommRing R] [CommRing Λ] [Algebra A R] (ι : Λ →+* R),
    Submodule.span A (Set.range ι) = ⊤ → ∀ (c : Λ →+* Λ) (cR : R →ₐ[A] R), (∀ a, cR (ι a) = ι (c a)) →
    (∀ a, c (c a) = a) →
    ∀ (T₁ T₂ T : Type) [AddCommGroup T₁] [Module A T₁] [AddCommGroup T₂] [Module A T₂] [AddCommGroup T] [Module A T]
      (ρ₁ : Λ →+* Module.End A T₁) (ρ₂ : Λ →+* Module.End A T₂) (ρ : Λ →+* Module.End A T)
      (e₁ : LinearMap.BilinForm A T₁) (e₂ : LinearMap.BilinForm A T₂) (e : LinearMap.BilinForm A T),
      Function.Bijective e₁ → Function.Bijective e₂ → Function.Bijective e →
      (∀ a x y, e₁ (ρ₁ a x) y = e₁ x (ρ₁ (c a) y)) → (∀ a x y, e₂ (ρ₂ a x) y = e₂ x (ρ₂ (c a) y)) →
      (∀ a x y, e (ρ a x) y = e x (ρ (c a) y)) →
    ∀ (m n : Type) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
      (φ₁ : m → (T₁ →ₗ[A] T)) (φ₂ : n → (T₂ →ₗ[A] T)) (g₁ : Matrix m m Λ) (g₂ : Matrix n n Λ),
      (∀ k a x, φ₁ k (ρ₁ a x) = ρ a (φ₁ k x)) → (∀ k a x, φ₂ k (ρ₂ a x) = ρ a (φ₂ k x)) →
      (∀ k l x y, e (φ₁ k x) (φ₁ l y) = e₁ (ρ₁ (g₁ k l) x) y) →
      (∀ k l x y, e (φ₂ k x) (φ₂ l y) = e₂ (ρ₂ (g₂ k l) x) y) →
      (∀ k l x y, e (φ₁ k x) (φ₂ l y) = 0) → (∀ k l x y, e (φ₂ k x) (φ₁ l y) = 0) →
    ∀ (f₁ : (Unit → R) ≃ₗ[A] T₁) (f₂ : (Unit → R) ≃ₗ[A] T₂) (f : (m ⊕ n → R) ≃ₗ[A] T),
      (∀ a r, f₁ (ι a • r) = ρ₁ a (f₁ r)) → (∀ a r, f₂ (ι a • r) = ρ₂ a (f₂ r)) →
      (∀ a r, f (ι a • r) = ρ a (f r)) →
    ∀ M : Matrix (m ⊕ n) (m ⊕ n) R, (∀ k, f (M (Sum.inl k)) = φ₁ k (f₁ 1)) →
      (∀ k, f (M (Sum.inr k)) = φ₂ k (f₂ 1)) →
      Associated (M.det * cR M.det) (ι (g₁.det * g₂.det)) := by
  atlas_forward_decl GlobalTheory.CMNorm.associated_det_mul_conj
end

section
section
open scoped TensorProduct NumberField

namespace GlobalTheory.TorusTateFree

open scoped nonZeroDivisors in

private theorem finrank_int_tower (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M]
    [Module (𝓞 E) M] : Module.finrank ℤ M = Module.finrank ℚ E * Module.finrank (𝓞 E) M := by
  let f : M →ₗ[𝓞 E] E ⊗[𝓞 E] M := TensorProduct.mk (𝓞 E) E M 1
  have hb : IsBaseChange E f := TensorProduct.isBaseChange _ _ _
  haveI h1 : IsLocalizedModule (𝓞 E)⁰ f := (isLocalizedModule_iff_isBaseChange (𝓞 E)⁰ E f).2 hb
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E :=
    IsIntegralClosure.isLocalization ℤ ℚ E (𝓞 E)
  haveI h2 : IsLocalizedModule (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) f :=
    (isLocalizedModule_iff_isBaseChange _ E f).2 hb
  haveI h3 : IsLocalizedModule ℤ⁰ (f.restrictScalars ℤ) := IsLocalizedModule.restrictScalars _ f
  rw [← IsLocalizedModule.finrank_eq ℤ⁰ (f.restrictScalars ℤ) le_rfl,
    ← IsLocalizedModule.finrank_eq (𝓞 E)⁰ f le_rfl,
    ← IsLocalization.finrank_eq ℚ ℤ⁰ le_rfl, ← IsLocalization.finrank_eq E (𝓞 E)⁰ le_rfl,
    Module.finrank_mul_finrank]

private theorem exists_span_mod {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (m : R) [Finite (R ⧸ Ideal.span {m})] :
    ∃ v : Fin (Module.finrank R N) → N, ∀ x : N, ∃ (c : Fin (Module.finrank R N) → R) (z : N),
      x = ∑ k, c k • v k + m • z := by
  set I : Ideal R := Ideal.span {m} with hI
  have : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) (Module.finrank R N)
    (fun P => by
      have := P.isMaximal
      let : Field ((R ⧸ I) ⧸ P.asIdeal) := Ideal.Quotient.field _
      rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal)
        ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]
      have h1 := Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥
      rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
      exact h1)
  have h1 : Submodule.span R (Set.range b) = ⊤ := by
    rw [← Submodule.restrictScalars_span R (R ⧸ I) Ideal.Quotient.mk_surjective, b.span_eq,
      Submodule.restrictScalars_top]
  let q := TensorProduct.quotTensorEquivQuotSMul N I
  choose v hv using fun k => Submodule.Quotient.mk_surjective _ (q (b k))
  refine ⟨v, fun x => ?_⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1
    (h1 ▸ Submodule.mem_top : q.symm (Submodule.Quotient.mk x) ∈ Submodule.span R (Set.range b))
  have h2 : x - ∑ k, c k • v k ∈ (I • ⊤ : Submodule R N) := by
    rw [← Submodule.Quotient.eq, ← q.apply_symm_apply (Submodule.Quotient.mk x), ← hc, map_sum,
      ← Submodule.mkQ_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smul, Submodule.mkQ_apply, hv]
  rw [hI, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h2
  obtain ⟨z, -, hz⟩ := h2
  exact ⟨c, z, by rw [hz]; abel⟩

theorem exists_gens_mod : ∀ (E : Type) [Field E] [NumberField E] (ℓ : ℕ) [Fact ℓ.Prime] (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : 𝓞 E →+* Module.End ℂ W) (L : Submodule ℤ W), (∀ a z, z ∈ L → ρ a z ∈ L) → Module.Finite ℤ L →
    ∀ (κ : Type) [Fintype κ], Module.finrank ℤ L = Fintype.card κ * Module.finrank ℚ E →
    ∃ y : κ → W, (∀ k, y k ∈ L) ∧ ∀ x ∈ L, ∃ (c : κ → 𝓞 E) (z : W), z ∈ L ∧ x = ∑ k, ρ (c k) (y k) + (ℓ : ℂ) • z := by
  intro E _ _ ℓ hℓ W _ _ ρ L hstab hfin κ _ hrk
  letI : Module (𝓞 E) W := Module.compHom W ρ
  have hs : ∀ (a : 𝓞 E) (z : W), a • z = ρ a z := fun _ _ => rfl
  let N : Submodule (𝓞 E) W :=
    { carrier := L
      add_mem' := fun ha hb => L.add_mem ha hb
      zero_mem' := L.zero_mem
      smul_mem' := fun a z hz => hstab a z hz }
  let e : L ≃ₗ[ℤ] N := AddEquiv.toIntLinearEquiv
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have : Module.Finite ℤ N := Module.Finite.equiv e
  have : Module.Finite (𝓞 E) N := Module.Finite.of_restrictScalars_finite ℤ _ _
  have : Module.IsTorsionFree (𝓞 E) W := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun a z h => or_iff_not_imp_left.2 fun ha => ?_
    obtain ⟨b, n, hn, h1⟩ := Algebra.IsAlgebraic.exists_smul_eq_mul ℤ (1 : 𝓞 E) ha
    have h2 : (n : 𝓞 E) = b * a := by rw [mul_comm, ← h1]; simp
    have h3 : (n : ℂ) • z = 0 := by
      rw [Int.cast_smul_eq_zsmul, ← Int.cast_smul_eq_zsmul (𝓞 E), h2, mul_smul, h, smul_zero]
    exact (smul_eq_zero.1 h3).resolve_left (Int.cast_ne_zero.2 hn)
  have : Module.FinitePresentation (𝓞 E) N := Module.finitePresentation_of_finite _ _
  have : Module.Flat (𝓞 E) N := inferInstance
  have : Module.Projective (𝓞 E) N := Module.Flat.projective_of_finitePresentation
  have : Finite (𝓞 E ⧸ Ideal.span {(ℓ : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hℓ.out.ne_zero)
  have hr : Fintype.card κ = Module.finrank (𝓞 E) N := by
    rw [e.finrank_eq, finrank_int_tower E N, mul_comm] at hrk
    exact (Nat.eq_of_mul_eq_mul_right Module.finrank_pos hrk).symm
  let σ : κ ≃ Fin (Module.finrank (𝓞 E) N) := Fintype.equivFinOfCardEq hr
  obtain ⟨v, hv⟩ := exists_span_mod (N := N) (ℓ : 𝓞 E)
  refine ⟨fun k => v (σ k), fun k => (v (σ k)).2, fun x hx => ?_⟩
  obtain ⟨c, z, h⟩ := hv ⟨x, hx⟩
  refine ⟨fun k => c (σ k), z, z.2, ?_⟩
  have h1 := congrArg N.subtype h
  rw [map_add, map_sum, map_smul, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul ℂ,
    ← σ.sum_comp] at h1
  exact h1

theorem exists_tate_gens : ∀ (E : Type) [Field E] [NumberField E] (ℓ : ℕ) [Fact ℓ.Prime] (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : 𝓞 E →+* Module.End ℂ W) (M : Type) [CommGroup M] (ex : W → M), (∀ z w, ex (z + w) = ex z * ex w) →
    Function.Surjective ex → ∀ (L : Submodule ℤ W), (∀ z, ex z = 1 ↔ z ∈ L) →
    ∀ (β : 𝓞 E → (M →* M)), (∀ a z, ex (ρ a z) = β a (ex z)) →
    ∀ (α : 𝓞 E →+* Module.End ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M)), (∀ a t n, (α a t).lev n = β a (t.lev n)) →
    ∀ (κ : Type) [Fintype κ] (y : κ → W), (∀ k, y k ∈ L) →
    (∀ x ∈ L, ∃ (c : κ → 𝓞 E) (z : W), z ∈ L ∧ x = ∑ k, ρ (c k) (y k) + (ℓ : ℂ) • z) →
    ∃ T : κ → GlobalTheory.HTLat.Tate ℓ M, ∀ t : GlobalTheory.HTLat.Tate ℓ M, ∃ (c : κ → 𝓞 E) (s : GlobalTheory.HTLat.Tate ℓ M),
      t = ∑ k, α (c k) (T k) + (ℓ : ℤ_[ℓ]) • s := by
  intro E _ _ ℓ hℓ W _ _ ρ M _ ex hadd hsurj L hL β hβ α hα κ _ y hyL hy
  have h0 : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hℓ.out.ne_zero
  let φ : W →+ Additive M := AddMonoidHom.mk' (fun z => Additive.ofMul (ex z)) hadd
  have hpow : ∀ (z : W) (n : ℕ), ex z ^ n = ex ((n : ℂ) • z) := fun z n => by
    rw [Nat.cast_smul_eq_nsmul]
    exact (map_nsmul φ n z).symm
  let lv : GlobalTheory.HTLat.Tate ℓ M →+ Additive M := AddMonoidHom.mk' (fun t => Additive.ofMul (t.lev 1))
    fun _ _ => rfl
  let T : κ → GlobalTheory.HTLat.Tate ℓ M := fun k =>
    GlobalTheory.HTLat.Tate.mk (fun n => ex (((ℓ : ℂ) ^ n)⁻¹ • y k)) fun n =>
      ⟨by rw [hpow, smul_smul, Nat.cast_pow, mul_inv_cancel₀ (pow_ne_zero _ h0), one_smul, hL]; exact hyL k,
        by rw [hpow, smul_smul, pow_succ', mul_inv, mul_inv_cancel_left₀ h0]⟩
  refine ⟨T, fun t => ?_⟩
  obtain ⟨w, hw⟩ := hsurj (t.lev 1)
  have hwL : (ℓ : ℂ) • w ∈ L := by
    rw [← hL, ← hpow, hw]
    simpa using t.lev_pow 1
  obtain ⟨c, z, hz, h⟩ := hy _ hwL
  have h1 : w = ∑ k, ρ (c k) (((ℓ : ℂ) ^ 1)⁻¹ • y k) + z := by
    rw [← inv_smul_smul₀ h0 w, h, smul_add, inv_smul_smul₀ h0, Finset.smul_sum, pow_one]
    simp only [map_smul]
  have h2 : lv (t - ∑ k, α (c k) (T k)) = 0 := by
    have h3 : lv t = φ w := congrArg Additive.ofMul hw.symm
    have h4 : φ z = 0 := congrArg Additive.ofMul ((hL z).2 hz)
    rw [map_sub, sub_eq_zero, h3, h1, map_add, h4, add_zero, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => congrArg Additive.ofMul ?_
    exact (hβ _ _).trans (hα _ (T k) 1).symm
  obtain ⟨s, hs⟩ := GlobalTheory.TateSpan.exists_eq_p_smul_of_lev_one (t - ∑ k, α (c k) (T k)) h2
  exact ⟨c, s, by rw [← hs]; abel⟩

theorem tate_free_of_lattice : ∀ (E : Type) [Field E] [NumberField E] (ℓ : ℕ) [Fact ℓ.Prime] (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : 𝓞 E →+* Module.End ℂ W) (M : Type) [CommGroup M] (ex : W → M), (∀ z w, ex (z + w) = ex z * ex w) →
    Function.Surjective ex → ∀ (L : Submodule ℤ W), (∀ z, ex z = 1 ↔ z ∈ L) → Module.Finite ℤ L →
    ∀ (β : 𝓞 E → (M →* M)), (∀ a z, ex (ρ a z) = β a (ex z)) →
    ∀ (α : 𝓞 E →+* Module.End ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M)), (∀ a t n, (α a t).lev n = β a (t.lev n)) →
    Module.Free ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M) → Module.Finite ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M) →
    ∀ (κ : Type) [Fintype κ], Module.finrank ℤ L = Fintype.card κ * Module.finrank ℚ E →
    Module.finrank ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M) = Fintype.card κ * Module.finrank ℚ E →
    ∃ f : (κ → ℤ_[ℓ] ⊗[ℤ] 𝓞 E) ≃ₗ[ℤ_[ℓ]] GlobalTheory.HTLat.Tate ℓ M,
      ∀ (a : 𝓞 E) (r : κ → ℤ_[ℓ] ⊗[ℤ] 𝓞 E), f (((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] a) • r) = α a (f r) := by
  intro E _ _ ℓ _ W _ _ ρ M _ ex hadd hsurj L hL hfin β hβ α hα hfree hfinT κ _ hrkL hrkT
  have hstab : ∀ a z, z ∈ L → ρ a z ∈ L := fun a z hz => by
    rw [← hL] at hz ⊢
    rw [hβ, hz, map_one]
  obtain ⟨y, hyL, hy⟩ := exists_gens_mod E ℓ W ρ L hstab hfin κ hrkL
  obtain ⟨T, hT⟩ := exists_tate_gens E ℓ W ρ M ex hadd hsurj L hL β hβ α hα κ y hyL hy
  let act : ℤ_[ℓ] ⊗[ℤ] 𝓞 E →ₐ[ℤ_[ℓ]] Module.End ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M) :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) α.toIntAlgHom
      (fun x a => Algebra.commute_algebraMap_left x _)
  have hact : ∀ a, act ((1 : ℤ_[ℓ]) ⊗ₜ a) = α a := fun a => by
    refine (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans ?_
    rw [map_one, one_mul]
    rfl
  let F : (κ → ℤ_[ℓ] ⊗[ℤ] 𝓞 E) →ₗ[ℤ_[ℓ]] GlobalTheory.HTLat.Tate ℓ M :=
    { toFun := fun r => ∑ k, act (r k) (T k)
      map_add' := fun r s => by
        simp only [Pi.add_apply, map_add, LinearMap.add_apply, Finset.sum_add_distrib]
      map_smul' := fun c r => by
        simp only [Pi.smul_apply, map_smul, LinearMap.smul_apply, Finset.smul_sum, RingHom.id_apply] }
  have hF : ∀ r, F r = ∑ k, act (r k) (T k) := fun r => rfl
  have hmem : ∀ c : κ → 𝓞 E, ∑ k, α (c k) (T k) ∈ LinearMap.range F := fun c =>
    ⟨fun k => (1 : ℤ_[ℓ]) ⊗ₜ c k, by simp only [hF, hact]⟩
  have hI : IsLocalRing.maximalIdeal ℤ_[ℓ] ≤ (⊥ : Ideal ℤ_[ℓ]).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have hle : (⊤ : Submodule ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M)) ≤
      LinearMap.range F ⊔ IsLocalRing.maximalIdeal ℤ_[ℓ] • ⊤ := by
    intro t _
    obtain ⟨c, s, rfl⟩ := hT t
    refine Submodule.add_mem_sup (hmem c) (Submodule.smul_mem_smul ?_ trivial)
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span rfl
  have hsurjF : Function.Surjective F := LinearMap.range_eq_top.1
    (top_le_iff.1 (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI hle))
  have hrkR : Module.finrank ℤ_[ℓ] (κ → ℤ_[ℓ] ⊗[ℤ] 𝓞 E) = Fintype.card κ * Module.finrank ℚ E := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Module.finrank_baseChange, NumberField.RingOfIntegers.rank]
  let e := LinearEquiv.ofFinrankEq (κ → ℤ_[ℓ] ⊗[ℤ] 𝓞 E) (GlobalTheory.HTLat.Tate ℓ M) (hrkR.trans hrkT.symm)
  have hinj : Function.Injective F := by
    have h := OrzechProperty.injective_of_surjective_endomorphism (e.symm.toLinearMap ∘ₗ F)
      (e.symm.surjective.comp hsurjF)
    rw [LinearMap.coe_comp] at h
    exact h.of_comp
  refine ⟨LinearEquiv.ofBijective F ⟨hinj, hsurjF⟩, fun a r => ?_⟩
  change F _ = α a (F r)
  rw [hF, hF, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul, hact]
  rfl

end GlobalTheory.TorusTateFree
end

open scoped TensorProduct NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponential_lattice_endomorphism_lift : ∀ (E : Type) [Field E] [NumberField E] (ℓ : ℕ) [Fact ℓ.Prime] (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : 𝓞 E →+* Module.End ℂ W) (M : Type) [CommGroup M] (ex : W → M), (∀ z w, ex (z + w) = ex z * ex w) →
    Function.Surjective ex → ∀ (L : Submodule ℤ W), (∀ z, ex z = 1 ↔ z ∈ L) → Module.Finite ℤ L →
    ∀ (β : 𝓞 E → (M →* M)), (∀ a z, ex (ρ a z) = β a (ex z)) →
    ∀ (α : 𝓞 E →+* Module.End ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M)), (∀ a t n, (α a t).lev n = β a (t.lev n)) →
    Module.Free ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M) → Module.Finite ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M) →
    ∀ (κ : Type) [Fintype κ], Module.finrank ℤ L = Fintype.card κ * Module.finrank ℚ E →
    Module.finrank ℤ_[ℓ] (GlobalTheory.HTLat.Tate ℓ M) = Fintype.card κ * Module.finrank ℚ E →
    ∃ f : (κ → ℤ_[ℓ] ⊗[ℤ] 𝓞 E) ≃ₗ[ℤ_[ℓ]] GlobalTheory.HTLat.Tate ℓ M,
      ∀ (a : 𝓞 E) (r : κ → ℤ_[ℓ] ⊗[ℤ] 𝓞 E), f (((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] a) • r) = α a (f r) := by
  atlas_forward_decl GlobalTheory.TorusTateFree.tate_free_of_lattice
end

section
set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.HTLat GlobalTheory.EigenSplit
open scoped TensorProduct NNReal

namespace GlobalTheory.IndexIdeal

section Index

variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U]

variable (C) in

def HasIndex (n : ℕ) (L L' : Submodule O U) (I : Ideal O) : Prop :=
  ∃ (w : Fin n → U) (g : Matrix (Fin n) (Fin n) O), LinearIndependent C w ∧ Submodule.span O (Set.range w) = L ∧
    Submodule.span O (Set.range fun i => ∑ j, g i j • w j) = L' ∧ g.det ≠ 0 ∧ Ideal.span {g.det} = I

example {x : U} (hx : x ≠ 0) {a : O} (ha : a ≠ 0) :
    HasIndex C 1 (Submodule.span O {x}) (Submodule.span O {a • x}) (Ideal.span {a}) :=
  ⟨fun _ => x, Matrix.of fun _ _ => a, by simpa using hx, by simp, by simp, by simpa using ha, by simp⟩

theorem hasIndex_of_fintype {κ : Type} [Fintype κ] [DecidableEq κ] {n : ℕ} (hn : Fintype.card κ = n) {w : κ → U}
    (g : Matrix κ κ O) (hw : LinearIndependent C w) (hg : g.det ≠ 0) :
    HasIndex C n (Submodule.span O (Set.range w)) (Submodule.span O (Set.range fun i => ∑ j, g i j • w j))
      (Ideal.span {g.det}) := by
  let e : Fin n ≃ κ := (Fintype.equivFinOfCardEq hn).symm
  refine ⟨w ∘ e, g.submatrix e e, hw.comp _ e.injective, by rw [e.surjective.range_comp], ?_,
    by rwa [Matrix.det_submatrix_equiv_self], by rw [Matrix.det_submatrix_equiv_self]⟩
  rw [← e.surjective.range_comp fun i => ∑ j, g i j • w j]
  congr 2
  funext i
  exact e.sum_comp fun j => g (e i) j • w j

theorem HasIndex.le {n : ℕ} {L L' : Submodule O U} {I : Ideal O} (h : HasIndex C n L L' I) : L' ≤ L := by
  obtain ⟨w, g, -, rfl, rfl, -⟩ := h
  exact Submodule.span_le.2 (Set.range_subset_iff.2 fun i =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

theorem exists_matrix {n : ℕ} {x y : Fin n → U} (h : Submodule.span O (Set.range x) ≤ Submodule.span O (Set.range y)) :
    ∃ a : Matrix (Fin n) (Fin n) O, ∀ i, x i = ∑ j, (a.map (algebraMap O C)) i j • y j := by
  choose a ha using fun i => (Submodule.mem_span_range_iff_exists_fun O).1 (h (Submodule.subset_span ⟨i, rfl⟩))
  exact ⟨Matrix.of a, fun i => by simp only [Matrix.map_apply, Matrix.of_apply, algebraMap_smul, ha]⟩

omit [Module O U] [IsScalarTower O C U] in
theorem comb_comb {n : ℕ} {x y z : Fin n → U} {a b : Matrix (Fin n) (Fin n) C} (h : ∀ i, x i = ∑ j, a i j • y j)
    (h' : ∀ i, y i = ∑ j, b i j • z j) (i : Fin n) : x i = ∑ j, (a * b) i j • z j := by
  simp only [h i, h', Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

omit [Module O U] [IsScalarTower O C U] in
theorem comb_inj {n : ℕ} {x z : Fin n → U} (hz : LinearIndependent C z) {a b : Matrix (Fin n) (Fin n) C}
    (h : ∀ i, x i = ∑ j, a i j • z j) (h' : ∀ i, x i = ∑ j, b i j • z j) : a = b :=
  Matrix.ext fun i => Fintype.linearIndependent_iffₛ.1 hz _ _ ((h i).symm.trans (h' i))

theorem HasIndex.det (hi : Function.Injective (algebraMap O C)) {n : ℕ} {L L' : Submodule O U} {I : Ideal O}
    (h : HasIndex C n L L' I) {x x' : Fin n → U} (hL : Submodule.span O (Set.range x) = L)
    (hL' : Submodule.span O (Set.range x') = L') {a : Matrix (Fin n) (Fin n) C} (ha : ∀ i, x' i = ∑ j, a i j • x j) :
    ∃ d : O, algebraMap O C d = a.det ∧ Ideal.span {d} = I := by
  obtain ⟨w, g, hw, h1, h2, hg, rfl⟩ := h
  haveI : IsDomain O := hi.isDomain (algebraMap O C)
  have hd : ∀ b : Matrix (Fin n) (Fin n) O, (b.map (algebraMap O C)).det = algebraMap O C b.det := fun b =>
    ((algebraMap O C).map_det b).symm
  have hw' : ∀ i, (fun i => ∑ j, g i j • w j) i = ∑ j, (g.map (algebraMap O C)) i j • w j := fun i => by
    simp only [Matrix.map_apply, algebraMap_smul]
  obtain ⟨s, hs⟩ := exists_matrix (C := C) (hL.trans h1.symm).le
  obtain ⟨t, ht⟩ := exists_matrix (C := C) (h1.trans hL.symm).le
  obtain ⟨s', hs'⟩ := exists_matrix (C := C) (hL'.trans h2.symm).le
  obtain ⟨t', ht'⟩ := exists_matrix (C := C) (h2.trans hL'.symm).le
  have e1 := congrArg Matrix.det (comb_inj hw (comb_comb ht hs) (b := 1) fun i => by simp [Matrix.one_apply])
  have e2 := congrArg Matrix.det (comb_inj hw (comb_comb ha hs) (comb_comb hs' hw'))
  have e3 := congrArg Matrix.det (comb_inj hw (comb_comb ht' (comb_comb hs' hw')) hw')
  simp only [Matrix.det_mul, hd, Matrix.det_one] at e1 e2 e3
  have f1 : t.det * s.det = 1 := hi (by rw [map_mul, e1, map_one])
  have f3 : t'.det * s'.det = 1 := mul_right_cancel₀ hg (hi (by rw [map_mul, map_mul, mul_assoc, e3, _root_.one_mul]))
  refine ⟨t.det * s'.det * g.det, ?_, ?_⟩
  · rw [map_mul, map_mul, mul_assoc, ← e2, mul_left_comm, e1, _root_.mul_one]
  · exact Ideal.span_singleton_mul_left_unit ((IsUnit.of_mul_eq_one _ f1).mul (IsUnit.of_mul_eq_one_right _ f3)) _

theorem HasIndex.val_det {v : Valuation C ℝ≥0} (hv : v.Integers O) {n : ℕ} {L L' : Submodule O U} {d : O}
    (h : HasIndex C n L L' (Ideal.span {d})) {x x' : Fin n → U} (hL : Submodule.span O (Set.range x) = L)
    (hL' : Submodule.span O (Set.range x') = L') {a : Matrix (Fin n) (Fin n) C} (ha : ∀ i, x' i = ∑ j, a i j • x j) :
    v a.det = v (algebraMap O C d) := by
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  obtain ⟨d', h1, h2⟩ := h.det hv.hom_inj hL hL' ha
  obtain ⟨u, rfl⟩ := Ideal.span_singleton_eq_span_singleton.1 h2
  rw [← h1, map_mul, map_mul, hv.one_of_isUnit u.isUnit, mul_one]

end Index

section Parts

variable {A R Λ O C : Type} [CommRing A] [CommRing R] [CommRing Λ] [CommRing O] [Field C] [Algebra A R] [Algebra A O]
  [Algebra A C] [Algebra O C] [IsScalarTower A O C] {ι : Λ →+* R} (hι : Submodule.span A (Set.range ι) = ⊤)
  {J : Type} [DecidableEq J] {σ : J → Λ →+* O} (hs : IsSplitting (embC C σ)) (k : J) (χ : R →ₐ[A] O)
  (hχ : ∀ a, χ (ι a) = σ k a) {T : Type} [AddCommGroup T] [Module A T] (ρ : Λ →+* Module.End A T)
  {κ : Type} [Fintype κ] [DecidableEq κ] (f : (κ → R) ≃ₗ[A] T) (hf : ∀ a r, f (ι a • r) = ρ a (f r))

def part (j : κ) : C ⊗[A] T := proj hs (baseChangeAction C ρ) k (1 ⊗ₜ f (Pi.single j 1))

include hι hχ hf in
theorem proj_frame (r : κ → R) :
    proj hs (baseChangeAction C ρ) k (1 ⊗ₜ f r) = ∑ j, χ (r j) • part hs k ρ f j := by
  have h1 : ∀ (s : R) (r : κ → R), proj hs (baseChangeAction C ρ) k (1 ⊗ₜ f (s • r)) =
      χ s • proj hs (baseChangeAction C ρ) k (1 ⊗ₜ f r) := fun s r => by
    have hm : s ∈ Submodule.span A (Set.range ι) := hι ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      have e := (isEquivariant_action (baseChangeAction C ρ) a).proj hs k (1 ⊗ₜ f r)
      rw [mem_eigenSub.1 (proj_mem hs _ k _) a] at e
      rw [hf, hχ, ← algebraMap_smul C]
      exact e.symm
    | zero => simp
    | add x y _ _ hx hy => rw [add_smul, map_add, TensorProduct.tmul_add, map_add, hx, hy, map_add, add_smul]
    | smul a x _ hx =>
      rw [smul_assoc, map_smul, TensorProduct.tmul_smul, LinearMap.map_smul_of_tower, hx, map_smul, smul_assoc]
  conv_lhs => rw [pi_eq_sum_univ' r, map_sum, TensorProduct.tmul_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ => h1 _ _

include hχ hf in
theorem linearIndependent_part : LinearIndependent C (part hs k ρ f) := by
  let g : κ → (C ⊗[A] T →ₗ[C] C) := fun j => LinearMap.liftBaseChange C
    ((Algebra.linearMap O C).restrictScalars A ∘ₗ χ.toLinearMap ∘ₗ LinearMap.proj j ∘ₗ f.symm.toLinearMap)
  let ρ' : Λ →+* Module.End C C := (algebraMap C _).comp (embC C σ k)
  have hg : ∀ j, IsEquivariant (baseChangeAction C ρ) ρ' (g j) := fun j a x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c t =>
      obtain ⟨r, rfl⟩ := f.surjective t
      have : baseChangeAction C ρ a (c ⊗ₜ f r) = c ⊗ₜ f (ι a • r) := by rw [hf]; rfl
      rw [this]
      simp [g, ρ', hχ, mul_left_comm]
  have hd : ∀ j l, g j (part hs k ρ f l) = if j = l then 1 else 0 := fun j l => by
    rw [part, (hg j).proj hs k, proj_of_mem hs (mem_eigenSub.2 fun a => by simp [ρ'])]
    simp [g, Pi.single_apply, apply_ite]
  refine Fintype.linearIndependent_iff.2 fun c hc j => ?_
  simpa [hd] using congrArg (g j) hc

include hι hχ hf in
theorem span_part : Submodule.span O (Set.range (part hs k ρ f)) = eigQuotLat (baseChangeAction C ρ) hs k
    (LinearMap.range ((TensorProduct.mk A C T 1).liftBaseChange O)) := by
  refine le_antisymm (Submodule.span_le.2 (Set.range_subset_iff.2 fun j => ⟨_, ⟨1 ⊗ₜ f (Pi.single j 1), ?_⟩, rfl⟩)) ?_
  · simp
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
    | tmul c t =>
      obtain ⟨r, rfl⟩ := f.surjective t
      rw [LinearMap.liftBaseChange_tmul, map_smul]
      refine Submodule.smul_mem _ _ ?_
      have e := proj_frame hι hs k χ hχ ρ f hf r
      exact e ▸ Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end Parts

section Sum

variable {A R Λ O C : Type} [CommRing A] [CommRing R] [CommRing Λ] [CommRing O] [Field C] [Algebra A R] [Algebra A O]
  [Algebra A C] [Algebra O C] [IsScalarTower A O C] {ι : Λ →+* R} (hι : Submodule.span A (Set.range ι) = ⊤)
  {J : Type} [DecidableEq J] {σ : J → Λ →+* O} (hs : IsSplitting (embC C σ)) (k : J) (χ : R →ₐ[A] O)
  (hχ : ∀ a, χ (ι a) = σ k a) {T : Type} [AddCommGroup T] [Module A T] (ρ : Λ →+* Module.End A T)
  {κ : Type} [Fintype κ] [DecidableEq κ] (f : (κ → R) ≃ₗ[A] T) (hf : ∀ a r, f (ι a • r) = ρ a (f r))
  {T' : Type} [AddCommGroup T'] [Module A T'] (ρ' : Λ →+* Module.End A T')
  (f' : (Unit → R) ≃ₗ[A] T') (hf' : ∀ a r, f' (ι a • r) = ρ' a (f' r))

include hι hχ hf hf' in

theorem map_quot_eq (φ : T' →ₗ[A] T) (hφ : ∀ a x, φ (ρ' a x) = ρ a (φ x)) {m : κ → R} (hm : f m = φ (f' 1)) :
    (eigQuotLat (baseChangeAction C ρ') hs k (LinearMap.range ((TensorProduct.mk A C T' 1).liftBaseChange O))).map
      ((φ.baseChange C).restrictScalars O) = Submodule.span O {∑ j, χ (m j) • part hs k ρ f j} := by
  have he : IsEquivariant (baseChangeAction C ρ') (baseChangeAction C ρ) (φ.baseChange C) := fun a x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c t => exact congrArg (c ⊗ₜ ·) (hφ a t)
  rw [← span_part hι hs k χ hχ ρ' f' hf', Set.range_unique, Submodule.map_span, Set.image_singleton,
    ← proj_frame hι hs k χ hχ ρ f hf, hm]
  congr 2
  refine (he.proj hs k _).trans ?_
  rw [LinearMap.baseChange_tmul]
  congr 4

end Sum

section Completion

variable (ℓ : ℕ) [Fact ℓ.Prime] (Λ : Type) [CommRing Λ]

abbrev toCompl : Λ →+* ℤ_[ℓ] ⊗[ℤ] Λ := (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom

theorem span_toCompl : Submodule.span ℤ_[ℓ] (Set.range (toCompl ℓ Λ)) = ⊤ := by
  refine top_le_iff.1 fun x _ => ?_
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
  | tmul c a =>
    have : c ⊗ₜ[ℤ] a = c • toCompl ℓ Λ a := by simp [TensorProduct.smul_tmul']
    exact this ▸ Submodule.smul_mem _ c (Submodule.subset_span ⟨a, rfl⟩)

variable {Λ} in

def extChar {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] (χ : Λ →+* O) : ℤ_[ℓ] ⊗[ℤ] Λ →ₐ[ℤ_[ℓ]] O :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) χ.toIntAlgHom fun _ _ => Commute.all _ _

variable {Λ} in
theorem extChar_toCompl {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] (χ : Λ →+* O) (a : Λ) :
    extChar ℓ χ (toCompl ℓ Λ a) = χ a := by simp [extChar]

end Completion

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompHt GlobalTheory.CM GlobalTheory.FlatCM GlobalTheory.PointMap GlobalTheory.GramAt
attribute [local instance] Over.cartesianMonoidalCategory

section Frames

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]

def IsFrame {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point ℓ v O Λ) {κ : Type}
    (f : (κ → ℤ_[ℓ] ⊗[ℤ] Λ) ≃ₗ[ℤ_[ℓ]] P.T) : Prop :=
  ∀ a r, f (toCompl ℓ Λ a • r) = P.actT a (f r)

variable {E : Type} [Field E] [NumberField E]

theorem exists_isFrame_complex [StarRing (𝓞 E)] {v : Valuation ℂ ℝ≥0} {O : Type} [CommRing O] [Algebra O ℂ]
    (P : Point ℓ v O (𝓞 E)) (κ : Type) [Fintype κ] (h : 2 * P.A.g = Fintype.card κ * Module.finrank ℚ E) :
    ∃ f : (κ → ℤ_[ℓ] ⊗[ℤ] 𝓞 E) ≃ₗ[ℤ_[ℓ]] P.T, IsFrame P f := by
  have hT : ThetaUnifAV := thetaUnifAV_all
  obtain ⟨u, HA, χA, -, hu, -⟩ := PureType.exists_isThetaUnif hT P.A
  obtain ⟨-, -, -, -, h1, h2, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hT P.A _ u HA χA hu
  let α := P.oA.toRingAct
  choose F hF using fun a : 𝓞 E => (HomLinear.exists_linear_of_isMonHom P.A.A P.A.A P.A.isAb P.A.isAb _ _ _ _ u u h1 h2
    (α.act a) (α.hom a)).imp fun _ h => h.1
  have hu0 : ∀ M N : (Fin P.A.g → ℂ) →ₗ[ℂ] (Fin P.A.g → ℂ), (∀ z, u.ex (M z) = u.ex (N z)) → M = N := fun M N h => by
    refine sub_eq_zero.1 (PointUnif.linear_eq_zero_of_discrete u.Λ u.discrete _ fun z => (u.ker _).1 ?_)
    have := u.ex_add ((M - N) z) (N z)
    rw [LinearMap.sub_apply, sub_add_cancel, h] at this
    exact mul_eq_right.1 this.symm
  let ρ : 𝓞 E →+* Module.End ℂ (Fin P.A.g → ℂ) := RingHom.mk' (MonoidHom.mk (OneHom.mk F
      (hu0 _ _ fun z => by rw [hF, α.map_one, Category.comp_id]; rfl))
      fun a b => hu0 _ _ fun z => by
        change u.ex (F (a * b) z) = u.ex (F a (F b z))
        rw [hF, hF, hF, α.map_mul, Category.assoc])
    fun a b => hu0 _ _ fun z => by
      change u.ex (F (a + b) z) = u.ex (F a z + F b z)
      rw [u.ex_add, hF, hF, hF, actPts_add]
  haveI := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  exact GlobalTheory.T.exponential_lattice_endomorphism_lift E ℓ _ ρ (ChTor.Pts P.A.A) u.ex u.ex_add u.ex_onto u.Λ u.ker (ZLattice.module_finite ℝ u.Λ)
    (actPts α _) hF P.actT (fun _ _ _ => rfl) inferInstance inferInstance κ
    (by rw [ZLattice.rank ℝ u.Λ, Module.finrank_pi_fintype, ← h]; simp [mul_comm]) (P.hodgeTateLatticePoint_finrank_tateModule.trans h)

variable [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K] [IsAlgClosed C] [CharZero C]
  (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C)

theorem exists_isFrame (T : PAT H (Sp (𝓞 K))) (κ : Type) [Fintype κ]
    (h : 2 * T.g = Fintype.card κ * Module.finrank ℚ E) : letI := H.starRing
    ∃ f : (κ → ℤ_[ℓ] ⊗[ℤ] 𝓞 E) ≃ₗ[ℤ_[ℓ]] (patPoint hv ε i T).T, IsFrame (patPoint hv ε i T) f := by
  classical
  letI := H.starRing
  obtain ⟨ε'⟩ : Nonempty (Eps ℓ ℂ) := inferInstance
  have hv' : (1 : Valuation ℂ ℝ≥0).Integers ℂ :=
    ⟨fun _ _ h => h, fun x => Valuation.one_apply_le_one x, fun {x} _ => ⟨x, rfl⟩⟩
  let i' : K →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := K) (M := ℂ)).toRingHom
  obtain ⟨e, he, -⟩ := exists_patT_equiv (H := H) hv' ε' i' hv ε i
  obtain ⟨f, hf⟩ := exists_isFrame_complex (patPoint hv' ε' i' T) κ h
  exact ⟨f.trans (e T), fun a r => (congrArg (e T) (hf a r)).trans (he T a _)⟩

end Frames

section Points

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  {Λ : Type} [CommRing Λ] [StarRing Λ] [Algebra ℤ_[ℓ] C] [Algebra ℤ_[ℓ] O] [IsScalarTower ℤ_[ℓ] O C]
  {J : Type} [DecidableEq J] {σ : J → Λ →+* O} (hs : IsSplitting (embC C σ)) (k : J)

theorem IsFrame.exists_basis {P : Point ℓ v O Λ} {n : ℕ} {f : (Fin n → ℤ_[ℓ] ⊗[ℤ] Λ) ≃ₗ[ℤ_[ℓ]] P.T}
    (hf : IsFrame P f) :
    ∃ w : Fin n → P.V, LinearIndependent C w ∧ Submodule.span O (Set.range w) = P.latTQuot hs k :=
  ⟨part hs k P.actT f, linearIndependent_part hs k (extChar ℓ (σ k)) (extChar_toCompl ℓ _) P.actT f hf,
    span_part (span_toCompl ℓ Λ) hs k (extChar ℓ (σ k)) (extChar_toCompl ℓ _) P.actT f hf⟩

theorem hasIndex_of_frames {A A' B : Point ℓ v O Λ} {p q : ℕ} (φ : Fin p → (A.T →ₗ[ℤ_[ℓ]] B.T))
    (φ' : Fin q → (A'.T →ₗ[ℤ_[ℓ]] B.T)) (hφ : ∀ a c x, φ a (A.actT c x) = B.actT c (φ a x))
    (hφ' : ∀ a c x, φ' a (A'.actT c x) = B.actT c (φ' a x)) {f₁ : (Unit → ℤ_[ℓ] ⊗[ℤ] Λ) ≃ₗ[ℤ_[ℓ]] A.T}
    {f₂ : (Unit → ℤ_[ℓ] ⊗[ℤ] Λ) ≃ₗ[ℤ_[ℓ]] A'.T} {f : (Fin p ⊕ Fin q → ℤ_[ℓ] ⊗[ℤ] Λ) ≃ₗ[ℤ_[ℓ]] B.T}
    (h₁ : IsFrame A f₁) (h₂ : IsFrame A' f₂) (h : IsFrame B f)
    {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) (ℤ_[ℓ] ⊗[ℤ] Λ)} (hM₁ : ∀ a, f (M (.inl a)) = φ a (f₁ 1))
    (hM₂ : ∀ a, f (M (.inr a)) = φ' a (f₂ 1)) (hd : extChar ℓ (σ k) M.det ≠ 0) :
    HasIndex C (p + q) (B.latTQuot hs k)
      ((⨆ a, (A.latTQuot hs k).map (((φ a).baseChange C).restrictScalars O)) ⊔
        ⨆ b, (A'.latTQuot hs k).map (((φ' b).baseChange C).restrictScalars O))
      (Ideal.span {extChar ℓ (σ k) M.det}) := by
  have hχ := extChar_toCompl ℓ (σ k)
  have e := hasIndex_of_fintype (n := p + q) (by simp) (M.map (extChar ℓ (σ k)))
    (linearIndependent_part hs k _ hχ B.actT f h) (((extChar ℓ (σ k)).map_det M).symm.trans_ne hd)
  rw [span_part (span_toCompl ℓ Λ) hs k _ hχ B.actT f h, Submodule.span_range_eq_iSup, iSup_sum] at e
  have e₁ : ∀ a, (A.latTQuot hs k).map (((φ a).baseChange C).restrictScalars O) = _ := fun a =>
    map_quot_eq (span_toCompl ℓ Λ) hs k _ hχ B.actT f h A.actT f₁ h₁ (φ a) (hφ a) (hM₁ a)
  have e₂ : ∀ a, (A'.latTQuot hs k).map (((φ' a).baseChange C).restrictScalars O) = _ := fun a =>
    map_quot_eq (span_toCompl ℓ Λ) hs k _ hχ B.actT f h A'.actT f₂ h₂ (φ' a) (hφ' a) (hM₂ a)
  rw [iSup_congr e₁, iSup_congr e₂, (extChar ℓ (σ k)).map_det M]
  exact e

end Points

section Object

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ}

section At

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C) (X : CMObj H K ρ σ₁ p q)

def IsFrameDet (δ : ℤ_[ℓ] ⊗[ℤ] 𝓞 E) : Prop :=
  letI := H.starRing
  ∃ (f₁ : (Unit → ℤ_[ℓ] ⊗[ℤ] 𝓞 E) ≃ₗ[ℤ_[ℓ]] (pointA hv ε i X true).T)
    (f₂ : (Unit → ℤ_[ℓ] ⊗[ℤ] 𝓞 E) ≃ₗ[ℤ_[ℓ]] (pointA hv ε i X false).T)
    (f : (Fin p ⊕ Fin q → ℤ_[ℓ] ⊗[ℤ] 𝓞 E) ≃ₗ[ℤ_[ℓ]] (pointB hv ε i X).T)
    (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) (ℤ_[ℓ] ⊗[ℤ] 𝓞 E)),
    IsFrame _ f₁ ∧ IsFrame _ f₂ ∧ IsFrame _ f ∧ (∀ a, f (M (.inl a)) = phiTP hv ε i X a (f₁ 1)) ∧
      (∀ a, f (M (.inr a)) = phiTQ hv ε i X a (f₂ 1)) ∧ M.det = δ

variable [IsAlgClosed C] [CharZero C]

omit [NumberField K] in
theorem two_mul_half : 2 * (Module.finrank ℚ E / 2) = Module.finrank ℚ E :=
  Nat.mul_div_cancel' ⟨Module.finrank ℚ (maximalRealSubfield E), by
    rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E, Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]⟩

theorem exists_isFrameDet : ∃ δ, IsFrameDet hv ε i X δ := by
  letI := H.starRing
  obtain ⟨h1, h2, -⟩ := dims X
  obtain ⟨f₁, h₁⟩ := exists_isFrame hv ε i (X.A true) Unit (by simp [h1, two_mul_half])
  obtain ⟨f₂, h₂⟩ := exists_isFrame hv ε i (X.A false) Unit (by simp [h1, two_mul_half])
  obtain ⟨f, h⟩ := exists_isFrame hv ε i X.B (Fin p ⊕ Fin q) (by
    rw [h2, ← mul_assoc, two_mul_half, mul_comm]; simp)
  exact ⟨_, f₁, f₂, f, Matrix.of (Sum.elim (fun a => f.symm (phiTP hv ε i X a (f₁ 1)))
    fun a => f.symm (phiTQ hv ε i X a (f₂ 1))), h₁, h₂, h, fun a => f.apply_symm_apply _,
    fun a => f.apply_symm_apply _, rfl⟩

variable {hv ε i X}

theorem IsFrameDet.transport {δ : ℤ_[ℓ] ⊗[ℤ] 𝓞 E} (h : IsFrameDet hv ε i X δ) {C' : Type} [Field C']
    {v' : Valuation C' ℝ≥0} {O' : Type} [CommRing O'] [Algebra O' C'] [IsAlgClosed C'] [CharZero C']
    (hv' : v'.Integers O') (ε' : Eps ℓ C') (i' : K →+* C') : IsFrameDet hv' ε' i' X δ := by
  letI := H.starRing
  obtain ⟨f₁, f₂, f, M, h₁, h₂, h, hM₁, hM₂, hd⟩ := h
  obtain ⟨e, he, he'⟩ := exists_patT_equiv (H := H) hv ε i hv' ε' i'
  exact ⟨f₁.trans (e (X.A true)), f₂.trans (e (X.A false)), f.trans (e X.B), M,
    fun a r => (congrArg (e _) (h₁ a r)).trans (he _ a _), fun a r => (congrArg (e _) (h₂ a r)).trans (he _ a _),
    fun a r => (congrArg (e _) (h a r)).trans (he _ a _),
    fun a => (congrArg (e _) (hM₁ a)).trans (he' (X.A true) X.B _ (X.lin (.inl a)) _),
    fun a => (congrArg (e _) (hM₂ a)).trans (he' (X.A false) X.B _ (X.lin (.inr a)) _), hd⟩

theorem IsFrameDet.associated {δ : ℤ_[ℓ] ⊗[ℤ] 𝓞 E} (h : IsFrameDet hv ε i X δ) {gP : Matrix (Fin p) (Fin p) (𝓞 E)}
    {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (hg : IsGram X gP gQ) :
    Associated (δ * Algebra.TensorProduct.map (AlgHom.id ℤ_[ℓ] ℤ_[ℓ]) (H.bar : 𝓞 E →+* 𝓞 E).toIntAlgHom δ)
      ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] (gP.det * gQ.det)) := by
  letI := H.starRing
  obtain ⟨f₁, f₂, f, M, h₁, h₂, h, hM₁, hM₂, rfl⟩ := h
  obtain ⟨hP, hQ, hO⟩ := tateModule_gram_relations_blocks_orthogonal hv ε i X hg
  exact GlobalTheory.T.conjugate_linear_tensor_module_decomposition ℤ_[ℓ] _ (𝓞 E) (toCompl ℓ _) (span_toCompl ℓ _) (H.bar : 𝓞 E →+* 𝓞 E) _ (fun _ => rfl)
    (fun a => star_star a) _ _ _ (pointA hv ε i X true).actT (pointA hv ε i X false).actT (pointB hv ε i X).actT
    (pairT (pointA hv ε i X true).A ε) (pairT (pointA hv ε i X false).A ε) (pairT (pointB hv ε i X).A ε)
    (pointA hv ε i X true).pairT_bijective (pointA hv ε i X false).pairT_bijective (pointB hv ε i X).pairT_bijective
    (pairT_act (pointA hv ε i X true).oA ε) (pairT_act (pointA hv ε i X false).oA ε)
    (pairT_act (pointB hv ε i X).oA ε) _ _ (phiTP hv ε i X) (phiTQ hv ε i X) gP gQ
    (fun a => patT_actT (T := X.A true) hv ε i (X.lin (.inl a)))
    (fun a => patT_actT (T := X.A false) hv ε i (X.lin (.inr a))) hP hQ hO
    (fun a b s t => ((isAlt_pairT (pointB hv ε i X).A ε).neg_eq _ _).symm.trans (neg_eq_zero.2 (hO b a t s)))
    f₁ f₂ f h₁ h₂ h M hM₁ hM₂

variable (hv ε i X) [Algebra ℤ_[ℓ] C] [Algebra ℤ_[ℓ] O] [IsScalarTower ℤ_[ℓ] O C]
  {J : Type} [DecidableEq J] {σ : J → 𝓞 E →+* O} (hs : IsSplitting (embC C σ)) (k : J)

abbrev quotImage : letI := H.starRing; Submodule O (pointB hv ε i X).V :=
  letI := H.starRing
  (⨆ a, ((pointA hv ε i X true).latTQuot hs k).map ((phiVP hv ε i X a).restrictScalars O)) ⊔
    ⨆ b, ((pointA hv ε i X false).latTQuot hs k).map ((phiVQ hv ε i X b).restrictScalars O)

theorem exists_basis_latTQuot_pure (b : Bool) : letI := H.starRing
    ∃ w : Fin 1 → (pointA hv ε i X b).V, LinearIndependent C w ∧
      Submodule.span O (Set.range w) = (pointA hv ε i X b).latTQuot hs k := by
  letI := H.starRing
  obtain ⟨f, h⟩ := exists_isFrame hv ε i (X.A b) (Fin 1) (by simp [(dims X).1, two_mul_half])
  exact h.exists_basis hs k

end At

theorem exists_indexIdeal (X : CMObj H K ρ σ₁ p q) {gP : Matrix (Fin p) (Fin p) (𝓞 E)}
    {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (h : IsGram X gP gQ) : letI := H.starRing
    ∃ 𝔫 : Ideal (𝓞 E), 𝔫 * 𝔫.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {gP.det * gQ.det} ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type)
        [CommRing O] [Algebra O C] [Algebra ℤ_[ℓ] C] [Algebra ℤ_[ℓ] O] [IsScalarTower ℤ_[ℓ] O C] (hv : v.Integers O)
        (ε : Eps ℓ C) (i : K →+* C) (J : Type) [DecidableEq J] (σ : J → 𝓞 E →+* O) (hs : IsSplitting (embC C σ)) (k : J),
        HasIndex C (p + q) ((pointB hv ε i X).latTQuot hs k) (quotImage hv ε i X hs k) (𝔫.map (σ k)) := by
  letI := H.starRing
  have hD : gP.det * gQ.det ≠ 0 := mul_ne_zero (gram_det X h).1 (gram_det X h).2.1
  have hex : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ δ, IsFrameDet (PadicComplexInt.integers ℓ)
      (Classical.arbitrary (Eps ℓ ℂ_[ℓ])) (IsAlgClosed.lift (R := ℚ) (S := K) (M := ℂ_[ℓ])).toRingHom X δ :=
    fun ℓ _ => exists_isFrameDet _ _ _ X
  choose δ hδ using hex
  have hm : 0 < Ideal.absNorm (Ideal.span {gP.det * gQ.det}) :=
    Nat.pos_of_ne_zero fun h0 => hD (Ideal.span_singleton_eq_bot.1 (Ideal.absNorm_eq_zero_iff.1 h0))
  obtain ⟨𝔫, h1, h2⟩ := GlobalTheory.T.ideal_norm_equation_from_local_associates (𝓞 E) (H.bar : 𝓞 E →+* 𝓞 E) _ _ hm (Ideal.absNorm_mem _) δ
    fun ℓ _ => (hδ ℓ).associated h
  refine ⟨𝔫, h1, fun ℓ _ C _ _ _ v O _ _ _ _ _ hv ε i J _ σ hs k => ?_⟩
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : CharZero O := (algebraMap O C).charZero
  have e : 𝔫.map (σ k) = Ideal.span {extChar ℓ (σ k) (δ ℓ)} := by
    have e' : (extChar ℓ (σ k)).toRingHom.comp (toCompl ℓ _) = σ k := RingHom.ext (extChar_toCompl ℓ (σ k))
    refine (congrArg 𝔫.map e').symm.trans ?_
    rw [← Ideal.map_map, h2, Ideal.map_span, Set.image_singleton]
    rfl
  have h0 : extChar ℓ (σ k) (δ ℓ) ≠ 0 := fun h0 => by
    have : (Ideal.span {gP.det * gQ.det}).map (σ k) = ⊥ := by
      rw [← h1, Ideal.map_mul, e, h0]; simp
    have h3 := Ideal.mem_map_of_mem (σ k) (Ideal.absNorm_mem (Ideal.span {gP.det * gQ.det}))
    rw [this, map_natCast, Ideal.mem_bot, Nat.cast_eq_zero] at h3
    exact hm.ne' h3
  obtain ⟨f₁, f₂, f, M, h₁, h₂, h', hM₁, hM₂, hd⟩ := (hδ ℓ).transport hv ε i
  rw [e, ← hd]
  exact hasIndex_of_frames hs k (A := pointA hv ε i X true) (A' := pointA hv ε i X false) (B := pointB hv ε i X)
    (phiTP hv ε i X) (phiTQ hv ε i X) (fun a => patT_actT (T := X.A true) hv ε i (X.lin (.inl a)))
    (fun a => patT_actT (T := X.A false) hv ε i (X.lin (.inr a))) h₁ h₂ h' hM₁ hM₂ (hd ▸ h0)

omit [IsCMField E] in

theorem exists_embO_eq {C : Type} [Field C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
    (hv : v.Integers O) (χ : 𝓞 E →+* O) : ∃ φ : E →+* C, embO hv φ = χ := by
  have hi : Function.Injective ((algebraMap O C).comp χ) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra h0
    have h := Ideal.absNorm_mem (RingHom.ker ((algebraMap O C).comp χ))
    rw [RingHom.mem_ker, map_natCast, Nat.cast_eq_zero] at h
    exact h0 (Ideal.absNorm_eq_zero_iff.1 h)
  exact ⟨IsFractionRing.lift hi, RingHom.ext fun a => hv.hom_inj
    ((algebraMap_embO hv _ a).trans (IsFractionRing.lift_algebraMap hi a))⟩

open Classical GlobalTheory.HTLat.OmegaRank in

theorem index_ideal (X : CMObj H K ρ σ₁ p q) {gP : Matrix (Fin p) (Fin p) (𝓞 E)}
    {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (h : IsGram X gP gQ) :
    ∃ 𝔫 : Ideal (𝓞 E), 𝔫 * 𝔫.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {gP.det * gQ.det} ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ε : Eps ℓ ℂ_[ℓ]) (i : K →+* ℂ_[ℓ]) (τ : 𝓞 E →+* 𝓞 K),
        letI := H.starRing; letI := algPadicInt ℓ; letI := algPadicField ℓ; haveI := towerPadic ℓ
        ∃ φ : E →+* ℂ_[ℓ], embO (PadicComplexInt.integers ℓ) φ = (embO (PadicComplexInt.integers ℓ) i).comp τ ∧
          HasIndex ℂ_[ℓ] (p + q)
            ((pointB (PadicComplexInt.integers ℓ) ε i X).latTQuot
              (σ := fun φ : E →+* ℂ_[ℓ] => embO (PadicComplexInt.integers ℓ) φ)
              (isSplitting_embO (PadicComplexInt.integers ℓ)) φ)
            (quotImage (PadicComplexInt.integers ℓ) ε i X
              (σ := fun φ : E →+* ℂ_[ℓ] => embO (PadicComplexInt.integers ℓ) φ)
              (isSplitting_embO (PadicComplexInt.integers ℓ)) φ)
            (𝔫.map ((embO (PadicComplexInt.integers ℓ) i).comp τ)) := by
  obtain ⟨𝔫, h1, h2⟩ := exists_indexIdeal X h
  refine ⟨𝔫, h1, fun ℓ _ ε i τ => ?_⟩
  letI := algPadicInt ℓ; letI := algPadicField ℓ; haveI := towerPadic ℓ
  obtain ⟨φ, hφ⟩ := exists_embO_eq (PadicComplexInt.integers ℓ) ((embO (PadicComplexInt.integers ℓ) i).comp τ)
  exact ⟨φ, hφ, hφ ▸ h2 ℓ ℂ_[ℓ] _ _ (PadicComplexInt.integers ℓ) ε i _
    (fun φ : E →+* ℂ_[ℓ] => embO (PadicComplexInt.integers ℓ) φ) (isSplitting_embO (PadicComplexInt.integers ℓ)) φ⟩

end Object

end GlobalTheory.IndexIdeal
end
end
