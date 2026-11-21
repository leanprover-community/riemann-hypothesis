import Mathlib
import Development.WeilBound.LevelCriteria.IsLevOneIff
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt

section
set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

namespace Pre

open GlobalTheory.PDA.Model TensorProduct

variable {B : Type} [CommRing B]

def liftL (c : ℕ → B) (h0 : c 0 = 1) (hm : ∀ m n, c m * c n = ((m + n).choose m : B) * c (m + n)) : L →ₐ[ℤ] B :=
  AlgHom.ofLinearMap (bL.constr ℤ c) (by rw [← bL_zero, Module.Basis.constr_basis, h0]) (by
    intro x y
    have key : (LinearMap.mul ℤ L).compr₂ (bL.constr ℤ c) =
        (LinearMap.mul ℤ B).compl₁₂ (bL.constr ℤ c) (bL.constr ℤ c) := by
      refine bL.ext fun m ↦ bL.ext fun n ↦ ?_
      simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₁₂_apply,
        Module.Basis.constr_basis, bL_mul]
      rw [← nsmul_eq_mul, map_nsmul, Module.Basis.constr_basis, nsmul_eq_mul, hm]
    exact congrArg (fun g ↦ g x y) key)

theorem liftL_bL (c : ℕ → B) (h0 : c 0 = 1) (hm : ∀ m n, c m * c n = ((m + n).choose m : B) * c (m + n))
    (n : ℕ) : liftL c h0 hm (bL n) = c n := bL.constr_basis ℤ c n

theorem cancel {n : ℕ} (hn : n ≠ 0) {x y : L ⊗[ℤ] L} (h : (n : L ⊗[ℤ] L) * x = n * y) : x = y := by
  rw [← nsmul_eq_mul, ← nsmul_eq_mul] at h
  refine (bL.tensorProduct bL).repr.injective (Finsupp.ext fun i ↦ ?_)
  have := congrArg (fun z ↦ (bL.tensorProduct bL).repr z i) h
  simp only [map_nsmul, Finsupp.smul_apply] at this
  rw [nsmul_eq_mul, nsmul_eq_mul] at this
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hn) this

theorem fact_mul {D : Type} [CommRing D] (u : ℕ → D) (h0 : u 0 = 1)
    (hm : ∀ m n, u m * u n = ((m + n).choose m : D) * u (m + n)) (n : ℕ) :
    (n.factorial : D) * u n = u 1 ^ n := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    rw [pow_succ', ← ih, mul_left_comm, hm, Nat.factorial_succ, add_comm 1 n]
    simp; ring

theorem fact_sum {D : Type} [CommRing D] (x y : D) (w w' : ℕ → D) (hw : ∀ k, (k.factorial : D) * w k = x ^ k)
    (hw' : ∀ k, (k.factorial : D) * w' k = y ^ k) (m : ℕ) :
    (m.factorial : D) * ∑ k ∈ Finset.HasAntidiagonal.antidiagonal m, w k.1 * w' k.2 = (x + y) ^ m := by
  rw [(Commute.all x y).add_pow', Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' : k.1 + k.2 = m := by simpa using hk
  rw [← hw, ← hw', ← hk', ← Nat.add_choose_mul_factorial_mul_factorial, Nat.choose_symm_add]
  push_cast
  rw [nsmul_eq_mul]; ring

theorem eq_ub {D : Type} [CommRing D] (hc : ∀ {n : ℕ}, n ≠ 0 → ∀ {x y : D}, (n : D) * x = n * y → x = y)
    (t : D) (z : ℕ → D) (hz : ∀ k, (k.factorial : D) * z k = t ^ k) (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (m.factorial : D) * ((m.uniformBell n : D) * z (m * n)) = z n ^ m := by
  refine hc (n := n.factorial ^ m) (by positivity) ?_
  have h := congrArg (Nat.cast : ℕ → D) (Nat.uniformBell_mul_eq m hn)
  push_cast at h ⊢
  rw [← mul_pow, hz, ← pow_mul, mul_comm n m, ← hz, ← h]; ring

theorem comp_add {J : Ideal B} {γ : ℕ → B → B} (H : IsPreDP J γ) {a b : B} (ha : a ∈ J) (hb : b ∈ J)
    (ka : ∀ m n : ℕ, n ≠ 0 → γ m (γ n a) = (m.uniformBell n : B) * γ (m * n) a)
    (kb : ∀ m n : ℕ, n ≠ 0 → γ m (γ n b) = (m.uniformBell n : B) * γ (m * n) b) (m n : ℕ) (hn : n ≠ 0) :
    γ m (γ n (a + b)) = (m.uniformBell n : B) * γ (m * n) (a + b) := by
  let u : ℕ → L ⊗[ℤ] L := fun k ↦ bL k ⊗ₜ 1
  let v : ℕ → L ⊗[ℤ] L := fun k ↦ 1 ⊗ₜ bL k
  have hu : ∀ k, (k.factorial : L ⊗[ℤ] L) * u k = u 1 ^ k := fact_mul u (by simp only [u, bL_zero]; rfl) fun i j ↦ by
    simp only [u, Algebra.TensorProduct.tmul_mul_tmul, one_mul, bL_mul]
    rw [← nsmul_eq_mul, ← nsmul_eq_mul, smul_tmul']
  have hv : ∀ k, (k.factorial : L ⊗[ℤ] L) * v k = v 1 ^ k := fact_mul v (by simp only [v, bL_zero]; rfl) fun i j ↦ by
    simp only [v, Algebra.TensorProduct.tmul_mul_tmul, one_mul, bL_mul]
    rw [← nsmul_eq_mul, ← nsmul_eq_mul, tmul_smul]
  let ψ : L ⊗[ℤ] L →ₐ[ℤ] B := Algebra.TensorProduct.lift
    (liftL (fun k ↦ γ k a) (H.zero a ha) fun i j ↦ H.mul_dpow i j a ha)
    (liftL (fun k ↦ γ k b) (H.zero b hb) fun i j ↦ H.mul_dpow i j b hb) fun _ _ ↦ Commute.all _ _
  have ψu : ∀ k, ψ (u k) = γ k a := fun k ↦ by simp [ψ, u, liftL_bL]
  have ψv : ∀ k, ψ (v k) = γ k b := fun k ↦ by simp [ψ, v, liftL_bL]
  let W : Ideal (L ⊗[ℤ] L) :=
    { carrier := {z | ψ z ∈ J ∧ ∀ k : ℕ, ∃ w, (k.factorial : L ⊗[ℤ] L) * w = z ^ k ∧ ψ w = γ k (ψ z)}
      zero_mem' := ⟨by simp, fun k ↦ by
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · exact ⟨1, by simp, by rw [map_one, map_zero, H.zero _ J.zero_mem]⟩
        · refine ⟨0, by simp [hk.ne'], ?_⟩
          have := H.mul k 0 0 J.zero_mem
          rw [mul_zero, zero_pow hk.ne', zero_mul] at this
          rw [map_zero, this]⟩
      add_mem' := fun {x y} hx hy ↦ ⟨by rw [map_add]; exact J.add_mem hx.1 hy.1, fun k ↦ by
        choose w hw hw' using hx.2
        choose w₁ hw₁ hw₁' using hy.2
        refine ⟨_, fact_sum x y w w₁ hw hw₁ k, ?_⟩
        rw [map_add, H.add k _ hx.1 _ hy.1, map_sum]
        simp only [map_mul, hw', hw₁']⟩
      smul_mem' := fun c x hx ↦ ⟨by rw [smul_eq_mul, map_mul]; exact J.mul_mem_left _ hx.1, fun k ↦ by
        obtain ⟨w, hw, hw'⟩ := hx.2 k
        refine ⟨c ^ k * w, by rw [smul_eq_mul, mul_pow, ← hw]; ring, ?_⟩
        rw [smul_eq_mul, map_mul, map_mul, H.mul _ _ _ hx.1, hw', map_pow]⟩ }
  have uW : ∀ i, i ≠ 0 → u i ∈ W := fun i hi ↦ ⟨by rw [ψu]; exact H.mem i hi a ha, fun k ↦
    ⟨_, eq_ub cancel _ u hu k hi, by rw [map_mul, map_natCast, ψu, ψu, ka k i hi]⟩⟩
  have vW : ∀ i, i ≠ 0 → v i ∈ W := fun i hi ↦ ⟨by rw [ψv]; exact H.mem i hi b hb, fun k ↦
    ⟨_, eq_ub cancel _ v hv k hi, by rw [map_mul, map_natCast, ψv, ψv, kb k i hi]⟩⟩
  let z : ℕ → L ⊗[ℤ] L := fun k ↦ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, u p.1 * v p.2
  have hz : ∀ k, (k.factorial : L ⊗[ℤ] L) * z k = (u 1 + v 1) ^ k := fact_sum _ _ u v hu hv
  have ψz : ∀ k, ψ (z k) = γ k (a + b) := fun k ↦ by
    rw [H.add k a ha b hb, map_sum]; simp only [map_mul, ψu, ψv]
  have zW : z n ∈ W := Ideal.sum_mem _ fun p hp ↦ by
    have hp' : p.1 + p.2 = n := by simpa using hp
    by_cases h : p.1 = 0
    · exact W.mul_mem_left _ (vW _ (by omega))
    · exact W.mul_mem_right _ (uW _ h)
  obtain ⟨w, hw, hw'⟩ := zW.2 m
  have e := cancel m.factorial_ne_zero (hw.trans (eq_ub cancel _ z hz m hn).symm)
  rw [← ψz n, ← hw', e, map_mul, map_natCast, ψz]

end Pre

theorem dp_of_pre' : ∀ (B : Type) [CommRing B] (J : Ideal B) (γ : ℕ → B → B) (s : Set B), IsPreDP J γ → J = Ideal.span s → (∀ x ∈ s, ∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x) → ∃ δ : DividedPowers J, δ.dpow = γ := by
  intro B _ J γ s H hs h
  have key : ∀ x ∈ J, ∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x := by
    subst hs
    have smul : ∀ c, ∀ x ∈ Ideal.span s, (∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x) →
        ∀ m n : ℕ, n ≠ 0 → γ m (γ n (c * x)) = (m.uniformBell n : B) * γ (m * n) (c * x) := by
      intro c x hx ih m n hn
      rw [H.mul n c x hx, H.mul m _ _ (H.mem n hn x hx), ih m n hn, H.mul _ c x hx, ← pow_mul, mul_comm n m]
      ring
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero =>
      intro m n hn
      have z : ∀ k, k ≠ 0 → γ k 0 = 0 := fun k hk ↦ by
        have := H.mul k 0 0 (Ideal.zero_mem _)
        rwa [mul_zero, zero_pow hk, zero_mul] at this
      rw [z n hn]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [Nat.uniformBell_zero_left]
      · rw [z m hm.ne', z _ (Nat.mul_ne_zero hm.ne' hn), mul_zero]
    | add x y hx hy ihx ihy => exact Pre.comp_add H hx hy ihx ihy
    | smul c x hx ih => exact smul c x hx ih
  exact ⟨{ dpow := γ
           dpow_null := fun hx ↦ H.null _ _ hx
           dpow_zero := fun hx ↦ H.zero _ hx
           dpow_one := fun hx ↦ H.one _ hx
           dpow_mem := fun hn hx ↦ H.mem _ hn _ hx
           dpow_add := fun hx hy ↦ H.add _ _ hx _ hy
           dpow_mul := fun hx ↦ H.mul _ _ _ hx
           mul_dpow := fun hx ↦ H.mul_dpow _ _ _ hx
           dpow_comp := fun hn hx ↦ key _ hx _ _ hn }, rfl⟩

end FubiniStudyChowHeightFormula₂.Adr
end
end

section
set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

namespace Pre

open GlobalTheory.PDA.Model TensorProduct

theorem conv_mul {B : Type} [CommRing B] (c c' : ℕ → B) (h0 : c 0 = 1)
    (hm : ∀ m n, c m * c n = ((m + n).choose m : B) * c (m + n)) (h0' : c' 0 = 1)
    (hm' : ∀ m n, c' m * c' n = ((m + n).choose m : B) * c' (m + n)) (m n : ℕ) :
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, c p.1 * c' p.2) *
      (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, c p.1 * c' p.2) =
      ((m + n).choose m : B) * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (m + n), c p.1 * c' p.2 := by
  obtain ⟨iL, hiL⟩ : ∃ f : ↥L →ₐ[ℤ] ↥L ⊗[ℤ] ↥L, f = Algebra.TensorProduct.includeLeft (S := ℤ) :=
    ⟨_, rfl⟩
  obtain ⟨iR, hiR⟩ : ∃ f : ↥L →ₐ[ℤ] ↥L ⊗[ℤ] ↥L, f = Algebra.TensorProduct.includeRight :=
    ⟨_, rfl⟩
  have hu0 : iL (bL 0) = 1 := by rw [bL_zero, map_one]
  have hv0 : iR (bL 0) = 1 := by rw [bL_zero, map_one]
  have hum : ∀ a b : ℕ, iL (bL a) * iL (bL b) =
      ((a + b).choose a : ↥L ⊗[ℤ] ↥L) * iL (bL (a + b)) := by
    intro a b
    rw [← map_mul, bL_mul, map_mul, map_natCast]
  have hvm : ∀ a b : ℕ, iR (bL a) * iR (bL b) =
      ((a + b).choose a : ↥L ⊗[ℤ] ↥L) * iR (bL (a + b)) := by
    intro a b
    rw [← map_mul, bL_mul, map_mul, map_natCast]
  have fu := fact_mul _ hu0 hum
  have fv := fact_mul _ hv0 hvm
  have fs := fact_sum _ _ _ _ fu fv
  have key : ∀ a b : ℕ,
      (∑ p ∈ Finset.HasAntidiagonal.antidiagonal a, iL (bL p.1) * iR (bL p.2)) *
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal b, iL (bL p.1) * iR (bL p.2)) =
        ((a + b).choose a : ↥L ⊗[ℤ] ↥L) *
          ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (a + b), iL (bL p.1) * iR (bL p.2) := by
    intro a b
    have hC : (a + b).choose a * a.factorial * b.factorial = (a + b).factorial := by
      have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
      simpa using this
    apply cancel (n := a.factorial * b.factorial) (by positivity)
    calc _ = ((a.factorial : ↥L ⊗[ℤ] ↥L) *
              ∑ p ∈ Finset.HasAntidiagonal.antidiagonal a, iL (bL p.1) * iR (bL p.2)) *
            ((b.factorial : ↥L ⊗[ℤ] ↥L) *
              ∑ p ∈ Finset.HasAntidiagonal.antidiagonal b, iL (bL p.1) * iR (bL p.2)) := by
            push_cast
            ring
      _ = (((a + b).choose a * a.factorial * b.factorial : ℕ) : ↥L ⊗[ℤ] ↥L) *
            ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (a + b), iL (bL p.1) * iR (bL p.2) := by
            rw [fs a, fs b, ← pow_add, hC, fs (a + b)]
      _ = _ := by
            push_cast
            ring
  have := congrArg (Algebra.TensorProduct.productMap (liftL c h0 hm) (liftL c' h0' hm')) (key m n)
  subst hiL hiR
  simpa [map_sum, map_mul, map_natCast, liftL_bL] using this

end Pre

theorem dp_split' : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (P : Type) [CommRing P] [Algebra B P] (ε : P →ₐ[B] B) (𝔞 : Ideal P) (η : DividedPowers 𝔞), (∀ p, p ∈ 𝔞 ↔ ε p = 0) → ∃ θ : DividedPowers (J.map (algebraMap B P) ⊔ 𝔞), IsDPMorphism δ θ (algebraMap B P) ∧ ∀ n, ∀ p ∈ 𝔞, θ.dpow n p = η.dpow n p := by
  intro B _ J δ P _ _ ε 𝔞 η hε
  classical
  have hεf : ∀ b : B, ε (algebraMap B P b) = b := fun b => ε.commutes b
  have hεa : ∀ a ∈ 𝔞, ε a = 0 := fun a ha => (hε a).1 ha
  have hK : ∀ p : P, p ∈ J.map (algebraMap B P) ⊔ 𝔞 ↔ ε p ∈ J := by
    intro p
    constructor
    · intro hp
      have hle : J.map (algebraMap B P) ⊔ 𝔞 ≤ J.comap ε := by
        refine sup_le ?_ ?_
        · rw [Ideal.map_le_iff_le_comap]
          intro b hb
          rw [Ideal.mem_comap, Ideal.mem_comap]
          simpa [hεf b] using hb
        · intro a ha
          rw [Ideal.mem_comap, hεa a ha]
          exact J.zero_mem
      have := hle hp
      rwa [Ideal.mem_comap] at this
    · intro hp
      rw [show p = algebraMap B P (ε p) + (p - algebraMap B P (ε p)) by ring]
      refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hp)) (Ideal.mem_sup_right ?_)
      rw [hε, map_sub, hεf, sub_self]
  have hdec : ∀ p ∈ J.map (algebraMap B P) ⊔ 𝔞, ∃ b ∈ J, ∃ a ∈ 𝔞, p = algebraMap B P b + a := by
    intro p hp
    refine ⟨ε p, (hK p).1 hp, p - algebraMap B P (ε p), ?_, by ring⟩
    rw [hε, map_sub, hεf, sub_self]
  have hfK : ∀ b ∈ J, algebraMap B P b ∈ J.map (algebraMap B P) ⊔ 𝔞 :=
    fun b hb => Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hb)
  have haK : ∀ a ∈ 𝔞, a ∈ J.map (algebraMap B P) ⊔ 𝔞 := fun a ha => Ideal.mem_sup_right ha
  obtain ⟨γ, hγ⟩ : ∃ γ : ℕ → P → P, ∀ n p, γ n p = if ε p ∈ J then
      ∑ k ∈ Finset.HasAntidiagonal.antidiagonal n,
        algebraMap B P (δ.dpow k.1 (ε p)) * η.dpow k.2 (p - algebraMap B P (ε p)) else 0 :=
    ⟨_, fun _ _ => rfl⟩
  have hS : ∀ n, ∀ b ∈ J, ∀ a ∈ 𝔞, γ n (algebraMap B P b + a) =
      ∑ k ∈ Finset.HasAntidiagonal.antidiagonal n, algebraMap B P (δ.dpow k.1 b) * η.dpow k.2 a := by
    intro n b hb a ha
    have h1 : ε (algebraMap B P b + a) = b := by rw [map_add, hεf, hεa a ha, add_zero]
    rw [hγ, h1, if_pos hb, add_sub_cancel_left]
  have hB : ∀ n, ∀ b ∈ J, γ n (algebraMap B P b) = algebraMap B P (δ.dpow n b) := by
    intro n b hb
    have h := hS n b hb 0 𝔞.zero_mem
    rw [add_zero] at h
    rw [h, Finset.sum_eq_single (n, 0)]
    · rw [η.dpow_zero 𝔞.zero_mem, mul_one]
    · intro k hk hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hk
      have h2 : k.2 ≠ 0 := fun h2 => hne (Prod.ext (by omega) h2)
      rw [η.dpow_eval_zero h2, mul_zero]
    · intro h
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp)) h
  have hA : ∀ n, ∀ a ∈ 𝔞, γ n a = η.dpow n a := by
    intro n a ha
    have h := hS n 0 J.zero_mem a ha
    rw [map_zero, zero_add] at h
    rw [h, Finset.sum_eq_single (0, n)]
    · rw [δ.dpow_zero J.zero_mem, map_one, one_mul]
    · intro k hk hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hk
      have h1 : k.1 ≠ 0 := fun h1 => hne (Prod.ext h1 (by omega))
      rw [δ.dpow_eval_zero h1, map_zero, zero_mul]
    · intro h
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp)) h
  have hc0 : ∀ b ∈ J, algebraMap B P (δ.dpow 0 b) = 1 := fun b hb => by
    rw [δ.dpow_zero hb, map_one]
  have hcm : ∀ b ∈ J, ∀ m n, algebraMap B P (δ.dpow m b) * algebraMap B P (δ.dpow n b) =
      ((m + n).choose m : P) * algebraMap B P (δ.dpow (m + n) b) := fun b hb m n => by
    rw [← map_mul, δ.mul_dpow hb, map_mul, map_natCast]
  have hmd : ∀ p ∈ J.map (algebraMap B P) ⊔ 𝔞, ∀ m n,
      γ m p * γ n p = ((m + n).choose m : P) * γ (m + n) p := by
    intro p hp m n
    obtain ⟨b, hb, a, ha, rfl⟩ := hdec p hp
    rw [hS m b hb a ha, hS n b hb a ha, hS (m + n) b hb a ha]
    exact Pre.conv_mul (fun i => algebraMap B P (δ.dpow i b)) (fun j => η.dpow j a)
      (hc0 b hb) (hcm b hb) (η.dpow_zero ha) (fun m n => η.mul_dpow ha) m n
  have hzero : ∀ p ∈ J.map (algebraMap B P) ⊔ 𝔞, γ 0 p = 1 := by
    intro p hp
    obtain ⟨b, hb, a, ha, rfl⟩ := hdec p hp
    rw [hS 0 b hb a ha]
    simp [δ.dpow_zero hb, η.dpow_zero ha]
  have hone : ∀ p ∈ J.map (algebraMap B P) ⊔ 𝔞, γ 1 p = p := by
    intro p hp
    obtain ⟨b, hb, a, ha, rfl⟩ := hdec p hp
    rw [hS 1 b hb a ha, Finset.Nat.sum_antidiagonal_succ]
    simp [δ.dpow_zero hb, η.dpow_zero ha, δ.dpow_one hb, η.dpow_one ha, add_comm]
  have hmem : ∀ n, n ≠ 0 → ∀ p ∈ J.map (algebraMap B P) ⊔ 𝔞, γ n p ∈ J.map (algebraMap B P) ⊔ 𝔞 := by
    intro n hn p hp
    obtain ⟨b, hb, a, ha, rfl⟩ := hdec p hp
    rw [hS n b hb a ha]
    refine Ideal.sum_mem _ fun k hk => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hk
    by_cases h1 : k.1 = 0
    · exact Ideal.mul_mem_left _ _ (haK _ (η.dpow_mem (by omega) ha))
    · exact Ideal.mul_mem_right _ _ (hfK _ (δ.dpow_mem h1 hb))
  have hadd : ∀ n, ∀ p ∈ J.map (algebraMap B P) ⊔ 𝔞, ∀ q ∈ J.map (algebraMap B P) ⊔ 𝔞,
      γ n (p + q) = ∑ k ∈ Finset.HasAntidiagonal.antidiagonal n, γ k.1 p * γ k.2 q := by
    intro n p hp q hq
    obtain ⟨b, hb, a, ha, rfl⟩ := hdec p hp
    obtain ⟨b', hb', a', ha', rfl⟩ := hdec q hq
    have e : algebraMap B P b + a + (algebraMap B P b' + a') =
        algebraMap B P (b + b') + (a + a') := by
      rw [map_add]
      ring
    have ser : ∀ (c : B) (d : P) (k : ℕ),
        ∑ i ∈ Finset.HasAntidiagonal.antidiagonal k, algebraMap B P (δ.dpow i.1 c) * η.dpow i.2 d =
          PowerSeries.coeff k ((PowerSeries.mk fun i => algebraMap B P (δ.dpow i c)) *
            PowerSeries.mk fun j => η.dpow j d) := by
      intro c d k
      rw [PowerSeries.coeff_mul]
      simp only [PowerSeries.coeff_mk]
    have hX : (PowerSeries.mk fun i => algebraMap B P (δ.dpow i (b + b'))) =
        (PowerSeries.mk fun i => algebraMap B P (δ.dpow i b)) *
          PowerSeries.mk fun i => algebraMap B P (δ.dpow i b') := by
      ext k
      rw [PowerSeries.coeff_mul]
      simp only [PowerSeries.coeff_mk]
      rw [δ.dpow_add hb hb', map_sum]
      simp only [map_mul]
    have hY : (PowerSeries.mk fun j => η.dpow j (a + a')) =
        (PowerSeries.mk fun j => η.dpow j a) * PowerSeries.mk fun j => η.dpow j a' :=
      DividedPowers.exp_add' _ (fun _ => η.dpow_add ha ha')
    rw [e, hS n _ (J.add_mem hb hb') _ (𝔞.add_mem ha ha'), ser, hX, hY, mul_mul_mul_comm,
      PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hS k.1 b hb a ha, hS k.2 b' hb' a' ha', ser, ser]
  have hfact : ∀ p ∈ J.map (algebraMap B P) ⊔ 𝔞, ∀ j : ℕ, p ^ j = (j.factorial : P) * γ j p := by
    intro p hp j
    rw [Pre.fact_mul (fun k => γ k p) (hzero p hp) (hmd p hp) j, hone p hp]
  have hmul : ∀ (n : ℕ) (c x : P), x ∈ J.map (algebraMap B P) ⊔ 𝔞 → γ n (c * x) = c ^ n * γ n x := by
    intro n c x hx
    have ha' : c - algebraMap B P (ε c) ∈ 𝔞 := by rw [hε, map_sub, hεf, sub_self]
    have hfs : ∀ i, γ i (algebraMap B P (ε c) * x) = algebraMap B P (ε c) ^ i * γ i x := by
      intro i
      obtain ⟨b, hb, a, ha, hxe⟩ := hdec x hx
      rw [hxe, show algebraMap B P (ε c) * (algebraMap B P b + a) =
          algebraMap B P (ε c * b) + algebraMap B P (ε c) * a by rw [map_mul]; ring,
        hS i _ (J.mul_mem_left _ hb) _ (𝔞.mul_mem_left _ ha), hS i b hb a ha, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hk
      rw [δ.dpow_mul hb, η.dpow_mul ha, map_mul, map_pow, ← hk, pow_add]
      ring
    have hax : ∀ j, γ j ((c - algebraMap B P (ε c)) * x) =
        η.dpow j (c - algebraMap B P (ε c)) * x ^ j := by
      intro j
      rw [hA j _ (𝔞.mul_mem_right x ha'), η.dpow_mul_right ha']
    have hcx : c * x = algebraMap B P (ε c) * x + (c - algebraMap B P (ε c)) * x := by ring
    rw [hcx, hadd n _ (Ideal.mul_mem_left _ _ hx) _ (haK _ (𝔞.mul_mem_right x ha'))]
    conv_rhs => rw [show c = algebraMap B P (ε c) + (c - algebraMap B P (ε c)) by ring]
    rw [(Commute.all _ _).add_pow', Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hk
    have hm := hmd x hx k.1 k.2
    rw [hk] at hm
    rw [hfs, hax, hfact x hx k.2, ← η.factorial_mul_dpow_eq_pow ha', nsmul_eq_mul]
    calc algebraMap B P (ε c) ^ k.1 * γ k.1 x *
          (η.dpow k.2 (c - algebraMap B P (ε c)) * ((k.2.factorial : P) * γ k.2 x))
        = algebraMap B P (ε c) ^ k.1 * η.dpow k.2 (c - algebraMap B P (ε c)) *
            (k.2.factorial : P) * (γ k.1 x * γ k.2 x) := by ring
      _ = _ := by
        rw [hm]
        ring
  have hpre : IsPreDP (J.map (algebraMap B P) ⊔ 𝔞) γ :=
    ⟨fun n x hx => by rw [hγ, if_neg (fun h => hx ((hK x).2 h))], hzero, hone, hmem, hadd, hmul,
      fun m n x hx => hmd x hx m n⟩
  have hcomp : ∀ m n, n ≠ 0 → ∀ p ∈ J.map (algebraMap B P) ⊔ 𝔞,
      γ m (γ n p) = (m.uniformBell n : P) * γ (m * n) p := by
    intro m n hn p hp
    obtain ⟨b, hb, a, ha, rfl⟩ := hdec p hp
    refine Pre.comp_add hpre (hfK b hb) (haK a ha) ?_ ?_ m n hn
    · intro m n hn
      rw [hB n b hb, hB m _ (δ.dpow_mem hn hb), hB (m * n) b hb, δ.dpow_comp hn hb, map_mul,
        map_natCast]
    · intro m n hn
      rw [hA n a ha, hA m _ (η.dpow_mem hn ha), hA (m * n) a ha, η.dpow_comp hn ha]
  obtain ⟨θ, hθ⟩ : ∃ θ : DividedPowers (J.map (algebraMap B P) ⊔ 𝔞), θ.dpow = γ :=
    ⟨{ dpow := γ
       dpow_null := fun {n x} hx => hpre.null n x hx
       dpow_zero := fun {x} hx => hzero x hx
       dpow_one := fun {x} hx => hone x hx
       dpow_mem := fun {n x} hn hx => hmem n hn x hx
       dpow_add := fun {n x y} hx hy => hadd n x hx y hy
       dpow_mul := fun {n a x} hx => hmul n a x hx
       mul_dpow := fun {m n x} hx => hmd x hx m n
       dpow_comp := fun {m n x} hn hx => hcomp m n hn x hx }, rfl⟩
  refine ⟨θ, ⟨le_sup_left, fun {n} b hb => ?_⟩, fun n p hp => ?_⟩
  · rw [hθ, hB n b hb]
  · rw [hθ, hA n p hp]

end FubiniStudyChowHeightFormula₂.Adr
end
end

section
set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

theorem dp_of_pre : ∀ (B : Type) [CommRing B] (J : Ideal B) (γ : ℕ → B → B) (s : Set B), IsPreDP J γ → J = Ideal.span s → (∀ x ∈ s, ∀ m n : ℕ, n ≠ 0 → γ m (γ n x) = (m.uniformBell n : B) * γ (m * n) x) → ∃ δ : DividedPowers J, δ.dpow = γ := dp_of_pre'

theorem dp_split : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (P : Type) [CommRing P] [Algebra B P] (ε : P →ₐ[B] B) (𝔞 : Ideal P) (η : DividedPowers 𝔞), (∀ p, p ∈ 𝔞 ↔ ε p = 0) → ∃ θ : DividedPowers (J.map (algebraMap B P) ⊔ 𝔞), IsDPMorphism δ θ (algebraMap B P) ∧ ∀ n, ∀ p ∈ 𝔞, θ.dpow n p = η.dpow n p := dp_split'

end FubiniStudyChowHeightFormula₂.Adr
end
end

section
set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

open PowerSeries Finset

variable {B : Type} [CommRing B]

def ser (g : ℕ → B) (a : B) : B⟦X⟧ := PowerSeries.mk fun n ↦ a ^ n * g n

theorem ser_zero {g : ℕ → B} (h0 : g 0 = 1) : ser g 0 = 1 := by
  ext n
  rcases n with _ | n <;> simp [ser, h0, coeff_one]

theorem ser_add {g : ℕ → B} (hmul : ∀ m n, g m * g n = ((m + n).choose m : B) * g (m + n)) (a b : B) :
    ser g (a + b) = ser g a * ser g b := by
  ext n
  simp only [ser, coeff_mul, coeff_mk, (Commute.all a b).add_pow', Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have e := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have := hmul p.1 p.2
  rw [e] at this
  rw [nsmul_eq_mul]
  linear_combination (-(a ^ p.1 * b ^ p.2)) * this

theorem ser_mul (g : ℕ → B) (a b : B) : ser g (a * b) = rescale a (ser g b) := by
  ext n
  simp only [ser, coeff_rescale, coeff_mk, mul_pow, mul_assoc]

def IsExp (f : B⟦X⟧) : Prop := ∀ m n, coeff m f * coeff n f = ((m + n).choose m : B) * coeff (m + n) f

theorem IsExp.mul {f g : B⟦X⟧} (hf : IsExp f) (hg : IsExp g) : IsExp (f * g) := by
  intro m n
  simp only [coeff_mul]
  have e : ((m + n).choose m : B) * ∑ p ∈ HasAntidiagonal.antidiagonal (m + n), coeff p.1 f * coeff p.2 g =
      ∑ i ∈ HasAntidiagonal.antidiagonal m, ∑ p ∈ HasAntidiagonal.antidiagonal (m + n),
        (p.1.choose i.1 : B) * (p.2.choose i.2 : B) * (coeff p.1 f * coeff p.2 g) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hp, Nat.add_choose_eq, ← Finset.sum_mul]
    push_cast
    rfl
  rw [e, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.HasAntidiagonal.mem_antidiagonal.1 hi
  rw [Finset.mul_sum]
  refine Finset.sum_of_injOn (fun k : ℕ × ℕ ↦ (i.1 + k.1, i.2 + k.2)) ?_ ?_ ?_ ?_
  · intro k _ l _ h
    simp only [Prod.mk.injEq, add_right_inj] at h
    exact Prod.ext h.1 h.2
  · intro k hk
    have := Finset.HasAntidiagonal.mem_antidiagonal.1 hk
    exact Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp only; omega)
  · intro p hp hn
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h1 : p.1 < i.1
    · simp [Nat.choose_eq_zero_of_lt h1]
    by_cases h2 : p.2 < i.2
    · simp [Nat.choose_eq_zero_of_lt h2]
    refine absurd ⟨(p.1 - i.1, p.2 - i.2), Finset.mem_coe.2 (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp only; omega)), ?_⟩ hn
    exact Prod.ext (by simp only; omega) (by simp only; omega)
  · intro k _
    have a := hf i.1 k.1
    have b := hg i.2 k.2
    simp only
    linear_combination (coeff i.2 g * coeff k.2 g) * a + (((i.1 + k.1).choose i.1 : B) * coeff (i.1 + k.1) f) * b

theorem pre_of_gens (B ι : Type) [CommRing B] (x : ι → B) (g : ι → ℕ → B) (h0 : ∀ i, g i 0 = 1)
    (h1 : ∀ i, g i 1 = x i) (hm : ∀ i n, n ≠ 0 → g i n ∈ Ideal.span (Set.range x))
    (hmul : ∀ i m n, g i m * g i n = ((m + n).choose m : B) * g i (m + n))
    (hrel : ∀ c : ι →₀ B, (c.sum fun i a ↦ a * x i) = 0 →
      (c.prod fun i a ↦ PowerSeries.mk fun n ↦ a ^ n * g i n) = 1) :
    ∃ γ : ℕ → B → B, IsPreDP (Ideal.span (Set.range x)) γ ∧ ∀ i n, γ n (x i) = g i n := by
  classical
  let Φ : (ι →₀ B) → B⟦X⟧ := fun c ↦ c.prod fun i a ↦ ser (g i) a
  let l : (ι →₀ B) →ₗ[B] B := Finsupp.linearCombination B x
  have hl : ∀ c, l c = c.sum fun i a ↦ a * x i := fun c ↦ rfl
  have Φadd : ∀ c c', Φ (c + c') = Φ c * Φ c' := fun c c' ↦
    Finsupp.prod_add_index' (fun i ↦ ser_zero (h0 i)) fun i ↦ ser_add (hmul i)
  have Φ0 : Φ 0 = 1 := Finsupp.prod_zero_index
  have Φs : ∀ i a, Φ (Finsupp.single i a) = ser (g i) a := fun i a ↦
    Finsupp.prod_single_index (ser_zero (h0 i))
  have Φwd : ∀ c c', l c = l c' → Φ c = Φ c' := fun c c' h ↦ by
    have : Φ (c - c') = 1 := hrel _ (by rw [← hl, map_sub, h, sub_self])
    rw [← sub_add_cancel c c', Φadd, this, one_mul]
  have hJ : ∀ y, y ∈ Ideal.span (Set.range x) ↔ ∃ c, l c = y := fun y ↦
    Finsupp.mem_span_range_iff_exists_finsupp
  have Φsm : ∀ a c, Φ (a • c) = rescale a (Φ c) := fun a c ↦ by
    induction c using Finsupp.induction_linear with
    | zero => rw [smul_zero, Φ0, map_one]
    | add c c' h h' => rw [smul_add, Φadd, Φadd, h, h', map_mul]
    | single i b => rw [Finsupp.smul_single, Φs, Φs, smul_eq_mul, ser_mul]
  have key : ∀ c, coeff 0 (Φ c) = 1 ∧ coeff 1 (Φ c) = l c ∧
      (∀ n, n ≠ 0 → coeff n (Φ c) ∈ Ideal.span (Set.range x)) ∧ IsExp (Φ c) := fun c ↦ by
    induction c using Finsupp.induction_linear with
    | zero =>
      rw [Φ0]
      refine ⟨by simp, by simp, fun n hn ↦ by simp [coeff_one, hn], fun m n ↦ ?_⟩
      rcases m with _ | m <;> rcases n with _ | n <;> simp [coeff_one]
    | add c c' h h' =>
      rw [Φadd]
      refine ⟨by rw [coeff_mul]; simp [h.1, h'.1, -coeff_zero_eq_constantCoeff], ?_, fun n hn ↦ ?_,
        h.2.2.2.mul h'.2.2.2⟩
      · rw [coeff_mul, Finset.Nat.antidiagonal_succ]
        simp [h.1, h'.1, h.2.1, h'.2.1, -coeff_zero_eq_constantCoeff, add_comm]
      · rw [coeff_mul]
        refine Ideal.sum_mem _ fun p hp ↦ ?_
        have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
        by_cases h1 : p.1 = 0
        · exact Ideal.mul_mem_left _ _ (h'.2.2.1 _ (by omega))
        · exact Ideal.mul_mem_right _ _ (h.2.2.1 _ h1)
    | single i b =>
      rw [Φs]
      refine ⟨by simp [ser, h0], by simp [ser, h1, l], fun n hn ↦ ?_, fun m n ↦ ?_⟩
      · rw [ser, coeff_mk]; exact Ideal.mul_mem_left _ _ (hm i n hn)
      · simp only [ser, coeff_mk, pow_add]
        linear_combination (b ^ m * b ^ n) * hmul i m n
  let γ : ℕ → B → B := fun n y ↦ if h : ∃ c, l c = y then coeff n (Φ h.choose) else 0
  have hγ : ∀ n c, γ n (l c) = coeff n (Φ c) := fun n c ↦ by
    have h : ∃ c', l c' = l c := ⟨c, rfl⟩
    simp only [γ, dif_pos h, Φwd _ _ h.choose_spec]
  refine ⟨γ, ⟨fun n y hy ↦ dif_neg fun h ↦ hy ((hJ y).2 h), ?_, ?_, ?_, ?_, ?_, ?_⟩, fun i n ↦ ?_⟩
  · intro y hy
    obtain ⟨c, rfl⟩ := (hJ y).1 hy
    rw [hγ, (key c).1]
  · intro y hy
    obtain ⟨c, rfl⟩ := (hJ y).1 hy
    rw [hγ, (key c).2.1]
  · intro n hn y hy
    obtain ⟨c, rfl⟩ := (hJ y).1 hy
    rw [hγ]; exact (key c).2.2.1 n hn
  · intro n y hy z hz
    obtain ⟨c, rfl⟩ := (hJ y).1 hy
    obtain ⟨c', rfl⟩ := (hJ z).1 hz
    simp only [← map_add, hγ, Φadd, coeff_mul]
  · intro n a y hy
    obtain ⟨c, rfl⟩ := (hJ y).1 hy
    rw [← smul_eq_mul, ← map_smul, hγ, hγ, Φsm, coeff_rescale]
  · intro m n y hy
    obtain ⟨c, rfl⟩ := (hJ y).1 hy
    simp only [hγ]
    exact (key c).2.2.2 m n
  · have : x i = l (Finsupp.single i 1) := by simp [l]
    rw [this, hγ, Φs]; simp [ser]

end FubiniStudyChowHeightFormula₂.Adr
end
end

section
set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

variable {B : Type} [CommRing B]

theorem e_succ_mem_aug (Q : PDPoly B) (n : ℕ) : Q.e (n + 1) ∈ Q.aug := Ideal.subset_span ⟨n, rfl⟩

def liftAlg (Q : PDPoly B) {C : Type} [CommRing C] [Algebra B C] (c : ℕ → C) (h0 : c 0 = 1)
    (hm : ∀ m n, c m * c n = ((m + n).choose m : C) * c (m + n)) : Q.P →ₐ[B] C :=
  AlgHom.ofLinearMap (Q.e.constr B c) (by rw [← Q.e_zero, Module.Basis.constr_basis, h0]) (by
    intro x y
    have key : (LinearMap.mul B Q.P).compr₂ (Q.e.constr B c) =
        (LinearMap.mul B C).compl₁₂ (Q.e.constr B c) (Q.e.constr B c) := by
      refine Q.e.ext fun m ↦ Q.e.ext fun n ↦ ?_
      simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₁₂_apply,
        Module.Basis.constr_basis, Q.e_mul]
      rw [← nsmul_eq_mul, LinearMap.map_smul_of_tower, Module.Basis.constr_basis, nsmul_eq_mul, hm]
    exact congrArg (fun g ↦ g x y) key)

theorem liftAlg_e (Q : PDPoly B) {C : Type} [CommRing C] [Algebra B C] (c : ℕ → C) (h0 : c 0 = 1)
    (hm : ∀ m n, c m * c n = ((m + n).choose m : C) * c (m + n)) (n : ℕ) :
    liftAlg Q c h0 hm (Q.e n) = c n :=
  Q.e.constr_basis B c n

theorem exists_lift_and_aug : ∀ (B : Type) [CommRing B] (Q : PDPoly B),
    (∀ (C : Type) [CommRing C] (f : B →+* C) (c : ℕ → C), c 0 = 1 →
      (∀ m n, c m * c n = ((m + n).choose m : C) * c (m + n)) →
      ∃ F : Q.P →+* C, (∀ b, F (algebraMap B Q.P b) = f b) ∧ ∀ n, F (Q.e n) = c n) ∧
    ∃ ε : Q.P →ₐ[B] B, ∀ p, p ∈ Q.aug ↔ ε p = 0 := by
  intro B _ Q
  refine ⟨fun C _ f c h0 hm ↦ ?_, ?_⟩
  · letI := f.toAlgebra
    exact ⟨(liftAlg Q c h0 hm).toRingHom, fun b ↦ (liftAlg Q c h0 hm).commutes b,
      fun n ↦ liftAlg_e Q c h0 hm n⟩
  · let d : ℕ → B := fun n ↦ if n = 0 then 1 else 0
    have h0 : d 0 = 1 := by simp [d]
    have hm : ∀ m n, d m * d n = ((m + n).choose m : B) * d (m + n) := by
      intro m n
      by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [d, hm, hn]
    let ε := liftAlg Q d h0 hm
    have hε : ∀ n, ε (Q.e n) = d n := liftAlg_e Q d h0 hm
    have hmem : ∀ p, p - algebraMap B Q.P (ε p) ∈ Q.aug := by
      intro p
      have hp : p ∈ Submodule.span B (Set.range Q.e) := by rw [Q.e.span_eq]; trivial
      induction hp using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨n, rfl⟩ := hx
        rw [hε]
        rcases n with _ | n
        · simp [d, Q.e_zero]
        · simpa [d] using e_succ_mem_aug Q n
      | zero => simp
      | add x y _ _ hx hy =>
        have : x + y - algebraMap B Q.P (ε (x + y)) =
            (x - algebraMap B Q.P (ε x)) + (y - algebraMap B Q.P (ε y)) := by
          rw [map_add, map_add]; abel
        rw [this]; exact add_mem hx hy
      | smul b x _ hx =>
        have : b • x - algebraMap B Q.P (ε (b • x)) = algebraMap B Q.P b * (x - algebraMap B Q.P (ε x)) := by
          rw [map_smul, smul_eq_mul, map_mul, Algebra.smul_def, mul_sub]
        rw [this]; exact Q.aug.mul_mem_left _ hx
    refine ⟨ε, fun p ↦ ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩⟩
    · have hle : Q.aug ≤ RingHom.ker ε := by
        refine Ideal.span_le.2 ?_
        rintro _ ⟨n, rfl⟩
        simp [RingHom.mem_ker, hε, d]
      exact RingHom.mem_ker.1 (hle hp)
    · have := hmem p
      rwa [hp, map_zero, sub_zero] at this

end FubiniStudyChowHeightFormula₂.Adr
end
end

section
set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

open PowerSeries

variable {B : Type} [CommRing B]

theorem e_pow (Q : PDPoly B) (l n : ℕ) :
    ∃ M : ℕ, M * l.factorial ^ n = (n * l).factorial ∧ Q.e l ^ n = (M : Q.P) * Q.e (n * l) := by
  induction n with
  | zero => exact ⟨1, by simp, by simp [Q.e_zero]⟩
  | succ n ih =>
    obtain ⟨M, h1, h2⟩ := ih
    refine ⟨M * (n * l + l).choose (n * l), ?_, ?_⟩
    · have := Nat.add_choose_mul_factorial_mul_factorial (n * l) l
      rw [← Nat.choose_symm_add] at this
      rw [Nat.succ_mul, ← this, ← h1]; ring
    · rw [pow_succ, h2, mul_assoc, Q.e_mul, Nat.succ_mul]; push_cast; ring

theorem choose_fac (a b : ℕ) : (a + b).choose a * a.factorial * b.factorial = (a + b).factorial := by
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
  rwa [Nat.add_sub_cancel_left] at h

theorem num1 (m n : ℕ) {K : ℕ} (hK : K ≠ 0) :
    m.uniformBell K * n.uniformBell K * (m * K + n * K).choose (m * K) =
      (m + n).choose m * (m + n).uniformBell K := by
  have hm := Nat.uniformBell_mul_eq m hK
  have hn := Nat.uniformBell_mul_eq n hK
  have hmn := Nat.uniformBell_mul_eq (m + n) hK
  have c1 := choose_fac (m * K) (n * K)
  have c2 := choose_fac m n
  have hpos : 0 < K.factorial ^ (m + n) * m.factorial * n.factorial := by positivity
  have e1 : m.uniformBell K * n.uniformBell K * (m * K + n * K).choose (m * K) *
      (K.factorial ^ (m + n) * m.factorial * n.factorial) = (m * K + n * K).factorial := by
    rw [← c1, ← hm, ← hn]
    ring
  have e2 : (m + n).choose m * (m + n).uniformBell K *
      (K.factorial ^ (m + n) * m.factorial * n.factorial) = (m * K + n * K).factorial := by
    rw [← add_mul, ← hmn, ← c2]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos (e1.trans e2.symm)

theorem num2 (n l M : ℕ) {K : ℕ} (hK : K ≠ 0) (hM : M * l.factorial ^ n = (n * l).factorial) :
    M * n.uniformBell K * (n * l + n * K).choose (n * l) = (l + K).choose l ^ n * n.uniformBell (l + K) := by
  have h1 := Nat.uniformBell_mul_eq n hK
  have h3 := Nat.uniformBell_mul_eq n (show l + K ≠ 0 by omega)
  have h4 := choose_fac (n * l) (n * K)
  have h5 := choose_fac l K
  have hpos : 0 < l.factorial ^ n * K.factorial ^ n * n.factorial := by positivity
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc _ = (n * l + n * K).choose (n * l) * (M * l.factorial ^ n) *
        (n.uniformBell K * K.factorial ^ n * n.factorial) := by ring
    _ = (n * (l + K)).factorial := by rw [h1, hM, h4, mul_add]
    _ = n.uniformBell (l + K) * ((l + K).choose l * l.factorial * K.factorial) ^ n * n.factorial := by
        rw [h5, h3]
    _ = _ := by ring

def gb (Q : PDPoly B) (K n : ℕ) : Q.P := (n.uniformBell K : Q.P) * Q.e (n * K)

theorem gb_zero (Q : PDPoly B) (K : ℕ) : gb Q K 0 = 1 := by simp [gb, Nat.uniformBell_zero_left, Q.e_zero]

theorem gb_mul (Q : PDPoly B) {K : ℕ} (hK : K ≠ 0) (m n : ℕ) :
    gb Q K m * gb Q K n = ((m + n).choose m : Q.P) * gb Q K (m + n) := by
  unfold gb
  have h := num1 m n hK
  calc ((m.uniformBell K : Q.P) * Q.e (m * K)) * ((n.uniformBell K : Q.P) * Q.e (n * K))
      = ((m.uniformBell K * n.uniformBell K * (m * K + n * K).choose (m * K) : ℕ) : Q.P) *
          Q.e (m * K + n * K) := by
        rw [mul_mul_mul_comm, Q.e_mul]
        push_cast
        ring
    _ = _ := by
        rw [h, ← add_mul]
        push_cast
        ring

private theorem dividedPower_identities_D_and_e_eq_gb (Q : PDPoly B) : ∃ D : ℕ → Q.P → Q.P,
    (∀ x, D 0 x = 1) ∧
    (∀ n x y, D n (x + y) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, D p.1 x * D p.2 y) ∧
    (∀ m n x, D m x * D n x = ((m + n).choose m : Q.P) * D (m + n) x) ∧
    (∀ n (c : B) x, D n (c • x) = algebraMap B Q.P c ^ n * D n x) ∧
    (∀ n K, K ≠ 0 → D n (Q.e K) = gb Q K n) := by
  classical
  obtain ⟨F, hF⟩ : ∃ F : ℕ → B → PowerSeries Q.P, ∀ K b,
      F K b = PowerSeries.mk fun j => algebraMap B Q.P (b ^ j) * gb Q K j := ⟨_, fun _ _ => rfl⟩
  have F0 : ∀ K, F K 0 = 1 := by
    intro K
    ext j
    rw [hF, PowerSeries.coeff_mk, PowerSeries.coeff_one]
    rcases j with _ | j
    · simp [gb_zero]
    · simp
  have Fadd : ∀ K, K ≠ 0 → ∀ a b, F K (a + b) = F K a * F K b := by
    intro K hK a b
    ext n
    rw [PowerSeries.coeff_mul]
    simp only [hF, PowerSeries.coeff_mk]
    have hterm : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        algebraMap B Q.P (a ^ p.1) * gb Q K p.1 * (algebraMap B Q.P (b ^ p.2) * gb Q K p.2) =
          algebraMap B Q.P (a ^ p.1 * b ^ p.2 * (n.choose p.1 : B)) * gb Q K n := by
      intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rw [mul_mul_mul_comm, gb_mul Q hK, hp]
      simp only [map_mul, map_natCast]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← map_sum, add_pow,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have Fsc : ∀ K c b, F K (c * b) = PowerSeries.rescale (algebraMap B Q.P c) (F K b) := by
    intro K c b
    ext n
    rw [PowerSeries.coeff_rescale]
    simp only [hF, PowerSeries.coeff_mk, mul_pow, map_mul, map_pow]
    ring
  have Fexp : ∀ K, K ≠ 0 → ∀ b, IsExp (F K b) := by
    intro K hK b m n
    simp only [hF, PowerSeries.coeff_mk]
    rw [mul_mul_mul_comm, gb_mul Q hK, pow_add, map_mul]
    ring
  have exp1 : IsExp (1 : PowerSeries Q.P) := by
    intro m n
    simp only [PowerSeries.coeff_one]
    by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [hm, hn]
  obtain ⟨E, hE⟩ : ∃ E : Finset ℕ → Q.P → PowerSeries Q.P, ∀ S x,
      E S x = ∏ k ∈ S, F (k + 1) (Q.e.repr x (k + 1)) := ⟨_, fun _ _ => rfl⟩
  have cover : ∀ x : Q.P, ∀ k, Q.e.repr x (k + 1) ≠ 0 →
      k ∈ Finset.range ((Q.e.repr x).support.sup id) := by
    intro x k hk
    have hmem : k + 1 ∈ (Q.e.repr x).support := Finsupp.mem_support_iff.mpr hk
    have := Finset.le_sup (f := id) hmem
    simp only [id] at this
    exact Finset.mem_range.mpr (by omega)
  have Eind : ∀ x S T, (∀ k, Q.e.repr x (k + 1) ≠ 0 → k ∈ S) →
      (∀ k, Q.e.repr x (k + 1) ≠ 0 → k ∈ T) → E S x = E T x := by
    intro x S T hS hT
    have mono : ∀ U V, U ⊆ V → (∀ k, Q.e.repr x (k + 1) ≠ 0 → k ∈ U) → E U x = E V x := by
      intro U V hUV hU
      rw [hE, hE]
      apply Finset.prod_subset hUV
      intro k _ hk
      have : Q.e.repr x (k + 1) = 0 := by
        by_contra h
        exact hk (hU k h)
      rw [this, F0]
    rw [mono S (S ∪ T) Finset.subset_union_left hS, mono T (S ∪ T) Finset.subset_union_right hT]
  have c0 : ∀ S x, PowerSeries.coeff 0 (E S x) = 1 := by
    intro S x
    rw [hE]
    induction S using Finset.induction_on with
    | empty => simp
    | insert k S hk ih =>
      rw [Finset.prod_insert hk, PowerSeries.coeff_mul]
      simp [ih, hF, gb_zero]
  refine ⟨fun n x => PowerSeries.coeff n (E (Finset.range ((Q.e.repr x).support.sup id)) x),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact c0 _ x
  · intro n x y
    dsimp only
    obtain ⟨S, hxS, hyS, hxyS⟩ : ∃ S : Finset ℕ, (∀ k, Q.e.repr x (k + 1) ≠ 0 → k ∈ S) ∧
        (∀ k, Q.e.repr y (k + 1) ≠ 0 → k ∈ S) ∧ (∀ k, Q.e.repr (x + y) (k + 1) ≠ 0 → k ∈ S) :=
      ⟨Finset.range ((Q.e.repr x).support.sup id) ∪ Finset.range ((Q.e.repr y).support.sup id) ∪
        Finset.range ((Q.e.repr (x + y)).support.sup id),
        fun k hk => Finset.mem_union_left _ (Finset.mem_union_left _ (cover x k hk)),
        fun k hk => Finset.mem_union_left _ (Finset.mem_union_right _ (cover y k hk)),
        fun k hk => Finset.mem_union_right _ (cover _ k hk)⟩
    rw [Eind x _ S (cover x) hxS, Eind y _ S (cover y) hyS, Eind (x + y) _ S (cover _) hxyS]
    have : E S (x + y) = E S x * E S y := by
      rw [hE, hE, hE, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [show Q.e.repr (x + y) = Q.e.repr x + Q.e.repr y from map_add _ _ _, Finsupp.add_apply,
        Fadd _ (Nat.succ_ne_zero k)]
    rw [this, PowerSeries.coeff_mul]
  · intro m n x
    dsimp only
    have : IsExp (E (Finset.range ((Q.e.repr x).support.sup id)) x) := by
      rw [hE]
      exact Finset.prod_induction _ IsExp (fun f g hf hg => hf.mul hg) exp1
        (fun k _ => Fexp _ (Nat.succ_ne_zero k) _)
    exact this m n
  · intro n c x
    dsimp only
    obtain ⟨S, hxS, hcS⟩ : ∃ S : Finset ℕ, (∀ k, Q.e.repr x (k + 1) ≠ 0 → k ∈ S) ∧
        (∀ k, Q.e.repr (c • x) (k + 1) ≠ 0 → k ∈ S) :=
      ⟨Finset.range ((Q.e.repr x).support.sup id) ∪ Finset.range ((Q.e.repr (c • x)).support.sup id),
        fun k hk => Finset.mem_union_left _ (cover x k hk),
        fun k hk => Finset.mem_union_right _ (cover _ k hk)⟩
    rw [Eind x _ S (cover x) hxS, Eind (c • x) _ S (cover _) hcS]
    have : E S (c • x) = PowerSeries.rescale (algebraMap B Q.P c) (E S x) := by
      rw [hE, hE, map_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [show Q.e.repr (c • x) = c • Q.e.repr x from map_smul _ _ _, Finsupp.smul_apply, smul_eq_mul,
        Fsc]
    rw [this, PowerSeries.coeff_rescale]
  · intro n K hK
    dsimp only
    have hS : ∀ k, Q.e.repr (Q.e K) (k + 1) ≠ 0 →
        k ∈ Finset.range ((Q.e.repr (Q.e K)).support.sup id) ∪ {K - 1} :=
      fun k hk => Finset.mem_union_left _ (cover _ k hk)
    rw [Eind (Q.e K) _ _ (cover _) hS, hE, Finset.prod_eq_single (K - 1)]
    · rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hK), Q.e.repr_self, Finsupp.single_eq_same, hF,
        PowerSeries.coeff_mk, one_pow, map_one, one_mul]
    · intro k _ hk
      rw [Q.e.repr_self, Finsupp.single_apply, if_neg (by omega), F0]
    · intro h
      exact absurd (Finset.mem_union_right _ (Finset.mem_singleton_self _)) h

theorem pre_aug (B : Type) [CommRing B] (Q : PDPoly B) : ∃ η : ℕ → Q.P → Q.P, IsPreDP Q.aug η ∧
    ∀ n k : ℕ, η n (Q.e (k + 1)) = (n.uniformBell (k + 1) : Q.P) * Q.e (n * (k + 1)) := by
  obtain ⟨D, h0, hadd, hexp, hsc, hgen⟩ := dividedPower_identities_D_and_e_eq_gb Q
  have hnat : ∀ (c : ℕ) (y : Q.P), (c : Q.P) * y = (c : B) • y := by
    intro c y
    rw [Algebra.smul_def, map_natCast]
  have hzero : ∀ n, n ≠ 0 → D n 0 = 0 := by
    intro n hn
    have := hsc n 0 0
    rw [zero_smul, map_zero, zero_pow hn, zero_mul] at this
    exact this
  have hmulgen : ∀ K, K ≠ 0 → ∀ (a : Q.P) n, D n (a * Q.e K) = a ^ n * D n (Q.e K) := by
    intro K hK a
    have ha : a ∈ Submodule.span B (Set.range Q.e) := by
      rw [Q.e.span_eq]
      trivial
    induction ha using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      intro n
      obtain ⟨M, hM, hpow⟩ := e_pow Q j n
      have key := num2 n j M hK hM
      have hr : (M : Q.P) * Q.e (n * j) * ((n.uniformBell K : Q.P) * Q.e (n * K)) =
          ((M * n.uniformBell K * (n * j + n * K).choose (n * j) : ℕ) : Q.P) * Q.e (n * j + n * K) := by
        rw [mul_mul_mul_comm, Q.e_mul]
        push_cast
        ring
      rw [Q.e_mul, hnat, hsc, hgen _ _ (by omega), hgen _ _ hK, hpow]
      unfold gb
      rw [hr, key, mul_add]
      simp only [map_natCast]
      push_cast
      ring
    | zero =>
      intro n
      rw [zero_mul]
      by_cases hn : n = 0
      · subst hn
        rw [h0, h0, pow_zero, one_mul]
      · rw [hzero n hn, zero_pow hn, zero_mul]
    | add a a' _ _ iha iha' =>
      intro n
      rw [add_mul, hadd, add_pow, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hle : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      dsimp only
      rw [iha, iha', mul_mul_mul_comm, hexp, Nat.add_sub_cancel' hle]
      ring
    | smul c a _ iha =>
      intro n
      rw [smul_mul_assoc, hsc, iha, smul_pow, Algebra.smul_def, map_pow]
      ring
  have haug : ∀ x ∈ Q.aug, (∀ (a : Q.P) n, D n (a * x) = a ^ n * D n x) ∧ D 1 x = x ∧
      (∀ n, n ≠ 0 → D n x ∈ Q.aug) := by
    intro x hx
    have hx' : x ∈ Submodule.span Q.P (Set.range fun n => Q.e (n + 1)) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨K, rfl⟩ := hy
      refine ⟨fun a n => hmulgen _ (by omega) a n, ?_, ?_⟩
      · rw [hgen 1 _ (by omega)]
        simp [gb, Nat.uniformBell_one_left]
      · intro n hn
        rw [hgen n _ (by omega)]
        unfold gb
        apply Ideal.mul_mem_left
        have hp : 0 < n * (K + 1) := Nat.mul_pos (Nat.pos_of_ne_zero hn) (Nat.succ_pos K)
        obtain ⟨m, hm⟩ : ∃ m, n * (K + 1) = m + 1 := ⟨n * (K + 1) - 1, by omega⟩
        rw [hm]
        exact Q.e_succ_mem_aug m
    | zero =>
      refine ⟨fun a n => ?_, ?_, fun n hn => ?_⟩
      · rw [mul_zero]
        by_cases hn : n = 0
        · subst hn
          rw [h0, pow_zero, one_mul]
        · rw [hzero n hn, mul_zero]
      · exact hzero 1 one_ne_zero
      · rw [hzero n hn]
        exact Q.aug.zero_mem
    | add x y _ _ ihx ihy =>
      obtain ⟨mx, ox, memx⟩ := ihx
      obtain ⟨my, oy, memy⟩ := ihy
      refine ⟨fun a n => ?_, ?_, fun n hn => ?_⟩
      · rw [mul_add, hadd, hadd, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [mx, my, ← Finset.HasAntidiagonal.mem_antidiagonal.mp hp, pow_add]
        ring
      · rw [hadd]
        simp [Finset.Nat.sum_antidiagonal_succ, h0, ox, oy, add_comm]
      · rw [hadd]
        apply Ideal.sum_mem
        intro p hp
        have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        by_cases h1 : p.1 = 0
        · exact Ideal.mul_mem_left _ _ (memy _ (by omega))
        · exact Ideal.mul_mem_right _ _ (memx _ h1)
    | smul r x _ ih =>
      obtain ⟨mx, ox, memx⟩ := ih
      refine ⟨fun a n => ?_, ?_, fun n hn => ?_⟩
      · rw [smul_eq_mul, ← mul_assoc, mx, mx, mul_pow]
        ring
      · rw [smul_eq_mul, mx, ox, pow_one]
      · rw [smul_eq_mul, mx]
        exact Ideal.mul_mem_left _ _ (memx n hn)
  classical
  refine ⟨fun n x => if x ∈ Q.aug then D n x else 0, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro n x hx
    simp only [if_neg hx]
  · intro x hx
    simp only [if_pos hx, h0]
  · intro x hx
    simp only [if_pos hx]
    exact (haug x hx).2.1
  · intro n hn x hx
    simp only [if_pos hx]
    exact (haug x hx).2.2 n hn
  · intro n x hx y hy
    simp only [if_pos hx, if_pos hy, if_pos (Q.aug.add_mem hx hy)]
    exact hadd n x y
  · intro n a x hx
    simp only [if_pos hx, if_pos (Q.aug.mul_mem_left a hx)]
    exact (haug x hx).1 a n
  · intro m n x hx
    simp only [if_pos hx]
    exact hexp m n x
  · intro n k
    have hm : Q.e (k + 1) ∈ Q.aug := Q.e_succ_mem_aug k
    simp only [if_pos hm]
    rw [hgen n (k + 1) (by omega)]
    rfl

end FubiniStudyChowHeightFormula₂.Adr
end
end

section
set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

open PowerSeries

theorem uniformBell_comp_coeff (m : ℕ) {n N : ℕ} (hn : n ≠ 0) (hN : N ≠ 0) :
    n.uniformBell N ^ m * m.uniformBell (n * N) = m.uniformBell n * (m * n).uniformBell N := by
  have h1 := Nat.uniformBell_mul_eq n hN
  have h2 := Nat.uniformBell_mul_eq m (Nat.mul_ne_zero hn hN)
  have h3 := Nat.uniformBell_mul_eq m hn
  have h4 := Nat.uniformBell_mul_eq (m * n) hN
  have hpos : 0 < N.factorial ^ (m * n) * n.factorial ^ m * m.factorial := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  have e1 : n.uniformBell N ^ m * m.uniformBell (n * N)
      * (N.factorial ^ (m * n) * n.factorial ^ m * m.factorial) = (m * (n * N)).factorial := by
    rw [← h2, ← h1]
    ring
  have e2 : m.uniformBell n * (m * n).uniformBell N
      * (N.factorial ^ (m * n) * n.factorial ^ m * m.factorial) = (m * n * N).factorial := by
    rw [← h4, ← h3]
    ring
  rw [e1, e2, mul_assoc]

theorem exists_dividedPowers_aug : ∀ (B : Type) [CommRing B] (Q : PDPoly B),
    ∃ η : DividedPowers Q.aug, ∀ n : ℕ, η.dpow n (Q.e 1) = Q.e n := by
  intro B _ Q
  obtain ⟨η, hpre, hη⟩ := pre_aug B Q
  obtain ⟨δ, hδ⟩ := dp_of_pre Q.P Q.aug η (Set.range fun n : ℕ => Q.e (n + 1)) hpre rfl (by
    rintro x ⟨k, rfl⟩ m n hn
    show η m (η n (Q.e (k + 1))) = _ * η (m * n) (Q.e (k + 1))
    obtain ⟨j, hj⟩ : ∃ j, n * (k + 1) = j + 1 :=
      ⟨n * (k + 1) - 1, by
        have : 0 < n * (k + 1) := Nat.mul_pos (Nat.pos_of_ne_zero hn) k.succ_pos
        omega⟩
    have hc := congrArg (Nat.cast : ℕ → Q.P) (uniformBell_comp_coeff m hn (N := k + 1) (by omega))
    push_cast at hc
    rw [hη n k, hj, hpre.mul m _ _ (Q.e_succ_mem_aug j), hη m j, hη (m * n) k, ← hj,
      show m * (n * (k + 1)) = m * n * (k + 1) by ring, ← mul_assoc, ← mul_assoc, hc])
  refine ⟨δ, fun n => ?_⟩
  rw [hδ]
  simpa [Nat.uniformBell_one_right] using hη n 0

private theorem dpowSeries_add_base_eq_mul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R}
    (κ : DividedPowers I) {r : R} (hr : r ∈ I) (a b : A) :
    (PowerSeries.mk fun n => (a + b) ^ n * algebraMap R A (κ.dpow n r)) =
      (PowerSeries.mk fun n => a ^ n * algebraMap R A (κ.dpow n r)) *
        PowerSeries.mk fun n => b ^ n * algebraMap R A (κ.dpow n r) := by
  ext n
  simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  rw [(Commute.all a b).add_pow', Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hk
  have h := κ.mul_dpow (m := k.1) (n := k.2) hr
  rw [hk] at h
  rw [show a ^ k.1 * algebraMap R A (κ.dpow k.1 r) * (b ^ k.2 * algebraMap R A (κ.dpow k.2 r))
      = a ^ k.1 * b ^ k.2 * algebraMap R A (κ.dpow k.1 r * κ.dpow k.2 r) by rw [map_mul]; ring,
    h, map_mul, map_natCast, nsmul_eq_mul]
  ring

private theorem dpowSeries_algebraMap_mul_base_eq_smul_arg {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R}
    (κ : DividedPowers I) {r : R} (hr : r ∈ I) (s : R) (y : A) :
    (PowerSeries.mk fun n => (algebraMap R A s * y) ^ n * algebraMap R A (κ.dpow n r)) =
      PowerSeries.mk fun n => y ^ n * algebraMap R A (κ.dpow n (s * r)) := by
  ext n
  simp only [PowerSeries.coeff_mk]
  rw [κ.dpow_mul hr, map_mul, map_pow]
  ring

private theorem dpowSeries_add_arg_eq_mul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R}
    (κ : DividedPowers I) {r r' : R} (hr : r ∈ I) (hr' : r' ∈ I) (y : A) :
    (PowerSeries.mk fun n => y ^ n * algebraMap R A (κ.dpow n (r + r'))) =
      (PowerSeries.mk fun n => y ^ n * algebraMap R A (κ.dpow n r)) *
        PowerSeries.mk fun n => y ^ n * algebraMap R A (κ.dpow n r') := by
  ext n
  simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  rw [κ.dpow_add hr hr', map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hk
  rw [← hk, pow_add, map_mul]
  ring

private theorem dpowSeries_zero_arg_eq_one {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R}
    (κ : DividedPowers I) (y : A) :
    (PowerSeries.mk fun n => y ^ n * algebraMap R A (κ.dpow n 0)) = 1 := by
  ext n
  rcases n with _ | n
  · simp [κ.dpow_zero I.zero_mem]
  · simp [κ.dpow_eval_zero (Nat.succ_ne_zero n)]

private theorem dpowSeries_zero_base_eq_one {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R}
    (κ : DividedPowers I) {r : R} (hr : r ∈ I) :
    (PowerSeries.mk fun n => (0 : A) ^ n * algebraMap R A (κ.dpow n r)) = 1 := by
  ext n
  rcases n with _ | n
  · simp [κ.dpow_zero hr]
  · simp

private theorem dpowSeries_sum_base_eq_prod {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R}
    (κ : DividedPowers I) {r : R} (hr : r ∈ I) {ι : Type} (s : Finset ι) (v : ι → A) :
    (PowerSeries.mk fun n => (∑ j ∈ s, v j) ^ n * algebraMap R A (κ.dpow n r)) =
      ∏ j ∈ s, PowerSeries.mk fun n => v j ^ n * algebraMap R A (κ.dpow n r) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using dpowSeries_zero_base_eq_one κ hr
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, dpowSeries_add_base_eq_mul κ hr, ih]

private theorem dpowSeries_sum_arg_eq_prod {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I : Ideal R}
    (κ : DividedPowers I) (y : A) {ι : Type} (s : Finset ι) (v : ι → R) (hv : ∀ i, v i ∈ I) :
    (PowerSeries.mk fun n => y ^ n * algebraMap R A (κ.dpow n (∑ i ∈ s, v i))) =
      ∏ i ∈ s, PowerSeries.mk fun n => y ^ n * algebraMap R A (κ.dpow n (v i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using dpowSeries_zero_arg_eq_one κ y
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj,
      dpowSeries_add_arg_eq_mul κ (hv j) (I.sum_mem fun i _ => hv i), ih]

theorem flatExt (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A] (I : Ideal R)
    (κ : DividedPowers I) : ∃ δ : DividedPowers (I.map (algebraMap R A)), IsDPMorphism κ δ (algebraMap R A) := by
  classical
  obtain ⟨γ, hpre, hγ⟩ := pre_of_gens A I (fun i : I => algebraMap R A i)
    (fun i n => algebraMap R A (κ.dpow n i))
    (fun i => by simp [κ.dpow_zero i.2])
    (fun i => by simp [κ.dpow_one i.2])
    (fun i n hn => Ideal.subset_span ⟨⟨κ.dpow n i, κ.dpow_mem hn i.2⟩, rfl⟩)
    (fun i m n => by rw [← map_mul, κ.mul_dpow i.2, map_mul, map_natCast])
    (by
      intro c hc
      have hrel : ∑ i : c.support, ((i : I) : R) • c i = 0 := by
        rw [Finset.sum_coe_sort c.support (fun i => ((i : I) : R) • c i)]
        simpa [Finsupp.sum, Algebra.smul_def, mul_comm] using hc
      obtain ⟨k, a, y, hca, hsum⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
        (R := R) (M := A) (f := fun i : c.support => ((i : I) : R)) (x := fun i => c i) hrel
      rw [Finsupp.prod, ← Finset.prod_coe_sort]
      calc (∏ i : c.support, PowerSeries.mk fun n =>
              c i ^ n * algebraMap R A (κ.dpow n ((i : I) : R)))
          = ∏ i : c.support, ∏ j, PowerSeries.mk fun n =>
              y j ^ n * algebraMap R A (κ.dpow n (a i j * ((i : I) : R))) := by
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [show (c i : A) = ∑ j, a i j • y j from hca i, dpowSeries_sum_base_eq_prod κ (i : I).2]
            refine Finset.prod_congr rfl fun j _ => ?_
            rw [Algebra.smul_def, dpowSeries_algebraMap_mul_base_eq_smul_arg κ (i : I).2]
        _ = ∏ j, ∏ i : c.support, PowerSeries.mk fun n =>
              y j ^ n * algebraMap R A (κ.dpow n (a i j * ((i : I) : R))) := Finset.prod_comm
        _ = ∏ j, PowerSeries.mk fun n =>
              y j ^ n * algebraMap R A (κ.dpow n (∑ i : c.support, a i j * ((i : I) : R))) := by
            refine Finset.prod_congr rfl fun j _ => ?_
            exact (dpowSeries_sum_arg_eq_prod κ (y j) Finset.univ (fun i : c.support => a i j * ((i : I) : R))
              fun i => I.mul_mem_left _ (i : I).2).symm
        _ = 1 := by
            refine Finset.prod_eq_one fun j _ => ?_
            have h0 : ∑ i : c.support, a i j * ((i : I) : R) = 0 := by
              rw [← hsum j]
              exact Finset.sum_congr rfl fun i _ => mul_comm _ _
            rw [h0, dpowSeries_zero_arg_eq_one κ (y j)])
  have hspan : I.map (algebraMap R A) = Ideal.span (Set.range fun i : I => algebraMap R A i) := by
    rw [Ideal.map, Set.image_eq_range]
    rfl
  obtain ⟨δ, hδ⟩ := dp_of_pre A (I.map (algebraMap R A)) γ (Set.range fun i : I => algebraMap R A i)
    (hspan ▸ hpre) hspan (by
      rintro _ ⟨i, rfl⟩ m n hn
      show γ m (γ n (algebraMap R A i)) = _ * γ (m * n) (algebraMap R A i)
      rw [hγ i n, hγ ⟨κ.dpow n i, κ.dpow_mem hn i.2⟩ m, hγ i (m * n)]
      show algebraMap R A (κ.dpow m (κ.dpow n i)) = _
      rw [κ.dpow_comp hn i.2, map_mul, map_natCast])
  refine ⟨δ, ⟨le_rfl, fun {n} a ha => ?_⟩⟩
  rw [hδ]
  exact hγ ⟨a, ha⟩ n

theorem exists_std (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) :
    ∃ η : DividedPowers (Q.ext J), Q.IsStd δ η := by
  obtain ⟨η, hη⟩ := exists_dividedPowers_aug B Q
  obtain ⟨-, ε, hε⟩ := exists_lift_and_aug B Q
  obtain ⟨θ, hθ, hθη⟩ := dp_split B J δ Q.P ε Q.aug η hε
  refine ⟨θ, ⟨hθ, fun n => ?_⟩⟩
  rw [hθη n _ (Q.e_succ_mem_aug 0)]
  exact hη n

end FubiniStudyChowHeightFormula₂.Adr
end
end
