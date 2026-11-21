import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GqPtOfNeZeroIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColReduced

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IntTerm

namespace GlobalTheory.PtEx

theorem exists_blocks {K : Type} [Zero K] (n : ℕ) : ∀ (w : ℕ → ℕ) (d : ℕ → K), (∀ a < n, d a ≠ 0) →
    (∀ a < n, w a < n) → (∀ a < n, ∀ b < n, w a = w b → a = b) → (∀ v < n, ∃ a < n, w a = v) →
    (∀ a b, a < b → b < n → w a = w b + 1 → b = a + 1 ∧ d a = d b) →
    ∃ bs : List (K × ℕ), ((∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) ∧ (bs.map Prod.snd).sum = n) ∧
      ∀ a < n, ∀ b < n, Formalism.MainNotions.S.ptEntry bs a b = if a = w b then d b else 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w d hd hlt hinj hsur hC
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨[], by simp, fun a ha => absurd ha (Nat.not_lt_zero a)⟩
  obtain ⟨s, hs⟩ : ∃ s, s = w 0 + 1 := ⟨_, rfl⟩
  have hsn : s ≤ n := by have := hlt 0 hn; omega
  have run (a : ℕ) : a < s → ∀ c ≤ a, w c + c + 1 = s ∧ d c = d 0 := by
    induction a with
    | zero => intro _ c hc; obtain rfl : c = 0 := by omega
              exact ⟨by omega, rfl⟩
    | succ a iha =>
      intro ha c hc
      have k := iha (by omega)
      rcases Nat.lt_or_ge c (a + 1) with h | h
      · exact k c (by omega)
      obtain rfl : c = a + 1 := by omega
      have ka := k a le_rfl
      obtain ⟨b, hb, e⟩ := hsur (w a - 1) (by omega)
      have hab : a < b := by
        by_contra h
        have := (k b (by omega)).1
        omega
      obtain ⟨rfl, e2⟩ := hC a b hab hb (by omega)
      exact ⟨by omega, e2.symm.trans ka.2⟩
  have lo (c : ℕ) (hc : c < s) : w c + c + 1 = s ∧ d c = d 0 := run c hc c le_rfl
  have hi (c : ℕ) (hc : s ≤ c) (hcn : c < n) : s ≤ w c := by
    by_contra h
    have h1 := (lo (s - 1 - w c) (by omega)).1
    have := hinj c hcn (s - 1 - w c) (by omega) (by omega)
    omega
  obtain ⟨bs, ⟨h1, h2⟩, h3⟩ := ih (n - s) (by omega) (fun a => w (a + s) - s) (fun a => d (a + s))
    (fun a ha => hd _ (by omega))
    (fun a ha => by have := hlt (a + s) (by omega); have := hi (a + s) (by omega) (by omega); omega)
    (fun a ha b hb e => by
      have := hi (a + s) (by omega) (by omega)
      have := hi (b + s) (by omega) (by omega)
      have := hinj (a + s) (by omega) (b + s) (by omega) (by omega)
      omega)
    (fun v hv => by
      obtain ⟨b, hb, e⟩ := hsur (v + s) (by omega)
      have : s ≤ b := by
        by_contra h
        have := (lo b (by omega)).1
        omega
      exact ⟨b - s, by omega, by simp only [Nat.sub_add_cancel this]; omega⟩)
    (fun a b hab hb e => by
      have := hi (a + s) (by omega) (by omega)
      have := hi (b + s) (by omega) (by omega)
      have := hC (a + s) (b + s) (by omega) (by omega) (by omega)
      exact ⟨by omega, this.2⟩)
  refine ⟨(d 0, s) :: bs, ⟨?_, by simp [h2]; omega⟩, fun a ha b hb => ?_⟩
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨⟨hd 0 hn, by omega⟩, h1⟩
  · rw [Formalism.MainNotions.S.ptEntry]
    rcases Nat.lt_or_ge b s with hbs | hbs
    · obtain ⟨e1, e2⟩ := lo b hbs
      rw [e2]
      split_ifs <;> first | rfl | omega
    · have := hi b hbs hb
      rw [if_neg (by omega)]
      rcases Nat.lt_or_ge a s with has | has
      · rw [if_neg (by omega), if_neg (by omega)]
      · rw [if_pos ⟨has, hbs⟩, h3 _ (by omega) _ (by omega)]
        simp only [Nat.sub_add_cancel hbs]
        split_ifs <;> first | rfl | omega

theorem exists_point {K : Type} [Zero K] {n : ℕ} (w : Equiv.Perm (Fin n)) (d : Fin n → K) (hd : ∀ a, d a ≠ 0)
    (hC : ∀ a b, a < b → (w a : ℕ) = w b + 1 → (b : ℕ) = a + 1 ∧ d a = d b) :
    ∃ p : Formalism.MainNotions.S.Point K n, Formalism.MainNotions.S.ptMat p = Matrix.of fun a b => if a = w b then d b else 0 := by
  obtain ⟨bs, h1, h2⟩ := exists_blocks n (fun a => if h : a < n then (w ⟨a, h⟩ : ℕ) else 0)
    (fun a => if h : a < n then d ⟨a, h⟩ else 0) (fun a ha => by simpa [ha] using hd _)
    (fun a ha => by simp [ha])
    (fun a ha b hb e => by
      simp only [ha, hb, dif_pos] at e
      simpa using w.injective (Fin.ext e))
    (fun v hv => ⟨w.symm ⟨v, hv⟩, (w.symm _).2, by simp⟩)
    (fun a b hab hb e => by
      have ha : a < n := hab.trans hb
      simp only [ha, hb, dif_pos] at e ⊢
      exact hC ⟨a, ha⟩ ⟨b, hb⟩ hab e)
  refine ⟨⟨bs, h1⟩, Matrix.ext fun a b => (h2 a a.2 b b.2).trans ?_⟩
  simp [Fin.ext_iff]

variable {E : Type} [Field E]


section Lie

variable {σ : E →+* E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {T T' : E}
  {P P' : Matrix (Fin n) (Fin (r + 1)) E} {Z A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}

theorem cT_cT (hσ : ∀ x, σ (σ x) = x) {a b : Type} (M : Matrix a b E) : cT σ (cT σ M) = M := by
  ext i j
  simp [cT, hσ]

theorem cT_add {a b : Type} (M N : Matrix a b E) : cT σ (M + N) = cT σ M + cT σ N := by
  ext i j
  simp [cT]

theorem det_cT (Z : Matrix (Fin n) (Fin n) E) : (cT σ Z).det = σ Z.det := by
  rw [cT, Matrix.det_transpose, RingHom.map_det]; rfl


theorem det_gram_ne_zero (hZ : Z.det ≠ 0) (hG : Gq σ T T' Z ≠ 0) :
    (Matrix.fromBlocks (TF r T) Z (cT σ Z) (TF r T')).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, e⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  rw [← Sum.elim_comp_inl_inr v, Matrix.fromBlocks_mulVec] at e
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at e
  have e1 : TF r T *ᵥ (v ∘ Sum.inl) + Z *ᵥ (v ∘ Sum.inr) = 0 := funext fun i => congrFun e (Sum.inl i)
  have e2 : TF r T' *ᵥ (v ∘ Sum.inr) + cT σ Z *ᵥ (v ∘ Sum.inl) = 0 :=
    (add_comm _ _).trans (funext fun i => congrFun e (Sum.inr i))
  apply hv
  rw [← Sum.elim_comp_inl_inr v]
  generalize v ∘ Sum.inl = a at *
  generalize v ∘ Sum.inr = a' at *
  have d1 := Iota.det_mul_last e1
  have d2 := Iota.det_mul_last e2
  have c2 : SgAlg.lead (cT σ Z) r (Nat.le_succ r) = σ (SgAlg.lead Z r (Nat.le_succ r)) := by
    rw [SgAlg.lead, SgAlg.lead, ← det_cT]
    rfl
  rw [det_cT, c2] at d2
  have l1 : a (Fin.last r) = 0 := (mul_eq_zero.1 (by
    rw [Gq]
    linear_combination Z.det * d2 + T' * σ (SgAlg.lead Z r (Nat.le_succ r)) * d1)).resolve_left hG
  have l2 : a' (Fin.last r) = 0 := (mul_eq_zero.1 (by
    rw [Gq]
    linear_combination σ Z.det * d1 + T * SgAlg.lead Z r (Nat.le_succ r) * d2)).resolve_left hG
  have k (T : E) {x : Fin (r + 1) → E} (hx : x (Fin.last r) = 0) : TF r T *ᵥ x = 0 := by
    ext i
    by_cases hi : i = Fin.last r <;> simp [TF, Matrix.mulVec_diagonal, hi, hx]
  rw [k T l1, zero_add] at e1
  rw [k T' l2, zero_add] at e2
  rw [Matrix.eq_zero_of_mulVec_eq_zero hZ e1,
    Matrix.eq_zero_of_mulVec_eq_zero (by rw [det_cT]; simpa using hZ) e2]
  simp



end Lie

section Generic

variable {σ : E →+* E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {T T' : E}
  {P P' : Matrix (Fin n) (Fin (r + 1)) E} {Z A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}



variable [CharZero E]



end Generic

section Signature

open scoped ComplexOrder

variable {n r p : ℕ}


variable {σ : E →+* E} {J : Matrix (Fin n) (Fin n) E} {T T' : E} {P P' : Matrix (Fin n) (Fin (r + 1)) E}
  {τ : E →+* ℂ}

theorem pairM_map (hτ : ∀ x, τ (σ x) = starRingEnd ℂ (τ x)) :
    pairM (starRingEnd ℂ) (J.map τ) (P'.map τ) (P.map τ) = (pairM σ J P' P).map τ := by
  rw [pairM, pairM, Matrix.map_mul, Matrix.map_mul]
  congr 2
  ext i j
  simp [cT, hτ]

theorem isFrame_map (hτ : ∀ x, τ (σ x) = starRingEnd ℂ (τ x)) (hP : IsFrame σ J T P) :
    IsFrame (starRingEnd ℂ) (J.map τ) (τ T) (P.map τ) := by
  obtain ⟨⟨L, hL⟩, h⟩ := hP
  refine ⟨⟨L.map τ, by rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero τ) (map_one τ)]⟩, ?_⟩
  rw [pairM_map hτ, h]
  ext i j
  simp [TF, Matrix.diagonal_apply, apply_ite τ]


end Signature

section Record

open Formalism.BasicNotions
open scoped ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u u' : D.what₂.Word}



end Record

end GlobalTheory.PtEx
