import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainFirstIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinorCellOfParts

section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal

theorem chainX1' {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M] (k r : ℕ) (c : Fin r → ℂ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M) (hG : GlRel E) (m : ℕ) (hm : m + 2 ≤ r)
    (u : ℂ)
    (hR0 : ∀ (x : A) (l : ℕ) (hl : l < m), La (x * E (eI k r ⟨l, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) = 0)
    (hR1 : ∀ x : A, La (x * E (eI k r ⟨m, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) = La x)
    (hL : ∀ (x : A) (q : ℕ) (hq : q ≤ m), La (E (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨q, by omega⟩) * x) =
      (if q = m then c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩ else 0) • La x) :
    La (qminor E (xR k r (m + 2) hm) (xR k r (m + 2) hm) u) =
      La (qminor E (xR k r (m + 1) (by omega)) (xR k r (m + 1) (by omega)) u *
          Tm E (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) -
        (c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩) • La (qminor E (xR k r m (by omega)) (xR k r m (by omega)) u) := by
  set a := xR k r (m + 2) hm with hadef
  have hav : ∀ l, (a l).val = l.val := by intro l; simp [a, xR, eI]
  have hcs : a ∘ Fin.castSucc = xR k r (m + 1) (by omega) := by
    funext l; ext; simp [a, xR, eI]
  have hexp := Formalism.FourierDecayAlt.P.expansion_last_column A _ (m + 1) E a a u
  rw [hexp, map_sum, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]

  have hzero : ∀ l : Fin m, La ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.castSucc l) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ (Fin.castSucc (Fin.castSucc l)).succAbove) (a ∘ Fin.castSucc) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.castSucc l))) (a (Fin.last (m + 1))))) = 0 := by
    intro l
    rw [la_intmul]
    have hne : a (Fin.castSucc (Fin.castSucc l)) ≠ a (Fin.last (m + 1)) := by
      intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this; omega
    rw [tm_offdiag _ _ hne]
    have ha1 : a (Fin.castSucc (Fin.castSucc l)) = eI k r ⟨l.val, by omega⟩ := by ext; rw [hav]; simp [eI]
    have ha2 : a (Fin.last (m + 1)) = eI k r ⟨m + 1, by omega⟩ := by ext; rw [hav]; simp [eI]
    rw [ha1, ha2, hR0 _ l.val l.isLt, smul_zero]
  rw [Finset.sum_eq_zero (fun l _ => hzero l), zero_add]

  have hlast : La ((((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ (Fin.last (m + 1)).succAbove) (a ∘ Fin.castSucc) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.last (m + 1))) (a (Fin.last (m + 1))))) =
      La (qminor E (xR k r (m + 1) (by omega)) (xR k r (m + 1) (by omega)) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) := by
    rw [la_intmul, Fin.succAbove_last, hcs]
    have h1 : a (Fin.last (m + 1)) = eI k r ⟨m + 1, by omega⟩ := by ext; rw [hav]; simp [eI]
    rw [h1]
    have h2 : ((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ))) = 1 := by
      simp only [Fin.val_last]; rw [← two_mul, pow_mul]; norm_num
    rw [h2]; simp
  rw [hlast]

  set rowsP : Fin (m + 1) → Fin (2 * r + k + 1) := Fin.cons (eI k r ⟨m + 1, by omega⟩) (xR k r m (by omega)) with hrP
  have hrows : a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove = rowsP ∘ (finRotate (m + 1)) := by
    funext q
    ext
    simp only [Function.comp_apply]
    by_cases hq : q = Fin.last m
    · subst hq
      rw [finRotate_last]
      simp only [rowsP, Fin.cons_zero]
      rw [hav, succAbove_val]; simp [eI]
    · have hq' : q.val < m := by
        have := q.isLt; have : q.val ≠ m := fun h' => hq (Fin.ext (by simp [h'])); omega
      have hr1 : finRotate (m + 1) q = Fin.succ ⟨q.val, hq'⟩ := by
        ext; rw [coe_finRotate_of_ne_last hq]; simp
      rw [hr1]
      simp only [rowsP, Fin.cons_succ]
      rw [hav, succAbove_val]; simp [xR, eI]; omega
  have hQm : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) =
      (c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩) • La (qminor E (xR k r m (by omega)) (xR k r m (by omega)) u) := by
    rw [hrows, Formalism.REAL.quantumMinorRowSkew_holds A _ (m + 1) E rowsP _ (finRotate (m + 1)) u, la_intmul, sign_finRotate]
    rw [Formalism.FourierDecayAlt.P.expansion_first_line A _ m E hG rowsP _ u, map_sum]
    rw [Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add]
    · rw [la_intmul]
      have hr0 : rowsP 0 = eI k r ⟨m + 1, by omega⟩ := by simp [rowsP]
      have hrs : rowsP ∘ Fin.succ = xR k r m (by omega) := by funext q; simp [rowsP]
      rw [hr0, hrs, Fin.succAbove_last, hcs]
      have hne : eI k r ⟨m + 1, by omega⟩ ≠ xR k r (m + 1) (by omega) (Fin.last m) := by
        intro h'; have := congrArg Fin.val h'; simp [eI, xR] at this
      rw [tm_offdiag _ _ hne]
      have hx : xR k r (m + 1) (by omega) (Fin.last m) = eI k r ⟨m, by omega⟩ := by ext; simp [xR, eI]
      rw [hx, hL _ m le_rfl, if_pos rfl]
      have hcs2 : xR k r (m + 1) (by omega) ∘ Fin.castSucc = xR k r m (by omega) := by funext q; ext; simp [xR, eI]
      rw [hcs2, smul_smul, smul_smul]
      congr 1
      simp only [Fin.val_last]
      push_cast
      rw [neg_one_sq', one_mul]
    · intro q _
      rw [la_intmul]
      have hr0 : rowsP 0 = eI k r ⟨m + 1, by omega⟩ := by simp [rowsP]
      rw [hr0, hcs]
      have hqv : (xR k r (m + 1) (by omega) (Fin.castSucc q)).val = q.val := by simp [xR, eI]
      have hne : eI k r ⟨m + 1, by omega⟩ ≠ xR k r (m + 1) (by omega) (Fin.castSucc q) := by
        intro h'; have := congrArg Fin.val h'; rw [hqv] at this; simp [eI] at this; omega
      rw [tm_offdiag _ _ hne]
      have hx : xR k r (m + 1) (by omega) (Fin.castSucc q) = eI k r ⟨q.val, by omega⟩ := by ext; simp [xR, eI]
      have hq := q.isLt
      rw [hx, hL _ q.val (by omega), if_neg (by omega), zero_smul, smul_zero]
  have hmT : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u *
      Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.last m))) (a (Fin.last (m + 1)))) =
      La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) := by
    have hne : a (Fin.castSucc (Fin.last m)) ≠ a (Fin.last (m + 1)) := by
      intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this
    rw [tm_offdiag _ _ hne]
    have ha1 : a (Fin.castSucc (Fin.last m)) = eI k r ⟨m, by omega⟩ := by ext; rw [hav]; simp [eI]
    have ha2 : a (Fin.last (m + 1)) = eI k r ⟨m + 1, by omega⟩ := by ext; rw [hav]; simp [eI]
    rw [ha1, ha2, hR1]
  rw [la_intmul, hmT, hQm]
  have h3 : ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.last m) : Fin (m + 2)) : ℕ))) : ℤ) : ℂ) = -1 := by
    simp only [Fin.val_castSucc, Fin.val_last]
    push_cast
    rw [show m + 1 + m = 2 * m + 1 by ring, pow_succ, pow_mul]; norm_num
  rw [h3, neg_one_smul]; abel

end Formalism.FourierDecayAlt.P.PBN
end

section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN.MC

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2

section alg

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)}

def cI (p : Fin (2 * r + k + 1)) : Fin (mdim k r 0) := ⟨p.val, by have := p.isLt; simp [mdim]; omega⟩

theorem posL_cI (p : Fin (2 * r + k + 1)) : posL k r 0 (cI p) = p := Fin.ext (by simp [posL, cI])

theorem cI_inj : Function.Injective (cI (k := k) (r := r)) := fun p q h => Fin.ext (by
  have := congrArg Fin.val h; simpa [cI] using this)

variable (E) in

abbrev SA (hD : IsOpen D) : Subalgebra ℂ (Module.End ℂ (VS k r 0 D E)) :=
  Algebra.adjoin ℂ (Set.range fun p : Fin (mdim k r 0) × Fin (mdim k r 0) => Eh (E := E) (i := 0) hD p.1 p.2)

def EA (hD : IsOpen D) (p q : Fin (2 * r + k + 1)) : SA E hD :=
  ⟨Eh hD (cI p) (cI q), Algebra.subset_adjoin ⟨(cI p, cI q), rfl⟩⟩

theorem EA_val (hD : IsOpen D) (p q : Fin (2 * r + k + 1)) : (EA (E := E) hD p q : Module.End ℂ (VS k r 0 D E)) =
    Eh hD (cI p) (cI q) := rfl

theorem EA_gl (hD : IsOpen D) : GlRel (EA (E := E) hD) := by
  intro a b c d
  apply Subtype.ext
  have h := Eh_gl (E := E) (i := 0) hD (cI a) (cI b) (cI c) (cI d)
  simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, EA_val]
  rw [h]
  congr 1
  · by_cases hbc : b = c
    · rw [if_pos (congrArg cI hbc), if_pos hbc]; rfl
    · rw [if_neg (fun e => hbc (cI_inj e)), if_neg hbc]; rfl
  · by_cases hda : d = a
    · rw [if_pos (congrArg cI hda), if_pos hda]; rfl
    · rw [if_neg (fun e => hda (cI_inj e)), if_neg hda]; rfl

def La (hD : IsOpen D) (v : VS k r 0 D E) (g : Mx k r) : SA E hD →ₗ[ℂ] E where
  toFun x := ((x : Module.End ℂ (VS k r 0 D E)) v : Mx k r → E) g
  map_add' x y := by simp
  map_smul' c x := by simp

theorem La_apply (hD : IsOpen D) (v : VS k r 0 D E) (g : Mx k r) (x : SA E hD) :
    La hD v g x = ((x : Module.End ℂ (VS k r 0 D E)) v : Mx k r → E) g := rfl

theorem leftEq_SA (hD : IsOpen D) (z : Fin (2 * r + k + 1) → ℂ)
    (hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D) (x : SA E hD) :
    ∀ v : VS k r 0 D E, LeftEq k r z 0 D (v : Mx k r → E) →
      LeftEq k r z 0 D ((x : Module.End ℂ (VS k r 0 D E)) v : Mx k r → E) := by
  obtain ⟨x, hx⟩ := x
  show ∀ v : VS k r 0 D E, LeftEq k r z 0 D (v : Mx k r → E) → LeftEq k r z 0 D (x v : Mx k r → E)
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨p, rfl⟩ := hy
    intro v hv g hg n hn
    have hng : n * g ∈ Glev k r 0 ∩ D := ⟨Formalism.FourierDecayAlt.P.Qx3.glev_mul hn.2 hg.1, hN g hg n hn⟩
    rw [ev_E hD p.1 p.2 v hng, ev_E hD p.1 p.2 v hg]
    exact ((generator_action_preserved E k r z 0 D p.1 p.2 (v : Mx k r → E) (v : Mx k r → E) 1 hD v.2.1 v.2.1).2.1 hN hv) g hg n hn
  | algebraMap c =>
    intro v hv g hg n hn
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hv g hg n hn, smul_comm]
  | add y₁ y₂ _ _ h₁ h₂ =>
    intro v hv g hg n hn
    simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
    rw [h₁ v hv g hg n hn, h₂ v hv g hg n hn, smul_add]
  | mul y₁ y₂ _ _ h₁ h₂ =>
    intro v hv
    exact h₁ _ (h₂ v hv)

abbrev Tor (hD : IsOpen D) (j : ℕ) : Subalgebra ℂ (SA E hD) :=
  Algebra.adjoin ℂ {x | ∃ l : Fin r, j ≤ l.val ∧ x = EA hD (eI k r l) (eI k r l)}

theorem comm_Tor (hD : IsOpen D) (j : ℕ) (p q : Fin (2 * r + k + 1))
    (hp : ∀ l : Fin r, j ≤ l.val → p ≠ eI k r l) (hq : ∀ l : Fin r, j ≤ l.val → q ≠ eI k r l) (P : SA E hD)
    (hP : P ∈ Tor hD j) : Commute (EA hD p q) P := by
  induction hP using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    have h := EA_gl (E := E) hD p q (eI k r l) (eI k r l)
    rw [if_neg (hq l hl), if_neg (fun e => hp l hl e.symm), sub_zero] at h
    exact sub_eq_zero.1 h
  | algebraMap c => exact Algebra.commute_algebraMap_right c _
  | add y₁ y₂ _ _ h₁ h₂ => exact h₁.add_right h₂
  | mul y₁ y₂ _ _ h₁ h₂ => exact h₁.mul_right h₂

theorem Tor_mono (hD : IsOpen D) {j j' : ℕ} (h : j ≤ j') : Tor (E := E) hD j' ≤ Tor hD j :=
  Algebra.adjoin_mono fun _ ⟨l, hl, e⟩ => ⟨l, h.trans hl, e⟩

theorem EA_mem_Tor (hD : IsOpen D) (l : Fin r) {j : ℕ} (h : j ≤ l.val) :
    EA (E := E) hD (eI k r l) (eI k r l) ∈ Tor hD j :=
  Algebra.subset_adjoin ⟨l, h, rfl⟩

end alg

section qm

theorem map_qminor {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B) {n t : ℕ}
    (E : Fin n → Fin n → A) (a b : Fin t → Fin n) (u : ℂ) :
    φ (qminor E a b u) = qminor (fun p q => φ (E p q)) a b u := by
  unfold qminor
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 2
  congr 1
  funext l
  simp only [Function.comp_apply, Tm, map_add]
  congr 1
  split_ifs <;> simp

theorem qminor_reindex {A : Type} [Ring A] [Algebra ℂ A] {n n' t : ℕ} (E : Fin n' → Fin n' → A) (ι : Fin n → Fin n')
    (hι : Function.Injective ι) (a b : Fin t → Fin n) (u : ℂ) :
    qminor (fun p q => E (ι p) (ι q)) a b u = qminor E (ι ∘ a) (ι ∘ b) u := by
  unfold qminor
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 2
  congr 1
  funext l
  simp only [Function.comp_apply, Tm]
  congr 1
  by_cases h : a (σ l) = b l
  · rw [if_pos h, if_pos (congrArg ι h)]
  · rw [if_neg h, if_neg (fun e => h (hι e))]

end qm

section main

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} (hD : IsOpen D)

theorem gauge_last (c : Fin r → ℂ) :
    (∏ a : Fin r, (if a.val < (Fin.last r).val then ‖c a‖ ^ (Mdim k r a - 1) else 1)) =
      ∏ a : Fin r, ‖c a‖ ^ (Mdim k r a - 1) :=
  Finset.prod_congr rfl fun a _ => if_pos a.isLt

theorem resG_last (J : Mx k r → E) (c : Fin r → ℂ) (g : Mx k r) :
    Q.resG k r (Fin.last r) J c g = ((∏ a : Fin r, ‖c a‖ ^ (Mdim k r a - 1) : ℝ) : ℂ) • J (wCell k r (Fin.last r) c * g) := by
  unfold Q.resG
  rw [gauge_last]

theorem root_vector_action_cutoff (z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') (hRR : RightRuleE) {f : Mx k r → E}
    (hf : SmoothLev k r 0 D f) (hRf : RightEq k r z' 0 D f) (a b : Fin r) (hab : a.val < b.val) :
    ((EA hD (eI k r a) (eI k r b) : SA E hD) : Module.End ℂ (VS k r 0 D E)) ⟨cut k r 0 D f, cut_mem hD hf⟩ =
      (if b.val = a.val + 1 then (1 : ℂ) else 0) • ⟨cut k r 0 D f, cut_mem hD hf⟩ := by
  apply Subtype.ext
  funext g
  by_cases hg : g ∈ Glev k r 0 ∩ D
  · rw [EA_val, ev_E hD _ _ _ hg]
    have hloc := (good_eh (E := E) hD (cI (eI k r a)) (cI (eI k r b))).loc (cut k r 0 D f) f
      (fun x hx => cut_of_mem f hx) g hg
    simp only [posL_cI] at hloc
    rw [posL_cI, posL_cI]
    show EH k r (eI k r a) (eI k r b) (cut k r 0 D f) g = (if b.val = a.val + 1 then (1 : ℂ) else 0) • cut k r 0 D f g
    rw [hloc, hRR E k r z' D f hz' hD hf hRf g hg a b hab, cut_of_mem f hg]
  · show ((Eh hD (cI (eI k r a)) (cI (eI k r b)) ⟨cut k r 0 D f, cut_mem hD hf⟩ : VS k r 0 D E) : Mx k r → E) g =
      (if b.val = a.val + 1 then (1 : ℂ) else 0) • cut k r 0 D f g
    rw [(Eh hD (cI (eI k r a)) (cI (eI k r b)) ⟨cut k r 0 D f, cut_mem hD hf⟩).2.2 g hg,
      show cut k r 0 D f g = 0 from Set.indicator_of_notMem hg f, smul_zero]

end main

end Formalism.FourierDecayAlt.P.PBN.MC
end
end
