import Mathlib
import Formalism.LocalToGlobal.Columns.RowFormsLemmas
import Formalism.LocalToGlobal.Columns.RowFormsNZs
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Formalism.LocalToGlobal.Columns.CoefColLemmas
import Formalism.LocalToGlobal.Columns.RowFormsNZp
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
import Formalism.LocalToGlobal.Columns.RowForms

section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.DivisionValues

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

open Classical in

def GSD.orbFun (d : S.D) (v : S.V) (x : S.D) : S.V := if hx : ∃ g : S.G, g • d = x then S.ρ hx.choose v else 0

variable {S}

theorem GSD.rho_eq_of_fixed {d : S.D} {v : S.V} (hv : ∀ g : S.G, g • d = d → S.ρ g v = v) {g₁ g₂ : S.G}
    (e : g₁ • d = g₂ • d) : S.ρ g₁ v = S.ρ g₂ v := by
  have h1 : (g₂⁻¹ * g₁) • d = d := by rw [mul_smul, e, inv_smul_smul]
  have h2 : S.ρ g₁ = S.ρ g₂ * S.ρ (g₂⁻¹ * g₁) := by rw [← map_mul, mul_inv_cancel_left]
  rw [h2, Module.End.mul_apply, hv _ h1]

theorem GSD.orbFun_smul {d : S.D} {v : S.V} (hv : ∀ g : S.G, g • d = d → S.ρ g v = v) (g : S.G) :
    S.orbFun d v (g • d) = S.ρ g v := by
  have hx : ∃ g' : S.G, g' • d = g • d := ⟨g, rfl⟩
  unfold GSD.orbFun
  rw [dif_pos hx]
  exact GSD.rho_eq_of_fixed hv hx.choose_spec

theorem GSD.orbFun_mem {d : S.D} {v : S.V} (hv : ∀ g : S.G, g • d = d → S.ρ g v = v) : S.orbFun d v ∈ S.EqFun := by
  intro g x
  by_cases hx : ∃ g' : S.G, g' • d = x
  · obtain ⟨g', rfl⟩ := hx
    rw [← mul_smul, GSD.orbFun_smul hv, GSD.orbFun_smul hv, map_mul, Module.End.mul_apply]
  · have hx' : ¬ ∃ g' : S.G, g' • d = g • x := by
      rintro ⟨g', e⟩
      exact hx ⟨g⁻¹ * g', by rw [mul_smul, e, inv_smul_smul]⟩
    unfold GSD.orbFun
    rw [dif_neg hx, dif_neg hx', map_zero]

theorem GSD.finrank_pos_iff (h : S.Ok) :
    0 < finrank K S.EqFun ↔ ∃ (d : S.D) (v : S.V), v ≠ 0 ∧ ∀ g : S.G, g • d = d → S.ρ g v = v := by
  have := S.finiteDimensional_EqFun h
  rw [Module.finrank_pos_iff_exists_ne_zero]
  constructor
  · rintro ⟨φ, hφ⟩
    have : ∃ d, (φ : S.D → S.V) d ≠ 0 := by
      by_contra hc
      exact hφ (Subtype.ext (funext fun d => by
        by_contra hd
        exact hc ⟨d, hd⟩))
    obtain ⟨d, hd⟩ := this
    refine ⟨d, _, hd, fun g hg => ?_⟩
    have := φ.2 g d
    rw [hg] at this
    exact this.symm
  · rintro ⟨d, v, hv0, hv⟩
    refine ⟨⟨S.orbFun d v, GSD.orbFun_mem hv⟩, fun e => hv0 ?_⟩
    have h1 : S.orbFun d v ((1 : S.G) • d) = 0 := congrFun (congrArg Subtype.val e) ((1 : S.G) • d)
    rw [GSD.orbFun_smul hv, map_one] at h1
    exact h1

end Gen

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

def RowsNonzero (P : LevFam X.E X.K R.r Pr.vGs) : Prop :=
  0 < finrank X.K (MtildeV W Ch sel mu P) ∧ ∀ j, 1 ≤ j → j ≤ R.m → 0 < finrank X.K (MtV W Ch sel mu P j)

end Rows

end Formalism.L2.Col
end
end

section
open MvPolynomial NumberField
open scoped Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.GradedWeylDivisibility

section One

variable (K : Type) [Field K] {n : ℕ}

theorem nz_rowAct_X (s : Equiv.Perm (Fin n)) (v : Fin n × Fin n) :
    rowAct K (n := n) (pM K s)ᵀ (X v) = X (s v.1, v.2) := by
  unfold rowAct
  rw [aeval_X, Finset.sum_eq_single (s v.1)]
  · rw [Matrix.transpose_apply, pM_apply, if_pos rfl, C_1, one_mul]
  · intro b _ hb
    rw [Matrix.transpose_apply, pM_apply, if_neg hb, C_0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem nz_rowAct_minor (s : Equiv.Perm (Fin n)) (i : ℕ) (hi : i ≤ n) :
    rowAct K (n := n) (pM K s)ᵀ (lpMinor K i hi hi) =
      (Matrix.of fun p q : Fin i => (X (s (Fin.castLE hi p), Fin.castLE hi q) : MvPolynomial (Fin n × Fin n) K)).det := by
  unfold lpMinor
  rw [AlgHom.map_det]
  congr 1
  refine Matrix.ext fun p q => ?_
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  exact nz_rowAct_X K s _

theorem nz_minor_swap_in {a b : Fin n} (hab : a < b) (i : ℕ) (hi : i ≤ n) (hb : b.val < i) :
    rowAct K (n := n) (pM K (Equiv.swap a b))ᵀ (lpMinor K i hi hi) = -lpMinor K i hi hi := by
  rw [nz_rowAct_minor]
  have ha : a.val < i := lt_trans hab hb
  have hne : (⟨a.val, ha⟩ : Fin i) ≠ ⟨b.val, hb⟩ := fun h => (ne_of_lt hab) (Fin.ext (Fin.mk.inj_iff.mp h))
  have h1 : (Matrix.of fun p q : Fin i => (X (Equiv.swap a b (Fin.castLE hi p), Fin.castLE hi q) : MvPolynomial (Fin n × Fin n) K)) =
      (Matrix.of fun p q : Fin i => (X (Fin.castLE hi p, Fin.castLE hi q) : MvPolynomial (Fin n × Fin n) K)).submatrix
        (Equiv.swap (⟨a.val, ha⟩ : Fin i) ⟨b.val, hb⟩) id := by
    refine Matrix.ext fun p q => ?_
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id]
    have key : Equiv.swap a b (Fin.castLE hi p) = Fin.castLE hi (Equiv.swap (⟨a.val, ha⟩ : Fin i) ⟨b.val, hb⟩ p) := by
      by_cases hpa : p = ⟨a.val, ha⟩
      · subst hpa
        rw [Equiv.swap_apply_left]
        have : Fin.castLE hi ⟨a.val, ha⟩ = a := Fin.ext rfl
        rw [this, Equiv.swap_apply_left]
        exact Fin.ext rfl
      · by_cases hpb : p = ⟨b.val, hb⟩
        · subst hpb
          rw [Equiv.swap_apply_right]
          have : Fin.castLE hi ⟨b.val, hb⟩ = b := Fin.ext rfl
          rw [this, Equiv.swap_apply_right]
          exact Fin.ext rfl
        · rw [Equiv.swap_apply_of_ne_of_ne hpa hpb, Equiv.swap_apply_of_ne_of_ne]
          · intro h
            exact hpa (Fin.ext (show p.val = a.val from congrArg Fin.val h))
          · intro h
            exact hpb (Fin.ext (show p.val = b.val from congrArg Fin.val h))
    rw [key]
  rw [h1, Matrix.det_permute, Equiv.Perm.sign_swap hne]
  unfold lpMinor
  simp

theorem nz_minor_swap_out {a b : Fin n} (hab : a < b) (i : ℕ) (hi : i ≤ n) (ha : i ≤ a.val) :
    rowAct K (n := n) (pM K (Equiv.swap a b))ᵀ (lpMinor K i hi hi) = lpMinor K i hi hi := by
  rw [nz_rowAct_minor]
  unfold lpMinor
  congr 1
  refine Matrix.ext fun p q => ?_
  simp only [Matrix.of_apply]
  rw [Equiv.swap_apply_of_ne_of_ne]
  · intro h
    have h1 : p.val = a.val := congrArg Fin.val h
    have := p.2
    omega
  · intro h
    have h1 : p.val = b.val := congrArg Fin.val h
    have := p.2
    have h2 : a.val < b.val := hab
    omega

theorem nz_tel (ν : Fin n → ℕ) (hν : Antitone ν) (b : Fin n) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => b ≤ i), (ν i - nuNext ν i) = ν b := by
  obtain ⟨k, hk⟩ : ∃ k, k = n - b.val := ⟨_, rfl⟩
  induction k generalizing b with
  | zero => have := b.2; omega
  | succ k ih =>
    by_cases hb : b.val + 1 < n
    · have hfil : Finset.univ.filter (fun i : Fin n => b ≤ i) =
          insert b (Finset.univ.filter (fun i : Fin n => (⟨b.val + 1, hb⟩ : Fin n) ≤ i)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.le_def, Fin.ext_iff]
        omega
      have hnot : b ∉ Finset.univ.filter (fun i : Fin n => (⟨b.val + 1, hb⟩ : Fin n) ≤ i) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
        omega
      rw [hfil, Finset.sum_insert hnot, ih ⟨b.val + 1, hb⟩ (by simp only; omega)]
      have h1 : nuNext ν b = ν ⟨b.val + 1, hb⟩ := by
        unfold nuNext
        rw [dif_pos hb]
      have h2 : ν ⟨b.val + 1, hb⟩ ≤ ν b := hν (by rw [Fin.le_def]; simp)
      rw [h1]
      omega
    · have hfil : Finset.univ.filter (fun i : Fin n => b ≤ i) = {b} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.le_def, Fin.ext_iff]
        have := i.2
        omega
      have h1 : nuNext ν b = 0 := by
        unfold nuNext
        rw [dif_neg hb]
      rw [hfil, Finset.sum_singleton, h1, Nat.sub_zero]

theorem nz_hw_swap (ν : Fin n → ℕ) (hν : Antitone ν) {a b : Fin n} (hab : a < b) (h : ν a = ν b) :
    rowAct K (n := n) (pM K (Equiv.swap a b))ᵀ (hw K le_rfl ν) = (-1) ^ ν b * hw K le_rfl ν := by
  unfold hw
  rw [map_prod]
  have h1 : ∀ i : Fin n, rowAct K (n := n) (pM K (Equiv.swap a b))ᵀ
      ((lpMinor K (i.val + 1) (by omega) (by omega)) ^ (ν i - nuNext ν i)) =
      (if b ≤ i then (-1 : MvPolynomial (Fin n × Fin n) K) ^ (ν i - nuNext ν i) else 1) *
        (lpMinor K (i.val + 1) (by omega) (by omega)) ^ (ν i - nuNext ν i) := by
    intro i
    rw [map_pow]
    by_cases hbi : b ≤ i
    · rw [if_pos hbi, nz_minor_swap_in K hab _ _ (by rw [Fin.le_def] at hbi; omega), neg_pow]
    · rw [if_neg hbi, one_mul]
      by_cases hai : i < a
      · rw [nz_minor_swap_out K hab _ _ (by rw [Fin.lt_def] at hai; omega)]
      · have hib : i.val + 1 < n := by
          rw [Fin.le_def] at hbi
          have := b.2
          omega
        have e1 : nuNext ν i = ν ⟨i.val + 1, hib⟩ := by
          unfold nuNext
          rw [dif_pos hib]
        have e2 : ν i ≤ ν a := hν (not_lt.mp hai)
        have e3 : ν b ≤ ν ⟨i.val + 1, hib⟩ := hν (by rw [Fin.le_def] at hbi ⊢; simp only; omega)
        have e4 : ν i - nuNext ν i = 0 := by rw [e1]; omega
        rw [e4, pow_zero, pow_zero]
  rw [Finset.prod_congr rfl fun i _ => h1 i, Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_filter, Finset.prod_pow_eq_pow_sum, nz_tel ν hν b]

theorem nz_det_pM (s : Equiv.Perm (Fin n)) : (pM K s).det = ((Equiv.Perm.sign s : ℤˣ) : ℤ) := by
  have h : pM K s = (1 : Matrix (Fin n) (Fin n) K).submatrix (s⁻¹ : Equiv.Perm (Fin n)) id := by
    ext i j
    rw [pM_apply, Matrix.submatrix_apply, Matrix.one_apply, id]
    by_cases hij : i = s j
    · rw [if_pos hij, if_pos (by rw [hij]; simp)]
    · rw [if_neg hij, if_neg (fun h' => hij (by rw [← h']; simp))]
  rw [h, Matrix.det_permute, Matrix.det_one, mul_one, Equiv.Perm.sign_inv]

theorem nz_sqAct_swap (lam : DomWeight n) {a b : Fin n} (hab : a < b) (h : lam.w a = lam.w b) :
    sqAct K n lam (permGL K (Equiv.swap a b)) (extremal K n lam) = ((-1 : K) ^ lam.w b) • extremal K n lam := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) b.2
  have hge : ∀ x : Fin n, lam.detShift ≤ lam.w x := by
    intro x
    unfold DomWeight.detShift
    rw [dif_pos hn]
    exact lam.anti (by rw [Fin.le_def]; have := x.2; simp only; omega)
  have hnat : ∀ x : Fin n, ((lam.natW x : ℕ) : ℤ) = lam.w x - lam.detShift := by
    intro x
    unfold DomWeight.natW
    rw [Int.toNat_of_nonneg (by have := hge x; omega)]
  have hab' : lam.natW a = lam.natW b := by
    have := hnat a
    have := hnat b
    omega
  unfold sqAct extremal
  rw [permGL_val, nz_hw_swap K lam.natW (natW_antitone lam) hab hab']
  have hdet : detPow K n (permGL K (Equiv.swap a b)) lam.detShift = (-1 : K) ^ lam.detShift := by
    unfold detPow
    rw [Units.val_zpow_eq_zpow_val]
    congr 1
    show ((permGL K (Equiv.swap a b) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = -1
    rw [permGL_val, nz_det_pM, Equiv.Perm.sign_swap (ne_of_lt hab)]
    simp
  rw [hdet]
  have hw : lam.w b = lam.detShift + ((lam.natW b : ℕ) : ℤ) := by rw [hnat b]; ring
  rw [hw, zpow_add₀ (by norm_num : (-1 : K) ≠ 0), zpow_natCast, mul_smul]
  congr 1
  rw [smul_eq_C_mul, map_pow, map_neg, C_1]

end One

section All

variable (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ}

def nzExt (lam : ι → DomWeight n) : VV K lam := ⟨extVV K lam, extVV_mem K lam⟩

theorem nzExt_ne_zero (lam : ι → DomWeight n) : nzExt K lam ≠ 0 :=
  fun h => extVV_ne_zero K lam (congrArg Subtype.val h)

theorem nz_prod_zpow (u : K) (hu : u ≠ 0) (f : ι → ℤ) (S : Finset ι) : ∏ τ ∈ S, u ^ f τ = u ^ ∑ τ ∈ S, f τ := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a S ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ hu]

theorem nz_ten_smul (c : ι → K) (f : ι → MvPolynomial (Fin n × Fin n) K) :
    ten (fun τ => c τ • f τ) = (∏ τ, c τ) • ten f := by
  unfold ten
  simp only [map_smul]
  rw [Finset.prod_smul]

theorem nz_rhoK_swap_lt (lam : ι → DomWeight n) {a b : Fin n} (hab : a < b) (h : ∀ τ, (lam τ).w a = (lam τ).w b) :
    rhoK lam (fun _ => permGL K (Equiv.swap a b)) (nzExt K lam) = ((-1 : K) ^ ∑ τ, (lam τ).w b) • nzExt K lam := by
  apply Subtype.ext
  rw [rhoK_coe]
  show actP lam (fun _ => permGL K (Equiv.swap a b)) (ten fun τ => extremal K n (lam τ)) =
    ((-1 : K) ^ ∑ τ, (lam τ).w b) • ten fun τ => extremal K n (lam τ)
  rw [actTen K ι n lam]
  have h1 : (fun τ => sqAct K n (lam τ) (permGL K (Equiv.swap a b)) (extremal K n (lam τ))) =
      fun τ => ((-1 : K) ^ (lam τ).w b) • extremal K n (lam τ) :=
    funext fun τ => nz_sqAct_swap K (lam τ) hab (h τ)
  rw [h1, nz_ten_smul, nz_prod_zpow K (-1) (by norm_num)]

theorem nz_rhoK_swap (lam : ι → DomWeight n) {a b : Fin n} (hab : a ≠ b) (h : ∀ τ, (lam τ).w a = (lam τ).w b)
    (he : Even (∑ τ, (lam τ).w a)) :
    rhoK lam (fun _ => permGL K (Equiv.swap a b)) (nzExt K lam) = nzExt K lam := by
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · have he' : Even (∑ τ, (lam τ).w b) := by
      rw [← Finset.sum_congr rfl fun τ _ => h τ]
      exact he
    rw [nz_rhoK_swap_lt K lam hlt h, he'.neg_one_zpow, one_smul]
  · rw [Equiv.swap_comm, nz_rhoK_swap_lt K lam hlt (fun τ => (h τ).symm), he.neg_one_zpow, one_smul]

theorem nz_rhoK_perm (lam : ι → DomWeight n) (s : Equiv.Perm (Fin n)) (h1 : ∀ τ x, (lam τ).w (s x) = (lam τ).w x)
    (h2 : ∀ x, s x ≠ x → Even (∑ τ, (lam τ).w x)) :
    rhoK lam (fun _ => permGL K s) (nzExt K lam) = nzExt K lam := by
  obtain ⟨k, hk⟩ : ∃ k, s.support.card = k := ⟨_, rfl⟩
  induction k using Nat.strong_induction_on generalizing s with
  | _ k ih =>
    by_cases hs : s = 1
    · subst hs
      have : (fun _ : ι => permGL K (1 : Equiv.Perm (Fin n))) = 1 := by
        funext τ
        rw [map_one]
        rfl
      rw [this, map_one]
      rfl
    · obtain ⟨x, hx⟩ : ∃ x, s x ≠ x := by
        by_contra hc
        push Not at hc
        exact hs (Equiv.ext hc)
      set s' : Equiv.Perm (Fin n) := Equiv.swap x (s x) * s with hs'
      have hcard : s'.support.card < k := by
        rw [← hk]
        exact Equiv.Perm.card_support_swap_mul hx
      have hsw : ∀ τ y, (lam τ).w (Equiv.swap x (s x) y) = (lam τ).w y := by
        intro τ y
        by_cases hy1 : y = x
        · rw [hy1, Equiv.swap_apply_left, h1]
        · by_cases hy2 : y = s x
          · rw [hy2, Equiv.swap_apply_right, h1]
          · rw [Equiv.swap_apply_of_ne_of_ne hy1 hy2]
      have h1' : ∀ τ y, (lam τ).w (s' y) = (lam τ).w y := by
        intro τ y
        rw [hs', Equiv.Perm.mul_apply, hsw, h1]
      have h2' : ∀ y, s' y ≠ y → Even (∑ τ, (lam τ).w y) := by
        intro y hy
        apply h2
        intro hsy
        apply hy
        rw [hs', Equiv.Perm.mul_apply, hsy]
        apply Equiv.swap_apply_of_ne_of_ne
        · intro hyx
          exact hx (by rw [← hyx]; exact hsy)
        · intro hyx
          have : s y = s x := by rw [hsy]; exact hyx
          exact hx (by rw [← s.injective this]; exact hsy)
      have hdec : s = Equiv.swap x (s x) * s' := by
        rw [hs', ← mul_assoc, Equiv.swap_mul_self, one_mul]
      have hfun : (fun _ : ι => permGL K s) =
          (fun _ : ι => permGL K (Equiv.swap x (s x))) * fun _ : ι => permGL K s' := by
        funext τ
        rw [Pi.mul_apply, ← map_mul, ← hdec]
      rw [hfun, map_mul, Module.End.mul_apply, ih _ hcard s' h1' h2' rfl]
      exact nz_rhoK_swap K lam (Ne.symm hx) (fun τ => (h1 τ x).symm) (h2 x hx)

end All

section Emb

variable {E : Type} [Field E] (K : Type) [Field K] {ι : Type} [Fintype ι] {n : ℕ} (emb : ι → E →+* K)

theorem nz_embGL_perm (s : Equiv.Perm (Fin n)) : embGL emb (permGL E s) = fun _ => permGL K s := by
  funext τ
  apply Units.ext
  rw [embGL_coe, permGL_val, permGL_val, pM_map]

theorem nz_invTrK_perm (s : Equiv.Perm (Fin n)) :
    invTrK (fun _ : ι => permGL K s) = fun _ => permGL K s := by
  funext τ
  apply Units.ext
  rw [invTrK_coe, ← map_inv, permGL_val, permGL_val, pM_transpose, inv_inv]

theorem nz_rhoV_perm (lam : ι → DomWeight n) (s : Equiv.Perm (Fin n)) (h1 : ∀ τ x, (lam τ).w (s x) = (lam τ).w x)
    (h2 : ∀ x, s x ≠ x → Even (∑ τ, (lam τ).w x)) :
    rhoV emb lam (permGL E s) (nzExt K lam) = nzExt K lam := by
  show rhoK lam (embGL emb (permGL E s)) (nzExt K lam) = nzExt K lam
  rw [nz_embGL_perm]
  exact nz_rhoK_perm K lam s h1 h2

theorem nz_rhoVr_perm (lam : ι → DomWeight n) (s : Equiv.Perm (Fin n)) (h1 : ∀ τ x, (lam τ).w (s x) = (lam τ).w x)
    (h2 : ∀ x, s x ≠ x → Even (∑ τ, (lam τ).w x)) :
    rhoVr emb lam (permGL E s) (nzExt K lam) = nzExt K lam := by
  show rhoK lam (invTrK (embGL emb (permGL E s))) (nzExt K lam) = nzExt K lam
  rw [nz_embGL_perm, nz_invTrK_perm]
  exact nz_rhoK_perm K lam s h1 h2

end Emb

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions

section PosX

variable (R : Ranks)

def posXn (i : ℕ) : ℕ :=
  if i < R.k - 1 then i
  else if i < R.r then R.k - 1 + (i - (R.k - 1)) * (R.t + 1)
  else R.k - 1 + ((i - R.r) / R.t) * (R.t + 1) + ((i - R.r) % R.t + 1)

def invXn (y : ℕ) : ℕ :=
  if y < R.k - 1 then y
  else if (y - (R.k - 1)) % (R.t + 1) = 0 then R.k - 1 + (y - (R.k - 1)) / (R.t + 1)
  else R.r + ((y - (R.k - 1)) / (R.t + 1)) * R.t + ((y - (R.k - 1)) % (R.t + 1) - 1)

theorem nz_t_pos : 0 < R.t := by
  have := R.rank_add_five_le
  omega

theorem nz_r_eq : R.r = R.k - 1 + R.m := by
  have := R.m_add_three_le_k
  unfold Ranks.r
  omega

theorem nz_rankX : R.N R.m - 1 = R.k - 1 + R.m * (R.t + 1) := by
  have := R.m_add_three_le_k
  unfold Ranks.N
  omega

theorem nz_posXn_hi {i : ℕ} (h : R.r ≤ i) :
    posXn R i = R.k - 1 + ((i - R.r) / R.t) * (R.t + 1) + ((i - R.r) % R.t + 1) := by
  have := nz_r_eq R
  unfold posXn
  rw [if_neg (by omega), if_neg (by omega)]

theorem nz_invXn_posXn (i : ℕ) : invXn R (posXn R i) = i := by
  have hr := nz_r_eq R
  have ht := nz_t_pos R
  by_cases h1 : i < R.k - 1
  · unfold posXn invXn
    rw [if_pos h1, if_pos h1]
  by_cases h2 : i < R.r
  · have e0 : posXn R i = R.k - 1 + (i - (R.k - 1)) * (R.t + 1) := by
      unfold posXn
      rw [if_neg h1, if_pos h2]
    obtain ⟨d1, d2⟩ := divmod (R.t + 1) (i - (R.k - 1)) 0 (by omega)
    have e1 : R.k - 1 + (i - (R.k - 1)) * (R.t + 1) - (R.k - 1) = (i - (R.k - 1)) * (R.t + 1) + 0 := by omega
    unfold invXn
    rw [e0, if_neg (by omega), e1, d1, d2, if_pos rfl]
    omega
  · have hm : (i - R.r) % R.t < R.t := Nat.mod_lt _ ht
    obtain ⟨d1, d2⟩ := divmod (R.t + 1) ((i - R.r) / R.t) ((i - R.r) % R.t + 1) (by omega)
    have e1 : R.k - 1 + ((i - R.r) / R.t) * (R.t + 1) + ((i - R.r) % R.t + 1) - (R.k - 1) =
        ((i - R.r) / R.t) * (R.t + 1) + ((i - R.r) % R.t + 1) := by omega
    have e2 := Nat.div_add_mod (i - R.r) R.t
    rw [Nat.mul_comm] at e2
    unfold invXn
    rw [nz_posXn_hi R (Nat.not_lt.mp h2), if_neg (by omega), e1, d1, d2, if_neg (by omega)]
    omega

theorem nz_posXn_lt {i : ℕ} (h : i < R.N R.m - 1) : posXn R i < R.N R.m - 1 := by
  have hr := nz_r_eq R
  have ht := nz_t_pos R
  have hn := nz_rankX R
  have hn' := rank_X'_eq R
  by_cases h1 : i < R.k - 1
  · unfold posXn
    rw [if_pos h1]
    exact h
  by_cases h2 : i < R.r
  · have h3 : (i - (R.k - 1) + 1) * (R.t + 1) ≤ R.m * (R.t + 1) := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h3
    unfold posXn
    rw [if_neg h1, if_pos h2]
    omega
  · have hm : (i - R.r) % R.t < R.t := Nat.mod_lt _ ht
    have hd : (i - R.r) / R.t < R.m := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
    have h3 : ((i - R.r) / R.t + 1) * (R.t + 1) ≤ R.m * (R.t + 1) := Nat.mul_le_mul_right _ hd
    rw [Nat.add_mul, Nat.one_mul] at h3
    rw [nz_posXn_hi R (Nat.not_lt.mp h2)]
    omega

def posXf (i : Fin (R.N R.m - 1)) : Fin (R.N R.m - 1) := ⟨posXn R i.1, nz_posXn_lt R i.2⟩

theorem nz_posXf_inj : Function.Injective (posXf R) := by
  intro a b h
  have h1 : posXn R a.1 = posXn R b.1 := congrArg Fin.val h
  apply Fin.ext
  rw [← nz_invXn_posXn R a.1, ← nz_invXn_posXn R b.1, h1]

def posX : Equiv.Perm (Fin (R.N R.m - 1)) :=
  Equiv.ofBijective (posXf R) (Finite.injective_iff_bijective.mp (nz_posXf_inj R))

theorem nz_posX_val (i : Fin (R.N R.m - 1)) : (posX R i).1 = posXn R i.1 := rfl

theorem nz_coarseX {a : ℕ} (h1 : R.r ≤ a) (h2 : a < R.N R.m - 1) :
    coarse R.r (List.replicate R.m R.t) a = (a - R.r) / R.t + 1 := by
  have hn' := rank_X'_eq R
  rw [coarse_of_le h1, blkIdx_replicate (nz_t_pos R) R.m (a - R.r) (by omega)]

def sX (B : ℕ) : ℚ := ((R.t : ℚ) - 1) / 2 - (((R.N R.m - 1 : ℕ) : ℚ) - 1) / 2 + (R.k : ℚ) + (B : ℚ) * ((R.t : ℚ) + 1)

theorem nz_sX_int (B : ℕ) : ∃ z : ℤ, sX R B = z := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨c, hc⟩ := R.t_odd
  have hk := R.m_add_three_le_k
  have hn : ((R.N R.m - 1 : ℕ) : ℚ) = (R.k : ℚ) + (R.m : ℚ) * ((R.t : ℚ) + 1) - 1 := by
    have : R.N R.m - 1 + 1 = R.k + R.m * (R.t + 1) := by
      unfold Ranks.N
      omega
    have h2 : ((R.N R.m - 1 + 1 : ℕ) : ℚ) = ((R.k + R.m * (R.t + 1) : ℕ) : ℚ) := by rw [this]
    push_cast at h2
    linarith
  unfold sX
  rw [hn, ha, hc]
  exact ⟨(c : ℤ) - ((a : ℤ) + (R.m : ℤ) * ((c : ℤ) + 1) - 1) + ((a : ℤ) + a) + (B : ℤ) * (2 * (c : ℤ) + 1 + 1), by push_cast; ring⟩

variable {R}

theorem RowPar.nz_sgTrue_pos (P : HCParam R) (a : Fin (R.N R.m - 1)) (h : R.r ≤ a.1) :
    (((RowPar.of P).sgTrue).w (posX R a) : ℚ) = -(RowPar.of P).eAt ((a.1 - R.r) / R.t) + sX R ((a.1 - R.r) / R.t) := by
  have ht := nz_t_pos R
  have hk := R.m_add_three_le_k
  have hm : (a.1 - R.r) % R.t < R.t := Nat.mod_lt _ ht
  rw [RowPar.sgTrue_eq P (posX R a), nz_posX_val, nz_posXn_hi R h,
    RowPar.sgHC_e _ ((a.1 - R.r) / R.t) ((a.1 - R.r) % R.t + 1) (by omega) (by omega)]
  unfold rhoVec sX
  rw [nz_posX_val, nz_posXn_hi R h]
  have hk1 : ((R.k - 1 : ℕ) : ℚ) = (R.k : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  push_cast
  rw [hk1]
  ring

end PosX

section WtsX

variable {X : Fields} {Word : Type} {R : Ranks} {W : Wts X Word R}

theorem nz_sg_val (hW : W.Ok) (τ : X.Tau) (a : Fin (R.N R.m - 1)) (h : R.r ≤ a.1) :
    ((W.sgTrue τ).w (posX R a) : ℚ) = -(W.row τ).eAt ((a.1 - R.r) / R.t) + sX R ((a.1 - R.r) / R.t) := by
  obtain ⟨P, hP⟩ := hW.row_ok τ
  unfold Wts.sgTrue
  rw [← hP]
  exact RowPar.nz_sgTrue_pos P a h

theorem nz_sg_const (hW : W.Ok) (τ : X.Tau) (a b : Fin (R.N R.m - 1)) (ha : R.r ≤ a.1) (hb : R.r ≤ b.1)
    (hab : coarse R.r (List.replicate R.m R.t) a.1 = coarse R.r (List.replicate R.m R.t) b.1) :
    (W.sgTrue τ).w (posX R a) = (W.sgTrue τ).w (posX R b) := by
  rw [nz_coarseX R ha a.2, nz_coarseX R hb b.2] at hab
  have h1 : (a.1 - R.r) / R.t = (b.1 - R.r) / R.t := by omega
  have h2 : ((W.sgTrue τ).w (posX R a) : ℚ) = ((W.sgTrue τ).w (posX R b) : ℚ) := by
    rw [nz_sg_val hW τ a ha, nz_sg_val hW τ b hb, h1]
  exact_mod_cast h2

theorem nz_sg_even (hW : W.Ok) (hf : Even X.f) (he : ∀ j : Fin R.m, ∃ z : ℤ, ∑ τ, (W.row τ).e j = 2 * (z : ℚ))
    (a : Fin (R.N R.m - 1)) (ha : R.r ≤ a.1) : Even (∑ τ, (W.sgTrue τ).w (posX R a)) := by
  have hn' := rank_X'_eq R
  have hB : (a.1 - R.r) / R.t < R.m := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; have := a.2; omega)
  obtain ⟨z, hz⟩ := he ⟨(a.1 - R.r) / R.t, hB⟩
  obtain ⟨y, hy⟩ := nz_sX_int R ((a.1 - R.r) / R.t)
  obtain ⟨c, hc⟩ := hf
  have h1 : ((∑ τ, (W.sgTrue τ).w (posX R a) : ℤ) : ℚ) = ((2 * (-z + (c : ℤ) * y) : ℤ) : ℚ) := by
    push_cast
    rw [Finset.sum_congr rfl fun τ _ => nz_sg_val hW τ a ha, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_const, Finset.card_univ]
    have h2 : ∑ τ, (W.row τ).eAt ((a.1 - R.r) / R.t) = 2 * (z : ℚ) := by
      rw [← hz]
      refine Finset.sum_congr rfl fun τ _ => ?_
      unfold RowPar.eAt
      rw [dif_pos hB]
    have h3 : Fintype.card X.Tau = c + c := hc
    rw [h2, h3, hy, nsmul_eq_mul]
    push_cast
    ring
  have h4 : ∑ τ, (W.sgTrue τ).w (posX R a) = 2 * (-z + (c : ℤ) * y) := by exact_mod_cast h1
  rw [h4]
  exact even_two_mul _

end WtsX

section PosV

variable (R : Ranks) (j : ℕ)

def pV : ℕ := min (RowPar.pOf R j) R.r

def posVn (i : ℕ) : ℕ :=
  if i < pV R j then i else if i < R.r then i + R.t else i - R.r + pV R j

theorem nz_pV_le : pV R j ≤ R.r := min_le_right _ _

theorem nz_posVn_lt {i : ℕ} (h : i < R.nV) : posVn R j i < R.nV := by
  have h1 := nz_pV_le R j
  unfold Ranks.nV at h ⊢
  unfold posVn
  split_ifs <;> omega

def posVf (i : Fin R.nV) : Fin R.nV := ⟨posVn R j i.1, nz_posVn_lt R j i.2⟩

theorem nz_posVf_inj : Function.Injective (posVf R j) := by
  intro a b h
  have h1 : posVn R j a.1 = posVn R j b.1 := congrArg Fin.val h
  have h2 := nz_pV_le R j
  have ha := a.2
  have hb := b.2
  unfold Ranks.nV at ha hb
  apply Fin.ext
  unfold posVn at h1
  split_ifs at h1 <;> omega

def posV : Equiv.Perm (Fin R.nV) :=
  Equiv.ofBijective (posVf R j) (Finite.injective_iff_bijective.mp (nz_posVf_inj R j))

theorem nz_posV_val (i : Fin R.nV) : (posV R j i).1 = posVn R j i.1 := rfl

variable {R j}

theorem nz_pV_eq (h2 : j ≤ R.m) : pV R j = RowPar.pOf R j := by
  have := R.m_add_three_le_k
  unfold pV RowPar.pOf Ranks.r
  omega

def sV (R : Ranks) (j : ℕ) : ℚ := ((R.k : ℚ) - (R.m : ℚ)) / 2 + (j : ℚ) - 1

theorem nz_sV_int (R : Ranks) (j : ℕ) : ∃ z : ℤ, sV R j = z := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  unfold sV
  rw [ha, hb]
  exact ⟨(a : ℤ) - b + j - 1, by push_cast; ring⟩

theorem RowPar.nz_lamVQ_pos (S : RowPar R) (h1 : 1 ≤ j) (h2 : j ≤ R.m) (a : Fin R.nV) (h : R.r ≤ a.1) :
    S.lamVQ j (posV R j a) = -S.eAt (j - 1) + sV R j := by
  have hp := nz_pV_eq h2
  have hle := nz_pV_le R j
  have ha := a.2
  unfold Ranks.nV at ha
  have e : (posV R j a).1 = a.1 - R.r + RowPar.pOf R j := by
    rw [nz_posV_val]
    unfold posVn
    rw [if_neg (by omega), if_neg (by omega), hp]
  unfold RowPar.lamVQ
  rw [e, if_neg (by omega), if_pos (by omega)]
  unfold RowPar.dV sV
  rw [RowPar.cast_pOf h1, RowPar.cast_qOf h2]
  ring

end PosV

section WtsV

variable {X : Fields} {Word : Type} {R : Ranks} {W : Wts X Word R} {j : ℕ}

theorem nz_lamV_val (hW : W.Ok) (h1 : 1 ≤ j) (h2 : j ≤ R.m) (τ : X.Tau) (a : Fin R.nV) (h : R.r ≤ a.1) :
    ((W.lamV j τ).w (posV R j a) : ℚ) = -(W.row τ).eAt (j - 1) + sV R j := by
  rw [Wts.lamV_eq hW h1 h2 τ (posV R j a)]
  exact RowPar.nz_lamVQ_pos _ h1 h2 a h

theorem nz_lamV_const (hW : W.Ok) (h1 : 1 ≤ j) (h2 : j ≤ R.m) (τ : X.Tau) (a b : Fin R.nV) (ha : R.r ≤ a.1)
    (hb : R.r ≤ b.1) : (W.lamV j τ).w (posV R j a) = (W.lamV j τ).w (posV R j b) := by
  have h3 : ((W.lamV j τ).w (posV R j a) : ℚ) = ((W.lamV j τ).w (posV R j b) : ℚ) := by
    rw [nz_lamV_val hW h1 h2 τ a ha, nz_lamV_val hW h1 h2 τ b hb]
  exact_mod_cast h3

theorem nz_lamV_even (hW : W.Ok) (hf : Even X.f) (he : ∀ j : Fin R.m, ∃ z : ℤ, ∑ τ, (W.row τ).e j = 2 * (z : ℚ))
    (h1 : 1 ≤ j) (h2 : j ≤ R.m) (a : Fin R.nV) (ha : R.r ≤ a.1) : Even (∑ τ, (W.lamV j τ).w (posV R j a)) := by
  have hB : j - 1 < R.m := by omega
  obtain ⟨z, hz⟩ := he ⟨j - 1, hB⟩
  obtain ⟨y, hy⟩ := nz_sV_int R j
  obtain ⟨c, hc⟩ := hf
  have h3 : ((∑ τ, (W.lamV j τ).w (posV R j a) : ℤ) : ℚ) = ((2 * (-z + (c : ℤ) * y) : ℤ) : ℚ) := by
    push_cast
    rw [Finset.sum_congr rfl fun τ _ => nz_lamV_val hW h1 h2 τ a ha, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_const, Finset.card_univ]
    have h4 : ∑ τ, (W.row τ).eAt (j - 1) = 2 * (z : ℚ) := by
      rw [← hz]
      refine Finset.sum_congr rfl fun τ _ => ?_
      unfold RowPar.eAt
      rw [dif_pos hB]
    have h5 : Fintype.card X.Tau = c + c := hc
    rw [h4, h5, hy, nsmul_eq_mul]
    push_cast
    ring
  have h6 : ∑ τ, (W.lamV j τ).w (posV R j a) = 2 * (-z + (c : ℤ) * y) := by exact_mod_cast h3
  rw [h6]
  exact even_two_mul _

end WtsV

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Chr

variable {n : ℕ}

theorem nz_pM_bt (κ : Type) [CommRing κ] {β : ℕ → ℕ} (s : Equiv.Perm (Fin n)) (hβ : ∀ b : Fin n, β (s b).val = β b.val) :
    permGL κ s ∈ btG n κ β := by
  rw [mem_btG]
  intro i j hij
  rw [permGL_val, pM_apply, if_neg]
  intro h
  rw [h, hβ] at hij
  exact lt_irrefl _ hij

def sgnU (κ : Type) [CommRing κ] : ℤˣ →* κˣ := Units.map (Int.castRingHom κ).toMonoidHom

theorem sgnU_eq (κ : Type) [CommRing κ] (ε : ℤˣ) : sgnU κ ε = 1 ∨ sgnU κ ε = -1 := by
  rcases Int.units_eq_one_or ε with h | h
  · left; rw [h, map_one]
  · right
    rw [h]
    apply Units.ext
    simp [sgnU]

theorem nz_blkDet {β : ℕ → ℕ} (s : Equiv.Perm (Fin n)) (hβ : ∀ b : Fin n, β (s b).val = β b.val) (c : ℕ) :
    ∃ ε : ℤˣ, ∀ (κ : Type) [CommRing κ] (hM : permGL κ s ∈ btG n κ β), blkDet n κ β c ⟨permGL κ s, hM⟩ = sgnU κ ε := by
  refine ⟨blkDet n ℤ β c ⟨permGL ℤ s, nz_pM_bt ℤ s hβ⟩, fun κ _ hM => ?_⟩
  apply Units.ext
  show _ = (Int.castRingHom κ) ((blkDet n ℤ β c ⟨permGL ℤ s, nz_pM_bt ℤ s hβ⟩ : ℤˣ) : ℤ)
  rw [blkDet_val, blkDet_val, RingHom.map_det]
  congr 1
  ext i j
  show pM κ s i.1 j.1 = (Int.castRingHom κ) (pM ℤ s i.1 j.1)
  rw [pM_apply, pM_apply]
  split_ifs <;> simp

theorem blockZero_permutation_eq_one {κ : Type} [CommRing κ] {r : ℕ} (h : r ≤ n) (bl : List ℕ) (s : Equiv.Perm (Fin n))
    (hfix : ∀ b : Fin n, b.val < r → s b = b) (hM : permGL κ s ∈ blockUT n κ r bl) :
    blk0 n κ h bl ⟨permGL κ s, hM⟩ = 1 := by
  apply Units.ext
  ext i j
  rw [blockZero_val]
  show pM κ s (Fin.castLE h i) (Fin.castLE h j) = (1 : Matrix (Fin r) (Fin r) κ) i j
  rw [pM_apply, hfix _ (show (Fin.castLE h j).val < r from j.2), Matrix.one_apply]
  by_cases hij : i = j
  · rw [if_pos hij, if_pos (by rw [hij])]
  · rw [if_neg hij, if_neg (fun hc => hij (Fin.castLE_injective h hc))]

variable {κ K : Type} [CommRing κ] [Field K]

theorem nz_lamPar_ev {r : ℕ} (h : r ≤ n) (bl : List ℕ) (H₀ : Subgroup (GL (Fin r) κ)) (lam₀ : ↥H₀ →* Kˣ) (χ : ℕ → κˣ →* Kˣ)
    (s : Equiv.Perm (Fin n)) (hfix : ∀ b : Fin n, b.val < r → s b = b)
    (hco : ∀ b : Fin n, coarse r bl (s b).val = coarse r bl b.val) (hχ : ∀ (c : ℕ) (ε : ℤˣ), χ c (sgnU κ ε) = 1) :
    (⟨HPar n κ h bl H₀, lamPar h bl lam₀ χ⟩ : Lev κ K n).ev (permGL κ s) = 1 := by
  by_cases hm : permGL κ s ∈ HPar n κ h bl H₀
  · rw [Lev.ev_of_mem _ hm]
    show lamPar h bl lam₀ χ ⟨permGL κ s, hm⟩ = 1
    rw [lamPar_apply, detChar_apply]
    have h1 : (⟨blk0 n κ h bl ⟨permGL κ s, HPar_le h bl H₀ hm⟩, (mem_HPar.mp hm).2⟩ : ↥H₀) = 1 :=
      Subtype.ext (blockZero_permutation_eq_one h bl s hfix _)
    rw [h1, map_one, one_mul]
    refine Finset.prod_eq_one fun c _ => ?_
    obtain ⟨ε, hε⟩ := nz_blkDet (β := coarse r bl) s hco (c + 1)
    rw [hε κ, hχ]
  · exact dif_neg hm

theorem nz_coarse_two {a b x : ℕ} (hx : x < a + b) : coarse a [b] x = if x < a then 0 else 1 := by
  by_cases h : x < a
  · rw [if_pos h, coarse_of_lt h]
  · rw [if_neg h, coarse_of_le (Nat.not_lt.mp h)]
    have : x - a < b := by omega
    simp [blkIdx, this]

theorem nz_coarse_two_perm {a b : ℕ} (hn : n ≤ a + b) (s : Equiv.Perm (Fin n)) (hfix : ∀ x : Fin n, x.val < a → s x = x)
    (x : Fin n) : coarse a [b] (s x).val = coarse a [b] x.val := by
  rw [nz_coarse_two (lt_of_lt_of_le (s x).2 hn), nz_coarse_two (lt_of_lt_of_le x.2 hn)]
  have := nz_ge_of_fix s hfix x
  by_cases h : x.val < a
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

theorem nz_lamQ_ev {a b : ℕ} (hn : n ≤ a + b) (s : Equiv.Perm (Fin n)) (hfix : ∀ x : Fin n, x.val < a → s x = x) :
    ∃ ε : ℤˣ, ∀ (κ : Type) [CommRing κ] (ξ : κˣ →* Kˣ),
      (⟨HQ κ n a b, lamQ ξ n a b⟩ : Lev κ K n).ev (permGL κ s) = ξ (sgnU κ ε) := by
  obtain ⟨ε, hε⟩ := nz_blkDet (β := coarse a [b]) s (nz_coarse_two_perm hn s hfix) 1
  refine ⟨ε, fun κ _ ξ => ?_⟩
  have hm : permGL κ s ∈ HQ κ n a b := nz_pM_bt κ s (nz_coarse_two_perm hn s hfix)
  rw [Lev.ev_of_mem _ hm]
  show lamQ ξ n a b ⟨permGL κ s, hm⟩ = _
  rw [lamQ_apply, hε κ]

end Chr

section Gen

variable {X : Fields} {n : ℕ} [NeZero n] {SG : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem nz_form_pos (C : CoefPk X n (DecoSet X.E n ∅ SG)) (Λ : LevFam X.E X.K n SG) (hOk : (formGSD C Λ).Ok) (hX : X.Ok)
    (pos : Equiv.Perm (Fin n)) {r : ℕ} (bl : List ℕ) (i0 : Fin n) (hi : i0.val < r)
    (w1 w2 : SG) (hne : w2 ≠ w1) {g1 g2 : ℕ} (hg1 : g1.Prime) (hg2 : g2.Prime)
    (hgw1 : (g1 : 𝓞 X.E) ∈ w1.1.asIdeal) (hgw2 : (g2 : 𝓞 X.E) ∈ w2.1.asIdeal) (hb1 : 2 * X.f + 1 < g1)
    (hb2 : 2 * X.f + 1 < g2) (hΛ2 : (Λ w2).H ≤ uniUT n _ r bl) (hΛ1 : (Λ w1).H ≤ blockUT n _ r bl)
    (v : C.V) (hv : v ≠ 0)
    (hrho : ∀ (s : Equiv.Perm (Fin n)) (γ : UF X.E n), (∀ b : Fin n, b.val < r → s b = b) →
      (∀ b : Fin n, coarse r bl (s b).val = coarse r bl b.val) → ufGL X.E n γ = permGL X.E (pos * s * pos⁻¹) → C.rho γ v = v)
    (hchr : ∀ (s : Equiv.Perm (Fin n)) (h : ↥Λ.grp), (∀ b : Fin n, b.val < r → s b = b) →
      (∀ b : Fin n, coarse r bl (s b).val = coarse r bl b.val) → (∀ w, h.1 w = permGL _ s) → Λ.chr h = 1) :
    0 < finrank X.K (formGSD C Λ).EqFun := by
  refine (GSD.finrank_pos_iff hOk).mpr ⟨nzPt (nzFr pos i0 hi w1), v, hv, fun g hg => ?_⟩
  obtain ⟨s, hfix, hco, hγ, hh⟩ := nz_stab_perm hX pos bl i0 hi w1 w2 hne hg1 hg2 hgw1 hgw2 hb1 hb2 g.1 g.2.1
    (hΛ2 (Λ.mem_at g.2 w2)) (hΛ1 (Λ.mem_at g.2 w1)) hg
  show ((Λ.chr g.2 : X.Kˣ) : X.K) • C.rho g.1 v = v
  rw [hchr s g.2 hfix hco hh, hrho s g.1 hfix hco hγ, Units.val_one, one_smul]

end Gen

section Signs

variable {X : Fields} {Pr : Primes X} {R : Ranks}

open Classical in
theorem nz_mem_vG {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vGs) : ∃ i, w ∈ Pr.vG i := by
  unfold Primes.vGs at hw
  rcases Finset.mem_union.mp hw with h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩

theorem nz_chi_neg_one {m : ℕ} {Ch : Chars X Pr m} (hPr : Pr.Ok) (hCh : Ch.Ok) (w : {w // w ∈ Pr.vGs}) (j : Fin m) :
    Ch.chi j w (-1) = 1 := by
  obtain ⟨i, hi⟩ := nz_mem_vG w.2
  obtain ⟨om, -, hom⟩ := hCh.chi_om i
  have hp : Fact (Pr.g i).Prime := ⟨hPr.g_prime i⟩
  have hg0 : ((Pr.g i : ℕ) : 𝓞 X.E ⧸ w.1.asIdeal) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.mpr (hPr.g_mem hi)
    rwa [map_natCast] at this
  have hval : (((-1 : (ZMod (Pr.g i))ˣ) : ZMod (Pr.g i))).val = Pr.g i - 1 := by
    rw [Units.val_neg, Units.val_one, ZMod.neg_val, if_neg one_ne_zero, ZMod.val_one]
  rw [hom w hi j (-1) (-1) (by
    rw [hval, Nat.cast_sub (hPr.g_prime i).one_le, hg0, Nat.cast_one, zero_sub, Units.val_neg, Units.val_one])]
  rw [pow_mul, ← map_pow, neg_one_sq, map_one, one_pow]

theorem nz_chiAt_sgn {Ch : Chars X Pr R.m} (hPr : Pr.Ok) (hCh : Ch.Ok) (w : {w // w ∈ Pr.vGs}) (c : ℕ) (ε : ℤˣ) :
    chiAt Ch w c (sgnU _ ε) = 1 := by
  rcases sgnU_eq (𝓞 X.E ⧸ w.1.asIdeal) ε with h | h
  · rw [h, map_one]
  · rw [h]
    unfold chiAt extChi
    split_ifs
    · exact nz_chi_neg_one hPr hCh w _
    · rfl

open Classical in

def XiSign (Pr : Primes X) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (ξ : Chr X.F X.E X.K) : Prop :=
  ∏ P ∈ QE sel ξ \ Pr.vGs, resChar ξ P (-1) = 1

open Classical in
theorem XiSign.prod {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {ξ : Chr X.F X.E X.K}
    (h : XiSign Pr sel ξ) (ε : ℤˣ) :
    (∏ w : uSG Pr.vGs (QE sel ξ), if w.1 ∈ Pr.vGs then (1 : X.Kˣ) else resChar ξ w.1 (sgnU _ ε)) = 1 := by
  rcases Int.units_eq_one_or ε with he | he
  · refine Finset.prod_eq_one fun w _ => ?_
    rw [he, map_one, map_one, ite_self]
  · have h1 : ∀ w : HeightOneSpectrum (𝓞 X.E), sgnU (𝓞 X.E ⧸ w.asIdeal) ε = -1 := by
      intro w
      rw [he]
      apply Units.ext
      simp [sgnU]
    simp only [h1]
    rw [Finset.prod_coe_sort (uSG Pr.vGs (QE sel ξ))
      (fun w => if w ∈ Pr.vGs then (1 : X.Kˣ) else resChar ξ w (-1)), Finset.prod_ite, Finset.prod_const_one, one_mul]
    have h2 : (uSG Pr.vGs (QE sel ξ)).filter (fun w => ¬ w ∈ Pr.vGs) = QE sel ξ \ Pr.vGs := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
      tauto
    rw [h2]
    exact h

theorem signCondition_trivialTuple (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) :
    XiSign Pr sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K) := by
  unfold XiSign
  rw [twistPrimes_trivialTuple_empty]
  simp

theorem nz_two_primes (hX : X.Ok) (hPr : Pr.Ok) : ∃ w1 ∈ Pr.vG 0, ∃ w2 ∈ Pr.vG 1, w2 ≠ w1 := by
  have hc : ∀ i, (Pr.vG i).Nonempty := fun i => by
    rw [← Finset.card_pos, hPr.vG_card]
    exact hX.f_pos
  obtain ⟨w1, h1⟩ := hc 0
  obtain ⟨w2, h2⟩ := hc 1
  refine ⟨w1, h1, w2, h2, fun h => hPr.g_ne ?_⟩
  rw [← hPr.vG_norm 0 w1 h1, ← hPr.vG_norm 1 w2 h2, h]

end Signs

section Final

theorem HPar_mono {κ : Type} [CommRing κ] {n r : ℕ} (h : r ≤ n) (bl : List ℕ) {H₀ H₁ : Subgroup (GL (Fin r) κ)} (hH : H₀ ≤ H₁) :
    HPar n κ h bl H₀ ≤ HPar n κ h bl H₁ := fun _ hM => by
  obtain ⟨h1, h2⟩ := mem_HPar.mp hM
  exact mem_HPar.mpr ⟨h1, hH h2⟩

theorem nz_r_pos (R : Ranks) : 0 < R.r := by
  have := R.m_add_three_le_k
  unfold Ranks.r
  omega

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

open Classical in

theorem mtilde_finrank_pos' (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hW : W.Ok)
    (hpar : ∀ a : Fin (R.N R.m - 1), R.r ≤ a.val → Even (∑ τ, (W.sgTrue τ).w (posX R a))) (hg : ∀ i, 2 * X.f + 1 < Pr.g i)
    (hξ : XiSign Pr sel (mu : Chr X.F X.E X.K)) (P : LevFam X.E X.K R.r Pr.vGs) (hP : ∀ w, (P w).H ≤ HU _ R.r) :
    0 < finrank X.K (MtildeV W Ch sel mu P) := by
  have : NeZero (R.N R.m - 1) := ⟨(X'_pos R).ne'⟩
  obtain ⟨w1, h1, w2, h2, hne⟩ := nz_two_primes hX hPr
  have m1 : w1 ∈ Pr.vGs := Finset.mem_union_left _ h1
  have m2 : w2 ∈ Pr.vGs := Finset.mem_union_right _ h2
  let W1 : rowSG Pr sel mu := ⟨w1, Finset.mem_union_left _ m1⟩
  let W2 : rowSG Pr sel mu := ⟨w2, Finset.mem_union_left _ m2⟩
  refine nz_form_pos (rowVal W _) (rowTy Ch sel mu P).inv (mtildeOk W Ch sel mu hX P) hX (posX R) (List.replicate R.m R.t)
    ⟨0, X'_pos R⟩ (nz_r_pos R) W1 W2 (fun h => hne (congrArg Subtype.val h)) (hPr.g_prime 0) (hPr.g_prime 1) (hPr.g_mem h1)
    (hPr.g_mem h2) (hg 0) (hg 1) ?_ ?_ (nzExt X.K W.sgTrue) (nzExt_ne_zero _ _) ?_ ?_
  · show (rowTy Ch sel mu P W2).H ≤ _
    rw [rowTy, LevFam.glue_of_mem _ _ W2 m2, uniUT_eq_HPar (r_le_X' R)]
    exact HPar_mono _ _ (hP _)
  · show (rowTy Ch sel mu P W1).H ≤ _
    rw [rowTy, LevFam.glue_of_mem _ _ W1 m1]
    exact HPar_le _ _ _
  · intro s γ hfix hco hγ
    show rhoV X.emb W.sgTrue (ufGL X.E _ γ) (nzExt X.K W.sgTrue) = _
    rw [hγ]
    have hx : ∀ x, (posX R * s * (posX R)⁻¹) x = posX R (s ((posX R)⁻¹ x)) := fun _ => rfl
    have hx' : ∀ x, posX R ((posX R)⁻¹ x) = x := fun x => by simp
    apply nz_rhoV_perm
    · intro τ x
      rw [hx]
      by_cases hb : ((posX R)⁻¹ x).val < R.r
      · rw [hfix _ hb, hx']
      · rw [nz_sg_const hW τ _ _ ((nz_ge_of_fix s hfix _).mpr (Nat.not_lt.mp hb)) (Nat.not_lt.mp hb) (hco _), hx']
    · intro x hne'
      rw [hx] at hne'
      have hb : ¬ ((posX R)⁻¹ x).val < R.r := fun hb => hne' (by rw [hfix _ hb, hx'])
      have := hpar _ (Nat.not_lt.mp hb)
      rwa [hx'] at this
  · intro s h hfix hco hh
    obtain ⟨ε, hε⟩ := nz_lamQ_ev (K := X.K) (a := R.r) (b := R.m * R.t) (le_of_eq (rank_X'_eq R)) s hfix
    have key : ∀ w : rowSG Pr sel mu, ((rowTy Ch sel mu P).inv w).ev (h.1 w) =
        if w.1 ∈ Pr.vGs then (1 : X.Kˣ) else resChar (mu : Chr X.F X.E X.K) w.1 (sgnU _ ε) := by
      intro w
      rw [hh w]
      show ((rowTy Ch sel mu P w).inv).ev _ = _
      rw [Lev.inv_ev]
      by_cases hw : w.1 ∈ Pr.vGs
      · rw [if_pos hw, rowTy, LevFam.glue_of_mem _ _ w hw]
        show ((⟨HPar _ _ (r_le_X' R) (List.replicate R.m R.t) (P ⟨w.1, hw⟩).H,
          lamPar (r_le_X' R) (List.replicate R.m R.t) (P ⟨w.1, hw⟩).lam (chiAt Ch ⟨w.1, hw⟩)⟩ : Lev _ X.K _).ev _)⁻¹ = 1
        rw [nz_lamPar_ev _ _ _ _ _ s hfix hco (nz_chiAt_sgn hPr hCh ⟨w.1, hw⟩), inv_one]
      · rw [if_neg hw, rowTy, LevFam.glue_of_not _ _ w hw]
        show (((⟨HQ _ _ R.r (R.m * R.t), lamQ (resChar (mu : Chr X.F X.E X.K) w.1) _ R.r (R.m * R.t)⟩ :
          Lev _ X.K _).inv).ev _)⁻¹ = _
        rw [Lev.inv_ev, inv_inv, hε]
    rw [LevFam.chr_ev, Finset.prod_congr rfl fun w _ => key w]
    exact hξ.prod ε

open Classical in

theorem mt_finrank_pos' (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hW : W.Ok) (hg : ∀ i, 2 * X.f + 1 < Pr.g i)
    (hξ : XiSign Pr sel (mu : Chr X.F X.E X.K)) (P : LevFam X.E X.K R.r Pr.vGs) (hP : ∀ w, (P w).H ≤ HU _ R.r)
    (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ R.m)
    (hpar : ∀ a : Fin R.nV, R.r ≤ a.val → Even (∑ τ, (W.lamV j τ).w (posV R j a))) :
    0 < finrank X.K (MtV W Ch sel mu P j) := by
  have : NeZero R.nV := ⟨(nV_pos R).ne'⟩
  obtain ⟨w1, h1, w2, h2, hne⟩ := nz_two_primes hX hPr
  have m1 : w1 ∈ Pr.vGs := Finset.mem_union_left _ h1
  have m2 : w2 ∈ Pr.vGs := Finset.mem_union_right _ h2
  let W1 : rowSG Pr sel mu := ⟨w1, Finset.mem_union_left _ m1⟩
  let W2 : rowSG Pr sel mu := ⟨w2, Finset.mem_union_left _ m2⟩
  refine nz_form_pos (mtVal W j _) (mtTy Ch sel mu P j).inv (mtOk W Ch sel mu hX P j) hX (posV R j) [R.t]
    ⟨0, nV_pos R⟩ (nz_r_pos R) W1 W2 (fun h => hne (congrArg Subtype.val h)) (hPr.g_prime 0) (hPr.g_prime 1) (hPr.g_mem h1)
    (hPr.g_mem h2) (hg 0) (hg 1) ?_ ?_ (nzExt X.K (W.lamV j)) (nzExt_ne_zero _ _) ?_ ?_
  · show (mtTy Ch sel mu P j W2).H ≤ _
    rw [mtTy, LevFam.glue_of_mem _ _ W2 m2, uniUT_eq_HPar (r_le_nV R)]
    exact HPar_mono _ _ (hP _)
  · show (mtTy Ch sel mu P j W1).H ≤ _
    rw [mtTy, LevFam.glue_of_mem _ _ W1 m1]
    exact HPar_le _ _ _
  · intro s γ hfix hco hγ
    show rhoVr X.emb (W.lamV j) (ufGL X.E _ γ) (nzExt X.K (W.lamV j)) = _
    rw [hγ]
    have hx : ∀ x, (posV R j * s * (posV R j)⁻¹) x = posV R j (s ((posV R j)⁻¹ x)) := fun _ => rfl
    have hx' : ∀ x, posV R j ((posV R j)⁻¹ x) = x := fun x => by simp
    apply nz_rhoVr_perm
    · intro τ x
      rw [hx]
      by_cases hb : ((posV R j)⁻¹ x).val < R.r
      · rw [hfix _ hb, hx']
      · rw [nz_lamV_const hW hj1 hj2 τ _ _ ((nz_ge_of_fix s hfix _).mpr (Nat.not_lt.mp hb)) (Nat.not_lt.mp hb), hx']
    · intro x hne'
      rw [hx] at hne'
      have hb : ¬ ((posV R j)⁻¹ x).val < R.r := fun hb => hne' (by rw [hfix _ hb, hx'])
      have := hpar _ (Nat.not_lt.mp hb)
      rwa [hx'] at this
  · intro s h hfix hco hh
    obtain ⟨ε, hε⟩ := nz_lamQ_ev (K := X.K) (a := R.r) (b := R.t) (le_refl R.nV) s hfix
    have key : ∀ w : rowSG Pr sel mu, ((mtTy Ch sel mu P j).inv w).ev (h.1 w) =
        (if w.1 ∈ Pr.vGs then (1 : X.Kˣ) else resChar (mu : Chr X.F X.E X.K) w.1 (sgnU _ ε))⁻¹ := by
      intro w
      rw [hh w]
      show ((mtTy Ch sel mu P j w).inv).ev _ = _
      rw [Lev.inv_ev]
      by_cases hw : w.1 ∈ Pr.vGs
      · rw [if_pos hw, mtTy, LevFam.glue_of_mem _ _ w hw]
        show (((⟨HPar _ _ (r_le_nV R) [R.t] (P ⟨w.1, hw⟩).H,
          lamPar (r_le_nV R) [R.t] (P ⟨w.1, hw⟩).lam fun _ => chiAt Ch ⟨w.1, hw⟩ (j - 1)⟩ : Lev _ X.K _).inv).ev _)⁻¹ = 1⁻¹
        rw [Lev.inv_ev, nz_lamPar_ev _ _ _ _ _ s hfix hco (fun _ => nz_chiAt_sgn hPr hCh ⟨w.1, hw⟩ (j - 1)), inv_one, inv_one]
      · rw [if_neg hw, mtTy, LevFam.glue_of_not _ _ w hw]
        show ((⟨HQ _ _ R.r R.t, lamQ (resChar (mu : Chr X.F X.E X.K) w.1) _ R.r R.t⟩ : Lev _ X.K _).ev _)⁻¹ = _
        rw [hε]
    rw [LevFam.chr_ev, Finset.prod_congr rfl fun w _ => key w, Finset.prod_inv_distrib, hξ.prod ε, inv_one]

theorem mtilde_finrank_pos (hX : X.Ok) (hf : Even X.f) (hPr : Pr.Ok) (hCh : Ch.Ok) (hW : W.Ok)
    (he : ∀ j : Fin R.m, ∃ z : ℤ, ∑ τ, (W.row τ).e j = 2 * (z : ℚ)) (hg : ∀ i, 2 * X.f + 1 < Pr.g i)
    (hξ : XiSign Pr sel (mu : Chr X.F X.E X.K)) (P : LevFam X.E X.K R.r Pr.vGs) (hP : ∀ w, (P w).H ≤ HU _ R.r) :
    0 < finrank X.K (MtildeV W Ch sel mu P) :=
  mtilde_finrank_pos' W Ch sel mu hX hPr hCh hW (fun a ha => nz_sg_even hW hf he a ha) hg hξ P hP

theorem mt_finrank_pos (hX : X.Ok) (hf : Even X.f) (hPr : Pr.Ok) (hCh : Ch.Ok) (hW : W.Ok)
    (he : ∀ j : Fin R.m, ∃ z : ℤ, ∑ τ, (W.row τ).e j = 2 * (z : ℚ)) (hg : ∀ i, 2 * X.f + 1 < Pr.g i)
    (hξ : XiSign Pr sel (mu : Chr X.F X.E X.K)) (P : LevFam X.E X.K R.r Pr.vGs) (hP : ∀ w, (P w).H ≤ HU _ R.r)
    (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ R.m) : 0 < finrank X.K (MtV W Ch sel mu P j) :=
  mt_finrank_pos' W Ch sel mu hX hPr hCh hW hg hξ P hP j hj1 hj2 (fun a ha => nz_lamV_even hW hf he hj1 hj2 a ha)

theorem rowsNonzero_of (hX : X.Ok) (hf : Even X.f) (hPr : Pr.Ok) (hCh : Ch.Ok) (hW : W.Ok)
    (he : ∀ j : Fin R.m, ∃ z : ℤ, ∑ τ, (W.row τ).e j = 2 * (z : ℚ)) (hg : ∀ i, 2 * X.f + 1 < Pr.g i)
    (hξ : XiSign Pr sel (mu : Chr X.F X.E X.K)) (P : LevFam X.E X.K R.r Pr.vGs) (hP : ∀ w, (P w).H ≤ HU _ R.r) :
    RowsNonzero W Ch sel mu P :=
  ⟨mtilde_finrank_pos W Ch sel mu hX hf hPr hCh hW he hg hξ P hP,
    fun j h1 h2 => mt_finrank_pos W Ch sel mu hX hf hPr hCh hW he hg hξ P hP j h1 h2⟩

end Final

section Dat

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem rPsym_le (Ch : Chars X Pr R.m) (w : {w // w ∈ Pr.vGs}) : (rPsym (R := R) Ch w).H ≤ HU _ R.r := HPsym_le _ _ _ _

theorem Sizes.g_gt {W : Wts X Pr.Word R} {a : ℝ} (h : Sizes Pr W a) (i : Fin 2) : 2 * X.f + 1 < Pr.g i := by
  have h1 := h.g_big i
  have h2 : 2 * X.f * 1 ≤ 2 * X.f * R.k := Nat.mul_le_mul_left _ (by have := R.m_add_three_le_k; omega)
  omega

theorem Dat.Ok.rowsNonzero {D : Dat} (hD : D.Ok) (sel : HeightOneSpectrum (𝓞 D.X.F) → HeightOneSpectrum (𝓞 D.X.E)) {S : Set ℕ}
    (mu : Tup D.X.F D.X.E D.X.K S) (hξ : XiSign D.Pr sel (mu : Chr D.X.F D.X.E D.X.K))
    (P : LevFam D.X.E D.X.K D.R.r D.Pr.vGs) (hP : ∀ w, (P w).H ≤ HU _ D.R.r) : RowsNonzero D.W D.Ch sel mu P :=
  rowsNonzero_of D.W D.Ch sel mu hD.fields hD.fieldsConditions.f_even hD.primes hD.chars hD.wts hD.e_even hD.sizes.g_gt hξ P hP

end Dat

end Formalism.L2.Col
end
end
