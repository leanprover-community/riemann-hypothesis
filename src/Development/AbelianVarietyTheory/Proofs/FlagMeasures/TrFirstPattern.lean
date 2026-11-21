import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass

section
noncomputable section

namespace GlobalTheory.GLm

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq
open scoped Classical

variable {g : ℕ} [Fact g.Prime] {N : ℕ}

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {N : ℕ} in
private lemma traceOnCharacter_averagedSingles_eq (g N : ℕ) [Fact g.Prime]
    (Φ : Matrix (Fin N) (Fin N) (ZMod g) → Prop) (E : Matrix (Fin N) (Fin N) (ZMod g) → ZMod g)
    (ψ : AddChar (ZMod g) ℂ) (χ : GL (Fin N) (ZMod g) → ℂ) :
    _root_.GlobalTheory.GLq.tr (_root_.Formalism.MainNotions.ArithmeticCylinders.eDat g N Φ E ψ) χ =
      ((Finset.univ.filter
          (fun u : GL (Fin N) (ZMod g) => Φ (u : Matrix (Fin N) (Fin N) (ZMod g)))).card : ℂ)⁻¹ *
        ∑ u ∈ Finset.univ.filter
            (fun u : GL (Fin N) (ZMod g) => Φ (u : Matrix (Fin N) (Fin N) (ZMod g))),
          (ψ (E u))⁻¹ * χ u := by
  unfold _root_.GlobalTheory.GLq.tr _root_.Formalism.MainNotions.ArithmeticCylinders.eDat
  simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, Finsupp.smul_apply,
    Finsupp.finset_sum_apply, MonoidAlgebra.coeff_single_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {N : ℕ} in

theorem _root_.GlobalTheory.GLm.tr_ePat_renumber : ∀ (g : ℕ) [Fact g.Prime]
    (ψ : AddChar (ZMod g) ℂ) (N : ℕ) (Φ E : Fin N → Fin N → Prop)
    (σ : Equiv.Perm (Fin N)) (χ : _root_.GlobalTheory.GLq.Gn g N → ℂ), _root_.GlobalTheory.GLq.IsClass χ →
    _root_.GlobalTheory.GLq.tr (_root_.GlobalTheory.GLm.ePat g N (fun a b => Φ (σ a) (σ b))
      (fun a b => E (σ a) (σ b)) ψ) χ =
      _root_.GlobalTheory.GLq.tr (_root_.GlobalTheory.GLm.ePat g N Φ E ψ) χ := by
  intro g _ ψ N Φ E σ χ hχ
  unfold _root_.GlobalTheory.GLm.ePat
  rw [traceOnCharacter_averagedSingles_eq, traceOnCharacter_averagedSingles_eq]
  set Q : GL (Fin N) (ZMod g) := (Matrix.permMatrixHom (R := ZMod g)).toHomUnits σ⁻¹ with hQdef
  have hQ : ∀ (u : GL (Fin N) (ZMod g)) (x y : Fin N),
      ((Q⁻¹ * u * Q : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g)) x y =
        (u : Matrix (Fin N) (Fin N) (ZMod g)) (σ.symm x) (σ.symm y) := by
    intro u x y
    have hinv : ((Q⁻¹ : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g)) =
        (σ⁻¹ : Equiv.Perm (Fin N)).toPEquiv.toMatrix := by
      rw [hQdef]
      show (((σ⁻¹)⁻¹)⁻¹ : Equiv.Perm (Fin N)).toPEquiv.toMatrix = _
      rw [inv_inv]
    have hval : ((Q : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g)) =
        σ.toPEquiv.toMatrix := by
      rw [hQdef]
      show ((σ⁻¹)⁻¹ : Equiv.Perm (Fin N)).toPEquiv.toMatrix = _
      rw [inv_inv]
    rw [Units.val_mul, Units.val_mul, hinv, hval, PEquiv.toMatrix_toPEquiv_mul,
      PEquiv.mul_toMatrix_toPEquiv]
    rfl
  let e : GL (Fin N) (ZMod g) ≃ GL (Fin N) (ZMod g) := (MulAut.conj Q⁻¹).toEquiv
  have he : ∀ u, e u = Q⁻¹ * u * Q := by
    intro u
    simp [e, MulAut.conj_apply]
  have hmem : ∀ u : GL (Fin N) (ZMod g),
      _root_.GlobalTheory.GLm.InPat (fun a b => Φ (σ a) (σ b)) (u : Matrix (Fin N) (Fin N) (ZMod g)) ↔
        _root_.GlobalTheory.GLm.InPat Φ (e u : Matrix (Fin N) (Fin N) (ZMod g)) := by
    intro u
    unfold _root_.GlobalTheory.GLm.InPat
    simp only [he, hQ]
    constructor
    · intro h x y hxy
      have hxy' := h (σ.symm x) (σ.symm y) (by simpa using hxy)
      rw [hxy', Matrix.one_apply, Matrix.one_apply]
      simp
    · intro h a b hab
      have hab' := h (σ a) (σ b) hab
      simp only [Equiv.symm_apply_apply] at hab'
      rw [hab', Matrix.one_apply, Matrix.one_apply]
      simp
  have hsum : ∀ u : GL (Fin N) (ZMod g),
      _root_.GlobalTheory.GLm.sumAt (fun a b => E (σ a) (σ b)) (u : Matrix (Fin N) (Fin N) (ZMod g)) =
        _root_.GlobalTheory.GLm.sumAt E (e u : Matrix (Fin N) (Fin N) (ZMod g)) := by
    intro u
    unfold _root_.GlobalTheory.GLm.sumAt
    simp only [he, hQ]
    conv_rhs => rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_rhs => rw [← Equiv.sum_comp σ]
    simp only [Equiv.symm_apply_apply]
  congr 1
  · congr 2
    exact Finset.card_equiv e (fun u => by simp [hmem])
  · refine Finset.sum_equiv e (fun u => by simp [hmem]) (fun u _ => ?_)
    rw [hsum, he]
    congr 1
    have hconj := hχ u Q⁻¹
    simpa using hconj.symm

end GlobalTheory.GLm
end
end

section
noncomputable section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.FirstPattern

def front (N k s : ℕ) (h : k + s ≤ N) : Equiv.Perm (Fin N) where
  toFun a := ⟨if (a : ℕ) < k then s + a else if (a : ℕ) < k + s then a - k else a, by
    have := a.2; split_ifs <;> omega⟩
  invFun a := ⟨if (a : ℕ) < s then k + a else if (a : ℕ) < k + s then a - s else a, by
    have := a.2; split_ifs <;> omega⟩
  left_inv a := by
    apply Fin.ext
    simp only
    split_ifs <;> omega
  right_inv a := by
    apply Fin.ext
    simp only
    split_ifs <;> omega

theorem front_val (N k s : ℕ) (h : k + s ≤ N) (a : Fin N) :
    ((front N k s h a : Fin N) : ℕ) = if (a : ℕ) < k then s + a else if (a : ℕ) < k + s then a - k else a := rfl

theorem phI_front (N k s : ℕ) (h : k + s ≤ N) (a b : Fin N) :
    phI k s 0 (front N k s h a) (front N k s h b) ↔ (a : ℕ) < b ∧ ¬ ((a : ℕ) < k ∧ (b : ℕ) = k) := by
  simp only [phI, IsW, Fin.lt_def, front_val]
  split_ifs <;> omega

theorem eeI_front (N k s : ℕ) (h : k + s ≤ N) (a b : Fin N) :
    eeI k s (front N k s h a) (front N k s h b) ↔ (b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k := by
  simp only [eeI, IsW, front_val]
  split_ifs <;> omega

theorem eDat_congr (g N : ℕ) [NeZero g] (P P' : Mt g N → Prop) (φ φ' : Mt g N → ZMod g)
    (ψ : AddChar (ZMod g) ℂ) (hP : ∀ M, P M ↔ P' M) (hφ : ∀ M, P' M → φ M = φ' M) :
    eDat g N P φ ψ = eDat g N P' φ' ψ := by
  obtain rfl : P = P' := funext fun M => propext (hP M)
  unfold eDat
  congr 1
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [hφ _ (Finset.mem_filter.1 hu).2]

theorem inPat_iff {g : ℕ} [Fact g.Prime] (N k : ℕ) (hk : k < N) (M : Mt g N) :
    InPat (fun a b : Fin N => (a : ℕ) < b ∧ ¬ ((a : ℕ) < k ∧ (b : ℕ) = k)) M ↔
      IsUniUp M ∧ ∀ a, a < k → entN M a k = 0 := by
  constructor
  · intro h
    refine ⟨fun a b => ⟨fun hab => ?_, fun hab => ?_⟩, fun a ha => ?_⟩
    · have hab' : (b : ℕ) < a := hab
      rw [h a b (by omega), Matrix.one_apply_ne hab.ne']
    · subst hab
      rw [h a a (by omega), Matrix.one_apply_eq]
    · have haN : a < N := by omega
      rw [entN, dif_pos ⟨haN, hk⟩, h _ _ (by simp [ha]), Matrix.one_apply_ne]
      intro e
      have := congrArg Fin.val e
      simp only at this
      omega
  · rintro ⟨hU, hz⟩ a b hab
    rcases lt_trichotomy a b with h | h | h
    · have h' : (a : ℕ) < b := h
      have h2 : (a : ℕ) < k ∧ (b : ℕ) = k := by
        by_contra hh
        exact hab ⟨h', hh⟩
      have := hz a h2.1
      rw [entN, dif_pos ⟨a.2, hk⟩] at this
      have hb : b = ⟨k, hk⟩ := Fin.ext h2.2
      rw [Matrix.one_apply_ne h.ne, hb]
      exact this
    · rw [(hU a b).2 h, h, Matrix.one_apply_eq]
    · rw [(hU a b).1 h, Matrix.one_apply_ne h.ne']

theorem sumAt_eq {g : ℕ} [Fact g.Prime] (N k : ℕ) (M : Mt g N) (hz : ∀ a, a < k → entN M a k = 0) :
    sumAt (fun a b : Fin N => (b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k) M =
      ∑ i ∈ Finset.range (N - 1), entN M i (i + 1) := by
  have h1 : ∀ a : Fin N, (∑ b : Fin N, if ((b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k) then M a b else 0) =
      entN M a (a + 1) := by
    intro a
    by_cases ha : (a : ℕ) + 1 < N
    · rw [Finset.sum_eq_single (⟨a + 1, ha⟩ : Fin N)]
      · by_cases hk : (a : ℕ) + 1 = k
        · rw [if_neg (by simp [hk]), hk, hz a (by omega)]
        · rw [if_pos (by simp [hk]), entN, dif_pos ⟨a.2, ha⟩]
      · intro b _ hb
        rw [if_neg]
        rintro ⟨e, -⟩
        exact hb (Fin.ext e)
      · simp
    · rw [entN, dif_neg (by omega)]
      refine Finset.sum_eq_zero fun b _ => if_neg ?_
      have := b.2
      omega
  have h2 : ∑ i ∈ Finset.range (N - 1), entN M i (i + 1) = ∑ i ∈ Finset.range N, entN M i (i + 1) := by
    refine Finset.sum_subset (Finset.range_subset_range.2 (Nat.sub_le _ _)) fun i _ hi => ?_
    rw [Finset.mem_range] at hi
    rw [entN, dif_neg (by omega)]
  rw [h2, Finset.sum_range, sumAt]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← h1 a]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr

theorem tr_first_pattern : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (N k s : ℕ), N = k + 2 * s + 1 →
    ∀ χ : Gn g N → ℂ, IsClass χ → tr (ePat g N (phI k s 0) (eeI k s) ψ) χ = tr (eJ' g N k ψ) χ := by
  intro g _ ψ N k s hN χ hχ
  have h : k + s ≤ N := by omega
  rw [← GlobalTheory.GLm.tr_ePat_renumber g ψ N (phI k s 0) (eeI k s) (front N k s h) χ hχ]
  congr 1
  have e1 : (fun a b => phI k s 0 (front N k s h a) (front N k s h b)) =
      fun a b : Fin N => (a : ℕ) < b ∧ ¬ ((a : ℕ) < k ∧ (b : ℕ) = k) :=
    funext fun a => funext fun b => propext (phI_front N k s h a b)
  have e2 : (fun a b => eeI k s (front N k s h a) (front N k s h b)) =
      fun a b : Fin N => (b : ℕ) = a + 1 ∧ (b : ℕ) ≠ k :=
    funext fun a => funext fun b => propext (eeI_front N k s h a b)
  rw [e1, e2, ePat, eJ']
  exact eDat_congr g N _ _ _ _ ψ (inPat_iff N k (by omega)) fun M hM => sumAt_eq N k M hM.2

end GlobalTheory.GLm.FirstPattern
end
end
