import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PutLinPack
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PutMulPut
import BuildAid.ForwardExisting

section
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul.PutNest

theorem put_apply' {R : Type} [CommRing R] (n o₁ o₂ : ℕ) {p q : ℕ} (X : Matrix (Fin p) (Fin q) R) (i j : Fin n) :
    put n o₁ o₂ X i j = if h : (o₁ ≤ i.val ∧ i.val < o₁ + p) ∧ (o₂ ≤ j.val ∧ j.val < o₂ + q) then
      X ⟨i.val - o₁, by omega⟩ ⟨j.val - o₂, by omega⟩ else 0 := rfl

theorem stdSum_symm_lt {p₁ p₂ p : ℕ} (h : p₁ + p₂ = p) (r : Fin p) (hr : r.val < p₁) :
    (stdSum h).symm r = Sum.inl ⟨r.val, hr⟩ := by
  rw [Equiv.symm_apply_eq]; ext; simp

theorem stdSum_symm_ge {p₁ p₂ p : ℕ} (h : p₁ + p₂ = p) (r : Fin p) (hr : p₁ ≤ r.val) :
    (stdSum h).symm r = Sum.inr ⟨r.val - p₁, by omega⟩ := by
  rw [Equiv.symm_apply_eq]; ext; simp; omega

theorem part1 {R : Type} [CommRing R] (n m o o' o₁ o₂ p q : ℕ) (X : Matrix (Fin p) (Fin q) R)
    (h1 : o₁ + p ≤ m) (h2 : o₂ + q ≤ m) : put n o o' (put m o₁ o₂ X) = put n (o + o₁) (o' + o₂) X := by
  ext i j
  rw [put_apply', put_apply']
  split_ifs with ha hb hb
  · rw [put_apply']
    rw [dif_pos (by simp only; omega)]
    congr 1 <;> ext <;> simp <;> omega
  · rw [put_apply', dif_neg (by simp only; omega)]
  · exfalso; omega
  · rfl

theorem part2 {R : Type} [CommRing R] (n o₁ o₂ p q p₁ p₂ : ℕ) (h : p₁ + p₂ = p) (X : Matrix (Fin p₁) (Fin q) R)
    (Y : Matrix (Fin p₂) (Fin q) R) :
    put n o₁ o₂ ((fromRows X Y).submatrix (stdSum h).symm id) = put n o₁ o₂ X + put n (o₁ + p₁) o₂ Y := by
  ext i j
  rw [Matrix.add_apply, put_apply', put_apply', put_apply']
  split_ifs with ha hb hc hc hb hc hc
  · exfalso; omega
  · rw [submatrix_apply, id, stdSum_symm_lt h _ (by simp only; omega), fromRows_apply_inl, add_zero]
  · rw [submatrix_apply, id, stdSum_symm_ge h _ (by simp only; omega), fromRows_apply_inr, zero_add]
    congr 1; ext; simp only; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · simp

theorem part3 {R : Type} [CommRing R] (n o₁ o₂ p q p₁ p₂ : ℕ) (h : p₁ + p₂ = p) (X : Matrix (Fin q) (Fin p₁) R)
    (Y : Matrix (Fin q) (Fin p₂) R) :
    put n o₁ o₂ ((fromCols X Y).submatrix id (stdSum h).symm) = put n o₁ o₂ X + put n o₁ (o₂ + p₁) Y := by
  ext i j
  rw [Matrix.add_apply, put_apply', put_apply', put_apply']
  split_ifs with ha hb hc hc hb hc hc
  · exfalso; omega
  · rw [submatrix_apply, id, stdSum_symm_lt h _ (by simp only; omega), fromCols_apply_inl, add_zero]
  · rw [submatrix_apply, id, stdSum_symm_ge h _ (by simp only; omega), fromCols_apply_inr, zero_add]
    congr 1; ext; simp only; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · simp

theorem main : ∀ (R : Type) [CommRing R] (n m o o' o₁ o₂ p q p₁ p₂ : ℕ), (∀ X : Matrix (Fin p) (Fin q) R, o₁ + p ≤ m → o₂ + q ≤ m → put n o o' (put m o₁ o₂ X) = put n (o + o₁) (o' + o₂) X) ∧ (∀ (h : p₁ + p₂ = p) (X : Matrix (Fin p₁) (Fin q) R) (Y : Matrix (Fin p₂) (Fin q) R), put n o₁ o₂ ((fromRows X Y).submatrix (stdSum h).symm id) = put n o₁ o₂ X + put n (o₁ + p₁) o₂ Y) ∧ (∀ (h : p₁ + p₂ = p) (X : Matrix (Fin q) (Fin p₁) R) (Y : Matrix (Fin q) (Fin p₂) R), put n o₁ o₂ ((fromCols X Y).submatrix id (stdSum h).symm) = put n o₁ o₂ X + put n o₁ (o₂ + p₁) Y) :=
  fun R _ n m o o' o₁ o₂ p q p₁ p₂ =>
    ⟨fun X h1 h2 => part1 n m o o' o₁ o₂ p q X h1 h2, fun h X Y => part2 n o₁ o₂ p q p₁ p₂ h X Y,
      fun h X Y => part3 n o₁ o₂ p q p₁ p₂ h X Y⟩

end GlobalTheory.GamMul.PutNest
end

section
section
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul

theorem toGL_of_inv {R : Type} [CommRing R] {n : ℕ} (M N : Matrix (Fin n) (Fin n) R) (h₁ : M * N = 1)
    (h₂ : N * M = 1) : toGL M = ⟨M, N, h₁, h₂⟩ := by
  unfold toGL
  have hu : IsUnit M := ⟨⟨M, N, h₁, h₂⟩, rfl⟩
  rw [dif_pos hu]
  exact Units.ext rfl

theorem eye_mul_eye {R : Type} [CommRing R] (n o₁ o₂ o₃ b : ℕ) (h : o₂ + b ≤ n) :
    eye R n o₁ o₂ b * eye R n o₂ o₃ b = eye R n o₁ o₃ b := by
  unfold eye
  rw [(put_mul_put R n o₁ o₂ o₃ 0 b b b b (1 : Matrix (Fin b) (Fin b) R) 1 1).1 h, Matrix.mul_one]

theorem eye_mul_eye_zero {R : Type} [CommRing R] (n o₁ o₂ o₃ o₄ b c : ℕ) (h : o₂ + b ≤ o₃ ∨ o₃ + c ≤ o₂) :
    eye R n o₁ o₂ b * eye R n o₃ o₄ c = 0 := by
  unfold eye
  exact (put_mul_put R n o₁ o₂ o₃ o₄ b b c c (1 : Matrix (Fin b) (Fin b) R) 0 1).2 h

theorem val_uni_dg_shuf : ∀ (R : Type) [CommRing R] (n o₁ o₂ p q : ℕ),
    (∀ X : Matrix (Fin p) (Fin q) R, (o₁ + p ≤ o₂ ∨ o₂ + q ≤ o₁) →
      (uni n o₁ o₂ X).val = 1 + put n o₁ o₂ X ∧ (uni n o₁ o₂ X)⁻¹.val = 1 - put n o₁ o₂ X) ∧
    (∀ g : GL (Fin p) R, o₁ + p ≤ n →
      (dg n o₁ g).val = 1 - eye R n o₁ o₁ p + put n o₁ o₁ g.val ∧
      (dg n o₁ g)⁻¹.val = 1 - eye R n o₁ o₁ p + put n o₁ o₁ g⁻¹.val) ∧
    (p ≤ n → (shuf R n p).val = eye R n 0 p (n - p) + eye R n (n - p) 0 p ∧
      (shuf R n p)⁻¹.val = eye R n p 0 (n - p) + eye R n 0 (n - p) p) := by
  intro R _ n o₁ o₂ p q
  refine ⟨?_, ?_, ?_⟩
  · intro X hX
    have hPP : put n o₁ o₂ X * put n o₁ o₂ X = 0 :=
      (put_mul_put R n o₁ o₂ o₁ o₂ p q q p X 0 X).2 hX.symm
    have h₁ : (1 + put n o₁ o₂ X) * (1 - put n o₁ o₂ X) = 1 := by
      rw [add_mul, one_mul, mul_sub, mul_one, hPP]; abel
    have h₂ : (1 - put n o₁ o₂ X) * (1 + put n o₁ o₂ X) = 1 := by
      rw [sub_mul, one_mul, mul_add, mul_one, hPP]; abel
    have e : uni n o₁ o₂ X = ⟨_, _, h₁, h₂⟩ := toGL_of_inv _ _ h₁ h₂
    rw [e]; exact ⟨rfl, rfl⟩
  · intro g hg
    have hm : ∀ A B : Matrix (Fin p) (Fin p) R, put n o₁ o₁ A * put n o₁ o₁ B = put n o₁ o₁ (A * B) :=
      fun A B => (put_mul_put R n o₁ o₁ o₁ o₁ p p p p A B B).1 hg
    have key : ∀ a b : GL (Fin p) R, a * b = 1 →
        (1 - eye R n o₁ o₁ p + put n o₁ o₁ a.val) * (1 - eye R n o₁ o₁ p + put n o₁ o₁ b.val) = 1 := by
      intro a b hab
      have hab' : a.val * b.val = 1 := by rw [← Units.val_mul, hab]; rfl
      simp only [eye, sub_mul, add_mul, mul_sub, mul_add, one_mul, mul_one, hm, Matrix.one_mul, Matrix.mul_one, hab']
      abel
    have h₁ := key g g⁻¹ (mul_inv_cancel g)
    have h₂ := key g⁻¹ g (inv_mul_cancel g)
    have e : dg n o₁ g = ⟨_, _, h₁, h₂⟩ := toGL_of_inv _ _ h₁ h₂
    rw [e]; exact ⟨rfl, rfl⟩
  · intro hp
    have hpk := (put_lin_pack R n 0 0 (n - p) p).2.2.2.2.1
    have hpk' := (put_lin_pack R n 0 0 p (n - p)).2.2.2.2.1
    have hone := (put_lin_pack R n 0 0 0 0).2.2.2.2.2.1
    have hs : n - p + p = n := Nat.sub_add_cancel hp
    have hs' : p + (n - p) = n := by omega
    rw [hs, hone, zero_add] at hpk
    rw [hs', hone, zero_add] at hpk'
    have h₁ : (eye R n 0 p (n - p) + eye R n (n - p) 0 p) * (eye R n p 0 (n - p) + eye R n 0 (n - p) p) = 1 := by
      rw [add_mul, mul_add, mul_add, eye_mul_eye n 0 p 0 (n - p) (by omega),
        eye_mul_eye_zero n 0 p 0 (n - p) (n - p) p (Or.inr (by omega)),
        eye_mul_eye_zero n (n - p) 0 p 0 p (n - p) (Or.inl (by omega)),
        eye_mul_eye n (n - p) 0 (n - p) p (by omega), hpk]
      abel
    have h₂ : (eye R n p 0 (n - p) + eye R n 0 (n - p) p) * (eye R n 0 p (n - p) + eye R n (n - p) 0 p) = 1 := by
      rw [add_mul, mul_add, mul_add, eye_mul_eye n p 0 p (n - p) (by omega),
        eye_mul_eye_zero n p 0 (n - p) 0 (n - p) p (Or.inl (by omega)),
        eye_mul_eye_zero n 0 (n - p) 0 p p (n - p) (Or.inr (by omega)),
        eye_mul_eye n 0 (n - p) 0 p (by omega), hpk']
      abel
    have e : shuf R n p = ⟨_, _, h₁, h₂⟩ := toGL_of_inv _ _ h₁ h₂
    rw [e]; exact ⟨rfl, rfl⟩

end GlobalTheory.GamMul
end

open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_matrix_values_unipotent_diagonal : ∀ (R : Type) [CommRing R] (n o₁ o₂ p q : ℕ), (∀ X : Matrix (Fin p) (Fin q) R, (o₁ + p ≤ o₂ ∨ o₂ + q ≤ o₁) → (uni n o₁ o₂ X).val = 1 + put n o₁ o₂ X ∧ (uni n o₁ o₂ X)⁻¹.val = 1 - put n o₁ o₂ X) ∧ (∀ g : GL (Fin p) R, o₁ + p ≤ n → (dg n o₁ g).val = 1 - eye R n o₁ o₁ p + put n o₁ o₁ g.val ∧ (dg n o₁ g)⁻¹.val = 1 - eye R n o₁ o₁ p + put n o₁ o₁ g⁻¹.val) ∧ (p ≤ n → (shuf R n p).val = eye R n 0 p (n - p) + eye R n (n - p) 0 p ∧ (shuf R n p)⁻¹.val = eye R n p 0 (n - p) + eye R n 0 (n - p) p) := by
  atlas_forward_decl GlobalTheory.GamMul.val_uni_dg_shuf
end

section
section
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul.Hom

variable {R : Type} [CommRing R]

theorem put_entry (n o₁ o₂ : ℕ) {p q : ℕ} (X : Matrix (Fin p) (Fin q) R) (i j : Fin n) :
    put n o₁ o₂ X i j =
      if h : (o₁ ≤ i.val ∧ i.val < o₁ + p) ∧ (o₂ ≤ j.val ∧ j.val < o₂ + q) then
        X ⟨i.val - o₁, by omega⟩ ⟨j.val - o₂, by omega⟩ else 0 := rfl

theorem toGL_coe {n : ℕ} {M : Matrix (Fin n) (Fin n) R} (h : IsUnit M) :
    ((toGL M : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = M := by
  unfold toGL
  rw [dif_pos h]
  rfl

theorem det_one_add_put (n o₁ o₂ : ℕ) {p q : ℕ} (X : Matrix (Fin p) (Fin q) R)
    (hd : o₁ + p ≤ o₂ ∨ o₂ + q ≤ o₁) : (1 + put n o₁ o₂ X).det = 1 := by
  have hdiag : ∀ i : Fin n, (1 + put n o₁ o₂ X) i i = 1 := by
    intro i
    rw [Matrix.add_apply, Matrix.one_apply_eq, put_entry, dif_neg (by omega), add_zero]
  rcases hd with hd | hd
  · rw [Matrix.det_of_upperTriangular]
    · simp [hdiag]
    · intro i j hij
      have h' : j.val < i.val := hij
      rw [Matrix.add_apply, Matrix.one_apply_ne (show i ≠ j from fun e => by subst e; omega), put_entry, dif_neg (by omega), add_zero]
  · rw [Matrix.det_of_lowerTriangular]
    · simp [hdiag]
    · intro i j hij
      have h' : i.val < j.val := hij
      rw [Matrix.add_apply, Matrix.one_apply_ne (show i ≠ j from fun e => by subst e; omega), put_entry, dif_neg (by omega), add_zero]

theorem blk_mul (n o p : ℕ) (hp : o + p ≤ n) (A B : Matrix (Fin p) (Fin p) R) :
    (1 - eye R n o o p + put n o o A) * (1 - eye R n o o p + put n o o B) =
      1 - eye R n o o p + put n o o (A * B) := by
  have hm : ∀ X Y : Matrix (Fin p) (Fin p) R, put n o o X * put n o o Y = put n o o (X * Y) :=
    fun X Y => (put_mul_put R n o o o 0 p p p 0 X Y 0).1 hp
  unfold eye
  simp only [sub_mul, mul_sub, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, hm]
  abel

end GlobalTheory.GamMul.Hom

namespace GlobalTheory.GamMul.Hom

variable {R : Type} [CommRing R]

theorem uni_coe (n o₁ o₂ : ℕ) {p q : ℕ} (X : Matrix (Fin p) (Fin q) R) (hd : o₁ + p ≤ o₂ ∨ o₂ + q ≤ o₁) :
    ((uni n o₁ o₂ X : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 + put n o₁ o₂ X :=
  toGL_coe ((Matrix.isUnit_iff_isUnit_det _).2 (by rw [det_one_add_put n o₁ o₂ X hd]; exact isUnit_one))

theorem dg_coe (n o : ℕ) {p : ℕ} (g : GL (Fin p) R) (hp : o + p ≤ n) :
    ((dg n o g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 - eye R n o o p + put n o o g.val := by
  have h1 := blk_mul (R := R) n o p hp g.val g⁻¹.val
  have h2 := blk_mul (R := R) n o p hp g⁻¹.val g.val
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one] at h1
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one] at h2
  have e1 : (1 : Matrix (Fin n) (Fin n) R) - eye R n o o p + put n o o (1 : Matrix (Fin p) (Fin p) R) = 1 := by
    unfold eye; abel
  rw [e1] at h1 h2
  exact toGL_coe ⟨⟨_, _, h1, h2⟩, rfl⟩

theorem dg_one' (n o p : ℕ) : dg n o (1 : GL (Fin p) R) = 1 := by
  unfold dg
  rw [Units.val_one]
  have e1 : (1 : Matrix (Fin n) (Fin n) R) - eye R n o o p + put n o o (1 : Matrix (Fin p) (Fin p) R) = 1 := by
    unfold eye; abel
  rw [e1]
  exact Units.ext (toGL_coe isUnit_one)

theorem dg_mul' (n o : ℕ) {p : ℕ} (hp : o + p ≤ n) (g g' : GL (Fin p) R) :
    dg n o (g * g') = dg n o g * dg n o g' := by
  apply Units.ext
  rw [Units.val_mul, dg_coe n o _ hp, dg_coe n o _ hp, dg_coe n o _ hp, blk_mul n o p hp, Units.val_mul]

end GlobalTheory.GamMul.Hom

namespace GlobalTheory.GamMul.Hom

variable {R : Type} [CommRing R]

theorem dgM_in (n o p : ℕ) (A : Matrix (Fin p) (Fin p) R) (i j : Fin n) (hi : o ≤ i.val ∧ i.val < o + p)
    (hj : o ≤ j.val ∧ j.val < o + p) :
    (1 - eye R n o o p + put n o o A) i j = A ⟨i.val - o, by omega⟩ ⟨j.val - o, by omega⟩ := by
  unfold eye
  rw [Matrix.add_apply, Matrix.sub_apply, put_entry, put_entry, dif_pos ⟨hi, hj⟩, dif_pos ⟨hi, hj⟩]
  simp only [Matrix.one_apply, Fin.ext_iff]
  by_cases h : i.val = j.val
  · have h' : i.val - o = j.val - o := by omega
    simp [h, h']
  · have h' : i.val - o ≠ j.val - o := by omega
    simp [h, h']

theorem dgM_out (n o p : ℕ) (A : Matrix (Fin p) (Fin p) R) (i j : Fin n)
    (h : ¬((o ≤ i.val ∧ i.val < o + p) ∧ (o ≤ j.val ∧ j.val < o + p))) :
    (1 - eye R n o o p + put n o o A) i j = (1 : Matrix (Fin n) (Fin n) R) i j := by
  unfold eye
  rw [Matrix.add_apply, Matrix.sub_apply, put_entry, put_entry, dif_neg h, dif_neg h, sub_zero, add_zero]

theorem det_dg' (n o : ℕ) {p : ℕ} (hp : o + p ≤ n) (g : GL (Fin p) R) :
    GeneralLinearGroup.det (dg n o g) = GeneralLinearGroup.det g := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply, dg_coe n o g hp]
  let P : Fin n → Prop := fun i => o ≤ i.val ∧ i.val < o + p
  let f : {i : Fin n // P i} ≃ Fin p :=
    { toFun := fun i => ⟨i.1.val - o, by have := i.2; simp only [P] at this; omega⟩
      invFun := fun j => ⟨⟨o + j.val, by omega⟩, by simp only [P]; omega⟩
      left_inv := fun i => by
        have := i.2; simp only [P] at this
        apply Subtype.ext; apply Fin.ext; simp only; omega
      right_inv := fun j => by apply Fin.ext; simp only; omega }
  rw [Matrix.twoBlockTriangular_det _ P]
  · have h1 : toSquareBlockProp (1 - eye R n o o p + put n o o g.val) P = (g.val).submatrix f f := by
      ext i j
      have hi := i.2
      have hj := j.2
      simp only [P] at hi hj
      rw [toSquareBlockProp_def, Matrix.of_apply]
      rw [dgM_in n o p g.val i.1 j.1 hi hj]
      rfl
    have h2 : toSquareBlockProp (1 - eye R n o o p + put n o o g.val) (fun i => ¬P i) = 1 := by
      ext i j
      have hi := i.2
      rw [toSquareBlockProp_def, Matrix.of_apply]
      rw [dgM_out n o p g.val i.1 j.1 (fun h => hi h.1)]
      simp only [Matrix.one_apply, Subtype.ext_iff]
    rw [h1, h2, Matrix.det_submatrix_equiv_self, Matrix.det_one, mul_one]
  · intro i hi j hj
    rw [dgM_out n o p g.val i j (fun h => hi h.1), Matrix.one_apply_ne (by rintro rfl; exact hi hj)]

end GlobalTheory.GamMul.Hom

namespace GlobalTheory.GamMul.Hom

variable {R : Type} [CommRing R]

theorem dg_mul_dg_eq_emb₂ (n p q : ℕ) (h : p + q = n) (a : GL (Fin p) R) (b : GL (Fin q) R) :
    dg n 0 a * dg n p b = emb₂ R (stdSum h) (a, b) := by
  apply Units.ext
  rw [Units.val_mul, dg_coe n 0 a (by omega), dg_coe n p b (by omega), val_emb₂]
  have hz : ∀ (X : Matrix (Fin p) (Fin p) R) (Z : Matrix (Fin q) (Fin q) R),
      put n 0 0 X * put n p p Z = 0 :=
    fun X Z => (put_mul_put R n 0 0 p p p p q q X 0 Z).2 (Or.inl (by omega))
  have hsum : put n 0 0 (1 : Matrix (Fin p) (Fin p) R) + put n p p (1 : Matrix (Fin q) (Fin q) R) = 1 := by
    have h1 := (put_lin_pack R n 0 0 p q).2.2.2.2.1
    have h2 := (put_lin_pack R n 0 0 p q).2.2.2.2.2.1
    simp only [zero_add] at h1
    rw [h] at h1
    rw [← h2, h1]
    rfl
  have key : (1 - eye R n 0 0 p + put n 0 0 a.val) * (1 - eye R n p p q + put n p p b.val) =
      put n 0 0 a.val + put n p p b.val := by
    unfold eye
    simp only [sub_mul, mul_sub, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, hz]
    rw [← hsum]
    abel
  rw [key]
  ext i j
  obtain ⟨i, rfl⟩ := (stdSum h).surjective i
  obtain ⟨j, rfl⟩ := (stdSum h).surjective j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    Matrix.add_apply, put_entry, put_entry]
  rcases i with i | i <;> rcases j with j | j
  · have hi := i.2
    have hj := j.2
    rw [dif_pos (by simp only [stdSum_inl]; omega), dif_neg (by simp only [stdSum_inl]; omega), add_zero,
      fromBlocks_apply₁₁]
    congr 1 <;> apply Fin.ext <;> simp
  · have hi := i.2
    rw [dif_neg (by simp only [stdSum_inl, stdSum_inr]; omega), dif_neg (by simp only [stdSum_inl, stdSum_inr]; omega), add_zero,
      fromBlocks_apply₁₂, Matrix.zero_apply]
  · have hj := j.2
    rw [dif_neg (by simp only [stdSum_inl, stdSum_inr]; omega), dif_neg (by simp only [stdSum_inl, stdSum_inr]; omega), add_zero,
      fromBlocks_apply₂₁, Matrix.zero_apply]
  · have hi := i.2
    have hj := j.2
    rw [dif_neg (by simp only [stdSum_inr]; omega), dif_pos (by simp only [stdSum_inr]; omega), zero_add,
      fromBlocks_apply₂₂]
    show _ = (b : Matrix (Fin q) (Fin q) R) i j
    exact congrArg₂ (fun x y => (b : Matrix (Fin q) (Fin q) R) x y) (Fin.ext (by simp)) (Fin.ext (by simp))

theorem shuf_zero' (n : ℕ) : shuf R n 0 = 1 := by
  unfold shuf
  have h1 := (put_lin_pack R n 0 0 0 0).2.2.2.2.2.1
  have h2 := (put_lin_pack R n n 0 0 0).2.2.2.2.2.2.1 (1 : Matrix (Fin 0) (Fin 0) R) (Or.inl rfl)
  rw [Nat.sub_zero]
  change toGL (eye R n 0 0 n + put n n 0 (1 : Matrix (Fin 0) (Fin 0) R)) = 1
  rw [h1, h2, add_zero]
  exact Units.ext (toGL_coe isUnit_one)

theorem dg_zero_self (n : ℕ) (g : GL (Fin n) R) : dg n 0 g = g := by
  unfold dg
  rw [(put_lin_pack R n 0 0 0 0).2.2.2.2.2.1, (put_lin_pack R n 0 0 0 0).2.2.2.2.2.2.2, sub_self, zero_add]
  exact toGL_val g

end GlobalTheory.GamMul.Hom

namespace GlobalTheory.GamMul

theorem uni_dg_hom : ∀ (R : Type) [CommRing R] (n o₁ o₂ p q : ℕ), ((o₁ + p ≤ o₂ ∨ o₂ + q ≤ o₁) → (∀ X Y : Matrix (Fin p) (Fin q) R, uni n o₁ o₂ (X + Y) = uni n o₁ o₂ X * uni n o₁ o₂ Y) ∧ (∀ X : Matrix (Fin p) (Fin q) R, GeneralLinearGroup.det (uni n o₁ o₂ X) = 1)) ∧ uni n o₁ o₂ (0 : Matrix (Fin p) (Fin q) R) = 1 ∧ (∀ X : Matrix (Fin p) (Fin q) R, (p = 0 ∨ q = 0) → uni n o₁ o₂ X = 1) ∧ dg n o₁ (1 : GL (Fin p) R) = 1 ∧ (o₁ + p ≤ n → (∀ g g' : GL (Fin p) R, dg n o₁ (g * g') = dg n o₁ g * dg n o₁ g') ∧ ∀ g : GL (Fin p) R, GeneralLinearGroup.det (dg n o₁ g) = GeneralLinearGroup.det g) ∧ (∀ (h : p + q = n) (a : GL (Fin p) R) (b : GL (Fin q) R), dg n 0 a * dg n p b = emb₂ R (stdSum h) (a, b)) ∧ shuf R n 0 = 1 ∧ (∀ g : GL (Fin n) R, dg n 0 g = g) := by
  intro R _ n o₁ o₂ p q
  have hone : ∀ M : Matrix (Fin n) (Fin n) R, M = 0 → toGL (1 + M) = 1 := by
    intro M hM
    rw [hM, add_zero]
    exact Units.ext (Hom.toGL_coe isUnit_one)
  refine ⟨fun hd => ⟨fun X Y => ?_, fun X => ?_⟩, ?_, fun X hX => ?_, Hom.dg_one' n o₁ p,
    fun hp => ⟨fun g g' => Hom.dg_mul' n o₁ hp g g', fun g => Hom.det_dg' n o₁ hp g⟩,
    fun h a b => Hom.dg_mul_dg_eq_emb₂ n p q h a b, Hom.shuf_zero' n, Hom.dg_zero_self n⟩
  · apply Units.ext
    rw [Units.val_mul, Hom.uni_coe n o₁ o₂ _ hd, Hom.uni_coe n o₁ o₂ _ hd, Hom.uni_coe n o₁ o₂ _ hd,
      (put_lin_pack R n o₁ o₂ p q).1, add_mul, mul_add, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
      (put_mul_put R n o₁ o₂ o₁ o₂ p q q p X 0 Y).2 (hd.symm.imp id id)]
    abel
  · apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, Hom.uni_coe n o₁ o₂ _ hd, Hom.det_one_add_put n o₁ o₂ X hd, Units.val_one]
  · exact hone _ (put_lin_pack R n o₁ o₂ p q).2.2.1
  · exact hone _ ((put_lin_pack R n o₁ o₂ p q).2.2.2.2.2.2.1 X hX)

end GlobalTheory.GamMul
end

open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_unipotent_det_one_and_trivial : ∀ (R : Type) [CommRing R] (n o₁ o₂ p q : ℕ), ((o₁ + p ≤ o₂ ∨ o₂ + q ≤ o₁) → (∀ X Y : Matrix (Fin p) (Fin q) R, uni n o₁ o₂ (X + Y) = uni n o₁ o₂ X * uni n o₁ o₂ Y) ∧ (∀ X : Matrix (Fin p) (Fin q) R, GeneralLinearGroup.det (uni n o₁ o₂ X) = 1)) ∧ uni n o₁ o₂ (0 : Matrix (Fin p) (Fin q) R) = 1 ∧ (∀ X : Matrix (Fin p) (Fin q) R, (p = 0 ∨ q = 0) → uni n o₁ o₂ X = 1) ∧ dg n o₁ (1 : GL (Fin p) R) = 1 ∧ (o₁ + p ≤ n → (∀ g g' : GL (Fin p) R, dg n o₁ (g * g') = dg n o₁ g * dg n o₁ g') ∧ ∀ g : GL (Fin p) R, GeneralLinearGroup.det (dg n o₁ g) = GeneralLinearGroup.det g) ∧ (∀ (h : p + q = n) (a : GL (Fin p) R) (b : GL (Fin q) R), dg n 0 a * dg n p b = emb₂ R (stdSum h) (a, b)) ∧ shuf R n 0 = 1 ∧ (∀ g : GL (Fin n) R, dg n 0 g = g) := by
  atlas_forward_decl GlobalTheory.GamMul.uni_dg_hom
end

section
section
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul

section
variable {R : Type} [CommRing R] {n : ℕ}

private theorem comm_pm (o₁ o₂ o₃ : ℕ) {p q s : ℕ} (X : Matrix (Fin p) (Fin q) R) (Y : Matrix (Fin q) (Fin s) R)
    (h : o₂ + q ≤ n) : put n o₁ o₂ X * put n o₂ o₃ Y = put n o₁ o₃ (X * Y) :=
  (put_mul_put R n o₁ o₂ o₃ 0 p q s q X Y Y).1 h

private theorem comm_pz (o₁ o₂ o₃ o₄ : ℕ) {p q s t : ℕ} (X : Matrix (Fin p) (Fin q) R) (Z : Matrix (Fin t) (Fin s) R)
    (h : o₂ + q ≤ o₃ ∨ o₃ + t ≤ o₂) : put n o₁ o₂ X * put n o₃ o₄ Z = 0 :=
  (put_mul_put R n o₁ o₂ o₃ o₄ p q s t X 0 Z).2 h

private theorem comm_toGL (M N : Matrix (Fin n) (Fin n) R) (h₁ : M * N = 1) (h₂ : N * M = 1) : (toGL M).val = M := by
  have := toGL_val (⟨M, N, h₁, h₂⟩ : GL (Fin n) R)
  exact congrArg Units.val this

private theorem comm_uni {o₁ o₂ p q : ℕ} (X : Matrix (Fin p) (Fin q) R) (h : o₁ + p ≤ o₂ ∨ o₂ + q ≤ o₁) :
    (uni n o₁ o₂ X).val = 1 + put n o₁ o₂ X := by
  have h0 : put n o₁ o₂ X * put n o₁ o₂ X = 0 := comm_pz _ _ _ _ _ _ h.symm
  refine comm_toGL _ (1 - put n o₁ o₂ X) ?_ ?_
  · simp only [add_mul, mul_sub, mul_one, one_mul, h0]; abel
  · simp only [mul_add, sub_mul, mul_one, one_mul, h0]; abel

private theorem comm_dgmul {o p : ℕ} (A B : Matrix (Fin p) (Fin p) R) (hAB : A * B = 1) (h : o + p ≤ n) :
    (1 - eye R n o o p + put n o o A) * (1 - eye R n o o p + put n o o B) = 1 := by
  simp only [eye, add_mul, mul_add, mul_sub, sub_mul, mul_one, one_mul, comm_pm _ _ _ _ _ h, hAB]
  abel

private theorem comm_dg {o p : ℕ} (g : GL (Fin p) R) (h : o + p ≤ n) :
    (dg n o g).val = 1 - eye R n o o p + put n o o g.val :=
  comm_toGL _ (1 - eye R n o o p + put n o o g⁻¹.val) (comm_dgmul _ _ g.mul_inv h) (comm_dgmul _ _ g.inv_mul h)

end

theorem dg_uni_comm : ∀ (R : Type) [CommRing R] (n o₁ o₂ p q : ℕ), (o₁ + p ≤ o₂ ∨ o₂ + q ≤ o₁) → o₁ + p ≤ n → o₂ + q ≤ n → (∀ (g : GL (Fin p) R) (X : Matrix (Fin p) (Fin q) R), dg n o₁ g * uni n o₁ o₂ X = uni n o₁ o₂ (g.val * X) * dg n o₁ g) ∧ (∀ (g : GL (Fin q) R) (X : Matrix (Fin p) (Fin q) R), uni n o₁ o₂ X * dg n o₂ g = dg n o₂ g * uni n o₁ o₂ (X * g.val)) ∧ (∀ (a : GL (Fin p) R) (b : GL (Fin q) R), dg n o₁ a * dg n o₂ b = dg n o₂ b * dg n o₁ a) := by
  intro R _ n o₁ o₂ p q h h₁ h₂
  refine ⟨fun g X => Units.ext ?_, fun g X => Units.ext ?_, fun a b => Units.ext ?_⟩
  · simp only [Units.val_mul, comm_uni _ h, comm_dg _ h₁, eye, add_mul, mul_add, mul_sub, sub_mul, mul_one, one_mul,
      comm_pm _ _ _ _ _ h₁, comm_pz _ _ _ _ _ _ h.symm, Matrix.one_mul]
    abel
  · simp only [Units.val_mul, comm_uni _ h, comm_dg _ h₂, eye, add_mul, mul_add, mul_sub, sub_mul, mul_one, one_mul,
      comm_pm _ _ _ _ _ h₂, comm_pz _ _ _ _ _ _ h.symm, Matrix.mul_one]
    abel
  · simp only [Units.val_mul, comm_dg _ h₁, comm_dg _ h₂, eye, add_mul, mul_add, mul_sub, sub_mul, mul_one, one_mul,
      comm_pz _ _ _ _ _ _ h, comm_pz _ _ _ _ _ _ h.symm]
    abel

end GlobalTheory.GamMul
end

open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_block_conj_unipotent : ∀ (R : Type) [CommRing R] (n o₁ o₂ p q : ℕ), (o₁ + p ≤ o₂ ∨ o₂ + q ≤ o₁) → o₁ + p ≤ n → o₂ + q ≤ n → (∀ (g : GL (Fin p) R) (X : Matrix (Fin p) (Fin q) R), dg n o₁ g * uni n o₁ o₂ X = uni n o₁ o₂ (g.val * X) * dg n o₁ g) ∧ (∀ (g : GL (Fin q) R) (X : Matrix (Fin p) (Fin q) R), uni n o₁ o₂ X * dg n o₂ g = dg n o₂ g * uni n o₁ o₂ (X * g.val)) ∧ (∀ (a : GL (Fin p) R) (b : GL (Fin q) R), dg n o₁ a * dg n o₂ b = dg n o₂ b * dg n o₁ a) := by
  atlas_forward_decl GlobalTheory.GamMul.dg_uni_comm
end

section
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul.BlockId

theorem dg_dg {R : Type} [CommRing R] (n m o p : ℕ) (hm : m ≤ n) (hp : o + p ≤ m) (g : GL (Fin p) R) :
    dg n 0 (dg m o g) = dg n o g := by
  apply Units.ext
  obtain ⟨-, h2, -⟩ := GlobalTheory.T.block_matrix_values_unipotent_diagonal R n 0 0 m m
  obtain ⟨-, h2', -⟩ := GlobalTheory.T.block_matrix_values_unipotent_diagonal R m o o p p
  obtain ⟨-, h2'', -⟩ := GlobalTheory.T.block_matrix_values_unipotent_diagonal R n o o p p
  rw [(h2 _ (by omega)).1, (h2' g hp).1, (h2'' g (by omega)).1]
  obtain ⟨hadd, hneg, -, -, -, -, -, -⟩ := put_lin_pack R n 0 0 m m
  have hsub : ∀ X Y : Matrix (Fin m) (Fin m) R, put n 0 0 (X - Y) = put n 0 0 X - put n 0 0 Y := by
    intro X Y; rw [sub_eq_add_neg, hadd, hneg, ← sub_eq_add_neg]
  have hn1 := (PutNest.main R n m 0 0 o o p p 0 0).1
  have he1 : put n 0 0 (1 : Matrix (Fin m) (Fin m) R) = eye R n 0 0 m := rfl
  have he2 : put n 0 0 (eye R m o o p) = eye R n o o p := by
    simp only [eye]; rw [hn1 _ hp hp, zero_add]
  rw [hadd, hsub, he1, he2, hn1 _ hp hp, zero_add]
  abel

theorem dg_uni {R : Type} [CommRing R] (n m o₁ o₂ p q : ℕ) (hm : m ≤ n) (h1 : o₁ + p ≤ m) (h2 : o₂ + q ≤ m)
    (hd : o₁ + p ≤ o₂ ∨ o₂ + q ≤ o₁) (X : Matrix (Fin p) (Fin q) R) :
    dg n 0 (uni m o₁ o₂ X) = uni n o₁ o₂ X := by
  apply Units.ext
  obtain ⟨-, h2d, -⟩ := GlobalTheory.T.block_matrix_values_unipotent_diagonal R n 0 0 m m
  obtain ⟨h1u, -, -⟩ := GlobalTheory.T.block_matrix_values_unipotent_diagonal R m o₁ o₂ p q
  obtain ⟨h1u', -, -⟩ := GlobalTheory.T.block_matrix_values_unipotent_diagonal R n o₁ o₂ p q
  rw [(h2d _ (by omega)).1, (h1u X hd).1, (h1u' X hd).1]
  obtain ⟨hadd, -, -, -, -, -, -, -⟩ := put_lin_pack R n 0 0 m m
  have hn1 := (PutNest.main R n m 0 0 o₁ o₂ p q 0 0).1
  have he1 : put n 0 0 (1 : Matrix (Fin m) (Fin m) R) = eye R n 0 0 m := rfl
  rw [hadd, hn1 _ h1 h2, he1, zero_add, zero_add]
  abel

theorem main : ∀ (R : Type) [CommRing R] (n m m₁ m₂ : ℕ), m₁ + m₂ = m → m ≤ n → ∀ (a : GL (Fin m₁) R) (b : GL (Fin m₂) R) (x : Matrix (Fin m₂) (Fin m₁) R), dg n 0 (dg m 0 a * dg m m₁ b * uni m m₁ 0 x) = dg n 0 a * uni n m₁ 0 (b.val * x) * dg n m₁ b := by
  intro R _ n m m₁ m₂ hm hmn a b x
  have hmul := ((GlobalTheory.T.block_unipotent_det_one_and_trivial R n 0 0 m m).2.2.2.2.1 (by omega)).1
  rw [hmul, hmul, dg_dg n m 0 m₁ hmn (by omega), dg_dg n m m₁ m₂ hmn (by omega),
    dg_uni n m m₁ 0 m₂ m₁ hmn (by omega) (by omega) (Or.inr (by omega))]
  have hc := ((GlobalTheory.T.diagonal_block_conj_unipotent R n m₁ 0 m₂ m₁ (Or.inr (by omega)) (by omega) (by omega)).1 b x)
  rw [mul_assoc, hc, ← mul_assoc]

end GlobalTheory.GamMul.BlockId
end
