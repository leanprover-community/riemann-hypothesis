import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CvRhoOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfCVUnderIntOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothWordsAll

section
open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxE

open Formalism.REAL

variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}

def rel (E : Fin n → Fin n → A) (a b c d : Fin n) : A :=
  E a b * E c d - E c d * E a b - ((if b = c then E a d else 0) - (if d = a then E c b else 0))


theorem two_formal (E : Fin n → Fin n → A) (x y : ℂ) (hxy : x - y = 1) (p q c d : Fin n) :
    Tm E x p c * Tm E y q d - Tm E x q c * Tm E y p d + Tm E x p d * Tm E y q c
      - Tm E x q d * Tm E y p c = rel E p c q d + rel E p d q c := by
  obtain rfl : y = x - 1 := by linear_combination -hxy
  unfold rel
  simp only [eq_comm (a := c) (b := q), eq_comm (a := d) (b := p), eq_comm (a := d) (b := q),
    eq_comm (a := c) (b := p)]
  rw [ite_zero_eq_ite_smul (q = c) (E p d), ite_zero_eq_ite_smul (p = d) (E q c), ite_zero_eq_ite_smul (q = d) (E p c), ite_zero_eq_ite_smul (p = c) (E q d)]
  simp only [shiftedGenerator_eq_ite_smul_add, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  rw [ite_zero_eq_mul_ite (p = c) x, ite_zero_eq_mul_ite (q = d) (x - 1), ite_zero_eq_mul_ite (q = c) x, ite_zero_eq_mul_ite (p = d) (x - 1),
    ite_zero_eq_mul_ite (p = d) x, ite_zero_eq_mul_ite (q = c) (x - 1), ite_zero_eq_mul_ite (q = d) x, ite_zero_eq_mul_ite (p = c) (x - 1)]
  module

theorem four_formal {t : ℕ} (f₁ f₂ f₃ f₄ : Fin t → A) (i : ℕ) (hi : i + 1 < t)
    (h₂ : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → f₂ k = f₁ k)
    (h₃ : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → f₃ k = f₁ k)
    (h₄ : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → f₄ k = f₁ k) :
    (List.ofFn f₁).prod - (List.ofFn f₂).prod + (List.ofFn f₃).prod - (List.ofFn f₄).prod =
      ((List.ofFn f₁).take i).prod * (f₁ ⟨i, by omega⟩ * f₁ ⟨i + 1, hi⟩ - f₂ ⟨i, by omega⟩ * f₂ ⟨i + 1, hi⟩
        + f₃ ⟨i, by omega⟩ * f₃ ⟨i + 1, hi⟩ - f₄ ⟨i, by omega⟩ * f₄ ⟨i + 1, hi⟩) *
        ((List.ofFn f₁).drop (i + 2)).prod := by
  rw [prod_ofFn_split_pair f₁ i hi, prod_ofFn_split_pair f₂ i hi, prod_ofFn_split_pair f₃ i hi, prod_ofFn_split_pair f₄ i hi,
    take_ofFn_congr f₂ f₁ i (fun k hk => h₂ k (by omega) (by omega)),
    take_ofFn_congr f₃ f₁ i (fun k hk => h₃ k (by omega) (by omega)),
    take_ofFn_congr f₄ f₁ i (fun k hk => h₄ k (by omega) (by omega)),
    drop_ofFn_congr f₂ f₁ (i + 2) (fun k hk => h₂ k (by omega) (by omega)),
    drop_ofFn_congr f₃ f₁ (i + 2) (fun k hk => h₃ k (by omega) (by omega)),
    drop_ofFn_congr f₄ f₁ (i + 2) (fun k hk => h₄ k (by omega) (by omega)), sandwich_alternating_sum]

def fac (E : Fin n → Fin n → A) {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) (σ : Equiv.Perm (Fin t)) : Fin t → A :=
  fun k => Tm E (u - (k : ℂ)) (a (σ k)) (b k)

def Lt (E : Fin n → Fin n → A) {m : ℕ} (a b : Fin (m + 1) → Fin n) (u : ℂ) (σ : Equiv.Perm (Fin (m + 1)))
    (i : Fin m) : A :=
  ((List.ofFn (fac E a b u σ)).take (i : ℕ)).prod

def Rt (E : Fin n → Fin n → A) {m : ℕ} (a b : Fin (m + 1) → Fin n) (u : ℂ) (σ : Equiv.Perm (Fin (m + 1)))
    (i : Fin m) : A :=
  ((List.ofFn (fac E a b u σ)).drop ((i : ℕ) + 2)).prod

def Md (E : Fin n → Fin n → A) {m : ℕ} (a b : Fin (m + 1) → Fin n) (σ : Equiv.Perm (Fin (m + 1))) (i : Fin m) : A :=
  rel E (a (σ i.castSucc)) (b i.castSucc) (a (σ i.succ)) (b i.succ) +
    rel E (a (σ i.castSucc)) (b i.succ) (a (σ i.succ)) (b i.castSucc)

theorem key_formal (E : Fin n → Fin n → A) {m : ℕ} (a b : Fin (m + 1) → Fin n) (i : Fin m) (u : ℂ)
    (σ : Equiv.Perm (Fin (m + 1))) :
    exchangeTwo_self_eq_one E a b u σ - exchangeTwo_self_eq_one E a b u (σ * Equiv.swap i.castSucc i.succ)
      + exchangeTwo_self_eq_one E a (b ∘ Equiv.swap i.castSucc i.succ) u σ
      - exchangeTwo_self_eq_one E a (b ∘ Equiv.swap i.castSucc i.succ) u (σ * Equiv.swap i.castSucc i.succ) =
      Lt E a b u σ i * Md E a b σ i * Rt E a b u σ i := by
  have hs : ∀ k : Fin (m + 1), (k : ℕ) ≠ (i : ℕ) → (k : ℕ) ≠ (i : ℕ) + 1 →
      Equiv.swap i.castSucc i.succ k = k := by
    intro k h1 h2
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h; apply h1; rw [h]; simp
    · intro h; apply h2; rw [h]; simp
  unfold exchangeTwo_self_eq_one Lt Rt
  rw [four_formal _ _ _ _ (i : ℕ) (by omega)]
  · congr 2
    have e1 : (⟨(i : ℕ), by omega⟩ : Fin (m + 1)) = i.castSucc := rfl
    have e2 : (⟨(i : ℕ) + 1, by omega⟩ : Fin (m + 1)) = i.succ := rfl
    simp only [e1, e2, Equiv.Perm.mul_apply, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right, Md]
    exact two_formal E _ _ (by simp) _ _ _ _
  · intro k h1 h2; simp [Equiv.Perm.mul_apply, hs k h1 h2]
  · intro k h1 h2; simp [hs k h1 h2]
  · intro k h1 h2; simp [Equiv.Perm.mul_apply, hs k h1 h2]

theorem adj_formal (E : Fin n → Fin n → A) {m : ℕ} (a b : Fin (m + 1) → Fin n) (i : Fin m) (u : ℂ) :
    (2 : ℂ) • (qminor E a (b ∘ Equiv.swap i.castSucc i.succ) u + qminor E a b u) =
      ∑ σ : Equiv.Perm (Fin (m + 1)),
        ((Equiv.Perm.sign σ : ℤ) : A) * (Lt E a b u σ i * Md E a b σ i * Rt E a b u σ i) := by
  set s := Equiv.swap i.castSucc i.succ with hs_def
  have hsgn : Equiv.Perm.sign s = -1 := Equiv.Perm.sign_swap (by simp [Fin.ext_iff])
  set G : Equiv.Perm (Fin (m + 1)) → A := fun σ =>
    ((Equiv.Perm.sign σ : ℤ) : A) * (exchangeTwo_self_eq_one E a (b ∘ s) u σ + exchangeTwo_self_eq_one E a b u σ) with hG
  have hsum : qminor E a (b ∘ s) u + qminor E a b u = ∑ σ, G σ := by
    rw [quantumMinor_eq_sum_term, quantumMinor_eq_sum_term, ← Finset.sum_add_distrib]
    simp only [hG, mul_add]
  have hre : ∑ σ, G (σ * s) = ∑ σ, G σ := Fintype.sum_equiv (Equiv.mulRight s) _ _ (fun σ => rfl)
  have hpair : ∀ σ, G σ + G (σ * s) =
      ((Equiv.Perm.sign σ : ℤ) : A) * (Lt E a b u σ i * Md E a b σ i * Rt E a b u σ i) := by
    intro σ
    simp only [hG, Equiv.Perm.sign_mul, hsgn, mul_neg, mul_one, Units.val_neg, Int.cast_neg]
    have k := key_formal E a b i u σ
    rw [← hs_def] at k
    rw [← k]
    noncomm_ring
  rw [hsum, two_smul, ← Finset.sum_congr rfl (fun σ _ => hpair σ), Finset.sum_add_distrib, hre]

def Ead (E : Fin n → Fin n → A) (P Q : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) : A :=
  ∑ a, ∑ b, (P a c * Q d b) • E a b

theorem Tm_Ead (E : Fin n → Fin n → A) {P Q : Matrix (Fin n) (Fin n) ℂ} (hQP : Q * P = 1) (v : ℂ) (c d : Fin n) :
    Tm (Ead E P Q) v c d = ∑ a, ∑ b, (P a c * Q d b) • Tm E v a b := by
  have h1 : ∀ a, ∑ b, (P a c * Q d b) • (if a = b then algebraMap ℂ A v else 0) =
      (P a c * Q d a) • algebraMap ℂ A v := by
    intro a; simp [smul_ite]
  have h2 : ∑ a, P a c * Q d a = if c = d then 1 else 0 := by
    have := congrFun (congrFun hQP d) c
    simp only [Matrix.mul_apply, Matrix.one_apply] at this
    rw [show (∑ a, P a c * Q d a) = ∑ a, Q d a * P a c from Finset.sum_congr rfl fun a _ => mul_comm _ _, this]
    simp [eq_comm]
  unfold Tm Ead
  simp only [smul_add, Finset.sum_add_distrib, h1]
  rw [← Finset.sum_smul, h2]
  split_ifs <;> simp

theorem prod_expand {X : Type*} [Fintype X] :
    ∀ (t : ℕ) (c : Fin t → X → ℂ) (B : Fin t → X → A),
      (List.ofFn fun j => ∑ x, c j x • B j x).prod =
        ∑ φ : Fin t → X, (∏ j, c j (φ j)) • (List.ofFn fun j => B j (φ j)).prod := by
  intro t
  induction t with
  | zero => intro c B; simp
  | succ t ih =>
    intro c B
    rw [List.ofFn_succ, List.prod_cons, ih (fun j => c j.succ) (fun j => B j.succ), Finset.sum_mul]
    rw [← (Fin.consEquiv fun _ : Fin (t + 1) => X).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun φ _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, List.ofFn_succ,
      List.prod_cons, smul_mul_smul_comm]

theorem rowsum_det {t : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (e : Fin t ≃ Fin n) (α : Fin t → Fin n) :
    ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, P (α j) (e (σ j)) =
      (Matrix.of fun i j : Fin t => P (α i) (e j)).det := by
  rw [Matrix.det_apply]
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin t))) _ _ (fun σ => ?_)
  simp only [Equiv.inv_apply, Equiv.Perm.sign_inv, Matrix.of_apply, Units.smul_def, zsmul_eq_mul]
  congr 1
  exact Fintype.prod_equiv σ _ _ (fun j => by simp)

theorem det_rows_perm {t : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (e : Fin t ≃ Fin n) (γ : Equiv.Perm (Fin t)) :
    (Matrix.of fun i j : Fin t => P (e (γ i)) (e j)).det = ((Equiv.Perm.sign γ : ℤ) : ℂ) * P.det := by
  have : (Matrix.of fun i j : Fin t => P (e (γ i)) (e j)) = (P.submatrix e e).submatrix γ id := by
    ext i j; simp
  rw [this, Matrix.det_permute, Matrix.det_submatrix_equiv_self]

theorem det_rows_zero {t : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (e : Fin t ≃ Fin n) (α : Fin t → Fin n)
    (hα : ¬ Function.Injective α) : (Matrix.of fun i j : Fin t => P (α i) (e j)).det = 0 := by
  simp only [Function.Injective, not_forall] at hα
  obtain ⟨i, i', h, hne⟩ := hα
  exact Matrix.det_zero_of_row_eq hne (by funext j; simp [h])

theorem sum_inj {M : Type*} [AddCommMonoid M] {t : ℕ} (e : Fin t ≃ Fin n) (F : (Fin t → Fin n) → M)
    (hF : ∀ α, ¬ Function.Injective α → F α = 0) :
    ∑ α, F α = ∑ γ : Equiv.Perm (Fin t), F (e ∘ γ) := by
  classical
  have himg : ∑ α ∈ (Finset.univ.image fun γ : Equiv.Perm (Fin t) => (e ∘ γ : Fin t → Fin n)), F α = ∑ α, F α := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro α _ hα
    apply hF
    intro hinj
    apply hα
    have hi : Function.Injective (e.symm ∘ α) := e.symm.injective.comp hinj
    have hs : Function.Surjective (e.symm ∘ α) := Finite.injective_iff_surjective.mp hi
    refine Finset.mem_image.mpr ⟨Equiv.ofBijective _ ⟨hi, hs⟩, Finset.mem_univ _, ?_⟩
    funext j
    show e ((e.symm ∘ α) j) = α j
    simp
  rw [← himg, Finset.sum_image]
  intro γ₁ _ γ₂ _ h
  exact Equiv.ext fun j => by have := congrFun h j; simpa using this

theorem qminor_Ead (E : Fin n → Fin n → A) {P Q : Matrix (Fin n) (Fin n) ℂ} (hQP : Q * P = 1) {t : ℕ}
    (e : Fin t ≃ Fin n) (u : ℂ) :
    qminor (Ead E P Q) e e u = P.det • ∑ β : Fin t → Fin n, (∏ j, Q (e j) (β j)) • qminor E e β u := by
  have step1 : ∀ σ : Equiv.Perm (Fin t),
      (List.ofFn fun k : Fin t => Tm (Ead E P Q) (u - (k : ℂ)) (e (σ k)) (e k)).prod =
        ∑ β : Fin t → Fin n, ∑ α : Fin t → Fin n,
          ((∏ j, P (α j) (e (σ j))) * ∏ j, Q (e j) (β j)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α k) (β k)).prod := by
    intro σ
    calc (List.ofFn fun k : Fin t => Tm (Ead E P Q) (u - (k : ℂ)) (e (σ k)) (e k)).prod
        = (List.ofFn fun j : Fin t => ∑ x : Fin n × Fin n,
            (P x.1 (e (σ j)) * Q (e j) x.2) • Tm E (u - (j : ℂ)) x.1 x.2).prod := by
          simp only [Tm_Ead E hQP, ← Finset.sum_product', Finset.univ_product_univ]
      _ = ∑ φ : Fin t → Fin n × Fin n, (∏ j, (P (φ j).1 (e (σ j)) * Q (e j) (φ j).2)) •
            (List.ofFn fun j => Tm E (u - (j : ℂ)) (φ j).1 (φ j).2).prod :=
          by exact prod_expand (X := Fin n × Fin n) t _ _
      _ = _ := by
          rw [← (Equiv.arrowProdEquivProdArrow (Fin t) (fun _ => Fin n) (fun _ => Fin n)).symm.sum_comp, Fintype.sum_prod_type,
            Finset.sum_comm]
          refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => ?_
          simp [Equiv.arrowProdEquivProdArrow, Finset.prod_mul_distrib]
  have inner : ∀ β α : Fin t → Fin n,
      ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : A) *
        (((∏ j, P (α j) (e (σ j))) * ∏ j, Q (e j) (β j)) •
          (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α k) (β k)).prod) =
      ((Matrix.of fun i j : Fin t => P (α i) (e j)).det * ∏ j, Q (e j) (β j)) •
          (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α k) (β k)).prod := by
    intro β α
    rw [← rowsum_det P e α, Finset.sum_mul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [show ((Equiv.Perm.sign σ : ℤ) : A) = algebraMap ℂ A ((Equiv.Perm.sign σ : ℤ) : ℂ) by simp,
      ← Algebra.smul_def, smul_smul, mul_assoc]
  calc qminor (Ead E P Q) e e u
      = ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : A) * ∑ β : Fin t → Fin n, ∑ α : Fin t → Fin n,
          ((∏ j, P (α j) (e (σ j))) * ∏ j, Q (e j) (β j)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α k) (β k)).prod := by
        unfold qminor; simp only [step1]
    _ = ∑ β : Fin t → Fin n, ∑ α : Fin t → Fin n, ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : A) *
          (((∏ j, P (α j) (e (σ j))) * ∏ j, Q (e j) (β j)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α k) (β k)).prod) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun β _ => Finset.sum_comm
    _ = ∑ β : Fin t → Fin n, ∑ α : Fin t → Fin n,
          ((Matrix.of fun i j : Fin t => P (α i) (e j)).det * ∏ j, Q (e j) (β j)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α k) (β k)).prod := by
        simp only [inner]
    _ = ∑ β : Fin t → Fin n, ∑ γ : Equiv.Perm (Fin t),
          ((Matrix.of fun i j : Fin t => P (e (γ i)) (e j)).det * ∏ j, Q (e j) (β j)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (e (γ k)) (β k)).prod := by
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [sum_inj e _ (fun α hα => by rw [det_rows_zero P e α hα, zero_mul, zero_smul])]
        rfl
    _ = ∑ β : Fin t → Fin n, P.det • ((∏ j, Q (e j) (β j)) • qminor E e β u) := by
        refine Finset.sum_congr rfl fun β _ => ?_
        unfold qminor
        rw [Finset.smul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun γ _ => ?_
        rw [det_rows_perm P e γ,
          show ((Equiv.Perm.sign γ : ℤ) : A) = algebraMap ℂ A ((Equiv.Perm.sign γ : ℤ) : ℂ) by simp,
          ← Algebra.smul_def, smul_smul, smul_smul]
        congr 1
        ring
    _ = _ := by rw [Finset.smul_sum]

end Formalism.FourierDecayAlt.P.JFxE
end
end

section
open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

abbrev Ix (k r : ℕ) := Fin (2 * r + k + 1) × Fin (2 * r + k + 1)

abbrev VV (k r : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] := List (Ix k r) → (Mat k r → E)

abbrev AA (k r : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] := Module.End ℂ (VV k r E)

def ell (x : Ix k r) : AA k r E := LinearMap.funLeft ℂ (Mat k r → E) (fun w : List (Ix k r) => w ++ [x])

theorem ell_apply (x : Ix k r) (Φ : VV k r E) (w : List (Ix k r)) : ell x Φ w = Φ (w ++ [x]) := rfl

def Lf (k r : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (a b : Fin (2 * r + k + 1)) : AA k r E :=
  ell (a, b)

def Rep (d : ℕ) (a : AA k r E) : Prop :=
  ∃ L : List (ℂ × List (Ix k r)), (∀ p ∈ L, p.2.length ≤ d) ∧
    ∀ Φ w, a Φ w = (L.map fun p => p.1 • Φ (w ++ p.2)).sum

section RepLemmas

theorem Rep.mono {d d' : ℕ} (h : d ≤ d') {a : AA k r E} (ha : Rep d a) : Rep d' a := by
  obtain ⟨L, hL, h'⟩ := ha
  exact ⟨L, fun p hp => (hL p hp).trans h, h'⟩

theorem rep_zero (d : ℕ) : Rep d (0 : AA k r E) := by
  exact ⟨[], by simp, fun Φ w => by simp⟩

theorem rep_ell (x : Ix k r) : Rep 1 (ell x : AA k r E) := by
  exact ⟨[(1, [x])], by simp, fun Φ w => by simp [ell_apply]⟩

theorem rep_add {d : ℕ} {a b : AA k r E} (ha : Rep d a) (hb : Rep d b) : Rep d (a + b) := by
  obtain ⟨La, hLa, ha'⟩ := ha
  obtain ⟨Lb, hLb, hb'⟩ := hb
  refine ⟨La ++ Lb, fun p hp => ?_, fun Φ w => ?_⟩
  · rcases List.mem_append.mp hp with h | h
    exacts [hLa p h, hLb p h]
  · rw [LinearMap.add_apply, Pi.add_apply, ha', hb', List.map_append, List.sum_append]

theorem rep_smul {d : ℕ} (c : ℂ) {a : AA k r E} (ha : Rep d a) : Rep d (c • a) := by
  obtain ⟨L, hL, h⟩ := ha
  refine ⟨L.map fun p => (c * p.1, p.2), ?_, fun Φ w => ?_⟩
  · intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact hL q hq
  · rw [LinearMap.smul_apply, Pi.smul_apply, h, List.smul_sum]
    simp only [List.map_map, Function.comp_def, mul_smul]

theorem rep_sub {d : ℕ} {a b : AA k r E} (ha : Rep d a) (hb : Rep d b) : Rep d (a - b) := by
  have h1 := rep_add ha (rep_smul (-1) hb)
  first
    | (simpa [neg_one_smul] using h1)
    | (simpa [sub_eq_add_neg, neg_one_smul] using h1)

private theorem exists_word_expansion_length_le_add {d e : ℕ} {b : AA k r E} (Lb : List (ℂ × List (Ix k r)))
    (hLb : ∀ q ∈ Lb, q.2.length ≤ e) (hb : ∀ Φ w, b Φ w = (Lb.map fun q => q.1 • Φ (w ++ q.2)).sum) :
    ∀ La : List (ℂ × List (Ix k r)), (∀ p ∈ La, p.2.length ≤ d) →
      ∃ L : List (ℂ × List (Ix k r)), (∀ p ∈ L, p.2.length ≤ d + e) ∧
        ∀ Φ w, (La.map fun p => p.1 • (b Φ) (w ++ p.2)).sum = (L.map fun p => p.1 • Φ (w ++ p.2)).sum := by
  intro La
  induction La with
  | nil => intro _; exact ⟨[], by simp, fun _ _ => by simp⟩
  | cons p La ih =>
    intro hLa
    obtain ⟨L, hL, hL'⟩ := ih (fun q hq => hLa q (by simp [hq]))
    refine ⟨(Lb.map fun q => (p.1 * q.1, p.2 ++ q.2)) ++ L, ?_, ?_⟩
    · intro q hq
      simp only [List.mem_append, List.mem_map] at hq
      rcases hq with ⟨q', hq', rfl⟩ | hq
      · have h1 := hLa p (by simp)
        have h2 := hLb q' hq'
        simp only [List.length_append]
        omega
      · exact hL q hq
    · intro Φ w
      rw [List.map_cons, List.sum_cons, hL' Φ w, List.map_append, List.sum_append, hb, List.smul_sum]
      congr 1
      simp only [List.map_map, Function.comp_def, mul_smul, List.append_assoc]

theorem rep_mul {d e : ℕ} {a b : AA k r E} (ha : Rep d a) (hb : Rep e b) : Rep (d + e) (a * b) := by
  obtain ⟨La, hLa, ha'⟩ := ha
  obtain ⟨Lb, hLb, hb'⟩ := hb
  obtain ⟨L, hL, hL'⟩ := exists_word_expansion_length_le_add Lb hLb hb' La hLa
  refine ⟨L, hL, fun Φ w => ?_⟩
  show a (b Φ) w = _
  rw [ha', hL']

end RepLemmas

def HC (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) : Prop :=
  ∀ a b (m : ℕ) (f : Mat k r → E), CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f → CkOn (m : ℕ∞) (GV k r) (Eop a b f)

def HL (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) : Prop :=
  ∀ a b (f f₂ : Mat k r → E), (∀ g ∈ GV k r, f g = f₂ g) → ∀ g ∈ GV k r, Eop a b f g = Eop a b f₂ g

def HA (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) : Prop :=
  ∀ a b (f f₂ : Mat k r → E), CkOn 1 (GV k r) f → CkOn 1 (GV k r) f₂ → ∀ g ∈ GV k r,
    Eop a b (fun x => f x + f₂ x) g = Eop a b f g + Eop a b f₂ g

def HS (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) : Prop :=
  ∀ a b (c : ℂ) (f : Mat k r → E), CkOn 1 (GV k r) f → ∀ g ∈ GV k r, Eop a b (fun x => c • f x) g = c • Eop a b f g

def HGl (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) : Prop :=
  ∀ a b c d (f : Mat k r → E), CkOn 2 (GV k r) f → ∀ g ∈ GV k r,
    Eop a b (Eop c d f) g - Eop c d (Eop a b f) g =
      (if b = c then Eop a d f g else 0) - (if d = a then Eop c b f g else 0)

def Fw (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) (w : List (Ix k r))
    (f : Mat k r → E) : Mat k r → E :=
  w.foldr (fun x φ => Eop x.1 x.2 φ) f

def Phi (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) (f : Mat k r → E) :
    VV k r E := fun w => Fw Eop w f

def ev (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) (a : AA k r E)
    (f : Mat k r → E) : Mat k r → E := a (Phi Eop f) []

section Words

variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))

theorem Fw_append (w q : List (Ix k r)) (f : Mat k r → E) : Fw Eop (w ++ q) f = Fw Eop w (Fw Eop q f) := by
  simp [Fw, List.foldr_append]

theorem Fw_ck (hC : HC Eop) : ∀ (w : List (Ix k r)) (m : ℕ) (f : Mat k r → E),
    CkOn ((m + w.length : ℕ) : ℕ∞) (GV k r) f → CkOn (m : ℕ∞) (GV k r) (Fw Eop w f) := by
  intro w
  induction w with
  | nil => intro m f hf; simpa [Fw] using hf
  | cons x w ih =>
    intro m f hf
    have h1 : CkOn (((m + 1) + w.length : ℕ) : ℕ∞) (GV k r) f := by
      have e : (m + 1) + w.length = m + (x :: w).length := by simp only [List.length_cons]; omega
      rw [e]; exact hf
    exact hC x.1 x.2 m _ (ih (m + 1) f h1)

theorem ck_mono' {m m' : ℕ} (h : m ≤ m') {f : Mat k r → E} (hf : CkOn ((m' : ℕ) : ℕ∞) (GV k r) f) :
    CkOn ((m : ℕ) : ℕ∞) (GV k r) f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hg, hcd, hfe⟩ := hf g₀ hg₀
  refine ⟨U, f', hU, hg, hcd.of_le ?_, hfe⟩
  first | exact_mod_cast h | exact WithTop.coe_le_coe.mpr (Nat.cast_le.mpr h) | (norm_cast)

theorem Fw_add (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) : ∀ (w : List (Ix k r)) (f f₂ : Mat k r → E),
    CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f → CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f₂ →
    ∀ g ∈ GV k r, Fw Eop w (fun x => f x + f₂ x) g = Fw Eop w f g + Fw Eop w f₂ g := by
  intro w
  induction w with
  | nil => intro f f₂ _ _ g _; rfl
  | cons x w ih =>
    intro f f₂ hf hf₂ g hg
    have hf' : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f := ck_mono' (by simp) hf
    have hf₂' : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f₂ := ck_mono' (by simp) hf₂
    have e : 1 + w.length = (x :: w).length := by simp only [List.length_cons]; omega
    have c1 : CkOn 1 (GV k r) (Fw Eop w f) := by
      have h' : CkOn ((1 + w.length : ℕ) : ℕ∞) (GV k r) f := by rw [e]; exact hf
      simpa using Fw_ck Eop hC w 1 f h'
    have c2 : CkOn 1 (GV k r) (Fw Eop w f₂) := by
      have h' : CkOn ((1 + w.length : ℕ) : ℕ∞) (GV k r) f₂ := by rw [e]; exact hf₂
      simpa using Fw_ck Eop hC w 1 f₂ h'
    show Eop x.1 x.2 (Fw Eop w (fun y => f y + f₂ y)) g =
      Eop x.1 x.2 (Fw Eop w f) g + Eop x.1 x.2 (Fw Eop w f₂) g
    rw [hL x.1 x.2 _ (fun y => Fw Eop w f y + Fw Eop w f₂ y) (ih f f₂ hf' hf₂') g hg]
    exact hA x.1 x.2 _ _ c1 c2 g hg

theorem Fw_smul (hC : HC Eop) (hL : HL Eop) (hS : HS Eop) : ∀ (w : List (Ix k r)) (c : ℂ) (f : Mat k r → E),
    CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f → ∀ g ∈ GV k r, Fw Eop w (fun x => c • f x) g = c • Fw Eop w f g := by
  intro w
  induction w with
  | nil => intro c f _ g _; rfl
  | cons x w ih =>
    intro c f hf g hg
    have hf' : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f := ck_mono' (by simp) hf
    have e : 1 + w.length = (x :: w).length := by simp only [List.length_cons]; omega
    have c1 : CkOn 1 (GV k r) (Fw Eop w f) := by
      have h' : CkOn ((1 + w.length : ℕ) : ℕ∞) (GV k r) f := by rw [e]; exact hf
      simpa using Fw_ck Eop hC w 1 f h'
    show Eop x.1 x.2 (Fw Eop w (fun y => c • f y)) g = c • Eop x.1 x.2 (Fw Eop w f) g
    rw [hL x.1 x.2 _ (fun y => c • Fw Eop w f y) (ih c f hf') g hg]
    exact hS x.1 x.2 c _ c1 g hg

theorem Fw_zero (hC : HC Eop) (hL : HL Eop) (hS : HS Eop) (w : List (Ix k r)) :
    ∀ g ∈ GV k r, Fw Eop w (fun _ => (0 : E)) g = 0 := by
  intro g hg
  have h0 : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) (fun _ : Mat k r => (0 : E)) :=
    fun g₀ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩
  have h1 := Fw_smul Eop hC hL hS w 0 (fun _ => (0 : E)) h0 g hg
  simpa using h1

theorem ck_lsum {m : ℕ∞} (L : List (ℂ × (Mat k r → E))) (h : ∀ p ∈ L, CkOn m (GV k r) p.2) :
    CkOn m (GV k r) (fun x => (L.map fun p => p.1 • p.2 x).sum) := by
  induction L with
  | nil =>
    intro g₀ _
    exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => by simp⟩
  | cons p L ih =>
    intro g₀ hg₀
    obtain ⟨U1, f1, hU1, hg1, hc1, he1⟩ := h p (by simp) g₀ hg₀
    obtain ⟨U2, f2, hU2, hg2, hc2, he2⟩ := ih (fun q hq => h q (by simp [hq])) g₀ hg₀
    refine ⟨U1 ∩ U2, fun x => p.1 • f1 x + f2 x, hU1.inter hU2, ⟨hg1, hg2⟩,
      ((hc1.mono Set.inter_subset_left).const_smul p.1).add (hc2.mono Set.inter_subset_right), ?_⟩
    intro g hg hgG
    simp only [List.map_cons, List.sum_cons]
    rw [he1 g hg.1 hgG]
    congr 1
    exact he2 g hg.2 hgG

theorem Fw_lsum (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop) (w : List (Ix k r)) :
    ∀ (L : List (ℂ × (Mat k r → E))), (∀ p ∈ L, CkOn ((w.length : ℕ) : ℕ∞) (GV k r) p.2) →
    ∀ g ∈ GV k r, Fw Eop w (fun x => (L.map fun p => p.1 • p.2 x).sum) g = (L.map fun p => p.1 • Fw Eop w p.2 g).sum := by
  intro L
  induction L with
  | nil =>
    intro _ g hg
    simp only [List.map_nil, List.sum_nil]
    exact Fw_zero Eop hC hL hS w g hg
  | cons p L ih =>
    intro h g hg
    have hL' : ∀ q ∈ L, CkOn ((w.length : ℕ) : ℕ∞) (GV k r) q.2 := fun q hq => h q (by simp [hq])
    have hs : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) (fun x => p.1 • p.2 x) := by
      intro g₀ hg₀
      obtain ⟨U, f', hU, hg', hc, he⟩ := h p (by simp) g₀ hg₀
      exact ⟨U, fun x => p.1 • f' x, hU, hg', hc.const_smul p.1, fun g hg hgG => by simp only [he g hg hgG]⟩
    have hr := ck_lsum L hL'
    simp only [List.map_cons, List.sum_cons]
    rw [Fw_add Eop hC hL hA w (fun x => p.1 • p.2 x) _ hs hr g hg,
      Fw_smul Eop hC hL hS w p.1 p.2 (h p (by simp)) g hg, ih hL' g hg]

end Words

section Values

variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))

theorem lsum_apply {ι : Type*} (l : List ι) (F : ι → Mat k r → E) (x : Mat k r) :
    (l.map F).sum x = (l.map fun i => F i x).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

theorem ev_rep_ex {d : ℕ} {a : AA k r E} (ha : Rep d a) :
    ∃ L : List (ℂ × List (Ix k r)), (∀ p ∈ L, p.2.length ≤ d) ∧
      ∀ f x, ev Eop a f x = (L.map fun p => p.1 • Fw Eop p.2 f x).sum := by
  obtain ⟨L, hL, h⟩ := ha
  refine ⟨L, hL, fun f x => ?_⟩
  simp only [ev, h, lsum_apply, List.nil_append, Pi.smul_apply, Phi]

theorem ev_ck (hC : HC Eop) {d : ℕ} {a : AA k r E} (ha : Rep d a) (m : ℕ) (f : Mat k r → E)
    (hf : CkOn ((m + d : ℕ) : ℕ∞) (GV k r) f) : CkOn (m : ℕ∞) (GV k r) (ev Eop a f) := by
  obtain ⟨L, hL, h⟩ := ev_rep_ex Eop ha
  have e : ev Eop a f = fun x => ((L.map fun p => (p.1, Fw Eop p.2 f)).map fun q => q.1 • q.2 x).sum := by
    funext x
    rw [h]
    simp [List.map_map, Function.comp_def]
  rw [e]
  apply ck_lsum
  intro q hq
  simp only [List.mem_map] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  exact Fw_ck Eop hC p.2 m f (ck_mono' (by have := hL p hp; omega) hf)

theorem ev_zero (hC : HC Eop) (hL : HL Eop) (hS : HS Eop) {d : ℕ} {a : AA k r E} (ha : Rep d a) :
    ∀ g ∈ GV k r, ev Eop a (fun _ => (0 : E)) g = 0 := by
  obtain ⟨L, _, hrep⟩ := ev_rep_ex Eop ha
  intro g hg
  rw [hrep]
  apply List.sum_eq_zero
  intro y hy
  simp only [List.mem_map] at hy
  obtain ⟨p, _, rfl⟩ := hy
  rw [Fw_zero Eop hC hL hS p.2 g hg, smul_zero]

theorem ev_add (a b : AA k r E) (f : Mat k r → E) (x : Mat k r) : ev Eop (a + b) f x = ev Eop a f x + ev Eop b f x :=
  rfl

theorem ev_sub (a b : AA k r E) (f : Mat k r → E) (x : Mat k r) : ev Eop (a - b) f x = ev Eop a f x - ev Eop b f x :=
  rfl

theorem ev_smul (c : ℂ) (a : AA k r E) (f : Mat k r → E) (x : Mat k r) : ev Eop (c • a) f x = c • ev Eop a f x :=
  rfl

theorem ev_fsum {ι : Type*} (s : Finset ι) (F : ι → AA k r E) (f : Mat k r → E) (x : Mat k r) :
    ev Eop (∑ i ∈ s, F i) f x = ∑ i ∈ s, ev Eop (F i) f x := by
  first
    | (simp [ev, LinearMap.sum_apply, Finset.sum_apply]; done)
    | (simp only [ev, LinearMap.coeFn_sum, Finset.sum_apply])


theorem ev_intCast_mul (z : ℤ) (a : AA k r E) (f : Mat k r → E) (x : Mat k r) :
    ev Eop ((z : AA k r E) * a) f x = (z : ℂ) • ev Eop a f x := by
  rw [← map_intCast (algebraMap ℂ (AA k r E)) z]
  first
    | (simp only [ev, Module.End.mul_apply, Module.algebraMap_end_apply, Pi.smul_apply]; done)
    | (simp only [ev, LinearMap.mul_apply, Module.algebraMap_end_apply, Pi.smul_apply]; done)
    | rfl

theorem ev_mul (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop) {d e : ℕ} {a b : AA k r E}
    (ha : Rep d a) (hb : Rep e b) (f : Mat k r → E) (hf : CkOn ((d + e : ℕ) : ℕ∞) (GV k r) f) :
    ∀ g ∈ GV k r, ev Eop (a * b) f g = ev Eop a (ev Eop b f) g := by
  obtain ⟨La, hLa, ha'⟩ := ha
  obtain ⟨Lb, hLb, hb'⟩ := hb
  have hev : ev Eop b f = fun x => ((Lb.map fun q => (q.1, Fw Eop q.2 f)).map fun q => q.1 • q.2 x).sum := by
    funext x
    simp only [ev, hb', lsum_apply, List.nil_append, Pi.smul_apply, Phi, List.map_map, Function.comp_def]
  intro g hg
  show a (b (Phi Eop f)) [] g = a (Phi Eop (ev Eop b f)) [] g
  rw [ha', ha', lsum_apply, lsum_apply]
  congr 1
  apply List.map_congr_left
  intro p hp
  simp only [List.nil_append, Pi.smul_apply]
  congr 1
  have hck : ∀ q ∈ Lb.map (fun q => (q.1, Fw Eop q.2 f)), CkOn ((p.2.length : ℕ) : ℕ∞) (GV k r) q.2 := by
    intro q' hq'
    simp only [List.mem_map] at hq'
    obtain ⟨q, hq, rfl⟩ := hq'
    exact Fw_ck Eop hC q.2 p.2.length f (ck_mono' (by have := hLa p hp; have := hLb q hq; omega) hf)
  show b (Phi Eop f) p.2 g = Fw Eop p.2 (ev Eop b f) g
  rw [hev, Fw_lsum Eop hC hL hA hS p.2 _ hck g hg, hb', lsum_apply]
  simp only [List.map_map, Function.comp_def, Pi.smul_apply, Phi, Fw_append]

end Values

end Formalism.FourierDecayAlt.P.JFxE
end
end

section
open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

section Bridge

variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))

private theorem rep_zero_lemma_2 (d : ℕ) : Rep d (0 : AA k r E) :=
  ⟨[], by simp, fun _ _ => by simp⟩

theorem rep_Tm_of {Λ : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → AA k r E} (hΛ : ∀ c d, Rep 1 (Λ c d))
    (v : ℂ) (c d : Fin (2 * r + k + 1)) : Rep 1 (Tm Λ v c d) := by
  simp only [Formalism.REAL.Tm]
  refine rep_add ?_ (hΛ c d)
  split_ifs
  · exact ⟨[(v, [])], by simp, fun _ _ => by simp⟩
  · exact rep_zero_lemma_2 1

theorem ev_one (f : Mat k r → E) : ev Eop (1 : AA k r E) f = f := rfl

private theorem ckOn_mono_lemma_4 {m m' : ℕ∞} (h : m' ≤ m) {f : Mat k r → E} (hf : CkOn m (GV k r) f) :
    CkOn m' (GV k r) f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hcd, heq⟩ := hf g₀ hg₀
  exact ⟨U, f', hU, hgU, hcd.of_le (WithTop.coe_le_coe.mpr h), heq⟩

private theorem rep_prod_lemma_3 {Λ : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → AA k r E} (hΛ : ∀ c d, Rep 1 (Λ c d)) :
    ∀ ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)),
      Rep ts.length ((ts.map fun t => Tm Λ t.1 t.2.1 t.2.2).prod) := by
  intro ts
  induction ts with
  | nil => exact ⟨[(1, [])], by simp, fun _ _ => by simp⟩
  | cons t ts ih =>
    rw [List.map_cons, List.prod_cons]
    exact Rep.mono (by simp only [List.length_cons]; omega) (rep_mul (rep_Tm_of hΛ _ _ _) ih)

theorem bridge_fold (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop)
    {Λ : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → AA k r E} (hΛ : ∀ c d, Rep 1 (Λ c d))
    (Op : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) (hLop : HL Op)
    (hT : ∀ v c d (φ : Mat k r → E), CkOn 1 (GV k r) φ → ∀ g ∈ GV k r, ev Eop (Tm Λ v c d) φ g = Top Op v c d φ g) :
    ∀ (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (f : Mat k r → E),
      CkOn ((ts.length : ℕ) : ℕ∞) (GV k r) f → ∀ g ∈ GV k r,
        ev Eop ((ts.map fun t => Tm Λ t.1 t.2.1 t.2.2).prod) f g =
          (ts.map fun t => Top Op t.1 t.2.1 t.2.2).foldr (fun T h => T h) f g := by
  intro ts
  induction ts with
  | nil =>
    intro f _ g _
    simp [ev_one]
  | cons t ts ih =>
    intro f hf g hg
    have hP := rep_prod_lemma_3 hΛ ts
    have hf' : CkOn ((1 + ts.length : ℕ) : ℕ∞) (GV k r) f :=
      ckOn_mono_lemma_4 (ENat.coe_le_coe.mpr (by simp only [List.length_cons]; omega)) hf
    have hfs : CkOn ((ts.length : ℕ) : ℕ∞) (GV k r) f :=
      ckOn_mono_lemma_4 (ENat.coe_le_coe.mpr (by simp only [List.length_cons]; omega)) hf
    have hφ : CkOn 1 (GV k r) (ev Eop ((ts.map fun t => Tm Λ t.1 t.2.1 t.2.2).prod) f) := by
      simpa using ev_ck (Eop := Eop) hC hP 1 f hf'
    have hI := ih f hfs
    rw [List.map_cons, List.prod_cons,
      ev_mul (Eop := Eop) hC hL hA hS (rep_Tm_of hΛ _ _ _) hP f hf' g hg, hT _ _ _ _ hφ g hg]
    simp only [List.map_cons, List.foldr_cons, Formalism.QuantumDeterminants.Top]
    rw [hLop _ _ _ _ hI g hg, hI g hg]

theorem ev_Tm_Lf (v : ℂ) (a b : Fin (2 * r + k + 1)) (φ : Mat k r → E) (x : Mat k r) :
    ev Eop (Tm (Lf k r E) v a b) φ x = Top Eop v a b φ x := by
  simp only [ev, Formalism.REAL.Tm, Formalism.QuantumDeterminants.Top]
  split_ifs <;> simp [Lf, Formalism.FourierDecayAlt.P.JFxE.ell, Phi, Fw]

theorem bridge_qminor (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop)
    {Λ : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → AA k r E} (hΛ : ∀ c d, Rep 1 (Λ c d))
    (Op : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) (hLop : HL Op)
    (hT : ∀ v c d (φ : Mat k r → E), CkOn 1 (GV k r) φ → ∀ g ∈ GV k r, ev Eop (Tm Λ v c d) φ g = Top Op v c d φ g)
    {t : ℕ} (p q : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (f : Mat k r → E) (hf : CkOn ((t : ℕ) : ℕ∞) (GV k r) f) :
    ∀ g ∈ GV k r, ev Eop (qminor Λ p q u) f g = qminorOp Op p q u f g := by
  intro g hg
  simp only [qminor, ev, Formalism.QuantumDeterminants.qminorOp, LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hb := bridge_fold Eop hC hL hA hS hΛ Op hLop hT
    (List.ofFn fun j => (u - ((j : ℕ) : ℂ), p (σ j), q j)) f (by simpa using hf) g hg
  simp only [List.map_ofFn, Function.comp_def, ev] at hb
  simp [hb, Int.cast_smul_eq_zsmul]

end Bridge

section Skew

variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))

private theorem rep_Lf_lemma (a b : Fin (2 * r + k + 1)) : Rep 1 (Lf k r E a b) :=
  ⟨[(1, [(a, b)])], by simp, fun _ _ => by simp [Lf, Formalism.FourierDecayAlt.P.JFxE.ell]⟩

theorem rep_rel (a b c d : Fin (2 * r + k + 1)) : Rep 2 (rel (Lf k r E) a b c d) := by
  simp only [Formalism.FourierDecayAlt.P.JFxE.rel]
  have h1 := rep_Lf_lemma (k := k) (r := r) (E := E)
  refine rep_sub (rep_sub (rep_mul (h1 a b) (h1 c d)) (rep_mul (h1 c d) (h1 a b))) (rep_sub ?_ ?_) <;>
    split_ifs
  all_goals first
    | exact Rep.mono (by norm_num) (h1 _ _)
    | exact rep_zero_lemma_2 2

theorem ev_rel (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop) (hG : HGl Eop)
    (a b c d : Fin (2 * r + k + 1)) (ψ : Mat k r → E) (hψ : CkOn 2 (GV k r) ψ) :
    ∀ g ∈ GV k r, ev Eop (rel (Lf k r E) a b c d) ψ g = 0 := by
  intro g hg
  have hLf : ∀ (a b : Fin (2 * r + k + 1)) (φ : Mat k r → E), ev Eop (Lf k r E a b) φ = Eop a b φ := by
    intro a b φ
    funext x
    simp [ev, Lf, Formalism.FourierDecayAlt.P.JFxE.ell, Phi, Fw]
  have hz : ∀ φ : Mat k r → E, ev Eop (0 : AA k r E) φ = 0 := by
    intro φ
    funext x
    simp [ev]
  have hsub : ∀ (x y : AA k r E) (φ : Mat k r → E), ev Eop (x - y) φ g = ev Eop x φ g - ev Eop y φ g := by
    intro x y φ
    simp [ev]
  have h1 := rep_Lf_lemma (k := k) (r := r) (E := E)
  have hm : ∀ a b c d : Fin (2 * r + k + 1),
      ev Eop (Lf k r E a b * Lf k r E c d) ψ g = Eop a b (Eop c d ψ) g := by
    intro a b c d
    rw [ev_mul (Eop := Eop) hC hL hA hS (h1 a b) (h1 c d) ψ hψ g hg, hLf, hLf]
  simp only [Formalism.FourierDecayAlt.P.JFxE.rel]
  rw [hsub, hsub, hsub, hm, hm, hG a b c d ψ hψ g hg]
  split_ifs <;> simp [hLf, hz]

theorem rep_Md {m : ℕ} (a b : Fin (m + 1) → Fin (2 * r + k + 1)) (σ : Equiv.Perm (Fin (m + 1))) (i : Fin m) :
    Rep 2 (Md (Lf k r E) a b σ i) := by
  unfold Md
  exact rep_add (rep_rel _ _ _ _) (rep_rel _ _ _ _)

theorem rep_fac_list {m : ℕ} (a b : Fin (m + 1) → Fin (2 * r + k + 1)) (u : ℂ) (σ : Equiv.Perm (Fin (m + 1))) :
    ∀ x ∈ List.ofFn (fac (Lf k r E) a b u σ), Rep 1 x := by
  intro x hx
  rw [List.mem_ofFn] at hx
  obtain ⟨j, rfl⟩ := hx
  exact rep_Tm_of (fun c d => rep_Lf_lemma c d) _ _ _

private theorem fw_local_lemma_7 (hL : HL Eop) (w : List (Ix k r)) (f f₂ : Mat k r → E)
    (h : ∀ g ∈ GV k r, f g = f₂ g) : ∀ g ∈ GV k r, Fw Eop w f g = Fw Eop w f₂ g := by
  induction w with
  | nil => simpa [Fw] using h
  | cons x w ih =>
    intro g hg
    simp only [Fw, List.foldr_cons] at ih ⊢
    exact hL _ _ _ _ ih g hg

private theorem ev_local_lemma_8 (hL : HL Eop) {d : ℕ} {a : AA k r E} (ha : Rep d a) (f f₂ : Mat k r → E)
    (h : ∀ g ∈ GV k r, f g = f₂ g) : ∀ g ∈ GV k r, ev Eop a f g = ev Eop a f₂ g := by
  intro g hg
  obtain ⟨L, -, hLa⟩ := ha
  simp only [ev, hLa, Phi, List.nil_append]
  have key : ∀ L' : List (ℂ × List (Ix k r)),
      (L'.map fun p => p.1 • Fw Eop p.2 f).sum g = (L'.map fun p => p.1 • Fw Eop p.2 f₂).sum g := by
    intro L'
    induction L' with
    | nil => simp
    | cons p L' ih =>
      simp only [List.map_cons, List.sum_cons, Pi.add_apply, Pi.smul_apply, ih,
        fw_local_lemma_7 Eop hL p.2 f f₂ h g hg]
  exact key L

private theorem rep_list_lemma_9 : ∀ l : List (AA k r E), (∀ x ∈ l, Rep 1 x) → Rep l.length l.prod := by
  intro l
  induction l with
  | nil => intro _; exact ⟨[(1, [])], by simp, fun _ _ => by simp⟩
  | cons x l ih =>
    intro h
    rw [List.prod_cons]
    exact Rep.mono (by simp only [List.length_cons]; omega)
      (rep_mul (h x (by simp)) (ih fun y hy => h y (by simp [hy])))

theorem ev_LMR (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop) (hG : HGl Eop) {m : ℕ}
    (a b : Fin (m + 1) → Fin (2 * r + k + 1)) (u : ℂ) (σ : Equiv.Perm (Fin (m + 1))) (i : Fin m)
    (f : Mat k r → E) (hf : CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f) :
    ∀ g ∈ GV k r, ev Eop (Lt (Lf k r E) a b u σ i * Md (Lf k r E) a b σ i * Rt (Lf k r E) a b u σ i) f g = 0 := by
  intro g hg
  unfold Lt Rt
  have h0 : ∀ φ : Mat k r → E, ev Eop (0 : AA k r E) φ = 0 := by
    intro φ
    funext x
    simp [ev]
  have hadd : ∀ (x y : AA k r E) (φ : Mat k r → E) (g' : Mat k r),
      ev Eop (x + y) φ g' = ev Eop x φ g' + ev Eop y φ g' := by
    intro x y φ g'
    simp [ev]
  have hL1 := rep_fac_list (k := k) (r := r) (E := E) a b u σ
  set L := List.ofFn (fac (Lf k r E) a b u σ) with hLdef
  have hLt := rep_list_lemma_9 (L.take i) (fun x hx => hL1 x (List.mem_of_mem_take hx))
  have hRt := rep_list_lemma_9 (L.drop ((i : ℕ) + 2)) (fun x hx => hL1 x (List.mem_of_mem_drop hx))
  have hMd := rep_Md (k := k) (r := r) (E := E) a b σ i
  have hlen : (L.take i).length + 2 + (L.drop ((i : ℕ) + 2)).length = m + 1 := by
    have := i.isLt
    simp only [hLdef, List.length_take, List.length_drop, List.length_ofFn]
    omega
  have hf3 : CkOn (((L.take i).length + 2 + (L.drop ((i : ℕ) + 2)).length : ℕ) : ℕ∞) (GV k r) f := by
    rw [hlen]
    exact hf
  have hψ : CkOn (((L.take i).length + 2 : ℕ) : ℕ∞) (GV k r) (ev Eop (L.drop ((i : ℕ) + 2)).prod f) :=
    ev_ck (Eop := Eop) hC hRt _ f hf3
  have hψ2 : CkOn 2 (GV k r) (ev Eop (L.drop ((i : ℕ) + 2)).prod f) := by
    have := ev_ck (Eop := Eop) hC hRt 2 f (ckOn_mono_lemma_4 (ENat.coe_le_coe.mpr (by omega)) hf3)
    simpa using this
  have hz : ∀ g' ∈ GV k r,
      ev Eop (Md (Lf k r E) a b σ i) (ev Eop (L.drop ((i : ℕ) + 2)).prod f) g' = 0 := by
    intro g' hg'
    unfold Md
    rw [hadd, ev_rel Eop hC hL hA hS hG _ _ _ _ _ hψ2 g' hg', ev_rel Eop hC hL hA hS hG _ _ _ _ _ hψ2 g' hg',
      add_zero]
  rw [ev_mul (Eop := Eop) hC hL hA hS (rep_mul hLt hMd) hRt f hf3 g hg,
    ev_mul (Eop := Eop) hC hL hA hS hLt hMd _ hψ g hg,
    ev_local_lemma_8 Eop hL hLt (ev Eop (Md (Lf k r E) a b σ i) (ev Eop (L.drop ((i : ℕ) + 2)).prod f))
      (ev Eop (0 : AA k r E) (ev Eop (L.drop ((i : ℕ) + 2)).prod f))
      (fun g' hg' => by simp [hz g' hg', h0]) g hg,
    ← ev_mul (Eop := Eop) hC hL hA hS hLt (rep_zero_lemma_2 2) _ hψ g hg]
  simp [h0]

theorem sk_adj (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop) (hG : HGl Eop) {m : ℕ}
    (a b : Fin (m + 1) → Fin (2 * r + k + 1)) (i : Fin m) (u : ℂ)
    (f : Mat k r → E) (hf : CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f) :
    ∀ g ∈ GV k r, ev Eop (qminor (Lf k r E) a (b ∘ Equiv.swap i.castSucc i.succ) u) f g =
      - ev Eop (qminor (Lf k r E) a b u) f g := by
  intro g hg
  have hR : ∀ σ : Equiv.Perm (Fin (m + 1)),
      (Lt (Lf k r E) a b u σ i * Md (Lf k r E) a b σ i * Rt (Lf k r E) a b u σ i) (Phi Eop f) [] g = 0 :=
    fun σ => ev_LMR Eop hC hL hA hS hG a b u σ i f hf g hg
  have hR' : ∀ σ : Equiv.Perm (Fin (m + 1)),
      (((Equiv.Perm.sign σ : ℤ) : AA k r E) *
        (Lt (Lf k r E) a b u σ i * Md (Lf k r E) a b σ i * Rt (Lf k r E) a b u σ i)) (Phi Eop f) [] g = 0 := by
    intro σ
    have h0 := hR σ
    generalize Lt (Lf k r E) a b u σ i * Md (Lf k r E) a b σ i * Rt (Lf k r E) a b u σ i = P at h0 ⊢
    simp [h0]
  have h := congrArg (fun x : AA k r E => x (Phi Eop f) [] g) (adj_formal (Lf k r E) a b i u)
  simp only [LinearMap.smul_apply, LinearMap.add_apply, Pi.smul_apply, Pi.add_apply, LinearMap.sum_apply,
    Finset.sum_apply, hR', Finset.sum_const_zero] at h
  have h3 := (smul_eq_zero.mp h).resolve_left two_ne_zero
  exact eq_neg_of_add_eq_zero_left h3

theorem sk_perm (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop) (hG : HGl Eop) {t : ℕ}
    (a : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (f : Mat k r → E) (hf : CkOn ((t : ℕ) : ℕ∞) (GV k r) f)
    (τ : Equiv.Perm (Fin t)) :
    ∀ (b : Fin t → Fin (2 * r + k + 1)), ∀ g ∈ GV k r,
      ev Eop (qminor (Lf k r E) a (b ∘ τ) u) f g = ((Equiv.Perm.sign τ : ℤ) : ℂ) • ev Eop (qminor (Lf k r E) a b u) f g := by
  cases t with
  | zero =>
    intro b g hg
    have hτ : τ = 1 := Subsingleton.elim _ _
    subst hτ
    simp
  | succ m =>
    have hmem : τ ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top τ
    induction hmem using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro b g hg
      rw [sk_adj Eop hC hL hA hS hG a b i u f hf g hg, Equiv.Perm.sign_swap (Fin.castSucc_lt_succ : i.castSucc < i.succ).ne]
      simp
    | one =>
      intro b g hg
      simp
    | mul x y _ _ hx hy =>
      intro b g hg
      have e : b ∘ ⇑(x * y) = (b ∘ ⇑x) ∘ ⇑y := rfl
      rw [e, hy (b ∘ ⇑x) g hg, hx b g hg, Equiv.Perm.sign_mul]
      simp only [Units.val_mul, Int.cast_mul, mul_smul]
      rw [smul_comm]

theorem sk_zero (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop) (hG : HGl Eop) {t : ℕ}
    (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (f : Mat k r → E) (hf : CkOn ((t : ℕ) : ℕ∞) (GV k r) f)
    (hb : ¬ Function.Injective b) : ∀ g ∈ GV k r, ev Eop (qminor (Lf k r E) a b u) f g = 0 := by
  intro g hg
  simp only [Function.Injective, not_forall] at hb
  obtain ⟨i, j, hij, hne⟩ := hb
  have hb' : b ∘ ⇑(Equiv.swap i j) = b := by
    funext x
    simp only [Function.comp_apply, Equiv.swap_apply_def]
    split_ifs <;> simp_all
  have h := sk_perm Eop hC hL hA hS hG a u f hf (Equiv.swap i j) b g hg
  rw [hb', Equiv.Perm.sign_swap hne] at h
  simp at h
  have h2 : (2 : ℂ) • ev Eop (qminor (Lf k r E) a b u) f g = 0 := by
    rw [two_smul]
    nth_rw 1 [h]
    simp
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

end Skew

section Ad

variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))

theorem rep_Ead (P Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (c d : Fin (2 * r + k + 1)) :
    Rep 1 (Ead (Lf k r E) P Q c d) := by
  unfold Ead
  refine Finset.sum_induction _ (Rep 1) (fun _ _ => rep_add) (rep_zero_lemma_2 1) (fun a _ => ?_)
  refine Finset.sum_induction _ (Rep 1) (fun _ _ => rep_add) (rep_zero_lemma_2 1) (fun b _ => ?_)
  exact rep_smul _ (rep_Lf_lemma a b)

theorem ev_Tm_Ead (P Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : ℂ) (c d : Fin (2 * r + k + 1))
    (φ : Mat k r → E) (x : Mat k r) :
    ev Eop (Tm (Ead (Lf k r E) P Q) v c d) φ x =
      (if c = d then v • φ x else 0) + ∑ a, ∑ b, (P a c * Q d b) • Eop a b φ x := by
  simp only [ev, Formalism.REAL.Tm, Ead]
  split_ifs <;> simp [Lf, Formalism.FourierDecayAlt.P.JFxE.ell, Phi, Fw, LinearMap.sum_apply, Finset.sum_apply]

theorem ad_main (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop) (hG : HGl Eop)
    (Op : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) (hLop : HL Op)
    {P Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hQP : Q * P = 1)
    (hE : ∀ c d (φ : Mat k r → E), CkOn 1 (GV k r) φ → ∀ g ∈ GV k r,
      Op c d φ g = ∑ a, ∑ b, (P a c * Q d b) • Eop a b φ g)
    {t : ℕ} (e : Fin t ≃ Fin (2 * r + k + 1)) (u : ℂ) (f : Mat k r → E) (hf : CkOn ((t : ℕ) : ℕ∞) (GV k r) f) :
    ∀ g ∈ GV k r, qminorOp Op e e u f g = qminorOp Eop e e u f g := by
  intro g hg
  have hΛ : ∀ c d, Rep 1 (Ead (Lf k r E) P Q c d) := fun c d => rep_Ead P Q c d
  have hT : ∀ v c d (φ : Mat k r → E), CkOn 1 (GV k r) φ → ∀ g ∈ GV k r,
      ev Eop (Tm (Ead (Lf k r E) P Q) v c d) φ g = Formalism.QuantumDeterminants.Top Op v c d φ g := by
    intro v c d φ hφ g hg
    simp only [ev_Tm_Ead, Formalism.QuantumDeterminants.Top, hE c d φ hφ g hg]
  have hA' := bridge_qminor Eop hC hL hA hS hΛ Op hLop hT (⇑e) (⇑e) u f hf g hg
  have hB' := bridge_qminor Eop hC hL hA hS (fun c d => rep_Lf_lemma c d) Eop hL
    (fun v c d φ _ g _ => ev_Tm_Lf Eop v c d φ g) (⇑e) (⇑e) u f hf g hg
  rw [← hA', ← hB', qminor_Ead (Lf k r E) hQP e u]
  have hlin : ev Eop (P.det • ∑ β : Fin t → Fin (2 * r + k + 1),
      (∏ j, Q (e j) (β j)) • qminor (Lf k r E) (⇑e) β u) f g =
      P.det • ∑ β : Fin t → Fin (2 * r + k + 1),
        (∏ j, Q (e j) (β j)) • ev Eop (qminor (Lf k r E) (⇑e) β u) f g := by
    simp only [ev, LinearMap.smul_apply, LinearMap.sum_apply, Finset.sum_apply, Pi.smul_apply]
  rw [hlin, ← Equiv.sum_comp (Equiv.arrowCongr (Equiv.refl (Fin t)) e)]
  simp only [Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.coe_refl, Function.comp_id, Function.comp_apply]
  have hac : ∀ γ : Fin t → Fin t, (Equiv.arrowCongr (Equiv.refl (Fin t)) e) γ = ⇑e ∘ γ := fun γ => rfl
  simp only [hac]
  have hsplit : ∀ F : (Fin t → Fin t) → E, (∀ γ, ¬ Function.Injective γ → F γ = 0) →
      ∑ γ, F γ = ∑ τ : Equiv.Perm (Fin t), F ⇑τ := by
    classical
    intro F hF
    rw [← Finset.sum_subset
      (Finset.subset_univ (Finset.univ.image fun τ : Equiv.Perm (Fin t) => (⇑τ : Fin t → Fin t))) ?_]
    · rw [Finset.sum_image]
      intro τ₁ _ τ₂ _ h
      exact Equiv.coe_fn_injective h
    · intro γ _ hγ
      apply hF
      intro hinj
      apply hγ
      exact Finset.mem_image.mpr
        ⟨Equiv.ofBijective γ (Finite.injective_iff_bijective.mp hinj), Finset.mem_univ _, rfl⟩
  have hz : ∀ γ : Fin t → Fin t, ¬ Function.Injective γ →
      (∏ j, Q (e j) (e (γ j))) • ev Eop (qminor (Lf k r E) (⇑e) (⇑e ∘ γ) u) f g = 0 := by
    intro γ hγ
    rw [sk_zero Eop hC hL hA hS hG (⇑e) (⇑e ∘ γ) u f hf (fun h => hγ (Function.Injective.of_comp h)) g hg,
      smul_zero]
  rw [hsplit _ hz]
  have hp : ∀ τ : Equiv.Perm (Fin t), ev Eop (qminor (Lf k r E) (⇑e) (⇑e ∘ ⇑τ) u) f g =
      ((Equiv.Perm.sign τ : ℤ) : ℂ) • ev Eop (qminor (Lf k r E) (⇑e) (⇑e) u) f g :=
    fun τ => sk_perm Eop hC hL hA hS hG (⇑e) u f hf τ (⇑e) g hg
  simp only [hp, smul_smul, ← Finset.sum_smul]
  have hdet : ∑ τ : Equiv.Perm (Fin t), (∏ j, Q (e j) (e (τ j))) * ((Equiv.Perm.sign τ : ℤ) : ℂ) = Q.det := by
    rw [← Matrix.det_submatrix_equiv_self e Q, ← Matrix.det_transpose, Matrix.det_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp [Matrix.submatrix_apply, Matrix.transpose_apply, Units.smul_def, zsmul_eq_mul, mul_comm]
  have h1 : P.det * Q.det = 1 := by
    rw [mul_comm, ← Matrix.det_mul, hQP, Matrix.det_one]
  rw [hdet, h1, one_smul]

end Ad

end Formalism.FourierDecayAlt.P.JFxE
end
end

section
open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Hinv (k r : ℕ) : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv (Hsq k r)

theorem lie_inv {X : Mat k r} (hX : inLie k r X) : (Hpk k r)⁻¹ * Xᴴ * Hpk k r = -X := by
  have hX0 : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have h1 : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX0
  rw [Hinv, Matrix.mul_assoc, h1, Matrix.mul_neg, ← Matrix.mul_assoc, Hsq, Matrix.one_mul]

theorem hermPart_eq_self_of_mem_lie {X : Mat k r} (hX : inLie k r X) : hpart1 (Hpk k r) X = X := by
  simp only [hpart1]
  rw [lie_inv hX, sub_neg_eq_add, ← two_smul ℂ X, smul_smul]
  norm_num

theorem hpart2_eq_zero_of_inLie {X : Mat k r} (hX : inLie k r X) : hpart2 (Hpk k r) X = 0 := by
  simp only [hpart2]
  rw [lie_inv hX]
  simp

theorem two_I_inv : (1 / (2 * Complex.I) : ℂ) = -(Complex.I / 2) := by
  rw [div_eq_iff (mul_ne_zero two_ne_zero Complex.I_ne_zero)]
  linear_combination Complex.I_sq

theorem hp_decomp (Z : Mat k r) : hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z = Z := by
  simp only [hpart1, hpart2]
  have e : Complex.I * -(Complex.I / 2) = (1 / 2 : ℂ) := by
    linear_combination (-1 / 2 : ℂ) * Complex.I_sq
  rw [two_I_inv, smul_smul, e, ← smul_add, sub_add_add_cancel, ← two_smul ℂ Z, smul_smul]
  norm_num

theorem hpart1_add' (Z W : Mat k r) : hpart1 (Hpk k r) (Z + W) = hpart1 (Hpk k r) Z + hpart1 (Hpk k r) W := by
  simp only [hpart1, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  rw [← smul_add]
  congr 1
  abel

theorem hpart2_add' (Z W : Mat k r) : hpart2 (Hpk k r) (Z + W) = hpart2 (Hpk k r) Z + hpart2 (Hpk k r) W := by
  simp only [hpart2, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  rw [← smul_add]
  congr 1
  abel

theorem hp1_real (x : ℝ) (Z : Mat k r) : hpart1 (Hpk k r) ((x : ℂ) • Z) = (x : ℂ) • hpart1 (Hpk k r) Z := by
  have hs : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x
  simp only [hpart1, Matrix.conjTranspose_smul, hs, Matrix.mul_smul, Matrix.smul_mul]
  rw [← smul_sub, smul_comm]

theorem hpart2_ofReal_smul (x : ℝ) (Z : Mat k r) : hpart2 (Hpk k r) ((x : ℂ) • Z) = (x : ℂ) • hpart2 (Hpk k r) Z := by
  have hs : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x
  simp only [hpart2, Matrix.conjTranspose_smul, hs, Matrix.mul_smul, Matrix.smul_mul]
  rw [← smul_add, smul_comm]

theorem hpart1_I_smul (Z : Mat k r) : hpart1 (Hpk k r) (Complex.I • Z) = -hpart2 (Hpk k r) Z := by
  have hs : star Complex.I = -Complex.I := Complex.conj_I
  simp only [hpart1, hpart2, Matrix.conjTranspose_smul, hs, Matrix.mul_smul, Matrix.smul_mul, two_I_inv]
  simp only [neg_smul, neg_neg, sub_neg_eq_add]
  rw [← smul_add, smul_smul, show (1 / 2 : ℂ) * Complex.I = Complex.I / 2 by ring]

theorem hpart2_I_smul (Z : Mat k r) : hpart2 (Hpk k r) (Complex.I • Z) = hpart1 (Hpk k r) Z := by
  have hs : star Complex.I = -Complex.I := Complex.conj_I
  simp only [hpart1, hpart2, Matrix.conjTranspose_smul, hs, Matrix.mul_smul, Matrix.smul_mul, two_I_inv]
  have e1 : -(Complex.I / 2) * Complex.I = 1 / 2 := by
    linear_combination (-1 / 2 : ℂ) * Complex.I_sq
  have e2 : -(Complex.I / 2) * -Complex.I = -(1 / 2) := by
    linear_combination (1 / 2 : ℂ) * Complex.I_sq
  rw [smul_add, smul_smul, smul_smul, smul_sub, e1, e2, neg_smul, sub_eq_add_neg]

theorem lie_bracket {X Y : Mat k r} (hX : inLie k r X) (hY : inLie k r Y) : inLie k r (X * Y - Y * X) := by
  have hX0 : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have hY0 : Yᴴ * Hpk k r + Hpk k r * Y = 0 := hY
  have hX' : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX0
  have hY' : Yᴴ * Hpk k r = -(Hpk k r * Y) := eq_neg_of_add_eq_zero_left hY0
  have hX'' : ∀ M : Mat k r, Xᴴ * (Hpk k r * M) = -(Hpk k r * (X * M)) := by
    intro M
    rw [← Matrix.mul_assoc, hX', Matrix.neg_mul, Matrix.mul_assoc]
  have hY'' : ∀ M : Mat k r, Yᴴ * (Hpk k r * M) = -(Hpk k r * (Y * M)) := by
    intro M
    rw [← Matrix.mul_assoc, hY', Matrix.neg_mul, Matrix.mul_assoc]
  show (X * Y - Y * X)ᴴ * Hpk k r + Hpk k r * (X * Y - Y * X) = 0
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_assoc, hX', hY', Matrix.mul_neg, hX'', hY'', neg_neg]
  abel

theorem hp_of_parts {X Y : Mat k r} (hX : inLie k r X) (hY : inLie k r Y) :
    hpart1 (Hpk k r) (X + Complex.I • Y) = X ∧ hpart2 (Hpk k r) (X + Complex.I • Y) = Y := by
  refine ⟨?_, ?_⟩
  · rw [hpart1_add', hpart1_I_smul, hermPart_eq_self_of_mem_lie hX, hpart2_eq_zero_of_inLie hY, neg_zero, add_zero]
  · rw [hpart2_add', hpart2_I_smul, hpart2_eq_zero_of_inLie hX, hermPart_eq_self_of_mem_lie hY, zero_add]

def Psi (D : Mat k r →L[ℝ] E) (g Z : Mat k r) : E :=
  D (g * hpart1 (Hpk k r) Z) + Complex.I • D (g * hpart2 (Hpk k r) Z)

theorem Psi_add (D : Mat k r →L[ℝ] E) (g Z W : Mat k r) : Psi D g (Z + W) = Psi D g Z + Psi D g W := by
  simp only [Psi, hpart1_add', hpart2_add', Matrix.mul_add, map_add, smul_add]
  abel

theorem D_real (D : Mat k r →L[ℝ] E) (g M : Mat k r) (x : ℝ) : D (g * ((x : ℂ) • M)) = (x : ℂ) • D (g * M) := by
  rw [Matrix.mul_smul]
  exact (map_smul D x (g * M)).trans (Complex.coe_smul x _).symm

theorem Psi_real (D : Mat k r →L[ℝ] E) (g Z : Mat k r) (x : ℝ) : Psi D g ((x : ℂ) • Z) = (x : ℂ) • Psi D g Z := by
  simp only [Psi, hp1_real, hpart2_ofReal_smul, D_real, smul_add]
  rw [smul_comm (x : ℂ) Complex.I]

theorem Psi_I (D : Mat k r →L[ℝ] E) (g Z : Mat k r) : Psi D g (Complex.I • Z) = Complex.I • Psi D g Z := by
  simp only [Psi, hpart1_I_smul, hpart2_I_smul, Matrix.mul_neg, map_neg, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]
  abel

theorem Psi_smul (D : Mat k r →L[ℝ] E) (g Z : Mat k r) (c : ℂ) : Psi D g (c • Z) = c • Psi D g Z := by
  have hc := Complex.re_add_im c
  calc Psi D g (c • Z) = Psi D g ((c.re : ℂ) • Z + (c.im : ℂ) • (Complex.I • Z)) := by
        rw [smul_smul, ← add_smul, hc]
    _ = (c.re : ℂ) • Psi D g Z + (c.im : ℂ) • (Complex.I • Psi D g Z) := by
        rw [Psi_add, Psi_real, Psi_real, Psi_I]
    _ = c • Psi D g Z := by
        rw [smul_smul, ← add_smul, hc]

theorem Psi_zero (D : Mat k r →L[ℝ] E) (g : Mat k r) : Psi D g 0 = 0 := by
  simpa using Psi_smul D g 0 0

theorem Psi_sub (D : Mat k r →L[ℝ] E) (g Z W : Mat k r) : Psi D g (Z - W) = Psi D g Z - Psi D g W := by
  rw [sub_eq_add_neg, Psi_add, ← neg_one_smul ℂ W, Psi_smul, neg_one_smul, ← sub_eq_add_neg]

end Formalism.FourierDecayAlt.P.JFxE
end
end

section
open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem dx_repF {X : Mat k r} (hX : inLie k r X) {φ F : Mat k r → E} {F' : Mat k r →L[ℝ] E} {U : Set (Mat k r)}
    {g : Mat k r} (hU : IsOpen U) (hgU : g ∈ U) (hg : g ∈ GV k r) (hF : HasFDerivAt F F' g)
    (hff : ∀ h ∈ U, h ∈ GV k r → φ h = F h) : Dx (false, X) φ g = F' (g * X) := by
  rw [← dx_false]
  have hc := Formalism.REAL.hasDerivAt_mul_exp_smul_zero g X
  have hF0 : HasFDerivAt F F' (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by simpa using hF
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) (F' (g * X)) 0 :=
    hF0.comp_hasDerivAt (0 : ℝ) hc
  have hU0 : U ∈ nhds (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by simpa using hU.mem_nhds hgU
  have hev : (fun t : ℝ => φ (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[nhds 0]
      fun t => F (g * NormedSpace.exp ((t : ℂ) • X)) := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds hU0] with t ht
    exact hff _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hg hX t)
  exact (hcomp.congr_of_eventuallyEq hev).deriv

theorem EH_psi {φ F : Mat k r → E} {F' : Mat k r →L[ℝ] E} {U : Set (Mat k r)}
    {g : Mat k r} (hU : IsOpen U) (hgU : g ∈ U) (hg : g ∈ GV k r) (hF : HasFDerivAt F F' g)
    (hff : ∀ h ∈ U, h ∈ GV k r → φ h = F h) (a b : Fin (2 * r + k + 1)) :
    Q.EH k r a b φ g = Psi F' g (Matrix.single a b 1) := by
  have h1 : RdV (Xa k r a b) φ g = F' (g * Xa k r a b) := dx_repF (Xa_lie a b) hU hgU hg hF hff
  have h2 : RdV (Xb k r a b) φ g = F' (g * Xb k r a b) := dx_repF (Xb_lie a b) hU hgU hg hF hff
  show RdV (Xa k r a b) φ g + Complex.I • RdV (Xb k r a b) φ g =
    F' (g * Xa k r a b) + Complex.I • F' (g * Xb k r a b)
  rw [h1, h2]

private theorem inLie_conj_of_mem_GV' {y X : Mat k r} (hy : y ∈ GV k r) (hX : inLie k r X) :
    inLie k r (y⁻¹ * X * y) := by
  have hu : IsUnit y.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hy
  have hy' : yᴴ * Hpk k r * y = Hpk k r := hy
  have h1 : Hpk k r * y⁻¹ = yᴴ * Hpk k r := by
    calc Hpk k r * y⁻¹ = yᴴ * Hpk k r * y * y⁻¹ := by rw [hy']
      _ = yᴴ * Hpk k r := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have h2 : (y⁻¹)ᴴ * Hpk k r = Hpk k r * y := by
    calc (y⁻¹)ᴴ * Hpk k r = (y⁻¹)ᴴ * (yᴴ * Hpk k r * y) := by rw [hy']
      _ = (y * y⁻¹)ᴴ * Hpk k r * y := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hpk k r * y := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one, Matrix.one_mul]
  unfold inLie at hX ⊢
  have e1 : (y⁻¹ * X * y)ᴴ * Hpk k r = yᴴ * (Xᴴ * Hpk k r) * y := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc, h2]
  have e2 : Hpk k r * (y⁻¹ * X * y) = yᴴ * (Hpk k r * X) * y := by
    simp only [← Matrix.mul_assoc]
    rw [h1]
  rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hX, Matrix.mul_zero, Matrix.zero_mul]

theorem EHc_psi {y : Mat k r} (hy : y ∈ GV k r) {φ F : Mat k r → E} {F' : Mat k r →L[ℝ] E} {U : Set (Mat k r)}
    {g : Mat k r} (hU : IsOpen U) (hgU : g ∈ U) (hg : g ∈ GV k r) (hF : HasFDerivAt F F' g)
    (hff : ∀ h ∈ U, h ∈ GV k r → φ h = F h) (c d : Fin (2 * r + k + 1)) :
    EHc k r y c d φ g = Psi F' g (y⁻¹ * Matrix.single c d 1 * y) := by
  rw [EHc_eq]
  beta_reduce
  rw [dx_repF (inLie_conj_of_mem_GV' hy (Xa_lie c d)) hU hgU hg hF hff,
    dx_repF (inLie_conj_of_mem_GV' hy (Xb_lie c d)) hU hgU hg hF hff]
  have hZ : y⁻¹ * Matrix.single c d 1 * y = y⁻¹ * Xa k r c d * y + Complex.I • (y⁻¹ * Xb k r c d * y) := by
    conv_lhs => rw [← hp_decomp (Matrix.single c d 1)]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    all_goals rfl
  obtain ⟨h1, h2⟩ := hp_of_parts (inLie_conj_of_mem_GV' hy (Xa_lie c d)) (inLie_conj_of_mem_GV' hy (Xb_lie c d))
  unfold Psi
  rw [hZ, h1, h2]

theorem conj_single (P Q : Mat k r) (c d : Fin (2 * r + k + 1)) :
    P * Matrix.single c d 1 * Q = ∑ a, ∑ b, (P a c * Q d b) • Matrix.single a b 1 := by
  ext i j
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, ite_and, mul_ite, ite_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq']

private theorem psi_add_hermitian_curvature (D : Mat k r →L[ℝ] E) (g A B : Mat k r) :
    Psi D g (A + B) = Psi D g A + Psi D g B := by
  have h1 : hpart1 (Hpk k r) (A + B) = hpart1 (Hpk k r) A + hpart1 (Hpk k r) B := by
    simp only [hpart1, Matrix.conjTranspose_add, mul_add, add_mul]
    rw [← smul_add]
    congr 1
    abel
  have h2 : hpart2 (Hpk k r) (A + B) = hpart2 (Hpk k r) A + hpart2 (Hpk k r) B := by
    simp only [hpart2, Matrix.conjTranspose_add, mul_add, add_mul]
    rw [← smul_add]
    congr 1
    abel
  simp only [Psi, h1, h2, mul_add, map_add, smul_add]
  abel

theorem Psi_sum {ι : Type*} (s : Finset ι) (D : Mat k r →L[ℝ] E) (g : Mat k r) (Z : ι → Mat k r) :
    Psi D g (∑ i ∈ s, Z i) = ∑ i ∈ s, Psi D g (Z i) := by
  exact map_sum (AddMonoidHom.mk' (Psi D g) (psi_add_hermitian_curvature D g)) Z s

theorem rep1 {φ : Mat k r → E} (hφ : CkOn 1 (GV k r) φ) {g : Mat k r} (hg : g ∈ GV k r) :
    ∃ (U : Set (Mat k r)) (F : Mat k r → E), IsOpen U ∧ g ∈ U ∧ HasFDerivAt F (fderiv ℝ F g) g ∧
      ∀ h ∈ U, h ∈ GV k r → φ h = F h := by
  obtain ⟨U, f', hU, hgU, hf', hff⟩ := hφ g hg
  have hd : DifferentiableAt ℝ f' g :=
    (hf'.differentiableOn (by first | exact le_rfl | simp)).differentiableAt (hU.mem_nhds hgU)
  exact ⟨U, f', hU, hgU, hd.hasFDerivAt, hff⟩

theorem EH_HC : HC (Q.EH (E := E) k r) := by
  intro a b m f hf
  have h := EHc_ck (Formalism.QuantumDeterminants.WeylGroupFacts.uh_one (k := k) (r := r)) a b m f hf
  rwa [EHc_one] at h

theorem EH_HL : HL (Q.EH (E := E) k r) := by
  intro a b f f₂ h
  exact EH_congr a b f f₂ h

theorem EH_HA : HA (Q.EH (E := E) k r) := by
  intro a b f f₂ hf hf₂ g hg
  obtain ⟨U, F, hU, hgU, hF, hff⟩ := rep1 hf hg
  obtain ⟨U₂, F₂, hU₂, hgU₂, hF₂, hff₂⟩ := rep1 hf₂ hg
  rw [EH_psi (φ := fun x => f x + f₂ x) (hU.inter hU₂) ⟨hgU, hgU₂⟩ hg (hF.add hF₂)
      (fun h hh hG => by simp only [hff h hh.1 hG, hff₂ h hh.2 hG, Pi.add_apply]) a b,
    EH_psi hU hgU hg hF hff a b, EH_psi hU₂ hgU₂ hg hF₂ hff₂ a b]
  simp only [Psi]
  show fderiv ℝ F g (g * hpart1 (Hpk k r) (Matrix.single a b 1)) +
      fderiv ℝ F₂ g (g * hpart1 (Hpk k r) (Matrix.single a b 1)) +
      Complex.I • (fderiv ℝ F g (g * hpart2 (Hpk k r) (Matrix.single a b 1)) +
        fderiv ℝ F₂ g (g * hpart2 (Hpk k r) (Matrix.single a b 1))) = _
  rw [smul_add]
  abel

theorem EH_HS : HS (Q.EH (E := E) k r) := by
  intro a b c f hf g hg
  obtain ⟨U, F, hU, hgU, hF, hff⟩ := rep1 hf hg
  rw [EH_psi (φ := fun x => c • f x) hU hgU hg (hF.const_smul c)
      (fun h hh hG => by simp only [hff h hh hG, Pi.smul_apply]) a b,
    EH_psi hU hgU hg hF hff a b]
  simp only [Psi]
  show c • fderiv ℝ F g (g * hpart1 (Hpk k r) (Matrix.single a b 1)) +
      Complex.I • c • fderiv ℝ F g (g * hpart2 (Hpk k r) (Matrix.single a b 1)) = _
  rw [smul_add, smul_comm Complex.I c]

theorem EHc_HL {y : Mat k r} (hy : y ∈ GV k r) : HL (EHc (E := E) k r y) := by
  intro a b f f₂ h g hg
  rw [EHc_eq, EHc_eq]
  beta_reduce
  rw [Dx_congr (x := (false, y⁻¹ * Xa k r a b * y)) (inLie_conj_of_mem_GV' hy (Xa_lie a b)) h g hg,
    Dx_congr (x := (false, y⁻¹ * Xb k r a b * y)) (inLie_conj_of_mem_GV' hy (Xb_lie a b)) h g hg]

theorem EHc_change {y : Mat k r} (hy : y ∈ GV k r) (c d : Fin (2 * r + k + 1)) (φ : Mat k r → E)
    (hφ : CkOn 1 (GV k r) φ) : ∀ g ∈ GV k r,
      EHc k r y c d φ g = ∑ a, ∑ b, (y⁻¹ a c * y d b) • Q.EH k r a b φ g := by
  intro g hg
  obtain ⟨U, F, hU, hgU, hF, hff⟩ := rep1 hφ hg
  rw [EHc_psi hy hU hgU hg hF hff c d, conj_single, Psi_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Psi_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Psi_smul, EH_psi hU hgU hg hF hff a b]

end Formalism.FourierDecayAlt.P.JFxE
end
end

section
open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem lie_sub {X Y : Mat k r} (hX : inLie k r X) (hY : inLie k r Y) : inLie k r (X - Y) := by
  unfold inLie at *
  rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, sub_add_sub_comm, hX, hY, sub_zero]

theorem lie_add {X Y : Mat k r} (hX : inLie k r X) (hY : inLie k r Y) : inLie k r (X + Y) := by
  unfold inLie at *
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]

theorem EHH {φ F : Mat k r → E} {U : Set (Mat k r)} {g : Mat k r} (hφ : CkOn 2 (GV k r) φ) (hU : IsOpen U)
    (hgU : g ∈ U) (hg : g ∈ GV k r) (hF : ContDiffOn ℝ 2 F U) (hff : ∀ h ∈ U, h ∈ GV k r → φ h = F h)
    (a b c d : Fin (2 * r + k + 1)) :
    Q.EH k r a b (Q.EH k r c d φ) g =
      (fderiv ℝ F g (g * Xa k r a b * Xa k r c d) +
          fderiv ℝ (fderiv ℝ F) g (g * Xa k r a b) (g * Xa k r c d)) +
        Complex.I • (fderiv ℝ F g (g * Xa k r a b * Xb k r c d) +
          fderiv ℝ (fderiv ℝ F) g (g * Xa k r a b) (g * Xb k r c d)) +
      Complex.I • ((fderiv ℝ F g (g * Xb k r a b * Xa k r c d) +
          fderiv ℝ (fderiv ℝ F) g (g * Xb k r a b) (g * Xa k r c d)) +
        Complex.I • (fderiv ℝ F g (g * Xb k r a b * Xb k r c d) +
          fderiv ℝ (fderiv ℝ F) g (g * Xb k r a b) (g * Xb k r c d))) := by
  have hc : ContDiffOn ℝ (((1 + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) F U := by simpa using hF
  have hφ2 : CkOn ((1 : ℕ∞) + 1) (GV k r) φ := by
    have e : ((1 : ℕ∞) + 1) = 2 := by norm_num
    rw [e]; exact hφ
  have hφ1 : ∀ X : Mat k r, inLie k r X → CkOn 1 (GV k r) (Dx (false, X) φ) :=
    fun X hX => CkOn_Dx (x := (false, X)) hX hφ2
  have hop : ∀ X Y : Mat k r, inLie k r X → inLie k r Y →
      Dx (false, X) (Dx (false, Y) φ) g =
        fderiv ℝ (fderiv ℝ F) g (g * X) (g * Y) + fderiv ℝ F g (g * X * Y) :=
    fun X Y hX hY => Formalism.FourierDecayAlt.P.B4.op_op_ext false false hU hc hff hX hY hgU hg
  have hEcd : Q.EH k r c d φ = fun h => Dx (false, Xa k r c d) φ h + Complex.I • Dx (false, Xb k r c d) φ h :=
    EH_eq c d φ
  rw [EH_eq a b, hEcd]
  simp only
  rw [Dx_add (x := (false, Xa k r a b)) (Xa_lie a b) (hφ1 _ (Xa_lie c d)) (CkOn_smul _ (hφ1 _ (Xb_lie c d))) g hg,
    Dx_add (x := (false, Xb k r a b)) (Xb_lie a b) (hφ1 _ (Xa_lie c d)) (CkOn_smul _ (hφ1 _ (Xb_lie c d))) g hg,
    Dx_smul, Dx_smul]
  simp only
  rw [hop _ _ (Xa_lie a b) (Xa_lie c d), hop _ _ (Xa_lie a b) (Xb_lie c d), hop _ _ (Xb_lie a b) (Xa_lie c d),
    hop _ _ (Xb_lie a b) (Xb_lie c d)]
  simp only [smul_add]
  abel

theorem single_comm (a b c d : Fin (2 * r + k + 1)) :
    Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      ((if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) : Mat k r) := by
  split_ifs with h1 h2 h2
  all_goals
    first
    | (try subst h1); (try subst h2)
      simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, *]
    | ext i j
      simp_all [Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, ite_mul, Finset.sum_ite_eq,
        Finset.sum_ite_eq']

theorem EH_HGl : HGl (Q.EH (E := E) k r) := by
  intro a b c d φ hφ g hg
  obtain ⟨U, F, hU, hgU, hF, hff⟩ := hφ g hg
  have hF2 : ContDiffOn ℝ 2 F U := by exact_mod_cast hF
  have hF' : HasFDerivAt F (fderiv ℝ F g) g :=
    ((hF2.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hgU)).hasFDerivAt
  have hsym : ∀ v w : Mat k r, fderiv ℝ (fderiv ℝ F) g v w = fderiv ℝ (fderiv ℝ F) g w v := by
    have hc : ContDiffOn ℝ (((1 + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) F U := by simpa using hF2
    have := (hc.contDiffAt (hU.mem_nhds hgU)).isSymmSndFDerivAt
      (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)
    intro v w; exact this v w
  set A1 := Xa k r a b with hA1
  set A2 := Xb k r a b with hA2
  set C1 := Xa k r c d with hC1
  set C2 := Xb k r c d with hC2
  set D1 := fderiv ℝ F g with hD1
  set D2 := fderiv ℝ (fderiv ℝ F) g with hD2
  have hR : (if b = c then Q.EH k r a d φ g else 0) - (if d = a then Q.EH k r c b φ g else 0) =
      Psi D1 g (Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1) := by
    rw [single_comm, Psi_sub]
    congr 1
    · split_ifs
      · exact EH_psi hU hgU hg hF' hff a d
      · exact (Psi_zero D1 g).symm
    · split_ifs
      · exact EH_psi hU hgU hg hF' hff c b
      · exact (Psi_zero D1 g).symm
  have e1 : A1 + Complex.I • A2 = Matrix.single a b 1 := hp_decomp _
  have e2 : C1 + Complex.I • C2 = Matrix.single c d 1 := hp_decomp _
  have hbr : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      ((A1 * C1 - C1 * A1) - (A2 * C2 - C2 * A2)) + Complex.I • ((A1 * C2 - C2 * A1) + (A2 * C1 - C1 * A2)) := by
    rw [← e1, ← e2]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (norm := module) hI • (A2 * C2 - C2 * A2)
  have hl1 : inLie k r ((A1 * C1 - C1 * A1) - (A2 * C2 - C2 * A2)) :=
    lie_sub (lie_bracket (Xa_lie a b) (Xa_lie c d)) (lie_bracket (Xb_lie a b) (Xb_lie c d))
  have hl2 : inLie k r ((A1 * C2 - C2 * A1) + (A2 * C1 - C1 * A2)) :=
    lie_add (lie_bracket (Xa_lie a b) (Xb_lie c d)) (lie_bracket (Xb_lie a b) (Xa_lie c d))
  have hP : Psi D1 g (((A1 * C1 - C1 * A1) - (A2 * C2 - C2 * A2)) + Complex.I • ((A1 * C2 - C2 * A1) + (A2 * C1 - C1 * A2))) =
      D1 (g * ((A1 * C1 - C1 * A1) - (A2 * C2 - C2 * A2))) + Complex.I • D1 (g * ((A1 * C2 - C2 * A1) + (A2 * C1 - C1 * A2))) := by
    unfold Psi
    rw [(hp_of_parts hl1 hl2).1, (hp_of_parts hl1 hl2).2]
  rw [hR, hbr, hP, EHH hφ hU hgU hg hF2 hff a b c d, EHH hφ hU hgU hg hF2 hff c d a b]
  rw [← hA1, ← hA2, ← hC1, ← hC2, ← hD1, ← hD2]
  rw [hsym (g * C1) (g * A1), hsym (g * C2) (g * A1), hsym (g * C1) (g * A2), hsym (g * C2) (g * A2)]
  simp only [Matrix.mul_sub, Matrix.mul_add, map_sub, map_add, ← Matrix.mul_assoc]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (norm := module) hI • (D1 (g * A2 * C2) - D1 (g * C2 * A2))

theorem capAdInv : CapAdInv := by
  intro k r E _ _ y u f hy hf h hh
  have hyu := gv_unit hy
  have hQP : y * y⁻¹ = 1 := Matrix.mul_nonsing_inv _ hyu
  have hm : Q.mdim k r 0 = 2 * r + k + 1 := by simp [Q.mdim]
  set e : Fin (Q.mdim k r 0) ≃ Fin (2 * r + k + 1) := finCongr hm with he
  have hpos : Q.posL k r 0 = ⇑e := by
    funext j; apply Fin.ext; simp [Q.posL, he]
  rw [hpos]
  exact ad_main (Q.EH k r) EH_HC EH_HL EH_HA EH_HS EH_HGl (EHc k r y) (EHc_HL hy) hQP
    (fun c d φ hφ g hg => EHc_change hy c d φ hφ g hg) e u f (by rw [hm]; exact hf) h hh


theorem cVRho : JF.CVRho := cvRho_of capAdInv

end Formalism.FourierDecayAlt.P.JFxE
end
end

section
theorem Formalism.FourierDecayAlt.P.capelli_rho_commute : Formalism.FourierDecayAlt.JF.CVRho := by
  exact Formalism.FourierDecayAlt.P.JFxE.cVRho
end
