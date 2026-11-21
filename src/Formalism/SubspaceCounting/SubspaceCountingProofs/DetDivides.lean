import Formalism.SubspaceCounting.StatementW

noncomputable section
open scoped BigOperators
open Polynomial

namespace Formalism.G0.DetDividesP
open Formalism.G0

variable {L : Type} [Field L] {r : ℕ}

lemma lastIdx_iff (hr : 0 < r) (a : Fin r) : a.val + 1 = r ↔ a = ⟨r - 1, by omega⟩ := by
  constructor
  · intro h; ext; simp; omega
  · intro h; subst h; simp; omega

lemma prod_lastX (hr : 0 < r) {R : Type} [CommRing R] (u : R) :
    (∏ a : Fin r, if a.val + 1 = r then u else 1) = u := by
  have : (fun a : Fin r => if a.val + 1 = r then u else 1) =
      fun a => if (⟨r - 1, by omega⟩ : Fin r) = a then u else 1 := by
    funext a; simp only [lastIdx_iff hr, eq_comm]
  rw [this, Finset.prod_ite_eq]; simp

lemma det_msMat (hr : 0 < r) (g : GL (Fin r) L) : (msMat g).det = X := by
  unfold msMat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, prod_lastX hr]
  have h1 : (g.1.map C).det * (((g⁻¹ : GL (Fin r) L)).1.map C).det = 1 := by
    rw [← Matrix.det_mul, ← Matrix.map_mul]
    simp
  calc (g.1.map C).det * X * (((g⁻¹ : GL (Fin r) L)).1.map C).det
      = ((g.1.map C).det * (((g⁻¹ : GL (Fin r) L)).1.map C).det) * X := by ring
    _ = X := by rw [h1, one_mul]

def nMat (g : GL (Fin r) L) : Matrix (Fin r) (Fin r) L[X] :=
  (g.1.map C) * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then 1 else X) *
    ((g⁻¹ : GL (Fin r) L).1.map C)





end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators
open Polynomial

namespace Formalism.G0.DetDividesP
open Formalism.G0

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

open Classical in

def ptA {L : Type} [Field L] (A : Fin r → ι) (g : GL (Fin r) L) (x : ι × Fin r → L) : ι × Fin r → L[X] :=
  fun p => if p.1 ∈ Set.range A then ∑ b, msMat g p.2 b * C (x (p.1, b)) else C (x p)

def Red (A : Fin r → ι) (G : MvPolynomial (ι × Fin r) K) (n : ℕ) : Prop :=
  ∀ (L : Type) [Field L] [Algebra K L] (g : GL (Fin r) L) (x : ι × Fin r → L),
    MvPolynomial.aeval x (detLetters (K := K) A) ≠ 0 →
      (X : L[X]) ^ n ∣ MvPolynomial.aeval (ptA A g x) G




end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators
open Polynomial

namespace Formalism.G0.DetDividesP
open Formalism.G0

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}






end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators
open Polynomial

namespace Formalism.G0.DetDividesP
open Formalism.G0

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

lemma sum_split (vec : ι → Bool) (S : Finset ι) (A : Fin r → ι) (d : ι → ℕ)
    (hAS : ∀ l, A l ∈ S ∧ vec (A l) = true) :
    (∑ i ∈ S.filter (fun i => i ∉ Set.range A), d i) =
      (∑ i ∈ S.filter (fun i => vec i = true ∧ i ∉ Set.range A), d i) +
        ∑ i ∈ S.filter (fun i => vec i = false), d i := by
  rw [← Finset.sum_filter_add_sum_filter_not (S.filter (fun i => i ∉ Set.range A)) (fun i => vec i = true)]
  congr 1
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext i; simp [Finset.mem_filter]; tauto
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext i
    simp only [Finset.mem_filter, Bool.not_eq_true]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      rintro ⟨l, rfl⟩
      have := (hAS l).2; simp_all


end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators

namespace Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

lemma not_mem_vars_of_degreeOf {σ : Type} {p : MvPolynomial σ K} {x : σ} (h : degreeOf x p = 0) :
    x ∉ p.vars := by
  intro hx
  rw [mem_vars_iff_mem_support] at hx
  obtain ⟨d, hd, hxd⟩ := hx
  have h1 := Finset.le_sup (f := fun m : σ →₀ ℕ => m x) hd
  rw [← degreeOf_eq_sup, h] at h1
  rw [Finsupp.mem_support_iff] at hxd
  exact hxd (by simpa using h1)




end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators

namespace Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

def Tm (K : Type) [Field K] (A : Fin r → ι) : Matrix (Fin r) (Fin r) (MvPolynomial ((ι × Fin r) ⊕ ι) K) :=
  Matrix.of fun l b => X (Sum.inl (A l, b))

def Wv (K : Type) [Field K] (A : Fin r → ι) : Fin r → MvPolynomial ((ι × Fin r) ⊕ ι) K :=
  fun l => X (Sum.inr (A l))

open Classical in

def evPerm (A : Fin r → ι) (τ : Equiv.Perm (Fin r)) : MvPolynomial ((ι × Fin r) ⊕ ι) K →ₐ[K] K :=
  aeval (Sum.elim (fun q => if h : ∃ l, A l = q.1 then (if q.2 = τ (Classical.choose h) then 1 else 0) else 0)
    (fun _ => 0))





end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators

namespace Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

def rho (K : Type) [Field K] (A : Fin r → ι) (l : Fin r) :
    MvPolynomial ((ι × Fin r) ⊕ ι) K →ₐ[K] MvPolynomial ((ι × Fin r) ⊕ ι) K :=
  aeval (Sum.elim (fun q => X (Sum.inl q)) (fun i => if i = A l then 1 else 0))

lemma rho_Tm (A : Fin r → ι) (l : Fin r) : (rho K A l).mapMatrix (Tm K A) = Tm K A := by
  ext i j; simp [rho, Tm]

lemma rho_adj (A : Fin r → ι) (l i j : Fin r) : rho K A l ((Tm K A).adjugate i j) = (Tm K A).adjugate i j := by
  have := RingHom.map_adjugate (rho K A l).toRingHom (Tm K A)
  have h2 : (rho K A l).toRingHom.mapMatrix (Tm K A) = Tm K A := rho_Tm A l
  rw [h2] at this
  exact congrFun (congrFun this i) j


lemma rho_fix (A : Fin r → ι) (l : Fin r) {p : MvPolynomial ((ι × Fin r) ⊕ ι) K}
    (hp : ∀ i, degreeOf (Sum.inr i) p = 0) : rho K A l p = p := by
  have hsub : (p.vars : Set ((ι × Fin r) ⊕ ι)) ⊆ Set.range Sum.inl := by
    intro x hx
    cases x with
    | inl q => exact ⟨q, rfl⟩
    | inr i => exact absurd hx (not_mem_vars_of_degreeOf (hp i))
  obtain ⟨q, rfl⟩ := exists_rename_eq_of_vars_subset_range p Sum.inl Sum.inl_injective hsub
  rw [rho, aeval_rename]
  have : ((Sum.elim (fun q => (X (Sum.inl q) : MvPolynomial ((ι × Fin r) ⊕ ι) K))
      (fun i => if i = A l then 1 else 0)) ∘ Sum.inl) = fun q => X (Sum.inl q) := by
    funext q; simp
  rw [this]
  clear hp hsub this
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp' hq' => rw [map_add, map_add, hp', hq']
  | mul_X p n hp' => rw [map_mul, map_mul, hp', aeval_X, rename_X]


end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators

namespace Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}


def lst (hr : 0 < r) : Fin r := ⟨r - 1, by omega⟩

section matrices
variable {L : Type} [Field L]



lemma E_sq (i : Fin r) (φ : Fin r → L) (hφ : φ i = 1) :
    Matrix.vecMulVec (Pi.single i (1 : L)) (φ - Pi.single i 1) *
      Matrix.vecMulVec (Pi.single i (1 : L)) (φ - Pi.single i 1) = 0 := by
  rw [Matrix.vecMulVec_mul_vecMulVec, dotProduct_single]; simp [hφ]

def gU (i : Fin r) (φ : Fin r → L) (hφ : φ i = 1) : GL (Fin r) L where
  val := 1 - Matrix.vecMulVec (Pi.single i (1 : L)) (φ - Pi.single i 1)
  inv := 1 + Matrix.vecMulVec (Pi.single i (1 : L)) (φ - Pi.single i 1)
  val_inv := by
    rw [mul_add, mul_one, sub_mul, one_mul, E_sq i φ hφ]; abel
  inv_val := by
    rw [add_mul, one_mul, mul_sub, mul_one, E_sq i φ hφ]; abel


end matrices

end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators

namespace Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}



end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators

namespace Formalism.G0.DetDividesP
open Formalism.G0

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}


end Formalism.G0.DetDividesP

namespace Formalism.G0


end Formalism.G0

end
