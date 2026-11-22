module

public import Mathlib

@[expose] public section

noncomputable section

open scoped Matrix

namespace GlobalTheory.IndLine.Iwasawa

section Exp

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

open scoped Matrix in
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
theorem _root_.GlobalTheory.IndLine.Iwasawa.exp_mul_eq {A : Matrix m m ℂ} {D : Matrix n n ℂ}
    {B : Matrix m n ℂ} (h : A * B = B * D) :
    NormedSpace.exp A * B = B * NormedSpace.exp D := by
  letI : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  have hk : ∀ k : ℕ, A ^ k * B = B * D ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
  have hA := NormedSpace.expSeries_summable' (𝕂 := ℂ) A
  have hD := NormedSpace.expSeries_summable' (𝕂 := ℂ) D
  let L : Matrix m m ℂ →L[ℂ] Matrix m n ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun X => X * B, map_add' := fun X Y => Matrix.add_mul X Y B,
      map_smul' := fun c X => Matrix.smul_mul c X B }
  let L' : Matrix n n ℂ →L[ℂ] Matrix m n ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun X => B * X, map_add' := fun X Y => Matrix.mul_add B X Y,
      map_smul' := fun c X => Matrix.mul_smul B c X }
  have e1 := L.map_tsum hA
  have e2 := L'.map_tsum hD
  simp only [L, L', LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk] at e1 e2
  rw [NormedSpace.exp_eq_tsum ℂ, NormedSpace.exp_eq_tsum ℂ]
  show (∑' k : ℕ, ((k.factorial : ℂ)⁻¹ • A ^ k)) * B = B * ∑' k : ℕ, ((k.factorial : ℂ)⁻¹ • D ^ k)
  refine e1.trans (Eq.trans ?_ e2.symm)
  congr 1
  funext k
  rw [Matrix.smul_mul, Matrix.mul_smul, hk]

end Exp

section Ring

variable {R : Type} [Ring R]

namespace Grading

variable {p r q θ : R} (h : Grading p r q θ)
include h

end Grading

end Ring

section Adj

variable {m : Type} [Fintype m] [DecidableEq m]

variable {N A B A' B' : Matrix m m ℂ}

variable {p r q θ Z : Matrix m m ℂ}

end Adj

section Plane

variable {A A' : Type} [CommRing A] [CommRing A'] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

variable {c : A →+* A} {c' : A' →+* A'} {J : Matrix m m A} {x y : m → A} {ι : Matrix m n A} {ι' : Matrix n m A}

namespace Hyp

variable (h : Hyp c J x y ι ι')
include h

end Hyp

end Plane

end GlobalTheory.IndLine.Iwasawa

end
