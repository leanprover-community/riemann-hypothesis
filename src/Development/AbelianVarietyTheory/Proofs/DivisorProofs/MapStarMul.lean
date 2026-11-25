module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

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

def up (p r q Z : R) : R := p * Z * r + p * Z * q + r * Z * q

structure Grading (p r q θ : R) : Prop where
  pp : p * p = p
  qq : q * q = q
  pq : p * q = 0
  qp : q * p = 0
  sum : r = 1 - p - q
  θθ : θ * θ = 1
  θp : θ * p = q * θ

end Ring

section Adj

variable {m : Type} [Fintype m] [DecidableEq m]

def Adj (N A B : Matrix m m ℂ) : Prop := Aᵀ * N = N * B.map star

end Adj

section Plane

variable {A A' : Type} [CommRing A] [CommRing A'] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

def prX (c : A →+* A) (J : Matrix m m A) (x y : m → A) : Matrix m m A := Matrix.vecMulVec x (J *ᵥ (c ∘ y))

def prY (c : A →+* A) (J : Matrix m m A) (x y : m → A) : Matrix m m A := -Matrix.vecMulVec y (J *ᵥ (c ∘ x))

structure Hyp (c : A →+* A) (J : Matrix m m A) (x y : m → A) (ι : Matrix m n A) (ι' : Matrix n m A) : Prop where
  cc : ∀ a, c (c a) = a
  skew : J.map c = -Jᵀ
  xx : x ⬝ᵥ J *ᵥ (c ∘ x) = 0
  yy : y ⬝ᵥ J *ᵥ (c ∘ y) = 0
  xy : x ⬝ᵥ J *ᵥ (c ∘ y) = 1
  yx : y ⬝ᵥ J *ᵥ (c ∘ x) = -1
  ιx : (J *ᵥ (c ∘ x)) ᵥ* ι = 0
  ιy : (J *ᵥ (c ∘ y)) ᵥ* ι = 0
  left : ι' * ι = 1
  right : ι * ι' = 1 - prX c J x y - prY c J x y

variable {c : A →+* A} {c' : A' →+* A'} {J : Matrix m m A} {x y : m → A} {ι : Matrix m n A} {ι' : Matrix n m A}

end Plane

end GlobalTheory.IndLine.Iwasawa

end
