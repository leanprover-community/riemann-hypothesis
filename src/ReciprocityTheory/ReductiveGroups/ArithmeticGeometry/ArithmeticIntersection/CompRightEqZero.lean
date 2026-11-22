module

public import Mathlib

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AI

universe u

open Polynomial

def mix {V : Type*} {n : ℕ} (k : ℕ) (x y : V) : Fin n → V :=
  fun i => if (i : ℕ) < k then x else y

def IsSymmForm {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (I : MultilinearMap (RingHom.id ℝ) (fun _ : Fin n => V) ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → V), I (v ∘ σ) = I v

def word {VW : Type*} (D k i : ℕ) (x₁ x₂ a : VW) : Fin D → VW :=
  fun j => if (j : ℕ) = 0 then x₂ else if (j : ℕ) < 1 + 2 * i then x₁ else
    if (j : ℕ) < 2 * k - 1 then x₂ else a

noncomputable def volPoly (D : ℕ) (J : ℕ → ℝ) : ℝ[X] :=
  ∑ j ∈ Finset.range (D + 1), C ((D.choose j : ℝ) * J j) * (-X) ^ j

noncomputable def tsgPoly (D : ℕ) (κ : ℕ → ℝ) (P : ℝ[X]) : ℝ[X] :=
  ∑ n ∈ Finset.range (P.natDegree + 1),
    if Odd n then C (((D : ℝ) + 1) * κ ((n + 1) / 2) / (((n + 1) / 2 : ℕ) : ℝ) * P.coeff n) * X ^ (n + 1)
    else 0

attribute [instance] FibreSquare.acgV FibreSquare.modV FibreSquare.acgW FibreSquare.modW

end ReciprocityTheory.ChartRestriction.G.AI
