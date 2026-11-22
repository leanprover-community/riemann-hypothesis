module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AI.T

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

universe u

instance : Fintype WBlk := ⟨{.base, .det, .line0, .line1}, by intro k; cases k <;> simp⟩

instance : Fintype YBlk := ⟨{.base, .det, .line}, by intro k; cases k <;> simp⟩

instance wwIdx.fintype {ι ν κ : Type u} [Fintype ι] [Fintype ν] [Fintype κ] :
    (k : WBlk) → Fintype (wwIdx ι ν κ k)
  | .base => inferInstanceAs (Fintype ι)
  | .det => inferInstanceAs (Fintype ν)
  | .line0 => inferInstanceAs (Fintype κ)
  | .line1 => inferInstanceAs (Fintype κ)

instance yyIdx.fintype {ι ν κ : Type u} [Fintype ι] [Fintype ν] [Fintype κ] :
    (k : YBlk) → Fintype (yyIdx ι ν κ k)
  | .base => inferInstanceAs (Fintype ι)
  | .det => inferInstanceAs (Fintype ν)
  | .line => inferInstanceAs (Fintype κ)

def multiConeMap {K : Type*} {ι : K → Type*} {Φ : Type*} [Field Φ] (c : (Σ k, ι k) → Φ) :
    MvPolynomial (Σ k, ι k) ℤ →+* MvPolynomial K Φ :=
  eval₂Hom (Int.castRingHom _) fun p => C (c p) * X p.1

section Models

variable {Ω : Type*} [Field Ω] {ι ν κ : Type u} [Fintype ι] [Fintype ν] [Fintype κ]
  {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ] [Algebra Ω Φ]

def toZCycle {α : Type*} (z : α →₀ ℕ) : α →₀ ℤ :=
  Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) z

end Models

section Degrees

end Degrees

section Diagonal

variable {ι ν κ : Type u} [Fintype ι] [Fintype ν] [Fintype κ]

end Diagonal

end ReciprocityTheory.ChartRestriction.G.AI.T
