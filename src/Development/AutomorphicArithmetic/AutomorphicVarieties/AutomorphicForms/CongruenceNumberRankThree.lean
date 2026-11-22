module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.GalOfCusp
open scoped Matrix

namespace UpperTheory.V.Af

section admitted

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def AttR [IsTotallyReal F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) (π : TR.CuspSub F n) : Prop :=
  AttachedSys ι r π.HasSat

def IsAutR [IsTotallyReal F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ π : TR.CuspSub F n, π.IsRegAlg ∧ AttR ι r π

def DualTw {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin n) k) (θ : Γ →* kˣ) : Prop :=
  ∃ P : GL (Fin n) k, ∀ s, (r s : Matrix (Fin n) (Fin n) k)ᵀ * (P : Matrix (Fin n) (Fin n) k) * (r s : Matrix (Fin n) (Fin n) k) =
    (θ s : k) • (P : Matrix (Fin n) (Fin n) k)

omit [NumberField F] in
variable (l) in
def IsCycWt (wt : ℤ) (θ : G F Ω →* (Qbar l)ˣ) : Prop :=
  ∃ (M : ℕ) (χ : G F Ω →* (Qbar l)ˣ), 1 ≤ M ∧ KillsMu M χ ∧ θ = cycBar F Ω l ^ wt * χ

end admitted

def NewformAutR : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (f : Newform k) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (j : ℤ), f.Att ι (tw W (cycBar ℚ Ω l ^ j)) → IsAutR ι W

section U3

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
  {l : ℕ} [Fact l.Prime]

end U3

def eis3 (q e : ℕ) (z : ℂ) : ℂ := ((q : ℂ) ^ e)⁻¹ * z + 1 + (q : ℂ) ^ e * z⁻¹

def eis4 (p e : ℕ) (z₁ z₂ z₃ : ℂ) : ℂ := (p : ℂ) ^ (e + 1) * z₁ + (p : ℂ) ^ e * z₂ + (p : ℂ) * z₃ + 1

section Ad

variable {F₀ F Ω : Type} [Field F₀] [Field F] [Field Ω] [Algebra F₀ F] [Algebra F₀ Ω] [Algebra F Ω] [IsScalarTower F₀ F Ω]
  {k : Type} [Field k] {n : ℕ}

def IsAdOf (r : G F Ω →* GL (Fin n) k) (μ : G F Ω →* kˣ) (ρ : Representation k (G F₀ Ω) (Matrix (Fin n) (Fin n) k)) : Prop :=
  ∃ (c : G F₀ Ω) (P : GL (Fin n) k), (∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)) ∧
    (∀ s s' : G F Ω, s'.restrictScalars F₀ = c * s.restrictScalars F₀ * c⁻¹ →
      (r s : Matrix (Fin n) (Fin n) k)ᵀ * (P : Matrix (Fin n) (Fin n) k) * (r s' : Matrix (Fin n) (Fin n) k) =
        (μ s : k) • (P : Matrix (Fin n) (Fin n) k)) ∧
    (∀ (s : G F Ω) (X : Matrix (Fin n) (Fin n) k), ρ (s.restrictScalars F₀) X =
      (r s : Matrix (Fin n) (Fin n) k) * X * ((r s)⁻¹ : GL (Fin n) k)) ∧
    ∀ X : Matrix (Fin n) (Fin n) k, ρ c X = -((P⁻¹ : GL (Fin n) k) * Xᵀ * (P : Matrix (Fin n) (Fin n) k))

end Ad

end UpperTheory.V.Af
