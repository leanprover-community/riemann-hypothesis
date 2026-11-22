module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
public import Formalism.LocalToGlobal.ProjectiveLattices.IsThRule
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Formalism.LocalToGlobal.ProjectiveLattices.RowDeg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj MvPolynomial
open scoped Pointwise

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def stdForm (x y : Fin n → E) : E := ∑ j, x j * IsCMField.complexConj E (y j)

def stdMod (E : Type) [Field E] (n : ℕ) : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)

structure Lat (E : Type) [Field E] (n : ℕ) where
  L : Submodule (𝓞 E) (Fin n → E)
  fg : L.FG
  span_top : Submodule.span E (L : Set (Fin n → E)) = ⊤

omit [NumberField E] [IsCMField E] in
theorem mem_stdMod {x : Fin n → E} : x ∈ stdMod E n ↔ ∀ j, ∃ a : 𝓞 E, (a : E) = x j := by
  simp only [stdMod, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]

omit [NumberField E] [IsCMField E] in
theorem single_mem_stdMod (j : Fin n) : (Pi.single j 1 : Fin n → E) ∈ stdMod E n := by
  rw [mem_stdMod]
  intro i
  by_cases h : i = j
  · subst h
    exact ⟨1, by simp⟩
  · exact ⟨0, by simp [h]⟩

def Lat.std (E : Type) [Field E] (n : ℕ) : Lat E n where
  L := stdMod E n
  fg := Submodule.fg_pi fun _ => by
    rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  span_top := by
    classical
    rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    simpa using single_mem_stdMod j

def Lat.SelfDual (Λ : Lat E n) : Prop :=
  ∀ x : Fin n → E, x ∈ Λ.L ↔ ∀ y ∈ Λ.L, ∃ a : 𝓞 E, (a : E) = stdForm x y

def EqAtPrime (p : ℕ) (L₁ L₂ : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  (∀ x ∈ L₁, ∃ k : ℕ, ¬ p ∣ k ∧ k • x ∈ L₂) ∧ ∀ x ∈ L₂, ∃ k : ℕ, ¬ p ∣ k ∧ k • x ∈ L₁

def IsUnitary (γ : (Fin n → E) ≃ₗ[E] (Fin n → E)) : Prop := ∀ x y, stdForm (γ x) (γ y) = stdForm x y

def Lat.map (Λ : Lat E n) (γ : (Fin n → E) ≃ₗ[E] (Fin n → E)) : Lat E n where
  L := Λ.L.map (γ.toLinearMap.restrictScalars (𝓞 E))
  fg := Λ.fg.map _
  span_top := by
    have h : ((Λ.L.map (γ.toLinearMap.restrictScalars (𝓞 E)) : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) =
        γ.toLinearMap '' (Λ.L : Set (Fin n → E)) := rfl
    rw [h, ← Submodule.map_span, Λ.span_top, Submodule.map_top, LinearEquiv.range]

def Lat.InGenus (Λ : Lat E n) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E),
    IsUnitary γ ∧ EqAtPrime p Λ.L ((Lat.std E n).map γ).L

section Poly

variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)

end Poly

end GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
