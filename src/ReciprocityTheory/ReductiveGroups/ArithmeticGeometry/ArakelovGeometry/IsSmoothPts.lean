module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
public import ReciprocityTheory.GeometryOfNumbers.AsymptoticSequences.ClosingHS

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Module

abbrev GlobalTheory (κ : Type) : Unit → Type := fun _ => κ

abbrev Ix (κ : Type) : Type := Σ k, GlobalTheory κ k

section Points

variable {J : Type} [Fintype J] {D : ℕ}

abbrev pts (P : Ideal (MvPolynomial J ℤ)) : Set (J → ℂ) :=
  conePts (Int.castRingHom ℂ) P

def IsDegZero (g : (J → ℂ) → ℝ) : Prop :=
  ∀ (c : ℂ) (z : J → ℂ), c ≠ 0 → g (c • z) = g z

def conjPt (z : J → ℂ) : J → ℂ := fun i => starRingEnd ℂ (z i)

end Points

section Lattice

variable {Ω : Type*} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

def IsSecBasis (x : J → Ω) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial J ℚ) : Prop :=
  (∀ k, ∃ f : MvPolynomial J ℤ, f.IsHomogeneous n ∧ b k = map (Int.castRingHom ℚ) f) ∧
    LinearIndependent ℤ (fun k => aeval x (b k)) ∧
    Submodule.span ℤ (Set.range fun k => aeval x (b k)) = sec ℤ x n

def matAct (A : Matrix J J ℚ) (x : J → Ω) : J → Ω :=
  fun i => ∑ j, (A i j : Ω) * x j

def matActC (A : Matrix J J ℚ) (z : J → ℂ) : J → ℂ :=
  fun i => ∑ j, (A i j : ℂ) * z j

end Lattice

section Top

variable {κ : Type} [Fintype κ]

def _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofCone
    (m : ConeMetric (C := ℂ) (ι := Ix κ)) : HermLine (GlobalTheory κ) where
  a := 1
  h := m.ρ
  pos z hz := m.pos z fun h0 => by
    obtain ⟨i, hi⟩ := hz ()
    exact hi (congrFun h0 _)
  smul c z _ := by
    have : (fun p : Ix κ => c p.1 * z p) = c () • z := by
      funext p
      rfl
    rw [this, m.smul]
    simp

abbrev AllFam : Type 1 :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
    Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ

def AllFam.IsFamily (I : AllFam) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], IsIntersectionFamily (I K ι)

variable {Ω : Type*} [Field Ω] [CharZero Ω]

def top (I : AllFam) (x : Ix κ → Ω) (m : ConeMetric (C := ℂ) (ι := Ix κ)) (D : ℕ) : ℝ :=
  I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) fun _ => HermLine.ofCone m

end Top

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
