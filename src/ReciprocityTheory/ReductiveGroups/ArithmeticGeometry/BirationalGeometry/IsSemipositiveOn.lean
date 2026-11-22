module

public import Mathlib

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

section Coord

variable (o : Type*) {Ω : Type*} [CommRing o] [CommRing Ω] [Algebra o Ω] {ι : Type*}

def coneMap (x : ι → Ω) : MvPolynomial (ι) o →ₐ[o] Polynomial Ω :=
  aeval fun i => Polynomial.C (x i) * Polynomial.X

def coneRing (x : ι → Ω) : Subalgebra o (Polynomial Ω) :=
  (coneMap o x).range

def coordIdeal (x : ι → Ω) : Ideal (MvPolynomial (ι) o) :=
  RingHom.ker (coneMap o x)

def sec (x : ι → Ω) (d : ℕ) : Submodule o Ω :=
  (homogeneousSubmodule (ι) o d).map
    (aeval x : MvPolynomial (ι) o →ₐ[o] Ω).toLinearMap

def IsHomogIdeal (I : Ideal (MvPolynomial (ι) o)) : Prop :=
  ∀ f ∈ I, ∀ d, homogeneousComponent d f ∈ I

end Coord

section Points

variable {o : Type*} [CommRing o] {C : Type*} [NormedField C] {ι : Type*}

def conePts (σ : o →+* C) (I : Ideal (MvPolynomial (ι) o)) : Set (ι → C) :=
  {z | z ≠ 0 ∧ ∀ f ∈ I, eval z (map σ f) = 0}

variable (C ι) in
structure ConeMetric where

  ρ : (ι → C) → ℝ
  pos : ∀ z, z ≠ 0 → 0 < ρ z
  smul : ∀ (c : C) (z : ι → C), ρ (c • z) = ‖c‖ * ρ z

variable (C ι) in
def maxMetric [Fintype ι] : ConeMetric (C := C) (ι := ι) where
  ρ z := ‖z‖
  pos _ hz := norm_pos_iff.mpr hz
  smul c z := norm_smul c z

variable (ι) in
def fsMetric [Fintype ι] : ConeMetric (C := ℂ) (ι := ι) where
  ρ z := ‖WithLp.toLp 2 z‖
  pos _ hz := norm_pos_iff.mpr (by simpa using hz)
  smul c z := by rw [WithLp.toLp_smul, norm_smul]

def ptNorm (m : ConeMetric (C := C) (ι := ι)) (σ : o →+* C) (d : ℕ) (f : MvPolynomial (ι) o)
    (z : ι → C) : ℝ :=
  ‖eval z (map σ f)‖ / m.ρ z ^ d

def IsConjInvariant (m : ConeMetric (C := ℂ) (ι := ι)) : Prop :=
  ∀ z, m.ρ (fun i => (starRingEnd ℂ) (z i)) = m.ρ z

end Points

section Heights

end Heights

section Curvature

variable {ι : Type*} [Fintype ι]

def IsSmoothMetric (m : ConeMetric (C := ℂ) (ι := ι)) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m.ρ {z | z ≠ 0}

def leviForm (φ : (ι → ℂ) → ℝ) (z w : ι → ℂ) : ℝ :=
  (fderiv ℝ (fderiv ℝ φ) z w w + fderiv ℝ (fderiv ℝ φ) z (Complex.I • w) (Complex.I • w)) / 4

end Curvature

section Chow

open NumberField

variable {e n : ℕ}

end Chow

section MetrisedHeight

open NumberField

variable {ι : Type*}

end MetrisedHeight

section SphereMeasure

variable {e n : ℕ}

end SphereMeasure

section Joins

variable {Ω : Type*} [CommRing Ω] {ι κ : Type*}

end Joins

section Multi

variable {r : ℕ} {ι : Fin r → Type*} [∀ k, Fintype (ι k)]

end Multi

section Along

variable {o : Type*} [CommRing o] {ι : Type*} [Fintype ι]

def IsConeTangent (σ : o →+* ℂ) (I : Ideal (MvPolynomial ι o)) (z w : ι → ℂ) : Prop :=
  ∀ f ∈ I, ∑ i, eval z (pderiv i (map σ f)) * w i = 0

end Along

section MongeAmpere

variable {D : ℕ}

def cxHessian (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  fun i j =>
    let H := fderiv ℝ (fderiv ℝ φ) z
    let ei : Fin D → ℂ := Pi.single i 1
    let ej : Fin D → ℂ := Pi.single j 1
    ((H ei ej + H (Complex.I • ei) (Complex.I • ej) : ℝ) +
      Complex.I * ((H ei (Complex.I • ej) - H (Complex.I • ei) ej : ℝ))) / 4

def mixedDisc (A : Fin D → Matrix (Fin D) (Fin D) ℂ) : ℂ :=
  (1 / (D.factorial : ℂ)) *
    ∑ S : Finset (Fin D), (-1) ^ (D - S.card) * (∑ k ∈ S, A k).det

def maDensity (φ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) : ℝ :=
  (D.factorial : ℝ) * (2 / Real.pi) ^ D * (mixedDisc fun k => cxHessian (φ k) z).re

end MongeAmpere

section LatticeDegree

open NumberField ComplexConjugate

variable {ι : Type*} {r : ℕ}

end LatticeDegree

end ReciprocityTheory.ChartRestriction.G.Geo
