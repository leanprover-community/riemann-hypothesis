import Formalism.SharpRestriction.LevelLetterCocycles.CylinderCountFamily

noncomputable section

namespace Formalism.MainNotions.N.CylinderCountFamily

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Formalism.MainNotions.FamilyNumericLemmas Filter Topology Polynomial

variable (D : D7) {Dall Dgood : ℕ}

def CountCylAt (A : AllRowsAt D Dall Dgood) (c₃ : ℝ) : Prop :=
  ∀ (k : Fin 2) (S : Set (Tup D k)),
    |(A.dimT (cyl D k S) : ℝ) -
        A.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll A.B.I A.B.σ A.B.w) A.B.μf A.B.fund (A.eT (cyl D k S))| ≤
      Real.exp (-c₃ * (A.B.I.n : ℝ) * (A.B.I.f : ℝ) * Real.log (A.B.I.n : ℝ)) *
        A.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll A.B.I A.B.σ A.B.w) A.B.μf A.B.fund (A.eT (cyl D k S))

def CylinderCountUniformAt (A : AllRowsAt D Dall Dgood) (n₀ : ℕ) (Alev C₃ c₃ cb CL : ℝ) : Prop :=
  CountCylAt D A c₃ ∧ lawL D A.eVec CL ∧ LabelCountSpace A ∧ TieCountAt A n₀ Alev C₃ cb ∧ TieAdmG D


def FamilyDeficitBoundOfUniformAdmissibility {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (J : ∀ x, Fm.Ix x → Type) (Dall Dgood : ∀ x i, J x i → ℕ)
    (A : ∀ x (i : Fm.Ix x) (ι : J x i), AllRowsAt (Fm.D x i) (Dall x i ι) (Dgood x i ι)) : Prop :=
  ∀ (n₀ : ℕ) (Alev C₃ c₃ cb CL x₂ : ℝ), 0 < c₃ →
    (∀ x ≥ x₂, ∀ (i : Fm.Ix x) (ι : J x i), CylinderCountUniformAt (Fm.D x i) (A x i ι) n₀ Alev C₃ c₃ cb CL) → ParO Fm →
      FamilyDeficitBracketBound Fm J Dall Dgood ∧ (ParX Fm → FamilyExpDeficitBound Fm J Dall Dgood)




end Formalism.MainNotions.N.CylinderCountFamily
