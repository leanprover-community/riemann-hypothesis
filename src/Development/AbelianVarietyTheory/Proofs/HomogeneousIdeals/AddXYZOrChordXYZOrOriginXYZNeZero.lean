import Mathlib

section
open WeierstrassCurve WeierstrassCurve.Projective

namespace GlobalTheory.AddLaw

variable {R S : Type*} [CommRing R] [CommRing S]

def diagX (W : Projective R) (P Q : Fin 3 → R) : R :=
  -W.a₁ * W.a₂ * P 0 ^ 2 * Q 0 ^ 2 + W.a₁ ^ 2 * P 0 * P 1 * Q 0 ^ 2
    - W.a₂ * P 0 * P 1 * Q 0 ^ 2 + W.a₁ * P 1 ^ 2 * Q 0 ^ 2 - W.a₂ * W.a₃ * P 0 * P 2 * Q 0 ^ 2
    - W.a₁ * W.a₄ * P 0 * P 2 * Q 0 ^ 2 + W.a₁ * W.a₃ * P 1 * P 2 * Q 0 ^ 2
    - W.a₄ * P 1 * P 2 * Q 0 ^ 2 - W.a₃ * W.a₄ * P 2 ^ 2 * Q 0 ^ 2 - W.a₂ * P 0 ^ 2 * Q 0 * Q 1
    + 2 * W.a₁ * P 0 * P 1 * Q 0 * Q 1 + P 1 ^ 2 * Q 0 * Q 1 - 2 * W.a₄ * P 0 * P 2 * Q 0 * Q 1
    + 2 * W.a₃ * P 1 * P 2 * Q 0 * Q 1 - 3 * W.a₆ * P 2 ^ 2 * Q 0 * Q 1 + P 0 * P 1 * Q 1 ^ 2
    - W.a₁ ^ 2 * W.a₃ * P 0 ^ 2 * Q 0 * Q 2 - 2 * W.a₁ * W.a₄ * P 0 ^ 2 * Q 0 * Q 2
    - 2 * W.a₄ * P 0 * P 1 * Q 0 * Q 2 + W.a₃ * P 1 ^ 2 * Q 0 * Q 2
    - 2 * W.a₁ * W.a₃ ^ 2 * P 0 * P 2 * Q 0 * Q 2 - 2 * W.a₃ * W.a₄ * P 0 * P 2 * Q 0 * Q 2
    - 6 * W.a₁ * W.a₆ * P 0 * P 2 * Q 0 * Q 2 - 6 * W.a₆ * P 1 * P 2 * Q 0 * Q 2
    - W.a₃ ^ 3 * P 2 ^ 2 * Q 0 * Q 2 - 6 * W.a₃ * W.a₆ * P 2 ^ 2 * Q 0 * Q 2
    - W.a₁ * W.a₃ * P 0 ^ 2 * Q 1 * Q 2 - W.a₄ * P 0 ^ 2 * Q 1 * Q 2
    - 2 * W.a₃ ^ 2 * P 0 * P 2 * Q 1 * Q 2 - 6 * W.a₆ * P 0 * P 2 * Q 1 * Q 2
    - W.a₂ * W.a₃ ^ 2 * P 2 ^ 2 * Q 1 * Q 2 + W.a₁ * W.a₃ * W.a₄ * P 2 ^ 2 * Q 1 * Q 2
    + W.a₄ ^ 2 * P 2 ^ 2 * Q 1 * Q 2 - W.a₁ ^ 2 * W.a₆ * P 2 ^ 2 * Q 1 * Q 2
    - 4 * W.a₂ * W.a₆ * P 2 ^ 2 * Q 1 * Q 2 - W.a₁ * W.a₃ ^ 2 * P 0 ^ 2 * Q 2 ^ 2
    - 3 * W.a₁ * W.a₆ * P 0 ^ 2 * Q 2 ^ 2 - W.a₃ ^ 2 * P 0 * P 1 * Q 2 ^ 2
    - 3 * W.a₆ * P 0 * P 1 * Q 2 ^ 2 - W.a₁ * W.a₂ * W.a₃ ^ 2 * P 0 * P 2 * Q 2 ^ 2
    - W.a₃ ^ 3 * P 0 * P 2 * Q 2 ^ 2 + W.a₁ ^ 2 * W.a₃ * W.a₄ * P 0 * P 2 * Q 2 ^ 2
    + W.a₁ * W.a₄ ^ 2 * P 0 * P 2 * Q 2 ^ 2 - W.a₁ ^ 3 * W.a₆ * P 0 * P 2 * Q 2 ^ 2
    - 4 * W.a₁ * W.a₂ * W.a₆ * P 0 * P 2 * Q 2 ^ 2 - 3 * W.a₃ * W.a₆ * P 0 * P 2 * Q 2 ^ 2
    - W.a₂ * W.a₃ ^ 2 * P 1 * P 2 * Q 2 ^ 2 + W.a₁ * W.a₃ * W.a₄ * P 1 * P 2 * Q 2 ^ 2
    + W.a₄ ^ 2 * P 1 * P 2 * Q 2 ^ 2 - W.a₁ ^ 2 * W.a₆ * P 1 * P 2 * Q 2 ^ 2
    - 4 * W.a₂ * W.a₆ * P 1 * P 2 * Q 2 ^ 2 - W.a₂ * W.a₃ ^ 3 * P 2 ^ 2 * Q 2 ^ 2
    + W.a₁ * W.a₃ ^ 2 * W.a₄ * P 2 ^ 2 * Q 2 ^ 2 + W.a₃ * W.a₄ ^ 2 * P 2 ^ 2 * Q 2 ^ 2
    - W.a₁ ^ 2 * W.a₃ * W.a₆ * P 2 ^ 2 * Q 2 ^ 2 - 4 * W.a₂ * W.a₃ * W.a₆ * P 2 ^ 2 * Q 2 ^ 2

def negDiagY (W : Projective R) (P Q : Fin 3 → R) : R :=
  W.a₁ ^ 2 * W.a₂ * P 0 ^ 2 * Q 0 ^ 2 + W.a₂ ^ 2 * P 0 ^ 2 * Q 0 ^ 2
    - 3 * W.a₁ * W.a₃ * P 0 ^ 2 * Q 0 ^ 2 - 3 * W.a₄ * P 0 ^ 2 * Q 0 ^ 2
    - W.a₁ ^ 3 * P 0 * P 1 * Q 0 ^ 2 - W.a₁ ^ 2 * P 1 ^ 2 * Q 0 ^ 2
    - 3 * W.a₃ ^ 2 * P 0 * P 2 * Q 0 ^ 2 + W.a₁ ^ 2 * W.a₄ * P 0 * P 2 * Q 0 ^ 2
    + W.a₂ * W.a₄ * P 0 * P 2 * Q 0 ^ 2 - 9 * W.a₆ * P 0 * P 2 * Q 0 ^ 2
    - W.a₁ ^ 2 * W.a₃ * P 1 * P 2 * Q 0 ^ 2 - W.a₂ * W.a₃ ^ 2 * P 2 ^ 2 * Q 0 ^ 2
    + W.a₁ * W.a₃ * W.a₄ * P 2 ^ 2 * Q 0 ^ 2 + W.a₄ ^ 2 * P 2 ^ 2 * Q 0 ^ 2
    - 3 * W.a₂ * W.a₆ * P 2 ^ 2 * Q 0 ^ 2 + W.a₁ * W.a₂ * P 0 ^ 2 * Q 0 * Q 1
    - 3 * W.a₃ * P 0 ^ 2 * Q 0 * Q 1 - 2 * W.a₁ ^ 2 * P 0 * P 1 * Q 0 * Q 1
    - 2 * W.a₁ * P 1 ^ 2 * Q 0 * Q 1 - 2 * W.a₂ * W.a₃ * P 0 * P 2 * Q 0 * Q 1
    + 2 * W.a₁ * W.a₄ * P 0 * P 2 * Q 0 * Q 1 - 2 * W.a₁ * W.a₃ * P 1 * P 2 * Q 0 * Q 1
    - W.a₃ * W.a₄ * P 2 ^ 2 * Q 0 * Q 1 + 3 * W.a₁ * W.a₆ * P 2 ^ 2 * Q 0 * Q 1
    - W.a₁ * P 0 * P 1 * Q 1 ^ 2 - P 1 ^ 2 * Q 1 ^ 2 - W.a₃ * P 1 * P 2 * Q 1 ^ 2
    - 3 * W.a₃ ^ 2 * P 0 ^ 2 * Q 0 * Q 2 + W.a₁ ^ 2 * W.a₄ * P 0 ^ 2 * Q 0 * Q 2
    + W.a₂ * W.a₄ * P 0 ^ 2 * Q 0 * Q 2 - 9 * W.a₆ * P 0 ^ 2 * Q 0 * Q 2
    - 2 * W.a₁ ^ 2 * W.a₃ * P 0 * P 1 * Q 0 * Q 2 - 2 * W.a₁ * W.a₃ * P 1 ^ 2 * Q 0 * Q 2
    - 4 * W.a₂ * W.a₃ ^ 2 * P 0 * P 2 * Q 0 * Q 2
    + 4 * W.a₁ * W.a₃ * W.a₄ * P 0 * P 2 * Q 0 * Q 2 + 4 * W.a₄ ^ 2 * P 0 * P 2 * Q 0 * Q 2
    - 12 * W.a₂ * W.a₆ * P 0 * P 2 * Q 0 * Q 2 - 2 * W.a₁ * W.a₃ ^ 2 * P 1 * P 2 * Q 0 * Q 2
    - W.a₂ ^ 2 * W.a₃ ^ 2 * P 2 ^ 2 * Q 0 * Q 2
    + W.a₁ * W.a₂ * W.a₃ * W.a₄ * P 2 ^ 2 * Q 0 * Q 2 + W.a₂ * W.a₄ ^ 2 * P 2 ^ 2 * Q 0 * Q 2
    - W.a₁ ^ 2 * W.a₂ * W.a₆ * P 2 ^ 2 * Q 0 * Q 2 - 4 * W.a₂ ^ 2 * W.a₆ * P 2 ^ 2 * Q 0 * Q 2
    + 3 * W.a₁ * W.a₃ * W.a₆ * P 2 ^ 2 * Q 0 * Q 2 + 3 * W.a₄ * W.a₆ * P 2 ^ 2 * Q 0 * Q 2
    - W.a₂ * W.a₃ * P 0 ^ 2 * Q 1 * Q 2 + W.a₁ * W.a₄ * P 0 ^ 2 * Q 1 * Q 2
    - 2 * W.a₁ * W.a₃ * P 0 * P 1 * Q 1 * Q 2 - 2 * W.a₃ * P 1 ^ 2 * Q 1 * Q 2
    - 2 * W.a₃ * W.a₄ * P 0 * P 2 * Q 1 * Q 2 + 6 * W.a₁ * W.a₆ * P 0 * P 2 * Q 1 * Q 2
    - 2 * W.a₃ ^ 2 * P 1 * P 2 * Q 1 * Q 2 + W.a₁ * W.a₂ * W.a₃ ^ 2 * P 2 ^ 2 * Q 1 * Q 2
    - W.a₃ ^ 3 * P 2 ^ 2 * Q 1 * Q 2 - W.a₁ ^ 2 * W.a₃ * W.a₄ * P 2 ^ 2 * Q 1 * Q 2
    - W.a₁ * W.a₄ ^ 2 * P 2 ^ 2 * Q 1 * Q 2 + W.a₁ ^ 3 * W.a₆ * P 2 ^ 2 * Q 1 * Q 2
    + 4 * W.a₁ * W.a₂ * W.a₆ * P 2 ^ 2 * Q 1 * Q 2 - 3 * W.a₃ * W.a₆ * P 2 ^ 2 * Q 1 * Q 2
    - W.a₂ * W.a₃ ^ 2 * P 0 ^ 2 * Q 2 ^ 2 + W.a₁ * W.a₃ * W.a₄ * P 0 ^ 2 * Q 2 ^ 2
    + W.a₄ ^ 2 * P 0 ^ 2 * Q 2 ^ 2 - 3 * W.a₂ * W.a₆ * P 0 ^ 2 * Q 2 ^ 2
    - W.a₁ * W.a₃ ^ 2 * P 0 * P 1 * Q 2 ^ 2 - W.a₃ ^ 2 * P 1 ^ 2 * Q 2 ^ 2
    - W.a₂ ^ 2 * W.a₃ ^ 2 * P 0 * P 2 * Q 2 ^ 2
    + W.a₁ * W.a₂ * W.a₃ * W.a₄ * P 0 * P 2 * Q 2 ^ 2 + W.a₂ * W.a₄ ^ 2 * P 0 * P 2 * Q 2 ^ 2
    - W.a₁ ^ 2 * W.a₂ * W.a₆ * P 0 * P 2 * Q 2 ^ 2 - 4 * W.a₂ ^ 2 * W.a₆ * P 0 * P 2 * Q 2 ^ 2
    + 3 * W.a₁ * W.a₃ * W.a₆ * P 0 * P 2 * Q 2 ^ 2 + 3 * W.a₄ * W.a₆ * P 0 * P 2 * Q 2 ^ 2
    - W.a₃ ^ 3 * P 1 * P 2 * Q 2 ^ 2 - W.a₂ * W.a₃ ^ 2 * W.a₄ * P 2 ^ 2 * Q 2 ^ 2
    + W.a₁ * W.a₃ * W.a₄ ^ 2 * P 2 ^ 2 * Q 2 ^ 2 + W.a₄ ^ 3 * P 2 ^ 2 * Q 2 ^ 2
    + 3 * W.a₃ ^ 2 * W.a₆ * P 2 ^ 2 * Q 2 ^ 2 - W.a₁ ^ 2 * W.a₄ * W.a₆ * P 2 ^ 2 * Q 2 ^ 2
    - 4 * W.a₂ * W.a₄ * W.a₆ * P 2 ^ 2 * Q 2 ^ 2 + 9 * W.a₆ ^ 2 * P 2 ^ 2 * Q 2 ^ 2

def diagZ (W : Projective R) (P Q : Fin 3 → R) : R :=
  3 * W.a₁ * P 0 ^ 2 * Q 0 ^ 2 + 3 * P 0 * P 1 * Q 0 ^ 2 + W.a₁ * W.a₂ * P 0 * P 2 * Q 0 ^ 2
    + 3 * W.a₃ * P 0 * P 2 * Q 0 ^ 2 + W.a₂ * P 1 * P 2 * Q 0 ^ 2
    + W.a₂ * W.a₃ * P 2 ^ 2 * Q 0 ^ 2 + 3 * P 0 ^ 2 * Q 0 * Q 1
    + 2 * W.a₂ * P 0 * P 2 * Q 0 * Q 1 + W.a₄ * P 2 ^ 2 * Q 0 * Q 1 + P 1 * P 2 * Q 1 ^ 2
    + W.a₁ ^ 3 * P 0 ^ 2 * Q 0 * Q 2 + 2 * W.a₁ * W.a₂ * P 0 ^ 2 * Q 0 * Q 2
    + 2 * W.a₁ ^ 2 * P 0 * P 1 * Q 0 * Q 2 + 2 * W.a₂ * P 0 * P 1 * Q 0 * Q 2
    + W.a₁ * P 1 ^ 2 * Q 0 * Q 2 + 2 * W.a₁ ^ 2 * W.a₃ * P 0 * P 2 * Q 0 * Q 2
    + 2 * W.a₂ * W.a₃ * P 0 * P 2 * Q 0 * Q 2 + 2 * W.a₁ * W.a₄ * P 0 * P 2 * Q 0 * Q 2
    + 2 * W.a₁ * W.a₃ * P 1 * P 2 * Q 0 * Q 2 + 2 * W.a₄ * P 1 * P 2 * Q 0 * Q 2
    + W.a₁ * W.a₃ ^ 2 * P 2 ^ 2 * Q 0 * Q 2 + 2 * W.a₃ * W.a₄ * P 2 ^ 2 * Q 0 * Q 2
    + W.a₁ ^ 2 * P 0 ^ 2 * Q 1 * Q 2 + W.a₂ * P 0 ^ 2 * Q 1 * Q 2
    + 2 * W.a₁ * P 0 * P 1 * Q 1 * Q 2 + P 1 ^ 2 * Q 1 * Q 2
    + 2 * W.a₁ * W.a₃ * P 0 * P 2 * Q 1 * Q 2 + 2 * W.a₄ * P 0 * P 2 * Q 1 * Q 2
    + 2 * W.a₃ * P 1 * P 2 * Q 1 * Q 2 + W.a₃ ^ 2 * P 2 ^ 2 * Q 1 * Q 2
    + 3 * W.a₆ * P 2 ^ 2 * Q 1 * Q 2 + W.a₁ ^ 2 * W.a₃ * P 0 ^ 2 * Q 2 ^ 2
    + W.a₁ * W.a₄ * P 0 ^ 2 * Q 2 ^ 2 + 2 * W.a₁ * W.a₃ * P 0 * P 1 * Q 2 ^ 2
    + W.a₄ * P 0 * P 1 * Q 2 ^ 2 + W.a₃ * P 1 ^ 2 * Q 2 ^ 2
    + 2 * W.a₁ * W.a₃ ^ 2 * P 0 * P 2 * Q 2 ^ 2 + W.a₃ * W.a₄ * P 0 * P 2 * Q 2 ^ 2
    + 3 * W.a₁ * W.a₆ * P 0 * P 2 * Q 2 ^ 2 + 2 * W.a₃ ^ 2 * P 1 * P 2 * Q 2 ^ 2
    + 3 * W.a₆ * P 1 * P 2 * Q 2 ^ 2 + W.a₃ ^ 3 * P 2 ^ 2 * Q 2 ^ 2
    + 3 * W.a₃ * W.a₆ * P 2 ^ 2 * Q 2 ^ 2

def diagY (W : Projective R) (P Q : Fin 3 → R) : R :=
  W.negY ![diagX W P Q, negDiagY W P Q, diagZ W P Q]

def diagXYZ (W : Projective R) (P Q : Fin 3 → R) : Fin 3 → R :=
  ![diagX W P Q, diagY W P Q, diagZ W P Q]

variable {W : Projective R}

lemma diagX_self {P : Fin 3 → R} (hP : W.Equation P) : diagX W P P = W.dblX P := by
  linear_combination (norm := (simp only [diagX, dblX]; ring1))
    (W.a₁ ^ 3 * P 0 + 4 * W.a₁ * W.a₂ * P 0 + 9 * W.a₃ * P 0 + 2 * W.a₁ ^ 2 * P 1
      + 8 * W.a₂ * P 1 + W.a₁ ^ 2 * W.a₃ * P 2 + 4 * W.a₂ * W.a₃ * P 2) * (sub_eq_zero.mpr <| (equation_iff _).mp hP)

lemma negDiagY_self {P : Fin 3 → R} (hP : W.Equation P) : negDiagY W P P = W.negDblY P := by
  linear_combination (norm := (simp only [negDiagY, negDblY]; ring1))
    (2 * W.a₁ ^ 2 * W.a₂ * P 0 + 8 * W.a₂ ^ 2 * P 0 - 6 * W.a₁ * W.a₃ * P 0 + 3 * W.a₄ * P 0
      - W.a₁ ^ 3 * P 1 - 4 * W.a₁ * W.a₂ * P 1 - 6 * W.a₃ * P 1 - 3 * W.a₃ ^ 2 * P 2
      + W.a₁ ^ 2 * W.a₄ * P 2 + 4 * W.a₂ * W.a₄ * P 2 - 9 * W.a₆ * P 2) * (sub_eq_zero.mpr <| (equation_iff _).mp hP)

lemma diagZ_self {P : Fin 3 → R} (hP : W.Equation P) : diagZ W P P = W.dblZ P := by
  linear_combination (norm := (simp only [diagZ, dblZ, negY]; ring1))
    (-3 * W.a₁ * P 0 - 6 * P 1 - 3 * W.a₃ * P 2) * (sub_eq_zero.mpr <| (equation_iff _).mp hP)

lemma diagX_mul_addZ {P Q : Fin 3 → R} (hP : W.Equation P) (hQ : W.Equation Q) :
    diagX W P Q * W.addZ P Q = diagZ W P Q * W.addX P Q := by
  linear_combination (norm := (simp only [diagX, diagZ, addZ, addX]; ring1))
    (-3 * W.a₁ * P 2 * Q 0 ^ 2 * Q 1 ^ 2 - 3 * P 2 * Q 0 * Q 1 ^ 3
      + 3 * W.a₁ ^ 2 * P 1 * Q 0 ^ 3 * Q 2 - W.a₁ ^ 3 * W.a₂ * P 2 * Q 0 ^ 3 * Q 2
      - W.a₁ * W.a₂ ^ 2 * P 2 * Q 0 ^ 3 * Q 2 + 3 * W.a₁ ^ 2 * W.a₃ * P 2 * Q 0 ^ 3 * Q 2
      + 3 * W.a₁ * W.a₄ * P 2 * Q 0 ^ 3 * Q 2 - 3 * W.a₁ ^ 2 * P 0 * Q 0 ^ 2 * Q 1 * Q 2
      - 3 * W.a₁ * P 1 * Q 0 ^ 2 * Q 1 * Q 2 + W.a₁ ^ 2 * W.a₂ * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      + W.a₂ ^ 2 * P 2 * Q 0 ^ 2 * Q 1 * Q 2 - 6 * W.a₁ * W.a₃ * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      - 3 * W.a₄ * P 2 * Q 0 ^ 2 * Q 1 * Q 2 - 3 * W.a₁ * P 0 * Q 0 * Q 1 ^ 2 * Q 2
      - 3 * P 1 * Q 0 * Q 1 ^ 2 * Q 2 - W.a₁ ^ 3 * P 2 * Q 0 * Q 1 ^ 2 * Q 2
      - W.a₁ * W.a₂ * P 2 * Q 0 * Q 1 ^ 2 * Q 2 - 6 * W.a₃ * P 2 * Q 0 * Q 1 ^ 2 * Q 2
      - W.a₁ ^ 2 * P 2 * Q 1 ^ 3 * Q 2 - W.a₂ * P 2 * Q 1 ^ 3 * Q 2
      + W.a₁ ^ 3 * W.a₂ * P 0 * Q 0 ^ 2 * Q 2 ^ 2 + W.a₁ * W.a₂ ^ 2 * P 0 * Q 0 ^ 2 * Q 2 ^ 2
      - 3 * W.a₁ ^ 2 * W.a₃ * P 0 * Q 0 ^ 2 * Q 2 ^ 2 - 3 * W.a₁ * W.a₄ * P 0 * Q 0 ^ 2 * Q 2 ^ 2
      + 4 * W.a₁ ^ 2 * W.a₂ * P 1 * Q 0 ^ 2 * Q 2 ^ 2 + W.a₂ ^ 2 * P 1 * Q 0 ^ 2 * Q 2 ^ 2
      - 3 * W.a₁ * W.a₃ * P 1 * Q 0 ^ 2 * Q 2 ^ 2 - 3 * W.a₄ * P 1 * Q 0 ^ 2 * Q 2 ^ 2
      - W.a₁ ^ 3 * W.a₂ ^ 2 * P 2 * Q 0 ^ 2 * Q 2 ^ 2 - W.a₁ * W.a₂ ^ 3 * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      + 4 * W.a₁ ^ 2 * W.a₂ * W.a₃ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      + W.a₂ ^ 2 * W.a₃ * P 2 * Q 0 ^ 2 * Q 2 ^ 2 - 3 * W.a₁ * W.a₃ ^ 2 * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      + 3 * W.a₁ * W.a₂ * W.a₄ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      - 3 * W.a₃ * W.a₄ * P 2 * Q 0 ^ 2 * Q 2 ^ 2 - W.a₁ ^ 4 * P 0 * Q 0 * Q 1 * Q 2 ^ 2
      - W.a₁ ^ 2 * W.a₂ * P 0 * Q 0 * Q 1 * Q 2 ^ 2 - 3 * W.a₁ * W.a₃ * P 0 * Q 0 * Q 1 * Q 2 ^ 2
      - 4 * W.a₁ ^ 3 * P 1 * Q 0 * Q 1 * Q 2 ^ 2 - W.a₁ * W.a₂ * P 1 * Q 0 * Q 1 * Q 2 ^ 2
      - 3 * W.a₃ * P 1 * Q 0 * Q 1 * Q 2 ^ 2 + W.a₁ ^ 4 * W.a₂ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      + W.a₁ ^ 2 * W.a₂ ^ 2 * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 4 * W.a₁ ^ 3 * W.a₃ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - W.a₁ * W.a₂ * W.a₃ * P 2 * Q 0 * Q 1 * Q 2 ^ 2 - 6 * W.a₃ ^ 2 * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 2 * W.a₁ ^ 2 * W.a₄ * P 2 * Q 0 * Q 1 * Q 2 ^ 2 + W.a₂ * W.a₄ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 9 * W.a₆ * P 2 * Q 0 * Q 1 * Q 2 ^ 2 - W.a₁ ^ 3 * P 0 * Q 1 ^ 2 * Q 2 ^ 2
      - W.a₁ * W.a₂ * P 0 * Q 1 ^ 2 * Q 2 ^ 2 - 4 * W.a₁ ^ 2 * P 1 * Q 1 ^ 2 * Q 2 ^ 2
      - W.a₂ * P 1 * Q 1 ^ 2 * Q 2 ^ 2 + W.a₁ ^ 3 * W.a₂ * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      + W.a₁ * W.a₂ ^ 2 * P 2 * Q 1 ^ 2 * Q 2 ^ 2 - 5 * W.a₁ ^ 2 * W.a₃ * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      - 2 * W.a₂ * W.a₃ * P 2 * Q 1 ^ 2 * Q 2 ^ 2 - 3 * W.a₁ * W.a₄ * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      - 3 * W.a₁ * W.a₃ ^ 2 * P 0 * Q 0 * Q 2 ^ 3 + W.a₁ ^ 3 * W.a₄ * P 0 * Q 0 * Q 2 ^ 3
      + W.a₁ * W.a₂ * W.a₄ * P 0 * Q 0 * Q 2 ^ 3 - 9 * W.a₁ * W.a₆ * P 0 * Q 0 * Q 2 ^ 3
      - 3 * W.a₃ ^ 2 * P 1 * Q 0 * Q 2 ^ 3 + 4 * W.a₁ ^ 2 * W.a₄ * P 1 * Q 0 * Q 2 ^ 3
      + W.a₂ * W.a₄ * P 1 * Q 0 * Q 2 ^ 3 - 9 * W.a₆ * P 1 * Q 0 * Q 2 ^ 3
      - 3 * W.a₃ ^ 3 * P 2 * Q 0 * Q 2 ^ 3 - W.a₁ ^ 3 * W.a₂ * W.a₄ * P 2 * Q 0 * Q 2 ^ 3
      - W.a₁ * W.a₂ ^ 2 * W.a₄ * P 2 * Q 0 * Q 2 ^ 3
      + 4 * W.a₁ ^ 2 * W.a₃ * W.a₄ * P 2 * Q 0 * Q 2 ^ 3
      + W.a₂ * W.a₃ * W.a₄ * P 2 * Q 0 * Q 2 ^ 3 + 3 * W.a₁ * W.a₄ ^ 2 * P 2 * Q 0 * Q 2 ^ 3
      - 9 * W.a₃ * W.a₆ * P 2 * Q 0 * Q 2 ^ 3 - W.a₁ ^ 3 * W.a₃ * P 0 * Q 1 * Q 2 ^ 3
      - W.a₁ * W.a₂ * W.a₃ * P 0 * Q 1 * Q 2 ^ 3 - 4 * W.a₁ ^ 2 * W.a₃ * P 1 * Q 1 * Q 2 ^ 3
      - W.a₂ * W.a₃ * P 1 * Q 1 * Q 2 ^ 3 + W.a₁ ^ 3 * W.a₂ * W.a₃ * P 2 * Q 1 * Q 2 ^ 3
      + W.a₁ * W.a₂ ^ 2 * W.a₃ * P 2 * Q 1 * Q 2 ^ 3
      - 4 * W.a₁ ^ 2 * W.a₃ ^ 2 * P 2 * Q 1 * Q 2 ^ 3 - 2 * W.a₂ * W.a₃ ^ 2 * P 2 * Q 1 * Q 2 ^ 3
      - 2 * W.a₁ * W.a₃ * W.a₄ * P 2 * Q 1 * Q 2 ^ 3 + W.a₄ ^ 2 * P 2 * Q 1 * Q 2 ^ 3
      - 3 * W.a₂ * W.a₆ * P 2 * Q 1 * Q 2 ^ 3 - W.a₁ * W.a₂ * W.a₃ ^ 2 * P 0 * Q 2 ^ 4
      + W.a₁ ^ 2 * W.a₃ * W.a₄ * P 0 * Q 2 ^ 4 + W.a₁ * W.a₄ ^ 2 * P 0 * Q 2 ^ 4
      - 3 * W.a₁ * W.a₂ * W.a₆ * P 0 * Q 2 ^ 4 - W.a₂ * W.a₃ ^ 2 * P 1 * Q 2 ^ 4
      + W.a₁ * W.a₃ * W.a₄ * P 1 * Q 2 ^ 4 + W.a₄ ^ 2 * P 1 * Q 2 ^ 4
      + 3 * W.a₁ ^ 2 * W.a₆ * P 1 * Q 2 ^ 4 - 3 * W.a₂ * W.a₆ * P 1 * Q 2 ^ 4
      - W.a₂ * W.a₃ ^ 3 * P 2 * Q 2 ^ 4 + W.a₁ * W.a₃ ^ 2 * W.a₄ * P 2 * Q 2 ^ 4
      + W.a₃ * W.a₄ ^ 2 * P 2 * Q 2 ^ 4 - W.a₁ ^ 3 * W.a₂ * W.a₆ * P 2 * Q 2 ^ 4
      - W.a₁ * W.a₂ ^ 2 * W.a₆ * P 2 * Q 2 ^ 4 + 3 * W.a₁ ^ 2 * W.a₃ * W.a₆ * P 2 * Q 2 ^ 4
      - 3 * W.a₂ * W.a₃ * W.a₆ * P 2 * Q 2 ^ 4 + 3 * W.a₁ * W.a₄ * W.a₆ * P 2 * Q 2 ^ 4) * (sub_eq_zero.mpr <| (equation_iff _).mp hP)
    + (3 * W.a₁ * P 0 ^ 2 * P 1 * P 2 * Q 1 + 3 * P 0 * P 1 ^ 2 * P 2 * Q 1
      - W.a₁ ^ 2 * W.a₂ * P 0 ^ 2 * P 2 ^ 2 * Q 1 - W.a₂ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 1
      + 3 * W.a₁ * W.a₃ * P 0 ^ 2 * P 2 ^ 2 * Q 1 + 3 * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 1
      + W.a₁ ^ 3 * P 0 * P 1 * P 2 ^ 2 * Q 1 + W.a₁ * W.a₂ * P 0 * P 1 * P 2 ^ 2 * Q 1
      + 3 * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 1 + W.a₁ ^ 2 * P 1 ^ 2 * P 2 ^ 2 * Q 1
      + W.a₂ * P 1 ^ 2 * P 2 ^ 2 * Q 1 + 3 * W.a₃ ^ 2 * P 0 * P 2 ^ 3 * Q 1
      - W.a₁ ^ 2 * W.a₄ * P 0 * P 2 ^ 3 * Q 1 - W.a₂ * W.a₄ * P 0 * P 2 ^ 3 * Q 1
      + 9 * W.a₆ * P 0 * P 2 ^ 3 * Q 1 + W.a₁ ^ 2 * W.a₃ * P 1 * P 2 ^ 3 * Q 1
      + W.a₂ * W.a₃ * P 1 * P 2 ^ 3 * Q 1 + W.a₂ * W.a₃ ^ 2 * P 2 ^ 4 * Q 1
      - W.a₁ * W.a₃ * W.a₄ * P 2 ^ 4 * Q 1 - W.a₄ ^ 2 * P 2 ^ 4 * Q 1
      + 3 * W.a₂ * W.a₆ * P 2 ^ 4 * Q 1 + 6 * W.a₁ * P 0 ^ 2 * P 1 ^ 2 * Q 2
      + 3 * P 0 * P 1 ^ 3 * Q 2 + W.a₁ ^ 4 * P 0 ^ 2 * P 1 * P 2 * Q 2
      - 3 * W.a₁ ^ 2 * W.a₂ * P 0 ^ 2 * P 1 * P 2 * Q 2 - W.a₂ ^ 2 * P 0 ^ 2 * P 1 * P 2 * Q 2
      + 9 * W.a₁ * W.a₃ * P 0 ^ 2 * P 1 * P 2 * Q 2 + 3 * W.a₄ * P 0 ^ 2 * P 1 * P 2 * Q 2
      + 5 * W.a₁ ^ 3 * P 0 * P 1 ^ 2 * P 2 * Q 2 + 2 * W.a₁ * W.a₂ * P 0 * P 1 ^ 2 * P 2 * Q 2
      + 6 * W.a₃ * P 0 * P 1 ^ 2 * P 2 * Q 2 + 4 * W.a₁ ^ 2 * P 1 ^ 3 * P 2 * Q 2
      + W.a₂ * P 1 ^ 3 * P 2 * Q 2 + W.a₁ ^ 3 * W.a₂ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 2
      + W.a₁ * W.a₂ ^ 3 * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - 4 * W.a₁ ^ 2 * W.a₂ * W.a₃ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - W.a₂ ^ 2 * W.a₃ * P 0 ^ 2 * P 2 ^ 2 * Q 2 + 6 * W.a₁ * W.a₃ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - W.a₁ ^ 3 * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - 4 * W.a₁ * W.a₂ * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      + 3 * W.a₃ * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 2 + 9 * W.a₁ * W.a₆ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - W.a₁ ^ 4 * W.a₂ * P 0 * P 1 * P 2 ^ 2 * Q 2
      - W.a₁ ^ 2 * W.a₂ ^ 2 * P 0 * P 1 * P 2 ^ 2 * Q 2
      + 5 * W.a₁ ^ 3 * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 2
      + 2 * W.a₁ * W.a₂ * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 2
      + 6 * W.a₃ ^ 2 * P 0 * P 1 * P 2 ^ 2 * Q 2 - W.a₁ ^ 2 * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 2
      - W.a₂ * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 2 + 9 * W.a₆ * P 0 * P 1 * P 2 ^ 2 * Q 2
      - W.a₁ ^ 3 * W.a₂ * P 1 ^ 2 * P 2 ^ 2 * Q 2 - W.a₁ * W.a₂ ^ 2 * P 1 ^ 2 * P 2 ^ 2 * Q 2
      + 8 * W.a₁ ^ 2 * W.a₃ * P 1 ^ 2 * P 2 ^ 2 * Q 2 + 2 * W.a₂ * W.a₃ * P 1 ^ 2 * P 2 ^ 2 * Q 2
      + 3 * W.a₁ * W.a₄ * P 1 ^ 2 * P 2 ^ 2 * Q 2 + W.a₁ * W.a₂ * W.a₃ ^ 2 * P 0 * P 2 ^ 3 * Q 2
      + 3 * W.a₃ ^ 3 * P 0 * P 2 ^ 3 * Q 2 + W.a₁ ^ 3 * W.a₂ * W.a₄ * P 0 * P 2 ^ 3 * Q 2
      + W.a₁ * W.a₂ ^ 2 * W.a₄ * P 0 * P 2 ^ 3 * Q 2
      - 5 * W.a₁ ^ 2 * W.a₃ * W.a₄ * P 0 * P 2 ^ 3 * Q 2
      - W.a₂ * W.a₃ * W.a₄ * P 0 * P 2 ^ 3 * Q 2 - 4 * W.a₁ * W.a₄ ^ 2 * P 0 * P 2 ^ 3 * Q 2
      + 3 * W.a₁ * W.a₂ * W.a₆ * P 0 * P 2 ^ 3 * Q 2 + 9 * W.a₃ * W.a₆ * P 0 * P 2 ^ 3 * Q 2
      - W.a₁ ^ 3 * W.a₂ * W.a₃ * P 1 * P 2 ^ 3 * Q 2
      - W.a₁ * W.a₂ ^ 2 * W.a₃ * P 1 * P 2 ^ 3 * Q 2
      + 4 * W.a₁ ^ 2 * W.a₃ ^ 2 * P 1 * P 2 ^ 3 * Q 2 + 2 * W.a₂ * W.a₃ ^ 2 * P 1 * P 2 ^ 3 * Q 2
      + 2 * W.a₁ * W.a₃ * W.a₄ * P 1 * P 2 ^ 3 * Q 2 - W.a₄ ^ 2 * P 1 * P 2 ^ 3 * Q 2
      - 3 * W.a₁ ^ 2 * W.a₆ * P 1 * P 2 ^ 3 * Q 2 + 3 * W.a₂ * W.a₆ * P 1 * P 2 ^ 3 * Q 2
      + W.a₂ * W.a₃ ^ 3 * P 2 ^ 4 * Q 2 - W.a₁ * W.a₃ ^ 2 * W.a₄ * P 2 ^ 4 * Q 2
      - W.a₃ * W.a₄ ^ 2 * P 2 ^ 4 * Q 2 + W.a₁ ^ 3 * W.a₂ * W.a₆ * P 2 ^ 4 * Q 2
      + W.a₁ * W.a₂ ^ 2 * W.a₆ * P 2 ^ 4 * Q 2 - 3 * W.a₁ ^ 2 * W.a₃ * W.a₆ * P 2 ^ 4 * Q 2
      + 3 * W.a₂ * W.a₃ * W.a₆ * P 2 ^ 4 * Q 2 - 3 * W.a₁ * W.a₄ * W.a₆ * P 2 ^ 4 * Q 2) * (sub_eq_zero.mpr <| (equation_iff _).mp hQ)

lemma negDiagY_mul_addZ {P Q : Fin 3 → R} (hP : W.Equation P) (hQ : W.Equation Q) :
    negDiagY W P Q * W.addZ P Q = diagZ W P Q * W.negAddY P Q := by
  linear_combination (norm := (simp only [negDiagY, diagZ, addZ, negAddY]; ring1))
    (9 * W.a₁ * P 1 * Q 0 ^ 4 - 3 * W.a₁ ^ 2 * W.a₂ * P 2 * Q 0 ^ 4
      - 3 * W.a₂ ^ 2 * P 2 * Q 0 ^ 4 + 9 * W.a₁ * W.a₃ * P 2 * Q 0 ^ 4 + 9 * W.a₄ * P 2 * Q 0 ^ 4
      - 9 * W.a₁ * P 0 * Q 0 ^ 3 * Q 1 - 3 * W.a₁ * W.a₂ * P 2 * Q 0 ^ 3 * Q 1
      - 9 * P 0 * Q 0 ^ 2 * Q 1 ^ 2 + 3 * W.a₁ ^ 2 * P 2 * Q 0 ^ 2 * Q 1 ^ 2
      - 3 * W.a₂ * P 2 * Q 0 ^ 2 * Q 1 ^ 2 + 3 * W.a₁ * P 2 * Q 0 * Q 1 ^ 3
      + 3 * W.a₁ ^ 2 * W.a₂ * P 0 * Q 0 ^ 3 * Q 2 + 3 * W.a₂ ^ 2 * P 0 * Q 0 ^ 3 * Q 2
      - 9 * W.a₁ * W.a₃ * P 0 * Q 0 ^ 3 * Q 2 - 9 * W.a₄ * P 0 * Q 0 ^ 3 * Q 2
      + 12 * W.a₁ * W.a₂ * P 1 * Q 0 ^ 3 * Q 2 - 3 * W.a₁ ^ 2 * W.a₂ ^ 2 * P 2 * Q 0 ^ 3 * Q 2
      - 3 * W.a₂ ^ 3 * P 2 * Q 0 ^ 3 * Q 2 + 9 * W.a₁ * W.a₂ * W.a₃ * P 2 * Q 0 ^ 3 * Q 2
      + 9 * W.a₂ * W.a₄ * P 2 * Q 0 ^ 3 * Q 2 - 3 * W.a₁ ^ 3 * P 0 * Q 0 ^ 2 * Q 1 * Q 2
      - 6 * W.a₁ * W.a₂ * P 0 * Q 0 ^ 2 * Q 1 * Q 2 - 9 * W.a₃ * P 0 * Q 0 ^ 2 * Q 1 * Q 2
      - 9 * W.a₁ ^ 2 * P 1 * Q 0 ^ 2 * Q 1 * Q 2 + W.a₁ ^ 3 * W.a₂ * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      + W.a₁ * W.a₂ ^ 2 * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      - 6 * W.a₁ ^ 2 * W.a₃ * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      - 3 * W.a₂ * W.a₃ * P 2 * Q 0 ^ 2 * Q 1 * Q 2 - 9 * W.a₁ * W.a₄ * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      - 3 * W.a₁ ^ 2 * P 0 * Q 0 * Q 1 ^ 2 * Q 2 - 6 * W.a₂ * P 0 * Q 0 * Q 1 ^ 2 * Q 2
      - 9 * W.a₁ * P 1 * Q 0 * Q 1 ^ 2 * Q 2 + W.a₁ ^ 4 * P 2 * Q 0 * Q 1 ^ 2 * Q 2
      + 3 * W.a₁ ^ 2 * W.a₂ * P 2 * Q 0 * Q 1 ^ 2 * Q 2 + 2 * W.a₂ ^ 2 * P 2 * Q 0 * Q 1 ^ 2 * Q 2
      - 6 * W.a₁ * W.a₃ * P 2 * Q 0 * Q 1 ^ 2 * Q 2 - 12 * W.a₄ * P 2 * Q 0 * Q 1 ^ 2 * Q 2
      + W.a₁ ^ 3 * P 2 * Q 1 ^ 3 * Q 2 + W.a₁ * W.a₂ * P 2 * Q 1 ^ 3 * Q 2
      + W.a₁ ^ 2 * W.a₂ ^ 2 * P 0 * Q 0 ^ 2 * Q 2 ^ 2 + W.a₂ ^ 3 * P 0 * Q 0 ^ 2 * Q 2 ^ 2
      - 3 * W.a₁ * W.a₂ * W.a₃ * P 0 * Q 0 ^ 2 * Q 2 ^ 2 - 9 * W.a₃ ^ 2 * P 0 * Q 0 ^ 2 * Q 2 ^ 2
      + 3 * W.a₁ ^ 2 * W.a₄ * P 0 * Q 0 ^ 2 * Q 2 ^ 2 - 27 * W.a₆ * P 0 * Q 0 ^ 2 * Q 2 ^ 2
      + 3 * W.a₁ * W.a₂ ^ 2 * P 1 * Q 0 ^ 2 * Q 2 ^ 2 + 9 * W.a₁ * W.a₄ * P 1 * Q 0 ^ 2 * Q 2 ^ 2
      - W.a₁ ^ 2 * W.a₂ ^ 3 * P 2 * Q 0 ^ 2 * Q 2 ^ 2 - W.a₂ ^ 4 * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      + 3 * W.a₁ * W.a₂ ^ 2 * W.a₃ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      - 3 * W.a₂ * W.a₃ ^ 2 * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      - W.a₁ ^ 2 * W.a₂ * W.a₄ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      + 2 * W.a₂ ^ 2 * W.a₄ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      + 6 * W.a₁ * W.a₃ * W.a₄ * P 2 * Q 0 ^ 2 * Q 2 ^ 2 + 6 * W.a₄ ^ 2 * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      - 9 * W.a₂ * W.a₆ * P 2 * Q 0 ^ 2 * Q 2 ^ 2 - W.a₁ ^ 3 * W.a₂ * P 0 * Q 0 * Q 1 * Q 2 ^ 2
      - W.a₁ * W.a₂ ^ 2 * P 0 * Q 0 * Q 1 * Q 2 ^ 2
      - 3 * W.a₁ ^ 2 * W.a₃ * P 0 * Q 0 * Q 1 * Q 2 ^ 2
      - 6 * W.a₂ * W.a₃ * P 0 * Q 0 * Q 1 * Q 2 ^ 2
      - 3 * W.a₁ ^ 2 * W.a₂ * P 1 * Q 0 * Q 1 * Q 2 ^ 2
      - 9 * W.a₁ * W.a₃ * P 1 * Q 0 * Q 1 * Q 2 ^ 2
      + W.a₁ ^ 3 * W.a₂ ^ 2 * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      + W.a₁ * W.a₂ ^ 3 * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - W.a₁ ^ 2 * W.a₂ * W.a₃ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      + 2 * W.a₂ ^ 2 * W.a₃ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 6 * W.a₁ * W.a₃ ^ 2 * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 2 * W.a₁ ^ 3 * W.a₄ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 5 * W.a₁ * W.a₂ * W.a₄ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 12 * W.a₃ * W.a₄ * P 2 * Q 0 * Q 1 * Q 2 ^ 2 + 9 * W.a₁ * W.a₆ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - W.a₁ ^ 2 * W.a₂ * P 0 * Q 1 ^ 2 * Q 2 ^ 2 - W.a₂ ^ 2 * P 0 * Q 1 ^ 2 * Q 2 ^ 2
      - 3 * W.a₁ * W.a₂ * P 1 * Q 1 ^ 2 * Q 2 ^ 2 + W.a₁ ^ 2 * W.a₂ ^ 2 * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      + W.a₂ ^ 3 * P 2 * Q 1 ^ 2 * Q 2 ^ 2 + W.a₁ ^ 3 * W.a₃ * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      - 2 * W.a₁ * W.a₂ * W.a₃ * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      - W.a₁ ^ 2 * W.a₄ * P 2 * Q 1 ^ 2 * Q 2 ^ 2 - 4 * W.a₂ * W.a₄ * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      - 6 * W.a₂ * W.a₃ ^ 2 * P 0 * Q 0 * Q 2 ^ 3 + W.a₁ ^ 2 * W.a₂ * W.a₄ * P 0 * Q 0 * Q 2 ^ 3
      + W.a₂ ^ 2 * W.a₄ * P 0 * Q 0 * Q 2 ^ 3 + 3 * W.a₁ * W.a₃ * W.a₄ * P 0 * Q 0 * Q 2 ^ 3
      + 3 * W.a₄ ^ 2 * P 0 * Q 0 * Q 2 ^ 3 - 18 * W.a₂ * W.a₆ * P 0 * Q 0 * Q 2 ^ 3
      + 3 * W.a₁ * W.a₂ * W.a₄ * P 1 * Q 0 * Q 2 ^ 3 + 9 * W.a₁ * W.a₆ * P 1 * Q 0 * Q 2 ^ 3
      - W.a₂ ^ 2 * W.a₃ ^ 2 * P 2 * Q 0 * Q 2 ^ 3
      - W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₄ * P 2 * Q 0 * Q 2 ^ 3 - W.a₂ ^ 3 * W.a₄ * P 2 * Q 0 * Q 2 ^ 3
      + 4 * W.a₁ * W.a₂ * W.a₃ * W.a₄ * P 2 * Q 0 * Q 2 ^ 3
      - 3 * W.a₃ ^ 2 * W.a₄ * P 2 * Q 0 * Q 2 ^ 3 + W.a₁ ^ 2 * W.a₄ ^ 2 * P 2 * Q 0 * Q 2 ^ 3
      + 5 * W.a₂ * W.a₄ ^ 2 * P 2 * Q 0 * Q 2 ^ 3
      - 3 * W.a₁ ^ 2 * W.a₂ * W.a₆ * P 2 * Q 0 * Q 2 ^ 3
      - 6 * W.a₂ ^ 2 * W.a₆ * P 2 * Q 0 * Q 2 ^ 3 + 9 * W.a₁ * W.a₃ * W.a₆ * P 2 * Q 0 * Q 2 ^ 3
      - W.a₁ ^ 2 * W.a₂ * W.a₃ * P 0 * Q 1 * Q 2 ^ 3 - W.a₂ ^ 2 * W.a₃ * P 0 * Q 1 * Q 2 ^ 3
      - 3 * W.a₁ * W.a₂ * W.a₃ * P 1 * Q 1 * Q 2 ^ 3
      + W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₃ * P 2 * Q 1 * Q 2 ^ 3 + W.a₂ ^ 3 * W.a₃ * P 2 * Q 1 * Q 2 ^ 3
      - 2 * W.a₁ * W.a₂ * W.a₃ ^ 2 * P 2 * Q 1 * Q 2 ^ 3
      - 2 * W.a₁ ^ 2 * W.a₃ * W.a₄ * P 2 * Q 1 * Q 2 ^ 3
      - 4 * W.a₂ * W.a₃ * W.a₄ * P 2 * Q 1 * Q 2 ^ 3 - W.a₁ * W.a₄ ^ 2 * P 2 * Q 1 * Q 2 ^ 3
      + 3 * W.a₁ * W.a₂ * W.a₆ * P 2 * Q 1 * Q 2 ^ 3 - W.a₂ ^ 2 * W.a₃ ^ 2 * P 0 * Q 2 ^ 4
      + W.a₁ * W.a₂ * W.a₃ * W.a₄ * P 0 * Q 2 ^ 4 + W.a₂ * W.a₄ ^ 2 * P 0 * Q 2 ^ 4
      - 3 * W.a₂ ^ 2 * W.a₆ * P 0 * Q 2 ^ 4 + 3 * W.a₁ * W.a₂ * W.a₆ * P 1 * Q 2 ^ 4
      - W.a₂ * W.a₃ ^ 2 * W.a₄ * P 2 * Q 2 ^ 4 + W.a₁ * W.a₃ * W.a₄ ^ 2 * P 2 * Q 2 ^ 4
      + W.a₄ ^ 3 * P 2 * Q 2 ^ 4 - W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₆ * P 2 * Q 2 ^ 4
      - W.a₂ ^ 3 * W.a₆ * P 2 * Q 2 ^ 4 + 3 * W.a₁ * W.a₂ * W.a₃ * W.a₆ * P 2 * Q 2 ^ 4) * (sub_eq_zero.mpr <| (equation_iff _).mp hP)
    + (9 * P 0 ^ 2 * P 1 ^ 2 * Q 0 + 3 * W.a₁ ^ 3 * P 0 ^ 2 * P 1 * P 2 * Q 0
      - 3 * W.a₁ * W.a₂ * P 0 ^ 2 * P 1 * P 2 * Q 0 + 9 * W.a₃ * P 0 ^ 2 * P 1 * P 2 * Q 0
      + 12 * W.a₁ ^ 2 * P 0 * P 1 ^ 2 * P 2 * Q 0 + 6 * W.a₂ * P 0 * P 1 ^ 2 * P 2 * Q 0
      + 9 * W.a₁ * P 1 ^ 3 * P 2 * Q 0 + 2 * W.a₁ ^ 2 * W.a₂ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 0
      + 2 * W.a₂ ^ 3 * P 0 ^ 2 * P 2 ^ 2 * Q 0 - 6 * W.a₁ * W.a₂ * W.a₃ * P 0 ^ 2 * P 2 ^ 2 * Q 0
      + 9 * W.a₃ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 0 - 3 * W.a₁ ^ 2 * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 0
      - 9 * W.a₂ * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 0 + 27 * W.a₆ * P 0 ^ 2 * P 2 ^ 2 * Q 0
      - 2 * W.a₁ ^ 3 * W.a₂ * P 0 * P 1 * P 2 ^ 2 * Q 0
      - 2 * W.a₁ * W.a₂ ^ 2 * P 0 * P 1 * P 2 ^ 2 * Q 0
      + 12 * W.a₁ ^ 2 * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 0
      + 6 * W.a₂ * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 0
      - 2 * W.a₁ ^ 2 * W.a₂ * P 1 ^ 2 * P 2 ^ 2 * Q 0 - 2 * W.a₂ ^ 2 * P 1 ^ 2 * P 2 ^ 2 * Q 0
      + 18 * W.a₁ * W.a₃ * P 1 ^ 2 * P 2 ^ 2 * Q 0 + 9 * W.a₄ * P 1 ^ 2 * P 2 ^ 2 * Q 0
      + 6 * W.a₂ * W.a₃ ^ 2 * P 0 * P 2 ^ 3 * Q 0
      + 2 * W.a₁ ^ 2 * W.a₂ * W.a₄ * P 0 * P 2 ^ 3 * Q 0
      + 2 * W.a₂ ^ 2 * W.a₄ * P 0 * P 2 ^ 3 * Q 0 - 12 * W.a₁ * W.a₃ * W.a₄ * P 0 * P 2 ^ 3 * Q 0
      - 12 * W.a₄ ^ 2 * P 0 * P 2 ^ 3 * Q 0 + 18 * W.a₂ * W.a₆ * P 0 * P 2 ^ 3 * Q 0
      - 2 * W.a₁ ^ 2 * W.a₂ * W.a₃ * P 1 * P 2 ^ 3 * Q 0
      - 2 * W.a₂ ^ 2 * W.a₃ * P 1 * P 2 ^ 3 * Q 0 + 9 * W.a₁ * W.a₃ ^ 2 * P 1 * P 2 ^ 3 * Q 0
      + 9 * W.a₃ * W.a₄ * P 1 * P 2 ^ 3 * Q 0 - 9 * W.a₁ * W.a₆ * P 1 * P 2 ^ 3 * Q 0
      + W.a₂ ^ 2 * W.a₃ ^ 2 * P 2 ^ 4 * Q 0 - W.a₁ * W.a₂ * W.a₃ * W.a₄ * P 2 ^ 4 * Q 0
      - W.a₂ * W.a₄ ^ 2 * P 2 ^ 4 * Q 0 + 3 * W.a₁ ^ 2 * W.a₂ * W.a₆ * P 2 ^ 4 * Q 0
      + 6 * W.a₂ ^ 2 * W.a₆ * P 2 ^ 4 * Q 0 - 9 * W.a₁ * W.a₃ * W.a₆ * P 2 ^ 4 * Q 0
      - 9 * W.a₄ * W.a₆ * P 2 ^ 4 * Q 0 - 3 * W.a₁ ^ 2 * P 0 ^ 2 * P 1 * P 2 * Q 1
      - 3 * W.a₁ * P 0 * P 1 ^ 2 * P 2 * Q 1 + W.a₁ ^ 3 * W.a₂ * P 0 ^ 2 * P 2 ^ 2 * Q 1
      + W.a₁ * W.a₂ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 1 - 3 * W.a₁ ^ 2 * W.a₃ * P 0 ^ 2 * P 2 ^ 2 * Q 1
      - 3 * W.a₁ * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 1 - W.a₁ ^ 4 * P 0 * P 1 * P 2 ^ 2 * Q 1
      - W.a₁ ^ 2 * W.a₂ * P 0 * P 1 * P 2 ^ 2 * Q 1 - 3 * W.a₁ * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 1
      - W.a₁ ^ 3 * P 1 ^ 2 * P 2 ^ 2 * Q 1 - W.a₁ * W.a₂ * P 1 ^ 2 * P 2 ^ 2 * Q 1
      - 3 * W.a₁ * W.a₃ ^ 2 * P 0 * P 2 ^ 3 * Q 1 + W.a₁ ^ 3 * W.a₄ * P 0 * P 2 ^ 3 * Q 1
      + W.a₁ * W.a₂ * W.a₄ * P 0 * P 2 ^ 3 * Q 1 - 9 * W.a₁ * W.a₆ * P 0 * P 2 ^ 3 * Q 1
      - W.a₁ ^ 3 * W.a₃ * P 1 * P 2 ^ 3 * Q 1 - W.a₁ * W.a₂ * W.a₃ * P 1 * P 2 ^ 3 * Q 1
      - W.a₁ * W.a₂ * W.a₃ ^ 2 * P 2 ^ 4 * Q 1 + W.a₁ ^ 2 * W.a₃ * W.a₄ * P 2 ^ 4 * Q 1
      + W.a₁ * W.a₄ ^ 2 * P 2 ^ 4 * Q 1 - 3 * W.a₁ * W.a₂ * W.a₆ * P 2 ^ 4 * Q 1
      + 3 * W.a₂ * P 0 ^ 2 * P 1 ^ 2 * Q 2 + W.a₁ ^ 3 * W.a₂ * P 0 ^ 2 * P 1 * P 2 * Q 2
      - 2 * W.a₁ * W.a₂ ^ 2 * P 0 ^ 2 * P 1 * P 2 * Q 2
      + 3 * W.a₂ * W.a₃ * P 0 ^ 2 * P 1 * P 2 * Q 2 + 3 * W.a₁ * W.a₄ * P 0 ^ 2 * P 1 * P 2 * Q 2
      + 4 * W.a₁ ^ 2 * W.a₂ * P 0 * P 1 ^ 2 * P 2 * Q 2 + W.a₂ ^ 2 * P 0 * P 1 ^ 2 * P 2 * Q 2
      + 3 * W.a₄ * P 0 * P 1 ^ 2 * P 2 * Q 2 + 3 * W.a₁ * W.a₂ * P 1 ^ 3 * P 2 * Q 2
      + W.a₁ ^ 2 * W.a₂ ^ 3 * P 0 ^ 2 * P 2 ^ 2 * Q 2 + W.a₂ ^ 4 * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - 3 * W.a₁ * W.a₂ ^ 2 * W.a₃ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      + 3 * W.a₂ * W.a₃ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - 2 * W.a₁ ^ 2 * W.a₂ * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - 5 * W.a₂ ^ 2 * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      + 3 * W.a₁ * W.a₃ * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 2 + 3 * W.a₄ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 2
      + 9 * W.a₂ * W.a₆ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - W.a₁ ^ 3 * W.a₂ ^ 2 * P 0 * P 1 * P 2 ^ 2 * Q 2
      - W.a₁ * W.a₂ ^ 3 * P 0 * P 1 * P 2 ^ 2 * Q 2
      + 4 * W.a₁ ^ 2 * W.a₂ * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 2
      + W.a₂ ^ 2 * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 2 + W.a₁ ^ 3 * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 2
      + W.a₁ * W.a₂ * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 2
      + 3 * W.a₃ * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 2
      - W.a₁ ^ 2 * W.a₂ ^ 2 * P 1 ^ 2 * P 2 ^ 2 * Q 2 - W.a₂ ^ 3 * P 1 ^ 2 * P 2 ^ 2 * Q 2
      + 6 * W.a₁ * W.a₂ * W.a₃ * P 1 ^ 2 * P 2 ^ 2 * Q 2
      + W.a₁ ^ 2 * W.a₄ * P 1 ^ 2 * P 2 ^ 2 * Q 2 + 4 * W.a₂ * W.a₄ * P 1 ^ 2 * P 2 ^ 2 * Q 2
      + W.a₂ ^ 2 * W.a₃ ^ 2 * P 0 * P 2 ^ 3 * Q 2
      + W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₄ * P 0 * P 2 ^ 3 * Q 2 + W.a₂ ^ 3 * W.a₄ * P 0 * P 2 ^ 3 * Q 2
      - 4 * W.a₁ * W.a₂ * W.a₃ * W.a₄ * P 0 * P 2 ^ 3 * Q 2
      + 3 * W.a₃ ^ 2 * W.a₄ * P 0 * P 2 ^ 3 * Q 2 - W.a₁ ^ 2 * W.a₄ ^ 2 * P 0 * P 2 ^ 3 * Q 2
      - 5 * W.a₂ * W.a₄ ^ 2 * P 0 * P 2 ^ 3 * Q 2 + 3 * W.a₂ ^ 2 * W.a₆ * P 0 * P 2 ^ 3 * Q 2
      + 9 * W.a₄ * W.a₆ * P 0 * P 2 ^ 3 * Q 2 - W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₃ * P 1 * P 2 ^ 3 * Q 2
      - W.a₂ ^ 3 * W.a₃ * P 1 * P 2 ^ 3 * Q 2 + 3 * W.a₁ * W.a₂ * W.a₃ ^ 2 * P 1 * P 2 ^ 3 * Q 2
      + W.a₁ ^ 2 * W.a₃ * W.a₄ * P 1 * P 2 ^ 3 * Q 2
      + 4 * W.a₂ * W.a₃ * W.a₄ * P 1 * P 2 ^ 3 * Q 2
      - 3 * W.a₁ * W.a₂ * W.a₆ * P 1 * P 2 ^ 3 * Q 2 + W.a₂ * W.a₃ ^ 2 * W.a₄ * P 2 ^ 4 * Q 2
      - W.a₁ * W.a₃ * W.a₄ ^ 2 * P 2 ^ 4 * Q 2 - W.a₄ ^ 3 * P 2 ^ 4 * Q 2
      + W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₆ * P 2 ^ 4 * Q 2 + W.a₂ ^ 3 * W.a₆ * P 2 ^ 4 * Q 2
      - 3 * W.a₁ * W.a₂ * W.a₃ * W.a₆ * P 2 ^ 4 * Q 2) * (sub_eq_zero.mpr <| (equation_iff _).mp hQ)

lemma diagX_mul_negAddY {P Q : Fin 3 → R} (hP : W.Equation P) (hQ : W.Equation Q) :
    diagX W P Q * W.negAddY P Q = negDiagY W P Q * W.addX P Q := by
  linear_combination (norm := (simp only [diagX, negDiagY, negAddY, addX]; ring1))
    (3 * W.a₁ * W.a₂ * P 1 * Q 0 ^ 4 - W.a₁ ^ 2 * W.a₂ ^ 2 * P 2 * Q 0 ^ 4
      - W.a₂ ^ 3 * P 2 * Q 0 ^ 4 + 3 * W.a₁ * W.a₂ * W.a₃ * P 2 * Q 0 ^ 4
      + 3 * W.a₂ * W.a₄ * P 2 * Q 0 ^ 4 - 3 * W.a₁ * W.a₂ * P 0 * Q 0 ^ 3 * Q 1
      + 3 * W.a₁ ^ 2 * P 1 * Q 0 ^ 3 * Q 1 - 3 * W.a₁ * W.a₄ * P 2 * Q 0 ^ 3 * Q 1
      - 3 * W.a₂ * P 0 * Q 0 ^ 2 * Q 1 ^ 2 + 6 * W.a₁ * P 1 * Q 0 ^ 2 * Q 1 ^ 2
      + 3 * W.a₁ * W.a₃ * P 2 * Q 0 ^ 2 * Q 1 ^ 2 - 3 * W.a₄ * P 2 * Q 0 ^ 2 * Q 1 ^ 2
      + 3 * P 1 * Q 0 * Q 1 ^ 3 + 3 * W.a₃ * P 2 * Q 0 * Q 1 ^ 3
      + W.a₁ ^ 2 * W.a₂ ^ 2 * P 0 * Q 0 ^ 3 * Q 2 + W.a₂ ^ 3 * P 0 * Q 0 ^ 3 * Q 2
      - 3 * W.a₁ * W.a₂ * W.a₃ * P 0 * Q 0 ^ 3 * Q 2 - 3 * W.a₂ * W.a₄ * P 0 * Q 0 ^ 3 * Q 2
      - W.a₁ ^ 3 * W.a₂ * P 1 * Q 0 ^ 3 * Q 2 + 2 * W.a₁ * W.a₂ ^ 2 * P 1 * Q 0 ^ 3 * Q 2
      + 3 * W.a₁ ^ 2 * W.a₃ * P 1 * Q 0 ^ 3 * Q 2 + 6 * W.a₁ * W.a₄ * P 1 * Q 0 ^ 3 * Q 2
      - W.a₁ ^ 2 * W.a₂ ^ 3 * P 2 * Q 0 ^ 3 * Q 2 - W.a₂ ^ 4 * P 2 * Q 0 ^ 3 * Q 2
      + 3 * W.a₁ * W.a₂ ^ 2 * W.a₃ * P 2 * Q 0 ^ 3 * Q 2
      + 3 * W.a₂ ^ 2 * W.a₄ * P 2 * Q 0 ^ 3 * Q 2 - W.a₁ ^ 3 * W.a₂ * P 0 * Q 0 ^ 2 * Q 1 * Q 2
      - W.a₁ * W.a₂ ^ 2 * P 0 * Q 0 ^ 2 * Q 1 * Q 2 - 3 * W.a₂ * W.a₃ * P 0 * Q 0 ^ 2 * Q 1 * Q 2
      - 3 * W.a₁ * W.a₄ * P 0 * Q 0 ^ 2 * Q 1 * Q 2 + W.a₁ ^ 4 * P 1 * Q 0 ^ 2 * Q 1 * Q 2
      - 3 * W.a₁ ^ 2 * W.a₂ * P 1 * Q 0 ^ 2 * Q 1 * Q 2 - W.a₂ ^ 2 * P 1 * Q 0 ^ 2 * Q 1 * Q 2
      + 9 * W.a₁ * W.a₃ * P 1 * Q 0 ^ 2 * Q 1 * Q 2 + 3 * W.a₄ * P 1 * Q 0 ^ 2 * Q 1 * Q 2
      + W.a₁ ^ 3 * W.a₂ ^ 2 * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      + W.a₁ * W.a₂ ^ 3 * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      - 4 * W.a₁ ^ 2 * W.a₂ * W.a₃ * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      - W.a₂ ^ 2 * W.a₃ * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      + 3 * W.a₁ * W.a₃ ^ 2 * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      - W.a₁ ^ 3 * W.a₄ * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      - 4 * W.a₁ * W.a₂ * W.a₄ * P 2 * Q 0 ^ 2 * Q 1 * Q 2
      - 9 * W.a₁ * W.a₆ * P 2 * Q 0 ^ 2 * Q 1 * Q 2 - W.a₁ ^ 2 * W.a₂ * P 0 * Q 0 * Q 1 ^ 2 * Q 2
      - W.a₂ ^ 2 * P 0 * Q 0 * Q 1 ^ 2 * Q 2 - 3 * W.a₄ * P 0 * Q 0 * Q 1 ^ 2 * Q 2
      + 2 * W.a₁ ^ 3 * P 1 * Q 0 * Q 1 ^ 2 * Q 2 - W.a₁ * W.a₂ * P 1 * Q 0 * Q 1 ^ 2 * Q 2
      + 6 * W.a₃ * P 1 * Q 0 * Q 1 ^ 2 * Q 2 + W.a₁ ^ 2 * W.a₂ ^ 2 * P 2 * Q 0 * Q 1 ^ 2 * Q 2
      + W.a₂ ^ 3 * P 2 * Q 0 * Q 1 ^ 2 * Q 2 + W.a₁ ^ 3 * W.a₃ * P 2 * Q 0 * Q 1 ^ 2 * Q 2
      - 2 * W.a₁ * W.a₂ * W.a₃ * P 2 * Q 0 * Q 1 ^ 2 * Q 2
      + 3 * W.a₃ ^ 2 * P 2 * Q 0 * Q 1 ^ 2 * Q 2 - W.a₁ ^ 2 * W.a₄ * P 2 * Q 0 * Q 1 ^ 2 * Q 2
      - 4 * W.a₂ * W.a₄ * P 2 * Q 0 * Q 1 ^ 2 * Q 2 - 9 * W.a₆ * P 2 * Q 0 * Q 1 ^ 2 * Q 2
      + W.a₁ ^ 2 * P 1 * Q 1 ^ 3 * Q 2 + W.a₂ * P 1 * Q 1 ^ 3 * Q 2
      + W.a₁ ^ 2 * W.a₃ * P 2 * Q 1 ^ 3 * Q 2 + W.a₂ * W.a₃ * P 2 * Q 1 ^ 3 * Q 2
      - 3 * W.a₂ * W.a₃ ^ 2 * P 0 * Q 0 ^ 2 * Q 2 ^ 2
      + 2 * W.a₁ ^ 2 * W.a₂ * W.a₄ * P 0 * Q 0 ^ 2 * Q 2 ^ 2
      + 2 * W.a₂ ^ 2 * W.a₄ * P 0 * Q 0 ^ 2 * Q 2 ^ 2
      - 3 * W.a₁ * W.a₃ * W.a₄ * P 0 * Q 0 ^ 2 * Q 2 ^ 2 - 3 * W.a₄ ^ 2 * P 0 * Q 0 ^ 2 * Q 2 ^ 2
      - 9 * W.a₂ * W.a₆ * P 0 * Q 0 ^ 2 * Q 2 ^ 2
      - W.a₁ ^ 2 * W.a₂ * W.a₃ * P 1 * Q 0 ^ 2 * Q 2 ^ 2
      - W.a₂ ^ 2 * W.a₃ * P 1 * Q 0 ^ 2 * Q 2 ^ 2 + 6 * W.a₁ * W.a₃ ^ 2 * P 1 * Q 0 ^ 2 * Q 2 ^ 2
      - W.a₁ ^ 3 * W.a₄ * P 1 * Q 0 ^ 2 * Q 2 ^ 2
      + 5 * W.a₁ * W.a₂ * W.a₄ * P 1 * Q 0 ^ 2 * Q 2 ^ 2
      + 3 * W.a₃ * W.a₄ * P 1 * Q 0 ^ 2 * Q 2 ^ 2 + 9 * W.a₁ * W.a₆ * P 1 * Q 0 ^ 2 * Q 2 ^ 2
      - 2 * W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₄ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      - 2 * W.a₂ ^ 3 * W.a₄ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      + 6 * W.a₁ * W.a₂ * W.a₃ * W.a₄ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      - 3 * W.a₃ ^ 2 * W.a₄ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      + W.a₁ ^ 2 * W.a₄ ^ 2 * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      + 7 * W.a₂ * W.a₄ ^ 2 * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      + 3 * W.a₁ ^ 2 * W.a₂ * W.a₆ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      + 3 * W.a₂ ^ 2 * W.a₆ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      - 9 * W.a₁ * W.a₃ * W.a₆ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      - 18 * W.a₄ * W.a₆ * P 2 * Q 0 ^ 2 * Q 2 ^ 2
      - W.a₁ ^ 2 * W.a₂ * W.a₃ * P 0 * Q 0 * Q 1 * Q 2 ^ 2
      - W.a₂ ^ 2 * W.a₃ * P 0 * Q 0 * Q 1 * Q 2 ^ 2 - W.a₁ ^ 3 * W.a₄ * P 0 * Q 0 * Q 1 * Q 2 ^ 2
      - W.a₁ * W.a₂ * W.a₄ * P 0 * Q 0 * Q 1 * Q 2 ^ 2
      - 3 * W.a₃ * W.a₄ * P 0 * Q 0 * Q 1 * Q 2 ^ 2
      + 2 * W.a₁ ^ 3 * W.a₃ * P 1 * Q 0 * Q 1 * Q 2 ^ 2
      - W.a₁ * W.a₂ * W.a₃ * P 1 * Q 0 * Q 1 * Q 2 ^ 2 + 6 * W.a₃ ^ 2 * P 1 * Q 0 * Q 1 * Q 2 ^ 2
      - 4 * W.a₁ ^ 2 * W.a₄ * P 1 * Q 0 * Q 1 * Q 2 ^ 2 - W.a₂ * W.a₄ * P 1 * Q 0 * Q 1 * Q 2 ^ 2
      + 9 * W.a₆ * P 1 * Q 0 * Q 1 * Q 2 ^ 2
      + W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₃ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      + W.a₂ ^ 3 * W.a₃ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 3 * W.a₁ * W.a₂ * W.a₃ ^ 2 * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      + 3 * W.a₃ ^ 3 * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      + W.a₁ ^ 3 * W.a₂ * W.a₄ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      + W.a₁ * W.a₂ ^ 2 * W.a₄ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 5 * W.a₁ ^ 2 * W.a₃ * W.a₄ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 5 * W.a₂ * W.a₃ * W.a₄ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 3 * W.a₁ * W.a₄ ^ 2 * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 3 * W.a₁ ^ 3 * W.a₆ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - 3 * W.a₁ * W.a₂ * W.a₆ * P 2 * Q 0 * Q 1 * Q 2 ^ 2
      - W.a₁ ^ 2 * W.a₄ * P 0 * Q 1 ^ 2 * Q 2 ^ 2 - W.a₂ * W.a₄ * P 0 * Q 1 ^ 2 * Q 2 ^ 2
      + 2 * W.a₁ ^ 2 * W.a₃ * P 1 * Q 1 ^ 2 * Q 2 ^ 2 + 2 * W.a₂ * W.a₃ * P 1 * Q 1 ^ 2 * Q 2 ^ 2
      - 3 * W.a₁ * W.a₄ * P 1 * Q 1 ^ 2 * Q 2 ^ 2 + W.a₁ ^ 2 * W.a₃ ^ 2 * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      + W.a₂ * W.a₃ ^ 2 * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      + W.a₁ ^ 2 * W.a₂ * W.a₄ * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      + W.a₂ ^ 2 * W.a₄ * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      - 3 * W.a₁ * W.a₃ * W.a₄ * P 2 * Q 1 ^ 2 * Q 2 ^ 2 - 3 * W.a₄ ^ 2 * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      - 3 * W.a₁ ^ 2 * W.a₆ * P 2 * Q 1 ^ 2 * Q 2 ^ 2 - 3 * W.a₂ * W.a₆ * P 2 * Q 1 ^ 2 * Q 2 ^ 2
      - W.a₂ ^ 2 * W.a₃ ^ 2 * P 0 * Q 0 * Q 2 ^ 3
      + W.a₁ * W.a₂ * W.a₃ * W.a₄ * P 0 * Q 0 * Q 2 ^ 3
      - 3 * W.a₃ ^ 2 * W.a₄ * P 0 * Q 0 * Q 2 ^ 3 + W.a₁ ^ 2 * W.a₄ ^ 2 * P 0 * Q 0 * Q 2 ^ 3
      + 2 * W.a₂ * W.a₄ ^ 2 * P 0 * Q 0 * Q 2 ^ 3 - 3 * W.a₂ ^ 2 * W.a₆ * P 0 * Q 0 * Q 2 ^ 3
      - 9 * W.a₄ * W.a₆ * P 0 * Q 0 * Q 2 ^ 3 + W.a₁ * W.a₂ * W.a₃ ^ 2 * P 1 * Q 0 * Q 2 ^ 3
      + 3 * W.a₃ ^ 3 * P 1 * Q 0 * Q 2 ^ 3 - 2 * W.a₁ ^ 2 * W.a₃ * W.a₄ * P 1 * Q 0 * Q 2 ^ 3
      - W.a₂ * W.a₃ * W.a₄ * P 1 * Q 0 * Q 2 ^ 3 + 2 * W.a₁ * W.a₄ ^ 2 * P 1 * Q 0 * Q 2 ^ 3
      + 6 * W.a₁ * W.a₂ * W.a₆ * P 1 * Q 0 * Q 2 ^ 3 + 9 * W.a₃ * W.a₆ * P 1 * Q 0 * Q 2 ^ 3
      - W.a₂ * W.a₃ ^ 2 * W.a₄ * P 2 * Q 0 * Q 2 ^ 3
      - W.a₁ ^ 2 * W.a₂ * W.a₄ ^ 2 * P 2 * Q 0 * Q 2 ^ 3
      - W.a₂ ^ 2 * W.a₄ ^ 2 * P 2 * Q 0 * Q 2 ^ 3
      + 4 * W.a₁ * W.a₃ * W.a₄ ^ 2 * P 2 * Q 0 * Q 2 ^ 3 + 4 * W.a₄ ^ 3 * P 2 * Q 0 * Q 2 ^ 3
      - W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₆ * P 2 * Q 0 * Q 2 ^ 3 - W.a₂ ^ 3 * W.a₆ * P 2 * Q 0 * Q 2 ^ 3
      + 3 * W.a₁ * W.a₂ * W.a₃ * W.a₆ * P 2 * Q 0 * Q 2 ^ 3
      - 9 * W.a₃ ^ 2 * W.a₆ * P 2 * Q 0 * Q 2 ^ 3
      + 3 * W.a₁ ^ 2 * W.a₄ * W.a₆ * P 2 * Q 0 * Q 2 ^ 3
      + 3 * W.a₂ * W.a₄ * W.a₆ * P 2 * Q 0 * Q 2 ^ 3 - 27 * W.a₆ ^ 2 * P 2 * Q 0 * Q 2 ^ 3
      - W.a₁ ^ 2 * W.a₃ * W.a₄ * P 0 * Q 1 * Q 2 ^ 3 - W.a₂ * W.a₃ * W.a₄ * P 0 * Q 1 * Q 2 ^ 3
      + W.a₁ ^ 2 * W.a₃ ^ 2 * P 1 * Q 1 * Q 2 ^ 3 + 2 * W.a₂ * W.a₃ ^ 2 * P 1 * Q 1 * Q 2 ^ 3
      - 4 * W.a₁ * W.a₃ * W.a₄ * P 1 * Q 1 * Q 2 ^ 3 - W.a₄ ^ 2 * P 1 * Q 1 * Q 2 ^ 3
      + 3 * W.a₂ * W.a₆ * P 1 * Q 1 * Q 2 ^ 3 + W.a₂ * W.a₃ ^ 3 * P 2 * Q 1 * Q 2 ^ 3
      + W.a₁ ^ 2 * W.a₂ * W.a₃ * W.a₄ * P 2 * Q 1 * Q 2 ^ 3
      + W.a₂ ^ 2 * W.a₃ * W.a₄ * P 2 * Q 1 * Q 2 ^ 3
      - 4 * W.a₁ * W.a₃ ^ 2 * W.a₄ * P 2 * Q 1 * Q 2 ^ 3
      - 4 * W.a₃ * W.a₄ ^ 2 * P 2 * Q 1 * Q 2 ^ 3
      - 3 * W.a₁ ^ 2 * W.a₃ * W.a₆ * P 2 * Q 1 * Q 2 ^ 3 - W.a₂ * W.a₃ ^ 2 * W.a₄ * P 0 * Q 2 ^ 4
      + W.a₁ * W.a₃ * W.a₄ ^ 2 * P 0 * Q 2 ^ 4 + W.a₄ ^ 3 * P 0 * Q 2 ^ 4
      - 3 * W.a₂ * W.a₄ * W.a₆ * P 0 * Q 2 ^ 4 + W.a₂ * W.a₃ ^ 3 * P 1 * Q 2 ^ 4
      - W.a₁ * W.a₃ ^ 2 * W.a₄ * P 1 * Q 2 ^ 4 - W.a₃ * W.a₄ ^ 2 * P 1 * Q 2 ^ 4
      + 3 * W.a₂ * W.a₃ * W.a₆ * P 1 * Q 2 ^ 4 + 3 * W.a₁ * W.a₄ * W.a₆ * P 1 * Q 2 ^ 4
      - 3 * W.a₂ * W.a₃ ^ 2 * W.a₆ * P 2 * Q 2 ^ 4 - W.a₁ ^ 2 * W.a₂ * W.a₄ * W.a₆ * P 2 * Q 2 ^ 4
      - W.a₂ ^ 2 * W.a₄ * W.a₆ * P 2 * Q 2 ^ 4 + 6 * W.a₁ * W.a₃ * W.a₄ * W.a₆ * P 2 * Q 2 ^ 4
      + 6 * W.a₄ ^ 2 * W.a₆ * P 2 * Q 2 ^ 4 - 9 * W.a₂ * W.a₆ ^ 2 * P 2 * Q 2 ^ 4) * (sub_eq_zero.mpr <| (equation_iff _).mp hP)
    + (-3 * W.a₁ ^ 2 * P 0 ^ 2 * P 1 ^ 2 * Q 0 + 3 * W.a₂ * P 0 ^ 2 * P 1 ^ 2 * Q 0
      - 3 * W.a₁ * P 0 * P 1 ^ 3 * Q 0 + 2 * W.a₁ ^ 3 * W.a₂ * P 0 ^ 2 * P 1 * P 2 * Q 0
      - W.a₁ * W.a₂ ^ 2 * P 0 ^ 2 * P 1 * P 2 * Q 0
      - 3 * W.a₁ ^ 2 * W.a₃ * P 0 ^ 2 * P 1 * P 2 * Q 0
      + 3 * W.a₂ * W.a₃ * P 0 ^ 2 * P 1 * P 2 * Q 0 - W.a₁ ^ 4 * P 0 * P 1 ^ 2 * P 2 * Q 0
      + 3 * W.a₁ ^ 2 * W.a₂ * P 0 * P 1 ^ 2 * P 2 * Q 0 + W.a₂ ^ 2 * P 0 * P 1 ^ 2 * P 2 * Q 0
      - 3 * W.a₁ * W.a₃ * P 0 * P 1 ^ 2 * P 2 * Q 0 + 3 * W.a₄ * P 0 * P 1 ^ 2 * P 2 * Q 0
      - W.a₁ ^ 3 * P 1 ^ 3 * P 2 * Q 0 + 2 * W.a₁ * W.a₂ * P 1 ^ 3 * P 2 * Q 0
      + W.a₁ ^ 2 * W.a₂ ^ 3 * P 0 ^ 2 * P 2 ^ 2 * Q 0 + W.a₂ ^ 4 * P 0 ^ 2 * P 2 ^ 2 * Q 0
      - 3 * W.a₁ * W.a₂ ^ 2 * W.a₃ * P 0 ^ 2 * P 2 ^ 2 * Q 0
      + 3 * W.a₂ * W.a₃ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 0
      - 2 * W.a₁ ^ 2 * W.a₂ * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 0
      - 5 * W.a₂ ^ 2 * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 0
      + 3 * W.a₁ * W.a₃ * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 0 + 3 * W.a₄ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 0
      + 9 * W.a₂ * W.a₆ * P 0 ^ 2 * P 2 ^ 2 * Q 0
      - W.a₁ ^ 3 * W.a₂ ^ 2 * P 0 * P 1 * P 2 ^ 2 * Q 0
      - W.a₁ * W.a₂ ^ 3 * P 0 * P 1 * P 2 ^ 2 * Q 0
      + 4 * W.a₁ ^ 2 * W.a₂ * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 0
      + W.a₂ ^ 2 * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 0
      - 3 * W.a₁ * W.a₃ ^ 2 * P 0 * P 1 * P 2 ^ 2 * Q 0
      + 2 * W.a₁ ^ 3 * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 0
      + 2 * W.a₁ * W.a₂ * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 0
      + 3 * W.a₃ * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 0 - 9 * W.a₁ * W.a₆ * P 0 * P 1 * P 2 ^ 2 * Q 0
      - W.a₁ ^ 2 * W.a₂ ^ 2 * P 1 ^ 2 * P 2 ^ 2 * Q 0 - W.a₂ ^ 3 * P 1 ^ 2 * P 2 ^ 2 * Q 0
      - W.a₁ ^ 3 * W.a₃ * P 1 ^ 2 * P 2 ^ 2 * Q 0
      + 5 * W.a₁ * W.a₂ * W.a₃ * P 1 ^ 2 * P 2 ^ 2 * Q 0
      + W.a₁ ^ 2 * W.a₄ * P 1 ^ 2 * P 2 ^ 2 * Q 0 + 4 * W.a₂ * W.a₄ * P 1 ^ 2 * P 2 ^ 2 * Q 0
      + W.a₂ ^ 2 * W.a₃ ^ 2 * P 0 * P 2 ^ 3 * Q 0
      + W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₄ * P 0 * P 2 ^ 3 * Q 0 + W.a₂ ^ 3 * W.a₄ * P 0 * P 2 ^ 3 * Q 0
      - 4 * W.a₁ * W.a₂ * W.a₃ * W.a₄ * P 0 * P 2 ^ 3 * Q 0
      + 3 * W.a₃ ^ 2 * W.a₄ * P 0 * P 2 ^ 3 * Q 0 - W.a₁ ^ 2 * W.a₄ ^ 2 * P 0 * P 2 ^ 3 * Q 0
      - 5 * W.a₂ * W.a₄ ^ 2 * P 0 * P 2 ^ 3 * Q 0 + 3 * W.a₂ ^ 2 * W.a₆ * P 0 * P 2 ^ 3 * Q 0
      + 9 * W.a₄ * W.a₆ * P 0 * P 2 ^ 3 * Q 0 - W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₃ * P 1 * P 2 ^ 3 * Q 0
      - W.a₂ ^ 3 * W.a₃ * P 1 * P 2 ^ 3 * Q 0 + 2 * W.a₁ * W.a₂ * W.a₃ ^ 2 * P 1 * P 2 ^ 3 * Q 0
      + 2 * W.a₁ ^ 2 * W.a₃ * W.a₄ * P 1 * P 2 ^ 3 * Q 0
      + 4 * W.a₂ * W.a₃ * W.a₄ * P 1 * P 2 ^ 3 * Q 0 + W.a₁ * W.a₄ ^ 2 * P 1 * P 2 ^ 3 * Q 0
      - 6 * W.a₁ * W.a₂ * W.a₆ * P 1 * P 2 ^ 3 * Q 0 + W.a₂ * W.a₃ ^ 2 * W.a₄ * P 2 ^ 4 * Q 0
      - W.a₁ * W.a₃ * W.a₄ ^ 2 * P 2 ^ 4 * Q 0 - W.a₄ ^ 3 * P 2 ^ 4 * Q 0
      + W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₆ * P 2 ^ 4 * Q 0 + W.a₂ ^ 3 * W.a₆ * P 2 ^ 4 * Q 0
      - 3 * W.a₁ * W.a₂ * W.a₃ * W.a₆ * P 2 ^ 4 * Q 0 - 3 * W.a₁ * P 0 ^ 2 * P 1 ^ 2 * Q 1
      - 3 * P 0 * P 1 ^ 3 * Q 1 + W.a₁ ^ 2 * W.a₂ * P 0 ^ 2 * P 1 * P 2 * Q 1
      + W.a₂ ^ 2 * P 0 ^ 2 * P 1 * P 2 * Q 1 - 6 * W.a₁ * W.a₃ * P 0 ^ 2 * P 1 * P 2 * Q 1
      - 3 * W.a₄ * P 0 ^ 2 * P 1 * P 2 * Q 1 - W.a₁ ^ 3 * P 0 * P 1 ^ 2 * P 2 * Q 1
      - W.a₁ * W.a₂ * P 0 * P 1 ^ 2 * P 2 * Q 1 - 6 * W.a₃ * P 0 * P 1 ^ 2 * P 2 * Q 1
      - W.a₁ ^ 2 * P 1 ^ 3 * P 2 * Q 1 - W.a₂ * P 1 ^ 3 * P 2 * Q 1
      + W.a₁ ^ 2 * W.a₂ * W.a₃ * P 0 ^ 2 * P 2 ^ 2 * Q 1
      + W.a₂ ^ 2 * W.a₃ * P 0 ^ 2 * P 2 ^ 2 * Q 1 - 3 * W.a₁ * W.a₃ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 1
      - 3 * W.a₃ * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 1 - W.a₁ ^ 3 * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 1
      - W.a₁ * W.a₂ * W.a₃ * P 0 * P 1 * P 2 ^ 2 * Q 1 - 6 * W.a₃ ^ 2 * P 0 * P 1 * P 2 ^ 2 * Q 1
      + W.a₁ ^ 2 * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 1 + W.a₂ * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 1
      - 9 * W.a₆ * P 0 * P 1 * P 2 ^ 2 * Q 1 - 2 * W.a₁ ^ 2 * W.a₃ * P 1 ^ 2 * P 2 ^ 2 * Q 1
      - 2 * W.a₂ * W.a₃ * P 1 ^ 2 * P 2 ^ 2 * Q 1 - 3 * W.a₃ ^ 3 * P 0 * P 2 ^ 3 * Q 1
      + W.a₁ ^ 2 * W.a₃ * W.a₄ * P 0 * P 2 ^ 3 * Q 1 + W.a₂ * W.a₃ * W.a₄ * P 0 * P 2 ^ 3 * Q 1
      - 9 * W.a₃ * W.a₆ * P 0 * P 2 ^ 3 * Q 1 - W.a₁ ^ 2 * W.a₃ ^ 2 * P 1 * P 2 ^ 3 * Q 1
      - 2 * W.a₂ * W.a₃ ^ 2 * P 1 * P 2 ^ 3 * Q 1 + W.a₁ * W.a₃ * W.a₄ * P 1 * P 2 ^ 3 * Q 1
      + W.a₄ ^ 2 * P 1 * P 2 ^ 3 * Q 1 - 3 * W.a₂ * W.a₆ * P 1 * P 2 ^ 3 * Q 1
      - W.a₂ * W.a₃ ^ 3 * P 2 ^ 4 * Q 1 + W.a₁ * W.a₃ ^ 2 * W.a₄ * P 2 ^ 4 * Q 1
      + W.a₃ * W.a₄ ^ 2 * P 2 ^ 4 * Q 1 - 3 * W.a₂ * W.a₃ * W.a₆ * P 2 ^ 4 * Q 1
      - 3 * W.a₁ * W.a₃ * P 0 ^ 2 * P 1 ^ 2 * Q 2 + 3 * W.a₄ * P 0 ^ 2 * P 1 ^ 2 * Q 2
      - 3 * W.a₃ * P 0 * P 1 ^ 3 * Q 2 + W.a₁ ^ 2 * W.a₂ * W.a₃ * P 0 ^ 2 * P 1 * P 2 * Q 2
      + W.a₂ ^ 2 * W.a₃ * P 0 ^ 2 * P 1 * P 2 * Q 2
      - 3 * W.a₁ * W.a₃ ^ 2 * P 0 ^ 2 * P 1 * P 2 * Q 2
      + W.a₁ ^ 3 * W.a₄ * P 0 ^ 2 * P 1 * P 2 * Q 2
      - 2 * W.a₁ * W.a₂ * W.a₄ * P 0 ^ 2 * P 1 * P 2 * Q 2
      + 9 * W.a₁ * W.a₆ * P 0 ^ 2 * P 1 * P 2 * Q 2 - W.a₁ ^ 3 * W.a₃ * P 0 * P 1 ^ 2 * P 2 * Q 2
      - W.a₁ * W.a₂ * W.a₃ * P 0 * P 1 ^ 2 * P 2 * Q 2 - 3 * W.a₃ ^ 2 * P 0 * P 1 ^ 2 * P 2 * Q 2
      + 4 * W.a₁ ^ 2 * W.a₄ * P 0 * P 1 ^ 2 * P 2 * Q 2 + W.a₂ * W.a₄ * P 0 * P 1 ^ 2 * P 2 * Q 2
      + 9 * W.a₆ * P 0 * P 1 ^ 2 * P 2 * Q 2 - W.a₁ ^ 2 * W.a₃ * P 1 ^ 3 * P 2 * Q 2
      - W.a₂ * W.a₃ * P 1 ^ 3 * P 2 * Q 2 + 3 * W.a₁ * W.a₄ * P 1 ^ 3 * P 2 * Q 2
      + W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      + W.a₂ ^ 3 * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - 3 * W.a₁ * W.a₂ * W.a₃ * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      + 3 * W.a₃ ^ 2 * W.a₄ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - W.a₁ ^ 2 * W.a₄ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - 4 * W.a₂ * W.a₄ ^ 2 * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - 3 * W.a₁ ^ 2 * W.a₂ * W.a₆ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      - 3 * W.a₂ ^ 2 * W.a₆ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      + 9 * W.a₁ * W.a₃ * W.a₆ * P 0 ^ 2 * P 2 ^ 2 * Q 2
      + 18 * W.a₄ * W.a₆ * P 0 ^ 2 * P 2 ^ 2 * Q 2 - 3 * W.a₃ ^ 3 * P 0 * P 1 * P 2 ^ 2 * Q 2
      - W.a₁ ^ 3 * W.a₂ * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 2
      - W.a₁ * W.a₂ ^ 2 * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 2
      + 5 * W.a₁ ^ 2 * W.a₃ * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 2
      + 2 * W.a₂ * W.a₃ * W.a₄ * P 0 * P 1 * P 2 ^ 2 * Q 2
      + 3 * W.a₁ ^ 3 * W.a₆ * P 0 * P 1 * P 2 ^ 2 * Q 2
      + 3 * W.a₁ * W.a₂ * W.a₆ * P 0 * P 1 * P 2 ^ 2 * Q 2
      - W.a₁ ^ 2 * W.a₃ ^ 2 * P 1 ^ 2 * P 2 ^ 2 * Q 2 - W.a₂ * W.a₃ ^ 2 * P 1 ^ 2 * P 2 ^ 2 * Q 2
      - W.a₁ ^ 2 * W.a₂ * W.a₄ * P 1 ^ 2 * P 2 ^ 2 * Q 2
      - W.a₂ ^ 2 * W.a₄ * P 1 ^ 2 * P 2 ^ 2 * Q 2
      + 6 * W.a₁ * W.a₃ * W.a₄ * P 1 ^ 2 * P 2 ^ 2 * Q 2 + 3 * W.a₄ ^ 2 * P 1 ^ 2 * P 2 ^ 2 * Q 2
      + 3 * W.a₁ ^ 2 * W.a₆ * P 1 ^ 2 * P 2 ^ 2 * Q 2 + 3 * W.a₂ * W.a₆ * P 1 ^ 2 * P 2 ^ 2 * Q 2
      + W.a₂ * W.a₃ ^ 2 * W.a₄ * P 0 * P 2 ^ 3 * Q 2
      + W.a₁ ^ 2 * W.a₂ * W.a₄ ^ 2 * P 0 * P 2 ^ 3 * Q 2
      + W.a₂ ^ 2 * W.a₄ ^ 2 * P 0 * P 2 ^ 3 * Q 2
      - 4 * W.a₁ * W.a₃ * W.a₄ ^ 2 * P 0 * P 2 ^ 3 * Q 2 - 4 * W.a₄ ^ 3 * P 0 * P 2 ^ 3 * Q 2
      + 9 * W.a₃ ^ 2 * W.a₆ * P 0 * P 2 ^ 3 * Q 2
      - 3 * W.a₁ ^ 2 * W.a₄ * W.a₆ * P 0 * P 2 ^ 3 * Q 2 + 27 * W.a₆ ^ 2 * P 0 * P 2 ^ 3 * Q 2
      - W.a₂ * W.a₃ ^ 3 * P 1 * P 2 ^ 3 * Q 2
      - W.a₁ ^ 2 * W.a₂ * W.a₃ * W.a₄ * P 1 * P 2 ^ 3 * Q 2
      - W.a₂ ^ 2 * W.a₃ * W.a₄ * P 1 * P 2 ^ 3 * Q 2
      + 4 * W.a₁ * W.a₃ ^ 2 * W.a₄ * P 1 * P 2 ^ 3 * Q 2
      + 4 * W.a₃ * W.a₄ ^ 2 * P 1 * P 2 ^ 3 * Q 2
      + 3 * W.a₁ ^ 2 * W.a₃ * W.a₆ * P 1 * P 2 ^ 3 * Q 2
      - 3 * W.a₁ * W.a₄ * W.a₆ * P 1 * P 2 ^ 3 * Q 2 + 3 * W.a₂ * W.a₃ ^ 2 * W.a₆ * P 2 ^ 4 * Q 2
      + W.a₁ ^ 2 * W.a₂ * W.a₄ * W.a₆ * P 2 ^ 4 * Q 2 + W.a₂ ^ 2 * W.a₄ * W.a₆ * P 2 ^ 4 * Q 2
      - 6 * W.a₁ * W.a₃ * W.a₄ * W.a₆ * P 2 ^ 4 * Q 2 - 6 * W.a₄ ^ 2 * W.a₆ * P 2 ^ 4 * Q 2
      + 9 * W.a₂ * W.a₆ ^ 2 * P 2 ^ 4 * Q 2) * (sub_eq_zero.mpr <| (equation_iff _).mp hQ)

lemma diagX_smul (P Q : Fin 3 → R) (u v : R) :
    diagX W (u • P) (v • Q) = (u * v) ^ 2 * diagX W P Q := by
  simp only [diagX, smul_fin3_ext]
  ring1

lemma negDiagY_smul (P Q : Fin 3 → R) (u v : R) :
    negDiagY W (u • P) (v • Q) = (u * v) ^ 2 * negDiagY W P Q := by
  simp only [negDiagY, smul_fin3_ext]
  ring1

lemma diagZ_smul (P Q : Fin 3 → R) (u v : R) :
    diagZ W (u • P) (v • Q) = (u * v) ^ 2 * diagZ W P Q := by
  simp only [diagZ, smul_fin3_ext]
  ring1

lemma map_diagX (f : R →+* S) (P Q : Fin 3 → R) :
    diagX (W.map f) (f ∘ P) (f ∘ Q) = f (diagX W P Q) := by
  simp only [diagX, map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow,
    WeierstrassCurve.map, Function.comp_apply]

lemma map_negDiagY (f : R →+* S) (P Q : Fin 3 → R) :
    negDiagY (W.map f) (f ∘ P) (f ∘ Q) = f (negDiagY W P Q) := by
  simp only [negDiagY, map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow,
    WeierstrassCurve.map, Function.comp_apply]

lemma map_diagZ (f : R →+* S) (P Q : Fin 3 → R) :
    diagZ (W.map f) (f ∘ P) (f ∘ Q) = f (diagZ W P Q) := by
  simp only [diagZ, map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow,
    WeierstrassCurve.map, Function.comp_apply]

end GlobalTheory.AddLaw
end

section
open WeierstrassCurve WeierstrassCurve.Projective

namespace GlobalTheory.AddLaw

variable {R : Type*} [CommRing R]

def originN (W : Projective R) (z₁ w₁ z₂ : R) : R :=
  z₁ ^ 2 + z₁ * z₂ + z₂ ^ 2 + W.a₁ * w₁ + W.a₂ * w₁ * (z₁ + z₂) + W.a₄ * w₁ ^ 2

def originD (W : Projective R) (w₁ z₂ w₂ : R) : R :=
  1 - W.a₁ * z₂ - W.a₂ * z₂ ^ 2 - W.a₃ * (w₁ + w₂) - W.a₄ * z₂ * (w₁ + w₂)
    - W.a₆ * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2)

def lineCubicCoeff (W : Projective R) (n d : R) : R :=
  d ^ 3 + W.a₂ * n * d ^ 2 + W.a₄ * n ^ 2 * d + W.a₆ * n ^ 3

def lineQuadCoeff (W : Projective R) (n v d : R) : R :=
  W.a₁ * n * d ^ 2 + W.a₂ * v * d ^ 2 + W.a₃ * n ^ 2 * d + 2 * W.a₄ * n * v * d
    + 3 * W.a₆ * n ^ 2 * v

variable {W : Projective R}

lemma sub_mul_originD {z₁ w₁ z₂ w₂ : R} (h₁ : W.Equation ![z₁, -1, w₁])
    (h₂ : W.Equation ![z₂, -1, w₂]) :
    (w₂ - w₁) * originD W w₁ z₂ w₂ = (z₂ - z₁) * originN W z₁ w₁ z₂ := by
  have h := (equation_iff _).mp h₁
  have h' := (equation_iff _).mp h₂
  linear_combination (norm := (simp only [originN, originD, fin3_def_ext]; ring1)) h' - h

lemma addZ_line (z₁ w₁ z₂ l : R) :
    W.addZ ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)] =
      l * W.addX ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)]
      - (w₁ - l * z₁) * W.negAddY ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)] := by
  simp only [addX, addZ, negAddY, fin3_def_ext]
  ring1

lemma negAddY_line {z₁ w₁ z₂ l : R} (h₁ : W.Equation ![z₁, -1, w₁])
    (hl : originN W z₁ w₁ z₂ = l * originD W w₁ z₂ (w₁ + l * (z₂ - z₁))) :
    (-lineQuadCoeff W l (w₁ - l * z₁) 1 - lineCubicCoeff W l 1 * (z₁ + z₂))
        * W.negAddY ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)]
      + lineCubicCoeff W l 1 * W.addX ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)] = 0 := by
  have h := sub_eq_zero.mpr <| (equation_iff _).mp h₁
  linear_combination (norm := (simp only [originN, originD, lineCubicCoeff, lineQuadCoeff, addX, negAddY, fin3_def_ext]; ring1))
    (-3 * z₁ - 3 * W.a₂ * z₁ * l - 3 * W.a₄ * z₁ * l ^ 2 - 3 * W.a₆ * z₁ * l ^ 3 + 3 * z₂
      + 3 * W.a₂ * l * z₂ + 3 * W.a₄ * l ^ 2 * z₂ + 3 * W.a₆ * l ^ 3 * z₂) * h
    + (-3 * z₁ ^ 2 - W.a₁ * z₁ * l - 2 * W.a₂ * z₁ ^ 2 * l - W.a₃ * z₁ * l ^ 2
      - W.a₄ * z₁ ^ 2 * l ^ 2 - W.a₂ * z₁ * w₁ - 2 * W.a₄ * z₁ * l * w₁
      - 3 * W.a₆ * z₁ * l ^ 2 * w₁ + 3 * z₁ * z₂ + W.a₁ * l * z₂ + 2 * W.a₂ * z₁ * l * z₂
      + W.a₃ * l ^ 2 * z₂ + W.a₄ * z₁ * l ^ 2 * z₂ + W.a₂ * w₁ * z₂ + 2 * W.a₄ * l * w₁ * z₂
      + 3 * W.a₆ * l ^ 2 * w₁ * z₂) * hl

lemma diagZ_line {z₁ w₁ z₂ l : R} (h₁ : W.Equation ![z₁, -1, w₁])
    (hl : originN W z₁ w₁ z₂ = l * originD W w₁ z₂ (w₁ + l * (z₂ - z₁))) :
    diagZ W ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)] =
      l * diagX W ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)]
      - (w₁ - l * z₁) * negDiagY W ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)] := by
  have h := sub_eq_zero.mpr <| (equation_iff _).mp h₁
  linear_combination (norm := (simp only [originN, originD, diagX, diagZ, negDiagY, fin3_def_ext]; ring1))
    (-3 + 3 * W.a₁ * z₁ + 3 * W.a₂ * z₁ ^ 2 - W.a₁ ^ 2 * l - 4 * W.a₂ * l
      - W.a₁ ^ 2 * W.a₃ * z₁ * l ^ 2 - 4 * W.a₂ * W.a₃ * z₁ * l ^ 2
      - W.a₂ * W.a₃ ^ 2 * z₁ ^ 2 * l ^ 3 + W.a₁ * W.a₃ * W.a₄ * z₁ ^ 2 * l ^ 3
      + W.a₄ ^ 2 * z₁ ^ 2 * l ^ 3 + W.a₁ ^ 3 * w₁ + 4 * W.a₁ * W.a₂ * w₁ + 3 * W.a₃ * w₁
      + W.a₁ ^ 2 * W.a₂ * z₁ * w₁ + 4 * W.a₂ ^ 2 * z₁ * w₁ - 3 * W.a₁ * W.a₃ * z₁ * w₁
      - 3 * W.a₄ * z₁ * w₁ + 2 * W.a₁ ^ 2 * W.a₃ * l * w₁ + 8 * W.a₂ * W.a₃ * l * w₁
      + 3 * W.a₂ * W.a₃ ^ 2 * z₁ * l ^ 2 * w₁ - 3 * W.a₁ * W.a₃ * W.a₄ * z₁ * l ^ 2 * w₁
      - 3 * W.a₄ ^ 2 * z₁ * l ^ 2 * w₁ - 3 * W.a₃ ^ 2 * w₁ ^ 2 + W.a₁ ^ 2 * W.a₄ * w₁ ^ 2
      + 4 * W.a₂ * W.a₄ * w₁ ^ 2 - 9 * W.a₆ * w₁ ^ 2 - 3 * W.a₂ * W.a₃ ^ 2 * l * w₁ ^ 2
      + 3 * W.a₁ * W.a₃ * W.a₄ * l * w₁ ^ 2 + 3 * W.a₄ ^ 2 * l * w₁ ^ 2 + 3 * W.a₁ * z₂
      + 3 * W.a₂ * z₁ * z₂ + W.a₁ ^ 3 * l * z₂ + 4 * W.a₁ * W.a₂ * l * z₂ + 3 * W.a₃ * l * z₂
      + W.a₁ ^ 2 * W.a₃ * l ^ 2 * z₂ + 4 * W.a₂ * W.a₃ * l ^ 2 * z₂
      + 3 * W.a₃ ^ 2 * z₁ * l ^ 2 * z₂ - W.a₁ ^ 2 * W.a₄ * z₁ * l ^ 2 * z₂
      - 4 * W.a₂ * W.a₄ * z₁ * l ^ 2 * z₂ + 9 * W.a₆ * z₁ * l ^ 2 * z₂
      + 2 * W.a₂ * W.a₃ ^ 2 * z₁ * l ^ 3 * z₂ - 2 * W.a₁ * W.a₃ * W.a₄ * z₁ * l ^ 3 * z₂
      - 2 * W.a₄ ^ 2 * z₁ * l ^ 3 * z₂ + W.a₁ ^ 2 * W.a₂ * w₁ * z₂ + 4 * W.a₂ ^ 2 * w₁ * z₂
      - 3 * W.a₁ * W.a₃ * w₁ * z₂ - 3 * W.a₄ * w₁ * z₂ - 6 * W.a₃ ^ 2 * l * w₁ * z₂
      + 2 * W.a₁ ^ 2 * W.a₄ * l * w₁ * z₂ + 8 * W.a₂ * W.a₄ * l * w₁ * z₂
      - 18 * W.a₆ * l * w₁ * z₂ - 3 * W.a₂ * W.a₃ ^ 2 * l ^ 2 * w₁ * z₂
      + 3 * W.a₁ * W.a₃ * W.a₄ * l ^ 2 * w₁ * z₂ + 3 * W.a₄ ^ 2 * l ^ 2 * w₁ * z₂
      + 3 * W.a₂ * z₂ ^ 2 + W.a₁ ^ 2 * W.a₂ * l * z₂ ^ 2 + 4 * W.a₂ ^ 2 * l * z₂ ^ 2
      - 3 * W.a₁ * W.a₃ * l * z₂ ^ 2 - 3 * W.a₄ * l * z₂ ^ 2 - 3 * W.a₃ ^ 2 * l ^ 2 * z₂ ^ 2
      + W.a₁ ^ 2 * W.a₄ * l ^ 2 * z₂ ^ 2 + 4 * W.a₂ * W.a₄ * l ^ 2 * z₂ ^ 2
      - 9 * W.a₆ * l ^ 2 * z₂ ^ 2 - W.a₂ * W.a₃ ^ 2 * l ^ 3 * z₂ ^ 2
      + W.a₁ * W.a₃ * W.a₄ * l ^ 3 * z₂ ^ 2 + W.a₄ ^ 2 * l ^ 3 * z₂ ^ 2) * h
    + (-3 * z₁ + 3 * W.a₁ * z₁ ^ 2 + 3 * W.a₂ * z₁ ^ 3 - W.a₁ ^ 2 * w₁ - 4 * W.a₂ * w₁
      + W.a₁ ^ 3 * z₁ * w₁ + 4 * W.a₁ * W.a₂ * z₁ * w₁ + 3 * W.a₃ * z₁ * w₁
      + W.a₁ ^ 2 * W.a₂ * z₁ ^ 2 * w₁ + 4 * W.a₂ ^ 2 * z₁ ^ 2 * w₁ - 3 * W.a₁ * W.a₃ * z₁ ^ 2 * w₁
      - 3 * W.a₄ * z₁ ^ 2 * w₁ + W.a₁ ^ 2 * W.a₃ * w₁ ^ 2 + 4 * W.a₂ * W.a₃ * w₁ ^ 2
      - 3 * W.a₃ ^ 2 * z₁ * w₁ ^ 2 + W.a₁ ^ 2 * W.a₄ * z₁ * w₁ ^ 2 + 4 * W.a₂ * W.a₄ * z₁ * w₁ ^ 2
      - 9 * W.a₆ * z₁ * w₁ ^ 2 - W.a₂ * W.a₃ ^ 2 * w₁ ^ 3 + W.a₁ * W.a₃ * W.a₄ * w₁ ^ 3
      + W.a₄ ^ 2 * w₁ ^ 3) * hl

lemma negDiagY_line {z₁ w₁ z₂ l : R} (h₁ : W.Equation ![z₁, -1, w₁])
    (hl : originN W z₁ w₁ z₂ = l * originD W w₁ z₂ (w₁ + l * (z₂ - z₁))) :
    (-lineQuadCoeff W l (w₁ - l * z₁) 1 - lineCubicCoeff W l 1 * (z₁ + z₂))
        * negDiagY W ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)]
      + lineCubicCoeff W l 1 * diagX W ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)] = 0 := by
  have h := sub_eq_zero.mpr <| (equation_iff _).mp h₁
  linear_combination (norm := (simp only [originN, originD, lineCubicCoeff, lineQuadCoeff, diagX, negDiagY, fin3_def_ext]; ring1))
    (W.a₁ ^ 2 + W.a₂ - 3 * W.a₃ * z₁ - 6 * W.a₂ ^ 2 * z₁ ^ 2 + 6 * W.a₂ ^ 2 * l
      + 3 * W.a₁ * W.a₃ * l + 3 * W.a₄ * l + W.a₁ ^ 2 * W.a₃ * z₁ * l - 2 * W.a₂ * W.a₃ * z₁ * l
      - 3 * W.a₃ ^ 2 * z₁ ^ 2 * l + W.a₁ ^ 2 * W.a₄ * z₁ ^ 2 * l - 5 * W.a₂ * W.a₄ * z₁ ^ 2 * l
      - 9 * W.a₆ * z₁ ^ 2 * l + 3 * W.a₃ ^ 2 * l ^ 2 + 6 * W.a₂ * W.a₄ * l ^ 2 + 9 * W.a₆ * l ^ 2
      + 6 * W.a₂ ^ 2 * W.a₃ * z₁ * l ^ 2 + 3 * W.a₁ * W.a₃ ^ 2 * z₁ * l ^ 2
      - 3 * W.a₂ * W.a₃ ^ 2 * z₁ ^ 2 * l ^ 2 + 3 * W.a₁ * W.a₃ * W.a₄ * z₁ ^ 2 * l ^ 2
      + 3 * W.a₄ ^ 2 * z₁ ^ 2 * l ^ 2 - 9 * W.a₂ * W.a₆ * z₁ ^ 2 * l ^ 2 + W.a₂ * W.a₃ ^ 2 * l ^ 3
      - W.a₁ * W.a₃ * W.a₄ * l ^ 3 - W.a₄ ^ 2 * l ^ 3 + W.a₁ ^ 2 * W.a₆ * l ^ 3
      + 4 * W.a₂ * W.a₆ * l ^ 3 + 3 * W.a₃ ^ 3 * z₁ * l ^ 3 + 6 * W.a₂ * W.a₃ * W.a₄ * z₁ * l ^ 3
      + 6 * W.a₃ * W.a₆ * z₁ * l ^ 3 - 6 * W.a₂ ^ 2 * W.a₆ * z₁ ^ 2 * l ^ 3
      + W.a₂ * W.a₃ ^ 3 * z₁ * l ^ 4 - W.a₁ * W.a₃ ^ 2 * W.a₄ * z₁ * l ^ 4
      - W.a₃ * W.a₄ ^ 2 * z₁ * l ^ 4 + W.a₁ ^ 2 * W.a₃ * W.a₆ * z₁ * l ^ 4
      + 4 * W.a₂ * W.a₃ * W.a₆ * z₁ * l ^ 4 + W.a₂ * W.a₃ ^ 2 * W.a₄ * z₁ ^ 2 * l ^ 4
      - W.a₁ * W.a₃ * W.a₄ ^ 2 * z₁ ^ 2 * l ^ 4 - W.a₄ ^ 3 * z₁ ^ 2 * l ^ 4
      - 3 * W.a₃ ^ 2 * W.a₆ * z₁ ^ 2 * l ^ 4 + W.a₁ ^ 2 * W.a₄ * W.a₆ * z₁ ^ 2 * l ^ 4
      - 2 * W.a₂ * W.a₄ * W.a₆ * z₁ ^ 2 * l ^ 4 - 9 * W.a₆ ^ 2 * z₁ ^ 2 * l ^ 4
      - 6 * W.a₁ * W.a₂ ^ 2 * w₁ - 2 * W.a₁ ^ 2 * W.a₃ * w₁ - 2 * W.a₂ * W.a₃ * w₁
      - 6 * W.a₂ ^ 3 * z₁ * w₁ + 3 * W.a₃ ^ 2 * z₁ * w₁ - W.a₁ ^ 2 * W.a₄ * z₁ * w₁
      - W.a₂ * W.a₄ * z₁ * w₁ + 9 * W.a₆ * z₁ * w₁ - 12 * W.a₂ ^ 2 * W.a₃ * l * w₁
      - 6 * W.a₁ * W.a₃ ^ 2 * l * w₁ - 6 * W.a₁ * W.a₂ * W.a₄ * l * w₁ - 6 * W.a₃ * W.a₄ * l * w₁
      - 6 * W.a₂ ^ 2 * W.a₄ * z₁ * l * w₁ - 6 * W.a₃ ^ 3 * l ^ 2 * w₁
      - 12 * W.a₂ * W.a₃ * W.a₄ * l ^ 2 * w₁ - 18 * W.a₃ * W.a₆ * l ^ 2 * w₁
      - 3 * W.a₂ ^ 2 * W.a₃ ^ 2 * z₁ * l ^ 2 * w₁
      + 3 * W.a₁ * W.a₂ * W.a₃ * W.a₄ * z₁ * l ^ 2 * w₁ + 3 * W.a₂ * W.a₄ ^ 2 * z₁ * l ^ 2 * w₁
      - 3 * W.a₁ ^ 2 * W.a₂ * W.a₆ * z₁ * l ^ 2 * w₁ + 6 * W.a₂ ^ 2 * W.a₆ * z₁ * l ^ 2 * w₁
      + 9 * W.a₁ * W.a₃ * W.a₆ * z₁ * l ^ 2 * w₁ + 9 * W.a₄ * W.a₆ * z₁ * l ^ 2 * w₁
      - 2 * W.a₂ * W.a₃ ^ 3 * l ^ 3 * w₁ + 2 * W.a₁ * W.a₃ ^ 2 * W.a₄ * l ^ 3 * w₁
      + 2 * W.a₃ * W.a₄ ^ 2 * l ^ 3 * w₁ - 2 * W.a₁ ^ 2 * W.a₃ * W.a₆ * l ^ 3 * w₁
      - 8 * W.a₂ * W.a₃ * W.a₆ * l ^ 3 * w₁ - 4 * W.a₂ * W.a₃ ^ 2 * W.a₄ * z₁ * l ^ 3 * w₁
      + 4 * W.a₁ * W.a₃ * W.a₄ ^ 2 * z₁ * l ^ 3 * w₁ + 4 * W.a₄ ^ 3 * z₁ * l ^ 3 * w₁
      + 12 * W.a₃ ^ 2 * W.a₆ * z₁ * l ^ 3 * w₁ - 4 * W.a₁ ^ 2 * W.a₄ * W.a₆ * z₁ * l ^ 3 * w₁
      + 2 * W.a₂ * W.a₄ * W.a₆ * z₁ * l ^ 3 * w₁ + 36 * W.a₆ ^ 2 * z₁ * l ^ 3 * w₁
      + 3 * W.a₂ * W.a₃ ^ 2 * w₁ ^ 2 - 6 * W.a₂ ^ 2 * W.a₄ * w₁ ^ 2
      - 3 * W.a₁ * W.a₃ * W.a₄ * w₁ ^ 2 - 3 * W.a₄ ^ 2 * w₁ ^ 2 + 9 * W.a₂ * W.a₆ * w₁ ^ 2
      + 3 * W.a₂ ^ 2 * W.a₃ ^ 2 * l * w₁ ^ 2 - 3 * W.a₁ * W.a₂ * W.a₃ * W.a₄ * l * w₁ ^ 2
      - 9 * W.a₂ * W.a₄ ^ 2 * l * w₁ ^ 2 + 3 * W.a₁ ^ 2 * W.a₂ * W.a₆ * l * w₁ ^ 2
      - 6 * W.a₂ ^ 2 * W.a₆ * l * w₁ ^ 2 - 9 * W.a₁ * W.a₃ * W.a₆ * l * w₁ ^ 2
      - 9 * W.a₄ * W.a₆ * l * w₁ ^ 2 + 3 * W.a₂ * W.a₃ ^ 2 * W.a₄ * l ^ 2 * w₁ ^ 2
      - 3 * W.a₁ * W.a₃ * W.a₄ ^ 2 * l ^ 2 * w₁ ^ 2 - 3 * W.a₄ ^ 3 * l ^ 2 * w₁ ^ 2
      - 9 * W.a₃ ^ 2 * W.a₆ * l ^ 2 * w₁ ^ 2 + 3 * W.a₁ ^ 2 * W.a₄ * W.a₆ * l ^ 2 * w₁ ^ 2
      - 6 * W.a₂ * W.a₄ * W.a₆ * l ^ 2 * w₁ ^ 2 - 27 * W.a₆ ^ 2 * l ^ 2 * w₁ ^ 2 - W.a₁ ^ 3 * z₂
      - W.a₁ * W.a₂ * z₂ - W.a₁ ^ 2 * W.a₂ * z₁ * z₂ - 7 * W.a₂ ^ 2 * z₁ * z₂
      + 3 * W.a₁ * W.a₃ * z₁ * z₂ + 3 * W.a₄ * z₁ * z₂ - 6 * W.a₁ * W.a₂ ^ 2 * l * z₂
      - 4 * W.a₁ ^ 2 * W.a₃ * l * z₂ - W.a₂ * W.a₃ * l * z₂ - 3 * W.a₁ * W.a₄ * l * z₂
      + 3 * W.a₃ ^ 2 * z₁ * l * z₂ - W.a₁ ^ 2 * W.a₄ * z₁ * l * z₂ - 7 * W.a₂ * W.a₄ * z₁ * l * z₂
      + 9 * W.a₆ * z₁ * l * z₂ - 6 * W.a₂ ^ 2 * W.a₃ * l ^ 2 * z₂
      - 6 * W.a₁ * W.a₃ ^ 2 * l ^ 2 * z₂ - 6 * W.a₁ * W.a₂ * W.a₄ * l ^ 2 * z₂
      - 3 * W.a₃ * W.a₄ * l ^ 2 * z₂ - 9 * W.a₁ * W.a₆ * l ^ 2 * z₂
      + 6 * W.a₂ ^ 2 * W.a₄ * z₁ * l ^ 2 * z₂ - W.a₁ * W.a₂ * W.a₃ ^ 2 * l ^ 3 * z₂
      - 3 * W.a₃ ^ 3 * l ^ 3 * z₂ + W.a₁ ^ 2 * W.a₃ * W.a₄ * l ^ 3 * z₂
      - 6 * W.a₂ * W.a₃ * W.a₄ * l ^ 3 * z₂ + W.a₁ * W.a₄ ^ 2 * l ^ 3 * z₂
      - W.a₁ ^ 3 * W.a₆ * l ^ 3 * z₂ - 4 * W.a₁ * W.a₂ * W.a₆ * l ^ 3 * z₂
      - 9 * W.a₃ * W.a₆ * l ^ 3 * z₂ - W.a₂ ^ 2 * W.a₃ ^ 2 * z₁ * l ^ 3 * z₂
      + W.a₁ * W.a₂ * W.a₃ * W.a₄ * z₁ * l ^ 3 * z₂ + 7 * W.a₂ * W.a₄ ^ 2 * z₁ * l ^ 3 * z₂
      - W.a₁ ^ 2 * W.a₂ * W.a₆ * z₁ * l ^ 3 * z₂ + 8 * W.a₂ ^ 2 * W.a₆ * z₁ * l ^ 3 * z₂
      + 3 * W.a₁ * W.a₃ * W.a₆ * z₁ * l ^ 3 * z₂ + 3 * W.a₄ * W.a₆ * z₁ * l ^ 3 * z₂
      - W.a₂ * W.a₃ ^ 3 * l ^ 4 * z₂ + W.a₁ * W.a₃ ^ 2 * W.a₄ * l ^ 4 * z₂
      + W.a₃ * W.a₄ ^ 2 * l ^ 4 * z₂ - W.a₁ ^ 2 * W.a₃ * W.a₆ * l ^ 4 * z₂
      - 4 * W.a₂ * W.a₃ * W.a₆ * l ^ 4 * z₂ - W.a₂ * W.a₃ ^ 2 * W.a₄ * z₁ * l ^ 4 * z₂
      + W.a₁ * W.a₃ * W.a₄ ^ 2 * z₁ * l ^ 4 * z₂ + W.a₄ ^ 3 * z₁ * l ^ 4 * z₂
      + 3 * W.a₃ ^ 2 * W.a₆ * z₁ * l ^ 4 * z₂ - W.a₁ ^ 2 * W.a₄ * W.a₆ * z₁ * l ^ 4 * z₂
      + 8 * W.a₂ * W.a₄ * W.a₆ * z₁ * l ^ 4 * z₂ + 9 * W.a₆ ^ 2 * z₁ * l ^ 4 * z₂
      - 6 * W.a₂ ^ 3 * w₁ * z₂ + 3 * W.a₃ ^ 2 * w₁ * z₂ - W.a₁ ^ 2 * W.a₄ * w₁ * z₂
      - W.a₂ * W.a₄ * w₁ * z₂ + 9 * W.a₆ * w₁ * z₂ + 6 * W.a₂ * W.a₃ ^ 2 * l * w₁ * z₂
      - 18 * W.a₂ ^ 2 * W.a₄ * l * w₁ * z₂ - 6 * W.a₁ * W.a₃ * W.a₄ * l * w₁ * z₂
      - 6 * W.a₄ ^ 2 * l * w₁ * z₂ + 18 * W.a₂ * W.a₆ * l * w₁ * z₂
      + 3 * W.a₂ ^ 2 * W.a₃ ^ 2 * l ^ 2 * w₁ * z₂
      - 3 * W.a₁ * W.a₂ * W.a₃ * W.a₄ * l ^ 2 * w₁ * z₂ - 15 * W.a₂ * W.a₄ ^ 2 * l ^ 2 * w₁ * z₂
      + 3 * W.a₁ ^ 2 * W.a₂ * W.a₆ * l ^ 2 * w₁ * z₂ - 6 * W.a₂ ^ 2 * W.a₆ * l ^ 2 * w₁ * z₂
      - 9 * W.a₁ * W.a₃ * W.a₆ * l ^ 2 * w₁ * z₂ - 9 * W.a₄ * W.a₆ * l ^ 2 * w₁ * z₂
      + 2 * W.a₂ * W.a₃ ^ 2 * W.a₄ * l ^ 3 * w₁ * z₂
      - 2 * W.a₁ * W.a₃ * W.a₄ ^ 2 * l ^ 3 * w₁ * z₂ - 2 * W.a₄ ^ 3 * l ^ 3 * w₁ * z₂
      - 6 * W.a₃ ^ 2 * W.a₆ * l ^ 3 * w₁ * z₂ + 2 * W.a₁ ^ 2 * W.a₄ * W.a₆ * l ^ 3 * w₁ * z₂
      - 10 * W.a₂ * W.a₄ * W.a₆ * l ^ 3 * w₁ * z₂ - 18 * W.a₆ ^ 2 * l ^ 3 * w₁ * z₂
      - 6 * W.a₂ ^ 2 * z₂ ^ 2 - 6 * W.a₂ ^ 3 * l * z₂ ^ 2 - 6 * W.a₂ * W.a₄ * l * z₂ ^ 2
      - 12 * W.a₂ ^ 2 * W.a₄ * l ^ 2 * z₂ ^ 2 - 6 * W.a₂ * W.a₄ ^ 2 * l ^ 3 * z₂ ^ 2
      - 6 * W.a₂ ^ 2 * W.a₆ * l ^ 3 * z₂ ^ 2 - 6 * W.a₂ * W.a₄ * W.a₆ * l ^ 4 * z₂ ^ 2) * h
    + (-W.a₁ + W.a₁ ^ 2 * z₁ + W.a₂ * z₁ - 3 * W.a₃ * z₁ ^ 2 - 6 * W.a₂ ^ 2 * z₁ ^ 3 - W.a₃ * l
      + 2 * W.a₄ * z₁ * l + W.a₁ ^ 2 * W.a₃ * z₁ ^ 2 * l - W.a₂ * W.a₃ * z₁ ^ 2 * l
      - W.a₁ * W.a₄ * z₁ ^ 2 * l - 3 * W.a₃ ^ 2 * z₁ ^ 3 * l + W.a₁ ^ 2 * W.a₄ * z₁ ^ 3 * l
      - 5 * W.a₂ * W.a₄ * z₁ ^ 3 * l - 9 * W.a₆ * z₁ ^ 3 * l - W.a₃ ^ 2 * z₁ * l ^ 2
      + 3 * W.a₆ * z₁ * l ^ 2 + W.a₁ * W.a₃ ^ 2 * z₁ ^ 2 * l ^ 2
      - 3 * W.a₁ * W.a₆ * z₁ ^ 2 * l ^ 2 - 2 * W.a₂ * W.a₃ ^ 2 * z₁ ^ 3 * l ^ 2
      + 2 * W.a₁ * W.a₃ * W.a₄ * z₁ ^ 3 * l ^ 2 + 2 * W.a₄ ^ 2 * z₁ ^ 3 * l ^ 2
      - 6 * W.a₂ * W.a₆ * z₁ ^ 3 * l ^ 2 + 6 * W.a₂ ^ 2 * w₁ + 3 * W.a₁ * W.a₃ * w₁ + W.a₄ * w₁
      - 6 * W.a₁ * W.a₂ ^ 2 * z₁ * w₁ - 2 * W.a₁ ^ 2 * W.a₃ * z₁ * w₁ - 3 * W.a₂ * W.a₃ * z₁ * w₁
      + W.a₁ * W.a₄ * z₁ * w₁ - 6 * W.a₂ ^ 3 * z₁ ^ 2 * w₁ + 3 * W.a₃ ^ 2 * z₁ ^ 2 * w₁
      - W.a₁ ^ 2 * W.a₄ * z₁ ^ 2 * w₁ - W.a₂ * W.a₄ * z₁ ^ 2 * w₁ + 9 * W.a₆ * z₁ ^ 2 * w₁
      + 4 * W.a₃ ^ 2 * l * w₁ + 6 * W.a₂ * W.a₄ * l * w₁ + 6 * W.a₆ * l * w₁
      - 2 * W.a₁ * W.a₃ ^ 2 * z₁ * l * w₁ - 6 * W.a₁ * W.a₂ * W.a₄ * z₁ * l * w₁
      - 4 * W.a₃ * W.a₄ * z₁ * l * w₁ - 2 * W.a₂ * W.a₃ ^ 2 * z₁ ^ 2 * l * w₁
      - 6 * W.a₂ ^ 2 * W.a₄ * z₁ ^ 2 * l * w₁ + 2 * W.a₁ * W.a₃ * W.a₄ * z₁ ^ 2 * l * w₁
      + 2 * W.a₄ ^ 2 * z₁ ^ 2 * l * w₁ - 6 * W.a₂ * W.a₆ * z₁ ^ 2 * l * w₁
      + W.a₂ * W.a₃ ^ 2 * l ^ 2 * w₁ - W.a₁ * W.a₃ * W.a₄ * l ^ 2 * w₁ - W.a₄ ^ 2 * l ^ 2 * w₁
      + W.a₁ ^ 2 * W.a₆ * l ^ 2 * w₁ + 4 * W.a₂ * W.a₆ * l ^ 2 * w₁
      - W.a₁ * W.a₂ * W.a₃ ^ 2 * z₁ * l ^ 2 * w₁ + W.a₃ ^ 3 * z₁ * l ^ 2 * w₁
      + W.a₁ ^ 2 * W.a₃ * W.a₄ * z₁ * l ^ 2 * w₁ + W.a₁ * W.a₄ ^ 2 * z₁ * l ^ 2 * w₁
      - W.a₁ ^ 3 * W.a₆ * z₁ * l ^ 2 * w₁ - 4 * W.a₁ * W.a₂ * W.a₆ * z₁ * l ^ 2 * w₁
      - 3 * W.a₃ * W.a₆ * z₁ * l ^ 2 * w₁ - 2 * W.a₂ ^ 2 * W.a₃ ^ 2 * z₁ ^ 2 * l ^ 2 * w₁
      + 2 * W.a₁ * W.a₂ * W.a₃ * W.a₄ * z₁ ^ 2 * l ^ 2 * w₁
      + 2 * W.a₂ * W.a₄ ^ 2 * z₁ ^ 2 * l ^ 2 * w₁
      - 2 * W.a₁ ^ 2 * W.a₂ * W.a₆ * z₁ ^ 2 * l ^ 2 * w₁
      - 8 * W.a₂ ^ 2 * W.a₆ * z₁ ^ 2 * l ^ 2 * w₁ + 6 * W.a₁ * W.a₃ * W.a₆ * z₁ ^ 2 * l ^ 2 * w₁
      + 6 * W.a₄ * W.a₆ * z₁ ^ 2 * l ^ 2 * w₁ - 6 * W.a₂ ^ 2 * W.a₃ * w₁ ^ 2
      - 2 * W.a₁ * W.a₃ ^ 2 * w₁ ^ 2 - 2 * W.a₃ * W.a₄ * w₁ ^ 2 + 3 * W.a₁ * W.a₆ * w₁ ^ 2
      + 4 * W.a₂ * W.a₃ ^ 2 * z₁ * w₁ ^ 2 - 6 * W.a₂ ^ 2 * W.a₄ * z₁ * w₁ ^ 2
      - 4 * W.a₁ * W.a₃ * W.a₄ * z₁ * w₁ ^ 2 - 4 * W.a₄ ^ 2 * z₁ * w₁ ^ 2
      + 12 * W.a₂ * W.a₆ * z₁ * w₁ ^ 2 + W.a₁ * W.a₂ * W.a₃ ^ 2 * l * w₁ ^ 2
      - 4 * W.a₃ ^ 3 * l * w₁ ^ 2 - W.a₁ ^ 2 * W.a₃ * W.a₄ * l * w₁ ^ 2
      - 6 * W.a₂ * W.a₃ * W.a₄ * l * w₁ ^ 2 - W.a₁ * W.a₄ ^ 2 * l * w₁ ^ 2
      + W.a₁ ^ 3 * W.a₆ * l * w₁ ^ 2 + 4 * W.a₁ * W.a₂ * W.a₆ * l * w₁ ^ 2
      - 9 * W.a₃ * W.a₆ * l * w₁ ^ 2 + W.a₂ ^ 2 * W.a₃ ^ 2 * z₁ * l * w₁ ^ 2
      - W.a₁ * W.a₂ * W.a₃ * W.a₄ * z₁ * l * w₁ ^ 2 - 7 * W.a₂ * W.a₄ ^ 2 * z₁ * l * w₁ ^ 2
      + W.a₁ ^ 2 * W.a₂ * W.a₆ * z₁ * l * w₁ ^ 2 + 4 * W.a₂ ^ 2 * W.a₆ * z₁ * l * w₁ ^ 2
      - 3 * W.a₁ * W.a₃ * W.a₆ * z₁ * l * w₁ ^ 2 - 3 * W.a₄ * W.a₆ * z₁ * l * w₁ ^ 2
      - W.a₂ * W.a₃ ^ 3 * l ^ 2 * w₁ ^ 2 + W.a₁ * W.a₃ ^ 2 * W.a₄ * l ^ 2 * w₁ ^ 2
      + W.a₃ * W.a₄ ^ 2 * l ^ 2 * w₁ ^ 2 - W.a₁ ^ 2 * W.a₃ * W.a₆ * l ^ 2 * w₁ ^ 2
      - 4 * W.a₂ * W.a₃ * W.a₆ * l ^ 2 * w₁ ^ 2 - 2 * W.a₂ * W.a₃ ^ 2 * W.a₄ * z₁ * l ^ 2 * w₁ ^ 2
      + 2 * W.a₁ * W.a₃ * W.a₄ ^ 2 * z₁ * l ^ 2 * w₁ ^ 2 + 2 * W.a₄ ^ 3 * z₁ * l ^ 2 * w₁ ^ 2
      + 6 * W.a₃ ^ 2 * W.a₆ * z₁ * l ^ 2 * w₁ ^ 2
      - 2 * W.a₁ ^ 2 * W.a₄ * W.a₆ * z₁ * l ^ 2 * w₁ ^ 2
      - 8 * W.a₂ * W.a₄ * W.a₆ * z₁ * l ^ 2 * w₁ ^ 2 + 18 * W.a₆ ^ 2 * z₁ * l ^ 2 * w₁ ^ 2
      + W.a₂ ^ 2 * W.a₃ ^ 2 * w₁ ^ 3 - W.a₁ * W.a₂ * W.a₃ * W.a₄ * w₁ ^ 3
      - W.a₂ * W.a₄ ^ 2 * w₁ ^ 3 + W.a₁ ^ 2 * W.a₂ * W.a₆ * w₁ ^ 3 - 2 * W.a₂ ^ 2 * W.a₆ * w₁ ^ 3
      - 3 * W.a₁ * W.a₃ * W.a₆ * w₁ ^ 3 - 3 * W.a₄ * W.a₆ * w₁ ^ 3
      + 2 * W.a₂ * W.a₃ ^ 2 * W.a₄ * l * w₁ ^ 3 - 2 * W.a₁ * W.a₃ * W.a₄ ^ 2 * l * w₁ ^ 3
      - 2 * W.a₄ ^ 3 * l * w₁ ^ 3 - 6 * W.a₃ ^ 2 * W.a₆ * l * w₁ ^ 3
      + 2 * W.a₁ ^ 2 * W.a₄ * W.a₆ * l * w₁ ^ 3 + 2 * W.a₂ * W.a₄ * W.a₆ * l * w₁ ^ 3
      - 18 * W.a₆ ^ 2 * l * w₁ ^ 3 + W.a₁ ^ 2 * z₂ - W.a₁ ^ 3 * z₁ * z₂
      - W.a₁ ^ 2 * W.a₂ * z₁ ^ 2 * z₂ - W.a₂ ^ 2 * z₁ ^ 2 * z₂ + 3 * W.a₁ * W.a₃ * z₁ ^ 2 * z₂
      + 3 * W.a₄ * z₁ ^ 2 * z₂ + 2 * W.a₁ * W.a₃ * l * z₂ - 2 * W.a₁ ^ 2 * W.a₃ * z₁ * l * z₂
      + 3 * W.a₃ ^ 2 * z₁ ^ 2 * l * z₂ - W.a₁ ^ 2 * W.a₄ * z₁ ^ 2 * l * z₂
      - W.a₂ * W.a₄ * z₁ ^ 2 * l * z₂ + 9 * W.a₆ * z₁ ^ 2 * l * z₂ + W.a₃ ^ 2 * l ^ 2 * z₂
      - W.a₁ * W.a₃ ^ 2 * z₁ * l ^ 2 * z₂ + W.a₂ * W.a₃ ^ 2 * z₁ ^ 2 * l ^ 2 * z₂
      - W.a₁ * W.a₃ * W.a₄ * z₁ ^ 2 * l ^ 2 * z₂ - W.a₄ ^ 2 * z₁ ^ 2 * l ^ 2 * z₂
      + 3 * W.a₂ * W.a₆ * z₁ ^ 2 * l ^ 2 * z₂ - W.a₁ ^ 2 * W.a₃ * w₁ * z₂
      + 3 * W.a₃ ^ 2 * z₁ * w₁ * z₂ - W.a₁ ^ 2 * W.a₄ * z₁ * w₁ * z₂ - W.a₂ * W.a₄ * z₁ * w₁ * z₂
      + 9 * W.a₆ * z₁ * w₁ * z₂ - 2 * W.a₁ * W.a₃ ^ 2 * l * w₁ * z₂
      + 4 * W.a₂ * W.a₃ ^ 2 * z₁ * l * w₁ * z₂ - 4 * W.a₁ * W.a₃ * W.a₄ * z₁ * l * w₁ * z₂
      - 4 * W.a₄ ^ 2 * z₁ * l * w₁ * z₂ + 12 * W.a₂ * W.a₆ * z₁ * l * w₁ * z₂
      - W.a₃ ^ 3 * l ^ 2 * w₁ * z₂ + W.a₂ ^ 2 * W.a₃ ^ 2 * z₁ * l ^ 2 * w₁ * z₂
      - W.a₁ * W.a₂ * W.a₃ * W.a₄ * z₁ * l ^ 2 * w₁ * z₂ - W.a₂ * W.a₄ ^ 2 * z₁ * l ^ 2 * w₁ * z₂
      + W.a₁ ^ 2 * W.a₂ * W.a₆ * z₁ * l ^ 2 * w₁ * z₂ + 4 * W.a₂ ^ 2 * W.a₆ * z₁ * l ^ 2 * w₁ * z₂
      - 3 * W.a₁ * W.a₃ * W.a₆ * z₁ * l ^ 2 * w₁ * z₂ - 3 * W.a₄ * W.a₆ * z₁ * l ^ 2 * w₁ * z₂
      + W.a₂ * W.a₃ ^ 2 * w₁ ^ 2 * z₂ - W.a₁ * W.a₃ * W.a₄ * w₁ ^ 2 * z₂ - W.a₄ ^ 2 * w₁ ^ 2 * z₂
      + 3 * W.a₂ * W.a₆ * w₁ ^ 2 * z₂ + W.a₂ ^ 2 * W.a₃ ^ 2 * l * w₁ ^ 2 * z₂
      - W.a₁ * W.a₂ * W.a₃ * W.a₄ * l * w₁ ^ 2 * z₂ - W.a₂ * W.a₄ ^ 2 * l * w₁ ^ 2 * z₂
      + W.a₁ ^ 2 * W.a₂ * W.a₆ * l * w₁ ^ 2 * z₂ + 4 * W.a₂ ^ 2 * W.a₆ * l * w₁ ^ 2 * z₂
      - 3 * W.a₁ * W.a₃ * W.a₆ * l * w₁ ^ 2 * z₂ - 3 * W.a₄ * W.a₆ * l * w₁ ^ 2 * z₂
      + W.a₂ * W.a₃ ^ 2 * W.a₄ * l ^ 2 * w₁ ^ 2 * z₂
      - W.a₁ * W.a₃ * W.a₄ ^ 2 * l ^ 2 * w₁ ^ 2 * z₂ - W.a₄ ^ 3 * l ^ 2 * w₁ ^ 2 * z₂
      - 3 * W.a₃ ^ 2 * W.a₆ * l ^ 2 * w₁ ^ 2 * z₂ + W.a₁ ^ 2 * W.a₄ * W.a₆ * l ^ 2 * w₁ ^ 2 * z₂
      + 4 * W.a₂ * W.a₄ * W.a₆ * l ^ 2 * w₁ ^ 2 * z₂ - 9 * W.a₆ ^ 2 * l ^ 2 * w₁ ^ 2 * z₂) * hl

end GlobalTheory.AddLaw
end

section
open WeierstrassCurve WeierstrassCurve.Projective

namespace GlobalTheory.AddLaw

section Ring

variable {R S : Type*} [CommRing R] [CommRing S]

def Proportional (T U : Fin 3 → R) : Prop :=
  ∀ i j, T i * U j = T j * U i

lemma Proportional.symm {T U : Fin 3 → R} (h : Proportional T U) : Proportional U T :=
  fun i j => by linear_combination h j i

lemma Proportional.smul_left {T U : Fin 3 → R} (h : Proportional T U) (u : R) :
    Proportional (u • T) U :=
  fun i j => by simp only [Pi.smul_apply, smul_eq_mul]; linear_combination u * h i j

lemma proportional_negY (W : Projective R) {X N Z X' N' Z' : R} (hxz : X * Z' = Z * X')
    (hnz : N * Z' = Z * N') (hxn : X * N' = N * X') :
    Proportional ![X, W.negY ![X, N, Z], Z] ![X', W.negY ![X', N', Z'], Z'] := by
  have hxy : X * W.negY ![X', N', Z'] = W.negY ![X, N, Z] * X' := by
    simp only [negY_eq]; linear_combination -hxn - W.a₃ * hxz
  have hyz : W.negY ![X, N, Z] * Z' = Z * W.negY ![X', N', Z'] := by
    simp only [negY_eq]; linear_combination -hnz - W.a₁ * hxz
  intro i j
  fin_cases i <;> fin_cases j
  exacts [rfl, hxy, hxz, hxy.symm, rfl, hyz, hxz.symm, hyz.symm, rfl]

variable {W : Projective R}

lemma diagXYZ_X (P Q : Fin 3 → R) : diagXYZ W P Q 0 = diagX W P Q := rfl

lemma diagXYZ_Y (P Q : Fin 3 → R) : diagXYZ W P Q 1 = diagY W P Q := rfl

lemma diagXYZ_Z (P Q : Fin 3 → R) : diagXYZ W P Q 2 = diagZ W P Q := rfl

lemma diagXYZ_self {P : Fin 3 → R} (hP : W.Equation P) : diagXYZ W P P = W.dblXYZ P := by
  rw [diagXYZ, diagY, diagX_self hP, negDiagY_self hP, diagZ_self hP, dblXYZ, dblY]

lemma diagY_smul (P Q : Fin 3 → R) (u v : R) :
    diagY W (u • P) (v • Q) = (u * v) ^ 2 * diagY W P Q := by
  simp only [diagY, negY_eq, diagX_smul, negDiagY_smul, diagZ_smul]
  ring1

lemma diagXYZ_smul (P Q : Fin 3 → R) (u v : R) :
    diagXYZ W (u • P) (v • Q) = (u * v) ^ 2 • diagXYZ W P Q := by
  rw [diagXYZ, diagX_smul, diagY_smul, diagZ_smul, smul_fin3, diagXYZ_X, diagXYZ_Y, diagXYZ_Z]

lemma map_diagY (f : R →+* S) (P Q : Fin 3 → R) :
    diagY (W.map f) (f ∘ P) (f ∘ Q) = f (diagY W P Q) := by
  simp only [diagY, negY_eq, map_diagX, map_negDiagY, map_diagZ]
  simp only [map_neg, map_sub, map_mul, WeierstrassCurve.map]

lemma map_diagXYZ (f : R →+* S) (P Q : Fin 3 → R) :
    diagXYZ (W.map f) (f ∘ P) (f ∘ Q) = f ∘ diagXYZ W P Q := by
  simp only [diagXYZ, map_diagX, map_diagY, map_diagZ, comp_fin3]

lemma proportional_diagXYZ_addXYZ {P Q : Fin 3 → R} (hP : W.Equation P) (hQ : W.Equation Q) :
    Proportional (diagXYZ W P Q) (W.addXYZ P Q) :=
  proportional_negY W (diagX_mul_addZ hP hQ) (negDiagY_mul_addZ hP hQ) (diagX_mul_negAddY hP hQ)

variable (W) in

def chordN (x₁ y₁ x₂ : R) : R :=
  x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁

variable (W) in

def chordD (y₁ x₂ y₂ : R) : R :=
  y₁ + y₂ + W.a₁ * x₂ + W.a₃

variable (W) in

def slopeXYZ (x₁ y₁ x₂ n d : R) : Fin 3 → R :=
  W.neg ![d * (n ^ 2 + W.a₁ * n * d - (W.a₂ + x₁ + x₂) * d ^ 2),
    n * (n ^ 2 + W.a₁ * n * d - (W.a₂ + x₁ + x₂) * d ^ 2 - x₁ * d ^ 2) + y₁ * d ^ 3, d ^ 3]

variable (W) in

def chordXYZ (x₁ y₁ x₂ y₂ : R) : Fin 3 → R :=
  slopeXYZ W x₁ y₁ x₂ (chordN W x₁ y₁ x₂) (chordD W y₁ x₂ y₂)

variable (W) in

def thirdXYZ (s n v d : R) : Fin 3 → R :=
  ![d * (-lineQuadCoeff W n v d - lineCubicCoeff W n d * s), -(d * lineCubicCoeff W n d),
    n * (-lineQuadCoeff W n v d - lineCubicCoeff W n d * s) + v * lineCubicCoeff W n d]

variable (W) in

def originXYZ (z₁ w₁ z₂ w₂ : R) : Fin 3 → R :=
  W.neg (thirdXYZ W (z₁ + z₂) (originN W z₁ w₁ z₂)
    (w₁ * originD W w₁ z₂ w₂ - originN W z₁ w₁ z₂ * z₁) (originD W w₁ z₂ w₂))

end Ring

section Field

variable {F : Type*} [Field F] {W : Projective F}

lemma ne_zero_of_nonsingular {P : Fin 3 → F} (hP : W.Nonsingular P) : P ≠ 0 := by
  rintro rfl
  exact Y_ne_zero_of_Z_eq_zero hP rfl rfl

lemma nonsingular_iff_of_Δ_ne_zero (hΔ : W.Δ ≠ 0) (P : Fin 3 → F) :
    W.Nonsingular P ↔ W.Equation P ∧ P ≠ 0 := by
  refine ⟨fun h => ⟨h.left, ne_zero_of_nonsingular h⟩, fun ⟨h, h0⟩ => ?_⟩
  by_cases hz : P 2 = 0
  · have hx := X_eq_zero_of_Z_eq_zero h hz
    have hy : P 1 ≠ 0 := fun hy => h0 <| by
      ext i; fin_cases i
      exacts [hx, hy, hz]
    refine (nonsingular_of_Z_eq_zero hz).mpr ⟨h, Or.inr ?_⟩
    simpa [hx] using hy
  · exact (nonsingular_of_Z_ne_zero hz).mpr <|
      (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp <| (equation_of_Z_ne_zero hz).mp h

lemma equiv_of_proportional {T U : Fin 3 → F} (h : Proportional T U) (hT : T ≠ 0) (hU : U ≠ 0) :
    T ≈ U := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hU
  replace hj : U j ≠ 0 := hj
  have e : (T j / U j) • U = T := by
    ext i
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, div_eq_iff hj, h i j]
  have hu : T j / U j ≠ 0 := fun h0 => hT <| by rw [← e, h0, zero_smul]
  exact ⟨Units.mk0 _ hu, e⟩

variable (W) in

def Represents (T : Fin 3 → F) (p : W.toAffine.Point) : Prop :=
  W.Nonsingular T ∧ Point.toAffine W T = p

lemma Represents.ne_zero {T : Fin 3 → F} {p : W.toAffine.Point} (h : Represents W T p) : T ≠ 0 :=
  ne_zero_of_nonsingular h.left

lemma Represents.of_equiv {T U : Fin 3 → F} {p : W.toAffine.Point} (h : Represents W U p)
    (e : T ≈ U) : Represents W T p :=
  ⟨(nonsingular_of_equiv e).mpr h.left, (Point.toAffine_of_equiv e).trans h.right⟩

lemma Represents.equiv {T U : Fin 3 → F} {p : W.toAffine.Point} (hT : Represents W T p)
    (hU : Represents W U p) : T ≈ U := by
  classical
  have h : (⟨(nonsingularLift_iff T).mpr hT.left⟩ : W.Point) =
      ⟨(nonsingularLift_iff U).mpr hU.left⟩ :=
    (Point.toAffineAddEquiv W).injective (hT.right.trans hU.right.symm)
  exact Quotient.exact (congrArg Point.point h)

lemma addXYZ_ne_zero_iff {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    W.addXYZ P Q ≠ 0 ↔ ¬P ≈ Q := by
  refine ⟨fun h ⟨u, e⟩ => h ?_, fun h => ?_⟩
  · have := addXYZ_smul (W' := W) Q Q u 1
    rw [one_smul, addXYZ_self] at this
    rw [← show (u : F) • Q = P from e, this]
    ext i
    fin_cases i <;> simp
  · rw [← add_of_not_equiv h]
    exact ne_zero_of_nonsingular <| nonsingular_add hP hQ

lemma diagXYZ_equiv_add_of_equiv {P Q : Fin 3 → F} (hP : W.Equation P) (h : P ≈ Q) :
    diagXYZ W P Q ≈ W.add P Q := by
  rw [add_of_equiv h, ← diagXYZ_self hP]
  obtain ⟨u, e⟩ := Setoid.symm h
  have := diagXYZ_smul (W := W) P P 1 u
  rw [one_smul, one_mul] at this
  rw [← show (u : F) • P = Q from e, this]
  exact smul_equiv _ (u.isUnit.pow 2)

lemma diagXYZ_ne_zero_of_equiv {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (h : P ≈ Q) : diagXYZ W P Q ≠ 0 :=
  ne_zero_of_nonsingular <| (nonsingular_of_equiv <| diagXYZ_equiv_add_of_equiv hP.left h).mpr <|
    nonsingular_add hP hQ

theorem addXYZ_ne_zero_or_diagXYZ_ne_zero {P Q : Fin 3 → F} (hP : W.Nonsingular P)
    (hQ : W.Nonsingular Q) : W.addXYZ P Q ≠ 0 ∨ diagXYZ W P Q ≠ 0 := by
  by_cases h : P ≈ Q
  · exact Or.inr <| diagXYZ_ne_zero_of_equiv hP hQ h
  · exact Or.inl <| (addXYZ_ne_zero_iff hP hQ).mpr h

lemma addXYZ_equiv_add {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (h : W.addXYZ P Q ≠ 0) : W.addXYZ P Q ≈ W.add P Q := by
  rw [add_of_not_equiv <| (addXYZ_ne_zero_iff hP hQ).mp h]

lemma diagXYZ_equiv_add {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (h : diagXYZ W P Q ≠ 0) : diagXYZ W P Q ≈ W.add P Q := by
  by_cases e : P ≈ Q
  · exact diagXYZ_equiv_add_of_equiv hP.left e
  · rw [add_of_not_equiv e]
    exact equiv_of_proportional (proportional_diagXYZ_addXYZ hP.left hQ.left) h <|
      (addXYZ_ne_zero_iff hP hQ).mpr e

lemma equiv_add_of_proportional {P Q T : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (h₁ : Proportional T (W.addXYZ P Q)) (h₂ : Proportional T (diagXYZ W P Q)) (hT : T ≠ 0) :
    T ≈ W.add P Q := by
  rcases addXYZ_ne_zero_or_diagXYZ_ne_zero hP hQ with h | h
  · exact Setoid.trans (equiv_of_proportional h₁ hT h) (addXYZ_equiv_add hP hQ h)
  · exact Setoid.trans (equiv_of_proportional h₂ hT h) (diagXYZ_equiv_add hP hQ h)

variable [DecidableEq F]

end Field

end GlobalTheory.AddLaw
end
