import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDomainMeasurable

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxDs5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k : ℕ}



lemma hb_eq : Hb k = castW (Hpk k 0) := by
  ext i j
  simp only [castW, Matrix.reindex_apply, Matrix.submatrix_apply, Hb, Matrix.diagonal_apply, Hpk]
  by_cases hij : i = j
  · subst hij
    by_cases hl : i = Fin.last k
    · subst hl
      simp [Fin.last]
    · have hv : (i : ℕ) ≠ k := fun h => hl (Fin.ext (by simpa [Fin.last] using h))
      have hlt : (i : ℕ) < k + 1 := i.isLt
      simp [hl, hv]
      omega
  · have hv : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    simp [hij, Fin.ext_iff, hv]


def NNSlice : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ),
    TransportedAlt k r A m → ∀ c : Fin r → ℂ, (∀ a, c a ≠ 0) → ∀ μ ∈ B.GV k 0,
      Integrable (fun nn : Mt k r × Mt k r =>
        B.gN ((Matrix.of nn.1)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2) ^ (-A)) (D.μN.prod D.μN)

def Slice1 : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    ∀ c : Fin r → ℂ, (∀ a, c a ≠ 0) → ∀ μ ∈ B.GV k 0,
      Integrable (fun nn : Mt k r × Mt k r =>
        F ((Matrix.of nn.1)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2)) (D.μN.prod D.μN)

def SliceRegularityClauses : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    (∀ c : Fin r → ℂ, (∀ a, c a ≠ 0) →
      B.InCC (k := k) (r := 0) ((A - 6 * (r : ℝ) * (m : ℝ)) / (9 * ((r : ℝ) + 1))) m (sliceR D F c)) ∧
    ∀ (d : ℕ) (O : Set (Fin d → ℝ)) (cx : (Fin d → ℝ) → Fin r → ℂ) (μx : (Fin d → ℝ) → B.Mat k 0),
      IsOpen O → ContDiffOn ℝ ∞ cx O → ContDiffOn ℝ ∞ μx O → (∀ x ∈ O, (∀ a, cx x a ≠ 0) ∧ μx x ∈ B.GV k 0) →
      ContDiffOn ℝ (m : WithTop ℕ∞) (fun x => sliceR D F (cx x) (μx x)) O




end Formalism.FourierDecayAlt.P.JFxDs5
