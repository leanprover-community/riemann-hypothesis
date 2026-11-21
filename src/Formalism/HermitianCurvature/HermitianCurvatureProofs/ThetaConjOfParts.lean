import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialAdjointOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothWordsAll

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def CptInCC : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : B.Mat k r → E) (C : Set (B.Mat k r)),
    B.CkOn ⊤ (B.GV k r) F → IsCompact C → (∀ g, g ∉ C → F g = 0) → ∀ (A : ℝ) (m : ℕ), B.InCC A m F

def JThetaAdjC : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    B.SmoothCoef (Om k r D.z D.z') Θ → B.Commutes D (Om k r D.z D.z') Θ → B.CkOn ⊤ (B.GV k r) F →
    (∃ C : Set (B.Mat k r), IsCompact C ∧ C ⊆ Om k r D.z D.z' ∧ ∀ g, g ∉ C → F g = 0) →
    ∀ g ∈ Om k r D.z D.z', B.JF D (B.opAdj Θ F) g = B.opAdj Θ (B.JF D F) g

def JThetaCOfParts : Prop := JDom → CptInCC → JThetaAdjC → JThetaC

theorem thr_big (k r m : ℕ) :
    TransportedAlt k r (9 * ((r : ℝ) + 1) * ((((2 * r + k + 1 : ℕ) : ℝ)) ^ 2 + 1) + 6 * (r : ℝ) * (m : ℝ)) m := by
  unfold TransportedAlt
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [Nat.cast_nonneg (α := ℝ) r, sq_nonneg (((2 * r + k + 1 : ℕ) : ℝ))]

end Formalism.FourierDecayAlt.P.JFxG

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


end Formalism.FourierDecayAlt.P
