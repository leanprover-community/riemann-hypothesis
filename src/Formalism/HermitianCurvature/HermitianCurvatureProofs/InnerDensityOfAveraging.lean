import Formalism.HermitianCurvature.LemmaDensOfSteps

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6



def averagingDatumInhabited {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) : Formalism.FourierDecayAlt.DensityAveraging.AvgDatum D F' γ where
  V := ℂ
  p := normSeminorm ℂ ℂ
  β := 1
  β_ne := one_ne_zero
  s := 1
  w := fun _ => 0
  w_inj := fun i j _ => Subsingleton.elim i j
  a := fun _ => 1
  k₀ := 0
  tie := fun h => absurd h (by simp)

end Formalism.FourierDecayAlt.P
