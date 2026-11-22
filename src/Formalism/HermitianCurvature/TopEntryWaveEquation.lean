module

public import Formalism.HermitianCurvature.TopDensNonnegOfKappa
public import Formalism.HermitianCurvature.ActualZetaSmooth

@[expose] public section

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

def TopTwistDensOfZeta : Prop :=
  NF.ActualZetaSmooth →
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')),
    IsData P z z' π π' X μ L st l0 → TopTwistDens S P z z' π π' L st l0 K

end Formalism.FourierDecayAlt.P5
