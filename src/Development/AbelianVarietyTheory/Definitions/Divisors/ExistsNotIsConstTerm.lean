module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonarchimedeanGroupOfIsCompactIsOpen

@[expose] public section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ContDiff

namespace GlobalTheory.UAut.Model

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

end GlobalTheory.UAut.Model

end
