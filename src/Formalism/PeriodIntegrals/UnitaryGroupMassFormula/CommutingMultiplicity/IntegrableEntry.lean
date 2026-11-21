import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CommutingMultiplicity.SchurStep

noncomputable section

namespace PI.UnitaryGroupMassFormula.CommMult

open MeasureTheory Matrix

section Integral

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [MeasurableSpace H] [BorelSpace H]

def mInt (μ : Measure H) {m n : Type} (F : H → Matrix m n ℂ) : Matrix m n ℂ :=
  Matrix.of fun i j => ∫ h, F h i j ∂μ






end Integral


end PI.UnitaryGroupMassFormula.CommMult
