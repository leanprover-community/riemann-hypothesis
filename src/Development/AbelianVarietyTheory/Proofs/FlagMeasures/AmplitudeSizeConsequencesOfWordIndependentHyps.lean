module

import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AbsOfRange
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Mathlib.Algebra.Order.Star.Real

@[expose] public section

noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.SizesProof

theorem sizes_of_hyp : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), D.host.rdE ≤ large₂.sc.b →
    HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → Sizes D large₂ Cl Cg CT := by
  apply GlobalTheory.Amp.RangeModel.sizes_of

end GlobalTheory.Amp.SizesProof
