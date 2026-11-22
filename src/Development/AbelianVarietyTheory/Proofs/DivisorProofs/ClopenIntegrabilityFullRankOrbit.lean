module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal

@[expose] public section

noncomputable section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.FullRankCoinv.Reduce

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end

end GlobalTheory.FullRankCoinv.Reduce
