module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal

@[expose] public section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

noncomputable section

namespace GlobalTheory.FullRankCoinv.UnitMinor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end GlobalTheory.FullRankCoinv.UnitMinor
