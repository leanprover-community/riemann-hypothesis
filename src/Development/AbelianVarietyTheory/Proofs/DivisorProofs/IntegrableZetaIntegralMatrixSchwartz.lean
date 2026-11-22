module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableDetPowIndicatorIntegerGl

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

noncomputable section
namespace GlobalTheory.GJIntegrable

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end GlobalTheory.GJIntegrable
