module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableZetaIntegralMatrixSchwartz

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

noncomputable section
namespace GlobalTheory.GJForm

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

end GlobalTheory.GJForm
