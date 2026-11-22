module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic

@[expose] public section

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.GenericShape

theorem superSum_one {F : Type} [Field F] {κ : ℕ} : superSum Fin.val (1 : Matrix (Fin κ) (Fin κ) F) = 0 := by
  refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun s _ => ?_
  split_ifs with e
  · rw [Matrix.one_apply_ne]; rintro rfl; omega
  · rfl

end GlobalTheory.GenericShape
