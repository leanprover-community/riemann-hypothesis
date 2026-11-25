module

public import Development.WeilBound.CoreStatements.ThetaDilations.IsOpenCoset
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopology
import CompanionTheory.AutomorphicTheory.ThetaDilations.OrbitAdelic

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]

theorem oh_nat (N : ℕ) : (N : A F) ∈ Oh F := by
  induction N with
  | zero => exact fun v => by rw [Nat.cast_zero]; exact zero_mem _
  | succ n ih => exact fun v => by rw [Nat.cast_succ]; exact add_mem (ih v) (one_mem _)

end PositivityTheory.PlacePermOperatorBicommutantSpan
