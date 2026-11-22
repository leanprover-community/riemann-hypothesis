module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel MeasureTheory

namespace GlobalTheory.UnitaryDual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsSquareIntegrable (δ : IrrGL (k := k)) : Prop :=
  0 < δ.1 ∧ IsUnitarisable δ.rep ∧
    letI : MeasurableSpace (GL (Fin δ.1) k ⧸ Subgroup.center (GL (Fin δ.1) k)) := borel _
    ∃ μ : Measure (GL (Fin δ.1) k ⧸ Subgroup.center (GL (Fin δ.1) k)), μ.IsHaarMeasure ∧
      ∀ v, ∀ ℓ ∈ smoothPart δ.rep.dual, ∫⁻ q, ‖ℓ (δ.rep q.out v)‖ₑ ^ 2 ∂μ < ⊤

end GlobalTheory.UnitaryDual

namespace GlobalTheory.Published

open GlobalTheory.UnitaryDual

end GlobalTheory.Published

end
