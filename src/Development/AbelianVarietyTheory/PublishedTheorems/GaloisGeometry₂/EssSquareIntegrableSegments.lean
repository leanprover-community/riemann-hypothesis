import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedCoeff

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

namespace GlobalTheory.Published

def EssSquareIntegrableSegments : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (δ : IrrGL k), 1 ≤ δ.1 →
    ((∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), IsSqIntCoeff (δ.tw χ hχ).rep) ↔ ∃ Δ : Segment k, IsLSeg Δ δ.rep)

namespace EssSquareIntegrableSegments

open MeasureTheory

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem subsingleton_adGL_one : Subsingleton (AdGL k 1) := by
  refine QuotientGroup.subsingleton_iff.2 (eq_top_iff.2 fun g _ => Subgroup.mem_center_iff.2 fun h => ?_)
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  simp [Matrix.mul_apply, mul_comm]



end EssSquareIntegrableSegments

end GlobalTheory.Published
