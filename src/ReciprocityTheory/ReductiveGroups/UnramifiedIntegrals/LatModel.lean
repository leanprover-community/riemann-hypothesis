import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.CoeffOneSubstOfConstantCoeffEqZero
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.BridgeTwoMore
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.AdditionAdditionRing
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveJetsUnitBall
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.FinalA

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

theorem lgS_eq_logSer {K : Type} [Field K] [CharZero K] (g2 g3 : K) :
    lgS g2 g3 = Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2 g3) := by
  obtain ⟨h0, -, -, -⟩ := Formalism.L2.Th1.A.logSpec K (Formalism.L2.Th1.A.shortW g2 g3)
  obtain ⟨-, -, -, h4, -⟩ := Formalism.L2.Th1.A.expSpec K (Formalism.L2.Th1.A.shortW g2 g3)
  refine (lgS_unique g2 g3 _ h0 ?_).symm
  rw [Formalism.L2.Th1.A.uSerEq K g2 g3]
  exact h4

theorem shortW_intModel {K : Type} [NormedField K] (g2 g3 : K)
    (h2 : ‖g2‖ ≤ 1) (h3 : ‖g3‖ ≤ 1) (h : ‖(2 : K)‖ = 1) :
    Formalism.L2.Th1.A.IntModel (Formalism.L2.Th1.A.shortW g2 g3) := by
  have h4 : ‖(4 : K)‖ = 1 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this, norm_mul, h, one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Formalism.L2.Th1.A.shortW, h4, h2, h3]

theorem curve_law {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 : K)
    (h2 : ‖g2‖ ≤ 1) (h3 : ‖g3‖ ≤ 1) (h : ‖(2 : K)‖ = 1) :
    LawD (lgS g2 g3) (Formalism.L2.Th1.A.fgl (Formalism.L2.Th1.A.shortW g2 g3)) := by
  rw [lgS_eq_logSer]
  obtain ⟨⟨hF0, hFi, hl0, hl1, -⟩, -, -⟩ :=
    Formalism.L2.Th1.A.bridgeLaw K (Formalism.L2.Th1.A.shortW g2 g3) (shortW_intModel g2 g3 h2 h3 h)
  exact ⟨hl0, hl1, hF0, hFi, (Formalism.L2.Th1.A.fglLog K (Formalism.L2.Th1.A.shortW g2 g3)).1⟩

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

structure LatModel (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (g2 g3 : ℂ_[l]) :
    Prop where
  eq2 : g2 = ι L.g₂
  eq3 : g3 = ι L.g₃
  n2 : ‖g2‖ ≤ 1
  n3 : ‖g3‖ ≤ 1

end ReciprocityTheory.ChartRestriction.L1
end
end
