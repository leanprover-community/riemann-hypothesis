import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsComplementaryProductAbsPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel MeasureTheory

namespace GlobalTheory.UnitaryDual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem subsingleton_quot_one : Subsingleton (GL (Fin 1) k ⧸ Subgroup.center (GL (Fin 1) k)) := by
  rw [QuotientGroup.subsingleton_iff, eq_top_iff]
  intro g _
  rw [Subgroup.mem_center_iff]
  intro h
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp [Matrix.mul_apply, mul_comm]










end GlobalTheory.UnitaryDual

end
