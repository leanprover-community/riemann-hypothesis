module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.unitaryCongruence Matrix

namespace PI.UnitaryDimensionFormula.NormCutK

section Dual

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem Z_smul_mL {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} {u : VA X.B.I} (hc : ZMod' X.B.I X.B.g c)
    (hu : u ∈ X.B.I.Lf) : c • u ∈ mL X.B.I X.B.g := by
  obtain ⟨t, ht, rfl⟩ := hc
  rw [mul_comm, mul_smul]
  exact Submodule.smul_mem (mL X.B.I X.B.g) (⟨t, ht⟩ : IntAf X.B.I.F X.B.I.E) (smul_mem_mL X.B.I hu)

theorem frame_Lf : (∀ a, X.e0 a ∈ X.B.I.Lf) ∧ (∀ a, X.f0 a ∈ X.B.I.Lf) ∧ X.z0 ∈ X.B.I.Lf ∧
    (∀ l, X.bw l ∈ X.B.I.Lf) ∧ (∀ l, X.bwd l ∈ X.B.I.Lf) := ⟨fun a => (X.vectorsInLattice.1 a).1, fun a => (X.vectorsInLattice.1 a).2, X.vectorsInLattice.2.1,
    fun l => (X.vectorsInLattice.2.2 l).1, fun l => (X.vectorsInLattice.2.2 l).2⟩

end Dual

end PI.UnitaryDimensionFormula.NormCutK
