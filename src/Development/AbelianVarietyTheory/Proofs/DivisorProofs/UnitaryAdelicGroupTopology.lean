module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCA
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.UnitaryAdelicTop

theorem lcsc_UA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E), IsTopologicalGroup (UA σ J) ∧ LocallyCompactSpace (UA σ J) ∧
      SecondCountableTopology (UA σ J) ∧ T2Space (UA σ J) := by
  apply GlobalTheory.LeviModulus.topUA

end GlobalTheory.UnitaryAdelicTop
