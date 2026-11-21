import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaIntegrationFormulaUpToConstantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaIntegrationFormulaConstant

section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem iwasawaFormula : IwasawaFormula := by
  intro n ε p q hp hq a j hj W hW c μN μM μK hc hN hM hK0 hK1 hKinv φ hφ
  obtain ⟨κ, -, -, hκ⟩ := GlobalTheory.T.iwasawa_integration_formula_up_to_constant n ε p q hp hq a j hj W hW μN μM μK hN hM hK0 hK1 hKinv
  have hconst := GlobalTheory.T.iwasawa_integration_formula_constant n ε p q hp hq a j hj W hW μN μM μK hN hM hK0 hK1 hKinv c κ hc hκ
  rw [hκ φ hφ, ← mul_assoc, hconst]

end GlobalTheory.FlagMeas
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_iwasawa_integration_formula_real_place : IwasawaFormula := by
  atlas_forward_decl GlobalTheory.FlagMeas.iwasawaFormula
