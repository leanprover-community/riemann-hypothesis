import Formalism.CoboundaryTransfers.GammaStableTransfers.GammaStableOfGammaQUnitHolds

noncomputable section

namespace Formalism.CoboundaryTransfers

theorem liftsAt_mono : Mono := by
  intro O A _ _ _ B M M' D _ _ _ _ W hMM' hGQ
  refine ⟨{
    N := W.N
    φ := W.φ
    γ := W.γ
    φ_smul := W.φ_smul
    γ_smul := W.γ_smul
    comm := W.comm
    X_inj := W.X_inj
    Q_bij := W.Q_bij
    φ_N := fun x hx => by
      have h : B.Q ^ M' = B.Q ^ (M' - M) * B.Q ^ M := by
        rw [← pow_add, Nat.sub_add_cancel hMM']
      rw [h, mul_smul]
      exact W.N.smul_mem _ (W.φ_N x hx)
    γ_N := W.γ_N
    γ_QN := gammaStableOfGammaQUnit_holds O A B M' D W.N W.γ hGQ W.Q_bij W.γ_smul W.γ_N }, rfl, rfl, rfl⟩


end Formalism.CoboundaryTransfers
