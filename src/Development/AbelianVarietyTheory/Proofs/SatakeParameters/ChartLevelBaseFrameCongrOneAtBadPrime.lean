import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBaseFrameBadPrimeEqCompanionLattice
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GlobLatCompanOfLev

section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV

theorem congAt_fb_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x : UA D i hi) p (κ : ((St i hi).K β).lev.U), IsPtAd A a i hi β x p → ∀ P : SB t μ, CongAt (seamP t.seam P.1) 0 ((ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P)) ∧ CongAt (seamP t.seam P.1) 0 ((ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P))⁻¹) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP H i hi β x p κ hp P
  exact GlobalTheory.LevStab.lev_stab_cong i hi _ a κ _ _ (GlobalTheory.T.chartBaseFrame_badPrime_eq_companion_lattice A dtU a hP H i hi β x p hp P)

end GlobalTheory.TwV

end
end

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartLevel_baseFrame_congr_one_at_badPrime : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x : UA D i hi) p (κ : ((St i hi).K β).lev.U), IsPtAd A a i hi β x p → ∀ P : SB t μ, CongAt (seamP t.seam P.1) 0 ((ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P)) ∧ CongAt (seamP t.seam P.1) 0 ((ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P))⁻¹) := by
  atlas_forward_decl GlobalTheory.TwV.congAt_fb_lev
