import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.InvSubOneBd
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.FiltRelIndex

namespace Formalism.L2.SG.Pf.RelativeIndexFlags.Filt

variable {n : ℕ} {K : Type*} [Field K] (L : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))

theorem sub_mono (k : ℕ) : (FG n K (k + 1)).subgroupOf L ≤ (FG n K k).subgroupOf L := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  exact FG_mono k hx






end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
