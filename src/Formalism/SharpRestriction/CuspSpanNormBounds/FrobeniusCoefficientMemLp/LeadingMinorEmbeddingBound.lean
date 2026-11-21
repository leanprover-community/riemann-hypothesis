import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.LeadMinorEZhatOMNorm
import Formalism.SharpRestriction.CuspSpanNormBounds.GramProductLeHeightBoundTwo

set_option linter.unusedVariables false

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.S.Pv.HH

open Finset NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.MainNotions.BesselShellMomentBounds
  Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem rdE_pos' : 0 < D.host.rdE := lt_of_lt_of_le zero_lt_one (one_le_rdE D)

theorem one_le_prod_norm (x : D.host.E) (hx : x ∈ intS D) (h0 : x ≠ 0) : 1 ≤ ∏ τ, ‖embS D τ x‖ :=
  Formalism.MainNotions.BesselShellMomentBounds.prod_absV_ge_one D x hx h0


def qS : ℝ := D.host.rdE ^ (-(D.R.rS : ℝ))






def R0 : ℝ := ((qS D)⁻¹) ^ (2 * (D.R.rS + 1))


def rhoIJ {j : ℕ} (I J : Fin j ↪o Fin (D.R.rS + 1)) : ℝ := ∏ a, (rhoF D (I a) * rhoF D (J a))





theorem frameExp_le (l : ℕ) (hl : l ≤ D.R.rS + 1) : frameExp D.R.rS l ≤ (D.R.rS + 1) ^ 2 := by
  unfold frameExp
  calc ∑ a ∈ Finset.Icc 1 l, (D.R.rS + 1 - a) ≤ ∑ a ∈ Finset.Icc 1 l, (D.R.rS + 1) :=
        Finset.sum_le_sum fun a _ => Nat.sub_le _ _
    _ = l * (D.R.rS + 1) := by rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul]; congr 1
    _ ≤ (D.R.rS + 1) ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right _ hl

def R1 : ℝ := D.host.rdE ^ (2 * ((D.R.rS : ℝ) + 1) ^ 2)






end Formalism.MainNotions.S.Pv.HH

end
