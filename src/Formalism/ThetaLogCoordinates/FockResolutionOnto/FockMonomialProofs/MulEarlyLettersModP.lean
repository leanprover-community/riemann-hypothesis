import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementE
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.FiltrationBotHolds
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.ResInto

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

section Gen

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ)

theorem dpow_zero (c : Fin r) (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) : dpow p LL j c 0 h = h := by
  simp [dpow]










noncomputable abbrev dw (l : List (Fin r × ℕ)) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  (l.map fun ck => dpow p LL j ck.1 ck.2).prod

theorem dw_cons (ck : Fin r × ℕ) (l : List (Fin r × ℕ)) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    dw p LL j (ck :: l) F = dpow p LL j ck.1 ck.2 (dw p LL j l F) := by
  simp only [dw, List.map_cons, List.prod_cons]; rfl


variable (M : WithTop ℤ)










end Gen




section Last

variable (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (M : WithTop ℤ)




end Last




end Formalism.InvariantFactorPaths.L4
