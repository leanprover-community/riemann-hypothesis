import Formalism.LocalToGlobal.IndefiniteReal.DiscreteSeriesPlaces
import Formalism.LocalToGlobal.IndefiniteReal.MultGood
import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank
import Formalism.LocalRingCardinality.PosOfIsomEmb
import Formalism.SharpRestriction.Divisibility.FunctionModelRallisFromInputs
import Mathlib
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLw
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Matrix

namespace Formalism.IndefR.DiscreteSeriesPlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem lamAt_anti {R : Ranks} (hc : HCParam R) {d c : ℕ} (hdc : d ≤ c) (hc' : c < R.r) :
    lamAt hc c ≤ lamAt hc d := by
  have := lamAt_add_add_le hc (c - d) d (by omega)
  rw [show d + (c - d) = c by omega] at this
  have h0 : (0 : ℚ) ≤ ((c - d : ℕ) : ℚ) := by positivity
  linarith


theorem isEnum_dual {n : ℕ} {S : SPar} {lam : Fin n → ℝ} {ε : Fin n → Bool} (h : IsEnum S lam ε) :
    IsEnum (dualPar S) (fun a => -lam (Fin.rev a)) (fun a => ε (Fin.rev a)) := by
  obtain ⟨hanti, Q, hQ, rfl⟩ := h
  refine ⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a => -Q (Fin.rev a),
    fun a => by simp [hQ], ?_⟩
  unfold dualPar
  rw [Finset.image_image]
  ext ⟨x, s⟩
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨Fin.rev a, by simpa using ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨_, ha⟩



section Rec

variable (D : D7) (τ : D.what₂.Tau)

end Rec

section Rec2

variable (D : D7) (τ : D.what₂.Tau)

end Rec2



end Formalism.IndefR.DiscreteSeriesPlaces

end
