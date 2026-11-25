module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVGrpCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainRecursionFromSingleDescent
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorPreservesFusionForms
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightDerivativeRulePsi
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellMulVecBasis
import Mathlib.Tactic.TypeStar

@[expose] public section

open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx3 Formalism.FourierDecayAlt.P.WeylCellAction

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem mirror_right_rule_holds : RightRuleEv := by
  intro E _ _ k r z' D f hz' hD hS hR g hg a b hab
  have ha := a.isLt
  have hjlt : 2 * r + k - a.val - b.val - 1 < mdim k r b.succ := by simp [mdim]; omega
  have hpos : posL k r b.succ ⟨2 * r + k - a.val - b.val - 1, hjlt⟩ = esI k r a := by
    simp [posL, esI, Fin.ext_iff]; omega
  have h := (right_action_at hz' hD hS hR hg b).2 ⟨2 * r + k - a.val - b.val - 1, hjlt⟩
  rw [hpos] at h
  rw [h]
  congr 1
  simp only [xbv, fvec, hpos, Fin.val_succ]
  rw [dite_eq_left (show b.val + 1 < r by omega)]
  rw [Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_eI]
  by_cases hh : a.val = b.val + 1
  · simp [hh, bvec, esI]
  · rw [ite_eq_right hh]
    simp only [bvec, Pi.single_apply, esI, Fin.ext_iff]
    rw [ite_eq_right (by omega)]

theorem mirror_torus_cell_holds : TorusCellv := by
  intro E _ _ k r D f hD hS c hc g hg hWD l
  exact (torus_action_cell hD hS hc hg hWD l).2

theorem herm_smul_right' {k r : ℕ} (v w : Fin (2 * r + k + 1) → ℂ) (s : ℂ) :
    herm (Hpk k r) v (s • w) = star s * herm (Hpk k r) v w := by
  unfold herm
  rw [star_smul, smul_dotProduct, smul_eq_mul]

theorem mirror_left_rule_cell_holds : LeftRuleCellv := by
  intro E _ _ k r z D f hz hD hDN hS hL c hc g hg hWD a b hba
  have ha := a.isLt
  obtain ⟨T, hT, hTG, hTe, _, _⟩ := tail (k := k) c hc b (r - b.val - 1) (Fin.last r) (by simp; omega)
  have hjlt : 2 * r + k - a.val - b.val - 1 < mdim k r b.succ := by simp [mdim]; omega
  have hpos : posL k r b.succ ⟨2 * r + k - a.val - b.val - 1, hjlt⟩ = esI k r a := by
    simp [posL, esI, Fin.ext_iff]; omega
  have h := (left_action_cell hz hD hDN hS hL hc hg hWD b hT hTG).2 ⟨2 * r + k - a.val - b.val - 1, hjlt⟩
  rw [hpos] at h
  rw [h]
  congr 1
  have hb1 : (b.succ : Fin (r + 1)).val < r := by simp; omega
  have hga : g *ᵥ bvec (eI k r a) = bvec (eI k r a) := (hg.2 a (by simp)).1
  have hTa := hTe a hba
  rw [ite_eq_left (by simp)] at hTa
  have hU : T * g ∈ UH (Hpk k r) := (glev_mul hTG (glev_mono (Fin.le_last _) hg)).1
  have key : ((T * g)⁻¹ *ᵥ bvec (eI k r ⟨b.val + 1, by omega⟩)) (esI k r a) =
      if a.val = b.val + 1 then star (c a) else 0 := by
    rw [← Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_eI ((T * g)⁻¹ *ᵥ bvec (eI k r ⟨b.val + 1, by omega⟩)) a,
      ← Formalism.FourierDecayAlt.P.Qx2.herm_uh hU, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hU), Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hga, hTa,
      herm_smul_right', ← Formalism.FourierDecayAlt.P.Qx2.herm_star, Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_eI]
    by_cases hh : a.val = b.val + 1
    · rw [ite_eq_left hh]
      have : (bvec (esI k r a) : Fin (2 * r + k + 1) → ℂ) (esI k r ⟨b.val + 1, by omega⟩) = 1 := by
        simp [bvec, esI, hh]
      rw [this, star_one, mul_one]
    · rw [ite_eq_right hh]
      have : (bvec (esI k r a) : Fin (2 * r + k + 1) → ℂ) (esI k r ⟨b.val + 1, by omega⟩) = 0 := by
        simp only [bvec, Pi.single_apply, esI, Fin.ext_iff]
        rw [ite_eq_right (by omega)]
      rw [this, star_zero, mul_zero]
  have hy : yv k r z b.succ (T * g) ⟨2 * r + k - a.val - b.val - 1, hjlt⟩ =
      if a.val = b.val + 1 then star (c a) else 0 := by
    simp only [yv, hpos, fvec, dite_eq_left hb1]
    exact key
  rw [hy]
  by_cases hh : a.val = b.val + 1
  · rw [ite_eq_left hh, ite_eq_left hh, div_eq_inv_mul]
  · rw [ite_eq_right hh, ite_eq_right hh, mul_zero]

end Formalism.FourierDecayAlt.P.CutMP.TVG
