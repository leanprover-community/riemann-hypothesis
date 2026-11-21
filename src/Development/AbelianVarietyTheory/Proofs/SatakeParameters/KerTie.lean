import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerEntTiedTrueEnt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsStdFStdLvC

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

theorem errXS_pi_of_colT : ∀ (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (t : ColT w Z), (Formalism.L2.Herm.toErrXS t.full.1).piG = w.px.piG ∧ (Formalism.L2.Herm.toErrXS t.full.1).piT = w.px.piT := by
  intro B f T w Z t
  have hc : t.full.1.cols = t.C.herm := t.full.2
  refine ⟨?_, ?_⟩
  · show (t.full.1.cols.levelZeroCompatibility (w.D Z).u₀).piG = _
    rw [hc, ← t.C.piG]
    exact (t.std _).gl.piG
  · funext u
    show (t.full.1.cols.atT u).piU = _
    rw [hc, ← t.C.piU u]
    exact (t.std u).piU

end GlobalTheory.Svd
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.errorData_generators_eq_columnPreDatum : ∀ (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (t : ColT w Z), (Formalism.L2.Herm.toErrXS t.full.1).piG = w.px.piG ∧ (Formalism.L2.Herm.toErrXS t.full.1).piT = w.px.piT := by
  atlas_forward_decl GlobalTheory.Svd.errXS_pi_of_colT
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Svd.Part.kerTie : ∀ (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)), Part w Z (ofObj O) → O.ex.tw = w.tw Z ∧ O.ex.errX.piG = w.px.piG ∧ O.ex.errX.piT = w.px.piT ∧ TC.QpIs w.I O.X.Qp ∧ ∃ t : KerEntTied O.ex, TC.StdKer w.I w.l Z t ∧ t.Adapted ∧ t.TopPinned := by
  intro B f T w Z O P
  obtain ⟨L, gatT, Gx, Gy, Kc, X, cX, ex⟩ := O
  obtain ⟨lev, th, th_io, cmp, lat, tw, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def,
    errX, err, nch, nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ := ex
  obtain ⟨pin, col, hErr, tp, hxi, qp, ker0, ker_eq, kt⟩ := P
  dsimp only [ofObj, extraObj] at hErr ker_eq qp kt
  cases ker_eq
  subst hErr
  have hpi := GlobalTheory.T.errorData_generators_eq_columnPreDatum B f T w Z col
  refine ⟨rfl, hpi.1, hpi.2, qp, ?_⟩
  refine Exists.imp (by intro t h; exact ⟨(StdModel.stdKer_iff w.I w.l Z t).2 h.1, h.2.2.2.1, h.2.2.2.2⟩)
    (GlobalTheory.Mem.Col2.TC.kerEntTied_true_ent w.I w.ok w.pins w.l Z _ _ _ _ _ _ _ _ kt.O kt.E qp kt.std kt.unf kt.ok (by exact kt.served))
end
