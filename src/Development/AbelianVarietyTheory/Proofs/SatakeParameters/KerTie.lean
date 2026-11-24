module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsStdFStdLvC
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ErrorDataGeneratorsEqColumnPreDatumStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerEntTiedTrueEnt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain



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
