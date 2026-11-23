module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsStdFStdLvC
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionPairingRationalOnRationalPoints
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IotaStarProjectionQsp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReFaceScalarsErrorsReadings
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ZetaUniformOfExtension
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerEntTiedTrueEnt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRowsKCColPins
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev GlobalTheory.Mem.R3 in

theorem GlobalTheory.Mem.Top.Bl.ze_u_prm_of_extension_with_law : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ZeU (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s := by
  intro hPr hL N S Γ hN K q
  have hK : ∃ t : Formalism.L2.Ker.KerEntTied q.O.ex, KPin q t := by
    obtain ⟨B, f, T, w, Z, O, x⟩ := q
    obtain ⟨L, gatT, Gx, Gy, Kc, X, cX, ex⟩ := O
    obtain ⟨lev, th, th_io, cmp, lat, tw, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def, errX, err, nch, nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ := ex
    obtain ⟨isOver, forced, Wt, pin, coh, vol, col, what₂, rx, hlev, herrX, n, nx, sx, ker0, ker_eq, kT, div, thT, obj, ox, real, dsig_eq, gaugeG, good⟩ := x
    simp only [ofObj, extraObj] at ker_eq
    cases ker_eq
    obtain ⟨t1, s1, o1, e1, a1, p1⟩ := TC.kerEntTied_true_ent w.I w.ok w.pins w.l Z L col.Gt Gx Gy Kc X cX
      ⟨lev, th, th_io, col.cmp, lat, w.tw Z, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def, errX, err, nch,
        nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ kT.O kT.E div.Qp kT.std
      kT.unf kT.ok kT.served
    exact ⟨t1, (StdModel.stdKer_iff w.I w.l Z t1).2 s1, o1, heq_of_eq e1, a1, p1⟩
  obtain ⟨t, ht⟩ := hK
  let _ : Algebra q.x.what₂.r.z.core.Q.c.F (q.w.D q.Z).what₂.LL := q.x.what₂.r.z.alg
  obtain ⟨Dc, Sp₀, Zsc₀, C₀, -⟩ := _root_.GlobalTheory.Mem.R3.SelC.square_integrable_columns_of_witnesses _ K q t ht ⟨q.x.rx⟩
  obtain ⟨kap, lam, err, hP, hH, -, -, -, Y', Z', htup, -, hjA, -⟩ := GlobalTheory.Mem.R3.reFace_scalars_errors_readings _ _ _ _ _ _ _
    q.x.what₂.r.z.R q.x.what₂.r.z.F q.x.what₂.r.z.cG q.O.ex.p0 q.x.what₂.r.Y q.x.what₂.r.Z Dc Sp₀ q.x.what₂.r.z.F.Zsc (fun _ => Or.inl rfl)
    q.x.what₂.r.z.pins q.x.what₂.r.intersectionNumber_baseChange
  obtain ⟨C'⟩ := GlobalTheory.Mem.R3.readC_reFace_updS q.x.what₂.r.z.R q.x.what₂.r.z.F q.O.ex.p0
    Dc Sp₀ Sp₀ Zsc₀ q.x.what₂.r.z.F.Zsc kap lam err C₀ Y' htup hjA
  obtain ⟨nb⟩ := hN _ _ _ _ _ _ _ _ _ _ _ _ _ q.x.nx.2
  have hBk : BkLaw (q.w.D q.Z) := nb.2.down
  have hRat := GlobalTheory.Mem.R3.divisionPairing_rational_on_rationalPoints hPr (q.w.st q.Z).toD7 _ _ _ _ _ _ _ _ _ _ Y' Z' C' hP hH
  exact GlobalTheory.Mem.R3.zeTied_of_read hPr (q.w.st q.Z).toD7 _ _ _ _ _ _ _ _ _ _ Y' Z' C' hP hH (hBk hRat)
end
