module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DsigEq
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.Top.Bl.WPt.extraTied_col : ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K), Formalism.L2.Forms.ColsExtraTiedS q.x.col.full q.O.ex ∧ ∃ g : Formalism.L2.G.GroupCompatibilityAll (q.w.D q.Z) q.O.gatT q.O.ex.cmp, HEq g q.x.col.g ∧ g.herm = q.x.col.full.1.to0 ∧ g.forms = fun u => (q.x.col.C.forms u).to0 := by
  intro 𝒮 K q
  obtain ⟨B, f, T, w, Z, O, x⟩ := q
  obtain ⟨L, gatT, Gx, Gy, K', X, cX, ex⟩ := O
  obtain ⟨lev, th, th_io, cmp, lat, tw, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def,
    errX, err, nch, nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ := ex
  obtain ⟨isOver, forced, Wt, pin, coh, vol, col, what₂, rx, hlev, herrX, n, nx, sx, ker0, ker_eq, kt, div, thT, obj, ox, real,
    dsig_eq, hgauge, good⟩ := x
  obtain ⟨⟨C, std, stdLv, full, stdDt, Gt, cmp', g, herm_eq, forms_eq, gpl⟩, isRec, om⟩ := col
  dsimp only at hlev herrX ker_eq ⊢
  cases ker_eq
  exact ⟨⟨⟨hlev, herrX, gpl⟩, kt.iw, kt.iw_pos⟩, g, HEq.rfl, herm_eq, forms_eq⟩
