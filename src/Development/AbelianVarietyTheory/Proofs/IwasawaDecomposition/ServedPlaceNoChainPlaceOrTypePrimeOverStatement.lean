module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ServedPlaceNoChainPlaceOrTypePrimeOver
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
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG

theorem _root_.GlobalTheory.T.served_place_no_chain_place_or_type_prime_over : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      Formalism.L2.Forms.okQ (w.D Z) (tt.ch.Q ((w.D Z).what₂.muAt v)) v ∧
        (∀ w' ∈ Formalism.L2.Forms.badQ (w.D Z) (tt.ch.Q ((w.D Z).what₂.muAt v)), (((w.D Z).what₂.places.resChar v : ℕ) : 𝓞 (w.D Z).host.F) ∉ w'.asIdeal) ∧
        ¬ (w.D Z).what₂.places.resChar v ∣ ((w.D Z).mem u).A.T := by
  first | exact @GlobalTheory.ServedPlace.places_prime | exact GlobalTheory.ServedPlace.places_prime | (intros; apply GlobalTheory.ServedPlace.places_prime <;> assumption)
