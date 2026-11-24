module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

noncomputable section

namespace GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar




def nOfLay {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P)
    (L : Lay0 (Dof x)) (hZ : L.ZOk) (hE : L.EtaOk) : NStage B w.C (P.q.W x.o.η x.o.hη) :=
  { loc := L.loc, locA := L.locA, locT := L.locT, nd := L.nd, ntw := L.ntw, naut := L.naut, nbc := L.nbc, nexp := L.nexp,
    ntypes := L.ntypes, nStage_trivialCharacter_compat := L.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := L.nStage_trivialCharacter_coeff_eq, nth := L.nth, nbr := L.nbr, nbr_ind := L.nbr_ind,
    self_good := L.self_good, ntwbr := L.ntwbr, ntwbr_ind := L.ntwbr_ind, loc_tie := L.loc_tie, bc_tie := L.bc_tie,
    rbar_tie := L.rbar_tie, mtpar_tie := L.mtpar_tie, Z_tie := hZ.1, Zgood_tie := hZ.2, etaJ_tie := hE }

theorem exists_pq_sel (B : Base) {px : PreX B.toPre} (I : ColIn B px) (hI : I.Ok) :
    ∃ Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield B.host.E)) → PlE B.host,
      (∀ v, NG.OverPl (Pq v) v) ∧ Set.range Pq = Set.range I.sel :=
  ⟨I.sel, fun v => hI.sel_ok v, rfl⟩

end GlobalTheory.HeightCounting.Up

end
