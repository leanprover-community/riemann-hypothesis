module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRowsReadingTransportLaterHeckeGaloisStageStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DomCongrSymmEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedRowLiftDataToFittingStages
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw

theorem exists_st_copyN : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : NStage B w.C (P.q.W x.o.η x.o.hη)), GrpTrue N f → GrpAt (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.I → (∀ eR, StdIso (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.px eR → CenIs P.q.p N eR) → ∃ x' : St P, x'.o = ⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ ∧ HEq (repOf x'.r.Y) (repOf x.r.Y) := by
  intro K B f T w P x N hG hGA hCen
  have fits' : RowPk.Over.Fits (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over) := ⟨x.fits.div, hG, hGA, hCen⟩
  obtain ⟨m, hc, hco⟩ := Mv.exists_moved B f T w P.Z₀ P.hX P.Wt P.z P.q _ P.intersectionNumber_baseChange P.exAt P.inGeo P.grp fits'
  obtain ⟨sg, s, h1, h2, h3⟩ := CopySide.side_copy x N hG
  obtain ⟨r, hpin, hrep⟩ := GlobalTheory.T.adelicRowsReading_transport_laterHeckeGaloisStage x N hG hGA hCen m hc hco sg s h1 h2 h3
  exact ⟨⟨_, fits', x.G_eq, x.etaF, x.bk, m, hc, hco, s, r, hpin⟩, rfl, hrep⟩

end GlobalTheory.Mem.R3.Rw
