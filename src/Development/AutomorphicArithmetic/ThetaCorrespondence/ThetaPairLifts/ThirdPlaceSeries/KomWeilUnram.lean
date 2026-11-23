module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatNotSelfDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeDataLocalRelation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDataLines
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.UnrWeil
end GlobalTheory.Fam.UnrWeil
open GlobalTheory.Fam.UnrWeil in
theorem GlobalTheory.Fam.kom_weil_unram_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (v : VCom f.c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat f.c k ι), f.RowOK → f.ColOK → v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ShapeOff v o → ∀ t j, j < D.R.m → ∃ μ, IsWeilDatumO f.c.ψ _ _ μ μ ((f.t t).kom j) ∧ ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D μ (o.p i).v := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW f v k _ _ _ _ ι o _ hC _ hV hS t j hj
  refine ⟨(_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1), hC.kom t j hj, fun i => ?_⟩
  have lev : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hW.bot.hyp.2.2.2.1.lev
  have hp : (o.p i).v ∈ v.tP := (hS.pre.tP _).2 ⟨i, rfl⟩
  have hTF : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (o.p i).v.asIdeal := (hV.tP _).1 hp
  have hTw : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = (o.p i).v →
      (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
    intro w hw
    rw [← hw] at hTF
    have := Ideal.mem_comap.1 hTF
    simpa using this
  show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (Formalism.IndefR.Lift.tup (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu0 ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.xi t) (j + 1)) (o.p i).v
  refine GlobalTheory.SeeSaw.WeilLines.charUnram_mul ?_ ?_
  · refine GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => ?_
    refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (lev.mu0 ⟨j, hj⟩) w).2 ?_
    refine ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.C.isMu0 ⟨j, hj⟩).unr w fun kk hk => ?_
    exact not_both_mem (D.mem u).A.T_prime (D.host.g_prime kk) (D.T_ne_g u kk) w (hTw w hw) hk
  · refine GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => ?_
    refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (lev.xi t) w).2 ?_
    by_contra hr
    rcases (lev.Q_ram t w).1 hr with hq | ⟨PP', hq, hc⟩
    · exact (lev.Q_off t w hq).2 u (hTw w hw)
    · exact (lev.Q_off t PP' hq).2 u (natCast_mem_of_isConjPl _ hc (hTw w hw))
end
