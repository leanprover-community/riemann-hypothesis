module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PinsCardIndexRanks
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.HeightCounting.Fin3

theorem grpTie_of_LC_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} {x : St P} (_ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x), Formalism.L2.DIV.GrpTie (Dof x)
      (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A x.m.z.F.P0 x.m.z.F.ψ0 x.m.z.F.P1 x.m.z.F.ψ1
      (x.m.z.R.eG.trans x.m.z.cG) := by
  intro hL K B f T w P x l
  have hc := GlobalTheory.Mem.R3.pins_card_index_ranks _ _ _ _ _ _ _ _ _ _ x.m.z.pins
  have hU : (Dof x).nexp.U = Formalism.IndefR.NX.U (Dof x).nd := l.b.Bs.exp.U_eq
  obtain ⟨_, _, _, he0, _, _⟩ := x.m.z.pins.keep.grp
  refine ⟨hc.1, he0, ?_, ?_, hc.2.1, x.m.z.pins.keep.psi.lvl⟩
  · intro g
    rw [hU]
    exact l.rat.rat.lvl g
  · intro u hu i b
    have hu' : (x.m.z.R.eG.trans x.m.z.cG) u ∈ Formalism.IndefR.NX.U (Dof x).nd := by
      simpa only [hU] using hu
    refine ⟨psiUOf (Dof x).nd (NX.xiRed (Dof x)) l.rat.In.θ ⟨_, hu'⟩, l.rat.rat.psi u hu', ?_⟩
    exact l.b.Bs.psiU i b _ hu hu'

end GlobalTheory.HeightCounting.Fin3

theorem _root_.GlobalTheory.T.grpTie_of_levelC : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} {x : St P} (_ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x), Formalism.L2.DIV.GrpTie (Dof x)
      (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A x.m.z.F.P0 x.m.z.F.ψ0 x.m.z.F.P1 x.m.z.F.ψ1
      (x.m.z.R.eG.trans x.m.z.cG) :=
  @GlobalTheory.HeightCounting.Fin3.grpTie_of_LC_alt
