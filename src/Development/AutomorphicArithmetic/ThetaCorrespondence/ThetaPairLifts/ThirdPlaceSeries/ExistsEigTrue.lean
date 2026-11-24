module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigOfRatAd
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SCuspRows

theorem exists_eigTrue_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} {x : St P} (l : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x) (n : InRat x.r.Y x.m.z.cG) :
    ∃ Sb, GlobalTheory.TwInputs.EigTrue (Dof x) (cfOf x) l.a.A.row Sb n.In.eig := by
  obtain ⟨Sb, h1, h2, -⟩ := GlobalTheory.TwInputs.Eig.exists_low (ι := Empty) n.In.Sb (fun i => i.elim) (fun i => i.elim) fun i => i.elim
  have h := _root_.GlobalTheory.TwInputs.Eig.eigTrue_of_read hL x.r.Y x.m.z.lev.is l.a.A.wdT l.a.A.row l.a.row n.rat.eig h1 h2
  have hC : x.m.z.R.C = cfOf x := x.m.z.lev.C
  exact ⟨Sb, (congrArg (fun c : CharFrame (Dof x) => GlobalTheory.TwInputs.EigTrue (Dof x) c l.a.A.row Sb n.In.eig) hC).mp h⟩
end GlobalTheory.SCuspRows
end
