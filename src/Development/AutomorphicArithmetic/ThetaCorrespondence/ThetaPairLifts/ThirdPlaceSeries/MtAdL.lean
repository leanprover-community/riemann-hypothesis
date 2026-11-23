module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalMultiplicityFamily
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



section
noncomputable section
namespace GlobalTheory.HeightCounting.Fin3
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem exists_mtAd_psi_vector_of_yRel {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
    {x : St P} (L : LocAll (lay0 (Dof x))) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0) (hY : YRel L Y) :
    ∃ ad : MtAd Y (_root_.GlobalTheory.HeightCounting.Fin3.localMultiplicityFamily L l), ad.PV = _root_.GlobalTheory.HeightCounting.Fin3.psiVectorLocal L l := by
  refine ⟨{ PV := _root_.GlobalTheory.HeightCounting.Fin3.psiVectorLocal L l
            std := (by with_unfolding_all exact (l.mt.ad.std :))
            eW := (by with_unfolding_all exact (l.mt.ad.eW :))
            read := fun μ h i y g => ?_
            rat := (by with_unfolding_all exact (l.mt.ad.rat :))
            wt := (by with_unfolding_all exact (l.mt.ad.wt :))
            id := (by with_unfolding_all exact (l.mt.ad.id :)) }, rfl⟩
  have h1 := l.mt.ad.read ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (y :))) ((by with_unfolding_all exact (g :)))
  have h2 := hY.jMt μ h i y
  with_unfolding_all
    exact h1.trans (congrFun (eq_of_heq h2) _).symm
end GlobalTheory.HeightCounting.Fin3
end
end
