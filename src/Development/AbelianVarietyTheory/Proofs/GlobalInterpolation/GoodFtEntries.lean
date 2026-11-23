module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
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
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM

namespace GlobalTheory.Fc.LabLinked

def Ties (D : D7) : Prop :=
  ∃ (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : Formalism.L2.SG.RowDict.GoodOp X)
    (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X),
    Formalism.MainNotions.S.AutTie D X.B X.pl ∧ Formalism.L2.SG.RowDict.RowDictTie X G ι ∧ GlobalTheory.LabPin.LabTie X ι


section Rows

open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.NX


end Rows

theorem lab_of_rows {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) :
    GlobalTheory.SerSys.LabTie (w.D Z) fun k => @GlobalTheory.Mem.TypePl.labDat ((w.D Z).host.g k) ⟨(w.D Z).host.g_prime k⟩ :=
  fun k => ⟨(t.grp.teich k).symm, t.grp.ser k⟩


end GlobalTheory.Fc.LabLinked
