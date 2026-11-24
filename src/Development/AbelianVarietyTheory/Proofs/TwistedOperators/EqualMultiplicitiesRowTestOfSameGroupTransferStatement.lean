module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqualMultiplicitiesRowTestOfSameGroupTransfer
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr
theorem _root_.GlobalTheory.T.equalMultiplicities_rowTest_of_sameGroupTransfer :
    ∀ (B : Base) (C : Cols B) (a b : Late B C) (px : PreX B.toPre) (I : ColIn B px)
      (hX : B.fields.Ok) (Tw : TwDat B) (Wt : Set B.places.Pl) (s : SameGrp a b)
      (z : Dat a.st I hX Tw Wt),
      let z' := GlobalTheory.Mem.R3.DatCopy.copy b s z
      (GlobalTheory.CuspMult.MultEq z'.R.toRealDat → GlobalTheory.CuspMult.MultEq z.R.toRealDat) ∧
        (Formalism.IndefR.Rat.RowTest (z'.R.toCx3 z'.F) →
          Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F)) :=
  GlobalTheory.Twist.multEq_rowTest_of_copy
