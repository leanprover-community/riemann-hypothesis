module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivisionSecondComplementAtConstructedPoints
public import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolumeSignatureIndepAndClassNumberItemsStatement
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory

theorem row_hInstR_of_hU (hU : ∀ D : D7, MassRatioUnderVolume D) : ∀ (Bd : BdT) (Q : V4.Slot) (Lk : LkT Bd), ClassTwoEntries.InstanceRankAtConstructedPoints Q Lk :=
  fun _ Q Lk => Row0.row (Row0.of_all (Q := Q) fun _ => by
    intro eps Fm _ x _ i
    exact GlobalTheory.T.volume_signature_indep_and_classNumberItems hU (Fm.D x i)) Lk

end GlobalTheory
