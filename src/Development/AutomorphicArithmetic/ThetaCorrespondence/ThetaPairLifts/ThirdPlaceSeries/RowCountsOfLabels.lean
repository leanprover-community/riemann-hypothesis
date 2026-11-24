module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowCountsOfTies
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
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.CountRowByName
theorem row_counts_of_labels_alt : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop) (Q Q' : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), (Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.RL.RowLabelCondition S Lk) → Lg1 KP Q Q' fun S => _root_.GlobalTheory.Fc.R1.CountsIrreducibilityConstants' S Lk :=
  fun hSW _ _ _ Lk ⟨R, hR, h⟩ => ⟨R, hR, _root_.GlobalTheory.CountRow.row_counts_of_ties_alt hSW _ Lk h⟩
end GlobalTheory.CountRowByName
end
