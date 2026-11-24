module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
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
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
namespace GlobalTheory.Fc.AllAtMember
section large₂
variable {KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop} {Q Q' : V4.Slot}
theorem forall_linked_bundles_and_alt {Lk : LkT _root_.GlobalTheory.Fc.BundleCondition} {H H' : ∀ 𝒜 : FamClass, RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜 → Prop}
    (h : Lg1 KP Q Q' fun S => Row S Lk H) (h' : Lg1 KP Q Q' fun S => Row S Lk H') :
    Lg1 KP Q Q' fun S => Row S Lk fun 𝒜 σ => H 𝒜 σ ∧ H' 𝒜 σ :=
  RowL.and (KP := KP) (Q := Q) (Q' := Q') h h'
end large₂
end GlobalTheory.Fc.AllAtMember
end
