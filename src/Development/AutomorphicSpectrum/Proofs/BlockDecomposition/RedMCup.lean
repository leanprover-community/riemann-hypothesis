module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.IsFirstChernThickening
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.RedCup

theorem redM_cup {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (r : Option ℤ) (c : b.R) {i j k : ℕ} (h : i + j = k)
    (x : HO Q i) (y : HO Q j) :
    redM Q r c k ((CH.mulP (sP Q).A).cup h x y) = (sqP (stdI Q r c)).cup h (redM Q r c i x) (redM Q r c j y) := by
  have hm : ∀ T (u v : (CH.modF (sP Q).A).obj ((𝟭 _).obj T)),
      (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).τ T ((CH.mulP (sP Q).A).μ _ u v) =
        (sqP (stdI Q r c)).μ T ((toSq (IdF.top _) (stdI Q r c) fun _ => rfl).τ T u)
          ((toSq (IdF.top _) (stdI Q r c) fun _ => rfl).τ T v) := fun _ _ _ => rfl
  exact CrystallineSemistableComparison.P.cup_pull (CH.mulP (sP Q).A) (sqP (stdI Q r c)) (𝟭 _)
    (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).τ (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).τ
    (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).τ (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).nat
    (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).nat (toSq (IdF.top _) (stdI Q r c) fun _ => rfl).nat hm h x y

end GlobalTheory.CompanionTheory.RedCup
