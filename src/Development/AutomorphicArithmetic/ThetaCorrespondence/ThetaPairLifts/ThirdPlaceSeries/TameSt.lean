module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallnessCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameAtSmallPlace
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
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
namespace GlobalTheory.TameStab
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Groups
variable {G Γ : Type} [Group G] [Group Γ]
end Groups
theorem tameSt_alt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → TameAt p j w := by
  unfold _root_.GlobalTheory.ExpTie.InRangeAlt _root_.GlobalTheory.BigOn.AtPtsAlt Formalism.MainNotions.Closed _root_.GlobalTheory.BigTop.EventuallyAtPoints
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ⟨0, fun x hx _ i p _ _ => ?_⟩⟩⟩
  intro j P W hD _ w _ _ hS
  exact tameAt_of_smallAt p j P w hD.Nr hS
end GlobalTheory.TameStab
end
end
