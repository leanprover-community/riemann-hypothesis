module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
public import Development.AutomorphicArithmetic.ResidueCharacters.ClosedOfAll
public import Development.AutomorphicArithmetic.ResidueCharacters.ThreeHost
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyBoundAtTwoThreeOfLocalBounds
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NRowThree
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NRowTwo
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

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace UpperTheory.N
theorem at23_family_alt (hP : Hypotheses₂) {eps : ℝ} (Fm : FamP eps) : _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm :=
  _root_.UpperTheory.N.boundAtTwoThree_of_local_bounds_at_two_three three_ne_q (_root_.UpperTheory.N.exists_nonneg_twoC_constants_of_prints hP) (_root_.UpperTheory.N.exists_nonneg_threeC_constants_of_prints hP) Fm
theorem boundAtTwoThree_n_linked (h : ∀ {eps : ℝ} (Fm : FamP eps), _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) :
    _root_.GlobalTheory.Fc.RL.LinkedAt p (fun Q L => _root_.GlobalTheory.Fc.R1.SlotNormCondition Q L fun 𝒞 => Closed 𝒞 fun Fm _ => _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm) :=
  _root_.GlobalTheory.Fc.RL.LinkedAt.of_row (GlobalTheory.Fc.Row.of_sel fun _ _ _ => closed_of_all _ fun Fm _ => h Fm)
theorem boundAtTwoThree_linked_of_recT (hP : Hypotheses₂) {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) :
    _root_.GlobalTheory.Fc.RL.LinkedAt p (fun Q L => _root_.GlobalTheory.Fc.R1.SlotNormCondition Q L fun 𝒞 => Closed 𝒞 fun Fm _ => _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm) :=
  _root_.UpperTheory.N.boundAtTwoThree_n_linked (fun Fm => _root_.UpperTheory.N.at23_family_alt hP Fm) p
end UpperTheory.N
end
