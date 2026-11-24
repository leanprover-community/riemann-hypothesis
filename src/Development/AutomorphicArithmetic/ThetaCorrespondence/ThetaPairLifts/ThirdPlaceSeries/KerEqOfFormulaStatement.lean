module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KerEqOfFormula
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

theorem _root_.GlobalTheory.T.leafKernel_tie_of_claim_inputs : _root_.GlobalTheory.BigTop.Fun.BundleCondition → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → GlobalTheory.RowClaim.LinK → GlobalTheory.RowClaim.InjK → GlobalTheory.RowClaim.ConstK → GlobalTheory.RowClaim.Formula2K → _root_.GlobalTheory.BigTop.Fun.LeafKernel @GlobalTheory.BigTop.Fun.Comparison₂ := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.leafKernel_of_linK_injK_constK_formula2K | exact _root_.GlobalTheory.BigTop.Fun.leafKernel_of_linK_injK_constK_formula2K | (intros; apply _root_.GlobalTheory.BigTop.Fun.leafKernel_of_linK_injK_constK_formula2K <;> assumption)
end
