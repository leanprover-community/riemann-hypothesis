module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightsAndFormsOfIntersectionAndInductiveStatement
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.IsClosedImmersionLift
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.ExistsMetricExtB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Set MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.TwistTop
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

namespace GlobalTheory.ArithmeticHeightTower.Read1

open GlobalTheory.Amb GlobalTheory.Published GlobalTheory.Published.Amb

theorem heights_of_form_mix (HF : FormZ) (HM : MixZ) : HeightsZ ∧ HeightsQ := by
  have H := GlobalTheory.T.arithHeightsAndForms_of_intersection_and_inductive (form HF) (mix HM)
  refine ⟨fun m n M _ => ?_, fun n' m n M _ => ?_⟩
  · have := isIntegral_mp ℤ m n
    exact (H ℤ _ _ _ (isArithVar_mpZ m n)).1 M
  · have := (isArithVar_qp n' m n).isIntegral
    exact (H ℤ _ _ _ (isArithVar_qp n' m n)).1 _

theorem bridge3 (HF : FormZ) (HM : MixZ) (HP : ProjQ) : ArFormExists ∧ ArMix ∧ HeightProjection :=
  ⟨form HF, mix HM, proj (heights_of_form_mix HF HM).1 (heights_of_form_mix HF HM).2 HP⟩

end GlobalTheory.ArithmeticHeightTower.Read1
