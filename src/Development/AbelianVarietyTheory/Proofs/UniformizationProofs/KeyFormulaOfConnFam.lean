module

public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditionalStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaUniformisationComplexAbelianVarietiesStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ChiGen
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsCommonCountable
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyRuleCharHalf
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSmoothThrough
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.FiniteAbsLeOneMulMemRange
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsDomainTensorOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyDataDescendCountableSubringsStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormLeTsumOfCubeFourierCoeffLe
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TorusAlgebraicHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory

theorem keyFormula_of_connFam : GlobalTheory.KeyKa.ConnFam → KeyFormula := fun hF =>
  have hL := GlobalTheory.T.abelianScheme_laws_unconditional.1
  have hR := GlobalTheory.KeyTop.exists_keyRule_charHalf hL GlobalTheory.T.theta_uniformisation_complex_abelian_varieties GlobalTheory.ThetaInversion.inversion (GlobalTheory.phHolo_of_phKoecher GlobalTheory.phKoecher) GlobalTheory.torusAlgebraic_holds
  GlobalTheory.KeyRoot.keyFormula_of_families GlobalTheory.T.theta_uniformisation_complex_abelian_varieties hL.polBaseChange (GlobalTheory.T.keyData_descend_countable_subrings hL).1 hR
    (GlobalTheory.ThetaFrameSpec.value_specialises hL GlobalTheory.T.theta_uniformisation_complex_abelian_varieties GlobalTheory.ThetaInversion.inversion hR (GlobalTheory.ThetaEquiv.val_equivariant hL GlobalTheory.T.theta_uniformisation_complex_abelian_varieties GlobalTheory.ThetaInversion.inversion hR hF))

end GlobalTheory
